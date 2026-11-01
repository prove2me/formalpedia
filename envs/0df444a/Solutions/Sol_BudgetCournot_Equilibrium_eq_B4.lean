-- Prove2me | solution 1 for BudgetCournot.Equilibrium.eq_B4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T21:06:35.940206+00:00
-- url     : https://prove2.me/submissions/13144720-a5f2-472a-8958-1b9a874663cf

import Mathlib
import Definitions.Def_BudgetCournot_Equilibrium_Model

open Finset

namespace BCSol

open BudgetCournot.Equilibrium

lemma total_update {N M : ℕ} (x : Fin N → Fin M → ℝ) (i : Fin N) (y : Fin M → ℝ) (j : Fin M) :
    total (Function.update x i y) j = total x j - x i j + y j := by
  unfold total
  rw [← Finset.add_sum_erase _ _ (mem_univ i), ← Finset.add_sum_erase _ _ (mem_univ i)]
  rw [Function.update_self]
  have : ∑ k ∈ univ.erase i, Function.update x i y k j = ∑ k ∈ univ.erase i, x k j := by
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [Function.update_of_ne (ne_of_mem_erase hk)]
  rw [this]; ring

lemma payoff_update {N M : ℕ} (R β : Fin M → ℝ) (x : Fin N → Fin M → ℝ) (i : Fin N)
    (y : Fin M → ℝ) :
    payoff R β i (Function.update x i y) =
      ∑ j, (R j - (total x j - x i j + y j) / β j) * y j := by
  unfold payoff
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [total_update, Function.update_self]

/-- per-coordinate inequality for KKT sufficiency -/
lemma kkt_coord (R β O x y lam : ℝ) (hβ : 0 < β) (hlam : 0 ≤ lam)
    (hx : x = max 0 (β * R - β * lam - O) / 2) (hy : 0 ≤ y) :
    (R - (O + y) / β) * y - (R - (O + x) / β) * x ≤ lam * (y - x) := by
  rcases le_total (β * R - β * lam - O) 0 with h | h
  · rw [max_eq_left h] at hx
    have hx0 : x = 0 := by linarith
    subst hx0
    have : R - O / β ≤ lam := by
      have e : R - O / β - lam = (β * R - β * lam - O) / β := by field_simp; ring
      have : (β * R - β * lam - O) / β ≤ 0 := div_nonpos_of_nonpos_of_nonneg h hβ.le
      linarith
    have h2 : (R - (O + y) / β) * y ≤ (R - O / β) * y := by
      have : (O + y) / β = O / β + y / β := by ring
      rw [this]
      have : 0 ≤ y / β * y := mul_nonneg (div_nonneg hy hβ.le) hy
      nlinarith
    nlinarith
  · rw [max_eq_right h] at hx
    have hg : R - (O + 2 * x) / β = lam := by
      field_simp
      linarith
    have key : (R - (O + y) / β) * y - (R - (O + x) / β) * x
        = (R - (O + 2 * x) / β) * (y - x) - (y - x) ^ 2 / β := by
      field_simp; ring
    rw [key, hg]
    have : 0 ≤ (y - x) ^ 2 / β := div_nonneg (sq_nonneg _) hβ.le
    linarith

theorem br_suff {N M : ℕ} (R β : Fin M → ℝ) (B : Fin N → ℝ) (hβ : ∀ j, 0 < β j)
    (x : Fin N → Fin M → ℝ) (i : Fin N) (lam : ℝ) (h : IsBR R β B i x lam) :
    x i ∈ feasible B i ∧
      ∀ y ∈ feasible B i, payoff R β i (Function.update x i y) ≤ payoff R β i x := by
  obtain ⟨hlam, hx, hsum, hcs⟩ := h
  refine ⟨⟨fun j => ?_, hsum⟩, ?_⟩
  · rw [hx j]; positivity
  rintro y ⟨hy0, hyB⟩
  have hpx : payoff R β i x = ∑ j, (R j - (total x j - x i j + x i j) / β j) * x i j := by
    have := payoff_update R β x i (x i)
    rw [Function.update_eq_self] at this
    exact this
  rw [payoff_update, hpx, ← sub_nonpos, ← Finset.sum_sub_distrib]
  calc ∑ j, ((R j - (total x j - x i j + y j) / β j) * y j
          - (R j - (total x j - x i j + x i j) / β j) * x i j)
        ≤ ∑ j, lam * (y j - x i j) :=
          Finset.sum_le_sum (fun j _ => kkt_coord _ _ _ _ _ _ (hβ j) hlam (hx j) (hy0 j))
    _ = lam * (∑ j, y j - ∑ j, x i j) := by
          rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
          simp [mul_sub]
    _ ≤ 0 := by
          rcases hcs with h0 | hb
          · simp [h0]
          · rw [hb]; exact mul_nonpos_of_nonneg_of_nonpos hlam (by linarith)

/-- variational inequality from Nash optimality -/
lemma vi_of_opt {N M : ℕ} (R β : Fin M → ℝ) (B : Fin N → ℝ) (hβ : ∀ j, 0 < β j)
    (x : Fin N → Fin M → ℝ) (i : Fin N) (hxi : x i ∈ feasible B i)
    (hopt : ∀ y ∈ feasible B i, payoff R β i (Function.update x i y) ≤ payoff R β i x)
    (z : Fin M → ℝ) (hz : z ∈ feasible B i) :
    ∑ j, (R j - (total x j + x i j) / β j) * (z j - x i j) ≤ 0 := by
  set A := ∑ j, (R j - (total x j + x i j) / β j) * (z j - x i j) with hA
  set C := ∑ j, (z j - x i j) ^ 2 / β j with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg (fun j _ => div_nonneg (sq_nonneg _) (hβ j).le)
  have key : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * A - t ^ 2 * C ≤ 0 := by
    intro t ht0 ht1
    set y : Fin M → ℝ := fun j => x i j + t * (z j - x i j) with hy
    have hyf : y ∈ feasible B i := by
      obtain ⟨hx0, hxB⟩ := hxi
      obtain ⟨hz0, hzB⟩ := hz
      refine ⟨fun j => ?_, ?_⟩
      · have : y j = (1 - t) * x i j + t * z j := by simp [hy]; ring
        rw [this]
        have := hx0 j; have := hz0 j
        positivity
      · have : ∑ j, y j = (1 - t) * ∑ j, x i j + t * ∑ j, z j := by
          simp only [hy, Finset.sum_add_distrib, Finset.mul_sum]
          rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun j _ => by ring)
        rw [this]
        nlinarith
    have h1 := hopt y hyf
    have hpx : payoff R β i x = ∑ j, (R j - (total x j - x i j + x i j) / β j) * x i j := by
      have := payoff_update R β x i (x i)
      rw [Function.update_eq_self] at this
      exact this
    rw [payoff_update, hpx, ← sub_nonpos, ← Finset.sum_sub_distrib] at h1
    have : ∑ j, ((R j - (total x j - x i j + y j) / β j) * y j
          - (R j - (total x j - x i j + x i j) / β j) * x i j) = t * A - t ^ 2 * C := by
      rw [hA, hC, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      have := (hβ j).ne'
      simp only [hy]
      field_simp
      ring
    linarith
  by_contra hpos
  push Not at hpos
  have hCA : 0 < C + A := by linarith
  set t := A / (C + A)
  have ht0 : 0 ≤ t := div_nonneg hpos.le hCA.le
  have ht1 : t ≤ 1 := by rw [div_le_one hCA]; linarith
  have := key t ht0 ht1
  have e : t * A - t ^ 2 * C = A * A * A / (C + A) ^ 2 := by
    simp only [t]; field_simp; ring
  rw [e] at this
  have : 0 < A * A * A / (C + A) ^ 2 := by positivity
  linarith

theorem ne_unique {N M : ℕ} (R β : Fin M → ℝ) (B : Fin N → ℝ) (hβ : ∀ j, 0 < β j)
    (x x' : Fin N → Fin M → ℝ) (hx : IsCournotEq R β B x) (hx' : IsCournotEq R β B x') :
    x = x' := by
  obtain ⟨hxf, hxo⟩ := hx
  obtain ⟨hxf', hxo'⟩ := hx'
  have v1 : ∀ i, ∑ j, (R j - (total x j + x i j) / β j) * (x' i j - x i j) ≤ 0 :=
    fun i => vi_of_opt R β B hβ x i (hxf i) (hxo i) (x' i) (hxf' i)
  have v2 : ∀ i, ∑ j, (R j - (total x' j + x' i j) / β j) * (x i j - x' i j) ≤ 0 :=
    fun i => vi_of_opt R β B hβ x' i (hxf' i) (hxo' i) (x i) (hxf i)
  set d : Fin N → Fin M → ℝ := fun i j => x' i j - x i j with hd
  have hsum : ∑ i, ∑ j, ((total x' j - total x j) + d i j) * d i j / β j ≤ 0 := by
    have : ∀ i, ∑ j, ((total x' j - total x j) + d i j) * d i j / β j =
        ∑ j, (R j - (total x j + x i j) / β j) * (x' i j - x i j) +
          ∑ j, (R j - (total x' j + x' i j) / β j) * (x i j - x' i j) := by
      intro i
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      have := (hβ j).ne'
      simp only [hd]
      field_simp
      ring
    calc _ = ∑ i, (∑ j, (R j - (total x j + x i j) / β j) * (x' i j - x i j) +
          ∑ j, (R j - (total x' j + x' i j) / β j) * (x i j - x' i j)) :=
            Finset.sum_congr rfl (fun i _ => this i)
      _ ≤ 0 := Finset.sum_nonpos (fun i _ => by linarith [v1 i, v2 i])
  have hD : ∀ j, total x' j - total x j = ∑ i, d i j := by
    intro j; simp [total, hd, Finset.sum_sub_distrib]
  have hsplit : ∑ i, ∑ j, ((total x' j - total x j) + d i j) * d i j / β j =
      ∑ j, (∑ i, d i j) ^ 2 / β j + ∑ i, ∑ j, d i j ^ 2 / β j := by
    have e1 : ∀ i, ∑ j, ((total x' j - total x j) + d i j) * d i j / β j =
        ∑ j, (∑ k, d k j) * d i j / β j + ∑ j, d i j ^ 2 / β j := by
      intro i; rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hD j]; ring
    rw [Finset.sum_congr rfl (fun i _ => e1 i), Finset.sum_add_distrib, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Finset.sum_div, ← Finset.mul_sum]; ring
  rw [hsplit] at hsum
  have h1 : 0 ≤ ∑ j, (∑ i, d i j) ^ 2 / β j :=
    Finset.sum_nonneg (fun j _ => div_nonneg (sq_nonneg _) (hβ j).le)
  have h2 : ∀ i, 0 ≤ ∑ j, d i j ^ 2 / β j :=
    fun i => Finset.sum_nonneg (fun j _ => div_nonneg (sq_nonneg _) (hβ j).le)
  have h3 : ∑ i, ∑ j, d i j ^ 2 / β j = 0 :=
    le_antisymm (by linarith) (Finset.sum_nonneg (fun i _ => h2 i))
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => h2 i)] at h3
  funext i j
  have h4 := h3 i (mem_univ i)
  rw [Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => div_nonneg (sq_nonneg _) (hβ j).le)] at h4
  have h5 := h4 j (mem_univ j)
  rw [div_eq_zero_iff] at h5
  rcases h5 with h5 | h5
  · have : d i j = 0 := by simpa using h5
    simp only [hd] at this; linarith
  · exact absurd h5 (hβ j).ne'

end BCSol

namespace BCSol

open BudgetCournot.Equilibrium

lemma kkt_coord2 (R β O x y lam : ℝ) (hβ : 0 < β)
    (hx : x = max 0 (β * R - β * lam - O) / 2) (hy : 0 ≤ y) :
    (R - (O + y) / β) * y - (R - (O + x) / β) * x ≤ lam * (y - x) - (y - x) ^ 2 / β := by
  rcases le_total (β * R - β * lam - O) 0 with h | h
  · rw [max_eq_left h] at hx
    have hx0 : x = 0 := by linarith
    subst hx0
    have : R - O / β ≤ lam := by
      have e : R - O / β - lam = (β * R - β * lam - O) / β := by field_simp; ring
      have : (β * R - β * lam - O) / β ≤ 0 := div_nonpos_of_nonpos_of_nonneg h hβ.le
      linarith
    have e2 : (R - (O + y) / β) * y - (R - (O + 0) / β) * 0 = (R - O / β) * y - (y - 0) ^ 2 / β := by
      field_simp; ring
    rw [e2]
    nlinarith
  · rw [max_eq_right h] at hx
    have hg : R - (O + 2 * x) / β = lam := by
      field_simp
      linarith
    have key : (R - (O + y) / β) * y - (R - (O + x) / β) * x
        = (R - (O + 2 * x) / β) * (y - x) - (y - x) ^ 2 / β := by
      field_simp; ring
    rw [key, hg]

theorem br_strong {N M : ℕ} (R β : Fin M → ℝ) (B : Fin N → ℝ) (hβ : ∀ j, 0 < β j)
    (x : Fin N → Fin M → ℝ) (i : Fin N) (lam : ℝ) (h : IsBR R β B i x lam)
    (y : Fin M → ℝ) (hy : y ∈ feasible B i) :
    payoff R β i (Function.update x i y) - payoff R β i x ≤ - ∑ j, (y j - x i j) ^ 2 / β j := by
  obtain ⟨hlam, hx, hsum, hcs⟩ := h
  obtain ⟨hy0, hyB⟩ := hy
  have hpx : payoff R β i x = ∑ j, (R j - (total x j - x i j + x i j) / β j) * x i j := by
    have := payoff_update R β x i (x i)
    rw [Function.update_eq_self] at this
    exact this
  rw [payoff_update, hpx, ← Finset.sum_sub_distrib]
  calc ∑ j, ((R j - (total x j - x i j + y j) / β j) * y j
          - (R j - (total x j - x i j + x i j) / β j) * x i j)
        ≤ ∑ j, (lam * (y j - x i j) - (y j - x i j) ^ 2 / β j) :=
          Finset.sum_le_sum (fun j _ => kkt_coord2 _ _ _ _ _ _ (hβ j) (hx j) (hy0 j))
    _ = lam * (∑ j, y j - ∑ j, x i j) - ∑ j, (y j - x i j) ^ 2 / β j := by
          rw [Finset.sum_sub_distrib, mul_sub, Finset.mul_sum, Finset.mul_sum,
            ← Finset.sum_sub_distrib]
          simp [mul_sub]
    _ ≤ - ∑ j, (y j - x i j) ^ 2 / β j := by
          have : lam * (∑ j, y j - ∑ j, x i j) ≤ 0 := by
            rcases hcs with h0 | hb
            · simp [h0]
            · rw [hb]; exact mul_nonpos_of_nonneg_of_nonpos hlam (by linarith)
          linarith

end BCSol

open BudgetCournot.Equilibrium in
theorem solution {N M : ℕ} (R β : Fin M → ℝ) (B : Fin N → ℝ) (hS : Standing R β B)
    (x : Fin N → Fin M → ℝ) (i : Fin N) :
    (x i ∈ feasible B i ∧
        ∀ y ∈ feasible B i, payoff R β i (Function.update x i y) ≤ payoff R β i x) ↔
      ∃ lam : ℝ, IsBR R β B i x lam := by
  have hβ : ∀ j, 0 < β j := hS.2.2.1
  have hBpos : 0 < B i := hS.2.2.2.2 i
  constructor
  · rintro ⟨hxf, hopt⟩
    set O : Fin M → ℝ := fun j => total x j - x i j with hO
    set w : ℝ → Fin M → ℝ := fun l j => max 0 (β j * R j - β j * l - O j) / 2 with hw
    set φ : ℝ → ℝ := fun l => ∑ j, w l j with hφ
    have hφc : Continuous φ := by
      simp only [hφ, hw]
      fun_prop
    -- choose the multiplier
    obtain ⟨lam, hlam0, hφle, hcs⟩ : ∃ lam : ℝ, 0 ≤ lam ∧ φ lam ≤ B i ∧ (lam = 0 ∨ φ lam = B i) := by
      by_cases h0 : φ 0 ≤ B i
      · exact ⟨0, le_rfl, h0, Or.inl rfl⟩
      · push Not at h0
        set L : ℝ := ∑ j, |R j - O j / β j| with hL
        have hL0 : 0 ≤ L := Finset.sum_nonneg (fun j _ => abs_nonneg _)
        have hφL : φ L = 0 := by
          simp only [hφ, hw]
          apply Finset.sum_eq_zero
          intro j _
          have h1 : R j - O j / β j ≤ L := by
            calc R j - O j / β j ≤ |R j - O j / β j| := le_abs_self _
              _ ≤ L := Finset.single_le_sum (f := fun j => |R j - O j / β j|)
                    (fun k _ => abs_nonneg _) (mem_univ j)
          have hbj := hβ j
          have h2 : β j * R j - β j * L - O j ≤ 0 := by
            have e : β j * R j - β j * L - O j = β j * (R j - O j / β j - L) := by
              field_simp; ring
            rw [e]
            exact mul_nonpos_of_nonneg_of_nonpos hbj.le (by linarith)
          rw [max_eq_left h2]; simp
        have hmem : B i ∈ Set.Icc (φ L) (φ 0) := ⟨by rw [hφL]; exact hBpos.le, h0.le⟩
        obtain ⟨l, ⟨hl0, _⟩, hl⟩ := intermediate_value_Icc' hL0 hφc.continuousOn hmem
        exact ⟨l, hl0, hl.le, Or.inr hl⟩
    -- the KKT point is a best response; uniqueness gives x i = w lam
    set y : Fin M → ℝ := w lam with hy
    have hyf : y ∈ feasible B i := ⟨fun j => by simp only [hy, hw]; positivity, hφle⟩
    set x' := Function.update x i y with hx'
    have hBR' : IsBR R β B i x' lam := by
      refine ⟨hlam0, fun j => ?_, ?_, ?_⟩
      · rw [hx', BCSol.total_update, Function.update_self]
        simp only [hy, hw, hO]
        ring_nf
      · rw [hx', Function.update_self]; exact hφle
      · rw [hx', Function.update_self]; exact hcs
    have hs := BCSol.br_strong R β B hβ x' i lam hBR' (x i) hxf
    have hupd : Function.update x' i (x i) = x := by
      rw [hx', Function.update_idem, Function.update_eq_self]
    rw [hupd] at hs
    have hle := hopt y hyf
    have hx'i : x' i = y := by rw [hx', Function.update_self]
    rw [hx'i] at hs
    have hsum0 : ∑ j, (x i j - y j) ^ 2 / β j = 0 := by
      have : 0 ≤ ∑ j, (x i j - y j) ^ 2 / β j :=
        Finset.sum_nonneg (fun j _ => div_nonneg (sq_nonneg _) (hβ j).le)
      linarith
    rw [Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => div_nonneg (sq_nonneg _) (hβ j).le)] at hsum0
    have hxy : x i = y := by
      funext j
      have h5 := hsum0 j (mem_univ j)
      rw [div_eq_zero_iff] at h5
      rcases h5 with h5 | h5
      · have : x i j - y j = 0 := by simpa using h5
        linarith
      · exact absurd h5 (hβ j).ne'
    have hxx : x' = x := by rw [hx', ← hxy, Function.update_eq_self]
    rw [hxx] at hBR'
    exact ⟨lam, hBR'⟩
  · rintro ⟨lam, h⟩
    exact BCSol.br_suff R β B hβ x i lam h
