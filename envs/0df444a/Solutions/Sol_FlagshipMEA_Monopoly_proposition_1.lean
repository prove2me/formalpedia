-- Prove2me | solution 1 for FlagshipMEA.Monopoly.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T18:04:15.494057+00:00
-- url     : https://prove2.me/submissions/c286fb11-fa47-44ec-9e1e-557a250dff39

import Mathlib
import Definitions.Def_FlagshipMEA_Monopoly_Model
import Theorems.Thm_FlagshipMEA_Monopoly_lemma_4
import Theorems.Thm_FlagshipMEA_Monopoly_lemma_5
import Theorems.Thm_FlagshipMEA_Monopoly_lemma_6
import Theorems.Thm_FlagshipMEA_Monopoly_proposition_2

open FlagshipMEA.Monopoly

/-- A convex, strictly increasing function on `[θ, ∞)` grows at least linearly. -/
private lemma convex_linear_growth {c : ℝ → ℝ} {θ : ℝ} (hconv : ConvexOn ℝ (Set.Ici θ) c)
    {x : ℝ} (hx : θ + 1 ≤ x) :
    c θ + (c (θ + 1) - c θ) * (x - θ) ≤ c x := by
  have hxθ : 0 < x - θ := by linarith
  set t := 1 / (x - θ) with ht
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := by rw [ht, div_le_one hxθ]; linarith
  have h := hconv.2 ((Set.mem_Ici.mpr le_rfl)) (show x ∈ Set.Ici θ by simp; linarith)
    (sub_nonneg.mpr ht1) ht0 (by ring)
  have e : (1 - t) • θ + t • x = θ + 1 := by
    simp only [smul_eq_mul, ht]; field_simp; ring
  rw [e] at h
  simp only [smul_eq_mul] at h
  -- h : c (θ+1) ≤ (1 - t) * c θ + t * c x
  have : (c (θ + 1) - c θ) * (x - θ) ≤ (c x - c θ) := by
    have h2 : (c (θ + 1) - c θ) ≤ t * (c x - c θ) := by linarith
    have h3 := mul_le_mul_of_nonneg_right h2 hxθ.le
    have : t * (c x - c θ) * (x - θ) = c x - c θ := by rw [ht]; field_simp
    linarith
  linarith

/-- Existence of an optimal allocation. -/
private lemma exists_optimal {n : ℕ} (D : Data n) (hS : D.Standing) :
    ∃ m, D.IsOptimal m := by
  obtain ⟨hlam, hmk, hmono, hconv, hC1⟩ := hS
  set b := D.base with hb
  have hb0 : 0 < b := Real.exp_pos _
  have hlb : D.lam * Real.log b = D.θ := by
    rw [hb]; unfold Data.base; rw [Real.log_exp]; field_simp
  set P : ℝ := ∑ i, D.markup i with hP
  have hP0 : 0 ≤ P := Finset.sum_nonneg (fun i _ => (hmk i).le)
  set s : ℝ := D.c (D.θ + 1) - D.c D.θ with hs
  have hs0 : 0 < s := by
    have := hmono ((Set.mem_Ici.mpr le_rfl)) (show D.θ + 1 ∈ Set.Ici D.θ by simp)
      (by linarith)
    linarith
  set X : ℝ := D.θ + 1 + P / s with hX
  set R : ℝ := Real.exp (X / D.lam) with hR
  have hR0 : 0 < R := Real.exp_pos _
  -- the argument of `c` lies in `[θ, ∞)`
  have harg : ∀ y : ℝ, 0 ≤ y → D.θ ≤ D.lam * Real.log (y + b) := by
    intro y hy
    rw [← hlb]
    have := Real.log_le_log hb0 (show b ≤ y + b by linarith)
    exact mul_le_mul_of_nonneg_left this hlam.le
  -- revenue bounds
  have hrev : ∀ m : Fin n → ℝ, Feasible m → 0 ≤ D.revenue m ∧ D.revenue m ≤ P := by
    intro m hm
    have hw : ∀ i, 0 < D.attraction m i := fun i =>
      mul_pos (by linarith [hm i]) (Real.exp_pos _)
    have hden : 0 < (∑ j, D.attraction m j) + 1 := by
      have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => (hw j).le)
      linarith
    have hsh : ∀ i, 0 ≤ logitShare (D.attraction m) i ∧ logitShare (D.attraction m) i ≤ 1 := by
      intro i
      unfold logitShare
      refine ⟨div_nonneg (hw i).le hden.le, ?_⟩
      rw [div_le_one hden]
      have := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => (hw j).le) (Finset.mem_univ i)
      linarith
    unfold Data.revenue
    constructor
    · exact Finset.sum_nonneg (fun i _ => mul_nonneg (hmk i).le (hsh i).1)
    · rw [hP]
      apply Finset.sum_le_sum
      intro i _
      have := mul_le_mul_of_nonneg_left (hsh i).2 (hmk i).le
      linarith
  -- cost of the zero allocation
  have hcost0 : D.cost 0 = ∑ _i : Fin n, D.c D.θ := by
    unfold Data.cost
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [← hb, hlb]
  -- coercivity: allocations outside the box are worse than zero
  have hout : ∀ m : Fin n → ℝ, Feasible m → ∀ i, R < m i → D.profit m < D.profit 0 := by
    intro m hm i hi
    have hterm : ∀ j, D.c D.θ ≤ D.c (D.lam * Real.log (m j + b)) := by
      intro j
      exact hmono.monotoneOn (Set.mem_Ici.mpr le_rfl) (harg (m j) (hm j)) (harg (m j) (hm j))
    have hxi : X < D.lam * Real.log (m i + b) := by
      have h1 : X / D.lam < Real.log (m i + b) := by
        rw [Real.lt_log_iff_exp_lt (by linarith [hm i])]
        linarith
      have := mul_lt_mul_of_pos_left h1 hlam
      rwa [mul_div_cancel₀ _ hlam.ne'] at this
    have hgrow := convex_linear_growth hconv (x := D.lam * Real.log (m i + b))
      (by have : D.θ + 1 ≤ X := by rw [hX]; have := div_nonneg hP0 hs0.le; linarith
          linarith)
    have hbig : D.c D.θ + P < D.c (D.lam * Real.log (m i + b)) := by
      have : s * (X - D.θ) = s + P := by rw [hX]; field_simp; ring
      have h2 : s * (X - D.θ) < s * (D.lam * Real.log (m i + b) - D.θ) :=
        mul_lt_mul_of_pos_left (by linarith) hs0
      rw [← hs] at hgrow
      nlinarith
    have hsum : (∑ _j : Fin n, D.c D.θ) + P < D.cost m := by
      unfold Data.cost
      have hnn : ∀ j ∈ (Finset.univ : Finset (Fin n)), 0 ≤ D.c (D.lam * Real.log (m j + b)) - D.c D.θ :=
        fun j _ => sub_nonneg.mpr (hterm j)
      have h1 := Finset.single_le_sum hnn (Finset.mem_univ i)
      have h2 : ∑ j, (D.c (D.lam * Real.log (m j + b)) - D.c D.θ)
          = ∑ j, D.c (D.lam * Real.log (m j + b)) - ∑ j : Fin n, D.c D.θ :=
        Finset.sum_sub_distrib _ _
      linarith
    have hr := hrev m hm
    have hr0 := hrev 0 (fun _ => le_refl 0)
    unfold Data.profit
    linarith
  -- compactness
  set K : Set (Fin n → ℝ) := Set.Icc 0 (fun _ => R) with hK
  have hKc : IsCompact K := isCompact_Icc
  have h0K : (0 : Fin n → ℝ) ∈ K := ⟨le_refl _, fun _ => hR0.le⟩
  have hKfeas : ∀ m ∈ K, Feasible m := fun m hm i => hm.1 i
  have hcont : ContinuousOn D.profit K := by
    unfold Data.profit Data.revenue Data.cost
    apply ContinuousOn.sub
    · apply continuousOn_finsetSum
      intro i _
      apply ContinuousOn.mul continuousOn_const
      unfold logitShare Data.attraction
      apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro m hm
      have hw : ∀ j, 0 < (m j + D.base) * Real.exp (D.u j / D.lam) := fun j =>
        mul_pos (by linarith [hKfeas m hm j]) (Real.exp_pos _)
      have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => (hw j).le)
      linarith
    · apply continuousOn_finsetSum
      intro i _
      have hg : ContinuousOn (fun m : Fin n → ℝ => D.lam * Real.log (m i + D.base)) K := by
        apply ContinuousOn.mul continuousOn_const
        apply ContinuousOn.log (by fun_prop)
        intro m hm
        have := hKfeas m hm i
        linarith
      exact hC1.continuousOn.comp hg (fun m hm => harg (m i) (hKfeas m hm i))
  obtain ⟨x, hxK, hxmax⟩ := hKc.exists_isMaxOn ⟨0, h0K⟩ hcont
  refine ⟨x, hKfeas x hxK, fun m' hm' => ?_⟩
  by_cases hin : m' ∈ K
  · exact hxmax hin
  · have : ∃ i, R < m' i := by
      by_contra hcon
      push Not at hcon
      exact hin ⟨fun i => hm' i, fun i => hcon i⟩
    obtain ⟨i, hi⟩ := this
    have h1 := hout m' hm' i hi
    have h2 : D.profit 0 ≤ D.profit x := hxmax h0K
    linarith

theorem solution {n : ℕ} (D : Data n) (hS : D.Standing) (hfc : D.FcConcave) :
    (∃ m, D.IsOptimal m) ∧
    (∃ m, D.IsOptimal m ∧ (IsConcentrated m ∨ m = 0)) ∧
    (D.Distinct → ∀ m, D.IsOptimal m → IsConcentrated m ∨ m = 0) := by
  -- zero total effort forces the zero allocation
  have hzero : ∀ m : Fin n → ℝ, Feasible m → ¬ 0 < tme m → m = 0 := by
    intro m hm hM
    have h0 : tme m = 0 := le_antisymm (not_lt.mp hM) (Finset.sum_nonneg (fun i _ => hm i))
    funext i
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hm j)).mp h0 i (Finset.mem_univ i)
  obtain ⟨m0, hm0⟩ := exists_optimal D hS
  refine ⟨⟨m0, hm0⟩, ?_, ?_⟩
  · by_cases hM : 0 < tme m0
    · have hn : 0 < n := by
        rcases Nat.eq_zero_or_pos n with h | h
        · subst h; simp [tme] at hM
        · exact h
      obtain ⟨k0, -, hrev0, -⟩ := lemma_4 D hS hn (tme m0) hM
      set mk : Fin n → ℝ := fun j => if j = k0 then tme m0 else 0 with hmk
      have hfeas : Feasible mk := by
        intro j; rw [hmk]; dsimp only; split_ifs <;> linarith
      have hc := lemma_5 D hS hfc (tme m0) hM.le k0 m0 hm0.1 rfl
      have hr := hrev0 m0 hm0.1 rfl
      refine ⟨mk, ⟨hfeas, fun m' hm' => ?_⟩, Or.inl ⟨k0, by simp [hmk, hM], fun j hj => by simp [hmk, hj]⟩⟩
      have := hm0.2 m' hm'
      unfold Data.profit at this ⊢
      linarith
    · exact ⟨m0, hm0, Or.inr (hzero m0 hm0.1 hM)⟩
  · intro hD m hm
    by_cases hM : 0 < tme m
    · left
      obtain ⟨i, hi⟩ : ∃ i, 0 < m i := by
        by_contra hcon
        push Not at hcon
        have : tme m ≤ 0 := Finset.sum_nonpos (fun i _ => hcon i)
        linarith
      have hn : 0 < n := Fin.pos i
      obtain ⟨i0, -, huniq⟩ := lemma_6 D hS hfc hD hn m hm hM
      have hpos : ∀ j, 0 < m j → j = i0 := fun j hj =>
        huniq j (proposition_2 D hS hfc m hm j hj)
      refine ⟨i, hi, fun j hj => ?_⟩
      rcases lt_or_eq_of_le (hm.1 j) with h | h
      · exact absurd ((hpos j h).trans (hpos i hi).symm) hj
      · exact h.symm
    · exact Or.inr (hzero m hm.1 hM)
