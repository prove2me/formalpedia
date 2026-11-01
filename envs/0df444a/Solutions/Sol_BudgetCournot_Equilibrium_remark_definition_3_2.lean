-- Prove2me | solution 1 for BudgetCournot.Equilibrium.remark_definition_3_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T21:15:24.852957+00:00
-- url     : https://prove2.me/submissions/1f36b516-2bc5-4faf-a995-e5c0c9df88de

import Mathlib
import Definitions.Def_BudgetCournot_Equilibrium_Model
import Theorems.Thm_BudgetCournot_Equilibrium_H_least_feasible_B17

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

open Finset

namespace BCSol

open BudgetCournot.Equilibrium

noncomputable def Ssum {N : ℕ} (α : Fin N → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ univ.filter (fun k : Fin N => (k : ℕ) < n),
    α k / (((k : ℕ) + 1 : ℝ) * ((k : ℕ) + 2 : ℝ))

noncomputable def lamv {N : ℕ} (α : Fin N → ℝ) (i : Fin N) : ℝ :=
  α i / ((i : ℕ) + 2 : ℝ) + ∑ k ∈ univ.filter (fun k : Fin N => k ≤ i),
    α k / (((k : ℕ) + 1 : ℝ) * ((k : ℕ) + 2 : ℝ))

noncomputable def cv {N : ℕ} (α : Fin N → ℝ) (r : ℝ) (n : ℕ) : ℝ :=
  r / (1 + (n : ℝ)) + Ssum α n

lemma closedForm_eq {N M : ℕ} (R β : Fin M → ℝ) (α : Fin N → ℝ) (n : Fin M → ℕ)
    (i : Fin N) (j : Fin M) :
    closedForm R β α n i j = β j * max 0 (cv α (R j) (n j) - lamv α i) := by
  unfold closedForm cv lamv Ssum
  congr 2
  ring

lemma filter_lt_succ {N : ℕ} (i : Fin N) :
    univ.filter (fun k : Fin N => (k : ℕ) < (i : ℕ) + 1) =
      insert i (univ.filter (fun k : Fin N => (k : ℕ) < (i : ℕ))) := by
  ext k; simp [Fin.ext_iff]; omega

lemma filter_le_eq {N : ℕ} (i : Fin N) :
    univ.filter (fun k : Fin N => k ≤ i) =
      univ.filter (fun k : Fin N => (k : ℕ) < (i : ℕ) + 1) := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [Fin.le_def]; omega

lemma filter_gt_succ {N : ℕ} (i i' : Fin N) (h : (i' : ℕ) = (i : ℕ) + 1) :
    univ.filter (fun k : Fin N => i < k) =
      insert i' (univ.filter (fun k : Fin N => i' < k)) := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  rw [Fin.lt_def, Fin.lt_def, Fin.ext_iff]; omega

lemma Ssum_succ {N : ℕ} (α : Fin N → ℝ) (i : Fin N) :
    Ssum α ((i : ℕ) + 1) = Ssum α (i : ℕ) + α i / (((i : ℕ) + 1 : ℝ) * ((i : ℕ) + 2 : ℝ)) := by
  unfold Ssum
  rw [filter_lt_succ, Finset.sum_insert (by simp)]
  ring

lemma Ssum_zero {N : ℕ} (α : Fin N → ℝ) : Ssum α 0 = 0 := by
  unfold Ssum; simp

lemma lamv_eq {N : ℕ} (α : Fin N → ℝ) (i : Fin N) :
    lamv α i = α i / ((i : ℕ) + 2 : ℝ) + Ssum α ((i : ℕ) + 1) := by
  unfold lamv Ssum; rw [filter_le_eq]

lemma L2 {N : ℕ} (α : Fin N → ℝ) (r : ℝ) (i : Fin N) :
    cv α r ((i : ℕ) + 1) - lamv α i = (r - α i) / ((i : ℕ) + 2 : ℝ) := by
  rw [lamv_eq]; unfold cv; push_cast
  have : (1 + ((i : ℕ) + 1 : ℝ)) = ((i : ℕ) + 2 : ℝ) := by ring
  rw [this]; ring

lemma L3 {N : ℕ} (α : Fin N → ℝ) (r : ℝ) (i : Fin N) :
    cv α r (i : ℕ) - lamv α i = (r - α i) / ((i : ℕ) + 1 : ℝ) := by
  rw [lamv_eq, Ssum_succ]; unfold cv
  have h1 : (0 : ℝ) < ((i : ℕ) : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) < ((i : ℕ) : ℝ) + 2 := by positivity
  field_simp; ring

lemma L1 {N : ℕ} (α : Fin N → ℝ) (i i' : Fin N) (h : (i' : ℕ) = (i : ℕ) + 1) :
    ((i : ℕ) + 2 : ℝ) * (lamv α i' - lamv α i) = α i' - α i := by
  rw [lamv_eq, lamv_eq, Ssum_succ α i', h]
  push_cast
  have h1 : (0 : ℝ) < ((i : ℕ) : ℝ) + 2 := by positivity
  have h2 : (0 : ℝ) < ((i : ℕ) : ℝ) + 1 + 2 := by positivity
  have h3 : (0 : ℝ) < ((i : ℕ) : ℝ) + 1 + 1 := by positivity
  field_simp; ring

lemma monotone_of_succ {N : ℕ} (f : Fin N → ℝ)
    (h : ∀ i i' : Fin N, (i' : ℕ) = (i : ℕ) + 1 → f i ≤ f i') : Monotone f := by
  have key : ∀ d : ℕ, ∀ i i' : Fin N, (i' : ℕ) = (i : ℕ) + d → f i ≤ f i' := by
    intro d
    induction d with
    | zero => intro i i' hii; rw [Fin.ext ((by omega) : (i' : ℕ) = i)]
    | succ d ih =>
      intro i i' hii
      have hlt : (i : ℕ) + d < N := by have := i'.isLt; omega
      exact le_trans (ih i ⟨(i : ℕ) + d, hlt⟩ rfl) (h _ _ (by simp; omega))
  intro i i' hle
  exact key ((i' : ℕ) - i) i i' (by rw [Fin.le_def] at hle; omega)

lemma lamv_mono {N : ℕ} (α : Fin N → ℝ) (hα : Monotone α) : Monotone (lamv α) := by
  apply monotone_of_succ
  intro i i' h
  have e := L1 α i i' h
  have hii : α i ≤ α i' := hα (by rw [Fin.le_def]; omega)
  have hpos : (0 : ℝ) < ((i : ℕ) : ℝ) + 2 := by positivity
  nlinarith

/-- the per-market structure -/
lemma market {N : ℕ} (α : Fin N → ℝ) (hα : Monotone α) (r : ℝ) (n : ℕ) (hn : n ≤ N)
    (hlo : ∀ i : Fin N, (i : ℕ) < n → α i ≤ r) (hhi : ∀ i : Fin N, n ≤ (i : ℕ) → r ≤ α i) :
    (∀ i : Fin N, (i : ℕ) < n → lamv α i ≤ cv α r n) ∧
    (∀ i : Fin N, n ≤ (i : ℕ) → cv α r n ≤ lamv α i) ∧
    (∀ i : Fin N, ((i : ℕ) + 2 : ℝ) * max 0 (cv α r n - lamv α i)
        + ∑ k ∈ univ.filter (fun k => i < k), max 0 (cv α r n - lamv α k)
        = max (r - α i) 0) ∧
    (∀ _i : Fin N, ∑ k, max 0 (cv α r n - lamv α k) = r - cv α r n) := by
  have hlm := lamv_mono α hα
  have Q1 : ∀ i : Fin N, (i : ℕ) < n → lamv α i ≤ cv α r n := by
    intro i hi
    set m : Fin N := ⟨n - 1, by omega⟩
    have hm : (m : ℕ) + 1 = n := by simp [m]; omega
    have e := L2 α r m
    rw [hm] at e
    have h1 : lamv α i ≤ lamv α m := hlm (by rw [Fin.le_def]; simp [m]; omega)
    have h2 : α m ≤ r := hlo m (by omega)
    have h3 : 0 ≤ (r - α m) / ((m : ℕ) + 2 : ℝ) := div_nonneg (by linarith) (by positivity)
    linarith
  have Q2 : ∀ i : Fin N, n ≤ (i : ℕ) → cv α r n ≤ lamv α i := by
    intro i hi
    set m : Fin N := ⟨n, by have := i.isLt; omega⟩
    have e := L3 α r m
    have hmn : (m : ℕ) = n := rfl
    rw [hmn] at e
    have h1 : lamv α m ≤ lamv α i := hlm (by rw [Fin.le_def]; simp [m]; omega)
    have h2 : r ≤ α m := hhi m (by simp [m])
    have h3 : (r - α m) / ((n : ℕ) + 1 : ℝ) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    linarith
  have P0 : ∀ i : Fin N, n ≤ (i : ℕ) → max 0 (cv α r n - lamv α i) = 0 := by
    intro i hi; exact max_eq_left (by linarith [Q2 i hi])
  have P1 : ∀ i : Fin N, (i : ℕ) < n → max 0 (cv α r n - lamv α i) = cv α r n - lamv α i := by
    intro i hi; exact max_eq_right (by linarith [Q1 i hi])
  have Q3 : ∀ i : Fin N, ((i : ℕ) + 2 : ℝ) * max 0 (cv α r n - lamv α i)
        + ∑ k ∈ univ.filter (fun k => i < k), max 0 (cv α r n - lamv α k)
        = max (r - α i) 0 := by
    have key : ∀ d : ℕ, ∀ i : Fin N, (i : ℕ) + 1 + d = N →
        ((i : ℕ) + 2 : ℝ) * max 0 (cv α r n - lamv α i)
        + ∑ k ∈ univ.filter (fun k => i < k), max 0 (cv α r n - lamv α k)
        = max (r - α i) 0 := by
      intro d
      induction d with
      | zero =>
        intro i hi
        have hemp : univ.filter (fun k : Fin N => i < k) = ∅ := by
          ext k
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
          rw [Fin.lt_def]; have := k.isLt; omega
        rw [hemp, Finset.sum_empty, add_zero]
        rcases lt_or_ge (i : ℕ) n with h | h
        · rw [P1 i h]
          have hn' : n = (i : ℕ) + 1 := by omega
          rw [hn', L2, max_eq_left (by linarith [hlo i h])]
          have : (0 : ℝ) < ((i : ℕ) : ℝ) + 2 := by positivity
          field_simp
        · rw [P0 i h, max_eq_right (by linarith [hhi i h])]; ring
      | succ d ih =>
        intro i hi
        set i' : Fin N := ⟨(i : ℕ) + 1, by omega⟩
        have hii : (i' : ℕ) = (i : ℕ) + 1 := rfl
        have IH := ih i' (by rw [hii]; omega)
        rw [filter_gt_succ i i' hii, Finset.sum_insert (by simp)]
        have eL1 := L1 α i i' hii
        rw [hii] at IH
        push_cast at IH
        rcases lt_or_ge (i' : ℕ) n with h | h
        · have hi : (i : ℕ) < n := by omega
          rw [P1 i hi]
          rw [P1 i' h, max_eq_left (by linarith [hlo i' h])] at IH
          rw [P1 i' h, max_eq_left (by linarith [hlo i hi])]
          linarith
        · rcases lt_or_ge (i : ℕ) n with h' | h'
          · rw [P0 i' h, max_eq_right (by linarith [hhi i' h])] at IH
            rw [P0 i' h, P1 i h', max_eq_left (by linarith [hlo i h'])]
            have hn' : n = (i : ℕ) + 1 := by omega
            have e2 := L2 α r i
            rw [← hn'] at e2
            rw [e2]
            have : (0 : ℝ) < ((i : ℕ) : ℝ) + 2 := by positivity
            field_simp
            linarith
          · rw [P0 i' h, max_eq_right (by linarith [hhi i' h])] at IH
            rw [P0 i' h, P0 i h', max_eq_right (by linarith [hhi i h'])]
            linarith
    intro i
    exact key (N - 1 - (i : ℕ)) i (by have := i.isLt; omega)
  refine ⟨Q1, Q2, Q3, ?_⟩
  intro i
  have hN : 0 < N := by have := i.isLt; omega
  set i0 : Fin N := ⟨0, hN⟩
  have huniv : (univ : Finset (Fin N)) = insert i0 (univ.filter (fun k => i0 < k)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, true_iff]
    have h0 : (i0 : ℕ) = 0 := rfl
    rw [Fin.lt_def, Fin.ext_iff, h0]; omega
  have hl0 : lamv α i0 = α i0 := by
    have e := L3 α r i0
    have : ((i0 : ℕ)) = 0 := rfl
    rw [this] at e
    unfold cv at e
    rw [Ssum_zero] at e
    simp at e
    linarith
  rw [huniv, Finset.sum_insert (by simp)]
  have e := Q3 i0
  have : ((i0 : ℕ) : ℝ) = 0 := by simp [i0]
  rw [this] at e
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    rw [P0 i0 (by simp)] at e ⊢
    rw [max_eq_right (by linarith [hhi i0 (by simp)])] at e
    have : cv α r 0 = r := by unfold cv; rw [Ssum_zero]; simp
    rw [this] at e ⊢; linarith
  · rw [P1 i0 (by simp [i0]; omega)] at e ⊢
    rw [max_eq_left (by linarith [hlo i0 (by simp [i0]; omega)])] at e
    rw [hl0] at e ⊢
    linarith

end BCSol

open Finset

namespace BCSol

open BudgetCournot.Equilibrium

lemma H_anti {M : ℕ} (R β : Fin M → ℝ) (hR : Monotone R) (hR0 : ∀ j, 0 ≤ R j)
    (hβ : ∀ j, 0 < β j) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : H R β y ≤ H R β x := by
  obtain ⟨h0, hG, _, _⟩ := H_least_feasible_B17 R β hR hR0 hβ x hx
  exact (H_least_feasible_B17 R β hR hR0 hβ y (hx.trans hxy)).2.2.1 _ h0 (hG.trans hxy)

lemma G_R {M : ℕ} (R β : Fin M → ℝ) (hR : Monotone R) (j : Fin M) :
    ∑ k, β k * max (R k - R j) 0 = cutoffBudget R β j := by
  unfold cutoffBudget
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  split_ifs with h
  · rw [max_eq_left (by linarith [hR h])]
  · push Not at h
    rw [max_eq_right (by linarith [hR h.le])]; ring

lemma H_le_R {M : ℕ} (R β : Fin M → ℝ) (hR : Monotone R) (hR0 : ∀ j, 0 ≤ R j)
    (hβ : ∀ j, 0 < β j) (X : ℝ) (hX : 0 ≤ X) (j : Fin M) (h : cutoffBudget R β j < X) :
    H R β X ≤ R j :=
  (H_least_feasible_B17 R β hR hR0 hβ X hX).2.2.1 (R j) (hR0 j) (by rw [G_R R β hR]; exact h.le)

lemma R_le_H {M : ℕ} (R β : Fin M → ℝ) (hR : Monotone R) (hR0 : ∀ j, 0 ≤ R j)
    (hβ : ∀ j, 0 < β j) (X : ℝ) (hX : 0 ≤ X) (j : Fin M) (h : X ≤ cutoffBudget R β j) :
    R j ≤ H R β X := by
  by_contra hlt
  push Not at hlt
  obtain ⟨_, hG, _, _⟩ := H_least_feasible_B17 R β hR hR0 hβ X hX
  have : ∑ k, β k * max (R k - R j) 0 < ∑ k, β k * max (R k - H R β X) 0 := by
    apply Finset.sum_lt_sum
    · intro k _
      apply mul_le_mul_of_nonneg_left _ (hβ k).le
      exact max_le_max (by linarith) le_rfl
    · refine ⟨j, mem_univ _, ?_⟩
      rw [sub_self, max_self, max_eq_left (by linarith)]
      have := hβ j
      nlinarith
  rw [G_R R β hR] at this
  linarith

lemma aug_split {N : ℕ} (B : Fin N → ℝ) (i : Fin N) :
    augBudget B i = ((i : ℕ) + 2 : ℝ) * B i + ∑ k ∈ univ.filter (fun k => i < k), B k := by
  unfold augBudget
  have : univ.filter (fun k : Fin N => i ≤ k) = insert i (univ.filter (fun k => i < k)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    rw [Fin.le_def, Fin.lt_def, Fin.ext_iff]; omega
  rw [this, Finset.sum_insert (by simp)]
  ring

lemma aug_nonneg {N : ℕ} (B : Fin N → ℝ) (hB : ∀ i, 0 < B i) (i : Fin N) :
    0 ≤ augBudget B i := by
  unfold augBudget
  have h1 : 0 ≤ ((i : ℕ) + 1 : ℝ) * B i := mul_nonneg (by positivity) (hB i).le
  have h2 : 0 ≤ ∑ k ∈ univ.filter (fun k => i ≤ k), B k :=
    Finset.sum_nonneg (fun k _ => (hB k).le)
  linarith

lemma aug_anti {N : ℕ} (B : Fin N → ℝ) (hB : Antitone B) : Antitone (augBudget B) := by
  have hm : Monotone (fun i => - augBudget B i) := by
    apply monotone_of_succ
    intro i i' h
    rw [aug_split B i, aug_split B i', filter_gt_succ i i' h, Finset.sum_insert (by simp), h]
    have hle : B i' ≤ B i := hB (by rw [Fin.le_def]; omega)
    push_cast
    have : (0 : ℝ) ≤ ((i : ℕ) : ℝ) + 2 := by positivity
    nlinarith
  intro a b hab
  have := hm hab
  simp only at this
  linarith

lemma sup_char {N : ℕ} (P : Fin N → Prop) [DecidablePred P]
    (hP : ∀ i i' : Fin N, i ≤ i' → P i' → P i) (i : Fin N) :
    (i : ℕ) < (univ.filter P).sup (fun k => (k : ℕ) + 1) ↔ P i := by
  constructor
  · intro h
    rw [Finset.lt_sup_iff] at h
    obtain ⟨k, hk, hik⟩ := h
    rw [Finset.mem_filter] at hk
    exact hP i k (by rw [Fin.le_def]; omega) hk.2
  · intro h
    have := Finset.le_sup (f := fun k : Fin N => (k : ℕ) + 1)
      (Finset.mem_filter.2 ⟨mem_univ i, h⟩)
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) this

lemma sup_le_N {N : ℕ} (P : Fin N → Prop) [DecidablePred P] :
    (univ.filter P).sup (fun k => (k : ℕ) + 1) ≤ N :=
  Finset.sup_le (fun k _ => k.isLt)

theorem xStar_BR {N M : ℕ} (R β : Fin M → ℝ) (B : Fin N → ℝ) (hS : Standing R β B)
    (i : Fin N) :
    IsBR R β B i (xStar R β B) (lamv (fun k => H R β (augBudget B k)) i) := by
  obtain ⟨hR, hR0, hβ, hBa, hB⟩ := hS
  set α : Fin N → ℝ := fun k => H R β (augBudget B k) with hαdef
  have hB17 := fun k => H_least_feasible_B17 R β hR hR0 hβ (augBudget B k) (aug_nonneg B hB k)
  have hα0 : ∀ k, 0 ≤ α k := fun k => (hB17 k).1
  have hαm : Monotone α := by
    intro a b hab
    exact H_anti R β hR hR0 hβ (aug_nonneg B hB b) (aug_anti B hBa hab)
  -- per-market data
  have hmk := fun j : Fin M =>
    market α hαm (R j) (nStar R β B j)
      (sup_le_N (fun k : Fin N => cutoffBudget R β j < augBudget B k))
      (fun k hk => by
        have := (sup_char (fun k : Fin N => cutoffBudget R β j < augBudget B k)
          (fun a b hab hb => lt_of_lt_of_le hb (aug_anti B hBa hab)) k).1 hk
        exact H_le_R R β hR hR0 hβ _ (aug_nonneg B hB k) j this)
      (fun k hk => by
        have : ¬ (cutoffBudget R β j < augBudget B k) := fun h =>
          absurd ((sup_char (fun k : Fin N => cutoffBudget R β j < augBudget B k)
            (fun a b hab hb => lt_of_lt_of_le hb (aug_anti B hBa hab)) k).2 h)
            (by unfold nStar at hk; omega)
        push Not at this
        exact R_le_H R β hR hR0 hβ _ (aug_nonneg B hB k) j this)
  set c : Fin M → ℝ := fun j => cv α (R j) (nStar R β B j) with hc
  set p : Fin N → Fin M → ℝ := fun k j => max 0 (c j - lamv α k) with hp
  have hx : ∀ k j, xStar R β B k j = β j * p k j := by
    intro k j
    unfold xStar
    rw [closedForm_eq]
  have htot : ∀ j, total (xStar R β B) j = β j * (R j - c j) := by
    intro j
    unfold total
    simp only [hx]
    rw [← Finset.mul_sum]
    rw [(hmk j).2.2.2 i]
  -- KKT equation
  have hkkt : ∀ j, xStar R β B i j = max 0 (β j * R j - β j * lamv α i
      - (total (xStar R β B) j - xStar R β B i j)) / 2 := by
    intro j
    rw [htot, hx]
    have hbj := hβ j
    rcases le_total (lamv α i) (c j) with h | h
    · have hpij : p i j = c j - lamv α i := max_eq_right (by linarith)
      rw [hpij]
      rw [max_eq_right (by nlinarith)]
      ring
    · have hpij : p i j = 0 := max_eq_left (by linarith)
      rw [hpij]
      rw [max_eq_left (by nlinarith)]
      ring
  -- budget analysis
  set T : Fin N → ℝ := fun k => ∑ j, xStar R β B k j with hT
  set G : ℝ → ℝ := fun z => ∑ j, β j * max (R j - z) 0 with hG
  have hL1 : ∀ k : Fin N, ((k : ℕ) + 2 : ℝ) * T k + ∑ l ∈ univ.filter (fun l => k < l), T l
      = G (α k) := by
    intro k
    simp only [hT, hG, hx]
    rw [Finset.mul_sum, Finset.sum_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← (hmk j).2.2.1 k, mul_add, Finset.mul_sum]
    ring
  set D : Fin N → ℝ := fun k => B k - T k with hD
  have hE : ∀ k : Fin N, ((k : ℕ) + 2 : ℝ) * D k + ∑ l ∈ univ.filter (fun l => k < l), D l
      = augBudget B k - G (α k) := by
    intro k
    rw [aug_split, ← hL1 k]
    simp only [hD, Finset.sum_sub_distrib]
    ring
  have hE0 : ∀ k, 0 ≤ augBudget B k - G (α k) := fun k => by linarith [(hB17 k).2.1]
  have hEp : ∀ k, 0 < α k → augBudget B k - G (α k) = 0 := by
    intro k hk
    rcases (hB17 k).2.2.2 with h | h
    · exact absurd h (ne_of_gt hk)
    · simp only [hG]; rw [h]; ring
  have claimA : ∀ k, 0 < α k → D k = 0 := by
    have key : ∀ d : ℕ, ∀ k : Fin N, N ≤ (k : ℕ) + 1 + d → 0 < α k → D k = 0 := by
      intro d
      induction d with
      | zero =>
        intro k hk hpos
        have hs : ∑ l ∈ univ.filter (fun l => k < l), D l = 0 := by
          apply Finset.sum_eq_zero
          intro l hl
          rw [Finset.mem_filter, Fin.lt_def] at hl
          have := l.isLt
          omega
        have := hE k
        rw [hs, hEp k hpos] at this
        have : (0 : ℝ) < ((k : ℕ) : ℝ) + 2 := by positivity
        nlinarith
      | succ d ih =>
        intro k hk hpos
        have hs : ∑ l ∈ univ.filter (fun l => k < l), D l = 0 := by
          apply Finset.sum_eq_zero
          intro l hl
          rw [Finset.mem_filter] at hl
          have hl' := hl.2
          rw [Fin.lt_def] at hl'
          exact ih l (by omega) (lt_of_lt_of_le hpos (hαm hl.2.le))
        have := hE k
        rw [hs, hEp k hpos] at this
        have : (0 : ℝ) < ((k : ℕ) : ℝ) + 2 := by positivity
        nlinarith
    intro k hk
    exact key N k (by omega) hk
  have lam0 : ∀ k, α k = 0 → lamv α k = 0 := by
    intro k hk
    unfold lamv
    rw [hk, zero_div, zero_add]
    apply Finset.sum_eq_zero
    intro l hl
    rw [Finset.mem_filter] at hl
    have : α l = 0 := le_antisymm (hk ▸ hαm hl.2) (hα0 l)
    rw [this, zero_div]
  have claimB : α i = 0 → 0 ≤ D i := by
    intro hi
    have hne : (univ.filter (fun k => α k ≤ 0)).Nonempty :=
      ⟨i, by rw [Finset.mem_filter]; exact ⟨mem_univ _, hi.le⟩⟩
    set m := (univ.filter (fun k => α k ≤ 0)).max' hne with hmdef
    have hmmem := Finset.max'_mem _ hne
    rw [← hmdef, Finset.mem_filter] at hmmem
    have hαm0 : α m = 0 := le_antisymm hmmem.2 (hα0 m)
    have him : i ≤ m := Finset.le_max' (univ.filter (fun k => α k ≤ 0)) i (by rw [Finset.mem_filter]; exact ⟨mem_univ _, hi.le⟩)
    have hgt : ∀ l, m < l → D l = 0 := by
      intro l hl
      apply claimA
      by_contra hle
      push Not at hle
      have : l ≤ m := Finset.le_max' (univ.filter (fun k => α k ≤ 0)) l
        (by rw [Finset.mem_filter]; exact ⟨mem_univ _, hle⟩)
      exact absurd hl (not_lt.2 this)
    have hs : ∑ l ∈ univ.filter (fun l => m < l), D l = 0 := by
      apply Finset.sum_eq_zero
      intro l hl
      rw [Finset.mem_filter] at hl
      exact hgt l hl.2
    have hEm := hE m
    rw [hs, add_zero] at hEm
    have hDm : 0 ≤ D m := by
      have := hE0 m
      have : (0 : ℝ) < ((m : ℕ) : ℝ) + 2 := by positivity
      nlinarith
    have hTim : T i = T m := by
      simp only [hT, hx, hp]
      rw [lam0 i hi, lam0 m hαm0]
    have hBim : B m ≤ B i := hBa him
    simp only [hD] at hDm ⊢
    rw [hTim]
    linarith
  refine ⟨?_, hkkt, ?_, ?_⟩
  · unfold lamv
    have h1 : 0 ≤ α i / ((i : ℕ) + 2 : ℝ) := div_nonneg (hα0 i) (by positivity)
    have h2 : 0 ≤ ∑ k ∈ univ.filter (fun k : Fin N => k ≤ i),
        α k / (((k : ℕ) + 1 : ℝ) * ((k : ℕ) + 2 : ℝ)) :=
      Finset.sum_nonneg (fun k _ => div_nonneg (hα0 k) (by positivity))
    linarith
  · rcases (hα0 i).lt_or_eq with h | h
    · have := claimA i h
      simp only [hD, hT] at this
      linarith
    · have := claimB h.symm
      simp only [hD, hT] at this
      linarith
  · rcases (hα0 i).lt_or_eq with h | h
    · right
      have := claimA i h
      simp only [hD, hT] at this
      linarith
    · left
      exact lam0 i h.symm

end BCSol

open BudgetCournot.Equilibrium in
theorem BCSol.main_thm {N M : ℕ} (R β : Fin M → ℝ) (B : Fin N → ℝ) (hS : Standing R β B)
    (x : Fin N → Fin M → ℝ) :
    IsCournotEq R β B x ↔ x = xStar R β B := by
  have hβ : ∀ j, 0 < β j := hS.2.2.1
  have hstar : IsCournotEq R β B (xStar R β B) := by
    unfold IsCournotEq CarbonDoubleCount.Planner.IsPureNash
    refine ⟨fun i => ?_, fun i => ?_⟩
    · exact (BCSol.br_suff R β B hβ _ i _ (BCSol.xStar_BR R β B hS i)).1
    · exact (BCSol.br_suff R β B hβ _ i _ (BCSol.xStar_BR R β B hS i)).2
  constructor
  · intro hx
    exact BCSol.ne_unique R β B hβ x _ hx hstar
  · rintro rfl
    exact hstar

namespace BCSol

open BudgetCournot.Equilibrium

lemma G_gap {M : ℕ} (R β : Fin M → ℝ) (hβ : ∀ j, 0 < β j) (w z : ℝ) (hwz : w ≤ z)
    (k : Fin M) (hk : z ≤ R k) :
    β k * (z - w) ≤ ∑ l, β l * max (R l - w) 0 - ∑ l, β l * max (R l - z) 0 := by
  rw [← Finset.sum_sub_distrib]
  have hnn : ∀ l ∈ (univ : Finset (Fin M)), 0 ≤ β l * max (R l - w) 0 - β l * max (R l - z) 0 := by
    intro l _
    rw [← mul_sub]
    exact mul_nonneg (hβ l).le (by
      have : max (R l - z) 0 ≤ max (R l - w) 0 := max_le_max (by linarith) le_rfl
      linarith)
  have := Finset.single_le_sum hnn (mem_univ k)
  rw [max_eq_left (by linarith), max_eq_left (by linarith)] at this
  linarith

end BCSol

open BudgetCournot.Equilibrium in
theorem solution {M : ℕ} (R β : Fin M → ℝ) (hR : Monotone R)
    (hR0 : ∀ j, 0 ≤ R j) (hβ : ∀ j, 0 < β j) :
    ContinuousOn (H R β) (Set.Ici 0) ∧ AntitoneOn (H R β) (Set.Ici 0) ∧
      (∃ T : Finset ℝ, ∀ a b : ℝ, 0 ≤ a → a ≤ b → (∀ t ∈ T, t ∉ Set.Ioo a b) →
        ∃ c d : ℝ, ∀ y ∈ Set.Icc a b, H R β y = c + d * y) ∧
      ∀ j, H R β (cutoffBudget R β j) = R j := by
  have B17 := fun x hx => H_least_feasible_B17 R β hR hR0 hβ x hx
  have hanti : AntitoneOn (H R β) (Set.Ici 0) := by
    intro x hx y _ hxy
    exact BCSol.H_anti R β hR hR0 hβ hx hxy
  have hcut : ∀ j, H R β (cutoffBudget R β j) = R j := by
    intro j
    have hB0 : 0 ≤ cutoffBudget R β j := by
      rw [← BCSol.G_R R β hR]
      exact Finset.sum_nonneg (fun k _ => mul_nonneg (hβ k).le (le_max_right _ _))
    apply le_antisymm
    · exact (B17 _ hB0).2.2.1 (R j) (hR0 j) (by rw [BCSol.G_R R β hR])
    · exact BCSol.R_le_H R β hR hR0 hβ _ hB0 j le_rfl
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM
    have hz : ∀ x, 0 ≤ x → H R β x = 0 := by
      intro x hx
      exact le_antisymm ((B17 x hx).2.2.1 0 le_rfl (by simp [hx])) (B17 x hx).1
    refine ⟨?_, hanti, ⟨∅, fun a b ha _ _ => ⟨0, 0, fun y hy => ?_⟩⟩, hcut⟩
    · exact (continuousOn_const (c := (0 : ℝ))).congr (fun x hx => hz x hx)
    · rw [hz y (le_trans ha hy.1)]; ring
  set kt : Fin M := ⟨M - 1, by omega⟩
  have hkt : ∀ l, R l ≤ R kt := fun l => hR (by rw [Fin.le_def]; simp [kt]; omega)
  have hbt := hβ kt
  have Htop : ∀ x, 0 ≤ x → H R β x ≤ R kt := by
    intro x hx
    refine (B17 x hx).2.2.1 (R kt) (hR0 kt) ?_
    have : ∑ j, β j * max (R j - R kt) 0 = 0 :=
      Finset.sum_eq_zero (fun l _ => by rw [max_eq_right (by linarith [hkt l])]; ring)
    rw [this]; exact hx
  -- Lipschitz bound
  have hlip : ∀ x y, 0 ≤ x → x ≤ y → H R β x - H R β y ≤ (y - x) / β kt := by
    intro x y hx hxy
    rcases le_or_gt (H R β x) (H R β y) with h | h
    · have : 0 ≤ (y - x) / β kt := div_nonneg (by linarith) hbt.le
      linarith
    · have hy := le_trans hx hxy
      have hbind : ∑ j, β j * max (R j - H R β x) 0 = x := by
        rcases (B17 x hx).2.2.2 with h0 | h0
        · have := (B17 y hy).1; linarith
        · exact h0
      have hGy := (B17 y hy).2.1
      have gap := BCSol.G_gap R β hβ (H R β y) (H R β x) h.le kt (Htop x hx)
      rw [le_div_iff₀ hbt]
      nlinarith
  have hcont : ContinuousOn (H R β) (Set.Ici 0) := by
    rw [Metric.continuousOn_iff]
    intro b hb ε hε
    refine ⟨ε * β kt, mul_pos hε hbt, fun a ha hab => ?_⟩
    rw [Real.dist_eq] at hab ⊢
    have hb' : (0 : ℝ) ≤ b := hb
    have ha' : (0 : ℝ) ≤ a := ha
    have key : |H R β a - H R β b| ≤ |a - b| / β kt := by
      rcases le_total a b with h | h
      · have h1 := hlip a b ha' h
        have h2 : H R β b ≤ H R β a := hanti ha hb h
        rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
        have e : -(a - b) / β kt = (b - a) / β kt := by ring
        linarith
      · have h1 := hlip b a hb' h
        have h2 : H R β a ≤ H R β b := hanti hb ha h
        rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
        linarith
    calc |H R β a - H R β b| ≤ |a - b| / β kt := key
      _ < ε * β kt / β kt := by
          apply div_lt_div_of_pos_right hab hbt
      _ = ε := by field_simp
  refine ⟨hcont, hanti, ?_, hcut⟩
  -- piecewise linearity
  set G0 : ℝ := ∑ j, β j * max (R j - 0) 0 with hG0
  refine ⟨insert G0 (univ.image (cutoffBudget R β)), fun a b ha hab hT => ?_⟩
  have hG0T := hT G0 (Finset.mem_insert_self _ _)
  rcases le_or_gt G0 a with h | h
  · refine ⟨0, 0, fun y hy => ?_⟩
    have hy0 : 0 ≤ y := le_trans ha hy.1
    have : H R β y = 0 := le_antisymm ((B17 y hy0).2.2.1 0 le_rfl (by
      have := hy.1; simp only [hG0] at h; linarith)) (B17 y hy0).1
    rw [this]; ring
  · have hbG : b ≤ G0 := by
      by_contra hc; push Not at hc
      exact hG0T ⟨h, hc⟩
    -- binding on [a,b]
    have hbind : ∀ y ∈ Set.Icc a b, ∑ j, β j * max (R j - H R β y) 0 = y := by
      intro y hy
      have hy0 : 0 ≤ y := le_trans ha hy.1
      rcases (B17 y hy0).2.2.2 with h0 | h0
      · rw [h0]
        have := (B17 y hy0).2.1
        rw [h0] at this
        simp only [hG0] at hbG
        have e : ∑ j, β j * max (R j - 0) 0 = ∑ j, β j * max (R j - (0:ℝ)) 0 := rfl
        linarith [hy.2]
      · exact h0
    set za := H R β a
    set zb := H R β b
    have hab' : zb ≤ za := hanti ha (le_trans ha hab) hab
    -- no R_k strictly between zb and za
    have hsep : ∀ k, R k ≤ zb ∨ za ≤ R k := by
      intro k
      by_contra hc
      push Not at hc
      obtain ⟨h1, h2⟩ := hc
      have hk := hT (cutoffBudget R β k)
        (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (mem_univ k)))
      apply hk
      rw [← BCSol.G_R R β hR]
      have ga := hbind a ⟨le_rfl, hab⟩
      have gb := hbind b ⟨hab, le_rfl⟩
      have g1 := BCSol.G_gap R β hβ (R k) za h2.le kt (Htop a ha)
      have g2 := BCSol.G_gap R β hβ zb (R k) h1.le k le_rfl
      constructor
      · have : 0 < β kt * (za - R k) := mul_pos hbt (by linarith)
        linarith
      · have : 0 < β k * (R k - zb) := mul_pos (hβ k) (by linarith)
        linarith
    set K := univ.filter (fun k => za ≤ R k)
    set C := ∑ k ∈ K, β k * R k
    set D := ∑ k ∈ K, β k
    have hlin : ∀ y ∈ Set.Icc a b, y = C - D * H R β y := by
      intro y hy
      have hy0 : 0 ≤ y := le_trans ha hy.1
      have hzy1 : H R β y ≤ za := hanti ha hy0 hy.1
      have hzy2 : zb ≤ H R β y := hanti hy0 (le_trans ha hab) hy.2
      have hb := hbind y hy
      suffices e : ∑ j, β j * max (R j - H R β y) 0 = C - D * H R β y by linarith
      simp only [C, D, K]
      rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      split_ifs with hk
      · rw [max_eq_left (by linarith)]; ring
      · push Not at hk
        rcases hsep k with h' | h'
        · rw [max_eq_right (by linarith)]; ring
        · linarith
    have hD0 : (0:ℝ) ≤ D := Finset.sum_nonneg (fun k _ => (hβ k).le)
    rcases hD0.lt_or_eq with hD | hD
    · refine ⟨C / D, -1 / D, fun y hy => ?_⟩
      have := hlin y hy
      have hDne : D ≠ 0 := hD.ne'
      rw [eq_comm, ← sub_eq_zero]
      have e : C / D + -1 / D * y - H R β y = (C - y - D * H R β y) / D := by
        field_simp; ring
      rw [e, div_eq_zero_iff]
      left; linarith
    · refine ⟨H R β a, 0, fun y hy => ?_⟩
      have e1 := hlin y hy
      have e2 := hlin a ⟨le_rfl, hab⟩
      rw [← hD] at e1 e2
      have : y = a := by linarith
      rw [this]; ring
