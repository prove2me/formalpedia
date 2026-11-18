-- Prove2me | solution 1 for FinitePermutationCoupling.correction_step
-- status  : ACCEPTED   (prove)
-- author  : @dmilosch
-- created : 2026-11-17T18:00:03.111608+00:00
-- url     : https://prove2.me/submissions/2ca2b81b-1836-4f37-94c8-e1987cfc984a

import Mathlib.Tactic
import Mathlib.Analysis.Convex.DoublyStochasticMatrix

namespace FinitePermutationCoupling

open scoped BigOperators

set_option linter.unusedSectionVars false

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The correction kernel in the random-order swap construction. -/
def residualKernel (P : Matrix α α ℝ) : Matrix α α ℝ :=
  fun u v => 1 - ((Fintype.card α : ℝ) - 1) * P u v

/-- A uniform upper bound on the conditional matching probabilities makes the
correction kernel nonnegative; its row and column sums remain one. -/
theorem residualKernel_doubly_stochastic (P : Matrix α α ℝ)
    (hP : P ∈ doublyStochastic ℝ α)
    (hcap : ∀ u v, ((Fintype.card α : ℝ) - 1) * P u v ≤ 1) :
    residualKernel P ∈ doublyStochastic ℝ α := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun u v => sub_nonneg.mpr (hcap u v), ?_, ?_⟩
  · intro u
    simp only [residualKernel, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one, ← Finset.mul_sum,
      sum_row_of_mem_doublyStochastic hP]
    ring
  · intro v
    simp only [residualKernel, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one, ← Finset.mul_sum,
      sum_col_of_mem_doublyStochastic hP]
    ring

theorem residualKernel_doubly_stochastic_of_bound (P : Matrix α α ℝ)
    (hP : P ∈ doublyStochastic ℝ α) (hm : 2 ≤ Fintype.card α)
    (hcap : ∀ u v, P u v ≤ 1 / ((Fintype.card α : ℝ) - 1)) :
    residualKernel P ∈ doublyStochastic ℝ α := by
  apply residualKernel_doubly_stochastic P hP
  intro u v
  have hmR : (2 : ℝ) ≤ Fintype.card α := by exact_mod_cast hm
  have hm' : 0 < (Fintype.card α : ℝ) - 1 := by linarith
  have hp := (le_div_iff₀ hm').mp (hcap u v)
  simpa only [mul_comm] using hp

/-- Mixing the original conditional partner law with the correction kernel
with respective probabilities `1-1/m` and `1/m` gives an exactly uniform partner. -/
theorem residualKernel_uniform_mixture [Nonempty α] (P : Matrix α α ℝ) (u v : α) :
    (1 - 1 / (Fintype.card α : ℝ)) * P u v +
      (1 / (Fintype.card α : ℝ)) * residualKernel P u v =
      1 / (Fintype.card α : ℝ) := by
  have hm : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold residualKernel
  field_simp
  ring

/-- Exchange the values of the current relabelling at the two selected partners. -/
def correct (φ : Equiv.Perm α) (y z : α) : Equiv.Perm α :=
  (Equiv.swap y z).trans φ

theorem correct_at_left (φ : Equiv.Perm α) (y z : α) :
    correct φ y z y = φ z := by simp [correct]

theorem correct_off (φ : Equiv.Perm α) (y z v : α) (hy : v ≠ y) (hz : v ≠ z) :
    correct φ y z v = φ v := by
  simp only [correct, Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne hy hz]

/-- Swaps within the active residual set preserve every already settled value. -/
theorem correct_preserves_settled (φ : Equiv.Perm α) (V : Finset α)
    {y z v : α} (hy : y ∈ V) (hz : z ∈ V) (hv : v ∉ V) :
    correct φ y z v = φ v := by
  apply correct_off
  · intro h; exact hv (h.symm ▸ hy)
  · intro h; exact hv (h.symm ▸ hz)

/-- For a fixed reference bijection, the unnormalized correction mass that can
move any specified value is at most two: one row and one column of the kernel. -/
theorem correction_touch_mass_le_two (T : Matrix α α ℝ)
    (hT : T ∈ doublyStochastic ℝ α) (h : Equiv.Perm α) (v : α) :
    (∑ u, ∑ z, if Equiv.swap (h u) z v ≠ v then T u z else 0) ≤ 2 := by
  have hn (u z : α) : 0 ≤ T u z := nonneg_of_mem_doublyStochastic hT
  have hpoint (u z : α) :
      (if Equiv.swap (h u) z v ≠ v then T u z else 0) ≤
        (if h u = v then T u z else 0) + (if z = v then T u z else 0) := by
    by_cases hu : h u = v
    · simp only [if_pos hu]
      split_ifs <;> linarith [hn u z]
    · by_cases hz : z = v
      · simp only [if_neg hu, if_pos hz, zero_add]
        split_ifs <;> linarith [hn u z]
      · have hfix := Equiv.swap_apply_of_ne_of_ne (Ne.symm hu) (Ne.symm hz)
        simp only [hfix, ne_eq, not_true_eq_false, if_false, if_neg hu, if_neg hz, add_zero,
          le_refl]
  have hrow : (∑ u, ∑ z, if h u = v then T u z else 0) = 1 := by
    calc
      _ = ∑ u, if h u = v then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro u _
        by_cases hu : h u = v
        · simp only [if_pos hu, sum_row_of_mem_doublyStochastic hT]
        · simp [hu]
      _ = ∑ u, if u = v then (1 : ℝ) else 0 := Fintype.sum_equiv h _ _ (fun _ => rfl)
      _ = 1 := by simp
  have hcol : (∑ u, ∑ z, if z = v then T u z else 0) = 1 := by
    simpa using sum_col_of_mem_doublyStochastic hT v
  calc
    _ ≤ ∑ u, ∑ z, ((if h u = v then T u z else 0) +
        (if z = v then T u z else 0)) := by
      apply Finset.sum_le_sum
      intro u _
      exact Finset.sum_le_sum (fun z _ => hpoint u z)
    _ = (∑ u, ∑ z, if h u = v then T u z else 0) +
        (∑ u, ∑ z, if z = v then T u z else 0) := by
      simp only [Finset.sum_add_distrib]
    _ = 2 := by rw [hrow, hcol]; norm_num

/-- The actual probability mass of moving `v` in the correction branch:
the branch has probability `1/m`, and the next residual input is uniform. -/
noncomputable def correctionMoveMass (T : Matrix α α ℝ) (h : Equiv.Perm α) (v : α) : ℝ :=
  (∑ u, ∑ z, if Equiv.swap (h u) z v ≠ v then T u z else 0) /
    (Fintype.card α : ℝ) ^ 2

theorem correctionMoveMass_le (T : Matrix α α ℝ)
    (hT : T ∈ doublyStochastic ℝ α) (h : Equiv.Perm α) (v : α) :
    correctionMoveMass T h v ≤ 2 / (Fintype.card α : ℝ) ^ 2 := by
  exact div_le_div_of_nonneg_right (correction_touch_mass_le_two T hT h v) (sq_nonneg _)

/-- A pointwise forward-disagreement bound conditional on the entire reference
permutation also bounds inverse disagreement, by querying its fixed preimage. -/
theorem inverse_disagreement_iff (g h : Equiv.Perm α) (v : α) :
    g.symm v ≠ h.symm v ↔ g (h.symm v) ≠ v := by
  constructor
  · intro hne he
    apply hne
    exact (congrArg g.symm he).symm.trans (g.symm_apply_apply (h.symm v))
  · intro hne he
    apply hne
    rw [← he, g.apply_symm_apply]

/-- A complete one-step correction kernel: it uniformizes the sampled partner
and has a pointwise `2/m²` correction-move bound for every fixed reference map. -/
theorem residual_correction_kernel_proof (P : Matrix α α ℝ)
    (hP : P ∈ doublyStochastic ℝ α) (hm : 2 ≤ Fintype.card α)
    (hcap : ∀ u v, P u v ≤ 1 / ((Fintype.card α : ℝ) - 1)) :
    ∃ T : Matrix α α ℝ,
      T ∈ doublyStochastic ℝ α ∧
      (∀ u v, (1 - 1 / (Fintype.card α : ℝ)) * P u v +
        (1 / (Fintype.card α : ℝ)) * T u v = 1 / (Fintype.card α : ℝ)) ∧
      ∀ (h : Equiv.Perm α) (v : α),
        (∑ u, ∑ z, if Equiv.swap (h u) z v ≠ v then T u z else 0) /
            (Fintype.card α : ℝ) ^ 2 ≤ 2 / (Fintype.card α : ℝ) ^ 2 := by
  have hT := residualKernel_doubly_stochastic_of_bound P hP hm hcap
  have : Nonempty α := Fintype.card_pos_iff.mp (by omega)
  exact ⟨residualKernel P, hT, residualKernel_uniform_mixture P,
    fun h v => correctionMoveMass_le _ hT h v⟩

/-- The local correction step, including singleton residual sets. The cap is
written without division so the same statement covers every nonempty set. -/
theorem correction_step_proof [Nonempty α] (P : Matrix α α ℝ)
    (hP : P ∈ doublyStochastic ℝ α)
    (hcap : ∀ u v, ((Fintype.card α : ℝ) - 1) * P u v ≤ 1) :
    ∃ T : Matrix α α ℝ,
      T ∈ doublyStochastic ℝ α ∧
      (∀ u v, (1 - 1 / (Fintype.card α : ℝ)) * P u v +
        (1 / (Fintype.card α : ℝ)) * T u v = 1 / (Fintype.card α : ℝ)) ∧
      ∀ (h : Equiv.Perm α) (v : α),
        (1 / (Fintype.card α : ℝ) ^ 2) *
            (∑ u, ∑ z, if Equiv.swap (h u) z v ≠ v then T u z else 0) ≤
          2 / (Fintype.card α : ℝ) ^ 2 := by
  have hT := residualKernel_doubly_stochastic P hP hcap
  refine ⟨residualKernel P, hT, residualKernel_uniform_mixture P, ?_⟩
  intro h v
  simpa only [correctionMoveMass, div_eq_mul_inv, one_mul, mul_one, mul_comm]
    using correctionMoveMass_le _ hT h v

end FinitePermutationCoupling

open scoped BigOperators

theorem solution {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] (P : Matrix α α ℝ)
    (hP : P ∈ doublyStochastic ℝ α)
    (hcap : ∀ u v, ((Fintype.card α : ℝ) - 1) * P u v ≤ 1) :
    ∃ T : Matrix α α ℝ,
      T ∈ doublyStochastic ℝ α ∧
      (∀ u v, (1 - 1 / (Fintype.card α : ℝ)) * P u v +
        (1 / (Fintype.card α : ℝ)) * T u v = 1 / (Fintype.card α : ℝ)) ∧
      ∀ (h : Equiv.Perm α) (v : α),
        (1 / (Fintype.card α : ℝ) ^ 2) *
            (∑ u, ∑ z, if Equiv.swap (h u) z v ≠ v then T u z else 0) ≤
          2 / (Fintype.card α : ℝ) ^ 2 := by
  exact FinitePermutationCoupling.correction_step_proof P hP hcap
