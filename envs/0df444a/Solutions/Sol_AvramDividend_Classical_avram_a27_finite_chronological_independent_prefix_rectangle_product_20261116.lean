-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_finite_chronological_independent_prefix_rectangle_product_20261116
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T09:48:29.833759+00:00
-- url     : https://prove2.me/submissions/305dd542-485b-4427-bcf4-7380e6376f4b

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators
noncomputable section
theorem solution
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (Y : ℕ → Ω → E)
    (hMeas : ∀ i < n, Measurable (Y i))
    (hPrefix : ∀ k < n,
      IndepFun (fun ω : Ω => fun i : Fin k => Y i.val ω)
        (Y k) P)
    (A : ℕ → Set E)
    (hA : ∀ i < n, MeasurableSet (A i)) :
    P (⋂ i ∈ Finset.range n, Y i ⁻¹' A i) =
      ∏ i ∈ Finset.range n, P (Y i ⁻¹' A i) := by
  classical
  have hRec : ∀ k : ℕ, k ≤ n →
      P (⋂ i ∈ Finset.range k, Y i ⁻¹' A i) =
        ∏ i ∈ Finset.range k, P (Y i ⁻¹' A i) := by
    intro k
    induction k with
    | zero =>
        intro _
        simp [measure_univ]
    | succ k ih =>
        intro hk
        have hk0 : k < n := by omega
        have hhk : k ≤ n := by omega
        have hB : MeasurableSet
            (Set.univ.pi (fun i : Fin k => A i.val)) := by
          exact MeasurableSet.univ_pi (fun i => hA i.val (by omega))
        have hE : (fun ω : Ω => fun i : Fin k => Y i.val ω) ⁻¹'
            (Set.univ.pi (fun i : Fin k => A i.val)) =
            (⋂ i ∈ Finset.range k, Y i ⁻¹' A i) := by
          ext ω
          simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left,
            Set.mem_iInter, Finset.mem_range]
          constructor
          · intro h i hi
            exact h ⟨i, hi⟩
          · intro h i
            exact h i i.isLt
        have hInd := (hPrefix k hk0).measure_inter_preimage_eq_mul
          (Set.univ.pi (fun i : Fin k => A i.val)) (A k)
          hB (hA k hk0)
        calc
          P (⋂ i ∈ Finset.range (k + 1), Y i ⁻¹' A i) =
              P ((⋂ i ∈ Finset.range k, Y i ⁻¹' A i) ∩
                (Y k ⁻¹' A k)) := by
                rw [Finset.range_add_one, Finset.set_biInter_insert]
                ac_rfl
          _ = P (⋂ i ∈ Finset.range k, Y i ⁻¹' A i) *
              P (Y k ⁻¹' A k) := by
                rw [← hE]
                exact hInd
          _ = ∏ i ∈ Finset.range (k + 1), P (Y i ⁻¹' A i) := by
                rw [ih hhk]
                simp [Finset.range_add_one, mul_comm]
  exact hRec n le_rfl
