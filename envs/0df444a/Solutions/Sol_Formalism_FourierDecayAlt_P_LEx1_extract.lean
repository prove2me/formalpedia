-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx1.extract
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:25:09.351328+00:00
-- url     : https://prove2.me/submissions/ea7b5fd1-1a7b-40e7-8240-5c87a9e358fe

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StepClaimFromStepsFull
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2ConstMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_coeff_id

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.LEx1
theorem _root_.solution (N d : ℕ) (grid : Fin N → Finset ℝ) (hg : ∀ a, (grid a).card = d + 1)
    (c : (Fin N → Fin (d + 1)) → ℂ) (κ : Fin N → Fin (d + 1)) :
    c κ = ∑ g ∈ Fintype.piFinset grid, ((∏ a, (Lagrange.basis (grid a) id (g a)).coeff (κ a : ℕ) : ℝ) : ℂ) *
      ∑ κ' : Fin N → Fin (d + 1), ((∏ a, (g a) ^ (κ' a : ℕ) : ℝ) : ℂ) * c κ' := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have key : ∀ κ' : Fin N → Fin (d + 1), ∑ g ∈ Fintype.piFinset grid,
      ((∏ a, (Lagrange.basis (grid a) id (g a)).coeff (κ a : ℕ) : ℝ) : ℂ) *
        (((∏ a, (g a) ^ (κ' a : ℕ) : ℝ) : ℂ) * c κ') = (if κ = κ' then 1 else 0) * c κ' := by
    intro κ'
    have h1 : ∑ g ∈ Fintype.piFinset grid, (∏ a, (Lagrange.basis (grid a) id (g a)).coeff (κ a : ℕ)) *
        (∏ a, (g a) ^ (κ' a : ℕ)) = if κ = κ' then (1 : ℝ) else 0 := by
      simp_rw [← Finset.prod_mul_distrib]
      rw [← Finset.prod_univ_sum (t := grid)
        (f := fun a x => (Lagrange.basis (grid a) id x).coeff (κ a : ℕ) * x ^ (κ' a : ℕ))]
      have h3 : ∀ a, ∑ x ∈ grid a, (Lagrange.basis (grid a) id x).coeff (κ a : ℕ) * x ^ (κ' a : ℕ) =
          if (κ a : ℕ) = (κ' a : ℕ) then 1 else 0 :=
        fun a => coeff_id (grid a) d _ _ (hg a) (Nat.lt_succ_iff.1 (κ' a).2)
      simp_rw [h3]
      by_cases h : κ = κ'
      · subst h; simp
      · rw [if_neg h]
        obtain ⟨a, ha⟩ := Function.ne_iff.1 h
        apply Finset.prod_eq_zero (Finset.mem_univ a)
        rw [if_neg]; intro hh; exact ha (Fin.ext hh)
    have h4 : ((if κ = κ' then (1 : ℂ) else 0)) = (((if κ = κ' then (1 : ℝ) else 0) : ℝ) : ℂ) := by
      split_ifs <;> simp
    rw [h4, ← h1]; push_cast; rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intros; ring
  simp_rw [key]; simp
end Formalism.FourierDecayAlt.P.LEx1
