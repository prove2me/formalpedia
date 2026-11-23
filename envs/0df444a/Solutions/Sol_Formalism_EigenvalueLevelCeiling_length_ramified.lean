-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.length_ramified
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:35:39.36781+00:00
-- url     : https://prove2.me/submissions/eeffc9ba-718a-41a8-a7f0-d88d8a9452ad

import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_ThreeForms
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_isLocalHom_of_map_eq_pow
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_exists_pow_smul_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Formalism.HermitianLatticesTheory
noncomputable section
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
open IsLocalRing
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution : LengthRamified := by
  intro O O' _ _ _ _ _ _ _ _ e hmap M _ _ hM
  by_cases he : e = 0
  · subst he
    rw [pow_zero, Ideal.one_eq_top] at hmap
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    have hu : IsUnit (algebraMap O O' ϖ) := by
      rw [hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton,
        Ideal.span_singleton_eq_top] at hmap
      exact hmap
    obtain ⟨n, hn⟩ := ThreeFormsAlt.exists_pow_smul_eq_zero O ϖ
      (by rw [hϖ.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self ϖ) M
      (Module.length_ne_top_iff.mp hM)
    have hsub : Subsingleton (TensorProduct O O' M) := by
      refine ⟨fun x y => ?_⟩
      have h0 : ∀ z : TensorProduct O O' M, z = 0 := by
        intro z
        induction z using TensorProduct.induction_on with
        | zero => rfl
        | tmul a m =>
          obtain ⟨u, hu'⟩ := hu.pow n
          have : a = ϖ ^ n • (a * (u⁻¹ : O'ˣ)) := by
            rw [Algebra.smul_def, map_pow, ← hu', mul_comm a, Units.mul_inv_cancel_left]
          rw [this, TensorProduct.smul_tmul, hn, TensorProduct.tmul_zero]
        | add a b ha hb => rw [ha, hb, add_zero]
      rw [h0 x, h0 y]
    rw [Module.length_eq_zero]
    simp
  · have := ThreeFormsAlt.isLocalHom_of_map_eq_pow O O' e he hmap
    rw [IsLocalRing.length_baseChange O O' M, hmap,
      IsDiscreteValuationRing.length_quotient_pow_maximalIdeal, mul_comm]
end Formalism.EigenvalueLevelCeiling
