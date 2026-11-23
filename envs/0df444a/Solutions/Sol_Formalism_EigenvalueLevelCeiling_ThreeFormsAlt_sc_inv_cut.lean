-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.ThreeFormsAlt.sc_inv_cut
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:47.308636+00:00
-- url     : https://prove2.me/submissions/2383d7c6-1361-4ed9-a7d8-0053e773a57e

import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_ThreeForms
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_mem_sc_inv

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
open Formalism.EigenvalueLevelCeiling.ThreeFormsAlt
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {Z : Type} [AddCommGroup Z] [Module K Z] [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z]
namespace Formalism.EigenvalueLevelCeiling.ThreeFormsAlt
theorem _root_.solution (W : Submodule K Z) (X : Submodule (𝓞 K) Z) {a : K} (ha : a ≠ 0) :
    sc a⁻¹ (cut W X) = cut W (sc a⁻¹ X) := by
  ext x
  rw [mem_sc_inv ha]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(mem_sc_inv ha _ _).mpr h1, ?_⟩
    have := W.smul_mem a⁻¹ h2
    rwa [smul_smul, inv_mul_cancel₀ ha, one_smul] at this
  · rintro ⟨h1, h2⟩
    exact ⟨(mem_sc_inv ha _ _).mp h1, W.smul_mem a h2⟩
end Formalism.EigenvalueLevelCeiling.ThreeFormsAlt
