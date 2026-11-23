-- Prove2me | solution 1 for Formalism.DivisionValues.StepBAux.locS_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:44.921657+00:00
-- url     : https://prove2.me/submissions/89aaa473-7998-4f5c-98da-e6fd9702b1d7

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LcvBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_RatHerm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionSecondStep
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_mem_locS


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.StepBAux
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.DivisionValues.StepBAux
theorem _root_.solution {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W] (S : Submonoid R)
    (f : W ≃ₗ[R] W) (A : Submodule R W) :
    Formalism.HermitianLatticesTheory.locS S (A.map (f : W →ₗ[R] W)) = (Formalism.HermitianLatticesTheory.locS S A).map (f : W →ₗ[R] W) := by
  ext x
  rw [Submodule.mem_map_equiv, Formalism.HermitianLatticesTheory.locBasic_mem_locS, Formalism.HermitianLatticesTheory.locBasic_mem_locS]
  constructor
  · rintro ⟨s, hs, hx⟩
    refine ⟨s, hs, ?_⟩
    rw [Submodule.mem_map_equiv] at hx
    simpa [map_smul] using hx
  · rintro ⟨s, hs, hx⟩
    refine ⟨s, hs, ?_⟩
    rw [Submodule.mem_map_equiv]
    simpa [map_smul] using hx
end Formalism.DivisionValues.StepBAux
