-- Prove2me | solution 1 for Formalism.DivisionValues.StepBAux.locS_locS_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:44.380347+00:00
-- url     : https://prove2.me/submissions/c5ee8cfd-2e9f-44a3-ad10-0349f210fff4

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
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_le_locS
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_locS_mono
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
theorem _root_.solution {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    {S T : Submonoid R} (hST : S ≤ T) (A : Submodule R W) :
    Formalism.HermitianLatticesTheory.locS T (Formalism.HermitianLatticesTheory.locS S A) = Formalism.HermitianLatticesTheory.locS T A := by
  apply le_antisymm
  · intro x hx
    obtain ⟨t, ht, hx⟩ := Formalism.HermitianLatticesTheory.locBasic_mem_locS.mp hx
    obtain ⟨s, hs, hx⟩ := Formalism.HermitianLatticesTheory.locBasic_mem_locS.mp hx
    exact Formalism.HermitianLatticesTheory.locBasic_mem_locS.mpr ⟨s * t, T.mul_mem (hST hs) ht, by rwa [mul_smul]⟩
  · exact Formalism.HermitianLatticesTheory.locBasic_locS_mono T (Formalism.HermitianLatticesTheory.locBasic_le_locS S A)
end Formalism.DivisionValues.StepBAux
