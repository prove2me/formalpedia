-- Prove2me | solution 1 for Formalism.DivisionValues.StepBAux.lidx_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:44:02.493003+00:00
-- url     : https://prove2.me/submissions/fdd3cdbb-de97-4860-bf2f-38163b54c10e

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
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_locS_inf


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
theorem _root_.solution {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W] (p : Ideal R)
    [p.IsPrime] (A A' B B' : Submodule R W) (hA : Formalism.HermitianLatticesTheory.localization₂ p A = Formalism.HermitianLatticesTheory.localization₂ p A')
    (hB : Formalism.HermitianLatticesTheory.localization₂ p B = Formalism.HermitianLatticesTheory.localization₂ p B') :
    Formalism.HermitianLatticesTheory.lidx p A B = Formalism.HermitianLatticesTheory.lidx p A' B' := by
  have hAB : Formalism.HermitianLatticesTheory.localization₂ p (A ⊓ B) = Formalism.HermitianLatticesTheory.localization₂ p (A' ⊓ B') := by
    unfold Formalism.HermitianLatticesTheory.localization₂ at hA hB ⊢
    rw [Formalism.HermitianLatticesTheory.locBasic_locS_inf, Formalism.HermitianLatticesTheory.locBasic_locS_inf, hA, hB]
  unfold Formalism.HermitianLatticesTheory.lidx Formalism.HermitianLatticesTheory.locLen
  rw [hA, hB, hAB]
end Formalism.DivisionValues.StepBAux
