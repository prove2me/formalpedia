-- Prove2me | solution 1 for Formalism.DivisionValues.StepBAux.localization_eq_and_conj_eq_of_semilocalization_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:31:45.070781+00:00
-- url     : https://prove2.me/submissions/7187d2f1-d3c1-46ad-a6a7-2c83521ca7fb

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
import Theorems.Thm_Formalism_DivisionValues_StepBAux_locS_locS_of_le
import Theorems.Thm_Formalism_DivisionValues_StepBAux_hcompl_le_conj
import Theorems.Thm_Formalism_DivisionValues_LocalCovolumeBasis_key
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_hcompl_le


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
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) {d : ℕ} (A B : Submodule (𝓞 K) (Fin d → K))
    (h : Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal A = Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal B) :
    Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal B ∧
      Formalism.HermitianLatticesTheory.localization₂ (conjPl w).asIdeal A = Formalism.HermitianLatticesTheory.localization₂ (conjPl w).asIdeal B := by
  have key : ∀ T : Submonoid (𝓞 K), Formalism.HermitianLatticesTheory.hcompl (K := K) w.asIdeal ≤ T →
      Formalism.HermitianLatticesTheory.locS T A = Formalism.HermitianLatticesTheory.locS T B := by
    intro T hT
    rw [← locS_locS_of_le hT A, ← locS_locS_of_le hT B]
    unfold Formalism.HermitianLatticesTheory.loc at h
    rw [h]
  exact ⟨key _ (Formalism.HermitianLatticesTheory.locBasic_hcompl_le (K := K) w.asIdeal), key _ (hcompl_le_conj w)⟩
end Formalism.DivisionValues.StepBAux
