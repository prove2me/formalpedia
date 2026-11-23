-- Prove2me | solution 1 for Formalism.DivisionValues.localizationAt_le_of_le_localizationAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:24:19.301249+00:00
-- url     : https://prove2.me/submissions/b3265966-cf69-451b-a4a2-f9fdfc303db5

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_DivIntoDualShift
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LcvBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DivIntoDual
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TwistedLatticeNaturality
import Theorems.Thm_Formalism_DivisionValues_imageLcv_mem_locP


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix nonZeroDivisors
noncomputable section
open Formalism Formalism.DivisionValues
variable {K : Type} [Field K] [NumberField K] [StarRing K] {d : ℕ}
namespace Formalism.DivisionValues
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) {A B : Submodule (𝓞 K) (Fin d → K)}
    (h : A ≤ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal B) :
    Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A ≤ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal B := by
  intro x hx
  rw [imageLcv_mem_locP] at hx
  obtain ⟨s, hs, hsx⟩ := hx
  obtain ⟨t, ht, htx⟩ := (imageLcv_mem_locP _ _ _).1 (h hsx)
  rw [imageLcv_mem_locP]
  exact ⟨t * s, w.asIdeal.primeCompl.mul_mem ht hs, by rw [mul_smul]; exact htx⟩
end Formalism.DivisionValues
