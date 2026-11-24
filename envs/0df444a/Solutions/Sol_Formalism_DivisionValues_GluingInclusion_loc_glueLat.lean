-- Prove2me | solution 1 for Formalism.DivisionValues.GluingInclusion.loc_glueLat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:56:21.801229+00:00
-- url     : https://prove2.me/submissions/c8ab6104-8756-44d6-bf05-17635f75ae2c

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_LatticeGlueUnique
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionSecondStep
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondStepGluing
import Theorems.Thm_Formalism_DivisionValues_GluingInclusion_loc_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.GluingInclusion
open Formalism.HermitianLatticesTheory
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.DivisionValues.GluingInclusion
theorem _root_.solution {D : ℕ} (L : HeightOneSpectrum (𝓞 K) → Submodule (𝓞 K) (Fin D → K))
    (hc : ∀ w, L (conjPl w) = L w) (R : Submodule (𝓞 K) (Fin D → K))
    (hR : ∀ w : HeightOneSpectrum (𝓞 K), localization₂ w.asIdeal R = localization₂ w.asIdeal (L w))
    (w : HeightOneSpectrum (𝓞 K)) :
    loc (K := K) w.asIdeal R = loc (K := K) w.asIdeal (L w) := by
  rw [loc_eq, loc_eq, hR w, hR (conjPl w), hc w]
end Formalism.DivisionValues.GluingInclusion
