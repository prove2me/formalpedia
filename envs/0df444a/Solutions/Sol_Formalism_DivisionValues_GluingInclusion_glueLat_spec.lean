-- Prove2me | solution 1 for Formalism.DivisionValues.GluingInclusion.glueLat_spec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:22:48.176605+00:00
-- url     : https://prove2.me/submissions/6abcd192-45c9-463f-84ad-1cb316cc2903

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_LatticeGlueUnique
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionSecondStep
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondStepGluing
import Theorems.Thm_Formalism_DivisionValues_GluingInclusion_glue_spec

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
variable {K : Type} [Field K] [NumberField K]
namespace Formalism.DivisionValues.GluingInclusion
theorem _root_.solution {D : ℕ} (L0 : Submodule (𝓞 K) (Fin D → K))
    (L : HeightOneSpectrum (𝓞 K) → Submodule (𝓞 K) (Fin D → K))
    (h0 : Submodule.IsLattice K L0) (hL : ∀ w, Submodule.IsLattice K (L w))
    (hfin : {w : HeightOneSpectrum (𝓞 K) | localization₂ w.asIdeal (L w) ≠ localization₂ w.asIdeal L0}.Finite) :
    Submodule.IsLattice K (glueLat L) ∧
      ∀ w : HeightOneSpectrum (𝓞 K), localization₂ w.asIdeal (glueLat L) = localization₂ w.asIdeal (L w) :=
  glue_spec (NumberField.RingOfIntegers.not_isField K) L0 L h0 hL hfin
end Formalism.DivisionValues.GluingInclusion
