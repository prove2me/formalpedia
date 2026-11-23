-- Prove2me | solution 1 for Formalism.DivisionValues.lattice_fg_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:30:30.4428+00:00
-- url     : https://prove2.me/submissions/fb8254d0-ec12-4d1f-ad8e-dcb3685ceec3

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_PassageScaleFree
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DualMu
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_KappaNormalise

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
namespace Formalism.DivisionValues
theorem _root_.solution {K : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] {D : ℕ}
    (hD : 0 < D) (R : Submodule (𝓞 K) (Fin D → K)) (hR : Submodule.IsLattice K R) :
    R.FG ∧ R ≠ ⊥ := by
  refine ⟨hR.fg, ?_⟩
  rintro rfl
  haveI : Nonempty (Fin D) := ⟨⟨0, hD⟩⟩
  have h := hR.span_eq_top
  rw [Submodule.bot_coe, Submodule.span_zero_singleton] at h
  exact bot_ne_top h
end Formalism.DivisionValues
