-- Prove2me | solution 1 for Formalism.FG.FormalGroupSubstitution.subst_X_add_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:37.182876+00:00
-- url     : https://prove2.me/submissions/1852e605-4563-423a-8bb5-33dcf2881d7d

import Definitions.Def_Formalism_FormalGroupWitt_Statement
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_AdditiveLawExample

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.FG Formalism.FG.FormalGroupSubstitution
open MvPowerSeries
namespace Formalism.FG.FormalGroupSubstitution
theorem _root_.solution {σ τ : Type*} [Finite σ] {R : Type*} [CommRing R]
    (a : σ → MvPowerSeries τ R) (h : ∀ s, constantCoeff (a s) = 0) (p q : σ) :
    subst a (X p + X q : MvPowerSeries σ R) = a p + a q := by
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero h
  rw [subst_add ha, subst_X ha, subst_X ha]
end Formalism.FG.FormalGroupSubstitution
