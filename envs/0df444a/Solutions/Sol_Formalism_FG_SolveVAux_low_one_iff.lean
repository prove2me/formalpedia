-- Prove2me | solution 1 for Formalism.FG.SolveVAux.low_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:14:55.430679+00:00
-- url     : https://prove2.me/submissions/990b93ed-09ed-42c1-b942-45e363652127

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v w
open Formalism Formalism.FG Formalism.FG.SolveVAux
open MvPowerSeries
variable {R : Type u} [CommRing R] {τ : Type w}
namespace Formalism.FG.SolveVAux
theorem _root_.solution (p : MvPowerSeries τ R) : Low 1 p ↔ constantCoeff p = 0 := by
  constructor
  · intro hp
    rw [← coeff_zero_eq_constantCoeff_apply]
    exact hp 0 (by simp)
  · intro hp d hd
    have : d = 0 := (Finsupp.degree_eq_zero_iff d).1 (by omega)
    rw [this, coeff_zero_eq_constantCoeff_apply, hp]
end Formalism.FG.SolveVAux
