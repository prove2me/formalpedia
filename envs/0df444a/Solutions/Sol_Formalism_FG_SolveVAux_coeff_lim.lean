-- Prove2me | solution 1 for Formalism.FG.SolveVAux.coeff_lim
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:15.004988+00:00
-- url     : https://prove2.me/submissions/f674d5ad-480b-4f6b-bc64-f01a8746535d

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
variable {R : Type u} [CommRing R] {ι : Type v} [Finite ι] {τ : Type w}
variable {G : ι → MvPowerSeries τ R} {g : ι → MvPowerSeries ι R}
namespace Formalism.FG.SolveVAux
theorem _root_.solution (d : τ →₀ ℕ) (i : ι) :
    coeff d (lim G g i) = coeff d (seq G g (d.degree + 1) i) :=
  rfl
end Formalism.FG.SolveVAux
