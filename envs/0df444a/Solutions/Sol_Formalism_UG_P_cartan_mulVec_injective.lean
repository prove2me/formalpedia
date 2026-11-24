-- Prove2me | solution 1 for Formalism.UG.P.cartan_mulVec_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:38:09.19014+00:00
-- url     : https://prove2.me/submissions/41b381a5-5afb-4ee1-aed7-19cd164b72bd

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Cartan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution (G : Matrix n n R) (hG : G.det ≠ 0) :
    Function.Injective (Matrix.mulVecLin G) := by
  rw [← LinearMap.ker_eq_bot, Matrix.ker_mulVecLin_eq_bot_iff]
  intro v hv
  by_contra hne
  exact hG (Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hne, hv⟩)
end Formalism.UG.P
