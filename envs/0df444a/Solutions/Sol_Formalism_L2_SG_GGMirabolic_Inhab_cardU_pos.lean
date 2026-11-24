-- Prove2me | solution 1 for Formalism.L2.SG.GGMirabolic.Inhab.cardU_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:17:46.982603+00:00
-- url     : https://prove2.me/submissions/ab5c8a5a-e54f-47a0-8969-8d9eb24c2dcc

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolicInhab
import Theorems.Thm_Formalism_L2_SG_GGMirabolic_isUni_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.GGMirabolic Formalism.L2.SG.GGMirabolic.Inhab
open Formalism.L2.SG.GGMirabolic
noncomputable section
open Classical
namespace Formalism.L2.SG.GGMirabolic.Inhab
theorem _root_.solution (F : Type) [Field F] [Fintype F] (k : ℕ) : 0 < cardU F k := by
  unfold cardU
  have : Nonempty {x : GL (Fin k) F // IsUni k x} := ⟨⟨1, isUni_one⟩⟩
  exact Nat.card_pos
end Formalism.L2.SG.GGMirabolic.Inhab
