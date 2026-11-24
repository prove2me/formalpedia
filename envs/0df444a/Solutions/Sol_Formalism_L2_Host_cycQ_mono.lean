-- Prove2me | solution 1 for Formalism.L2.Host.cycQ_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:12:04.373648+00:00
-- url     : https://prove2.me/submissions/e02a4d72-dfe5-45b1-89d9-111e292c85b0

import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_Lemmas
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_PowValCast
import Theorems.Thm_Formalism_L2_Host_mus_mono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IntermediateField NumberField
open Formalism Formalism.L2 Formalism.L2.Host
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.L2.Host
theorem _root_.solution {M N : ℕ} (h : M ∣ N) : cycQ M ≤ cycQ N := adjoin.mono ℚ _ _ (mus_mono h)
end Formalism.L2.Host
