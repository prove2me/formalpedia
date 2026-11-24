-- Prove2me | solution 1 for Formalism.WeaklyAdmissibleFiltrations.imFLe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:22:50.817671+00:00
-- url     : https://prove2.me/submissions/bff27c48-fc99-4543-8477-3ea5107bf851

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CocyclesFunctorial
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_Galois
import Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_colZero_iff_galois
import Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_imF_le_galois

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.WeaklyAdmissibleFiltrations
open Module TensorProduct
namespace Formalism.WeaklyAdmissibleFiltrations
theorem _root_.solution : ImFLe := by
  unfold ImFLe
  intros
  exact ⟨imF_le_galois _ ‹_›, colZero_iff_galois _⟩
end Formalism.WeaklyAdmissibleFiltrations
