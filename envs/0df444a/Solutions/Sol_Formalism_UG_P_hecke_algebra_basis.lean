-- Prove2me | solution 1 for Formalism.UG.P.hecke_algebra_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:20:34.269336+00:00
-- url     : https://prove2.me/submissions/2d61fd78-d3bd-4c9d-a423-f03d6d70f976

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Heckebasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
namespace Formalism.UG.P
theorem _root_.solution : Formalism.UG.HeckeBasis := by
  unfold Formalism.UG.HeckeBasis
  intro G _ K k _
  exact ⟨heckeEquiv K k, fun f g => biInv_mk_out K _ f.2.1 g⟩
end Formalism.UG.P
