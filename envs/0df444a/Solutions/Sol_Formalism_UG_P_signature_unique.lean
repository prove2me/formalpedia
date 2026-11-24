-- Prove2me | solution 1 for Formalism.UG.P.signature_unique
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:35.645961+00:00
-- url     : https://prove2.me/submissions/bf0e89b1-f4ba-40ca-8da7-13cfac9168ac

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureConjugationInvariant
import Theorems.Thm_Formalism_UG_P_sig_data
import Theorems.Thm_Formalism_UG_P_sig_dim

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
open Formalism.UG
namespace Formalism.UG.P
theorem _root_.solution : Formalism.UG.SigUnique := by
  intro n _ _ J p q p' q' h h'
  obtain ⟨hc, Q, hQ⟩ := sig_data J p q h
  obtain ⟨hc', Q', hQ'⟩ := sig_data J p' q' h'
  have d1 := sig_dim J Q hQ Q' hQ'
  have d2 := sig_dim J Q' hQ' Q hQ
  omega
end Formalism.UG.P
