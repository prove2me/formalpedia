-- Prove2me | solution 1 for Focil.canonical_implies_compliant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:38:10.932063+00:00
-- url     : https://prove2.me/submissions/b4a551f6-556a-47e9-9ad9-f63edf1bb15d

import Definitions.Def_Focil_Types
import Definitions.Def_Focil_Protocol
import Definitions.Def_Focil_ForkChoice

set_option autoImplicit false
open Focil
namespace Focil
theorem _root_.solution
    (fc : ForkChoice) (b : Block)
    (h_canon : IsCanonical fc b) :
    FocilCompliant fc.canAppend fc.full b fc.state := by
  have hQuorum : fc.HasQuorum b := h_canon
  obtain ⟨v, hHonest, hVoted⟩ :=
    fc.quorum_has_honest_voter b hQuorum
  exact fc.honest_attester_compliance b v hHonest hVoted
end Focil
