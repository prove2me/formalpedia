-- Prove2me | solution 1 for FongoSync.Hlc.before_of_notAfter_of_before
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:59:35.397702+00:00
-- url     : https://prove2.me/submissions/5caba5d8-2918-4e38-887f-160705acb7a7


import Definitions.Def_FongoSync_Clock

set_option autoImplicit false
open FongoSync
namespace FongoSync
namespace Hlc
theorem _root_.solution {a b c : Hlc} (h₁ : a.NotAfter b) (h₂ : b.Before c) :
    a.Before c := by
  unfold Hlc.NotAfter at h₁; unfold Hlc.Before at *; omega
end Hlc
end FongoSync
