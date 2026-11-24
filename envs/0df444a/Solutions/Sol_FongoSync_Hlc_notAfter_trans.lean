-- Prove2me | solution 1 for FongoSync.Hlc.notAfter_trans
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:01:51.840474+00:00
-- url     : https://prove2.me/submissions/9023dd55-2153-4720-933e-16f3b5edf6d8


import Definitions.Def_FongoSync_Clock

set_option autoImplicit false
open FongoSync
namespace FongoSync
namespace Hlc
theorem _root_.solution {a b c : Hlc} (h₁ : a.NotAfter b) (h₂ : b.NotAfter c) :
    a.NotAfter c := by
  unfold Hlc.NotAfter at *; omega
end Hlc
end FongoSync
