-- Prove2me | solution 1 for FongoSync.Hlc.notAfter_refl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:01:52.566+00:00
-- url     : https://prove2.me/submissions/6b6c56e8-2d40-4a38-934d-2a9c623d475d


import Definitions.Def_FongoSync_Clock

set_option autoImplicit false
open FongoSync
namespace FongoSync
namespace Hlc
theorem _root_.solution (a : Hlc) : a.NotAfter a := by
  unfold Hlc.NotAfter; omega
end Hlc
end FongoSync
