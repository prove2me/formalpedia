-- Prove2me | solution 1 for FongoSync.Hlc.lt_of_before
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:58:40.512222+00:00
-- url     : https://prove2.me/submissions/10570457-05ad-459d-9d0c-48819201da1b


import Definitions.Def_FongoSync_Clock

set_option autoImplicit false
open FongoSync
namespace FongoSync
namespace Hlc
theorem _root_.solution {a b : Hlc} (h : a.Before b) : a < b := by
  rw [Hlc.lt_iff]; unfold Hlc.Before at h; omega
end Hlc
end FongoSync
