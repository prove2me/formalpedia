-- Prove2me | solution 1 for FongoSync.Clock.observe_ignores
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:02:03.851683+00:00
-- url     : https://prove2.me/submissions/5866b95d-8769-4cb9-be7f-e8cb335af709


import Definitions.Def_FongoSync_Clock

set_option autoImplicit false
open FongoSync
namespace FongoSync
namespace Clock
theorem _root_.solution (c : Clock) (remote : Hlc) (h : ¬ remote.encodable) :
    c.observe remote = c := by
  simp [Clock.observe, h]
end Clock
end FongoSync
