-- Prove2me | solution 1 for FongoSync.Clock.observe_notAfter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:59:43.302204+00:00
-- url     : https://prove2.me/submissions/daf35f9d-1083-46eb-8177-8e2ddfba25a5


import Definitions.Def_FongoSync_Clock

set_option autoImplicit false
open FongoSync
namespace FongoSync
namespace Clock
theorem _root_.solution (c : Clock) (remote : Hlc) :
    c.last.NotAfter (c.observe remote).last ∧
      (remote.encodable → remote.NotAfter (c.observe remote).last) := by
  unfold Clock.observe Hlc.NotAfter
  split
  · rename_i h; simp only [Hlc.encodable, true_and] at h ⊢; omega
  · rename_i h; simp only [Hlc.encodable, true_and] at h ⊢; omega
end Clock
end FongoSync
