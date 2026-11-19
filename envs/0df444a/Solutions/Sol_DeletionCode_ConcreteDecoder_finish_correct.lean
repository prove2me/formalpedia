-- Prove2me | solution 1 for DeletionCode.ConcreteDecoder.finish_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:57:41.615812+00:00
-- url     : https://prove2.me/submissions/36216e42-ec47-4a5b-bb08-c101fe550c65

import Definitions.Def_DeletionCode_ConcreteFill
import Definitions.Def_DeletionCode_ConcreteStart
import Definitions.Def_DeletionCode_PathMemory
import Definitions.Def_DeletionCode_ConcreteDecoder
import Theorems.Thm_DeletionCode_ConcreteDecoder_finish_eq_some_iff
import Theorems.Thm_DeletionCode_PartialWords_readBits_sound


set_option autoImplicit true
open DeletionCode DeletionCode.ConcreteDecoder
open Windows PartialWords HeaderRecovery SelectedWindows
variable {B : Type*} [DecidableEq B]
namespace DeletionCode.ConcreteDecoder
theorem _root_.solution [Fintype B] (k : ℕ) (header : B → Header)
    (long : B → Letters) (mem : Bank B)
    (hs : ∀ b, Sound (mem b) (negativePath k (header b) (long b))
      (negativeLength k (header b)))
    (hknown : ∀ b, WindowKnown (mem b) 0 (negativeLength k (header b))) :
    finish k header mem = some (fun b i => negativePath k (header b) (long b) i.val) := by
  apply (finish_eq_some_iff k header mem _).mpr
  intro b
  obtain ⟨bits, hread⟩ := hknown b
  have hbits := readBits_sound (mem b) (negativePath k (header b) (long b))
    (negativeLength k (header b)) 0 (negativeLength k (header b))
    (hs b) (by omega) bits hread
  rw [hread]
  congr 1
  funext i
  simpa only [Nat.zero_add] using hbits i
end DeletionCode.ConcreteDecoder
