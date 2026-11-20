-- Prove2me | solution 1 for DeletionCode.ScriptRigidity.shared_source_letters
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:20:44.347043+00:00
-- url     : https://prove2.me/submissions/c3cbc6ff-a987-492e-95fc-5e6fef01b745

import Definitions.Def_DeletionCode_EditRigidity
import Definitions.Def_DeletionCode_SingleEditScripts
import Definitions.Def_DeletionCode_ScriptRigidity
import Theorems.Thm_DeletionCode_EditRigidity_shared_source_letters
import Theorems.Thm_DeletionCode_SingleEditScripts_within_one_realized


set_option autoImplicit true
open DeletionCode DeletionCode.ScriptRigidity
open Windows HeaderRecovery CatalogueWords EditAlignment SingleEditOrigins
namespace DeletionCode.ScriptRigidity
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) (x y z : List Bool)
    (hx : KUnique (listLetters x) x.length k)
    (hy : WithinEdits 1 x y) (hz : WithinEdits 1 x z) (a b : ℕ)
    (ha : a + (windowLength k - 1) ≤ y.length)
    (hb : b + (windowLength k - 1) ≤ z.length)
    (hag : Agree (listLetters y) a (listLetters z) b (windowLength k - 1)) :
    ∃ e f : Edit, e.Valid x.length ∧ f.Valid x.length ∧
      e.outputLength x.length = y.length ∧ f.outputLength x.length = z.length ∧
      e.word (listLetters x) = listLetters y ∧ f.word (listLetters x) = listLetters z ∧
      ∃ s r : ℕ, s + k ≤ windowLength k - 1 ∧ r + k ≤ x.length ∧
        ∀ i, i < k →
          e.origin (a + s + i) = some (r + i) ∧
          f.origin (b + s + i) = some (r + i) := by
  obtain ⟨e, he, hlen, hword⟩ := SingleEditScripts.within_one_realized hy
  obtain ⟨f, hf, hlen', hword'⟩ := SingleEditScripts.within_one_realized hz
  refine ⟨e, f, he, hf, hlen, hlen', hword, hword', ?_⟩
  apply EditRigidity.shared_source_letters hk (listLetters x) hx e f he hf a b
  · simpa only [hlen] using ha
  · simpa only [hlen'] using hb
  · simpa only [hword, hword'] using hag
end DeletionCode.ScriptRigidity
