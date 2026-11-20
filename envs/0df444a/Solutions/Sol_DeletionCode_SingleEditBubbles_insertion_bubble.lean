-- Prove2me | solution 1 for DeletionCode.SingleEditBubbles.insertion_bubble
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:46:56.473947+00:00
-- url     : https://prove2.me/submissions/e2ecdb69-803b-4399-b6bf-87ac0294976a

import Definitions.Def_DeletionCode_RunBubbleConstruction
import Definitions.Def_DeletionCode_BubbleContextGeometry
import Definitions.Def_DeletionCode_TraceSeparation
import Definitions.Def_DeletionCode_SingleEditBubbles
import Theorems.Thm_DeletionCode_SingleEditBubbles_LocalBubble_geometry
import Theorems.Thm_DeletionCode_SingleEditBubbles_LocalBubble_spectrum_change
import Theorems.Thm_DeletionCode_CatalogueBridge_ValidCatalogue_geometry
import Theorems.Thm_DeletionCode_RunBubbleConstruction_exists_insertion_bubble


set_option autoImplicit true
open DeletionCode DeletionCode.SingleEditBubbles
open Windows HeaderRecovery CatalogueWords SignedSupport
open RunBubbleConstruction BubbleContextGeometry TraceSeparation
namespace DeletionCode.SingleEditBubbles
theorem _root_.solution (word : List Bool) (pos k : ℕ) (bit : Bool) (hk : 1 ≤ k)
    (hx : KUnique (listLetters word) word.length k)
    (hleft : 4 * windowLength k ≤ pos)
    (hright : pos + 4 * windowLength k ≤ word.length) :
    ∃ p : RunBubbleConstruction.LocalBubble k word
        (word.take pos ++ bit :: word.drop pos) pos .insertion,
      p.bubble.bit = bit ∧ Geometry p.bubble ∧
      wordSpectrum (listLetters (word.take pos ++ bit :: word.drop pos))
          (word.take pos ++ bit :: word.drop pos).length (windowLength k) -
        wordSpectrum (listLetters word) word.length (windowLength k) =
        wordSpectrum (listLetters p.bubble.positiveWord) p.bubble.positiveWord.length (windowLength k) -
          wordSpectrum (listLetters p.bubble.negativeWord) p.bubble.negativeWord.length (windowLength k) := by
  obtain ⟨p, hbit⟩ := exists_insertion_bubble word pos k bit hx hleft hright
  exact ⟨p, hbit, LocalBubble.geometry p hk hx, LocalBubble.spectrum_change p⟩
end DeletionCode.SingleEditBubbles
