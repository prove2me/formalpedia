-- Prove2me | solution 1 for DeletionCode.SingleEditBubbles.deletion_bubble
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:46:55.977004+00:00
-- url     : https://prove2.me/submissions/2a3b704b-173e-4b42-8228-b92b710e1a6e

import Definitions.Def_DeletionCode_RunBubbleConstruction
import Definitions.Def_DeletionCode_BubbleContextGeometry
import Definitions.Def_DeletionCode_TraceSeparation
import Definitions.Def_DeletionCode_SingleEditBubbles
import Theorems.Thm_DeletionCode_SingleEditBubbles_LocalBubble_geometry
import Theorems.Thm_DeletionCode_SingleEditBubbles_LocalBubble_spectrum_change
import Theorems.Thm_DeletionCode_CatalogueBridge_ValidCatalogue_geometry
import Theorems.Thm_DeletionCode_RunBubbleConstruction_exists_deletion_bubble


set_option autoImplicit true
open DeletionCode DeletionCode.SingleEditBubbles
open Windows HeaderRecovery CatalogueWords SignedSupport
open RunBubbleConstruction BubbleContextGeometry TraceSeparation
namespace DeletionCode.SingleEditBubbles
theorem _root_.solution (word : List Bool) (pos k : ℕ) (hk : 1 ≤ k)
    (hx : KUnique (listLetters word) word.length k)
    (hleft : 4 * windowLength k ≤ pos)
    (hright : pos + 4 * windowLength k ≤ word.length) :
    ∃ p : RunBubbleConstruction.LocalBubble k word (word.eraseIdx pos) pos .deletion,
      Geometry p.bubble ∧
      wordSpectrum (listLetters (word.eraseIdx pos)) (word.eraseIdx pos).length (windowLength k) -
        wordSpectrum (listLetters word) word.length (windowLength k) =
        wordSpectrum (listLetters p.bubble.positiveWord) p.bubble.positiveWord.length (windowLength k) -
          wordSpectrum (listLetters p.bubble.negativeWord) p.bubble.negativeWord.length (windowLength k) := by
  obtain ⟨p⟩ := exists_deletion_bubble word pos k hx hleft hright
  exact ⟨p, LocalBubble.geometry p hk hx, LocalBubble.spectrum_change p⟩
end DeletionCode.SingleEditBubbles
