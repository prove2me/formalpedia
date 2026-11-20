-- Prove2me | solution 1 for DeletionCode.SeparatedTraceCoverage.catalogueRule
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:07:56.314047+00:00
-- url     : https://prove2.me/submissions/72d74db8-bdbd-432d-bc19-7a0a0047a354

import Definitions.Def_DeletionCode_TraceBubbleFamily
import Definitions.Def_DeletionCode_BubbleCatalogue
import Definitions.Def_DeletionCode_LocalBubbleDisjoint
import Definitions.Def_DeletionCode_TraceSpectrumAssembly
import Definitions.Def_DeletionCode_SeparatedTraceCoverage
import Theorems.Thm_DeletionCode_BubbleCatalogue_catalogueRule
import Theorems.Thm_DeletionCode_CatalogueBridge_ValidCatalogue_geometry
import Theorems.Thm_DeletionCode_ConnectedBlocks_RuleAdjacent_symm
import Theorems.Thm_DeletionCode_EditAlignment_Script_trans
import Theorems.Thm_DeletionCode_LocalBubbleDisjoint_localVertex_ne_of_trace
import Theorems.Thm_DeletionCode_SingleEditBubbles_LocalBubble_geometry
import Theorems.Thm_DeletionCode_SingleEditBubbles_LocalBubble_spectrum_change
import Theorems.Thm_DeletionCode_TraceEditData_card_deletionColumns
import Theorems.Thm_DeletionCode_TraceEditData_card_insertionColumns
import Theorems.Thm_DeletionCode_TraceSpectrumAssembly_spectrum_sum


set_option autoImplicit true
open DeletionCode DeletionCode.SeparatedTraceCoverage
open Windows HeaderRecovery CatalogueWords AlignmentTrace FiniteConflictGraph
open SignedSupport RunBubbleConstruction TraceEditData TraceBubbleFamily
open scoped BigOperators
namespace DeletionCode.SeparatedTraceCoverage
theorem _root_.solution (trace : Trace) (t k : ℕ) (hk : 1 ≤ k)
    (hx : KUnique (listLetters trace.source) trace.source.length k)
    (hsep : Separated (4 * windowLength k) trace)
    (hdel : trace.deletions = t) (hins : trace.insertions = t) :
    ConnectedBlocks.CatalogueRule t k
      (wordSpectrum (listLetters trace.target) trace.target.length (windowLength k) -
        wordSpectrum (listLetters trace.source) trace.source.length (windowLength k)) := by
  classical
  let E : Fin (2 * t) ≃ EditColumn trace := editEquiv trace t hdel hins
  let P := fun i : Fin (2 * t) => bubbleAt trace k hx hsep (E i)
  let words : Fin (2 * t) → BubbleWord k := fun i => (P i).bubble
  have hboundary : ∀ i, (words i).left.getLast? = some (!(words i).bit) ∧
      (words i).right.head? = some (!(words i).bit) :=
    fun i => ⟨(P i).left_boundary, (P i).right_boundary⟩
  have hgeometry : ∀ i, BubbleContextGeometry.Geometry (words i) :=
    fun i => SingleEditBubbles.LocalBubble.geometry (P i) hk hx
  have hdisjoint : ∀ a b : Fin (2 * t), a ≠ b → ∀ sa sb i j,
      i + (windowLength k - 1) ≤ (BubbleCatalogue.pathWord (words a) sa).length →
      j + (windowLength k - 1) ≤ (BubbleCatalogue.pathWord (words b) sb).length →
      SpectrumPath.vertexAt (listLetters (BubbleCatalogue.pathWord (words a) sa)) (windowLength k) i ≠
        SpectrumPath.vertexAt (listLetters (BubbleCatalogue.pathWord (words b) sb)) (windowLength k) j := by
    intro a b hab sa sb i j hi hj
    have hindices : (E a).val ≠ (E b).val := by
      intro heq
      exact hab (E.injective (Subtype.ext heq))
    exact LocalBubbleDisjoint.localVertex_ne_of_trace hk hx hsep
      (E a).val (E b).val (E a).property (E b).property hindices (P a) (P b)
      sa sb i j hi hj
  have hcount (o : Orientation) :
      (Finset.univ.filter (fun i => (words i).orientation = o)).card =
        Fintype.card {c : EditColumn trace // orientation trace c = o} := by
    calc
      _ = Fintype.card {i : Fin (2 * t) // (words i).orientation = o} :=
        (Fintype.card_subtype (fun i : Fin (2 * t) => (words i).orientation = o)).symm
      _ = _ := Fintype.card_congr (E.subtypeEquiv (by
        intro i
        change (P i).bubble.orientation = o ↔ orientation trace (E i) = o
        rw [(P i).orientation_eq]))
  have hdelWords : (Finset.univ.filter (fun i => (words i).orientation = .deletion)).card = t :=
    (hcount .deletion).trans ((card_deletionColumns trace).trans hdel)
  have hinsWords : (Finset.univ.filter (fun i => (words i).orientation = .insertion)).card = t :=
    (hcount .insertion).trans ((card_insertionColumns trace).trans hins)
  let delta := fun c : EditColumn trace =>
    wordSpectrum (listLetters (oneEditTarget trace c)) (oneEditTarget trace c).length (windowLength k) -
      wordSpectrum (listLetters trace.source) trace.source.length (windowLength k)
  have hsum :
      wordSpectrum (listLetters trace.target) trace.target.length (windowLength k) -
        wordSpectrum (listLetters trace.source) trace.source.length (windowLength k) =
      ∑ i : Fin (2 * t),
        (wordSpectrum (listLetters (words i).positiveWord) (words i).positiveWord.length (windowLength k) -
          wordSpectrum (listLetters (words i).negativeWord) (words i).negativeWord.length (windowLength k)) := by
    calc
      _ = ∑ c : EditColumn trace, delta c :=
        TraceSpectrumAssembly.spectrum_sum (by unfold windowLength; omega) hsep
      _ = ∑ i : Fin (2 * t), delta (E i) := (E.sum_comp delta).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        exact SingleEditBubbles.LocalBubble.spectrum_change (P i)
  rw [hsum]
  exact BubbleCatalogue.catalogueRule words hboundary hgeometry hdisjoint hdelWords hinsWords
end DeletionCode.SeparatedTraceCoverage
