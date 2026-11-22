-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.exists_hole_compressed_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:06:36.255887+00:00
-- url     : https://prove2.me/submissions/a4681b56-4ddb-400c-b936-628edbbd8d3e

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Bound
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Transport
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_RunCovers
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Compression
public import Theorems.Thm_DeciSigma1_Holes_Tail_retainedCount_surj
public import Theorems.Thm_DeciSigma1_Holes_Tail_retainedCount_eq_add_card
public import Theorems.Thm_DeciSigma1_Holes_Tail_isPeriodicPiece_deletePositions
public import Theorems.Thm_DeciSigma1_Holes_Tail_pieceLengthBound_mono
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_coordinate
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_start
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_stop
public import Theorems.Thm_DeciSigma1_Holes_Periodic_FollowerEdge_symm
public import Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_root_length
public import Theorems.Thm_DeciSigma1_Holes_Periodic_cap_exists
public import Theorems.Thm_DeciSigma1_Holes_Periodic_editedTuple_dominates
public import Theorems.Thm_DeciSigma1_Holes_Periodic_editedTuple_firstRejection
public import Theorems.Thm_DeciSigma1_Holes_Periodic_exists_preserved_piece_of_nonconjugate_root
public import Theorems.Thm_DeciSigma1_Holes_Periodic_mem_piecesOf
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthBound_nil
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthEnvelope_nil
public import Theorems.Thm_DeciSigma1_Readers_Dominates_refl
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_refl
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
public import Theorems.Thm_DeciSigma1_Readers_StructuralReader_IsHole_of_dominates
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_length_eq
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_refl
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_symm
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_trans
public import Theorems.Thm_DeciSigma1_Words_Ray_length_suffixBeforeOnset
public import Theorems.Thm_DeciSigma1_Words_deletePositions_empty
public import Theorems.Thm_DeciSigma1_Words_deletePositions_nil
public import Theorems.Thm_DeciSigma1_Words_greatestPreimage_empty
public import Theorems.Thm_DeciSigma1_Words_length_deletePositions
public import Theorems.Thm_DeciSigma1_Words_length_suffixOfLength
public import Theorems.Thm_DeciSigma1_Words_retainedCount_empty
public import Theorems.Thm_DeciSigma1_Words_retainedCount_greatestPreimage
public import Theorems.Thm_DeciSigma1_Words_retainedCount_lt_of_not_mem
public import Theorems.Thm_DeciSigma1_Words_retainedCount_mono
public import Theorems.Thm_DeciSigma1_Words_retainedCount_zero
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_cons_cons
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_nil
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_singleton
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Holes.Periodic.AdmissibleDeletion.imagePiece_coordinate
attribute [local simp] DeciSigma1.Holes.Periodic.AdmissibleDeletion.imagePiece_start
attribute [local simp] DeciSigma1.Holes.Periodic.AdmissibleDeletion.imagePiece_stop
attribute [local simp] DeciSigma1.Holes.Tail.suffixLengthBound_nil
attribute [local simp] DeciSigma1.Holes.Tail.suffixLengthEnvelope_nil
attribute [local simp] DeciSigma1.Words.Ray.length_suffixBeforeOnset
attribute [local simp] DeciSigma1.Words.deletePositions_empty
attribute [local simp] DeciSigma1.Words.deletePositions_nil
attribute [local simp] DeciSigma1.Words.greatestPreimage_empty
attribute [local simp] DeciSigma1.Words.length_suffixOfLength
attribute [local simp] DeciSigma1.Words.retainedCount_empty
attribute [local simp] DeciSigma1.Words.retainedCount_greatestPreimage
attribute [local simp] DeciSigma1.Words.retainedCount_zero
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Holes.Periodic DeciSigma1.Readers DeciSigma1.Words
variable {α S : Type} {k : ℕ}
variable [DecidableEq α] [Fintype S] [DecidableEq S]
open Classical
namespace DeciSigma1.Holes.Tail
theorem _root_.solution (M : StructuralReader α S k) {U : Fin k → List α}
    (hU : M.IsHole U) {n D E : ℕ}
    (runs : Finset (RunSpec k)) (hcard : runs.card ≤ n + 1) (hruns : ∀ r ∈ runs, IsBoundedRun U D r)
    (hE : ∑ i,
        (if M.Immortal (M.endState U i) then (uncoveredTailPositions M U runs i).card else 0) ≤ E)
    (hne : runs.Nonempty) :
    ∃ U', M.IsHole U' ∧
      HasBoundedRunCover M U' n D (E + (n + 1) * Periodic.pieceLengthBound (Fintype.card S) D
        (k * (Fintype.card S - 1)) (2 * (n + 1) + E)) := by
  classical
  set N := Fintype.card S with hNdef
  set H := k * (N - 1)
  set T := 2 * (n + 1) + E
  obtain ⟨r0, hr0, hmax⟩ := Finset.exists_max_image runs RunSpec.period hne
  let P0 : Piece U r0.period := Piece.ofIsPeriodicPiece (hruns r0 hr0).1
  have hρ : IsPrimitive P0.root := P0.primitive
  have hρlen : P0.root.length = r0.period := P0.root_length
  set ρ := P0.root with hρdef
  have hρD : ρ.length ≤ D := hρlen ▸ (hruns r0 hr0).2.1
  have hle : ∀ r ∈ runs, r.period ≤ ρ.length := fun r hr => hρlen ▸ hmax r hr
  have hsplit : OccurrenceSplit U ρ H T :=
    occurrenceSplit M hU ρ runs (fun r hr => ⟨(hruns r hr).1, hle r hr⟩) (by
      dsimp [T]; omega)
  obtain ⟨x, hx, hcap⟩ := cap_exists N hρ hsplit
  have hdom := editedTuple_dominates M.toTable hx
  obtain ⟨hU', hends⟩ := StructuralReader.IsHole.of_dominates hU hdom
  have hJ' : ∀ l, M.firstRejection (editedTuple U ρ N x) l =
      keepCut U ρ N x l (M.firstRejection U l) :=
    editedTuple_firstRejection M hU hx
  have hN : 0 < N := Fintype.card_pos_iff.mpr ⟨M.dead⟩
  -- the class of a designated run
  let same : RunSpec k → Prop :=
      fun r => IsConjugate (((U r.coordinate).drop r.start).take r.period) ρ
  have hsame0 : same r0 := IsConjugate.refl _
  let img : RunSpec k → RunSpec k := fun r =>
    ⟨r.coordinate, keepCut U ρ N x r.coordinate r.start, keepCut U ρ N x r.coordinate r.stop,
        r.period⟩
  let runs' := (runs.filter (fun r => ¬ same r)).image img
  refine ⟨editedTuple U ρ N x, hU', runs', ?_, ?_, ?_⟩
  · -- at least one run fewer
    have : (runs.filter (fun r => ¬ same r)).card < runs.card :=
      Finset.card_lt_card (Finset.filter_ssubset.mpr ⟨r0, hr0, fun h => h hsame0⟩)
    exact Finset.card_image_le.trans (by omega)
  · -- the runs of the other classes survive at their retained cuts
    intro r' hr'
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hr'
    obtain ⟨hr, hns⟩ := Finset.mem_filter.mp hr
    obtain ⟨hpc, hdD, hlong⟩ := hruns r hr
    let R : Piece U r.period := Piece.ofIsPeriodicPiece hpc
    obtain ⟨hin, hleft, hright, -⟩ :=
        exists_preserved_piece_of_nonconjugate_root hx hN R hns (hle r hr)
      (by change ρ.length + r.period ≤ r.stop - r.start; omega)
    obtain ⟨hpc', hke⟩ := isPeriodicPiece_deletePositions (U' := editedTuple U ρ N x)
      (Dl := deletedPositions U ρ N x r.coordinate) rfl hpc hin hleft hright
    refine ⟨hpc', hdD, ?_⟩
    change 2 * D ≤ retainedCount (deletedPositions U ρ N x r.coordinate) r.stop -
        retainedCount (deletedPositions U ρ N x r.coordinate) r.start
    omega
  · -- the letters: original letters and the retained letters of the processed runs
    have hcapD : Periodic.pieceLengthBound N ρ.length H T ≤
        Periodic.pieceLengthBound N D H T :=
        pieceLengthBound_mono hρD
    have hword : ∀ i, (uncoveredTailPositions M (editedTuple U ρ N x) runs' i).card ≤
        (uncoveredTailPositions M U runs i).card +
          Periodic.pieceLengthBound N D H T *
              (runs.filter (fun r => r.coordinate = i ∧ same r)).card := by
      intro i
      have hsub : uncoveredTailPositions M (editedTuple U ρ N x) runs' i ⊆
          ((uncoveredTailPositions M U runs i) ∪
          (runs.filter (fun r => r.coordinate = i ∧ same r)).biUnion
            (fun r => (Finset.Ico r.start r.stop).filter (· ∉ deletedPositions U ρ N x i))).image
              (retainedCount (deletedPositions U ρ N x i)) := by
        intro p' hp'
        simp only [uncoveredTailPositions, Finset.mem_filter, Finset.mem_Ico] at hp'
        obtain ⟨⟨hJp, hpl⟩, hnc⟩ := hp'
        have hlen' : (editedTuple U ρ N x i).length =
            retainedCount (deletedPositions U ρ N x i) (U i).length := by
          rw [editedTuple, length_deletePositions]
        rw [hlen'] at hpl
        obtain ⟨p, hp, hpD, rfl⟩ := retainedCount_surj hpl
        rw [hJ' i] at hJp
        change retainedCount (deletedPositions U ρ N x i) (M.firstRejection U i) ≤
            retainedCount (deletedPositions U ρ N x i) p at hJp
        have hJp' : M.firstRejection U i ≤ p := by
          by_contra hcon
          have := retainedCount_lt_of_not_mem hpD (show p < M.firstRejection U i by omega)
          omega
        apply Finset.mem_image_of_mem
        by_cases hcov : RunCovers runs i p
        · obtain ⟨r, hr, hrl, h1, h2⟩ := hcov
          by_cases hs : same r
          · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨r,
              Finset.mem_filter.mpr ⟨hr, hrl, hs⟩,
              Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨h1, h2⟩, hpD⟩⟩)
          · exfalso
            apply hnc
            refine ⟨img r, Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hr, hs⟩), hrl,
              ?_, ?_⟩
            · change retainedCount (deletedPositions U ρ N x r.coordinate) r.start ≤
                retainedCount (deletedPositions U ρ N x i) p
              rw [hrl]; exact retainedCount_mono h1
            · change retainedCount (deletedPositions U ρ N x i) p <
                retainedCount (deletedPositions U ρ N x r.coordinate) r.stop
              rw [hrl]; exact retainedCount_lt_of_not_mem hpD h2
        · exact Finset.mem_union_left _ (by
            simp only [uncoveredTailPositions, Finset.mem_filter, Finset.mem_Ico]
            exact ⟨⟨hJp', hp⟩, hcov⟩)
      refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans
        ((Finset.card_union_le _ _).trans (Nat.add_le_add_left
          ((Finset.card_biUnion_le_card_mul _ _ _ fun r hr => ?_).trans_eq (Nat.mul_comm _ _)) _)))
      obtain ⟨hr, hrl, hs⟩ := Finset.mem_filter.mp hr
      obtain ⟨hpc, -, -⟩ := hruns r hr
      have hrd : (((U r.coordinate).drop r.start).take r.period).length = r.period := by
        have := hpc.1; have := hpc.2.1; simp; omega
      have hdeq : r.period = ρ.length := by
        have := hs.length_eq; rw [hrd] at this; exact this.symm
      have hpc' : IsPeriodicPiece U ρ.length r.coordinate r.start r.stop := hdeq ▸ hpc
      let R : Piece U ρ.length := Piece.ofIsPeriodicPiece hpc'
      have hRmem : R ∈ piecesOf U ρ := by
        rw [mem_piecesOf]
        change IsConjugate (((U r.coordinate).drop r.start).take ρ.length) ρ
        rw [← hdeq]; exact hs
      have hend := hx.retainedCount_piece_end R
      have hc := hcap R hRmem
      change retainedCount (deletedPositions U ρ N x r.coordinate) r.stop =
          retainedCount (deletedPositions U ρ N x r.coordinate) r.start +
        (r.stop - r.start - Periodic.statePeriodModulus N ρ.length * x R) at hend
      change r.stop - r.start - Periodic.statePeriodModulus N ρ.length * x R ≤
          Periodic.pieceLengthBound N ρ.length H T at hc
      rw [← hrl]
      have hkc :=
          retainedCount_eq_add_card (D := deletedPositions U ρ N x r.coordinate)
              (show r.start ≤ r.stop by
        have := hpc.1; omega)
      omega
    calc ∑ i, (if M.Immortal (M.endState (editedTuple U ρ N x) i) then
            (uncoveredTailPositions M (editedTuple U ρ N x) runs' i).card else 0)
        ≤ ∑ i,
            ((if M.Immortal (M.endState U i) then (uncoveredTailPositions M U runs i).card else 0) +
            Periodic.pieceLengthBound N D H T *
              (runs.filter (fun r => r.coordinate = i)).card) := by
          apply Finset.sum_le_sum
          intro i _
          rw [hends i]
          have hf : (runs.filter (fun r => r.coordinate = i ∧ same r)).card ≤
              (runs.filter (fun r => r.coordinate = i)).card :=
            Finset.card_le_card (fun r hr => by
              simp only [Finset.mem_filter] at hr ⊢; exact ⟨hr.1, hr.2.1⟩)
          have := Nat.mul_le_mul_left (Periodic.pieceLengthBound N D H T) hf
          split_ifs
          · have := hword i; omega
          · omega
      _ = (∑ i,
          (if M.Immortal (M.endState U i) then (uncoveredTailPositions M U runs i).card else 0)) +
            Periodic.pieceLengthBound N D H T * runs.card := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum,
            ← Finset.card_eq_sum_card_fiberwise (fun r _ => Finset.mem_univ (RunSpec.coordinate r))]
      _ ≤ E + (n + 1) * Periodic.pieceLengthBound N D H T := by
          have := Nat.mul_le_mul_left (Periodic.pieceLengthBound N D H T) hcard
          rw [Nat.mul_comm (n + 1)]
          omega
end DeciSigma1.Holes.Tail
