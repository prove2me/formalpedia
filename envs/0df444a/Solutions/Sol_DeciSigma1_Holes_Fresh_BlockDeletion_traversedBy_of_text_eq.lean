-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.BlockDeletion.traversedBy_of_text_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:34:36.677831+00:00
-- url     : https://prove2.me/submissions/47dc9e30-e6e3-41e8-b430-1b905fcac439

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_DeletionCoordinates
public import Mathlib.Order.Nat
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelTransport
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_upperCutLength_spec
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_active_t_of_through
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_deletionMargin_gt
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_maxDepth_lt_endDepth
public import Theorems.Thm_DeciSigma1_Holes_Fresh_Edge_commonSuffixLength_le_startDepth
public import Theorems.Thm_DeciSigma1_Holes_Fresh_Edge_through_iff
public import Theorems.Thm_DeciSigma1_Holes_Fresh_anchorCount_anti
public import Theorems.Thm_DeciSigma1_Holes_Fresh_anchorCount_self
public import Theorems.Thm_DeciSigma1_Holes_Fresh_anchorCount_shift
public import Theorems.Thm_DeciSigma1_Holes_Fresh_anchors_eq_contextAnchors
public import Theorems.Thm_DeciSigma1_Holes_Fresh_anchors_succ_subset
public import Theorems.Thm_DeciSigma1_Holes_Fresh_card_prefixOccurrenceCuts_le
public import Theorems.Thm_DeciSigma1_Holes_Fresh_commonSuffixLength_comm
public import Theorems.Thm_DeciSigma1_Holes_Fresh_contextAnchors_le_length
public import Theorems.Thm_DeciSigma1_Holes_Fresh_contextAnchors_pos
public import Theorems.Thm_DeciSigma1_Holes_Fresh_crossBoundaryMarkerEnds_lt_inside
public import Theorems.Thm_DeciSigma1_Holes_Fresh_crossBoundaryMarkerEnds_subset_prefixOccurrenceCuts
public import Theorems.Thm_DeciSigma1_Holes_Fresh_depthCutAt_shift
public import Theorems.Thm_DeciSigma1_Holes_Fresh_depthCutAt_spec
public import Theorems.Thm_DeciSigma1_Holes_Fresh_depthCut_spec
public import Theorems.Thm_DeciSigma1_Holes_Fresh_getElem_reversedBlocks
public import Theorems.Thm_DeciSigma1_Holes_Fresh_le_commonPrefixLength_iff
public import Theorems.Thm_DeciSigma1_Holes_Fresh_le_length_of_mem_anchors
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_marker_one
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_reversedBlocks
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_upperSeq
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_occurrences_in_next_marker
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_one
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_contextAnchors_of_mem_anchors_of_lt_length
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_contextAnchors_succ
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_relAnchors_iff
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_upperOcc
public import Theorems.Thm_DeciSigma1_Holes_Fresh_min_le_commonSuffixLength
public import Theorems.Thm_DeciSigma1_Holes_Fresh_prefix_drop_of_occ
public import Theorems.Thm_DeciSigma1_Holes_Fresh_previousAnchor_le
public import Theorems.Thm_DeciSigma1_Holes_Fresh_previousAnchor_spec
public import Theorems.Thm_DeciSigma1_Holes_Fresh_relativeAnchors_eq_union
public import Theorems.Thm_DeciSigma1_Holes_Fresh_segment_eq
public import Theorems.Thm_DeciSigma1_Holes_Fresh_suffix_take_iff
public import Theorems.Thm_DeciSigma1_Holes_Fresh_upperOcc_spec
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
public import Theorems.Thm_DeciSigma1_Words_deletePositions_empty
public import Theorems.Thm_DeciSigma1_Words_deletePositions_nil
public import Theorems.Thm_DeciSigma1_Words_greatestPreimage_empty
public import Theorems.Thm_DeciSigma1_Words_retainedCount_empty
public import Theorems.Thm_DeciSigma1_Words_retainedCount_greatestPreimage
public import Theorems.Thm_DeciSigma1_Words_retainedCount_zero
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Holes.Fresh.length_reversedBlocks
attribute [local simp] DeciSigma1.Holes.Fresh.length_upperSeq
attribute [local simp] DeciSigma1.Holes.Fresh.marker_zero
attribute [local simp] DeciSigma1.Holes.Fresh.mem_active_one
attribute [local simp] DeciSigma1.Holes.Fresh.mem_active_zero
attribute [local simp] DeciSigma1.Words.deletePositions_empty
attribute [local simp] DeciSigma1.Words.deletePositions_nil
attribute [local simp] DeciSigma1.Words.greatestPreimage_empty
attribute [local simp] DeciSigma1.Words.retainedCount_empty
attribute [local simp] DeciSigma1.Words.retainedCount_greatestPreimage
attribute [local simp] DeciSigma1.Words.retainedCount_zero
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc


section
@[expose] public section
namespace DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
section Sites
variable {α : Type} [DecidableEq α] {k : ℕ} {S : Type} [Fintype S]
namespace BlockDeletion
variable {T : Table α S k} {W : Fin k → List α} {t : ℕ} (m : BlockDeletion T W t)
private theorem anchorCount_min_eq_card (Q : Finset ℕ) (hQ : Q.Nonempty) {n : ℕ}
    (hQle : ∀ q ∈ Q, q ≤ n) : anchorCount Q (Q.min' hQ) n + 1 = Q.card := by
  have hqmQ := Q.min'_mem hQ
  have hf : Q.filter (fun q => Q.min' hQ < q ∧ q ≤ n) = Q.erase (Q.min' hQ) := by
    ext q
    simp only [mem_filter, mem_erase]
    constructor
    · rintro ⟨hq, h1, -⟩; exact ⟨by omega, hq⟩
    · rintro ⟨h1, hq⟩
      exact ⟨hq, lt_of_le_of_ne (Q.min'_le q hq) (Ne.symm h1), hQle q hq⟩
  rw [anchorCount, hf, card_erase_of_mem hqmQ]
  have := card_pos.mpr hQ
  omega
private theorem reversedBlocks_take_eq_of_depthCuts
    {W : Fin k → List α} {t : ℕ} {o₁ o₂ : Fin k × ℕ × ℕ}
    {Q : Finset ℕ} {qm n c₁ c₂ D : ℕ} {z : List α}
    (hqmQ : qm ∈ Q) (hnQ : n ∈ Q) (hqmn : qm ≤ n) (hDdef : D = anchorCount Q qm n)
    (hnlow₁ : D ≤ lowerBlockCount W t o₁) (hnlow₂ : D ≤ lowerBlockCount W t o₂)
    (hdc₁ : ∀ d ≤ D, depthCut W t o₁ d = c₁ + depthCutAt Q n d)
    (hdc₂ : ∀ d ≤ D, depthCut W t o₂ d = c₂ + depthCutAt Q n d)
    (hz₁ : ((W o₁.1).drop c₁).take n = z) (hz₂ : ((W o₂.1).drop c₂).take n = z) :
    (reversedBlocks W t o₁).take D = (reversedBlocks W t o₂).take D := by
  have hr : ∀ d < D, depthCutAt Q n (d + 1) < depthCutAt Q n d ∧ depthCutAt Q n d ≤ n := by
    intro d hd
    have hlt : qm < n := by
      rcases Nat.eq_or_lt_of_le hqmn with h | h
      · rw [hDdef, h, anchorCount_self] at hd; omega
      · exact h
    obtain ⟨hall, -⟩ := depthCutAt_spec hlt hnQ (Or.inr hqmQ)
    obtain ⟨hrQ, hlr, hrn, -⟩ := hall d (by omega)
    exact ⟨(previousAnchor_spec ⟨qm, hqmQ, hlr⟩).2, hrn⟩
  apply List.ext_getElem
  · simp only [List.length_take, length_reversedBlocks]; omega
  · intro d h1 h2
    have hd : d < D := by simp only [List.length_take, length_reversedBlocks] at h1; omega
    obtain ⟨hlt, hle⟩ := hr d hd
    simp only [List.getElem_take, getElem_reversedBlocks]
    rw [hdc₁ d hd.le, hdc₁ (d + 1) hd, hdc₂ d hd.le, hdc₂ (d + 1) hd,
      Nat.add_sub_add_left, Nat.add_sub_add_left,
      segment_eq hz₁ hlt.le hle, segment_eq hz₂ hlt.le hle]
end BlockDeletion
end Sites
end DeciSigma1.Holes.Fresh
end
end

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ} {S : Type} [Fintype S]
open DeciSigma1.Holes.Fresh.BlockDeletion
variable {T : Table α S k} {W : Fin k → List α} {t : ℕ} (m : BlockDeletion T W t)
namespace DeciSigma1.Holes.Fresh.BlockDeletion
theorem _root_.solution [DecidableEq S] (hfr : ∀ i, T.Fresh W i)
    {o₁ : Fin k × ℕ × ℕ} (ho₁ : o₁ ∈ upperOccurrences W t) (hth : m.edge.TraversedBy o₁)
    {l₂ : Fin k} {p₂ : ℕ} (hp₂ : p₂ ∈ anchors W (t + 1) l₂) (hn : m.upperCutLength ≤ p₂)
    (hz : ((W l₂).drop (p₂ - m.upperCutLength)).take m.upperCutLength =
      ((W o₁.1).drop (o₁.2.2 - m.upperCutLength)).take m.upperCutLength) :
    m.edge.TraversedBy (l₂, upperOccurrenceStart W t l₂ p₂, p₂) := by
  obtain ⟨hnt1, -, hnpos⟩ := m.upperCutLength_spec ho₁ hth
  have hE₁ := (upperOcc_spec ho₁).2.1
  have hbn := (m.edge.through_iff.mp hth).1
  have hin : m.minDepth <
      lowerBlockCount W t o₁ := by have := m.minDepth_lt_maxDepth;
                                   have := m.maxDepth_lt_endDepth; omega
  obtain ⟨hall₁, -⟩ := depthCut_spec ho₁
  have hs₁c : o₁.2.1 < depthCut W t o₁ m.minDepth := (hall₁ m.minDepth hin).2.1
  have hcnt : anchorCount (anchors W t o₁.1) (depthCut W t o₁ m.minDepth) o₁.2.2 = m.minDepth :=
    (hall₁ m.minDepth hin).2.2.2
  have hp₂len : p₂ ≤ (W l₂).length := le_length_of_mem_anchors hp₂
  have hl₂ : W l₂ ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hmg := m.deletionMargin_gt m.left_margin
  set n := m.upperCutLength with hndef
  set E₁ := o₁.2.2 with hE₁def
  set c₁ := E₁ - n with hc₁def
  have hc₁ : depthCut W t o₁ m.minDepth = c₁ := by omega
  rw [hc₁] at hs₁c hcnt
  set z := ((W o₁.1).drop c₁).take n with hzdef
  have hzlen : z.length = n := by simp [hzdef]; omega
  set u₁ := (W o₁.1).take c₁ with hu₁def
  set u₂ := (W l₂).take (p₂ - n) with hu₂def
  have hact₁ := m.active_t_of_through ho₁ hth
  have hanc₁ := anchors_eq_contextAnchors hact₁
  set Q := contextAnchors W t z with hQ
  have hrel : ∀ u, relativeAnchors W t u z = Q ∪ crossBoundaryMarkerEnds W t u z :=
      fun u => relativeAnchors_eq_union t u z
  have hQle : ∀ q ∈ Q, q ≤ n := fun q hq => hzlen ▸ contextAnchors_le_length hq
  have hA₁ : ∀ q, 1 ≤ q → q ≤ n →
      (c₁ + q ∈ anchors W t o₁.1 ↔ q ∈ Q ∪ crossBoundaryMarkerEnds W t u₁ z) := by
    intro q h1 h2
    rw [← hrel, mem_relAnchors_iff rfl (by omega) h1 h2, hanc₁]
  have hA₂ : ∀ q, 1 ≤ q → q < n →
      (p₂ - n + q ∈ anchors W t l₂ ↔ q ∈ Q ∪ crossBoundaryMarkerEnds W t u₂ z) := by
    intro q h1 h2
    rw [← hrel, mem_relAnchors_iff hz (by omega) h1 h2.le]
    exact
        ⟨fun h => mem_contextAnchors_of_mem_anchors_of_lt_length h (by omega),
            fun h => mem_insert_of_mem h⟩
  -- counting: at least `i - k (N - 1)` inside anchors
  have hcardSO : (crossBoundaryMarkerEnds W t u₁ z).card ≤ k * (Fintype.card S - 1) :=
    (card_le_card (crossBoundaryMarkerEnds_subset_prefixOccurrenceCuts u₁ z)).trans
        (card_prefixOccurrenceCuts_le hfr z)
  have hcardQ : m.minDepth ≤ Q.card + k * (Fintype.card S - 1) := by
    have hsub : (anchors W t o₁.1).filter (fun p => c₁ < p ∧ p ≤ E₁) ⊆
        (Q ∪ crossBoundaryMarkerEnds W t u₁ z).image (c₁ + ·) := by
      intro p hp
      rw [mem_filter] at hp
      rw [mem_image]
      refine ⟨p - c₁, (hA₁ (p - c₁) (by omega) (by omega)).mp ?_, by omega⟩
      rw [Nat.add_sub_cancel' (by omega)]; exact hp.1
    have h1 := card_le_card hsub
    have h2 := card_image_le (s := Q ∪ crossBoundaryMarkerEnds W t u₁ z) (f := (c₁ + ·))
    have h3 := card_union_le Q (crossBoundaryMarkerEnds W t u₁ z)
    unfold anchorCount at hcnt
    omega
  have hnQ : n ∈ Q := by
    have hE : c₁ + n ∈ anchors W t o₁.1 := by
      rw [show c₁ + n = E₁ by omega]; exact (upperOcc_spec ho₁).2.2.1
    rcases mem_union.mp ((hA₁ n hnpos le_rfl).mp hE) with h | h
    · exact h
    · exfalso
      have hQe : Q = ∅ := by
        rw [eq_empty_iff_forall_notMem]
        intro q hq
        have := crossBoundaryMarkerEnds_lt_inside h hq
        have := hQle q hq
        omega
      rw [hQe, card_empty] at hcardQ
      omega
  have hQne : Q.Nonempty := ⟨n, hnQ⟩
  set qm := Q.min' hQne with hqmdef
  have hqmQ : qm ∈ Q := Q.min'_mem hQne
  have hqm_le : ∀ q ∈ Q, qm ≤ q := fun q hq => Q.min'_le q hq
  have hqm1 : 1 ≤ qm := contextAnchors_pos hqmQ
  have hqmn : qm ≤ n := hqm_le n hnQ
  -- from the first inside anchor on, the anchors in `z` are those of `z` alone
  have hcross : ∀ u q, qm ≤ q → (q ∈ Q ∪ crossBoundaryMarkerEnds W t u z ↔ q ∈ Q) := by
    refine fun u q h1 => ⟨fun h => (mem_union.mp h).elim id fun h => ?_, mem_union_left _⟩
    have := crossBoundaryMarkerEnds_lt_inside h hqmQ
    omega
  have hag₁ : ∀ q, qm ≤ q → q ≤ n → (c₁ + q ∈ anchors W t o₁.1 ↔ q ∈ Q) := fun q h1 h2 => by
    rw [hA₁ q (by omega) h2, hcross _ q h1]
  have hag₂ : ∀ q, qm ≤ q → q ≤ n → (p₂ - n + q ∈ anchors W t l₂ ↔ q ∈ Q) := by
    intro q h1 h2
    rcases Nat.lt_or_ge q n with hlt | hge
    · rw [hA₂ q (by omega) hlt, hcross _ q h1]
    · have hq : q = n := by omega
      rw [hq, Nat.sub_add_cancel hn]
      exact ⟨fun _ => hnQ, fun _ => anchors_succ_subset t l₂ hp₂⟩
  set D := anchorCount Q qm n with hDdef
  have hdc₁ : ∀ d ≤ D, depthCut W t o₁ d = c₁ + depthCutAt Q n d := by
    intro d hd
    have := depthCutAt_shift hag₁ hqmQ hnQ hqmn d hd
    rw [show c₁ + n = E₁ by omega] at this
    exact this
  have hdc₂ : ∀ d ≤ D, depthCutAt (anchors W t l₂) p₂ d = p₂ - n + depthCutAt Q n d := by
    intro d hd
    have := depthCutAt_shift hag₂ hqmQ hnQ hqmn d hd
    rwa [Nat.sub_add_cancel hn] at this
  have hD : D + 1 = Q.card := anchorCount_min_eq_card Q hQne hQle
  -- the target's upper boundary is at or before the first inside anchor
  have hz' : ((W l₂).drop (p₂ - n)).take n = z := hz
  have hs₂ : upperOccurrenceStart W t l₂ p₂ ≤ p₂ - n + qm := by
    by_contra! hcon
    have hex : ∃ q ∈ anchors W (t + 1) l₂, q < p₂ := by
      by_contra hno
      have : upperOccurrenceStart W t l₂ p₂ ≤ 0 :=
        previousAnchor_le (fun q hq hqp => absurd ⟨q, hq, hqp⟩ hno)
      omega
    obtain ⟨hs₂A, hs₂p⟩ : upperOccurrenceStart W t l₂ p₂ ∈ anchors W (t + 1) l₂ ∧
        upperOccurrenceStart W t l₂ p₂ < p₂ := previousAnchor_spec hex
    have hs₂ctx := mem_contextAnchors_of_mem_anchors_of_lt_length hs₂A (by omega)
    obtain ⟨-, g, hg, hσ⟩ := (mem_contextAnchors_succ W).mp hs₂ctx
    set s₂ := upperOccurrenceStart W t l₂ p₂ with hs₂def
    have hσ' : marker W (t + 1) g <:+ (W l₂).take s₂ := hσ
    set d₂ := s₂ - (p₂ - n) with hd₂def
    have htk₂ : (W l₂).take s₂ = u₂ ++ z.take d₂ := by
      rw [show s₂ = (p₂ - n) + d₂ by omega, List.take_add, ← hz', List.take_take,
        Nat.min_eq_left (by omega)]
    obtain ⟨hσl, hσo⟩ := (suffix_take_iff (by omega)).mp hσ'
    rcases Nat.lt_or_ge d₂ (marker W (t + 1) g).length with hlong | hshort
    · -- the upper marker starts left of `z`: the factor antichain property bounds the anchors
      have ht : 1 ≤ t := by
        by_contra ht0
        have h0 : t = 0 := by omega
        have h1 : (marker W (t + 1) g).length = 1 := by
          rw [h0] at hg ⊢; exact length_marker_one hg
        omega
      have hge : ∀ q ∈ Q, d₂ ≤ q := by
        intro q hq
        by_contra hql
        have hql' : q < d₂ := Nat.lt_of_not_le hql
        obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
        obtain ⟨hqz, h, hh, hμ⟩ := (mem_contextAnchors_succ W).mp hq
        have hμl : (marker W (t' + 1) h).length ≤ q := by
          have := hμ.length_le; simp only [List.length_take] at this; omega
        have hμ₂ : marker W (t' + 1) h <:+ (W l₂).take (p₂ - n + q) := by
          rw [List.take_add, show ((W l₂).drop (p₂ - n)).take q = z.take q by
            rw [← hz', List.take_take, Nat.min_eq_left (by omega)]]
          exact hμ.trans (List.suffix_append _ _)
        obtain ⟨-, hμo⟩ := (suffix_take_iff (by omega)).mp hμ₂
        have hin' := prefix_drop_of_occ hσo hμo (by omega) (by omega)
        rcases (marker_occurrences_in_next_marker (by omega) hg).2.2 h hh _ hin' with
          h1 | h1 <;> omega
      have := hge qm hqmQ
      omega
    · -- the upper marker is inside `z`: an upper anchor strictly inside `o₁`
      have hσz : marker W (t + 1) g <:+ z.take d₂ := by
        rw [htk₂] at hσ'
        exact List.suffix_of_suffix_length_le hσ' (List.suffix_append _ _) (by simp; omega)
      have hσ₁ : marker W (t + 1) g <:+ (W o₁.1).take (c₁ + d₂) := by
        rw [List.take_add, show ((W o₁.1).drop c₁).take d₂ = z.take d₂ by
          rw [hzdef, List.take_take, Nat.min_eq_left (by omega)]]
        exact hσz.trans (List.suffix_append _ _)
      have hanc : c₁ + d₂ ∈ anchors W (t + 1) o₁.1 :=
        mem_insert_of_mem ((mem_contextAnchors_succ W).mpr ⟨by omega, g, hg, hσ₁⟩)
      exact (upperOcc_spec ho₁).2.2.2.2 _ hanc ⟨by omega, by omega⟩
  have ho₂ : (l₂, upperOccurrenceStart W t l₂ p₂, p₂) ∈ upperOccurrences W t :=
      mem_upperOcc.mpr ⟨hl₂, hp₂, rfl⟩
  have hnlow₂ : D ≤ lowerBlockCount W t (l₂, upperOccurrenceStart W t l₂ p₂, p₂) := by
    have h1 := anchorCount_shift (A := anchors W t l₂) hag₂
    rw [Nat.sub_add_cancel hn] at h1
    have h2 := anchorCount_anti (A := anchors W t l₂) (e := p₂) hs₂
    change D ≤ anchorCount (anchors W t l₂) (upperOccurrenceStart W t l₂ p₂) p₂
    omega
  have hnlow₁ : D ≤ lowerBlockCount W t o₁ := by
    have h1 := anchorCount_shift (A := anchors W t o₁.1) hag₁
    rw [show c₁ + n = E₁ by omega] at h1
    have h2 := anchorCount_anti (A := anchors W t o₁.1) (e := E₁) (show o₁.2.1 ≤ c₁ + qm by omega)
    change D ≤ anchorCount (anchors W t o₁.1) o₁.2.1 E₁
    omega
  have htake : (reversedBlocks W t o₁).take D =
      (reversedBlocks W t (l₂, upperOccurrenceStart W t l₂ p₂, p₂)).take D :=
    reversedBlocks_take_eq_of_depthCuts hqmQ hnQ hqmn hDdef hnlow₁ hnlow₂
      hdc₁ hdc₂ hzdef.symm hz'
  have hlcs : D ≤
      commonSuffixLength (upperParse W t o₁)
          (upperParse W t (l₂, upperOccurrenceStart W t l₂ p₂, p₂)) := by
    unfold commonSuffixLength upperParse
    rw [List.reverse_reverse, List.reverse_reverse, le_commonPrefixLength_iff]
    simp only [length_reversedBlocks]
    exact ⟨hnlow₁, hnlow₂, htake⟩
  have hDa : m.edge.startDepth < D := by omega
  have hb₁ : m.edge.endDepth ≤ commonSuffixLength (upperParse W t o₁) m.edge.blocks := hth
  have hmin :=
      min_le_commonSuffixLength m.edge.blocks (upperParse W t o₁)
          (upperParse W t (l₂, upperOccurrenceStart W t l₂ p₂, p₂))
  rw [commonSuffixLength_comm m.edge.blocks (upperParse W t o₁)] at hmin
  have hlow : m.edge.startDepth <
      commonSuffixLength m.edge.blocks (upperParse W t (l₂, upperOccurrenceStart W t l₂ p₂, p₂)) :=
    lt_of_lt_of_le (lt_min (by have := m.edge.startDepth_lt_endDepth; omega) (by omega)) hmin
  unfold Edge.TraversedBy
  by_contra hcon
  have hY : upperParse W t (l₂, upperOccurrenceStart W t l₂ p₂, p₂) ∈ upperParses W t :=
      mem_image_of_mem _ ho₂
  have := m.edge.commonSuffixLength_le_startDepth hY (by rw [commonSuffixLength_comm]; omega)
  omega
end DeciSigma1.Holes.Fresh.BlockDeletion
