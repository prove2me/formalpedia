-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.exists_many_rayCandidates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:04:03.098726+00:00
-- url     : https://prove2.me/submissions/fe8b845d-8364-40e7-a59d-d8c868d44f37

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_RayCompatibility
public import Mathlib.Order.Nat
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Candidates
public import Theorems.Thm_DeciSigma1_Holes_Tail_RayCandidate_agrees
public import Theorems.Thm_DeciSigma1_Holes_Tail_RayCandidate_onset_le
public import Theorems.Thm_DeciSigma1_Holes_Tail_RayCandidate_period_le
public import Theorems.Thm_DeciSigma1_Holes_Tail_exists_initialSegment_transversal
public import Theorems.Thm_DeciSigma1_Holes_Tail_exists_periodicFactors_of_rays
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Tail_NoSuffixOccurrenceEndsBetween_mono
public import Theorems.Thm_DeciSigma1_Holes_Tail_PeriodicCover_mono
public import Theorems.Thm_DeciSigma1_Holes_Tail_RayAgrees_stream_eq_of_le
public import Theorems.Thm_DeciSigma1_Holes_Tail_exists_closed_factor_replicate
public import Theorems.Thm_DeciSigma1_Holes_Tail_factorLengthBound_mono
public import Theorems.Thm_DeciSigma1_Holes_Tail_periodicOn_take
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthBound_nil
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthEnvelope_nil
public import Theorems.Thm_DeciSigma1_Holes_Tail_uncoveredPositions_card_le
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
public import Theorems.Thm_DeciSigma1_Readers_StructuralReader_firstRejection_le
public import Theorems.Thm_DeciSigma1_Words_ChainBoundFrom_mono
public import Theorems.Thm_DeciSigma1_Words_ChainBound_mono
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_trans
public import Theorems.Thm_DeciSigma1_Words_PeriodicOn_mono
public import Theorems.Thm_DeciSigma1_Words_Ray_length_suffixBeforeOnset
public import Theorems.Thm_DeciSigma1_Words_Ray_onset_eq_of_stream_eq
public import Theorems.Thm_DeciSigma1_Words_length_suffixOfLength
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_cons_cons
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_nil
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_singleton
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Holes.Tail.suffixLengthBound_nil
attribute [local simp] DeciSigma1.Holes.Tail.suffixLengthEnvelope_nil
attribute [local simp] DeciSigma1.Words.Ray.length_suffixBeforeOnset
attribute [local simp] DeciSigma1.Words.length_suffixOfLength
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Arithmetic DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Automata DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}
variable [DecidableEq α] [Fintype α] [Fintype S] [DecidableEq S]
omit [DecidableEq S]
namespace DeciSigma1.Holes.Tail
theorem _root_.solution (C : LevelBounds (Fintype.card α) k (Fintype.card S))
    {M : StructuralReader α S k}
    {W : Fin k → List α} {v : Fin k} (hv : M.Eligible W v) {l : ℕ}
        (hM : ¬ CoordinateCover C l M W v)
    (ts : List (List α)) (hts : ts.length ≤ k)
        (hS : ∀ t ∈ ts, ChainBoundFrom t (C.startWindow l) (C.pieceCountBase + Fintype.card S)) :
    ∃ (n : ℕ) (cand : Fin n → RayCandidate M W ts v) (R : Finset (Fin n)),
      (∀ r, C.startWindow l ≤ (cand r).windowLength ∧ M.firstRejection W v ≤ (cand r).startCut ∧
        (cand r).endCut - (cand r).startCut ≤ C.periodBound l ∧ ∀ t ∈ ts,
            NoSuffixOccurrenceEndsBetween (W v) t (cand r).windowLength (cand r).startCut
                (cand r).endCut) ∧
      Set.InjOn (fun r => (cand r).ray.onset) R ∧
          (∀ r ∈ R, M.firstRejection W v < (cand r).ray.onset) ∧
      C.pieceCountBase - 1 ≤ R.card ∧
      ∀ r ∈
          R, PeriodicCover ((W v).take (cand r).startCut) (M.firstRejection W v)
              (C.pieceCountBase + 2) (C.periodBound l)
        ((C.pieceCountBase + 3) * (3 * C.escapeLengthBound l + 3)) := by
  classical
  set J := M.firstRejection W v with hJ
  set T := C.escapeLengthBound l with hTl
  have hPT : C.periodBound l < T :=
    C.periodBound_lt_escapeLengthBound (Fintype.card_pos_iff.mpr ⟨M.dead⟩) l
  have hJw : J ≤ (W v).length := StructuralReader.firstRejection_le hv
  set n := ((W v).length - J) / T with hn_def
  have hn : (W v).length < J + n * T + T := by
    have := Nat.lt_div_mul_add (a := (W v).length - J) (show 0 < T by omega)
    rw [← hn_def] at this; omega
  have hnT : n * T ≤ (W v).length - J := Nat.div_mul_le_self _ _
  -- one candidate in each segment `[J + m T, J + m T + T)`, `m < n`
  have hseg : ∀ m : Fin n, ∃ x : RayCandidate M W ts v, J + m * T ≤ x.startCut ∧
      x.endCut ≤ J + m * T + T ∧ C.startWindow l ≤ x.windowLength ∧
      x.endCut - x.startCut ≤ C.periodBound l ∧
      ∀ t ∈ ts, NoSuffixOccurrenceEndsBetween (W v) t x.windowLength x.startCut x.endCut := by
    intro m
    have : m * T + T ≤ n * T := by rw [← add_one_mul]; exact Nat.mul_le_mul_right _ m.isLt
    obtain ⟨B, c, c', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
      exists_closed_factor_replicate M.toTable (M.start v) (W v) ts hts hS (u := J + m * T)
        (bs := C.startWindow l) (by rw [← C.escapeLengthBound_eq]; omega)
    rw [← C.escapeLengthBound_eq] at h4
    rw [← C.comparisonWindow_eq] at h2
    exact ⟨⟨B, c, c', h5, h7⟩, h3, h4, h1,
      h8.trans ((factorLengthBound_mono _ _ h2).trans (C.factorLengthBound_le_periodBound l)), h6⟩
  choose cand hcand using hseg
  have hlt : ∀ m, (cand m).startCut < (cand m).endCut := fun m => (cand m).closed.1
  have hle : ∀ m, (cand m).endCut ≤ (W v).length := fun m => (cand m).closed.2.1
  have hper : ∀ m, (cand m).ray.period ≤ C.periodBound l := fun m =>
    (cand m).period_le.trans (hcand m).2.2.2.1
  -- the factors of the candidates of index `< m0` cover a position of each segment `m < r`
  -- below `cap`, so they leave at most `(|fs| + 1) · 2T` positions of `[J, cap)` uncovered
  have hcover : ∀ m0 r cap, r ≤ n → r ≤ m0 → cap ≤ (W v).length → cap ≤ J + r * T + T →
      (∀ m : Fin n, m.val < r → (cand m).startCut < cap) →
      ∃ fs : List PeriodicFactor,
        fs.length = ((Finset.univ.filter fun m : Fin n => m.val < m0).image
          fun m => (cand m).ray.onset).card ∧
        (∀ f ∈ fs, f.Valid (W v) (C.periodBound l) ∧ f.stop ≤ cap) ∧
        (uncoveredPositions fs J cap).card ≤ (fs.length + 1) * (2 * T) := by
    intro m0 r cap hrn hrm hcap hcapT hstart
    obtain ⟨fs, hlen, hval, hcov⟩ := exists_periodicFactors_of_rays _ (fun m => (cand m).ray)
      (fun m => (cand m).endCut) (fun m _ => (cand m).agrees) (fun m _ => hper m) hcap
    refine ⟨fs, hlen, hval, uncoveredPositions_card_le fs (by omega) hcapT fun m hm => ?_⟩
    have hmn : m < n := by omega
    have h1 : J + m * T ≤ (cand ⟨m, hmn⟩).startCut := (hcand ⟨m, hmn⟩).1
    have h2 : (cand ⟨m, hmn⟩).endCut ≤ J + m * T + T := (hcand ⟨m, hmn⟩).2.1
    refine ⟨_, h1, ?_, hstart _ hm, hcov _ ?_ _ ?_ (hlt _) (hstart _ hm)⟩
    · have := hlt ⟨m, hmn⟩; omega
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
    · exact (cand _).onset_le
  -- with at most `Q + 1` distinct onsets the tail would have a periodic cover at level `l`
  have hmany : C.pieceCountBase + 2 ≤ (Finset.univ.image fun m => (cand m).ray.onset).card := by
    by_contra hfew
    obtain ⟨fs, hlen, hval, hunc⟩ := hcover n n (W v).length le_rfl le_rfl le_rfl hn.le
      fun m _ => (hlt m).trans_le (hle m)
    rw [Finset.filter_true_of_mem fun m _ => m.isLt] at hlen
    refine hM ⟨fs, by omega, fun f hf => (hval f hf).1, hunc.trans ?_⟩
    calc (fs.length + 1) * (2 * T) ≤ (C.pieceCountBase + 2) * (3 * T + 3) :=
          Nat.mul_le_mul (by omega) (by omega)
      _ ≤ C.uncoveredBound l := C.uncoveredBound_ge_candidateBound l
  -- the first `Q + 2` distinct onsets
  obtain ⟨m0, R, hRm0, hinj, hRcard, hm0⟩ :=
    exists_initialSegment_transversal (fun m => (cand m).ray.onset) hmany
  -- at most three of them are at most `J`: those of index `0` and `1`, and one more, since two
  -- candidates of index at least `2` with onsets at most `J` are equal
  have hlow : (R.filter fun r => ¬ J < (cand r).ray.onset).card ≤ 3 := by
    have hsub : R.filter (fun r => ¬ J < (cand r).ray.onset) ⊆
        Finset.univ.filter (fun r : Fin n => r.val ≤ 1) ∪
          R.filter (fun r => 2 ≤ r.val ∧ (cand r).ray.onset ≤ J) := by
      intro r hr
      rw [Finset.mem_filter] at hr
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      by_cases h : r.val ≤ 1
      · exact Or.inl ⟨Finset.mem_univ _, h⟩
      · exact Or.inr ⟨hr.1, by omega, by omega⟩
    have h1 : (Finset.univ.filter fun r : Fin n => r.val ≤ 1).card ≤ 2 :=
      (Finset.card_le_card_of_injOn Fin.val (t := Finset.range 2)
        (fun r hr => by simp at hr ⊢; omega) Fin.val_injective.injOn).trans (by simp)
    have h2 : (R.filter fun r => 2 ≤ r.val ∧ (cand r).ray.onset ≤ J).card ≤ 1 := by
      refine Finset.card_le_one.mpr fun r1 hr1 r2 hr2 => ?_
      rw [Finset.mem_filter] at hr1 hr2
      refine hinj hr1.1 hr2.1 (Ray.onset_eq_of_stream_eq
        ((cand r1).agrees.stream_eq_of_le (cand r2).agrees ?_))
      have : 2 * T ≤ r1.val * T := Nat.mul_le_mul_right _ hr1.2.1
      have : 2 * T ≤ r2.val * T := Nat.mul_le_mul_right _ hr2.2.1
      have := (hcand r1).1; have := (hcand r2).1; have := hlt r1; have := hlt r2
      have := hper r1; have := hper r2
      omega
    calc _ ≤ _ := Finset.card_le_card hsub
      _ ≤ _ := Finset.card_union_le _ _
      _ ≤ 3 := by omega
  refine ⟨n, cand, R.filter fun r => J < (cand r).ray.onset,
    fun r => ⟨(hcand r).2.2.1, by have := (hcand r).1; omega, (hcand r).2.2.2⟩,
    hinj.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _)),
    fun r hr => (Finset.mem_filter.mp hr).2, ?_, fun r hr => ?_⟩
  · have := Finset.card_filter_add_card_filter_not (s := R) (p := fun r => J < (cand r).ray.onset)
    omega
  -- the tail before the factor of `r` is covered by the factors of the first `Q + 2` onsets
  have hr := hRm0 r (Finset.mem_filter.mp hr).1
  have hrw : (cand r).startCut ≤ (W v).length := (hlt r).le.trans (hle r)
  obtain ⟨fs, hlen, hval, hunc⟩ := hcover m0 r.val (cand r).startCut r.isLt.le hr.le hrw
    (by have := (hcand r).2.1; have := hlt r; omega) fun m hm => by
      have : m.val * T + T ≤ r.val * T := by
        rw [← add_one_mul]; exact Nat.mul_le_mul_right _ hm
      have := (hcand m).2.1; have := (hcand r).1; have := hlt m
      omega
  refine ⟨fs, by omega, fun f hf => ?_, ?_⟩
  · obtain ⟨⟨h1, h2, -, h4⟩, h5⟩ := hval f hf
    exact ⟨h1, h2, by rw [List.length_take]; omega, periodicOn_take h4 h5⟩
  · rw [List.length_take, min_eq_left hrw]
    exact hunc.trans (Nat.mul_le_mul (by omega) (by omega))
end DeciSigma1.Holes.Tail
