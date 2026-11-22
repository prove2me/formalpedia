-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.exists_compatible_rayCandidate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:05:11.209441+00:00
-- url     : https://prove2.me/submissions/65fabd61-a22d-4b43-aad2-2b0a0e39974f

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_RayCompatibility
public import Mathlib.Order.Nat
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Candidates
public import Theorems.Thm_DeciSigma1_Holes_Tail_RayCandidate_agrees
public import Theorems.Thm_DeciSigma1_Holes_Tail_RayCandidate_onset_le
public import Theorems.Thm_DeciSigma1_Holes_Tail_exists_many_rayCandidates
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Tail_card_periodicTailOverlap_le
public import Theorems.Thm_DeciSigma1_Holes_Tail_card_prefixOverlap_le
public import Theorems.Thm_DeciSigma1_Holes_Tail_card_reversePrefixOverlap_le
public import Theorems.Thm_DeciSigma1_Holes_Tail_exists_forall_of_card_filter_not_le
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthBound_nil
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthEnvelope_nil
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_trans
public import Theorems.Thm_DeciSigma1_Words_Ray_length_suffixBeforeOnset
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
namespace DeciSigma1.Holes.Tail
theorem _root_.solution (C : LevelBounds (Fintype.card α) k (Fintype.card S))
    {M : StructuralReader α S k}
    {W : Fin k → List α} (hW : M.IsHole W) {v : Fin k} {l : ℕ} (hl : 1 ≤ l)
    (hM : ¬ CoordinateCover C l M W v) (ts : List (List α)) (hts : ts.length ≤ k)
    (hS : ∀ t ∈ ts, ChainBoundFrom t (C.startWindow l) (C.pieceCountBase + Fintype.card S))
    (U : Finset (Fin k)) (hvU : v ∉ U)
    (Ωu : Fin k → Ray α) (Eu : Fin k → ℕ)
    (hU : ∀ u ∈ U, RayAgrees (Ωu u) (W u) (Eu u) ∧ (Ωu u).onset ≤ Eu u ∧
      M.firstRejection W u ≤ Eu u ∧ ((Ωu u).onset ≤ M.firstRejection W u →
          (Ωu u).period ≤ C.periodBound (l - 1))) :
    ∃ x : RayCandidate M W ts v, C.startWindow l ≤ x.windowLength ∧
        M.firstRejection W v ≤ x.startCut ∧
        x.endCut - x.startCut ≤ C.periodBound l ∧
      (∀ t ∈ ts, NoSuffixOccurrenceEndsBetween (W v) t x.windowLength x.startCut x.endCut) ∧
          M.firstRejection W v <
          x.ray.onset ∧
      PeriodicCover ((W v).take x.startCut) (M.firstRejection W v) (C.pieceCountBase + 2)
          (C.periodBound l)
        ((C.pieceCountBase + 3) * (3 * C.escapeLengthBound l + 3)) ∧
      ∀ u ∈
          U, NoForbiddenRayOverlap x.ray (Ωu u) (M.firstRejection W v) (M.firstRejection W u) := by
  classical
  obtain ⟨n, cand, R, hc, hinj, hJc, hR, hcov⟩ := exists_many_rayCandidates C (hW.1 v) hM ts hts hS
  have hagc : ∀ r ∈ R, RayAgrees (cand r).ray (W v) (cand r).endCut := fun r _ => (cand r).agrees
  have hAc : ∀ r ∈ R, (cand r).ray.onset ≤ (cand r).endCut := fun r _ => by
    have := (cand r).onset_le; have := (cand r).closed.1; omega
  have hbad : ∀ u ∈
      U, (R.filter (fun r => ¬ NoForbiddenRayOverlap (cand r).ray (Ωu u) (M.firstRejection W v)
      (M.firstRejection W u))).card ≤ 2 * (Fintype.card S - 1) := by
    intro u hu
    obtain ⟨hag, hAu, hJu, hpu⟩ := hU u hu
    have hsub : R.filter
        (fun r => ¬ NoForbiddenRayOverlap (cand r).ray (Ωu u) (M.firstRejection W v)
            (M.firstRejection W u)) ⊆
        R.filter
            (fun r => PrefixOverlap (cand r).ray (Ωu u) (M.firstRejection W v)
                (M.firstRejection W u)) ∪
        R.filter
            (fun r => PeriodicTailOverlap (cand r).ray (Ωu u) (M.firstRejection W v)
                (M.firstRejection W u)) ∪
        R.filter
            (fun r => ReversePrefixOverlap (cand r).ray (Ωu u) (M.firstRejection W v)
                (M.firstRejection W u)) := by
      intro r hr
      rw [Finset.mem_filter] at hr
      simp only [Finset.mem_union, Finset.mem_filter]
      unfold NoForbiddenRayOverlap at hr
      by_cases h1 : PrefixOverlap (cand r).ray (Ωu u) (M.firstRejection W v) (M.firstRejection W u)
      · exact Or.inl (Or.inl ⟨hr.1, h1⟩)
      by_cases h2 : PeriodicTailOverlap (cand r).ray (Ωu u) (M.firstRejection W v)
          (M.firstRejection W u)
      · exact Or.inl (Or.inr ⟨hr.1, h2⟩)
      by_cases h3 : ReversePrefixOverlap (cand r).ray (Ωu u) (M.firstRejection W v)
          (M.firstRejection W u)
      · exact Or.inr ⟨hr.1, h3⟩
      exact absurd ⟨h1, h2, h3⟩ hr.2
    have h1 :=
        card_prefixOverlap_le R (fun r => (cand r).ray) (fun r => (cand r).endCut) (hW.1 u) hag hAu
      hagc hAc hinj
    have h2 := card_reversePrefixOverlap_le (u := u) (Ωu := Ωu u) R (fun r => (cand r).ray)
      (fun r => (cand r).endCut) (hW.1 v) hagc hAc hJc hinj
    have hcu := (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _))
    by_cases hAJ : (Ωu u).onset ≤ M.firstRejection W u
    · have hrun : ∀ r ∈ R, (cand r).ray.onset + (Fintype.card S + 1) * (Ωu u).period ≤
          (cand r).endCut := by
        intro r hr
        have h1 := (cand r).onset_le
        have h2 := (hc r).1
        have h3 := C.startWindow_gt (l - 1)
        rw [show l - 1 + 1 = l by omega] at h3
        have h4 : (Fintype.card S + 1) * (Ωu u).period ≤ (Fintype.card S + 1) *
            C.periodBound (l - 1) :=
          Nat.mul_le_mul_left _ (hpu hAJ)
        have h5 := (cand r).windowLength_lt
        have h6 := (cand r).closed.1
        omega
      have h3 :=
          card_periodicTailOverlap_le R (fun r => (cand r).ray) (fun r => (cand r).endCut)
              (hW.1 u) hag hJu
        hagc hrun hJc hinj
      have h0 : R.filter
          (fun r => PrefixOverlap (cand r).ray (Ωu u) (M.firstRejection W v)
              (M.firstRejection W u)) = ∅ :=
        Finset.filter_false_of_mem (fun r _ h => by have := h.1; omega)
      rw [h0, Finset.card_empty] at hcu
      omega
    · have h0 : R.filter
        (fun r => PeriodicTailOverlap (cand r).ray (Ωu u) (M.firstRejection W v)
            (M.firstRejection W u)) = ∅ :=
        Finset.filter_false_of_mem (fun r _ h => hAJ h.1)
      rw [h0, Finset.card_empty] at hcu
      omega
  have hU1 : U.card ≤ k - 1 := by
    have hsub : U ⊆ Finset.univ.erase v :=
      fun u hu => Finset.mem_erase.mpr ⟨fun h => hvU (h ▸ hu), Finset.mem_univ _⟩
    have := Finset.card_le_card hsub
    rwa [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at this
  -- `|U| · 2 (N - 1) ≤ 2 (k - 1) (N - 1) < Q - 1 ≤ |R|`
  obtain ⟨r, hr, hrc⟩ := exists_forall_of_card_filter_not_le _ hbad (by
    have hQ := C.pieceCountBase_eq
    have e1 : U.card * (2 * (Fintype.card S - 1)) ≤ (k - 1) * (2 * (Fintype.card S - 1)) :=
      Nat.mul_le_mul_right _ hU1
    have e2 : (k - 1) * (2 * (Fintype.card S - 1)) = 2 * (k - 1) * (Fintype.card S - 1) := by ring
    omega)
  exact ⟨cand r, (hc r).1, (hc r).2.1, (hc r).2.2.1, (hc r).2.2.2, hJc r hr, hcov r hr, hrc⟩
end DeciSigma1.Holes.Tail
