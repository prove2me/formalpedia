-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.card_periodicTailOverlap_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:02:50.696505+00:00
-- url     : https://prove2.me/submissions/464073c5-82ca-497b-b106-11aa1506b90c

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_TerminalRays
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_RayCompatibility
public import Theorems.Thm_DeciSigma1_Holes_Tail_periodicOn_of_rayAgrees
public import Theorems.Thm_DeciSigma1_Holes_Periodic_FollowerEdge_symm
public import Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_period_pos
public import Theorems.Thm_DeciSigma1_Holes_Tail_NoSuffixOccurrenceEndsBetween_mono
public import Theorems.Thm_DeciSigma1_Holes_Tail_PeriodicCover_mono
public import Theorems.Thm_DeciSigma1_Holes_Tail_RayAgrees_stream_eq
public import Theorems.Thm_DeciSigma1_Holes_Tail_card_le_card_sub_one_of_injOn
public import Theorems.Thm_DeciSigma1_Holes_Tail_firstRejection_sub_lt_word
public import Theorems.Thm_DeciSigma1_Holes_Tail_no_early_repeat
public import Theorems.Thm_DeciSigma1_Readers_StructuralReader_Eligible_runPrefix_ne
public import Theorems.Thm_DeciSigma1_Words_ChainBoundFrom_mono
public import Theorems.Thm_DeciSigma1_Words_ChainBound_mono
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_symm
public import Theorems.Thm_DeciSigma1_Words_PeriodicOn_mono
public import Theorems.Thm_DeciSigma1_Words_Ray_onset_le_of_periodicFrom
public import Theorems.Thm_DeciSigma1_Words_Ray_periodicFrom_period
public import Theorems.Thm_DeciSigma1_Words_streamPrefix_suffix_iff
public import Theorems.Thm_P2M_DeciSigma1_Holes_Tail_RayAgrees_getElem__ac7111bad97d


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Arithmetic DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Automata DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}
variable [DecidableEq α] [Fintype S]
    [DecidableEq S] {M : StructuralReader α S k} {W : Fin k → List α}
  {u v : Fin k} {Ωu : Ray α} {κ : Type} (R : Finset κ) (Ωc : κ → Ray α) (Ec : κ → ℕ)
omit [DecidableEq S]
namespace DeciSigma1.Holes.Tail
theorem _root_.solution (hu : M.Eligible W u) {Eu : ℕ} (hΩu : RayAgrees Ωu (W u) Eu)
    (hJu : M.firstRejection W u ≤ Eu) (hc : ∀ r ∈ R, RayAgrees (Ωc r) (W v) (Ec r))
    (hrun : ∀ r ∈ R, (Ωc r).onset + (Fintype.card S + 1) * Ωu.period ≤ Ec r)
    (hJc : ∀ r ∈ R, M.firstRejection W v < (Ωc r).onset)
    (hinj : Set.InjOn (fun r => (Ωc r).onset) R) :
    (R.filter (fun r => PeriodicTailOverlap (Ωc r) Ωu (M.firstRejection W v)
        (M.firstRejection W u))).card ≤
      Fintype.card S - 1 := by
  classical
  classical
  have hν : 0 < Ωu.period := Ray.period_pos
  have hNν : Fintype.card S * Ωu.period + Ωu.period = (Fintype.card S + 1) * Ωu.period := by ring
  apply card_le_card_sub_one_of_injOn _ (fun r => (Ωc r).onset)
      (hinj.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _)))
    (fun r => M.runPrefix W u (Ωu.onset - ((Ωc r).onset - M.firstRejection W v))) M.dead
  · intro s hs t ht hlt
    rw [Finset.mem_filter] at hs ht
    obtain ⟨hsR, hAu, hsuf, hal⟩ := hs
    obtain ⟨htR, -, hsuf', hal'⟩ := ht
    rw [Ray.suffixBeforeOnset, Ray.prefixBeforeOnset, streamPrefix_suffix_iff] at hsuf hsuf'
    have hrs := hrun s hsR
    have hrt := hrun t htR
    have hJs := hJc s hsR
    have hJt := hJc t htR
    -- `J_u - A_u < N ν_u`
    have hf := firstRejection_sub_lt_word hu hν (periodicOn_of_rayAgrees hΩu) hAu hJu
    -- the candidates are `ν_u`-periodic from their onsets
    have hpu := Ray.periodicFrom_period Ωu
    have hps : PeriodicFrom (Ωc s).stream (Ωc s).onset Ωu.period := by
      intro y; change (Ωc s).stream ((Ωc s).onset + (y + Ωu.period)) =
          (Ωc s).stream ((Ωc s).onset + y)
      rw [hal, hal]; exact hpu y
    -- the two onsets are more than `N ν_u` apart
    have hsep : (Ωc s).onset + Fintype.card S * Ωu.period < (Ωc t).onset := by
      by_contra hle
      push Not at hle
      have hpt : PeriodicFrom (Ωc t).stream (Ωc t).onset Ωu.period := by
        intro y; change (Ωc t).stream ((Ωc t).onset + (y + Ωu.period)) =
            (Ωc t).stream ((Ωc t).onset + y)
        rw [hal', hal']; exact hpu y
      have hagree : ∀ y < Ωu.period, (Ωc s).stream ((Ωc t).onset + y) =
          (Ωc t).stream ((Ωc t).onset + y) := fun y hy =>
        (hc s hsR).stream_eq (hc t htR) (by omega) (by omega)
      have hps' : StreamPeriod (fun y => (Ωc s).stream ((Ωc t).onset + y)) Ωu.period := by
        have := hps.mono (A' := (Ωc t).onset) (by omega)
        exact this
      have hext : ∀ y, (Ωc s).stream ((Ωc t).onset + y) = (Ωc t).stream ((Ωc t).onset + y) := by
        intro y
        have e1 := streamPeriod_mod hps' y
        have e2 := streamPeriod_mod hpt y
        rw [e1, e2]; exact hagree _ (Nat.mod_lt _ hν)
      have heqs : ∀ x, (Ωc s).onset ≤ x → (Ωc t).stream x = (Ωc s).stream x := by
        intro x hx
        by_cases hxt : x < (Ωc t).onset
        · exact (hc t htR).stream_eq (hc s hsR) (by omega) (by omega)
        · have := hext (x - (Ωc t).onset)
          rw [show (Ωc t).onset + (x - (Ωc t).onset) = x by omega] at this
          exact this.symm
      have hpts : PeriodicFrom (Ωc t).stream (Ωc s).onset Ωu.period := by
        intro y
        change (Ωc t).stream ((Ωc s).onset + (y + Ωu.period)) = (Ωc t).stream ((Ωc s).onset + y)
        rw [heqs _ (by omega), heqs _ (by omega)]
        exact hps y
      have := Ray.onset_le_of_periodicFrom hν hpts
      omega
    -- letters of `W u` from `a_s` and from `a_t` agree with `W v` from `J_v`
    have keys : ∀ y < M.firstRejection W u - (Ωu.onset - ((Ωc s).onset - M.firstRejection W v)),
        (W u)[Ωu.onset - ((Ωc s).onset - M.firstRejection W v) + y]? =
            (W v)[M.firstRejection W v + y]? := by
      intro y hy
      by_cases hyX : y < (Ωc s).onset - M.firstRejection W v
      · rw [hΩu.getElem? (by omega), (hc s hsR).getElem? (by omega), hsuf.2 y hyX]
      · have e1 : Ωu.onset - ((Ωc s).onset - M.firstRejection W v) + y =
            Ωu.onset + (y - ((Ωc s).onset - M.firstRejection W v)) := by omega
        have e2 : M.firstRejection W v + y = (Ωc s).onset +
            (y - ((Ωc s).onset - M.firstRejection W v)) := by
          omega
        rw [e1, e2, hΩu.getElem? (by omega), (hc s hsR).getElem? (by omega), hal]
    have keyt : ∀ y < (Ωc t).onset - M.firstRejection W v,
        (W u)[Ωu.onset - ((Ωc t).onset - M.firstRejection W v) + y]? =
            (W v)[M.firstRejection W v + y]? := by
      intro y hy
      rw [hΩu.getElem? (by omega), (hc t htR).getElem? (by omega), hsuf'.2 y hy]
    intro he
    apply no_early_repeat hu (a' := Ωu.onset - ((Ωc t).onset - M.firstRejection W v))
      (a := Ωu.onset - ((Ωc s).onset - M.firstRejection W v)) (by omega) (by omega) _ he.symm
    intro y hy
    rw [keyt y (by omega), keys y hy]
  · intro r _; exact hu.runPrefix_ne _
end DeciSigma1.Holes.Tail
