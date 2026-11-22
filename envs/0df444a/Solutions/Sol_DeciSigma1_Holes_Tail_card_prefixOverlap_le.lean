-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.card_prefixOverlap_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:02:35.265493+00:00
-- url     : https://prove2.me/submissions/ed996524-3088-4635-953b-1e6424a34d05

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_TerminalRays
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_RayCompatibility
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Periodic_FollowerEdge_symm
public import Theorems.Thm_DeciSigma1_Holes_Tail_NoSuffixOccurrenceEndsBetween_mono
public import Theorems.Thm_DeciSigma1_Holes_Tail_PeriodicCover_mono
public import Theorems.Thm_DeciSigma1_Holes_Tail_card_le_card_sub_one_of_injOn
public import Theorems.Thm_DeciSigma1_Holes_Tail_no_early_repeat
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthBound_nil
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthEnvelope_nil
public import Theorems.Thm_DeciSigma1_Readers_StructuralReader_Eligible_runPrefix_ne
public import Theorems.Thm_DeciSigma1_Words_ChainBoundFrom_mono
public import Theorems.Thm_DeciSigma1_Words_ChainBound_mono
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_symm
public import Theorems.Thm_DeciSigma1_Words_PeriodicOn_mono
public import Theorems.Thm_DeciSigma1_Words_Ray_length_suffixBeforeOnset
public import Theorems.Thm_DeciSigma1_Words_length_suffixOfLength
public import Theorems.Thm_DeciSigma1_Words_streamPrefix_suffix_iff
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
public import Theorems.Thm_P2M_DeciSigma1_Holes_Tail_RayAgrees_getElem__ac7111bad97d
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
variable [DecidableEq α] [Fintype S]
    [DecidableEq S] {M : StructuralReader α S k} {W : Fin k → List α}
  {u v : Fin k} {Ωu : Ray α} {κ : Type} (R : Finset κ) (Ωc : κ → Ray α) (Ec : κ → ℕ)
omit [DecidableEq S]
namespace DeciSigma1.Holes.Tail
theorem _root_.solution (hu : M.Eligible W u) {Eu : ℕ} (hΩu : RayAgrees Ωu (W u) Eu)
    (hAu : Ωu.onset ≤ Eu) (hc : ∀ r ∈ R, RayAgrees (Ωc r) (W v) (Ec r))
    (hAc : ∀ r ∈ R, (Ωc r).onset ≤ Ec r) (hinj : Set.InjOn (fun r => (Ωc r).onset) R) :
    (R.filter (fun r => PrefixOverlap (Ωc r) Ωu (M.firstRejection W v)
        (M.firstRejection W u))).card ≤
      Fintype.card S - 1 := by
  classical
  classical
  apply card_le_card_sub_one_of_injOn _ (fun r => (Ωc r).onset)
      (hinj.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _)))
    (fun r => M.runPrefix W u (Ωu.onset - ((Ωc r).onset - M.firstRejection W v))) M.dead
  · intro r hr r' hr' hlt
    rw [Finset.mem_filter] at hr hr'
    obtain ⟨hrR, hJu, hsuf, hlen⟩ := hr
    obtain ⟨hrR', -, hsuf', hlen'⟩ := hr'
    rw [Ray.suffixBeforeOnset, Ray.prefixBeforeOnset, streamPrefix_suffix_iff] at hsuf hsuf'
    simp only [Ray.length_suffixBeforeOnset] at hlen hlen'
    have key : ∀ q ∈ R, (Ωc q).onset - M.firstRejection W v ≤ Ωu.onset →
        (∀ t < (Ωc q).onset - M.firstRejection W v, (Ωc q).stream (M.firstRejection W v + t) =
          Ωu.stream (Ωu.onset - ((Ωc q).onset - M.firstRejection W v) + t)) →
        ∀ t < (Ωc q).onset - M.firstRejection W v,
          (W u)[Ωu.onset - ((Ωc q).onset - M.firstRejection W v) + t]? =
              (W v)[M.firstRejection W v + t]? := by
      intro q hq h1 h2 t ht
      rw [hΩu.getElem? (by omega), (hc q hq).getElem? (by have := hAc q hq; omega), h2 t ht]
    intro he
    apply no_early_repeat hu (a' := Ωu.onset - ((Ωc r').onset - M.firstRejection W v))
      (a := Ωu.onset - ((Ωc r).onset - M.firstRejection W v)) (by omega) (by omega) _ he.symm
    intro t ht
    rw [key r' hrR' hsuf'.1 hsuf'.2 t (by omega), key r hrR hsuf.1 hsuf.2 t (by omega)]
  · intro r _; exact hu.runPrefix_ne _
end DeciSigma1.Holes.Tail
