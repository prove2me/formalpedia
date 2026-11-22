-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.exists_closed_factor_replicate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:00:12.911004+00:00
-- url     : https://prove2.me/submissions/ff8eb1ce-d2ff-475f-99d3-4613d3b7ae6d

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Rays
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ClosedFactors
public import Theorems.Thm_DeciSigma1_Holes_Tail_exists_closed_factor_free_of_suffix_occurrences
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthBound_pad

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Words
variable {α S : Type} {k : ℕ}
variable [DecidableEq α] [Fintype S]
variable (T : Readers.Table α S k) (q0 : S) (x : List α)
namespace DeciSigma1.Holes.Tail
theorem _root_.solution (ts : List (List α)) {m Sb bs : ℕ} (hm : ts.length ≤ m)
    (hS : ∀ t ∈ ts, ChainBoundFrom t bs Sb) {u : ℕ}
    (hseg : u + suffixLengthBound m (Fintype.card S) (List.replicate m Sb) bs ≤ x.length) :
    ∃ B c c', bs ≤ B ∧ B ≤ suffixLengthEnvelope m (Fintype.card S) (List.replicate m Sb) bs ∧
      u ≤ c ∧ c' ≤ u + suffixLengthBound m (Fintype.card S) (List.replicate m Sb) bs ∧
      NodeClosedAt T q0 (suffixDictionary ts B) x c c' ∧
      (∀ t ∈ ts, NoSuffixOccurrenceEndsBetween x t B c c') ∧ B < c' - c ∧
      c' - c ≤ factorLengthBound m (Fintype.card S) B := by
  obtain ⟨ts', hsub, hF⟩ := suffixLengthBound_pad ts hm hS
  obtain ⟨B, c, c', h1, h2, h3, h4, h5, h6, h7⟩ :=
    exists_closed_factor_free_of_suffix_occurrences T q0 x ts hm bs ts' (List.replicate m Sb) hF
      bs u le_rfl (by omega)
  exact ⟨B, c, c', h1, h2, h3, h4.le, h5, fun t ht => h6 t (hsub t ht), h7⟩
end DeciSigma1.Holes.Tail
