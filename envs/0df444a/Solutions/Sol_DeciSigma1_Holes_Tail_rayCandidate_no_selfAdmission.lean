-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.rayCandidate_no_selfAdmission
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:03:22.368387+00:00
-- url     : https://prove2.me/submissions/ebed396f-1edf-486e-84e8-11d7f528f475

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_RayCompatibility
public import Mathlib.Order.Nat
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Candidates
public import Theorems.Thm_DeciSigma1_Holes_Tail_rayState_eq_runPrefix
public import Theorems.Thm_DeciSigma1_Readers_StructuralReader_firstRejection_le
public import Theorems.Thm_DeciSigma1_Readers_Table_pair_mem_channel
public import Theorems.Thm_DeciSigma1_Words_Ray_suffix_eq_cases


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Arithmetic DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Automata DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}
namespace DeciSigma1.Holes.Tail
theorem _root_.solution [DecidableEq α] [DecidableEq S] {M : StructuralReader α S k}
    {W : Fin k → List α}
    (hW : M.IsHole W) {i : Fin k} {Ω : Ray α} {E : ℕ} (hag : RayAgrees Ω (W i) E)
    (hJE : M.firstRejection W i ≤ E) (hJA : M.firstRejection W i < Ω.onset) :
    ∀ a b, b ≤ M.firstRejection W i → a ≤ b →
      M.admitted (rayState M (M.start i) Ω a) (rayState M (M.start i) Ω b) = true →
      ¬ ∀ t, Ω.stream (a + t) = Ω.stream (b + t) := by
  intro a b hb hab hadm heq
  rcases Ray.suffix_eq_cases heq with ⟨_, h2⟩ | ⟨h1, h2⟩
  · omega
  · have hab' : a = b := by omega
    subst hab'
    have hJl := StructuralReader.firstRejection_le (hW.1 i)
    rw [rayState_eq_runPrefix M hag (by omega)] at hadm
    have h := hW.2 i i _ (pair_mem_channel (W := W) (a := a) (b := a) (by omega) (by omega)
      (List.prefix_refl _))
    rw [h] at hadm
    exact absurd hadm (by decide)
end DeciSigma1.Holes.Tail
