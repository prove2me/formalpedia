-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.rays_no_positiveCycle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:05:04.218818+00:00
-- url     : https://prove2.me/submissions/80376302-d0e1-4998-a00c-5ccd30bacd7c

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_RayCompatibility
public import Mathlib.Order.Nat
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Candidates
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_le_local
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Tail_not_mem_closed_walk_of_noForbiddenRayOverlap
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthBound_nil
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthEnvelope_nil
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
namespace DeciSigma1.Holes.Tail
theorem _root_.solution [DecidableEq α] [Fintype S] {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : StructuralReader α S k) (st : ι → S) (Ω : ι → Ray α) (J : ι → ℕ) (L : ι → ℤ)
        (isM : ι → Prop)
    (hM : ∀ v, isM v → J v < (Ω v).onset ∧ ∀ u,
        u ≠ v → NoForbiddenRayOverlap (Ω v) (Ω u) (J v) (J u))
    (hT : ∀ i j, ¬ isM i → ¬ isM j → i ≠ j → ∀ a b, b ≤ J j →
      M.admitted (rayState M (st i) (Ω i) a) (rayState M (st j) (Ω j) b) = true →
      (∀ t, (Ω i).stream (a + t) = (Ω j).stream (b + t)) → L i + ((b : ℤ) - a + 1) ≤ L j) :
    ¬ (raySystem M st Ω J).HasPositiveCycle := by
  classical
  rintro ⟨i, p, hw, hpos⟩
  by_cases hex : ∃ v ∈ i :: p, isM v
  · obtain ⟨v, hv, hMv⟩ := hex
    exact not_mem_closed_walk_of_noForbiddenRayOverlap (M := M) (st := st) (Ω := Ω) (J := J)
        (hM v hMv).1 (hM v hMv).2 hw hv
  push Not at hex
  have hP : ∀ u v c, ¬ isM u → ¬ isM v → (raySystem M st Ω J).edgeWeight u v = some c → L u + c ≤
      L v := by
    intro u v c hu hv hc
    have hmem := Finset.mem_of_max hc
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hmem
    rw [Finset.mem_filter] at he
    obtain ⟨he, hi, hj⟩ := he
    simp only [rayEdges, Finset.mem_biUnion, Finset.mem_univ, true_and] at he
    obtain ⟨i', j', he⟩ := he
    split_ifs at he with hij
    · simp at he
    · obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨hab, hadm, heq⟩ := Finset.mem_filter.mp hab
      obtain ⟨-, hb⟩ := Finset.mem_product.mp hab
      simp only at hi hj ⊢
      subst hi hj
      exact hT i' j' hu hv hij a b (by have := Finset.mem_range.mp hb; omega) hadm heq
  have hw' : (raySystem M st Ω J).IsWalk (i :: (p ++ [i])) := by simpa using hw
  have h1 :=
      DifferenceSystem.weight_le_local (D := raySystem M st Ω J) (x := L) (fun z => ¬ isM z) hP i
    (p ++ [i]) hw' (by
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hex z List.mem_cons_self
      · rcases List.mem_append.mp hz with hz | hz
        · exact hex z (List.mem_cons_of_mem _ hz)
        · rw [List.mem_singleton] at hz; subst hz; exact hex z List.mem_cons_self)
  have h2 : (i :: (p ++ [i])).getLast (List.cons_ne_nil _ _) = i := by simp
  rw [h2] at h1
  have : (raySystem M st Ω J).weight (i :: p ++ [i]) =
      (raySystem M st Ω J).weight (i :: (p ++ [i])) :=
      rfl
  linarith
end DeciSigma1.Holes.Tail
