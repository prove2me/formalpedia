-- Prove2me | solution 1 for Formalism.HermitianLattices.LocalLatticeBases.kernel_description
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:31:57.829627+00:00
-- url     : https://prove2.me/submissions/93b20acc-3aaf-41cd-b7b7-f770d0a37121

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_FourierTransformKernelSurjective
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ConditionIffDualEqFunctional
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.HermitianLattices.LocalLatticeBases
open Finset Matrix
private lemma nat_card_subtype_single {α : Type*} (C : α → Prop) (a0 : α) (P : Prop)
    (h : ∀ a, C a ↔ (a = a0 ∧ P)) :
    (P → Nat.card {a // C a} = 1) ∧ (¬ P → Nat.card {a // C a} = 0) := by
  constructor
  · intro hP
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨⟨fun a b => Subtype.ext (((h a).1 a.2).1.trans ((h b).1 b.2).1.symm)⟩,
      ⟨⟨a0, (h a0).2 ⟨rfl, hP⟩⟩⟩⟩
  · intro hP
    have : IsEmpty {a // C a} := ⟨fun a => hP ((h a).1 a.2).2⟩
    exact Nat.card_of_isEmpty
private lemma fraction_integer_iff_congruent (q : ℕ) [Fact q.Prime] (a : ℤ) (w : ZMod q) :
    ((a : ℚ) / q - ((w.val : ℕ) : ℚ) / q ∈ Set.range (Int.cast : ℤ → ℚ)) ↔ w = (a : ZMod q) := by
  have hq : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : q.Prime).ne_zero
  constructor
  · rintro ⟨m, hm⟩
    have h1 : (a : ℚ) - (w.val : ℚ) = q * m := by
      rw [hm]; field_simp
    have h2 : a - (w.val : ℤ) = q * m := by exact_mod_cast h1
    have h3 : ((a - (w.val : ℤ) : ℤ) : ZMod q) = ((q * m : ℤ) : ZMod q) := by rw [h2]
    push_cast at h3
    simp only [ZMod.natCast_val, ZMod.cast_id', id_eq, ZMod.natCast_self, zero_mul] at h3
    exact (sub_eq_zero.1 h3).symm
  · intro hw
    have h3 : ((a - (w.val : ℤ) : ℤ) : ZMod q) = 0 := by
      push_cast
      simp only [ZMod.natCast_val, ZMod.cast_id', id_eq]
      rw [hw, sub_self]
    obtain ⟨m, hm⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).1 h3
    refine ⟨m, ?_⟩
    have h1 : (a : ℚ) - (w.val : ℚ) = q * m := by exact_mod_cast hm
    rw [← sub_div, h1]; field_simp
section Count
variable {F : Type} [Field F]
variable [Fintype F]
end Count
section FJ
variable {F : Type} [Field F] [Fintype F]
end FJ
section Onto
open Formalism.LogVandermondeBounds.product_first_zeroth_parts
section FFOnto
variable {k : Type*} [Field k] [Fintype k] [DecidableEq k] {r : ℕ}
end FFOnto
end Onto
end Formalism.HermitianLattices.LocalLatticeBases
end

set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.LocalLatticeBases
open Finset Matrix
namespace Formalism.HermitianLattices.LocalLatticeBases
theorem _root_.solution : IndicatorKernelSum := by
  intro q _ n n' fW x0 x _ e1 intMat rhs UKcond KUcond
  have hq : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : q.Prime).ne_zero
  by_cases hI : intMat
  swap
  · have h1 : IsEmpty {xW // UKcond xW} := ⟨fun a => hI a.2.2.1⟩
    have h2 : IsEmpty {f // KUcond f} := ⟨fun a => hI a.2.2.1⟩
    refine ⟨by rw [Nat.card_of_isEmpty, Nat.card_of_isEmpty], fun h => absurd h.1 hI,
      fun _ => Nat.card_of_isEmpty⟩
  have hI' := hI
  choose X hX using hI'
  set y : Fin n' → ℤ := fun i => ∑ j, X i j * x0 j with hydef
  have hmv : ∀ (v : Fin n → ℚ) (i : Fin n'), x.mulVec v i = ∑ j, (X i j : ℚ) * v j := by
    intro v i
    simp only [Matrix.mulVec, dotProduct, hX]
  have hy : ∀ i, x.mulVec (fun j => (x0 j : ℚ)) i = (y i : ℚ) := by
    intro i
    rw [hmv, hydef]; push_cast; rfl
  have he1 : ∀ i, x.mulVec e1 i = (y i : ℚ) / q := by
    intro i
    rw [hmv, hydef]; push_cast
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun j _ => by simp only [e1]; ring)
  set Z : ℤ := ∑ i, fW i * y i with hZdef
  have hrhs : rhs ↔ (Z : ZMod q) = 1 := by
    constructor
    · rintro ⟨_, z, hz, hz1⟩
      have : (Z : ℚ) = z := by
        rw [← hz, hZdef]; push_cast
        exact Finset.sum_congr rfl (fun i _ => by rw [hy])
      have hZz : Z = z := by exact_mod_cast this
      rw [hZz]; exact hz1
    · intro h
      refine ⟨hI, Z, ?_, h⟩
      rw [hZdef]; push_cast
      exact Finset.sum_congr rfl (fun i _ => by rw [hy])
  have hKU : ∀ f, KUcond f ↔
      (f = (fun j => ((∑ i, fW i * X i j : ℤ) : ZMod q)) ∧ (Z : ZMod q) = 1) := by
    have key : ∑ j, ((∑ i, fW i * X i j : ℤ) : ZMod q) * (x0 j : ZMod q) = (Z : ZMod q) := by
      rw [hZdef, hydef]; push_cast
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
    intro f
    constructor
    · rintro ⟨h1, _, h3⟩
      have hf : f = (fun j => ((∑ i, fW i * X i j : ℤ) : ZMod q)) := by
        funext j
        obtain ⟨z, hz, hzf⟩ := h3 j
        have : ((∑ i, fW i * X i j : ℤ) : ℚ) = z := by
          rw [← hz]; push_cast
          exact Finset.sum_congr rfl (fun i _ => by rw [hX])
        have h' : (∑ i, fW i * X i j : ℤ) = z := by exact_mod_cast this
        rw [h', hzf]
      refine ⟨hf, ?_⟩
      rw [← key, ← h1, hf]
    · rintro ⟨hf, hP⟩
      refine ⟨?_, hI, fun j => ⟨∑ i, fW i * X i j, ?_, ?_⟩⟩
      · rw [hf, key, hP]
      · push_cast
        exact Finset.sum_congr rfl (fun i _ => by rw [hX])
      · rw [hf]
  have hUK : ∀ xW, UKcond xW ↔
      (xW = (fun i => (y i : ZMod q)) ∧ (Z : ZMod q) = 1) := by
    have key : ∑ i, (fW i : ZMod q) * (y i : ZMod q) = (Z : ZMod q) := by
      rw [hZdef]; push_cast; rfl
    intro xW
    constructor
    · rintro ⟨h1, _, h3, _⟩
      have hw : xW = (fun i => (y i : ZMod q)) := by
        funext i
        have := h3 i
        rw [he1] at this
        exact (fraction_integer_iff_congruent q (y i) (xW i)).1 this
      refine ⟨hw, ?_⟩
      rw [← key, ← h1, hw]
    · rintro ⟨hw, hP⟩
      have h3 : ∀ i, (y i : ℚ) / q - ((xW i).val : ℚ) / q ∈ Set.range (Int.cast : ℤ → ℚ) :=
        fun i => (fraction_integer_iff_congruent q (y i) (xW i)).2 (by rw [hw])
      refine ⟨?_, hI, fun i => by rw [he1]; exact h3 i, ?_⟩
      · rw [hw, key, hP]
      · intro l c
        choose m hm using h3
        refine ⟨fun i => (∑ j, X i j * l j) + c * m i, c, fun i => ?_⟩
        have hsplit : x.mulVec (fun j => (l j : ℚ) + c * e1 j) i =
            (∑ j, (X i j : ℚ) * l j) + c * x.mulVec e1 i := by
          rw [hmv, hmv, Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun j _ => by ring)
        rw [hsplit, he1]
        push_cast
        rw [hm i]
        ring
  obtain ⟨a1, a0⟩ := nat_card_subtype_single UKcond _ _ hUK
  obtain ⟨b1, b0⟩ := nat_card_subtype_single KUcond _ _ hKU
  refine ⟨?_, fun h => b1 (hrhs.1 h), fun h => b0 (fun hP => h (hrhs.2 hP))⟩
  by_cases hP : (Z : ZMod q) = 1
  · rw [a1 hP, b1 hP]
  · rw [a0 hP, b0 hP]
end Formalism.HermitianLattices.LocalLatticeBases
