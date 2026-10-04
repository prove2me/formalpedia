-- Prove2me | solution 1 for DiscreteConvex.AlgorithmsC.khat1_lift_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:21:47.321406+00:00
-- url     : https://prove2.me/submissions/4ed21e24-85fe-4f52-b1de-28042789d9d2

import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsC_LiftedFunctionL
import Definitions.Def_DiscreteConvex_AlgorithmsC_Khat1
import Definitions.Def_DiscreteConvex_AlgorithmsC_K1
import Definitions.Def_DiscreteConvex_AlgorithmsC_KInfty

set_option autoImplicit false

open DiscreteConvex.AlgorithmsC

namespace Khat1Bound

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

set_option linter.unusedSectionVars false

theorem linf_le_l1 (x : V → ℤ) : LInftyNorm x ≤ L1Norm x := by
  unfold LInftyNorm L1Norm
  refine Finset.sup'_le _ _ (fun v _ => ?_)
  exact Finset.single_le_sum (f := fun w => |x w|) (fun w _ => abs_nonneg _) (Finset.mem_univ v)

theorem l1_le_linf (x : V → ℤ) : L1Norm x ≤ (Fintype.card V : ℤ) * LInftyNorm x := by
  unfold LInftyNorm L1Norm
  calc ∑ v, |x v| ≤ ∑ _v : V, (Finset.univ : Finset V).sup' Finset.univ_nonempty
        (fun w => |x w|) := Finset.sum_le_sum (fun v _ => Finset.le_sup' (fun w => |x w|)
          (Finset.mem_univ v))
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem abs_le_linf (x : V → ℤ) (v : V) : |x v| ≤ LInftyNorm x :=
  Finset.le_sup' (fun w => |x w|) (Finset.mem_univ v)

/-- The key estimate for one lifted pair sharing a coordinate. -/
theorem lifted_pair (d : V → ℤ) (c : ℤ) (h : c = 0 ∨ ∃ v0, d v0 + c = 0) :
    |c| + ∑ v, |d v + c| ≤ L1Norm d + (Fintype.card V : ℤ) * LInftyNorm d := by
  have hL := linf_le_l1 d
  have hn : (0 : ℤ) ≤ Fintype.card V := by positivity
  have hI : 0 ≤ LInftyNorm d := le_trans (abs_nonneg _) (abs_le_linf d (Classical.arbitrary V))
  rcases h with rfl | ⟨v0, hv0⟩
  · simp only [abs_zero, add_zero, zero_add]
    have : (0 : ℤ) ≤ (Fintype.card V : ℤ) * LInftyNorm d := mul_nonneg hn hI
    unfold L1Norm; linarith
  · have hc : |c| ≤ LInftyNorm d := by
      have : c = -d v0 := by linarith
      rw [this, abs_neg]; exact abs_le_linf d v0
    have hG : ∑ v, (|d v| + |c|) = L1Norm d + (Fintype.card V : ℤ) * |c| := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; rfl
    have hsplitF := Finset.add_sum_erase (Finset.univ : Finset V) (fun v => |d v + c|)
      (Finset.mem_univ v0)
    have hsplitG := Finset.add_sum_erase (Finset.univ : Finset V) (fun v => |d v| + |c|)
      (Finset.mem_univ v0)
    have hrest : ∑ v ∈ Finset.univ.erase v0, |d v + c| ≤
        ∑ v ∈ Finset.univ.erase v0, (|d v| + |c|) :=
      Finset.sum_le_sum (fun v _ => abs_add_le _ _)
    rw [hv0, abs_zero] at hsplitF
    have : |c| + ∑ v, |d v + c| ≤ ∑ v, (|d v| + |c|) := by
      rw [← hsplitF, ← hsplitG]; have := abs_nonneg (d v0); linarith
    rw [hG] at this
    nlinarith

end Khat1Bound

open Khat1Bound in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (g : (V → ℤ) → WithTop ℝ) :
    (Khat1 (LiftedFunctionL g) : ℝ) ≤ (K1 g : ℝ) + (Fintype.card V : ℝ) * (KInfty g : ℝ) ∧
    (K1 g : ℝ) + (Fintype.card V : ℝ) * (KInfty g : ℝ) ≤
      min ((Fintype.card V + 1 : ℝ) * (K1 g : ℝ)) (2 * (Fintype.card V : ℝ) * (KInfty g : ℝ)) := by
  classical
  set n : ℤ := (Fintype.card V : ℤ) with hn_def
  have hn : (0 : ℤ) ≤ n := by positivity
  set S1 : Set ℤ := {k : ℤ | ∃ p q : V → ℤ, p ∈ DomZ g ∧ q ∈ DomZ g ∧
    k = L1Norm (fun v => p v - q v)} with hS1
  set SI : Set ℤ := {k : ℤ | ∃ p q : V → ℤ, p ∈ DomZ g ∧ q ∈ DomZ g ∧
    k = LInftyNorm (fun v => p v - q v)} with hSI
  set SH : Set ℤ := {k : ℤ | ∃ p q : Option V → ℤ, p ∈ DomZ (LiftedFunctionL g) ∧
    q ∈ DomZ (LiftedFunctionL g) ∧ (∃ v, p v = q v) ∧ k = L1Norm (fun v => p v - q v)} with hSH
  have eK1 : K1 g = sSup S1 := rfl
  have eKI : KInfty g = sSup SI := rfl
  have eKH : Khat1 (LiftedFunctionL g) = sSup SH := rfl
  -- the projection of a lifted point
  have proj : ∀ x : Option V → ℤ, x ∈ DomZ (LiftedFunctionL g) →
      (fun v => x (some v) - x none) ∈ DomZ g := fun x hx => hx
  -- the canonical lift of a point
  have lift : ∀ p : V → ℤ, p ∈ DomZ g →
      (fun w : Option V => w.elim 0 p) ∈ DomZ (LiftedFunctionL g) := by
    intro p hp
    show g (fun v => p v - 0) ≠ ⊤
    simp only [sub_zero]; exact hp
  have lift_norm : ∀ p q : V → ℤ, L1Norm (fun w : Option V => w.elim 0 p - w.elim 0 q) =
      L1Norm (fun v => p v - q v) := by
    intro p q; unfold L1Norm; rw [Fintype.sum_option]; simp
  -- generic bound for a lifted pair
  have pair : ∀ x y : Option V → ℤ, (∃ w, x w = y w) →
      L1Norm (fun w => x w - y w) ≤
        L1Norm (fun v => (x (some v) - x none) - (y (some v) - y none)) +
          n * LInftyNorm (fun v => (x (some v) - x none) - (y (some v) - y none)) := by
    intro x y hw
    have e : L1Norm (fun w => x w - y w) = |x none - y none| +
        ∑ v, |((x (some v) - x none) - (y (some v) - y none)) + (x none - y none)| := by
      unfold L1Norm; rw [Fintype.sum_option]; congr 1
      refine Finset.sum_congr rfl (fun v _ => ?_); congr 1; ring
    rw [e]
    apply lifted_pair
    obtain ⟨w, hw⟩ := hw
    cases w with
    | none => left; rw [hw]; ring
    | some v0 => right; exact ⟨v0, by rw [hw]; ring⟩
  rcases (Set.eq_empty_or_nonempty (DomZ g)) with hE | ⟨p0, hp0⟩
  · -- empty domain: every set is empty
    have h1 : S1 = ∅ := by
      ext k; simp only [hS1, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨p, q, hp, -⟩; rw [hE] at hp; exact hp
    have h2 : SI = ∅ := by
      ext k; simp only [hSI, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨p, q, hp, -⟩; rw [hE] at hp; exact hp
    have h3 : SH = ∅ := by
      ext k; simp only [hSH, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨p, q, hp, -⟩; have := proj p hp; rw [hE] at this; exact this
    rw [eK1, eKI, eKH, h1, h2, h3, Int.csSup_empty]
    simp
  · have hS1ne : S1.Nonempty := ⟨_, p0, p0, hp0, hp0, rfl⟩
    have hSIne : SI.Nonempty := ⟨_, p0, p0, hp0, hp0, rfl⟩
    have hSHne : SH.Nonempty := ⟨_, _, _, lift p0 hp0, lift p0 hp0, ⟨none, rfl⟩, rfl⟩
    by_cases hb : BddAbove S1
    · have hbI : BddAbove SI := by
        obtain ⟨M, hM⟩ := hb
        refine ⟨M, ?_⟩
        rintro k ⟨p, q, hp, hq, rfl⟩
        exact (linf_le_l1 _).trans (hM ⟨p, q, hp, hq, rfl⟩)
      have hKI_le : sSup SI ≤ sSup S1 := by
        refine csSup_le hSIne ?_
        rintro k ⟨p, q, hp, hq, rfl⟩
        exact (linf_le_l1 _).trans (le_csSup hb ⟨p, q, hp, hq, rfl⟩)
      have hK1_le : sSup S1 ≤ n * sSup SI := by
        refine csSup_le hS1ne ?_
        rintro k ⟨p, q, hp, hq, rfl⟩
        exact (l1_le_linf _).trans (mul_le_mul_of_nonneg_left
          (le_csSup hbI ⟨p, q, hp, hq, rfl⟩) hn)
      have hKI_nn : 0 ≤ sSup SI := by
        have : LInftyNorm (fun v => p0 v - p0 v) = 0 := by
          unfold LInftyNorm; simp
        rw [← this]; exact le_csSup hbI ⟨p0, p0, hp0, hp0, rfl⟩
      have hH : sSup SH ≤ sSup S1 + n * sSup SI := by
        refine csSup_le hSHne ?_
        rintro k ⟨x, y, hx, hy, hw, rfl⟩
        refine (pair x y hw).trans (add_le_add (le_csSup hb ⟨_, _, proj x hx, proj y hy, rfl⟩)
          (mul_le_mul_of_nonneg_left (le_csSup hbI ⟨_, _, proj x hx, proj y hy, rfl⟩) hn))
      rw [eK1, eKI, eKH]
      refine ⟨by exact_mod_cast hH, le_min ?_ ?_⟩
      · have : sSup S1 + n * sSup SI ≤ (n + 1) * sSup S1 := by nlinarith
        exact_mod_cast this
      · have : sSup S1 + n * sSup SI ≤ 2 * n * sSup SI := by nlinarith
        exact_mod_cast this
    · have hbI : ¬ BddAbove SI := by
        rintro ⟨M, hM⟩
        refine hb ⟨n * M, ?_⟩
        rintro k ⟨p, q, hp, hq, rfl⟩
        exact (l1_le_linf _).trans (mul_le_mul_of_nonneg_left (hM ⟨p, q, hp, hq, rfl⟩) hn)
      have hbH : ¬ BddAbove SH := by
        rintro ⟨M, hM⟩
        refine hb ⟨M, ?_⟩
        rintro k ⟨p, q, hp, hq, rfl⟩
        rw [← lift_norm]
        exact hM ⟨_, _, lift p hp, lift q hq, ⟨none, rfl⟩, rfl⟩
      rw [eK1, eKI, eKH, Int.csSup_of_not_bddAbove hb, Int.csSup_of_not_bddAbove hbI,
        Int.csSup_of_not_bddAbove hbH]
      simp

#print axioms solution
