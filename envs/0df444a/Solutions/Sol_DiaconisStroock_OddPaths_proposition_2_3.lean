-- Prove2me | solution 3 for DiaconisStroock.OddPaths.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T09:48:21.602285+00:00
-- url     : https://prove2.me/submissions/046ea3c0-7df9-4485-9abb-d546cbf4322d

import Mathlib
import Definitions.Def_DiaconisStroock_OddPaths_Iota
import Definitions.Def_mm_spectral
import Definitions.Def_DiaconisStroock_Poincare_Paths
import Definitions.Def_mm_basic
import Theorems.Thm_DiaconisStroock_OddPaths_eq_1_8
import Theorems.Thm_DiaconisStroock_OddPaths_inner_self_le_iota_mul

-- carved verbatim out of submission f2196187-2ec7-4b13-a48c-4afd8c626dc9, lines 304-343

section
set_option autoImplicit false
open scoped BigOperators
open MarkovMixing
open DiaconisStroock.Poincare
open MarkovMixing DiaconisStroock.Poincare DiaconisStroock.OddPaths
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma pow_entry_nonneg {P : Matrix V V ℝ} (hP : IsStochastic P) :
    ∀ (t : ℕ) (x y : V), 0 ≤ (P ^ t) x y := by
  intro t
  induction t with
  | zero =>
    intro x y
    by_cases h : x = y <;> simp [Matrix.one_apply, h]
  | succ t ih =>
    intro x y
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun z _ => mul_nonneg (ih x z) (hP.1 z y)

lemma vecMul_pow {P : Matrix V V ℝ} {π : V → ℝ} (hπ : IsStationary P π) :
    ∀ t : ℕ, Matrix.vecMul π (P ^ t) = π := by
  intro t
  induction t with
  | zero => simp
  | succ t ih => rw [pow_succ, ← Matrix.vecMul_vecMul, ih, hπ.2]

lemma pi_pos {P : Matrix V V ℝ} (hirr : MarkovMixing.Irreducible P) {π : V → ℝ}
    (hπ : IsStationary P π) (hP : IsStochastic P) : ∀ x, 0 < π x := by
  obtain ⟨y, hy⟩ : ∃ y, 0 < π y := by
    by_contra hcon
    push_neg at hcon
    have h1 : ∑ x, π x ≤ 0 := Finset.sum_nonpos fun i _ => hcon i
    have := hπ.1.2
    linarith
  intro x
  obtain ⟨t, ht⟩ := hirr y x
  have hv : ∑ z, π z * (P ^ t) z x = π x := congrFun (vecMul_pow hπ t) x
  have h2 : π y * (P ^ t) y x ≤ ∑ z, π z * (P ^ t) z x := by
    refine Finset.single_le_sum (f := fun z => π z * (P ^ t) z x) ?_ (Finset.mem_univ y)
    exact fun z _ => mul_nonneg (hπ.1.1 z) (pow_entry_nonneg hP t z x)
  have := mul_pos hy ht
  linarith

end

section
set_option autoImplicit false
open scoped BigOperators
open MarkovMixing
open DiaconisStroock.Poincare
open MarkovMixing DiaconisStroock.Poincare DiaconisStroock.OddPaths
open MarkovMixing DiaconisStroock.OddPaths

theorem DiaconisStroock.OddPaths.eigenvalue_ge {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P)
    (π : V → ℝ) (hπ : IsStationary P π) (hrev : DetailedBalance P π)
    (S : V → List V) (hS : IsOddPathSystem P π S) :
    ∀ β : ℝ, IsEigenvalue P β → -1 + 2 / iota P π S ≤ β := by
  intro β hβ
  obtain ⟨f, hfne, hf⟩ := hβ
  have hpos := pi_pos hirr hπ hP
  have hx : ∃ x, f x ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hfne (funext hn)
  obtain ⟨x, hfx⟩ := hx
  have hn : 0 < innerPi π f f := by
    unfold innerPi
    apply Finset.sum_pos'
    · intro y _; exact mul_nonneg (mul_self_nonneg _) (hπ.1.1 y)
    · exact ⟨x, Finset.mem_univ x, mul_pos (mul_self_pos.mpr hfx) (hpos x)⟩
  have hc : innerPi π f (P.mulVec f) = β * innerPi π f f := by
    rw [hf]
    change (∑ y, f y*(β*f y)*π y) = β*(∑ y, f y*f y*π y)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring
  have he : 0 ≤ innerPi π f f + innerPi π f (P.mulVec f) := by
    rw [← DiaconisStroock.OddPaths.eq_1_8 P hP π hπ f]
    apply mul_nonneg (by norm_num)
    apply Finset.sum_nonneg
    intro y _
    apply Finset.sum_nonneg
    intro z _
    exact mul_nonneg (sq_nonneg _) (mul_nonneg (hπ.1.1 y) (hP.1 y z))
  have hb := DiaconisStroock.OddPaths.inner_self_le_iota_mul P hP hirr π hπ hrev S hS f
  have hi : 0 < iota P π S := by
    by_contra hnot
    have hh : iota P π S / 2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hnot) (by norm_num)
    have hp := mul_nonpos_of_nonpos_of_nonneg hh he
    linarith
  rw [hc] at hb
  have hs : 1 ≤ iota P π S / 2 * (1+β) := by
    apply (mul_le_mul_iff_right₀ hn).mp
    rw [mul_one]
    nlinarith [hb]
  have hd : 2 / iota P π S ≤ 1+β := (div_le_iff₀ hi).mpr (by nlinarith [hs])
  linarith

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P)
    (haper : Aperiodic P) (π : V → ℝ) (hπ : IsStationary P π) (hrev : DetailedBalance P π)
    (S : V → List V) (hS : IsOddPathSystem P π S) :
    -1 + 2 / iota P π S ≤ betaMin P := by
  have hx : ∃ x, 0 < π x := by
    by_contra hn
    push_neg at hn
    have hs := Finset.sum_nonpos (s := Finset.univ) (fun x _ => hn x)
    have hm := hπ.1.2
    linarith
  obtain ⟨x, hx⟩ := hx
  have h1 : IsEigenvalue P 1 := by
    refine ⟨fun _ => 1, ?_, ?_⟩
    · intro hz
      have hc := congrFun hz x
      norm_num at hc
    · ext y
      change (∑ z, P y z*1) = 1*1
      simpa using hP.2 y
  apply le_csInf (show Set.Nonempty {β : ℝ | IsEigenvalue P β} from ⟨1, h1⟩)
  intro β hβ
  exact DiaconisStroock.OddPaths.eigenvalue_ge P hP hirr π hπ hrev S hS β hβ

end
