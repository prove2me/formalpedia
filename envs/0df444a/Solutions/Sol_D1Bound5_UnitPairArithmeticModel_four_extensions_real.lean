-- Prove2me | solution 1 for D1Bound5.UnitPairArithmeticModel.four_extensions_real
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:41:12.193039+00:00
-- url     : https://prove2.me/submissions/b106d23e-0cb0-4b67-8d2e-c0a95c4ffcd5

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Sqrt
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FullRingUnitPairPell_Definitions
import Definitions.Def_D1Bound5_UnitPairArithmeticModel_Definitions
import Definitions.Def_D1Bound5_UnitPairPellBounds_Definitions
import Definitions.Def_D1Bound5_UnitPairRealReduction_Definitions
import Theorems.Thm_D1Bound5_UnitPairArithmeticModel_imaginary_same_axis_impossible
import Theorems.Thm_D1Bound5_UnitPairArithmeticModel_mixed_impossible
import Theorems.Thm_D1Bound5_UnitPairArithmeticModel_real_imaginary_disjoint
import Theorems.Thm_D1Bound5_UnitPairPellDescription_norm_lower
import Theorems.Thm_D1Bound5_UnitPairPellDescription_two_le_parameter

section
open scoped NumberField
open Module

namespace D1Bound5



theorem UnitPairRealDescription.is_integer {R : Type*} [Ring R]
    (d : ℤ) (z : R) (h : UnitPairRealDescription d z) : ∃ m : ℤ, z = (m : R) := by
  obtain ⟨u,v,hv,hpell,h | h⟩ := h
  · exact ⟨d*v^2+1,h⟩
  · exact ⟨-(d*v^2+1),by simpa only [Int.cast_neg] using h⟩





private theorem three_nonzero_same_sign (a b c : ℤ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    0 < a*b ∨ 0 < a*c ∨ 0 < b*c := by
  rcases lt_or_gt_of_ne ha with ha | ha <;>
    rcases lt_or_gt_of_ne hb with hb | hb <;>
    rcases lt_or_gt_of_ne hc with hc | hc
  all_goals first
    | exact Or.inl (mul_pos ha hb)
    | exact Or.inl (mul_pos_of_neg_of_neg ha hb)
    | exact Or.inr (Or.inl (mul_pos ha hc))
    | exact Or.inr (Or.inl (mul_pos_of_neg_of_neg ha hc))
    | exact Or.inr (Or.inr (mul_pos hb hc))
    | exact Or.inr (Or.inr (mul_pos_of_neg_of_neg hb hc))

/-- Among four mutually compatible extensions of the unit pair, every
extension is real. All axis, parity and discreteness inputs are supplied
by the single arithmetic model and the actual square witnesses. -/
theorem _root_.solution
    {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    (M : UnitPairArithmeticModel R) (f : R →+* ℂ)
    (hdiscrete : ∀ z : R, z ≠ 0 → 1 ≤ ‖f z‖)
    (z : Fin 4 → R) (hz : ∀ i, z i ≠ 0)
    (hroots : ∀ i, (∃ r : R, r^2 = 1-z i) ∧ (∃ r : R, r^2 = 1+z i))
    (hpair : ∀ i j, i ≠ j → ∃ r : R, r^2 = 1+z i*z j) :
    ∀ i, UnitPairRealDescription M.d (z i) := by
  classical
  have hpell (i : Fin 4) : UnitPairPellDescription M.d M.w (z i) := by
    obtain ⟨r,hr⟩ := (hroots i).2
    obtain ⟨s,hs⟩ := (hroots i).1
    exact M.pell (z i) r s (hz i)
      (by simpa only [pow_two,add_comm] using hr) (by simpa only [pow_two] using hs)
  have hd : 2 ≤ M.d := (hpell 0).two_le_parameter M.d M.w (z 0) M.positive
  have hnorm (i : Fin 4) : 3 ≤ ‖f (z i)‖ := by
    have hw : f M.w*f M.w = -(M.d : ℂ) := by
      simpa only [map_mul,map_neg,map_intCast] using congrArg f M.square
    have hh := UnitPairPellDescription.norm_lower M.d (f M.w) (f (z i)) M.positive hw
      (UnitPairPellDescription.map f M.d M.w (z i) (hpell i))
    have hdR : (2 : ℝ) ≤ (M.d : ℝ) := by exact_mod_cast hd
    linarith only [hh,hdR]
  have hex : ∃ i, UnitPairRealDescription M.d (z i) := by
    by_contra hnone
    have himag (i : Fin 4) : ∃ n : ℤ, n ≠ 0 ∧ z i = (n : R)*M.w := by
      rcases hpell i with hreal | hi
      · exact (hnone ⟨i,hreal⟩).elim
      · obtain ⟨u,v,hv,hPell,hi⟩ := hi
        refine ⟨2*u*v,?_,hi⟩
        intro hh
        apply hz i
        simpa only [hh,Int.cast_zero,zero_mul] using hi
    obtain ⟨a,ha,hea⟩ := himag 0
    obtain ⟨b,hb,heb⟩ := himag 1
    obtain ⟨c,hc,hec⟩ := himag 2
    have hno (i j : Fin 4) (hij : i ≠ j) (m n : ℤ)
        (hi : z i = (m : R)*M.w) (hj : z j = (n : R)*M.w)
        (hmn : 0 < m*n) : False := by
      obtain ⟨r,hr⟩ := hpair i j hij
      apply M.imaginary_same_axis_impossible hd m n hmn
      exact ⟨r,by simpa only [pow_two,hi,hj,add_comm] using hr⟩
    rcases three_nonzero_same_sign a b c ha hb hc with hab | hac | hbc
    · exact hno 0 1 (by decide) a b hea heb hab
    · exact hno 0 2 (by decide) a c hea hec hac
    · exact hno 1 2 (by decide) b c heb hec hbc
  obtain ⟨i,hi⟩ := hex
  intro j
  rcases hpell j with hreal | himag
  · exact hreal
  · obtain ⟨u,v,hv,hPell,hj⟩ := himag
    have hint := hi.is_integer M.d (z i)
    have hji : ∃ n : ℤ, z j = (n : R)*M.w := ⟨2*u*v,hj⟩
    by_cases hij : i = j
    · subst j
      exact (M.real_imaginary_disjoint (z i) (hz i) hint hji).elim
    · exact (M.mixed_impossible f hdiscrete (z i) (z j) (hnorm i) (hnorm j)
        hint hji (hroots i).1 (hroots i).2 (hroots j).1 (hroots j).2
        (hpair i j hij)).elim







end D1Bound5
end
