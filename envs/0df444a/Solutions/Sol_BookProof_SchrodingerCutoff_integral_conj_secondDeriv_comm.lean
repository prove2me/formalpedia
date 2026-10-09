-- Prove2me | solution 1 for BookProof.SchrodingerCutoff.integral_conj_secondDeriv_comm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T14:52:19.380663+00:00
-- url     : https://prove2.me/submissions/8b4f4941-c450-4716-b128-27288da4e736

-- Generated from ChapterSchrodingerCutoffEsa.lean — solution of BookProof.SchrodingerCutoff.integral_conj_secondDeriv_comm
import Mathlib
import Definitions.Def_ChapterSchrodingerCutoffEsa
import Theorems.Thm_BookProof_SchrodingerCutoff_integral_deriv_eq_zero_of_hasCompactSupport
open BookProof.SchrodingerCutoff




open MeasureTheory Filter Complex

set_option maxHeartbeats 1000000 in
theorem solution
    (f g f' f'' g' g'' : ℝ → ℂ)
    (hf1 : ∀ x, HasDerivAt f (f' x) x) (hf2 : ∀ x, HasDerivAt f' (f'' x) x)
    (hg1 : ∀ x, HasDerivAt g (g' x) x) (hg2 : ∀ x, HasDerivAt g' (g'' x) x)
    (hf''c : Continuous f'') (hg''c : Continuous g'')
    (hfs : HasCompactSupport f) (hgs : HasCompactSupport g) :
    (∫ x, (starRingEnd ℂ) (f'' x) * g x) = ∫ x, (starRingEnd ℂ) (f x) * g'' x := by

  have hfd : Differentiable ℝ f := fun x => (hf1 x).differentiableAt
  have hf'd : Differentiable ℝ f' := fun x => (hf2 x).differentiableAt
  have hgd : Differentiable ℝ g := fun x => (hg1 x).differentiableAt
  have hg'd : Differentiable ℝ g' := fun x => (hg2 x).differentiableAt
  have hfc : Continuous f := hfd.continuous
  have hf'c : Continuous f' := hf'd.continuous
  have hgc : Continuous g := hgd.continuous
  have hg'c : Continuous g' := hg'd.continuous
  have hf's : HasCompactSupport f' := by
    rw [show f' = deriv f from funext fun x => ((hf1 x).deriv).symm]; exact hfs.deriv
  have hg's : HasCompactSupport g' := by
    rw [show g' = deriv g from funext fun x => ((hg1 x).deriv).symm]; exact hgs.deriv
  have hconjf : HasCompactSupport fun x => (starRingEnd ℂ) (f x) :=
    hfs.comp_left (g := starRingEnd ℂ) (by simp)
  -- first integration by parts, with `k = conj f' · g`
  have hk : ∀ x, HasDerivAt (fun y => (starRingEnd ℂ) (f' y) * g y)
      ((starRingEnd ℂ) (f'' x) * g x + (starRingEnd ℂ) (f' x) * g' x) x :=
    fun x => ((hf2 x).star).mul (hg1 x)
  have hk0 := integral_deriv_eq_zero_of_hasCompactSupport hk (by fun_prop) hgs.mul_left
  -- second integration by parts, with `m = conj f · g'`
  have hm : ∀ x, HasDerivAt (fun y => (starRingEnd ℂ) (f y) * g' y)
      ((starRingEnd ℂ) (f' x) * g' x + (starRingEnd ℂ) (f x) * g'' x) x :=
    fun x => ((hf1 x).star).mul (hg2 x)
  have hm0 := integral_deriv_eq_zero_of_hasCompactSupport hm (by fun_prop) hconjf.mul_right
  -- integrability of the three pieces
  have i1 : Integrable fun x => (starRingEnd ℂ) (f'' x) * g x :=
    (by fun_prop : Continuous fun x => (starRingEnd ℂ) (f'' x) * g x)
      |>.integrable_of_hasCompactSupport hgs.mul_left
  have i2 : Integrable fun x => (starRingEnd ℂ) (f' x) * g' x :=
    (by fun_prop : Continuous fun x => (starRingEnd ℂ) (f' x) * g' x)
      |>.integrable_of_hasCompactSupport hg's.mul_left
  have i3 : Integrable fun x => (starRingEnd ℂ) (f x) * g'' x :=
    (by fun_prop : Continuous fun x => (starRingEnd ℂ) (f x) * g'' x)
      |>.integrable_of_hasCompactSupport hconjf.mul_right
  rw [integral_add i1 i2] at hk0
  rw [integral_add i2 i3] at hm0
  linear_combination (norm := module) hk0 - hm0
