-- Prove2me | solution 1 for BookProof.SchrodingerCutoff.schrodingerOp_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T00:10:32.103042+00:00
-- url     : https://prove2.me/submissions/0ce64342-537b-46ab-9a08-18ff47aca30d

-- Generated from ChapterSchrodingerCutoffEsa.lean — solution of BookProof.SchrodingerCutoff.schrodingerOp_symmetric
import Mathlib
import Definitions.Def_ChapterSchrodingerCutoffEsa
import Theorems.Thm_BookProof_SchrodingerCutoff_integral_conj_secondDeriv_comm
import Theorems.Thm_BookProof_SchrodingerCutoff_schrodingerOp_apply
open BookProof.SchrodingerCutoff




open MeasureTheory Filter Complex

set_option maxHeartbeats 1000000 in

theorem solution (V : ℝ → ℝ) (hV : Continuous V)
    (f g f' f'' g' g'' : ℝ → ℂ)
    (hf1 : ∀ x, HasDerivAt f (f' x) x) (hf2 : ∀ x, HasDerivAt f' (f'' x) x)
    (hg1 : ∀ x, HasDerivAt g (g' x) x) (hg2 : ∀ x, HasDerivAt g' (g'' x) x)
    (hf''c : Continuous f'') (hg''c : Continuous g'')
    (hfs : HasCompactSupport f) (hgs : HasCompactSupport g) :
    (∫ x, (starRingEnd ℂ) (schrodingerOp V f x) * g x)
      = ∫ x, (starRingEnd ℂ) (f x) * schrodingerOp V g x := by
  have hfd : Differentiable ℝ f := fun x => (hf1 x).differentiableAt
  have hgd : Differentiable ℝ g := fun x => (hg1 x).differentiableAt
  have hfc : Continuous f := hfd.continuous
  have hgc : Continuous g := hgd.continuous
  have hconjf : HasCompactSupport fun x => (starRingEnd ℂ) (f x) :=
    hfs.comp_left (g := starRingEnd ℂ) (by simp)
  have key := integral_conj_secondDeriv_comm f g f' f'' g' g'' hf1 hf2 hg1 hg2 hf''c hg''c hfs hgs
  have hcs : HasCompactSupport fun x => (starRingEnd ℂ) (f x) * g x := hgs.mul_left
  have iA0 : Integrable fun x => (starRingEnd ℂ) (f'' x) * g x :=
    (by fun_prop : Continuous fun x => (starRingEnd ℂ) (f'' x) * g x)
      |>.integrable_of_hasCompactSupport hgs.mul_left
  have iC0 : Integrable fun x => (starRingEnd ℂ) (f x) * g'' x :=
    (by fun_prop : Continuous fun x => (starRingEnd ℂ) (f x) * g'' x)
      |>.integrable_of_hasCompactSupport hconjf.mul_right
  have iB : Integrable fun x => (V x : ℂ) * ((starRingEnd ℂ) (f x) * g x) :=
    (by fun_prop : Continuous fun x => (V x : ℂ) * ((starRingEnd ℂ) (f x) * g x))
      |>.integrable_of_hasCompactSupport hcs.mul_left
  have e1 : ∀ x, (starRingEnd ℂ) (schrodingerOp V f x) * g x
      = -((starRingEnd ℂ) (f'' x) * g x) + (V x : ℂ) * ((starRingEnd ℂ) (f x) * g x) := by
    intro x
    rw [schrodingerOp_apply V f f' f'' hf1 hf2 x, map_add, map_neg, map_mul, Complex.conj_ofReal]
    ring
  have e2 : ∀ x, (starRingEnd ℂ) (f x) * schrodingerOp V g x
      = -((starRingEnd ℂ) (f x) * g'' x) + (V x : ℂ) * ((starRingEnd ℂ) (f x) * g x) := by
    intro x
    rw [schrodingerOp_apply V g g' g'' hg1 hg2 x]
    ring
  have iA : Integrable fun x => -((starRingEnd ℂ) (f'' x) * g x) := iA0.neg
  have iC : Integrable fun x => -((starRingEnd ℂ) (f x) * g'' x) := iC0.neg
  rw [integral_congr_ae (Filter.Eventually.of_forall e1),
      integral_congr_ae (Filter.Eventually.of_forall e2),
      integral_add iA iB, integral_add iC iB, integral_neg, integral_neg, key]

/-! ## The exponential potential -/
