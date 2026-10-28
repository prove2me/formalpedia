-- Prove2me | solution 1 for BookProof.ScalaronFiberFL.integral_x_wronskian
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T06:45:02.096671+00:00
-- url     : https://prove2.me/submissions/18c936a5-4c11-485f-8883-b4126e6075a2

import Definitions.Def_ChapterStrichartzWave
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterScalaronWallEsa
import Definitions.Def_ChapterWallEsaSemibounded
import Definitions.Def_ChapterWallEsaBddBelow
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterSchrodingerCutoffEsa
import Definitions.Def_ChapterFriedrichsExtension
import Mathlib
import Definitions.Def_ChapterScalaronFiberFL
import Definitions.Def_ChapterQgOuterFockFlow
-- Generated from ChapterScalaronFiberFL.lean — theorem BookProof.ScalaronFiberFL.integral_x_wronskian
open BookProof.ScalaronFiberFL



open MeasureTheory SchwartzMap
open BookProof.StrichartzWave
open BookProof.FarisLavine BookProof.ScalaronEsa BookProof.ScalaronWallEsa
open BookProof.WallEsaSemibounded BookProof.WallEsaBddBelow
open BookProof.QgOuterFockFL BookProof.QgOuterFockCoreFL
open BookProof.SchrodingerCutoff BookProof.FriedrichsExtension

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
theorem solution (f g : ℝ → ℂ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hfs : HasCompactSupport f) (hgs : HasCompactSupport g) :
    (∫ x : ℝ, (x : ℂ) * ((starRingEnd ℂ) (f x) * deriv (deriv g) x
        - (starRingEnd ℂ) (deriv (deriv f) x) * g x))
      = -2 * ∫ x : ℝ, (starRingEnd ℂ) (f x) * deriv g x := by
  have hf' : ContDiff ℝ (⊤ : ℕ∞) f := hf
  have hg' : ContDiff ℝ (⊤ : ℕ∞) g := hg
  have hf1 : ContDiff ℝ (⊤ : ℕ∞) (deriv f) := hf'.iterate_deriv 1
  have hg1 : ContDiff ℝ (⊤ : ℕ∞) (deriv g) := hg'.iterate_deriv 1
  have hf2 : ContDiff ℝ (⊤ : ℕ∞) (deriv (deriv f)) := hf'.iterate_deriv 2
  have hg2 : ContDiff ℝ (⊤ : ℕ∞) (deriv (deriv g)) := hg'.iterate_deriv 2
  have dF : Differentiable ℝ f := hf'.differentiable (by simp)
  have dG : Differentiable ℝ g := hg'.differentiable (by simp)
  have dF1 : Differentiable ℝ (deriv f) := hf1.differentiable (by simp)
  have dG1 : Differentiable ℝ (deriv g) := hg1.differentiable (by simp)
  set cf : ℝ → ℂ := fun x => (starRingEnd ℂ) (f x)
  set cf1 : ℝ → ℂ := fun x => (starRingEnd ℂ) (deriv f x)
  set cf2 : ℝ → ℂ := fun x => (starRingEnd ℂ) (deriv (deriv f) x)
  have hcf : ∀ x, HasDerivAt cf (cf1 x) x := fun x => (dF x).hasDerivAt.star
  have hcf1 : ∀ x, HasDerivAt cf1 (cf2 x) x := fun x => (dF1 x).hasDerivAt.star
  have ccf : Continuous cf := (Complex.continuous_conj.comp hf'.continuous)
  have ccf1 : Continuous cf1 := (Complex.continuous_conj.comp hf1.continuous)
  have ccf2 : Continuous cf2 := (Complex.continuous_conj.comp hf2.continuous)
  have scf : HasCompactSupport cf := hfs.comp_left (map_zero _)
  have scf1 : HasCompactSupport cf1 := hfs.deriv.comp_left (map_zero _)
  have scf2 : HasCompactSupport cf2 := hfs.deriv.deriv.comp_left (map_zero _)
  have sg1 : HasCompactSupport (deriv g) := hgs.deriv
  have sg2 : HasCompactSupport (deriv (deriv g)) := hgs.deriv.deriv
  -- integrability
  have I1 : Integrable fun x => cf x * deriv g x :=
    (ccf.mul hg1.continuous).integrable_of_hasCompactSupport (scf.mul_right)
  have I2 : Integrable fun x => cf1 x * g x :=
    (ccf1.mul hg'.continuous).integrable_of_hasCompactSupport (scf1.mul_right)
  have I3 : Integrable fun x : ℝ => (x : ℂ) * (cf x * deriv (deriv g) x - cf2 x * g x) :=
    ((Complex.continuous_ofReal.mul ((ccf.mul hg2.continuous).sub (ccf2.mul hg'.continuous)))).integrable_of_hasCompactSupport
      ((scf.mul_right.sub scf2.mul_right).mul_left)
  -- first identity: ∫ d/dx [x (cf g' - cf' g)] = 0
  have hF : ∀ x : ℝ, HasDerivAt (fun x : ℝ => (x : ℂ) * (cf x * deriv g x - cf1 x * g x))
      ((cf x * deriv g x - cf1 x * g x) + (x : ℂ) * (cf x * deriv (deriv g) x - cf2 x * g x)) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 x := (hasDerivAt_id x).ofReal_comp
    have h2 := ((hcf x).mul (dG1 x).hasDerivAt).sub ((hcf1 x).mul (dG x).hasDerivAt)
    exact (h1.mul h2).congr_deriv (by simp only [Pi.sub_apply, Pi.mul_apply]; ring)
  have hFint : Integrable (fun x : ℝ => (x : ℂ) * (cf x * deriv g x - cf1 x * g x)) :=
    ((Complex.continuous_ofReal.mul ((ccf.mul hg1.continuous).sub (ccf1.mul hg'.continuous)))).integrable_of_hasCompactSupport
      ((scf.mul_right.sub scf1.mul_right).mul_left)
  have E1 := integral_eq_zero_of_hasDerivAt_of_integrable hF ((I1.sub I2).add I3) hFint
  rw [integral_add (f := fun x => cf x * deriv g x - cf1 x * g x) (I1.sub I2) I3, integral_sub I1 I2] at E1
  -- second identity: ∫ d/dx [cf g] = 0
  have hG : ∀ x : ℝ, HasDerivAt (fun x => cf x * g x) (cf1 x * g x + cf x * deriv g x) x :=
    fun x => (hcf x).mul (dG x).hasDerivAt
  have hGint : Integrable (fun x => cf x * g x) :=
    (ccf.mul hg'.continuous).integrable_of_hasCompactSupport scf.mul_right
  have E2 := integral_eq_zero_of_hasDerivAt_of_integrable hG (I2.add I1) hGint
  rw [integral_add (f := fun x => cf1 x * g x) I2 I1] at E2
  change ∫ x : ℝ, (x : ℂ) * (cf x * deriv (deriv g) x - cf2 x * g x) = -2 * ∫ x, cf x * deriv g x
  linear_combination E1 + E2
