-- Prove2me | solution 1 for EinsteinGrossmann1913.total_conservation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T15:15:04.993988+00:00
-- url     : https://prove2.me/submissions/6b8576e8-2c58-449b-b672-d1c7c264742c

import Theorems.Thm_EinsteinGrossmann1913_gravitational_energy_momentum_identity

open EinsteinGrossmann1913
open scoped Matrix

private lemma smooth_det (g : Field2) (hg : IsMetricField g) :
    ContDiff ℝ 2 (fun x => (g x).det) := by
  classical
  simp only [Matrix.det_apply']
  exact ContDiff.sum fun σ _ => contDiff_const.mul
    (contDiff_prod fun i _ => hg.contDiff (σ i) i)

private lemma smooth_gamma (g : Field2) (hg : IsMetricField g) (a b : Fin 4) :
    ContDiff ℝ 2 (fun x => gamma g x a b) := by
  classical
  have hadj : ContDiff ℝ 2 (fun x => (g x).adjugate a b) := by
    simp only [Matrix.adjugate_apply]
    simp only [Matrix.det_apply']
    apply ContDiff.sum
    intro σ _
    apply contDiff_const.mul
    apply contDiff_prod
    intro i _
    by_cases h : σ i = b
    · simp only [Matrix.updateRow_apply, h, if_true]
      exact contDiff_const
    · simpa only [Matrix.updateRow_apply, h, if_false] using hg.contDiff (σ i) i
  have hdet := (smooth_det g hg).inv (fun x => ne_of_lt (hg.det_neg x))
  have he : (fun x => gamma g x a b) =
      (fun x => (g x).det⁻¹ * (g x).adjugate a b) := by
    funext x
    simp [gamma, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply]
  rw [he]
  exact hdet.mul hadj

private lemma smooth_density (g : Field2) (hg : IsMetricField g) :
    ContDiff ℝ 2 (sqrtNegDet g) := by
  exact (smooth_det g hg).neg.sqrt (fun x => neg_ne_zero.mpr (ne_of_lt (hg.det_neg x)))

private lemma smooth_pd (f : Coord → ℝ) (hf : ContDiff ℝ 2 f) (a : Fin 4) :
    ContDiff ℝ 1 (fun x => pd a f x) := by
  exact (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).clm_apply contDiff_const

private lemma pd_add (a : Fin 4) (f h : Coord → ℝ) (x : Coord)
    (hf : DifferentiableAt ℝ f x) (hh : DifferentiableAt ℝ h x) :
    pd a (fun y => f y + h y) x = pd a f x + pd a h x := by
  unfold pd
  rw [fderiv_fun_add hf hh]
  rfl

private lemma pd_const_mul (a : Fin 4) (c : ℝ) (f : Coord → ℝ) (x : Coord)
    (hf : DifferentiableAt ℝ f x) :
    pd a (fun y => c * f y) x = c * pd a f x := by
  unfold pd
  rw [fderiv_const_mul hf]
  simp only [smul_apply, smul_eq_mul]

private lemma smooth_stress (κ : ℝ) (g : Field2) (hg : IsMetricField g)
    (i j : Fin 4) : ContDiff ℝ 1 (fun x => gravStressEnergy κ g x i j) := by
  classical
  have hg1 (a b : Fin 4) := (hg.contDiff a b).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hh1 (a b : Fin 4) := (smooth_gamma g hg a b).of_le
    (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hdp (a b c : Fin 4) := smooth_pd _ (hg.contDiff b c) a
  have hdq (a b c : Fin 4) := smooth_pd _ (smooth_gamma g hg b c) a
  unfold gravStressEnergy
  simp only [Matrix.of_apply]
  apply contDiff_const.mul
  apply ContDiff.sum
  intro α _
  apply ContDiff.sum
  intro β _
  apply ContDiff.sum
  intro τ _
  apply ContDiff.sum
  intro ρ _
  exact ((((hh1 α i).mul (hh1 β j)).mul (hdp α τ ρ)).mul (hdq β τ ρ)).sub
    ((((contDiff_const.mul (hh1 i j)).mul (hh1 α β)).mul (hdp α τ ρ)).mul (hdq β τ ρ))

theorem solution (κ : ℝ) (hκ : κ ≠ 0) (g Θ : Field2) (hg : IsMetricField g)
    (hΘ : ∀ μ ν : Fin 4, ContDiff ℝ 1 (fun x => Θ x μ ν))
    (h10 : MatterConservation g Θ) (h18 : EntwurfFieldEquations κ g Θ)
    (σ : Fin 4) (x : Coord) :
    ∑ μ : Fin 4, ∑ ν : Fin 4,
      pd ν (fun y => sqrtNegDet g y * g y σ μ
        * (Θ y μ ν + gravStressEnergy κ g y μ ν)) x = 0 := by
  have hsd := (smooth_density g hg).differentiable (by norm_num) x
  have hwd (μ ν : Fin 4) : DifferentiableAt ℝ
      (fun y => sqrtNegDet g y * g y σ μ) x :=
    hsd.mul ((hg.contDiff σ μ).differentiable (by norm_num) x)
  have htd (μ ν : Fin 4) := (hΘ μ ν).differentiable (by norm_num) x
  have hgd (μ ν : Fin 4) := (smooth_stress κ g hg μ ν).differentiable (by norm_num) x
  have hsplit (μ ν : Fin 4) :
      pd ν (fun y => sqrtNegDet g y * g y σ μ *
        (Θ y μ ν + gravStressEnergy κ g y μ ν)) x =
      pd ν (fun y => sqrtNegDet g y * g y σ μ * Θ y μ ν) x +
      pd ν (fun y => sqrtNegDet g y * g y σ μ * gravStressEnergy κ g y μ ν) x := by
    simp only [mul_add]
    exact pd_add _ _ _ _ ((hwd μ ν).mul (htd μ ν)) ((hwd μ ν).mul (hgd μ ν))
  have hscale (μ ν : Fin 4) :
      pd ν (fun y => sqrtNegDet g y * g y σ μ *
        (κ * gravStressEnergy κ g y μ ν)) x =
      κ * pd ν (fun y => sqrtNegDet g y * g y σ μ * gravStressEnergy κ g y μ ν) x := by
    have he : (fun y => sqrtNegDet g y * g y σ μ *
        (κ * gravStressEnergy κ g y μ ν)) =
        (fun y => κ * (sqrtNegDet g y * g y σ μ * gravStressEnergy κ g y μ ν)) := by
      funext y
      ring
    rw [he]
    exact pd_const_mul _ _ _ _ ((hwd μ ν).mul (hgd μ ν))
  have hgrav := gravitational_energy_momentum_identity κ hκ g hg σ x
  simp_rw [hscale] at hgrav
  simp only [← Finset.mul_sum] at hgrav
  have hmatter := h10 σ x
  unfold matterConservationLHS at hmatter
  have hfield (μ ν : Fin 4) : -entwurfDelta g x μ ν + κ * gravStressEnergy κ g x μ ν =
      -(κ * Θ x μ ν) := by
    have h := h18 x μ ν
    linarith
  simp_rw [hfield] at hgrav
  have hw : (∑ μ, ∑ ν, sqrtNegDet g x * pd σ (fun y => g y μ ν) x *
      -(κ * Θ x μ ν)) =
      -κ * ∑ μ, ∑ ν, sqrtNegDet g x * pd σ (fun y => g y μ ν) x * Θ x μ ν := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro μ _
    apply Finset.sum_congr rfl
    intro ν _
    ring
  rw [hw] at hgrav
  simp_rw [hsplit]
  simp only [Finset.sum_add_distrib]
  have hm := congrArg (fun z : ℝ => κ * z) hmatter
  apply (mul_eq_zero.mp (show κ * _ = 0 by nlinarith only [hm, hgrav])).resolve_left hκ
