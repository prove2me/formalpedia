-- Prove2me | solution 1 for ConvexOptAlg.Newton.error_representation
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T17:36:54.648631+00:00
-- url     : https://prove2.me/submissions/e82f85aa-3e1a-4fa0-b5f4-ee5c9ec1beb0

import Mathlib
import Definitions.Def_ConvexOptAlg_Newton_Defs

open InnerProductSpace in
theorem ConvexOptAlg.Newton.errRep_aux {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (hfgH : ConvexOptAlg.Newton.IsC2GradHess f g H) : Continuous H := by
  obtain ⟨hf, h2, h3⟩ := hfgH
  set b := EuclideanSpace.basisFun (Fin n) ℝ
  have hfd : ∀ x, fderiv ℝ f x = toDual ℝ _ (g x) := fun x =>
    (hasGradientAt_iff_hasFDerivAt.1 (h2 x)).fderiv
  have hg : g = fun x => ∑ i, (fderiv ℝ f x (b i)) • b i := by
    funext x
    conv_lhs => rw [← b.sum_repr' (g x)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hfd x, toDual_apply_apply, real_inner_comm]
  have hgC : ContDiff ℝ 1 g := by
    rw [hg]
    refine ContDiff.sum fun i _ => ?_
    exact ((hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).smul contDiff_const
  have hH : H = fderiv ℝ g := funext fun x => (h3 x).fderiv.symm
  rw [hH]
  exact hgC.continuous_fderiv (by norm_num)

open InnerProductSpace in
theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (hfgH : ConvexOptAlg.Newton.IsC2GradHess f g H) (xstar : EuclideanSpace ℝ (Fin n)) (hmin : IsLocalMin f xstar)
    (y yplus : EuclideanSpace ℝ (Fin n)) (hstep : H y (y - yplus) = g y) :
    g y = (∫ s in (0 : ℝ)..1, H (xstar + s • (y - xstar)) (y - xstar)) ∧
    H y (yplus - xstar) =
      ∫ s in (0 : ℝ)..1, (H y - H (xstar + s • (y - xstar))) (y - xstar) := by
  have hHc := ConvexOptAlg.Newton.errRep_aux f g H hfgH
  obtain ⟨hf, h2, h3⟩ := hfgH
  have hg0 : g xstar = 0 := by
    have := hmin.hasFDerivAt_eq_zero (hasGradientAt_iff_hasFDerivAt.1 (h2 xstar))
    exact (toDual ℝ _).map_eq_zero_iff.1 this
  set h := y - xstar with hh
  have hcont : Continuous fun s : ℝ => H (xstar + s • h) h :=
    (hHc.comp (continuous_const.add (continuous_id.smul continuous_const))).clm_apply
      continuous_const
  have hderiv : ∀ s : ℝ, HasDerivAt (fun s : ℝ => g (xstar + s • h)) (H (xstar + s • h) h) s := by
    intro s
    have hp : HasDerivAt (fun s : ℝ => xstar + s • h) h s := by
      simpa using ((hasDerivAt_id s).smul_const h).const_add xstar
    exact (h3 _).comp_hasDerivAt s hp
  have hint : IntervalIntegrable (fun s : ℝ => H (xstar + s • h) h) MeasureTheory.volume 0 1 :=
    hcont.intervalIntegrable 0 1
  have hFTC : (∫ s in (0 : ℝ)..1, H (xstar + s • h) h) = g y := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hderiv s) hint]
    simp [hh, hg0]
  refine ⟨hFTC.symm, ?_⟩
  have e1 : (fun s : ℝ => (H y - H (xstar + s • h)) h) = fun s => H y h - H (xstar + s • h) h := by
    funext s; rfl
  rw [e1, intervalIntegral.integral_sub intervalIntegrable_const hint, hFTC,
    intervalIntegral.integral_const, ← hstep, sub_zero, one_smul, ← map_sub, hh]
  congr 1
  abel
