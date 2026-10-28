-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.Suspension.convexOn_potential_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:44:20.958242+00:00
-- url     : https://prove2.me/submissions/b7fdf596-79a8-41ed-b96d-9a104b755e15

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Basic
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_convexOn_of_hessian_ge_readable

noncomputable section
open scoped ContDiff
open FunctionalInequalities.Analysis.BakryEmery
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
private theorem FunctionalInequalities.KLS.LogConcave.Suspension.convexOn_perturbation {V f : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f) {a M c : ℝ}
    (hVlower : ∀ x v, a * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ V x v v)
    (hfbound : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M)
    (hc : |c| * M ≤ a) :
    ConvexOn ℝ Set.univ (fun x => V x + c * f x) := by
  apply convexOn_of_hessian_ge_readable (hV.add (hf.const_smul c)) (ρ := 0) le_rfl
  intro x v
  have hF : |bilinearIteratedFDerivTwo ℝ f x v v| ≤ M * ‖v‖ ^ 2 := by
    change |(fderiv ℝ (fderiv ℝ f) x) v v| ≤ _
    calc
      _ = ‖(fderiv ℝ (fderiv ℝ f) x) v v‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ (fderiv ℝ f) x‖ * ‖v‖ * ‖v‖ :=
        (fderiv ℝ (fderiv ℝ f) x).le_opNorm₂ v v
      _ ≤ M * ‖v‖ * ‖v‖ := by gcongr; exact hfbound x
      _ = M * ‖v‖ ^ 2 := by ring
  have hsum : bilinearIteratedFDerivTwo ℝ (fun y => V y + c * f y) x v v =
      bilinearIteratedFDerivTwo ℝ V x v v + c * bilinearIteratedFDerivTwo ℝ f x v v := by
    rw [bilinearIteratedFDerivTwo_eq_iteratedFDeriv,
      bilinearIteratedFDerivTwo_eq_iteratedFDeriv,
      bilinearIteratedFDerivTwo_eq_iteratedFDeriv]
    change iteratedFDeriv ℝ 2 (V + c • f) x ![v, v] = _
    have hcf : ContDiff ℝ 2 (c • f) := hf.const_smul c
    rw [iteratedFDeriv_add_apply (g := c • f) hV.contDiffAt hcf.contDiffAt,
      iteratedFDeriv_const_smul_apply hf.contDiffAt]
    simp
  have hprod : |c * bilinearIteratedFDerivTwo ℝ f x v v| ≤ a * ‖v‖ ^ 2 := by
    rw [abs_mul]
    calc
      _ ≤ |c| * (M * ‖v‖ ^ 2) := mul_le_mul_of_nonneg_left hF (abs_nonneg c)
      _ = (|c| * M) * ‖v‖ ^ 2 := by ring
      _ ≤ a * ‖v‖ ^ 2 := mul_le_mul_of_nonneg_right hc (sq_nonneg ‖v‖)
  change 0 * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ (fun y => V y + c * f y) x v v
  rw [hsum, zero_mul]
  have := neg_abs_le (c * bilinearIteratedFDerivTwo ℝ f x v v)
  have := hVlower x v
  linarith
private theorem FunctionalInequalities.KLS.LogConcave.Suspension.convexOn_sum_add_linear {g : E → ℝ} (hg : ConvexOn ℝ Set.univ g)
    (N : ℕ) (q : ℝ) :
    ConvexOn ℝ Set.univ (fun p : ℝ × (Fin N → E) => (∑ i, g (p.2 i)) + q * p.1) := by
  classical
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ u v hu hv huv
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    hg.2 (Set.mem_univ (x.2 i)) (Set.mem_univ (y.2 i)) hu hv huv)
  simp only [smul_eq_mul] at hsum
  change (∑ i, g (u • x.2 i + v • y.2 i)) + q * (u * x.1 + v * y.1) ≤
    u * ((∑ i, g (x.2 i)) + q * x.1) + v * ((∑ i, g (y.2 i)) + q * y.1)
  calc
    _ ≤ (∑ i, (u * g (x.2 i) + v * g (y.2 i))) + q * (u * x.1 + v * y.1) :=
      add_le_add hsum le_rfl
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]; ring
/-- The source's convexity argument (109)–(110), with its Hessian condition and constants.
The auxiliary-coordinate scale is unrestricted, and no probability assumptions are needed. -/
theorem solution {V f : E → ℝ} (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f)
    {a M beta sigma : ℝ} (hbeta : 0 ≤ beta)
    (hVlower : ∀ x v, a * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ V x v v)
    (hfbound : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M)
    (N : ℕ) (hN : beta / Real.sqrt N * M ≤ a) :
    ConvexOn ℝ Set.univ (FunctionalInequalities.KLS.LogConcave.Suspension.potential V f beta sigma N) := by
  classical
  have hc : 0 ≤ beta / Real.sqrt N := div_nonneg hbeta (Real.sqrt_nonneg _)
  have hp := FunctionalInequalities.KLS.LogConcave.Suspension.convexOn_perturbation hV hf hVlower hfbound
    (c := beta / Real.sqrt N) (by simpa only [abs_of_nonneg hc] using hN)
  have hm := FunctionalInequalities.KLS.LogConcave.Suspension.convexOn_perturbation hV hf hVlower hfbound
    (c := -(beta / Real.sqrt N)) (by simpa only [abs_neg, abs_of_nonneg hc] using hN)
  have hmax := (FunctionalInequalities.KLS.LogConcave.Suspension.convexOn_sum_add_linear hm N (beta * sigma)).sup
    (FunctionalInequalities.KLS.LogConcave.Suspension.convexOn_sum_add_linear hp N (-(beta * sigma)))
  apply hmax.congr
  intro p _
  simp only [Pi.sup_apply]
  rw [FunctionalInequalities.KLS.LogConcave.Suspension.potential, abs_eq_max_neg]
  rw [mul_max_of_nonneg _ _ hbeta, add_max]
  congr 1 <;> rw [Finset.sum_add_distrib, ← Finset.mul_sum] <;> ring
