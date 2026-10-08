-- Prove2me | solution 1 for ConvexOptAlg.Newton.integral_formula
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T00:59:41.176066+00:00
-- url     : https://prove2.me/submissions/527ab7a8-630f-40ce-b932-9477759d984e

import Mathlib
import Definitions.Def_ConvexOptAlg_Newton_Defs

open InnerProductSpace in
theorem IntegralFormulaAux.contH {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
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

open ConvexOptAlg.Newton in
theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (hfgH : IsC2GradHess f g H) (x h : EuclideanSpace ℝ (Fin n)) :
    ∫ s in (0 : ℝ)..1, H (x + s • h) h = g (x + h) - g x := by
  have hHc := IntegralFormulaAux.contH f g H hfgH
  obtain ⟨_, _, h3⟩ := hfgH
  have hcont : Continuous fun s : ℝ => H (x + s • h) h :=
    (hHc.comp (continuous_const.add (continuous_id.smul continuous_const))).clm_apply
      continuous_const
  have hderiv : ∀ s : ℝ, HasDerivAt (fun s : ℝ => g (x + s • h)) (H (x + s • h) h) s := by
    intro s
    have hp : HasDerivAt (fun s : ℝ => x + s • h) h s := by
      simpa using ((hasDerivAt_id s).smul_const h).const_add x
    exact (h3 _).comp_hasDerivAt s hp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hderiv s)
    (hcont.intervalIntegrable 0 1)]
  simp
