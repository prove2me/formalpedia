-- Prove2me | solution 1 for FunctionalInequalities.Analysis.exists_regular_moment_weak_tensor_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:27:14.31276+00:00
-- url     : https://prove2.me/submissions/6846dc36-cda3-4012-84b7-1d0407bb189a

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_CEK_MomentRegularity_WeakDerivative
import Theorems.Thm_FunctionalInequalities_Analysis_exists_lipschitzWith_neg_add_comp_gradient_readable
import Theorems.Thm_FunctionalInequalities_Analysis_exists_regular_moment_potential_readable
import Theorems.Thm_FunctionalInequalities_Analysis_exists_weak_third_derivative_readable
import Theorems.Thm_FunctionalInequalities_Analysis_secondDifference_le_of_map_gradient_readable

section RegularSource
open MeasureTheory Set
open scoped ContDiff
variable {n : ℕ} (hn : 0 < n)
    {K : Set (EuclideanSpace ℝ (Fin n))} {W : EuclideanSpace ℝ (Fin n) → ℝ}
    {κ : ℝ} (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K)
    (hKint : (interior K).Nonempty) (hW : ContDiff ℝ ∞ W)
    (hstrong : ConvexOn ℝ Set.univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
    (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hμ : (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) =
      (MeasureTheory.MeasureSpace.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
    (hiso : FunctionalInequalities.KLS.Isotropic μ)
noncomputable section
open MeasureTheory Set Filter
open scoped RealInnerProductSpace ContDiff Topology
open FunctionalInequalities.Probability.Stein
include hn hκ hK hKc hKint hW hstrong hμ hiso in
/-- Actual source-law tensor: both original hw and hF inputs are produced;
all original regular-class data and the weak/local-L2 tensor are retained. -/
theorem solution :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (L LF : NNReal)
        (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      ConvexOn ℝ univ u ∧ LipschitzWith L u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ContDiff ℝ 1 u ∧ LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) ∧
      LipschitzWith LF (fun x => -u x + W (gradient u x)) ∧
      (∀ x h, u (x + h) + u (x - h) - 2 * u x ≤ (4 / κ) * ‖h‖ ^ 2) ∧
      (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (FunctionalInequalities.Probability.Stein.hessianMatrix u x).PosDef ∧
        Real.log (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det = -u x + W (gradient u x) ∧
        ((16 / κ) • (1 : Matrix (Fin n) (Fin n) ℝ) - FunctionalInequalities.Probability.Stein.hessianMatrix u x).PosSemidef) ∧
      ∀ k i j,
        FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => FunctionalInequalities.Probability.Stein.hessianMatrix u x i j) (fun x => T x k i j)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
            MemLp (fun x => T x k i j) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  obtain ⟨u, L, hconv, hLip, hnorm, hmap, hC1, hG, hdata⟩ :=
    FunctionalInequalities.Analysis.exists_regular_moment_potential_readable hn hκ hK hKc hKint hW hstrong μ hμ hiso
  have hV : ContDiff ℝ 1 W := hW.of_le (WithTop.coe_le_coe.mpr le_top)
  have hw := FunctionalInequalities.Analysis.secondDifference_le_of_map_gradient_readable hLip hconv hnorm hK hKc hV hκ hstrong
    (hmap.trans hμ) hC1
  obtain ⟨LF, hF⟩ := FunctionalInequalities.Analysis.exists_lipschitzWith_neg_add_comp_gradient_readable hLip hG hV
  have hVc : ConvexOn ℝ univ W := by
    have hn' : ConvexOn ℝ univ (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖ ^ 2) :=
      convexOn_univ_norm.pow (fun _ _ => norm_nonneg _) 2
    have hq := hn'.smul (show 0 ≤ κ / 2 by positivity)
    have he :
        (fun y => W y - κ / 2 * ‖y‖ ^ 2) +
          (fun y => (κ / 2) • ‖y‖ ^ 2) = W := by
      funext y
      simp only [Pi.add_apply, smul_eq_mul, sub_add_cancel]
    rw [← he]
    exact hstrong.add hq
  obtain ⟨T, hT⟩ := FunctionalInequalities.Analysis.exists_weak_third_derivative_readable hC1 hconv hG hV hVc hF
    (show 0 < 16 / κ by positivity) hdata hw
  exact ⟨u, L, LF, T, hconv, hLip, hnorm, hmap, hC1, hG, hF, hw, hdata, hT⟩
