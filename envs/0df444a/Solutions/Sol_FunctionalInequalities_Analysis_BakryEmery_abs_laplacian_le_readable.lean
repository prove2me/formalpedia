-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.abs_laplacian_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:24:54.117267+00:00
-- url     : https://prove2.me/submissions/188c5f64-682a-4dee-aa86-feeac423c500

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_Temperate

noncomputable section
open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] in
/-- `|Δg(x)| ≤ dim E · ‖∇²g(x)‖`. -/
theorem solution (g : E → ℝ) (x : E) :
    |Laplacian.laplacian g x| ≤ Module.finrank ℝ E * ‖iteratedFDeriv ℝ 2 g x‖ := by
    rw [FunctionalInequalities.Analysis.BakryEmery.laplacian_eq_sum_fderiv_fderiv]
    have hnorm (i : Fin (Module.finrank ℝ E)) :
        ‖(stdOrthonormalBasis ℝ E) i‖ = 1 :=
      (stdOrthonormalBasis ℝ E).norm_eq_one i
    have hterm (i : Fin (Module.finrank ℝ E)) :
        |(fderiv ℝ (fderiv ℝ g) x ((stdOrthonormalBasis ℝ E) i))
            ((stdOrthonormalBasis ℝ E) i)| ≤
          ‖iteratedFDeriv ℝ 2 g x‖ := by
      have h :=
        (iteratedFDeriv ℝ 2 g x).le_opNorm
          ![(stdOrthonormalBasis ℝ E) i, (stdOrthonormalBasis ℝ E) i]
      rw [iteratedFDeriv_two_apply] at h
      simpa [Real.norm_eq_abs] using h
    calc
      |∑ i : Fin (Module.finrank ℝ E),
          (fderiv ℝ (fderiv ℝ g) x ((stdOrthonormalBasis ℝ E) i))
            ((stdOrthonormalBasis ℝ E) i)| ≤
          ∑ i : Fin (Module.finrank ℝ E),
            |(fderiv ℝ (fderiv ℝ g) x ((stdOrthonormalBasis ℝ E) i))
              ((stdOrthonormalBasis ℝ E) i)| := by
        apply Finset.abs_sum_le_sum_abs
      _ ≤ ∑ i : Fin (Module.finrank ℝ E), ‖iteratedFDeriv ℝ 2 g x‖ := by
        exact Finset.sum_le_sum (fun i _ => hterm i)
      _ = (Module.finrank ℝ E : ℝ) * ‖iteratedFDeriv ℝ 2 g x‖ := by
        simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]
