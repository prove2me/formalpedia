-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.PoissonIterate.norm_taylorField_sq_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:42:28.856993+00:00
-- url     : https://prove2.me/submissions/20ee2e64-f834-4152-82b8-5be23dfa2328

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Criterion

section
noncomputable section
open Finset
open scoped RealInnerProductSpace
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
theorem FunctionalInequalities.Analysis.Tensor.coordTensor_apply {n k : ℕ} (b : OrthonormalBasis (Fin n) ℝ E)
    (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ) (i : Fin k → Fin n) :
    coordTensor b Φ i = Φ (fun j => b (i j)) := by
  rfl
end
end
end

noncomputable section
open MeasureTheory Filter Topology Finset
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Tensor
open scoped ENNReal NNReal RealInnerProductSpace InnerProductSpace ContDiff
section Taylor
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] {ν : MeasureTheory.ProbabilityMeasure V}
/-- **The Taylor bound (29) componentwise** (BKL p. 16, proof of Lemma 3.8, and p. 17): if
`|T_d g| ≤ R^d ‖g‖₂` for every `g ∈ L²(ν)` in the Hilbert–Schmidt norm of the standard basis,
then `|T_d u|² ≤ R^{2d} ‖u‖²` for every tensor field `u`, by summing over its components. -/
theorem solution {R : ℝ} {d : ℕ}
    (h29 : ∀ g : Lp ℝ 2 (ν : Measure V),
      ‖FunctionalInequalities.Analysis.Tensor.coordTensor (stdOrthonormalBasis ℝ V) (FunctionalInequalities.Analysis.BakryEmery.taylorTensor (ν : Measure V) (⇑g) d)‖ ≤
        R ^ d * ‖g‖) {k : ℕ} (u : FunctionalInequalities.KLS.LogConcave.PoissonIterate.Field ν k) :
    ‖FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorField d u‖ ^ 2 ≤ R ^ (2 * d) * FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq u := by
  rw [EuclideanSpace.norm_sq_eq, ← (Fin.appendEquiv d k).sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm, FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq, Finset.mul_sum]
  refine Finset.sum_le_sum fun I _ => ?_
  have hI : ∑ J : Fin d → Fin (Module.finrank ℝ V),
      ‖FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorField d u (Fin.appendEquiv d k (J, I))‖ ^ 2 =
        ‖FunctionalInequalities.Analysis.Tensor.coordTensor (stdOrthonormalBasis ℝ V) (FunctionalInequalities.Analysis.BakryEmery.taylorTensor (ν : Measure V) (⇑(u I)) d)‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun J _ => ?_
    simp [FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorField, FunctionalInequalities.Analysis.Tensor.coordTensor_apply, Fin.append_left, Fin.append_right]
  rw [hI, pow_mul', ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (h29 (u I)) 2
