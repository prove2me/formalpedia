-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.Suspension.sum_sq_cumulant_ge_of_entries_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:20:48.655192+00:00
-- url     : https://prove2.me/submissions/70a4c218-074a-4116-9c02-e7069d1f169b

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Cumulant
import Theorems.Thm_FunctionalInequalities_Analysis_Tensor_sum_sq_blocks_le_readable

section
noncomputable section
open Finset
section FiniteIndex
variable {ι κ : Type*}
variable [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
/-- If every block entry is `c` times a common array `T`, the block energy `|κ| c² |T|²` is at most
the whole Hilbert–Schmidt energy (the source's use, with `|κ| = N` and `c = d!/(σ√N)`). -/
theorem FunctionalInequalities.Analysis.Tensor.card_mul_sq_mul_sum_sq_le_of_blocks {d : ℕ} (hd : 0 < d) (A : (Fin d → Option (κ × ι)) → ℝ) (c : ℝ)
    (T : (Fin d → ι) → ℝ) (hA : ∀ i j, A (fun k => some (i, j k)) = c * T j) :
    (Fintype.card κ : ℝ) * c ^ 2 * ∑ j, T j ^ 2 ≤ ∑ J, A J ^ 2 := by
  have h := sum_sq_blocks_le_readable hd A
  simp only [hA, mul_pow, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at h
  linarith
end FiniteIndex
end
end

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
open MeasureTheory FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Analysis.Tensor
open FunctionalInequalities.Probability.Line
/-- **Hilbert–Schmidt lower bound from (112)** (BKL p. 29). -/
theorem solution {n N : ℕ} (hN : 0 < N) (ν : Measure (FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n))
    (μ : Measure (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ) {σ : ℝ} (hσ : 0 < σ)
    {d : ℕ} (hd : 1 ≤ d)
    (h112 : ∀ (I : Fin d → Fin N) (J : Fin d → Fin n),
      FunctionalInequalities.Analysis.BakryEmery.cumulant ν (d + 1) (Fin.cons (EuclideanSpace.single none 1) fun k =>
          EuclideanSpace.single (some (I k, J k)) 1) =
        if ∀ k k', I k = I k' then
          (d.factorial : ℝ) / (σ * Real.sqrt N) *
            FunctionalInequalities.Analysis.BakryEmery.taylorTensor μ f d fun k => EuclideanSpace.basisFun (Fin n) ℝ (J k)
        else 0) :
    (d.factorial : ℝ) ^ 2 / σ ^ 2 *
        ‖FunctionalInequalities.Analysis.Tensor.coordTensor (EuclideanSpace.basisFun (Fin n) ℝ) (FunctionalInequalities.Analysis.BakryEmery.taylorTensor μ f d)‖ ^ 2 ≤
      ∑ K : Fin d → Option (Fin N × Fin n),
        FunctionalInequalities.Analysis.BakryEmery.cumulant ν (d + 1) (Fin.cons (EuclideanSpace.single none 1) fun k =>
          EuclideanSpace.single (K k) 1) ^ 2 := by
  classical
  have h := FunctionalInequalities.Analysis.Tensor.card_mul_sq_mul_sum_sq_le_of_blocks (κ := Fin N) (ι := Fin n) (by omega)
    (fun K => FunctionalInequalities.Analysis.BakryEmery.cumulant ν (d + 1) (Fin.cons (EuclideanSpace.single none 1) fun k =>
      EuclideanSpace.single (K k) 1))
    ((d.factorial : ℝ) / (σ * Real.sqrt N))
    (fun J => FunctionalInequalities.Analysis.BakryEmery.taylorTensor μ f d fun k => EuclideanSpace.basisFun (Fin n) ℝ (J k))
    (fun i j => by simpa using h112 (fun _ => i) j)
  have hnorm : ‖FunctionalInequalities.Analysis.Tensor.coordTensor (EuclideanSpace.basisFun (Fin n) ℝ) (FunctionalInequalities.Analysis.BakryEmery.taylorTensor μ f d)‖ ^ 2 =
      ∑ J : Fin d → Fin n,
        (FunctionalInequalities.Analysis.BakryEmery.taylorTensor μ f d fun k => EuclideanSpace.basisFun (Fin n) ℝ (J k)) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [FunctionalInequalities.Analysis.Tensor.coordTensor_apply]
  have hsqrt : Real.sqrt (N : ℝ) ^ 2 = N := Real.sq_sqrt (by positivity)
  have hc : (Fintype.card (Fin N) : ℝ) * ((d.factorial : ℝ) / (σ * Real.sqrt N)) ^ 2 =
      (d.factorial : ℝ) ^ 2 / σ ^ 2 := by
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    rw [Fintype.card_fin, div_pow, mul_pow, hsqrt]
    field_simp
  rw [hc] at h
  rw [hnorm]
  exact h
