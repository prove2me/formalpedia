-- Prove2me | solution 1 for FunctionalInequalities.Analysis.CoordinateTensor.slot_derivative_sum_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:54:58.741838+00:00
-- url     : https://prove2.me/submissions/2886547e-1eea-46d1-9b5d-995998056026

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_EnergyForm
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_SlotAction
import Mathlib
import Theorems.Thm_FunctionalInequalities_Analysis_CoordinateTensor_sum_mul_prod_delta_erase_408915f

noncomputable section
open Matrix
open scoped RealInnerProductSpace
section S3Bf2EnergyFormFirstOrder
open Matrix
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.CoordinateTensor
end FunctionalInequalities.Analysis.CoordinateTensor
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.CoordinateTensor
variable {n r : ℕ}
namespace FunctionalInequalities.Analysis.CoordinateTensor
end FunctionalInequalities.Analysis.CoordinateTensor
open FunctionalInequalities.Analysis.CoordinateTensor in
 lemma solution
    (T : (Fin r → Fin n) → ℝ) (M : Matrix (Fin n) (Fin n) ℝ) :
    (∑ J : Fin r → Fin n, ∑ K : Fin r → Fin n,
      T J * T K * (∑ s : Fin r,
        (∏ u ∈ Finset.univ.erase s, if J u = K u then (1 : ℝ) else 0) *
          (-M (J s) (K s)))) =
      -FunctionalInequalities.Analysis.CoordinateTensor.inner T (FunctionalInequalities.Analysis.CoordinateTensor.actSum M T) := by
  classical
  let D (s : Fin r) (J K : Fin r → Fin n) : ℝ :=
    ∏ u ∈ Finset.univ.erase s, if J u = K u then (1 : ℝ) else 0
  have hc (s : Fin r) (J : Fin r → Fin n) :
      (∑ K, (T K * M (J s) (K s)) * D s J K) =
        ∑ k, T (Function.update J s k) * M (J s) k := by
    simpa only [D, Function.update_self] using
      FunctionalInequalities.Analysis.CoordinateTensor.sum_mul_prod_delta_erase_408915f J s (fun K => T K * M (J s) (K s))
  have hs (s : Fin r) (J : Fin r → Fin n) :
      (∑ K, T J * T K * (D s J K * (-M (J s) (K s)))) =
        -(T J * FunctionalInequalities.Analysis.CoordinateTensor.actOn M s T J) := by
    calc
      (∑ K, T J * T K * (D s J K * (-M (J s) (K s)))) =
          ∑ K, -(T J * ((T K * M (J s) (K s)) * D s J K)) := by
        apply Finset.sum_congr rfl
        intro K _
        ring
      _ = -(T J * ∑ K, (T K * M (J s) (K s)) * D s J K) := by
        rw [Finset.sum_neg_distrib, Finset.mul_sum]
      _ = -(T J * FunctionalInequalities.Analysis.CoordinateTensor.actOn M s T J) := by
        rw [hc]
        apply congrArg (fun z : ℝ => -(T J * z))
        unfold FunctionalInequalities.Analysis.CoordinateTensor.actOn
        apply Finset.sum_congr rfl
        intro k _
        exact mul_comm _ _
  have hJ (J : Fin r → Fin n) :
      (∑ K, T J * T K * (∑ s, D s J K * (-M (J s) (K s)))) =
        -(T J * FunctionalInequalities.Analysis.CoordinateTensor.actSum M T J) := by
    calc
      (∑ K, T J * T K * (∑ s, D s J K * (-M (J s) (K s)))) =
          ∑ K, ∑ s, T J * T K * (D s J K * (-M (J s) (K s))) := by
        simp only [Finset.mul_sum]
      _ = ∑ s, ∑ K, T J * T K * (D s J K * (-M (J s) (K s))) := by
        rw [Finset.sum_comm]
      _ = ∑ s, -(T J * FunctionalInequalities.Analysis.CoordinateTensor.actOn M s T J) := by
        apply Finset.sum_congr rfl
        intro s _
        exact hs s J
      _ = -(T J * FunctionalInequalities.Analysis.CoordinateTensor.actSum M T J) := by
        unfold FunctionalInequalities.Analysis.CoordinateTensor.actSum
        rw [Finset.sum_neg_distrib, Finset.mul_sum]
  change (∑ J, ∑ K, T J * T K * (∑ s, D s J K * (-M (J s) (K s)))) =
    -FunctionalInequalities.Analysis.CoordinateTensor.inner T (FunctionalInequalities.Analysis.CoordinateTensor.actSum M T)
  calc
    (∑ J, ∑ K, T J * T K * (∑ s, D s J K * (-M (J s) (K s)))) =
        ∑ J, -(T J * FunctionalInequalities.Analysis.CoordinateTensor.actSum M T J) := by
      apply Finset.sum_congr rfl
      intro J _
      exact hJ J
    _ = -FunctionalInequalities.Analysis.CoordinateTensor.inner T (FunctionalInequalities.Analysis.CoordinateTensor.actSum M T) := by
      simp only [FunctionalInequalities.Analysis.CoordinateTensor.inner, Finset.sum_neg_distrib]
