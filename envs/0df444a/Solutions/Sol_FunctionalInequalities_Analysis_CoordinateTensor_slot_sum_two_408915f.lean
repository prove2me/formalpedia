-- Prove2me | solution 1 for FunctionalInequalities.Analysis.CoordinateTensor.slot_sum_two_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:54:11.633997+00:00
-- url     : https://prove2.me/submissions/ebfc791f-87a5-40b2-a7d2-4f2bfdf96c38

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_EnergyForm
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_SlotAction
import Mathlib
import Theorems.Thm_FunctionalInequalities_Analysis_CoordinateTensor_sum_mul_prod_delta_erase_408915f

noncomputable section
open Matrix
open scoped RealInnerProductSpace
section S3Bf3B2SecondOrderCore
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
/-- One-slot delta collapse with two tensors: `Σ_{J,K} S_J T_K Σ_s Π_{u≠s} δ (−M_{J_s K_s}) = −⟨S, Σ_M T⟩`. -/
 lemma solution
    (S T : (Fin r → Fin n) → ℝ) (M : Matrix (Fin n) (Fin n) ℝ) :
    (∑ J : Fin r → Fin n, ∑ K : Fin r → Fin n,
      S J * T K * (∑ s : Fin r,
        (∏ u ∈ Finset.univ.erase s, if J u = K u then (1 : ℝ) else 0) *
          (-M (J s) (K s)))) =
      -FunctionalInequalities.Analysis.CoordinateTensor.inner S (FunctionalInequalities.Analysis.CoordinateTensor.actSum M T) := by
  let D (s : Fin r) (J K : Fin r → Fin n) : ℝ :=
    ∏ u ∈ Finset.univ.erase s, if J u = K u then (1 : ℝ) else 0
  have hc (s : Fin r) (J : Fin r → Fin n) :
      (∑ K, (T K * M (J s) (K s)) * D s J K) =
        ∑ k, T (Function.update J s k) * M (J s) k := by
    simpa only [D, Function.update_self] using
      FunctionalInequalities.Analysis.CoordinateTensor.sum_mul_prod_delta_erase_408915f J s (fun K => T K * M (J s) (K s))
  have hs (s : Fin r) (J : Fin r → Fin n) :
      (∑ K, S J * T K * (D s J K * (-M (J s) (K s)))) =
        -(S J * FunctionalInequalities.Analysis.CoordinateTensor.actOn M s T J) := by
    calc
      (∑ K, S J * T K * (D s J K * (-M (J s) (K s)))) =
          ∑ K, -(S J * ((T K * M (J s) (K s)) * D s J K)) := by
        apply Finset.sum_congr rfl
        intro K _
        ring
      _ = -(S J * ∑ K, (T K * M (J s) (K s)) * D s J K) := by
        rw [Finset.sum_neg_distrib, Finset.mul_sum]
      _ = -(S J * FunctionalInequalities.Analysis.CoordinateTensor.actOn M s T J) := by
        rw [hc]
        apply congrArg (fun z : ℝ => -(S J * z))
        unfold FunctionalInequalities.Analysis.CoordinateTensor.actOn
        apply Finset.sum_congr rfl
        intro k _
        exact mul_comm _ _
  have hJ (J : Fin r → Fin n) :
      (∑ K, S J * T K * (∑ s, D s J K * (-M (J s) (K s)))) =
        -(S J * FunctionalInequalities.Analysis.CoordinateTensor.actSum M T J) := by
    calc
      (∑ K, S J * T K * (∑ s, D s J K * (-M (J s) (K s)))) =
          ∑ K, ∑ s, S J * T K * (D s J K * (-M (J s) (K s))) := by
        simp only [Finset.mul_sum]
      _ = ∑ s, ∑ K, S J * T K * (D s J K * (-M (J s) (K s))) := by
        rw [Finset.sum_comm]
      _ = ∑ s, -(S J * FunctionalInequalities.Analysis.CoordinateTensor.actOn M s T J) := by
        apply Finset.sum_congr rfl
        intro s _
        exact hs s J
      _ = -(S J * FunctionalInequalities.Analysis.CoordinateTensor.actSum M T J) := by
        unfold FunctionalInequalities.Analysis.CoordinateTensor.actSum
        rw [Finset.sum_neg_distrib, Finset.mul_sum]
  change (∑ J, ∑ K, S J * T K * (∑ s, D s J K * (-M (J s) (K s)))) =
    -FunctionalInequalities.Analysis.CoordinateTensor.inner S (FunctionalInequalities.Analysis.CoordinateTensor.actSum M T)
  calc
    (∑ J, ∑ K, S J * T K * (∑ s, D s J K * (-M (J s) (K s)))) =
        ∑ J, -(S J * FunctionalInequalities.Analysis.CoordinateTensor.actSum M T J) := by
      apply Finset.sum_congr rfl
      intro J _
      exact hJ J
    _ = -FunctionalInequalities.Analysis.CoordinateTensor.inner S (FunctionalInequalities.Analysis.CoordinateTensor.actSum M T) := by
      simp only [FunctionalInequalities.Analysis.CoordinateTensor.inner, Finset.sum_neg_distrib]
