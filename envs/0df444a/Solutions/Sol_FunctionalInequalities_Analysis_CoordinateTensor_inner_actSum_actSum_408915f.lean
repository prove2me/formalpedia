-- Prove2me | solution 1 for FunctionalInequalities.Analysis.CoordinateTensor.inner_actSum_actSum_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:53:22.40467+00:00
-- url     : https://prove2.me/submissions/68cfa37e-ba00-48b1-badf-99d39a1f352b

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_SlotAction
import Mathlib
import Theorems.Thm_FunctionalInequalities_Analysis_CoordinateTensor_inner_actOn_left_408915f

noncomputable section
open Matrix
section S3Bf3ASlotActionAlgebra
open Matrix
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
/-- `|Σ_M T|² = Σ_s |M^{(s)} T|² + Σ_{s ≠ t} ⟨T, M^{(s)} M^{(t)} T⟩` for symmetric `M` (BKL (87)–(88)). -/
theorem solution (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) (T : (Fin r → Fin n) → ℝ) :
    FunctionalInequalities.Analysis.CoordinateTensor.inner (FunctionalInequalities.Analysis.CoordinateTensor.actSum M T) (FunctionalInequalities.Analysis.CoordinateTensor.actSum M T) =
      ∑ s, FunctionalInequalities.Analysis.CoordinateTensor.inner (FunctionalInequalities.Analysis.CoordinateTensor.actOn M s T) (FunctionalInequalities.Analysis.CoordinateTensor.actOn M s T) +
        ∑ s, ∑ t ∈ Finset.univ.erase s, FunctionalInequalities.Analysis.CoordinateTensor.inner T (FunctionalInequalities.Analysis.CoordinateTensor.actOn M s (FunctionalInequalities.Analysis.CoordinateTensor.actOn M t T)) := by
  classical
  have hexpand :
      FunctionalInequalities.Analysis.CoordinateTensor.inner (FunctionalInequalities.Analysis.CoordinateTensor.actSum M T) (FunctionalInequalities.Analysis.CoordinateTensor.actSum M T) =
        ∑ s, ∑ t, FunctionalInequalities.Analysis.CoordinateTensor.inner (FunctionalInequalities.Analysis.CoordinateTensor.actOn M s T) (FunctionalInequalities.Analysis.CoordinateTensor.actOn M t T) := by
    unfold FunctionalInequalities.Analysis.CoordinateTensor.inner FunctionalInequalities.Analysis.CoordinateTensor.actSum
    calc
      (∑ J, (∑ s, FunctionalInequalities.Analysis.CoordinateTensor.actOn M s T J) * (∑ t, FunctionalInequalities.Analysis.CoordinateTensor.actOn M t T J)) =
          ∑ J, ∑ s, ∑ t, (FunctionalInequalities.Analysis.CoordinateTensor.actOn M s T J) * (FunctionalInequalities.Analysis.CoordinateTensor.actOn M t T J) := by
            apply Finset.sum_congr rfl
            intro J hJ
            rw [Finset.sum_mul_sum]
      _ = ∑ s, ∑ J, ∑ t, (FunctionalInequalities.Analysis.CoordinateTensor.actOn M s T J) * (FunctionalInequalities.Analysis.CoordinateTensor.actOn M t T J) := by
            rw [Finset.sum_comm]
      _ = ∑ s, ∑ t, ∑ J, (FunctionalInequalities.Analysis.CoordinateTensor.actOn M s T J) * (FunctionalInequalities.Analysis.CoordinateTensor.actOn M t T J) := by
            apply Finset.sum_congr rfl
            intro s hs
            rw [Finset.sum_comm]
      _ = ∑ s, ∑ t, FunctionalInequalities.Analysis.CoordinateTensor.inner (FunctionalInequalities.Analysis.CoordinateTensor.actOn M s T) (FunctionalInequalities.Analysis.CoordinateTensor.actOn M t T) := by
            rfl
  calc
    FunctionalInequalities.Analysis.CoordinateTensor.inner (FunctionalInequalities.Analysis.CoordinateTensor.actSum M T) (FunctionalInequalities.Analysis.CoordinateTensor.actSum M T) =
        ∑ s, ∑ t, FunctionalInequalities.Analysis.CoordinateTensor.inner (FunctionalInequalities.Analysis.CoordinateTensor.actOn M s T) (FunctionalInequalities.Analysis.CoordinateTensor.actOn M t T) := hexpand
    _ = ∑ s, (FunctionalInequalities.Analysis.CoordinateTensor.inner (FunctionalInequalities.Analysis.CoordinateTensor.actOn M s T) (FunctionalInequalities.Analysis.CoordinateTensor.actOn M s T) +
          ∑ t ∈ Finset.univ.erase s, FunctionalInequalities.Analysis.CoordinateTensor.inner (FunctionalInequalities.Analysis.CoordinateTensor.actOn M s T) (FunctionalInequalities.Analysis.CoordinateTensor.actOn M t T)) := by
          apply Finset.sum_congr rfl
          intro s hs
          symm
          exact Finset.add_sum_erase (Finset.univ : Finset (Fin r))
            (fun t => FunctionalInequalities.Analysis.CoordinateTensor.inner (FunctionalInequalities.Analysis.CoordinateTensor.actOn M s T) (FunctionalInequalities.Analysis.CoordinateTensor.actOn M t T))
            (Finset.mem_univ s)
    _ = (∑ s, FunctionalInequalities.Analysis.CoordinateTensor.inner (FunctionalInequalities.Analysis.CoordinateTensor.actOn M s T) (FunctionalInequalities.Analysis.CoordinateTensor.actOn M s T)) +
          ∑ s, ∑ t ∈ Finset.univ.erase s,
            FunctionalInequalities.Analysis.CoordinateTensor.inner (FunctionalInequalities.Analysis.CoordinateTensor.actOn M s T) (FunctionalInequalities.Analysis.CoordinateTensor.actOn M t T) := by
          rw [Finset.sum_add_distrib]
    _ = (∑ s, FunctionalInequalities.Analysis.CoordinateTensor.inner (FunctionalInequalities.Analysis.CoordinateTensor.actOn M s T) (FunctionalInequalities.Analysis.CoordinateTensor.actOn M s T)) +
          ∑ s, ∑ t ∈ Finset.univ.erase s,
            FunctionalInequalities.Analysis.CoordinateTensor.inner T (FunctionalInequalities.Analysis.CoordinateTensor.actOn M s (FunctionalInequalities.Analysis.CoordinateTensor.actOn M t T)) := by
          apply congrArg (fun x : ℝ =>
            (∑ s, FunctionalInequalities.Analysis.CoordinateTensor.inner (FunctionalInequalities.Analysis.CoordinateTensor.actOn M s T) (FunctionalInequalities.Analysis.CoordinateTensor.actOn M s T)) + x)
          apply Finset.sum_congr rfl
          intro s hs
          apply Finset.sum_congr rfl
          intro t ht
          exact FunctionalInequalities.Analysis.CoordinateTensor.inner_actOn_left_408915f M hM s T (FunctionalInequalities.Analysis.CoordinateTensor.actOn M t T)
