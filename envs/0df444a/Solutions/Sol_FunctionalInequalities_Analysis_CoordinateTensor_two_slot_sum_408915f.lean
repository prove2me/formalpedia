-- Prove2me | solution 1 for FunctionalInequalities.Analysis.CoordinateTensor.two_slot_sum_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:54:12.684969+00:00
-- url     : https://prove2.me/submissions/f052376e-606e-4a36-9b4d-5ec63b18633b

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_EnergyForm
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_SlotAction
import Mathlib
import Theorems.Thm_FunctionalInequalities_Analysis_CoordinateTensor_sum_mul_prod_delta_erase_erase_408915f

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
/-- Two-slot delta collapse: the mixed second-order term is `Σ_s Σ_{u≠s} ⟨T, M^{(s)} M^{(u)} T⟩`. -/
 lemma solution (T : (Fin r → Fin n) → ℝ) (M : Matrix (Fin n) (Fin n) ℝ) :
    (∑ J : Fin r → Fin n, ∑ K : Fin r → Fin n, T J * T K *
      (∑ s : Fin r, (∑ u ∈ Finset.univ.erase s,
        (∏ v ∈ (Finset.univ.erase s).erase u, if J v = K v then (1 : ℝ) else 0) *
          (-M (J u) (K u))) * (-M (J s) (K s)))) =
      ∑ s : Fin r, ∑ u ∈ Finset.univ.erase s, FunctionalInequalities.Analysis.CoordinateTensor.inner T (FunctionalInequalities.Analysis.CoordinateTensor.actOn M s (FunctionalInequalities.Analysis.CoordinateTensor.actOn M u T)) := by
  have key (J : Fin r → Fin n) (s u : Fin r) (hus : u ≠ s) :
      (∑ K : Fin r → Fin n, T J * T K *
        ((∏ v ∈ (Finset.univ.erase s).erase u, if J v = K v then (1 : ℝ) else 0) *
          (-M (J u) (K u)) * (-M (J s) (K s)))) =
        T J * FunctionalInequalities.Analysis.CoordinateTensor.actOn M s (FunctionalInequalities.Analysis.CoordinateTensor.actOn M u T) J := by
    have hsu : s ≠ u := Ne.symm hus
    have hc := FunctionalInequalities.Analysis.CoordinateTensor.sum_mul_prod_delta_erase_erase_408915f J hsu
      (fun K => T K * M (J s) (K s) * M (J u) (K u))
    calc
      (∑ K : Fin r → Fin n, T J * T K *
          ((∏ v ∈ (Finset.univ.erase s).erase u, if J v = K v then (1 : ℝ) else 0) *
            (-M (J u) (K u)) * (-M (J s) (K s)))) =
          T J * ∑ K : Fin r → Fin n, (T K * M (J s) (K s) * M (J u) (K u)) *
            ∏ v ∈ (Finset.univ.erase s).erase u, (if J v = K v then (1 : ℝ) else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro K _
        ring
      _ = T J * ∑ k, ∑ l, T (Function.update (Function.update J s k) u l) *
            M (J s) k * M (J u) l := by
        rw [hc]
        congr 1
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro l _
        simp only [Function.update_self, Function.update_of_ne hsu]
      _ = T J * FunctionalInequalities.Analysis.CoordinateTensor.actOn M s (FunctionalInequalities.Analysis.CoordinateTensor.actOn M u T) J := by
        congr 1
        simp only [FunctionalInequalities.Analysis.CoordinateTensor.actOn, Function.update_of_ne hus]
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l _
        ring
  calc
    (∑ J : Fin r → Fin n, ∑ K : Fin r → Fin n, T J * T K *
        (∑ s : Fin r, (∑ u ∈ Finset.univ.erase s,
          (∏ v ∈ (Finset.univ.erase s).erase u, if J v = K v then (1 : ℝ) else 0) *
            (-M (J u) (K u))) * (-M (J s) (K s)))) =
        ∑ J : Fin r → Fin n, ∑ s : Fin r, ∑ u ∈ Finset.univ.erase s,
          ∑ K : Fin r → Fin n, T J * T K *
            ((∏ v ∈ (Finset.univ.erase s).erase u, if J v = K v then (1 : ℝ) else 0) *
              (-M (J u) (K u)) * (-M (J s) (K s))) := by
      apply Finset.sum_congr rfl
      intro J _
      calc
        (∑ K : Fin r → Fin n, T J * T K *
            (∑ s : Fin r, (∑ u ∈ Finset.univ.erase s,
              (∏ v ∈ (Finset.univ.erase s).erase u, if J v = K v then (1 : ℝ) else 0) *
                (-M (J u) (K u))) * (-M (J s) (K s)))) =
            ∑ K : Fin r → Fin n, ∑ s : Fin r, ∑ u ∈ Finset.univ.erase s, T J * T K *
              ((∏ v ∈ (Finset.univ.erase s).erase u, if J v = K v then (1 : ℝ) else 0) *
                (-M (J u) (K u)) * (-M (J s) (K s))) := by
          apply Finset.sum_congr rfl
          intro K _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s _
          rw [Finset.sum_mul, Finset.mul_sum]
        _ = ∑ s : Fin r, ∑ u ∈ Finset.univ.erase s, ∑ K : Fin r → Fin n, T J * T K *
              ((∏ v ∈ (Finset.univ.erase s).erase u, if J v = K v then (1 : ℝ) else 0) *
                (-M (J u) (K u)) * (-M (J s) (K s))) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro s _
          rw [Finset.sum_comm]
    _ = ∑ J : Fin r → Fin n, ∑ s : Fin r, ∑ u ∈ Finset.univ.erase s,
          T J * FunctionalInequalities.Analysis.CoordinateTensor.actOn M s (FunctionalInequalities.Analysis.CoordinateTensor.actOn M u T) J := by
      apply Finset.sum_congr rfl
      intro J _
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro u hu
      exact key J s u (Finset.ne_of_mem_erase hu)
    _ = ∑ s : Fin r, ∑ u ∈ Finset.univ.erase s, FunctionalInequalities.Analysis.CoordinateTensor.inner T (FunctionalInequalities.Analysis.CoordinateTensor.actOn M s (FunctionalInequalities.Analysis.CoordinateTensor.actOn M u T)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.sum_comm]
      rfl
