-- Prove2me | solution 1 for BlockCycleRotation.integralSum_prepartition
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T12:02:45.075512+00:00
-- url     : https://prove2.me/submissions/659ca95d-ba3d-4a49-8c8e-5df58ff6921c

import Definitions.Def_BlockCycleRotation_Algorithm
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_Theorem10
import Theorems.Thm_BlockCycleRotation_admissibleIndex_unitBox
import Mathlib

open Finset Real Filter Topology MeasureTheory BoxIntegral
open scoped ENNReal

namespace BlockCycleRotation

@[simp]
theorem remSum_zero (n : ℕ) : remSum n 0 = 0 := by
  rw [remSum]; simp

@[simp]
theorem norm_e (θ : ℝ) : ‖e θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

@[simp]
theorem norm_e_pow (θ : ℝ) (n : ℕ) : ‖e θ ^ n‖ = 1 := by
  rw [norm_pow, norm_e, one_pow]

@[simp]
theorem cost_zero (n : ℕ) : cost n 0 = 0 := by
  rw [cost]; simp

@[simp]
theorem finalSeg_zero (n : ℕ) : finalSeg n 0 = n := by
  rw [finalSeg]; simp

@[simp]
theorem e_zero : e 0 = 1 := by simp [e]

@[simp] theorem K_nil : K [] = 1 := rfl

@[simp] theorem K_singleton (c : ℕ) : K [c] = c := rfl

@[simp] theorem cf_zero (a : ℕ) : cf a 0 = [] := by rw [cf]; simp

end BlockCycleRotation

open BlockCycleRotation in
/-- The integral sum of the uniform subdivision is the evenly spaced Riemann sum. -/
theorem solution (n : ℕ) [NeZero n] :
    integralSum FBar (BoxAdditiveMap.toSMul (MeasureTheory.Measure.toBoxAdditive volume))
        (unitPartition.prepartition n unitBox)
      = (∑ j ∈ Finset.range n, fBar (((j : ℝ) + 1) / (n : ℝ))) / (n : ℝ):= by
  classical
  have hn : 0 < n := Nat.pos_of_neZero n
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [integralSum]
  have hboxes : (unitPartition.prepartition n unitBox).boxes
      = Finset.image (fun ν => unitPartition.box n ν) (unitPartition.admissibleIndex n unitBox) :=
    rfl
  rw [hboxes, Finset.sum_image (fun x _ y _ h => unitPartition.box_injective n h),
    admissibleIndex_unitBox n,
    Finset.sum_image (fun x hx y hy h => by
      have := congrFun h (0 : Fin 1)
      simpa using this)]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hν : (fun _ : Fin 1 => (j : ℤ)) ∈ unitPartition.admissibleIndex n unitBox := by
    rw [admissibleIndex_unitBox n]
    exact Finset.mem_image.2 ⟨j, hj, rfl⟩
  rw [unitPartition.prepartition_tag n hν]
  have hvol : (MeasureTheory.Measure.toBoxAdditive volume)
      (unitPartition.box n (fun _ : Fin 1 => (j : ℤ))) = 1 / (n : ℝ) := by
    rw [MeasureTheory.Measure.toBoxAdditive_apply, MeasureTheory.measureReal_def,
      unitPartition.volume_box]
    simp
  rw [BoxAdditiveMap.toSMul_apply, hvol]
  have htag : FBar (unitPartition.tag n (fun _ : Fin 1 => (j : ℤ)))
      = fBar (((j : ℝ) + 1) / (n : ℝ)) := by
    rw [FBar, unitPartition.tag_apply]
    push_cast
    ring_nf
  rw [htag, smul_eq_mul]
  ring
