-- Prove2me | solution 1 for D1Bound5.bennettClearedTaylor_eval_remove_pole
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:36:54.117513+00:00
-- url     : https://prove2.me/submissions/0c9d4960-9030-4808-bd7d-c5d0e9f0365b

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettClearedResidues_Definitions
import Definitions.Def_D1Bound5_BennettPoleSeries_Definitions
import Theorems.Thm_D1Bound5_bennettClearedTaylor_eval

section
open Finset

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]







/-- The single-pole node-removal identity is precisely Chu--Vandermonde,
expressed by multiplication of formal binomial series. -/
theorem _root_.solution
    (k r : ℕ) (hr : r ≤ k) (ν a N : F) (B : PowerSeries F)
    (hd : N + a ≠ 0) :
    (bennettClearedTaylor k r ν a
      (bennettPoleSeries (N + a) k * B)).eval N =
      ((N + a)⁻¹) ^ k *
        (bennettClearedTaylor k r (ν - (k : F)) a B).eval N := by
  rw [bennettClearedTaylor_eval k r hr ν a N _ hd,
    bennettClearedTaylor_eval k r hr (ν - (k : F)) a N B hd]
  have he : ((k : F) + ν) + -(k : F) = (k : F) + (ν - (k : F)) := by ring
  have hs :
      PowerSeries.rescale (N + a)⁻¹
          (PowerSeries.binomialSeries F ((k : F) + ν)) *
        (bennettPoleSeries (N + a) k * B) =
      PowerSeries.C (((N + a)⁻¹) ^ k) *
        (PowerSeries.rescale (N + a)⁻¹
          (PowerSeries.binomialSeries F ((k : F) + (ν - (k : F)))) * B) := by
    unfold bennettPoleSeries
    calc
      _ = PowerSeries.C (((N + a)⁻¹) ^ k) *
          ((PowerSeries.rescale (N + a)⁻¹
              (PowerSeries.binomialSeries F ((k : F) + ν)) *
            PowerSeries.rescale (N + a)⁻¹
              (PowerSeries.binomialSeries F (-(k : F)))) * B) := by ring
      _ = _ := by rw [← map_mul, ← PowerSeries.binomialSeries_add, he]
  rw [hs, PowerSeries.coeff_C_mul]
  ring

section Nodes

variable {I : Type*} [DecidableEq I]

















end Nodes

end D1Bound5
end
