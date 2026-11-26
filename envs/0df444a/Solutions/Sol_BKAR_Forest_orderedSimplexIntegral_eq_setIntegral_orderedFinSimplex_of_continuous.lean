-- Prove2me | solution 1 for BKAR.Forest.orderedSimplexIntegral_eq_setIntegral_orderedFinSimplex_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:46:50.929669+00:00
-- url     : https://prove2.me/submissions/4b3f7d17-ea1f-447d-a1d9-e60c7fbbcca1

import Definitions.Def_BKAR_CubePartition_SimplexSector
import Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
import Theorems.Thm_BKAR_Forest_orderedFinSimplex_eq_orderedFinSimplexWithTop_one
import Theorems.Thm_BKAR_Forest_orderedSimplexIntegralAux_eq_setIntegral_orderedFinSimplexWithTop_of_continuous

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V]
namespace BKAR.Forest
theorem _root_.solution
    (order : List (Edge V)) (G : (Fin order.length → ℝ) → ℝ)
    (hG : Continuous G) :
    orderedSimplexIntegral order
      (fun ts => G (fun i : Fin order.length => ts.getD i.val 0)) =
      ∫ xs in orderedFinSimplex order.length, G xs := by
  rw [orderedSimplexIntegral]
  calc
    orderedSimplexIntegralAux 1 order
        (fun ts => G (fun i : Fin order.length => ts.getD i.val 0)) =
      ∫ xs in orderedFinSimplexWithTop 1 order.length, G xs := by
        exact
          orderedSimplexIntegralAux_eq_setIntegral_orderedFinSimplexWithTop_of_continuous
            zero_le_one order G hG
    _ = ∫ xs in orderedFinSimplex order.length, G xs := by
        rw [orderedFinSimplex_eq_orderedFinSimplexWithTop_one]
end BKAR.Forest
