-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrderChainWeights.chainWeight_snoc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:35:37.696402+00:00
-- url     : https://prove2.me/submissions/e0d2b682-5f9a-487f-b87c-e68c191723a2

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrderChainWeights

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrderChainWeights
open Matrix Finset MeasureTheory
open Formalism.FourierDecayAlt.S3
open scoped ENNReal
namespace Formalism.FourierDecayAlt.P.OrderChainWeights
theorem _root_.solution {X : Type} (nrm : X → ℝ≥0∞) (i : ℕ) (h : Fin i → X) (c : X) :
    chainWeight nrm (i + 1) (Fin.snoc h c : Fin (i + 1) → X) =
      chainWeight nrm i h * (∏ l, nrm (h l)) ^ 2 := by
  unfold chainWeight
  rw [Finset.prod_range_succ]
  congr 1
  · refine Finset.prod_congr rfl fun l hl => ?_
    have hl' : l < i := Finset.mem_range.mp hl
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.snoc_castSucc, Fin.val_last]
    rw [if_neg (by omega), mul_one]
  · rw [Fin.prod_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.snoc_castSucc, Fin.val_last, lt_irrefl, if_false, mul_one,
      Fin.is_lt, if_true]
    rw [Finset.prod_pow]
end Formalism.FourierDecayAlt.P.OrderChainWeights
