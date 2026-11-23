-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G7.map_scale
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:34.339639+00:00
-- url     : https://prove2.me/submissions/aa5ac228-d900-44ec-94ad-2bdf7469216c

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Theorems.Thm_Formalism_FourierDecayAlt_P_dimension_count
import Theorems.Thm_Formalism_FourierDecayAlt_P_scale_product_measure


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G7
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2
namespace Formalism.FourierDecayAlt.P.G7
theorem _root_.solution (β t : ℂ) (n : ℕ) (ht : t ≠ 0) :
    Measure.map (fun p : BlockCoord n => ((t • p.1, t • p.2.1, t • p.2.2) : BlockCoord n)) (muBlock β n) =
      Real.toNNReal ((‖t‖ ^ (n * (n + 3)))⁻¹) • muBlock β n := by
  have hm : ∀ ι : Type, ∀ [Fintype ι], Measurable (fun v : ι → ℂ => t • v) := fun ι _ => measurable_const_smul t
  have e : (fun p : BlockCoord n => ((t • p.1, t • p.2.1, t • p.2.2) : BlockCoord n)) =
      Prod.map (fun v => t • v) (Prod.map (fun v => t • v) (fun v => t • v)) := rfl
  unfold muBlock
  rw [e, ← Measure.map_prod_map _ _ (hm _) ((hm _).prodMap (hm _)), ← Measure.map_prod_map _ _ (hm _) (hm _),
    scale_product_measure β t _ ht, scale_product_measure β t _ ht]
  simp only [ENNReal.smul_def, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  congr 1
  have hc : 2 * Fintype.card (UT n) = n * (n - 1) := (dimension_count n).1
  rw [hc, Fintype.card_fin, ← ENNReal.coe_mul, ← ENNReal.coe_mul, ← Real.toNNReal_mul (by positivity),
    ← Real.toNNReal_mul (by positivity), ← mul_inv, ← mul_inv, ← pow_add, ← pow_add]
  congr 4
  cases n with
  | zero => rfl
  | succ k => simp only [Nat.add_sub_cancel]; ring
end Formalism.FourierDecayAlt.P.G7
