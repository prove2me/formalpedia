-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.constant_product_formula
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:14.051306+00:00
-- url     : https://prove2.me/submissions/ffcf01bc-0b3b-4185-a61e-aad29347fdcb

import Definitions.Def_Formalism_FlagUnipotentLattices_UnitSumBound
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ConstantProductFormula
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_volU_pos_minkowski_factorial_bounds
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_volume_ratio_increment
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_volume_ratio_formula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.HermitianLatticeCounting.LocalIntegralStructure
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.LocalIntegralStructure.ConstProduct := by
  intro j r T T' g v n0 κ dimpi Vd VV hT hT' hg hv hVV hn
  have hR := volume_ratio_formula (j + 1) (2 * r + 1)
  have hS := volume_ratio_increment j
  have p0 := volU_pos_minkowski_factorial_bounds j
  have p1 := volU_pos_minkowski_factorial_bounds (j + 1)
  have p2 := volU_pos_minkowski_factorial_bounds (j + 1 + (2 * r + 1))
  have hsplit : ∏ i ∈ range (j + 1 + (2 * r + 1)), (i.factorial : ℝ) =
      (∏ i ∈ range (j + 1), (i.factorial : ℝ)) * ∏ i ∈ Ico (j + 1) (j + 1 + (2 * r + 1)), (i.factorial : ℝ) := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico, Finset.prod_Ico_consecutive _ (by omega) (by omega)]
  set F1 := ∏ i ∈ range (j + 1), (i.factorial : ℝ) with hF1
  set F2 := ∏ i ∈ Ico (j + 1) (j + 1 + (2 * r + 1)), (i.factorial : ℝ) with hF2
  have hF1p : 0 < F1 := prod_pos (fun i _ => by positivity)
  have hF2p : 0 < F2 := prod_pos (fun i _ => by positivity)
  rw [hsplit]
  have hpi := Real.pi_pos

  have L : n0 * (T * T') ^ j *
      (dimpi * (Vd / F1) * volU (j + 1 + (2 * r + 1)) * volU j /
        (VV / (F1 * F2) * volU (j + 1) ^ 2 * (2 * v) ^ (2 * r * (j + 1)))) =
      (n0 * (volU j / volU (j + 1))) * (volU (j + 1 + (2 * r + 1)) / volU (j + 1) * F2) * (T * T') ^ j *
        dimpi * (Vd / VV) / (2 * v) ^ (2 * r * (j + 1)) := by
    field_simp
  have hn' : n0 * ((j.factorial : ℝ) / (2 * Real.pi) ^ (j + 1)) =
      κ / (g ^ (2 * r + 2) * T * (2 * v)) ^ (j + 1) := by rw [← hn, mul_div_assoc]
  rw [L, hR, hS, hn']
  have e2 : (T * T') ^ j = (T * T') ^ (j + 1) / (T * T') := by rw [pow_succ]; field_simp
  have e3 : (2 * Real.pi) ^ ((2 * r + 1) * (j + 1)) = ((2 * Real.pi) ^ (2 * r + 1)) ^ (j + 1) := by rw [pow_mul]
  have e4 : (2 * v) ^ (2 * r * (j + 1)) = ((2 * v) ^ (2 * r)) ^ (j + 1) := by rw [pow_mul]
  have e5 : (T' / g ^ (2 * r + 2) * (Real.pi / v) ^ (2 * r + 1)) =
      (T * T') * (2 * Real.pi) ^ (2 * r + 1) / ((g ^ (2 * r + 2) * T * (2 * v)) * (2 * v) ^ (2 * r)) := by
    rw [div_pow, mul_pow 2 Real.pi, mul_pow 2 v (2 * r)]
    field_simp
    ring
  rw [pow_add (2 * Real.pi) ((2 * r + 1) * (j + 1)), e2, e3, e4, e5, div_pow, mul_pow (T * T'),
    mul_pow (g ^ (2 * r + 2) * T * (2 * v))]
  have hX : (g ^ (2 * r + 2) * T * (2 * v)) ^ (j + 1) ≠ 0 := by positivity
  have hZ : ((2 * v) ^ (2 * r)) ^ (j + 1) ≠ 0 := by positivity
  generalize (g ^ (2 * r + 2) * T * (2 * v)) ^ (j + 1) = X at hX ⊢
  generalize ((2 * v) ^ (2 * r)) ^ (j + 1) = Z0 at hZ ⊢
  generalize ((2 * Real.pi) ^ (2 * r + 1)) ^ (j + 1) = Y
  generalize (T * T') ^ (j + 1) = Q
  generalize (2 * Real.pi) ^ ((2 * r + 1) * (2 * r + 1 + 1) / 2) = S
  field_simp
end Formalism.HermitianLatticeCounting.P
