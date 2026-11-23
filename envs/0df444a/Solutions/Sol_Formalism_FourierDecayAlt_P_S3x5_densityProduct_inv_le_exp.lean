-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x5.densityProduct_inv_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:01:14.443799+00:00
-- url     : https://prove2.me/submissions/1868510e-72e5-4aab-bebb-5af87db8ae32

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFrameCount
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_qpow_le_half
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_factor_bounds
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_factor_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_inv_one_sub_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x5
open Finset Formalism.FourierDecayAlt.S3
namespace Formalism.FourierDecayAlt.P.S3x5
theorem _root_.solution (η : ℤ) (hη : η = 1 ∨ η = -1) (q : ℕ) (hq : 2 ≤ q) (lo hi : ℤ) (hlo : 1 ≤ lo) :
    (densP η q lo hi)⁻¹ ≤ Real.exp (∑ i ∈ Finset.Icc lo hi, 2 * (q : ℝ) ^ (-i)) := by
  unfold densP
  rw [Real.exp_sum, ← Finset.prod_inv_distrib]
  apply Finset.prod_le_prod
  · intro i hi'
    exact (inv_pos.2 (factor_pos η hη q hq i (by have := (Finset.mem_Icc.1 hi').1; omega))).le
  · intro i hi'
    have hi1 : 1 ≤ i := by have := (Finset.mem_Icc.1 hi').1; omega
    have h1 := (factor_bounds η hη q hq i hi1).1
    have h2 := qpow_le_half q hq i hi1
    have hpos : 0 < (q : ℝ) ^ (-i) := zpow_pos (by exact_mod_cast (by omega : 0 < q)) _
    have h3 := inv_one_sub_le _ hpos.le h2
    have h4 : (1 - (η : ℝ) ^ i * (q : ℝ) ^ (-i))⁻¹ ≤ (1 - (q : ℝ) ^ (-i))⁻¹ :=
      inv_anti₀ (by linarith) h1
    linarith
end Formalism.FourierDecayAlt.P.S3x5
