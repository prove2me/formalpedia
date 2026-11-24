-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.sn_wC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:21:27.197412+00:00
-- url     : https://prove2.me/submissions/1d140424-348a-400a-8992-68e8f17384df

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_coordinate_shift_product
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sn_qeval
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_coordinate_shift_split

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Polynomial
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NFx2
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.NF
noncomputable section
namespace Formalism.FourierDecayAlt.P.NFx2
theorem _root_.solution {P : M.Par} (hWE : M.WExact) (hP : P.OK) (τ : M.Ty P) {Y : ℂ} (hY1 : M.xC P τ (Y + 1) ≠ 0) :
    M.wC P τ Y = M.qC P Y / M.xC P τ (Y + 1) +
      ∑ j ∈ Icc 1 (P.k - 1), M.xEx P {j} τ Y / (Y + M.rho P τ j + 1) * ((M.Nrm P j τ : ℝ) : ℂ) := by
  have hx1 : (M.coordinatePolynomial P τ).eval Y = M.xC P τ (Y + 1) := by
    rw [coordinate_shift_product]; simp only [M.coordinatePolynomial, eval_prod, eval_add, eval_X, eval_C]
    exact Finset.prod_congr rfl fun i _ => by ring
  have hw := congrArg (Polynomial.eval Y) (hWE P hP τ)
  rw [eval_mul, hx1] at hw
  have hwc : M.wC P τ Y = (M.wNum P τ).eval Y / M.xC P τ (Y + 1) := by
    rw [hw, M.wC]; field_simp
  rw [hwc]
  simp only [M.wNum, eval_add, eval_finsetSum, eval_mul, eval_C, eval_prod, eval_X, sn_qeval]
  rw [add_div, Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hsplit := coordinate_shift_split hj τ Y
  have hne := hY1
  rw [hsplit] at hne
  have hB := right_ne_zero_of_mul hne
  have ha := left_ne_zero_of_mul hne
  have e1 : ∏ i ∈ (Icc 1 (P.k - 1)).erase j, (Y + ((M.rho P τ i : ℂ) + 1)) =
      ∏ i ∈ Icc 1 (P.k - 1) \ {j}, (Y + (1 + (M.rho P τ i : ℂ))) := by
    rw [Finset.sdiff_singleton_eq_erase]; exact Finset.prod_congr rfl fun i _ => by ring
  have e2 : ∏ i ∈ (Icc 1 (P.k - 1)).erase j, (Y + (M.rho P τ i : ℂ)) = M.xEx P {j} τ Y := by
    unfold M.xEx; rw [Finset.sdiff_singleton_eq_erase]
  rw [hsplit, e1, e2]
  field_simp
end Formalism.FourierDecayAlt.P.NFx2
