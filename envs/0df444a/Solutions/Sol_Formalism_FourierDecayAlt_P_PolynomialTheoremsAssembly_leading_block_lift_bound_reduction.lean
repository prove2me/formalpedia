-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PolynomialTheoremsAssembly.leading_block_lift_bound_reduction
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:42:01.472805+00:00
-- url     : https://prove2.me/submissions/811d03d0-d756-4d83-a44c-8fa9a0d57c14

import Definitions.Def_Formalism_HermitianCurvature_LowerBlockNormalisedBoundFromComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondPolynomialClauses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PolynomialTheoremsAssembly
import Theorems.Thm_Formalism_FourierDecayAlt_P_PolynomialTheoremsAssembly_thGrid_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_PolynomialTheoremsAssembly_lamPSq_ge
import Theorems.Thm_Formalism_FourierDecayAlt_P_PolynomialTheoremsAssembly_lamPSq_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PolynomialTheoremsAssembly
open Formalism.FourierDecayAlt.PairingProductCorollary
namespace Formalism.FourierDecayAlt.P.PolynomialTheoremsAssembly
theorem _root_.solution : LeadingBlockLiftBoundFromComponents := by
  intro hA hB V _ _ ex K d grid q x nn w e t t' Ntt X0 XK ρ E bw Rw ZZ hg he ht ht' hpos hTop hFS hR hZ
    hRw hZZ hbw hG
  have ha := hA V K d grid q x nn w e t (X0 t) XK ρ E (‖t‖ ^ ex) bw Rw ZZ hg he ht hpos hTop hFS hR hZ
    (by positivity) hbw
  have hpw : (‖t‖ ^ ex) ^ 2 = ‖t‖ ^ (2 * ex) := by rw [← pow_mul, mul_comm]
  rw [hpw] at ha
  refine ⟨ha, fun ho hle => ?_⟩
  have hE0 : ∀ j, 0 ≤ E j := fun j =>
    le_trans (mul_nonneg (Finset.prod_pos fun b _ => hFS.1 b j).le (sq_nonneg _)) (hFS.2.2 j)
  have hn0 : ∀ j, 0 < nnProd nn 0 grid j := fun j =>
    Finset.prod_pos fun b _ => by simpa using (hpos b (j b)).2.1
  have hS : 0 ≤ ∑ j, F7.thGrid grid j * (‖t‖ ^ (2 * ex) * E j / (bw * nnProd nn 0 grid j)) :=
    Finset.sum_nonneg fun j _ => mul_nonneg (thGrid_nonneg grid j)
      (div_nonneg (mul_nonneg (by positivity) (hE0 j)) (mul_pos hbw (hn0 j)).le)
  refine hB K t t' Ntt (‖t‖ ^ (2 * ex) * ‖X0 t‖ ^ 2 / bw) (‖t'‖ ^ (2 * ex) * ‖X0 t'‖ ^ 2 / bw)
    (∑ j, F7.thGrid grid j * (‖t‖ ^ (2 * ex) * E j / (bw * nnProd nn 0 grid j)))
    (Real.sqrt (lamPSq grid Rw ZZ)) (fun a => cg grid a ^ 2 * Rw * ZZ) ht ht' ho hle
    (div_nonneg (by positivity) hbw.le) (div_nonneg (by positivity) hbw.le) hS (Real.sqrt_nonneg _)
    (fun a => ⟨by positivity, ?_⟩) hG ha
  rw [Real.sq_sqrt (lamPSq_nonneg grid Rw ZZ)]
  exact lamPSq_ge grid Rw ZZ a
end Formalism.FourierDecayAlt.P.PolynomialTheoremsAssembly
