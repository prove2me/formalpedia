-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PolynomialTheoremsAssembly.lower_block_lift_bound_reduction
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:39:05.70648+00:00
-- url     : https://prove2.me/submissions/15667b20-b317-45be-bb9d-dced16f2ed31

import Definitions.Def_Formalism_HermitianCurvature_LowerBlockNormalisedBoundFromComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondPolynomialClauses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PolynomialTheoremsAssembly

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
theorem _root_.solution : LowerBlockLiftBoundFromComponents := by
  intro hA hU hC V _ _ R x ex K d grid q nn w e t t' W RL RV bw Qw BB hR hbw ht ht' he hg hpos hQ hB hBB
    hRL hD hS
  have hb := hU K d grid q w e (1 / t - 1 / t') (R (x t) (x t')) W RL RV he
    (fun j => Finset.prod_pos fun a _ => (hpos a (j a)).2.1) hRL hD hS
  have hc := hC K d grid q nn w (1 / t - 1 / t') (R (x t) (x t')) RL RV (‖t‖ ^ ex) (‖t'‖ ^ ex) bw Qw BB
    hg hpos hQ hB hBB (by positivity) (by positivity) hbw hRL hb
  have hN : ‖Npair R x (fun u => ‖u‖ ^ ex) bw t t'‖ = ‖t‖ ^ ex * ‖t'‖ ^ ex / bw * ‖R (x t) (x t')‖ := by
    unfold Npair
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (by positivity) hbw.le)]
  refine ⟨hA V R x (fun u => ‖u‖ ^ ex) bw hR hbw (fun u => by positivity) t t', hb, ?_⟩
  rw [hN]
  simp only [pow_mul']
  exact hc
end Formalism.FourierDecayAlt.P.PolynomialTheoremsAssembly
