-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SecondPolynomialClauses.cg_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:33:12.106802+00:00
-- url     : https://prove2.me/submissions/ece84ac3-d897-43bf-9775-073092d75fc7

import Definitions.Def_Formalism_HermitianCurvature_LowerBlockNormalisedBoundFromComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondPolynomialClauses
import Theorems.Thm_Formalism_FourierDecayAlt_P_SecondPolynomialClauses_lagCo_ne_zero

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SecondPolynomialClauses
open Formalism.FourierDecayAlt.PairingProductCorollary
namespace Formalism.FourierDecayAlt.P.SecondPolynomialClauses
theorem _root_.solution {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (hg : ∀ a, Function.Injective (grid a)) (a : Fin K) :
    0 < cg grid a := by
  unfold cg
  exact Finset.sum_pos' (fun i _ => abs_nonneg _)
    ⟨0, Finset.mem_univ _, abs_pos.mpr (lagCo_ne_zero (grid a) (hg a) 0)⟩
end Formalism.FourierDecayAlt.P.SecondPolynomialClauses
