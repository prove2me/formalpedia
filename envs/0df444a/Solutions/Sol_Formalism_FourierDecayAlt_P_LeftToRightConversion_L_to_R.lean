-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LeftToRightConversion.L_to_R
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:08:35.555069+00:00
-- url     : https://prove2.me/submissions/057148ac-c79c-474a-949a-ad1b745b63e1

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ListSumSplittings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeftToRightConversion
import Theorems.Thm_Formalism_FourierDecayAlt_P_LeftToRightConversion_inv_eq_iota
import Theorems.Thm_Formalism_FourierDecayAlt_P_LeftToRightConversion_cv_LR
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_inLie_conj
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_inLie_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumInequalities_op_expand


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LeftToRightConversion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10 Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic
  Formalism.FourierDecayAlt.P.ListSumInequalities Formalism.FourierDecayAlt.P.ListSumSplittings
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.LeftToRightConversion
theorem _root_.solution {H : Mat k r → E} {X g : Mat k r} (hX : inLie k r X) (hH : CkOn ((1 : ℕ) : ℕ∞) (GV k r) H)
    (hg : g ∈ GV k r) : op true X H g = ∑ i, cT i X g • op false (Lt i) H g := by
  have hY : inLie k r (-(g⁻¹ * X * g)) := inLie_neg (inLie_conj hg hX)
  have e1 : op true X H g = op false (-(g⁻¹ * X * g)) H g := by
    unfold op; congr 1; funext t; rw [cv_LR hg t]
  rw [e1, op_expand false hY hH hg, inv_eq_iota hg]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact RCLike.real_smul_eq_coe_smul (K := ℂ) _ _
end Formalism.FourierDecayAlt.P.LeftToRightConversion
