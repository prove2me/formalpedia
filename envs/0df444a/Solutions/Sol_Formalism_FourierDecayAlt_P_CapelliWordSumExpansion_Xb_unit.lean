-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.Xb_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:20:38.906302+00:00
-- url     : https://prove2.me/submissions/02ef5b88-c86a-49a0-a0c8-f442e2c0a21e

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliWordSumExpansion_conj_entry
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliWordSumExpansion_single_entry
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_hpart2_lie


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
theorem _root_.solution (a b : Fin (2 * r + k + 1)) : unitLie k r (Xb k r a b) := by
  refine ⟨Formalism.FourierDecayAlt.P.Qx2.hpart2_lie _, fun i j => ?_⟩
  have h1 := single_entry (k := k) (r := r) a b i j
  have h2 := conj_entry (k := k) (r := r) a b i j
  have h3 := norm_add_le ((Matrix.single a b (1 : ℂ) : Mat k r) i j)
    (((Hpk k r)⁻¹ * (Matrix.single a b (1 : ℂ))ᴴ * Hpk k r) i j)
  have h4 := norm_sub_le ((Matrix.single a b (1 : ℂ) : Mat k r) i j)
    (((Hpk k r)⁻¹ * (Matrix.single a b (1 : ℂ))ᴴ * Hpk k r) i j)
  simp only [Xb, hpart2, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, smul_eq_mul, norm_mul]
  norm_num at h1 h2 h3 h4 ⊢
  linarith
end Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
