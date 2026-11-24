-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.Xa_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:20:37.906266+00:00
-- url     : https://prove2.me/submissions/ca2e385c-9b77-4083-bf35-918c34ec8012

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliWordSumExpansion_conj_entry
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliWordSumExpansion_single_entry
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_hpart1_lie


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
theorem _root_.solution (a b : Fin (2 * r + k + 1)) : unitLie k r (Xa k r a b) := by
  refine ⟨Formalism.FourierDecayAlt.P.Qx2.hpart1_lie _, fun i j => ?_⟩
  simp only [Xa, hpart1, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, norm_mul]
  have h1 := single_entry (k := k) (r := r) a b i j
  have h2 := conj_entry (k := k) (r := r) a b i j
  have h3 := norm_sub_le ((Matrix.single a b (1 : ℂ) : Mat k r) i j)
    (((Hpk k r)⁻¹ * (Matrix.single a b (1 : ℂ))ᴴ * Hpk k r) i j)
  have hn : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [hn]
  linarith
end Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
