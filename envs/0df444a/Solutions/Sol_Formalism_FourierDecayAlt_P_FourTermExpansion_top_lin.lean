-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FourTermExpansion.top_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:03:41.506816+00:00
-- url     : https://prove2.me/submissions/34a3455d-6bfd-4287-abc4-10703331e320

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourTermExpansion
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_EZ_lin
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_FourTermExpansion_top_apply___a095e6ea583d

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FourTermExpansion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (M : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Mat k r)
namespace Formalism.FourierDecayAlt.P.FourTermExpansion
theorem _root_.solution {Φ₁ Φ₂ : Mat k r → E} {g : Mat k r} (h₁ : Loc 1 Φ₁ g) (h₂ : Loc 1 Φ₂ g) (hgG : g ∈ GV k r)
    (c : ℂ) (v : ℂ) (a b : Fin (2 * r + k + 1)) :
    Top (LT M) v a b (fun x => Φ₁ x + c • Φ₂ x) g = Top (LT M) v a b Φ₁ g + c • Top (LT M) v a b Φ₂ g := by
  rw [top_apply'' M, top_apply'' M, top_apply'' M, EZ_lin h₁ h₂ hgG]
  split_ifs <;> module
end Formalism.FourierDecayAlt.P.FourTermExpansion
