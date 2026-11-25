-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FourTermExpansion.two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:18:39.038748+00:00
-- url     : https://prove2.me/submissions/d3cf1fda-bc18-478d-b809-e621a09fbdfd

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourTermExpansion
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_FourTermExpansion_top_apply___a095e6ea583d
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_gl_single
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_EZ_top
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.P.FourTermExpansion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (M : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Mat k r)
end Formalism.FourierDecayAlt.P.FourTermExpansion
namespace Formalism.FourierDecayAlt.P.FourTermExpansion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
private theorem top_top_lemma_10 {Φ : Mat k r → E} {g : Mat k r} (hloc : Loc 2 Φ g) (hgG : g ∈ GV k r) (x y : ℂ)
    (a b c d : Fin (2 * r + k + 1)) :
    Top (LT (Msg k r)) x a b (Top (LT (Msg k r)) y c d Φ) g =
      (if a = b then x • ((if c = d then y • Φ g else 0) + EZ (Msg k r c d) Φ g) else 0) +
        ((if c = d then (1 : ℂ) else 0) • (y • EZ (Msg k r a b) Φ g) + EZ (Msg k r a b) (EZ (Msg k r c d) Φ) g) := by
  rw [top_apply'' (Msg k r), EZ_top hloc hgG, top_apply'' (Msg k r)]
end Formalism.FourierDecayAlt.P.FourTermExpansion
namespace Formalism.FourierDecayAlt.P.FourTermExpansion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
end Formalism.FourierDecayAlt.P.FourTermExpansion
namespace Formalism.FourierDecayAlt.P.FourTermExpansion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
end Formalism.FourierDecayAlt.P.FourTermExpansion
end
end

set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FourTermExpansion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.FourTermExpansion
theorem _root_.solution {Φ : Mat k r → E} {g : Mat k r} (hloc : Loc 2 Φ g) (hgG : g ∈ GV k r) (x y : ℂ) (hxy : x - y = 1)
    (p q c d : Fin (2 * r + k + 1)) :
    Top (LT (Msg k r)) x p c (Top (LT (Msg k r)) y q d Φ) g
      - Top (LT (Msg k r)) x q c (Top (LT (Msg k r)) y p d Φ) g
      + Top (LT (Msg k r)) x p d (Top (LT (Msg k r)) y q c Φ) g
      - Top (LT (Msg k r)) x q d (Top (LT (Msg k r)) y p c Φ) g = 0 := by
  rw [top_top_lemma_10 hloc hgG, top_top_lemma_10 hloc hgG, top_top_lemma_10 hloc hgG, top_top_lemma_10 hloc hgG]
  have g1 := gl_single hloc hgG p c q d
  have g2 := gl_single hloc hgG p d q c
  rw [sub_eq_iff_eq_add] at g1 g2
  rw [g1, g2]
  obtain rfl : x = y + 1 := by linear_combination hxy
  simp only [@eq_comm _ c q, @eq_comm _ d p, @eq_comm _ d q, @eq_comm _ c p]
  split_ifs <;> module
end Formalism.FourierDecayAlt.P.FourTermExpansion
