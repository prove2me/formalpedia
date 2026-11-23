-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x2.pSDEntryBound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:05:42.669802+00:00
-- url     : https://prove2.me/submissions/11510fe7-4c36-4597-b4b6-b0bad20dda9c

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PosSemidefEntryBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x2_gramRealiseCut

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x2
namespace Formalism.FourierDecayAlt.P.A6x2
theorem _root_.solution : PSDEntryBound := by
  intro X F k M h1 h2 x hx y hy
  obtain ⟨n, u, T, hT, hG, hGc⟩ := gramRealiseCut X F M k h1 h2
  have hn : ∀ z ∈ F, ‖u z‖ ^ 2 = (M z z).re := by
    intro z hz
    rw [← hG z hz z hz]
    exact (inner_self_eq_norm_sq (𝕜 := ℂ) (u z)).symm
  rw [← hGc x hx y hy, ← hn x hx, ← hn y hy, ← mul_pow]
  have h3 : ‖inner ℂ (T (u y)) (T (u x))‖ ≤ ‖u x‖ * ‖u y‖ :=
    calc ‖inner ℂ (T (u y)) (T (u x))‖ ≤ ‖T (u y)‖ * ‖T (u x)‖ := norm_inner_le_norm _ _
      _ ≤ ‖u y‖ * ‖u x‖ := mul_le_mul (hT _) (hT _) (norm_nonneg _) (norm_nonneg _)
      _ = ‖u x‖ * ‖u y‖ := mul_comm _ _
  exact pow_le_pow_left₀ (norm_nonneg _) h3 2
end Formalism.FourierDecayAlt.P.A6x2
