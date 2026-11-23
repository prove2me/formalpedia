-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ProductFactorBounds.prod_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:02:18.862333+00:00
-- url     : https://prove2.me/submissions/c6b20f24-bcb4-4e1b-86b9-64333c38712c

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ProductFactorBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ProductFactorBounds
open Formalism.FourierDecayAlt.F7
namespace Formalism.FourierDecayAlt.P.ProductFactorBounds
theorem _root_.solution (a b : ℝ) (ha1 : a ≤ 1) (hb : 0 ≤ b) (L : List ℝ)
    (h : ∀ f ∈ L, 1 - a ≤ f ∧ f ≤ 1 + b) :
    (1 - a) ^ L.length ≤ L.prod ∧ L.prod ≤ (1 + b) ^ L.length := by
  induction L with
  | nil => simp
  | cons f L ih =>
    have hf := h f (by simp)
    have hL := ih (fun g hg => h g (by simp [hg]))
    have h0 : 0 ≤ 1 - a := by linarith
    have h1 : 0 ≤ (1 - a) ^ L.length := pow_nonneg h0 _
    have h2 : 0 ≤ L.prod := le_trans h1 hL.1
    have h3 : 0 ≤ f := le_trans h0 hf.1
    simp only [List.length_cons, List.prod_cons, pow_succ']
    exact ⟨mul_le_mul hf.1 hL.1 h1 h3, mul_le_mul hf.2 hL.2 h2 (by linarith)⟩
end Formalism.FourierDecayAlt.P.ProductFactorBounds
