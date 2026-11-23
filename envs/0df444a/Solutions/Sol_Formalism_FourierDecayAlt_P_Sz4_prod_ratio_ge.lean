-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz4.prod_ratio_ge
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:39:41.141751+00:00
-- url     : https://prove2.me/submissions/6a07d5ef-a0b1-473c-b44e-2447b636f6e8

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz4
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz4
theorem _root_.solution (s : Finset ℕ) (f g : ℕ → ℝ) (B : ℝ) (hg : ∀ i ∈ s, 0 < g i)
    (hf : ∀ i ∈ s, 0 < f i) (h : ∏ i ∈ s, g i / f i ≤ Real.exp B) :
    Real.exp (-B) ≤ ∏ i ∈ s, f i / g i := by
  have e : ∏ i ∈ s, f i / g i = (∏ i ∈ s, g i / f i)⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun i _ => (inv_div _ _).symm
  rw [e, Real.exp_neg]
  exact inv_anti₀ (Finset.prod_pos fun i hi => div_pos (hg i hi) (hf i hi)) h
end Formalism.FourierDecayAlt.P.Sz4
