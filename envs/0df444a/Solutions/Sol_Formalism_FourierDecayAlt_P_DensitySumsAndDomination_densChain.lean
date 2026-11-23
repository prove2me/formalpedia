-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DensitySumsAndDomination.densChain
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:07:44.968398+00:00
-- url     : https://prove2.me/submissions/67538b60-7511-4ff1-9388-97436ebeda9b

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DensitySumsAndDomination

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TC
open scoped ComplexInnerProductSpace ComplexOrder ComplexConjugate
noncomputable section
open Classical
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DensitySumsAndDomination
namespace Formalism.FourierDecayAlt.P.DensitySumsAndDomination
theorem _root_.solution : DensChain := by
  intro hSum hLe hSize P q l k r f sd hk hl hfib hsd
  have hn : 2 ≤ k - 2 * r - 2 := by omega
  have hB : ∀ S : Finset P, ∏ p ∈ S, Real.exp (4 * (q p ^ (k - 2 * r - 2))⁻¹) ≤
      Real.exp (12 * (f : ℝ) * ((2 : ℝ) ^ (k - 2 * r - 2))⁻¹) := by
    intro S
    have h1 := hSum P S q l f (k - 2 * r - 2) hn (fun p _ => hl p)
      (fun m => hfib m _ (fun p hp => (Finset.mem_filter.mp hp).2))
    rw [← Real.exp_sum, Real.exp_le_exp, ← Finset.mul_sum]
    linarith
  have hmain : sd ≤ Real.exp (12 * (f : ℝ) * ((2 : ℝ) ^ (k - 2 * r - 2))⁻¹) := by
    by_contra hc
    push_neg at hc
    obtain ⟨x, hx1, hx2⟩ := exists_between hc
    obtain ⟨S, hS⟩ := hsd x hx2
    linarith [hB S]
  exact ⟨hmain, hmain.trans (hLe f _ (hSize k r f hk))⟩
end Formalism.FourierDecayAlt.P.DensitySumsAndDomination
