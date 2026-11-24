-- Prove2me | solution 1 for Formalism.L2.Th1.H.iteratedDeriv_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:27:27.741881+00:00
-- url     : https://prove2.me/submissions/75459fdc-c42f-4c4f-8373-3655ea7095f7

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_TaylorMvLinear
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_IteratedDerivLine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
namespace Formalism.L2.Th1.H
theorem _root_.solution {n : Type*} [Fintype n] (F : (n → ℂ) → ℂ) (hF : AnalyticAt ℂ F 0) (v : n → ℂ)
    (k : ℕ) : iteratedDeriv k (fun t : ℂ => F (t • v)) 0 = iteratedFDeriv ℂ k F 0 fun _ => v := by
  let g : ℂ →L[ℂ] (n → ℂ) := ContinuousLinearMap.toSpanSingleton ℂ v
  let s : Set (n → ℂ) := {x | AnalyticAt ℂ F x}
  have hs : IsOpen s := isOpen_analyticAt ℂ F
  have hgs : IsOpen (g ⁻¹' s) := hs.preimage g.continuous
  have h0 : g 0 ∈ s := by simpa [s] using hF
  have hc : ContDiffOn ℂ (k : ℕ∞) F s :=
    AnalyticOnNhd.contDiffOn (fun x hx => hx) hs.uniqueDiffOn
  have := g.iteratedFDerivWithin_comp_right hc hs.uniqueDiffOn hgs.uniqueDiffOn h0 (i := k) le_rfl
  rw [iteratedFDerivWithin_of_isOpen k hgs h0, iteratedFDerivWithin_of_isOpen k hs h0] at this
  have hfg : (fun t : ℂ => F (t • v)) = F ∘ g := by
    ext t; simp [g]
  rw [iteratedDeriv_eq_iteratedFDeriv, hfg, this]
  simp [g]
end Formalism.L2.Th1.H
