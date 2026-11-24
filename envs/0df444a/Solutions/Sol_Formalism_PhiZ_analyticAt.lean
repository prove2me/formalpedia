-- Prove2me | solution 1 for Formalism.PhiZ_analyticAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:11:13.348828+00:00
-- url     : https://prove2.me/submissions/e29c9e04-26ab-49c0-a48e-33501cccfe81

import Definitions.Def_Formalism_StatementU
import Definitions.Def_Formalism_ZetaNonvanishing_OfRealNeOfRealOfLt
import Definitions.Def_Formalism_ZetaNonvanishing_LandauEq
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSgen
import Definitions.Def_Formalism_ZetaNonvanishing_MellinElem
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_LogDerivZeroFree
import Definitions.Def_Formalism_ZetaNonvanishing_MellinDeriv
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaLandau
import Theorems.Thm_Formalism_differentiable_AZ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Formalism
open ArithmeticFunction
namespace Formalism
theorem _root_.solution (ε C θ : ℝ) {s : ℂ} (hs0 : s ≠ 0)
    (hE : riemannZeta₁ s ≠ 0) (hsθ : s ≠ θ) : AnalyticAt ℂ (PhiZ ε C θ) s := by
  set V : Set ℂ := {z | z ≠ 0 ∧ riemannZeta₁ z ≠ 0 ∧ z ≠ θ} with hV
  have hEd : Differentiable ℂ riemannZeta₁ := differentiable_riemannZeta₁
  have hVo : IsOpen V :=
    isOpen_ne.inter ((isOpen_ne_fun hEd.continuous continuous_const).inter isOpen_ne)
  have hdsl : DifferentiableOn ℂ (dslope AZ 1) univ :=
    (differentiableOn_dslope Filter.univ_mem).mpr differentiable_AZ.differentiableOn
  have hd : DifferentiableOn ℂ (PhiZ ε C θ) V := by
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    have h1 : DifferentiableAt ℂ (dslope AZ 1) z :=
      (hdsl z (mem_univ z)).differentiableAt Filter.univ_mem
    have h2 : DifferentiableAt ℂ riemannZeta₁ z := hEd z
    unfold PhiZ
    apply DifferentiableAt.add
    · exact (h1.const_mul _).div (differentiableAt_id.mul h2) (mul_ne_zero hz.1 hz.2.1)
    · exact (differentiableAt_const _).div (differentiableAt_id.sub_const _)
        (sub_ne_zero.mpr hz.2.2)
  exact hd.analyticAt (hVo.mem_nhds ⟨hs0, hE, hsθ⟩)
end Formalism
