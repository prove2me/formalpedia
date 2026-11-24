-- Prove2me | solution 1 for Formalism.HC.Landau.PhiP_analyticAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:22.020178+00:00
-- url     : https://prove2.me/submissions/8fadd574-1c0c-4fd2-b9ee-47091aad2803

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaLandau
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_Landau
import Theorems.Thm_Formalism_HC_Landau_differentiable_AP

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
open Formalism Formalism.HC Formalism.HC.Landau
open Formalism ArithmeticFunction
namespace Formalism.HC.Landau
theorem _root_.solution {P : ℂ → ℂ} (hP : Differentiable ℂ P) (a b : ℂ) (C θ : ℝ) {s : ℂ} (hs0 : s ≠ 0)
    (hE : P s ≠ 0) (hsθ : s ≠ θ) : AnalyticAt ℂ (PhiP P a b C θ) s := by
  set V : Set ℂ := {z | z ≠ 0 ∧ P z ≠ 0 ∧ z ≠ θ} with hV
  have hVo : IsOpen V :=
    isOpen_ne.inter ((isOpen_ne_fun hP.continuous continuous_const).inter isOpen_ne)
  have hdsl : DifferentiableOn ℂ (dslope (AP P a b) 1) univ :=
    (differentiableOn_dslope Filter.univ_mem).mpr (differentiable_AP hP a b).differentiableOn
  have hd : DifferentiableOn ℂ (PhiP P a b C θ) V := by
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    have h1 : DifferentiableAt ℂ (dslope (AP P a b) 1) z :=
      (hdsl z (mem_univ z)).differentiableAt Filter.univ_mem
    have h2 : DifferentiableAt ℂ P z := hP z
    unfold PhiP
    apply DifferentiableAt.add
    · exact h1.div (differentiableAt_id.mul h2) (mul_ne_zero hz.1 hz.2.1)
    · exact (differentiableAt_const _).div (differentiableAt_id.sub_const _)
        (sub_ne_zero.mpr hz.2.2)
  exact hd.analyticAt (hVo.mem_nhds ⟨hs0, hE, hsθ⟩)
end Formalism.HC.Landau
