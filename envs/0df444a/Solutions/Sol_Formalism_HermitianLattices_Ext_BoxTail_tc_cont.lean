-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.BoxTail.tc_cont
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:50.821919+00:00
-- url     : https://prove2.me/submissions/430fcdda-0e00-4684-84e4-bd3e4ebd31d6

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TailKernel
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_PerronHorizontalSegmentBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TailContourB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.BoxTail
namespace Formalism.HermitianLattices.Ext.BoxTail
theorem _root_.solution {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (y σ u : ℝ) (hy : 0 < y)
    (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hL : DirichletCharacter.LFunction χ ((σ : ℂ) + (u : ℂ) * I) ≠ 0) :
    ContinuousAt (fun v : ℝ => Formalism.ZeroFreeDirichlet.Fchi χ y ((σ : ℂ) + (v : ℂ) * I)) u := by
  have hd : Differentiable ℂ (DirichletCharacter.LFunction χ) :=
    DirichletCharacter.differentiable_LFunction hχ
  have hline : Continuous (fun v : ℝ => (σ : ℂ) + (v : ℂ) * I) := by fun_prop
  have hs0 : ((σ : ℂ) + (u : ℂ) * I) ≠ 0 := by
    intro h0
    have h1 := congrArg Complex.re h0
    simp at h1
    linarith
  have hs1 : ((σ : ℂ) + (u : ℂ) * I) - 1 ≠ 0 := by
    intro h0
    have h1 := congrArg Complex.re h0
    simp at h1
    linarith
  have hG : ContinuousAt (fun s : ℂ => Formalism.ZeroFreeDirichlet.Fchi χ y s) ((σ : ℂ) + (u : ℂ) * I) := by
    unfold Formalism.ZeroFreeDirichlet.Fchi Formalism.ZeroFreeDirichlet.negLD
    have hLc : ContinuousAt (DirichletCharacter.LFunction χ) ((σ : ℂ) + (u : ℂ) * I) :=
      hd.continuous.continuousAt
    have hdL : ContinuousAt (deriv (DirichletCharacter.LFunction χ)) ((σ : ℂ) + (u : ℂ) * I) :=
      (hd.analyticAt _).deriv.continuousAt
    have hcp : ContinuousAt (fun s : ℂ => (y : ℂ) ^ s) ((σ : ℂ) + (u : ℂ) * I) :=
      continuousAt_const_cpow (Complex.ofReal_ne_zero.2 hy.ne')
    apply ContinuousAt.div
    · exact ((hdL.div hLc hL).neg).mul hcp
    · fun_prop
    · exact mul_ne_zero hs0 hs1
  exact ContinuousAt.comp (g := fun s : ℂ => Formalism.ZeroFreeDirichlet.Fchi χ y s) hG hline.continuousAt
end Formalism.HermitianLattices.Ext.BoxTail
