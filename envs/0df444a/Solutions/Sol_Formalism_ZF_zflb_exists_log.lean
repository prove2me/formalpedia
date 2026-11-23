-- Prove2me | solution 1 for Formalism.ZF.zflb_exists_log
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:37:22.002876+00:00
-- url     : https://prove2.me/submissions/c3ef0b26-29ac-47df-bb82-dce72772bf5a

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_LogDerivBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Metric
noncomputable section
open Formalism Formalism.ZF
namespace Formalism.ZF
theorem _root_.solution {f : ℂ → ℂ} {z₀ : ℂ} {R : ℝ}
    (hf : DifferentiableOn ℂ f (ball z₀ R)) (hne : ∀ z ∈ ball z₀ R, f z ≠ 0) :
    ∃ g : ℂ → ℂ, g z₀ = 0 ∧ (∀ z ∈ ball z₀ R, HasDerivAt g (deriv f z / f z) z) ∧
      ∀ z ∈ ball z₀ R, f z = f z₀ * Complex.exp (g z) := by
  have hopen : IsOpen (ball z₀ R) := isOpen_ball
  have hd : DifferentiableOn ℂ (fun z => deriv f z / f z) (ball z₀ R) :=
    (hf.deriv hopen).div hf hne
  obtain ⟨G, hG⟩ := hd.isExactOn_ball
  refine ⟨fun z => G z - G z₀, by simp, fun z hz => (hG z hz).sub_const _, ?_⟩
  have hk : ∀ z ∈ ball z₀ R, HasDerivAt (fun w => f w * Complex.exp (-(G w - G z₀))) 0 z := by
    intro z hz
    have hfz : HasDerivAt f (deriv f z) z := (hf.differentiableAt (hopen.mem_nhds hz)).hasDerivAt
    have hgz : HasDerivAt (fun w => -(G w - G z₀)) (-(deriv f z / f z)) z := ((hG z hz).sub_const _).neg
    have h : HasDerivAt (fun w => f w * Complex.exp (-(G w - G z₀)))
        (deriv f z * Complex.exp (-(G z - G z₀)) +
          f z * (Complex.exp (-(G z - G z₀)) * -(deriv f z / f z))) z :=
      hfz.mul hgz.cexp
    have h0 : deriv f z * Complex.exp (-(G z - G z₀)) +
        f z * (Complex.exp (-(G z - G z₀)) * -(deriv f z / f z)) = 0 := by
      have h1 := hne z hz
      field_simp
      all_goals ring
    exact h0 ▸ h
  intro z hz
  have hz₀ : z₀ ∈ ball z₀ R := mem_ball_self (pos_of_mem_ball hz)
  have hconst := hopen.is_const_of_deriv_eq_zero (convex_ball z₀ R).isPreconnected
    (fun w hw => (hk w hw).differentiableAt.differentiableWithinAt) (fun w hw => (hk w hw).deriv) hz hz₀
  simp only [sub_self, neg_zero, Complex.exp_zero, mul_one] at hconst
  rw [← hconst, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
end Formalism.ZF
