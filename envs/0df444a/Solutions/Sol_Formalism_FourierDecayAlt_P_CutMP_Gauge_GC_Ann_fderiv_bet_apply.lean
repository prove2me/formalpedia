-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.fderiv_bet_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:37:30.586707+00:00
-- url     : https://prove2.me/submissions/f01de187-5d55-4d9d-944b-40411646e9fd

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FderivDecomp
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BasePointMemHalfPlane
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_hasFDerivAt_bet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Filter Topology Complex
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
noncomputable section
variable {TT : ℝ} {α : ℂ → ℂ}
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
theorem _root_.solution (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT)) {w : ℂ} (hw : w ∈ Hh TT) (v : ℂ) :
    fderiv ℝ (bet α) w v = (α (Complex.exp w) * Complex.exp w + wZ α (Complex.exp w) * Complex.exp w ^ 2) * v +
      wZb α (Complex.exp w) * Complex.exp w * (starRingEnd ℂ) (Complex.exp w) * (starRingEnd ℂ) v := by
  rw [(hasFDerivAt_bet hα hw).fderiv]
  unfold wZ wZb
  obtain ⟨L, hL⟩ : ∃ L, L = fderiv ℝ α (Complex.exp w) := ⟨_, rfl⟩
  rw [← hL]
  have hL' : ∀ u : ℂ, 2 * L u = (u + (starRingEnd ℂ) u) * L 1 + Complex.I * ((starRingEnd ℂ) u - u) * L Complex.I := by
    intro u
    have hre : L u = (u.re : ℂ) * L 1 + (u.im : ℂ) * L Complex.I := by
      have hu : u.re • (1 : ℂ) + u.im • Complex.I = u := by
        rw [Complex.real_smul, Complex.real_smul, mul_one, Complex.re_add_im]
      conv_lhs => rw [← hu]
      rw [map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
    have h1 := Complex.add_conj u
    have h2 := Complex.sub_conj u
    push_cast at h1 h2
    rw [hre]
    linear_combination (-(L 1)) * h1 + (Complex.I * L Complex.I) * h2 +
      (2 * (u.im : ℂ) * L Complex.I) * Complex.I_sq
  have key := hL' (Complex.exp w * v)
  have hcj : (starRingEnd ℂ) (Complex.exp w * v) = (starRingEnd ℂ) (Complex.exp w) * (starRingEnd ℂ) v :=
    map_mul (starRingEnd ℂ) _ _
  rw [hcj] at key
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply', smul_eq_mul]
  linear_combination (Complex.exp w / 2) * key
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
