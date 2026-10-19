-- Prove2me | solution 1 for CauchyRiemannIndex.complexLoop_homotopic_const_of_argLift
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-16T17:20:31.639687+00:00
-- url     : https://prove2.me/submissions/44d8fda7-722e-4584-98fb-81c609560e90

import Definitions.Def_CauchyRiemannIndex_Setting

open Matrix

namespace CRLK2

/-- Complex logarithm-type coordinate `log |v t| + i θ t`. -/
noncomputable def logCoord (v : C(unitInterval, ℂ)) (θ : unitInterval → ℝ) (t : unitInterval) : ℂ :=
  (Real.log ‖v t‖ : ℂ) + (θ t : ℂ) * Complex.I

lemma exp_logCoord (v : C(unitInterval, ℂ)) (hv : ∀ t, v t ≠ 0) (θ : unitInterval → ℝ)
    (hθ : CauchyRiemannIndex.IsArgLift (fun t => v t / (‖v t‖ : ℂ)) θ) (t : unitInterval) :
    Complex.exp (logCoord v θ t) = v t := by
  have hn : (‖v t‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr (hv t)
  unfold logCoord
  rw [Complex.exp_add, ← hθ.2 t, ← Complex.ofReal_exp, Real.exp_log (norm_pos_iff.mpr (hv t))]
  field_simp

lemma continuous_logCoord (v : C(unitInterval, ℂ)) (hv : ∀ t, v t ≠ 0) (θ : unitInterval → ℝ)
    (hθ : Continuous θ) : Continuous (logCoord v θ) := by
  unfold logCoord
  have hl : Continuous fun t => Real.log ‖v t‖ :=
    (continuous_norm.comp v.continuous).log (fun t => norm_ne_zero_iff.mpr (hv t))
  fun_prop

theorem main (v : C(unitInterval, ℂ)) (hv : ∀ t, v t ≠ 0)
    (h1 : v 1 = v 0) (θ : unitInterval → ℝ)
    (hθ : CauchyRiemannIndex.IsArgLift (fun t => v t / (‖v t‖ : ℂ)) θ) (hθ1 : θ 1 = θ 0) :
    ∃ H : C(unitInterval × unitInterval, ℂ), (∀ t, H (0, t) = v t) ∧ (∀ t, H (1, t) = v 0) ∧
      (∀ p, H p ≠ 0) ∧ (∀ s, H (s, 0) = v 0) ∧ ∀ s, H (s, 1) = v 0 := by
  have hL := continuous_logCoord v hv θ hθ.1
  have hL1 : logCoord v θ 1 = logCoord v θ 0 := by unfold logCoord; rw [h1, hθ1]
  refine ⟨⟨fun p => Complex.exp ((1 - ((p.1 : ℝ) : ℂ)) * logCoord v θ p.2 +
      ((p.1 : ℝ) : ℂ) * logCoord v θ 0), by fun_prop⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    simp only [ContinuousMap.coe_mk, Set.Icc.coe_zero, Complex.ofReal_zero, sub_zero, one_mul,
      zero_mul, add_zero]
    exact exp_logCoord v hv θ hθ t
  · intro t
    simp only [ContinuousMap.coe_mk, Set.Icc.coe_one, Complex.ofReal_one, sub_self, zero_mul,
      one_mul, zero_add]
    exact exp_logCoord v hv θ hθ 0
  · intro p; exact Complex.exp_ne_zero _
  · intro s
    simp only [ContinuousMap.coe_mk]
    rw [← exp_logCoord v hv θ hθ 0]; congr 1; ring
  · intro s
    simp only [ContinuousMap.coe_mk]
    rw [hL1, ← exp_logCoord v hv θ hθ 0]; congr 1; ring

end CRLK2

open CauchyRiemannIndex

open Matrix

theorem solution (v : C(unitInterval, ℂ)) (hv : ∀ t, v t ≠ 0)
    (h1 : v 1 = v 0) (θ : unitInterval → ℝ)
    (hθ : IsArgLift (fun t => v t / (‖v t‖ : ℂ)) θ) (hθ1 : θ 1 = θ 0) :
    ∃ H : C(unitInterval × unitInterval, ℂ), (∀ t, H (0, t) = v t) ∧ (∀ t, H (1, t) = v 0) ∧
      (∀ p, H p ≠ 0) ∧ (∀ s, H (s, 0) = v 0) ∧ ∀ s, H (s, 1) = v 0 :=
  CRLK2.main v hv h1 θ hθ hθ1
