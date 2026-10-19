-- Prove2me | solution 1 for CauchyRiemannIndex.arg_add_one_sub_eq
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-17T16:38:08.87987+00:00
-- url     : https://prove2.me/submissions/2afdcb8c-d97f-4f7a-9695-4949b95f8973

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Order.Field



/-!
# The increment of a continuous argument of a periodic loop
-/

namespace CauchyRiemannIndex

/-- If `θ` is a continuous argument of a nowhere-vanishing `1`-periodic loop `β`
(`β = |β| e^{iθ}`) and `θ(1) - θ(0) = 2πw`, then `θ(t + 1) - θ(t) = 2πw` for every `t`. -/
theorem arg_add_one_sub_eq (β : ℝ → ℂ) (hper : Function.Periodic β 1) (hnz : ∀ t, β t ≠ 0)
    (θ : ℝ → ℝ) (hθ : Continuous θ)
    (harg : ∀ t, β t = ‖β t‖ * Complex.exp (θ t * Complex.I))
    (w : ℤ) (hw : θ 1 - θ 0 = 2 * Real.pi * w) (t : ℝ) :
    θ (t + 1) - θ t = 2 * Real.pi * w := by
  have hint : ∀ s, ∃ n : ℤ, θ (s + 1) - θ s = 2 * Real.pi * n := by
    intro s
    have h1 := harg (s + 1)
    rw [hper s] at h1
    have h2 := harg s
    have hn : (‖β s‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 (hnz s)
    have he : Complex.exp (θ (s + 1) * Complex.I) = Complex.exp (θ s * Complex.I) := by
      have := h1.symm.trans h2
      exact mul_left_cancel₀ hn this
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 he
    refine ⟨n, ?_⟩
    have := congrArg Complex.im hn
    simp at this
    linarith
  let f : ℝ → ℝ := fun s => θ (s + 1) - θ s
  have hf : Continuous f := (hθ.comp (continuous_add_right 1)).sub hθ
  have hf0 : f 0 = 2 * Real.pi * w := by simpa [f] using hw
  obtain ⟨n, hn⟩ := hint t
  by_contra hne
  have hnw : n ≠ w := by
    rintro rfl; exact hne hn
  have hpi : 0 < 2 * Real.pi := by positivity
  -- an intermediate value strictly between two consecutive multiples of `2π` is attained
  have hval : ∃ s, f s = 2 * Real.pi * ((w : ℝ) + (if w < n then 1 / 2 else -1 / 2)) := by
    have hmem : 2 * Real.pi * ((w : ℝ) + (if w < n then 1 / 2 else -1 / 2)) ∈
        Set.uIcc (f 0) (f t) := by
      rw [hf0, show f t = 2 * Real.pi * n from hn]
      rcases lt_or_gt_of_ne hnw with h | h
      · have h' : (n : ℝ) + 1 ≤ w := by exact_mod_cast h
        rw [if_neg (not_lt.2 h.le)]
        refine Set.mem_uIcc.2 (Or.inr ⟨?_, ?_⟩) <;> nlinarith
      · have h' : (w : ℝ) + 1 ≤ n := by exact_mod_cast h
        rw [if_pos h]
        refine Set.mem_uIcc.2 (Or.inl ⟨?_, ?_⟩) <;> nlinarith
    obtain ⟨s, -, hs⟩ := intermediate_value_uIcc (hf.continuousOn) hmem
    exact ⟨s, hs⟩
  obtain ⟨s, hs⟩ := hval
  obtain ⟨k, hk⟩ := hint s
  have hk' : (k : ℝ) = w + (if w < n then 1 / 2 else -1 / 2) := by
    have : 2 * Real.pi * k = 2 * Real.pi * ((w : ℝ) + (if w < n then 1 / 2 else -1 / 2)) := by
      rw [← hk]; exact hs
    exact mul_left_cancel₀ hpi.ne' this
  split_ifs at hk' with h
  · have : (2 * (k - w) : ℝ) = 1 := by linarith
    have : (2 * (k - w) : ℤ) = 1 := by exact_mod_cast this
    omega
  · have : (2 * (k - w) : ℝ) = -1 := by linarith
    have : (2 * (k - w) : ℤ) = -1 := by exact_mod_cast this
    omega

end CauchyRiemannIndex

open CauchyRiemannIndex

theorem solution (β : ℝ → ℂ) (hper : Function.Periodic β 1) (hnz : ∀ t, β t ≠ 0)
    (θ : ℝ → ℝ) (hθ : Continuous θ)
    (harg : ∀ t, β t = ‖β t‖ * Complex.exp (θ t * Complex.I))
    (w : ℤ) (hw : θ 1 - θ 0 = 2 * Real.pi * w) (t : ℝ) :
    θ (t + 1) - θ t = 2 * Real.pi * w :=
  CauchyRiemannIndex.arg_add_one_sub_eq β hper hnz θ hθ harg w hw t
