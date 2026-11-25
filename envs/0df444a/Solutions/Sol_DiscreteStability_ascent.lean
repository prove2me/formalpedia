-- Prove2me | solution 1 for DiscreteStability.ascent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:53:35.749458+00:00
-- url     : https://prove2.me/submissions/d107bcec-0d68-49c4-adb2-70f054702e74

import Definitions.Def_DiscreteStability_Basic
import Definitions.Def_DiscreteStability_Ascent
import Theorems.Thm_DiscreteStability_StepBound_norm_sq_le


set_option autoImplicit true
open scoped RealInnerProductSpace
open Set
open DiscreteStability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace DiscreteStability
theorem _root_.solution {f : E → ℝ} {g : E → E} {S : Set E} {L lo hi : ℝ} {P : E →L[ℝ] E}
    (hP : StepBound P lo hi) (hL : 0 ≤ L) {x : E} {t : ℝ}
    (hseg : ∀ τ ∈ Icc (0 : ℝ) t, x + τ • P (g x) ∈ S)
    (hgrad : ∀ z ∈ S, HasFDerivAt f (innerSL ℝ (g z)) z)
    (hlip : ∀ u ∈ S, ∀ v ∈ S, ‖g u - g v‖ ≤ L * ‖u - v‖) :
    ∀ s ∈ Icc (0 : ℝ) t,
      f x + s * (1 - s / 2 * L * hi) * ⟪P (g x), g x⟫ ≤ f (x + s • P (g x)) := by
  intro s hs
  set d := P (g x) with hd
  set a := ⟪d, g x⟫ with ha
  have hxS : x ∈ S := by simpa using hseg 0 ⟨le_rfl, hs.1.trans hs.2⟩
  -- derivative of φ(τ) = f (x + τ d)
  have hφ : ∀ τ ∈ Icc (0 : ℝ) t,
      HasDerivAt (fun τ : ℝ => f (x + τ • d)) ⟪g (x + τ • d), d⟫ τ := by
    intro τ hτ
    have hl : HasDerivAt (fun τ : ℝ => x + τ • d) d τ := by
      simpa using ((hasDerivAt_id' τ).smul_const d).const_add x
    have := (hgrad _ (hseg τ hτ)).comp_hasDerivAt τ hl
    simpa [Function.comp_def, innerSL_apply_apply] using this
  -- ψ(τ) = φ(τ) - τ a + (L/2) τ² ‖d‖² is monotone on [0, t]
  set ψ : ℝ → ℝ := fun τ => f (x + τ • d) - τ * a + L / 2 * τ ^ 2 * ‖d‖ ^ 2 with hψdef
  have hψ : ∀ τ ∈ Icc (0 : ℝ) t, HasDerivAt ψ
      (⟪g (x + τ • d), d⟫ - 1 * a + L / 2 * ((2 : ℕ) * τ ^ (2 - 1)) * ‖d‖ ^ 2) τ := by
    intro τ hτ
    exact (((hφ τ hτ).sub ((hasDerivAt_id' τ).mul_const a)).add
      (((hasDerivAt_pow 2 τ).const_mul (L / 2)).mul_const (‖d‖ ^ 2)))
  have hmono : MonotoneOn ψ (Icc 0 t) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 t)
    · exact fun τ hτ => (hψ τ hτ).continuousAt.continuousWithinAt
    · intro τ hτ
      rw [interior_Icc] at hτ
      exact (hψ τ (Ioo_subset_Icc_self hτ)).hasDerivWithinAt
    · intro τ hτ
      rw [interior_Icc] at hτ
      have hτ' : τ ∈ Icc (0 : ℝ) t := Ioo_subset_Icc_self hτ
      have hz := hseg τ hτ'
      have h1 : -(‖g (x + τ • d) - g x‖ * ‖d‖) ≤ ⟪g (x + τ • d) - g x, d⟫ := by
        have := abs_real_inner_le_norm (g (x + τ • d) - g x) d
        linarith [neg_abs_le ⟪g (x + τ • d) - g x, d⟫]
      have h2 : ‖g (x + τ • d) - g x‖ ≤ L * ‖(x + τ • d) - x‖ := hlip _ hz _ hxS
      have h3 : ‖(x + τ • d) - x‖ = τ * ‖d‖ := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ.1.le]
      rw [h3] at h2
      have h4 := mul_le_mul_of_nonneg_right h2 (norm_nonneg d)
      have h5 : ⟪g (x + τ • d) - g x, d⟫ = ⟪g (x + τ • d), d⟫ - a := by
        rw [inner_sub_left, ha, real_inner_comm d (g x)]
      norm_num
      nlinarith [h1, h4, h5]
  have hψs := hmono ⟨le_rfl, hs.1.trans hs.2⟩ hs hs.1
  simp only [hψdef, zero_smul, add_zero, zero_mul, sub_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, mul_zero] at hψs
  -- use ‖d‖² ≤ hi ⟪d, g⟫
  have hnorm : ‖d‖ ^ 2 ≤ hi * ⟪P (g x), g x⟫ := hP.norm_sq_le (g x)
  have ha' : a = ⟪P (g x), g x⟫ := rfl
  have h6 := mul_le_mul_of_nonneg_left hnorm (by positivity : (0 : ℝ) ≤ L / 2 * s ^ 2)
  rw [← ha'] at h6
  nlinarith [hψs, h6]
end DiscreteStability
