-- Prove2me | solution 1 for BookProof.FarisLavine.deficiencyTrivialAt_of_farisLavine
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T13:00:41.148679+00:00
-- url     : https://prove2.me/submissions/65033a74-68bb-446c-8bbd-4920669832c6

-- Generated from ChapterFarisLavineCore.lean — solution of BookProof.FarisLavine.deficiencyTrivialAt_of_farisLavine
import Mathlib
import Definitions.Def_ChapterFarisLavineCore
import Theorems.Thm_BookProof_FarisLavine_inner_apply_self_im
import Theorems.Thm_BookProof_FarisLavine_quadForm_im
import Theorems.Thm_BookProof_FarisLavine_commForm_eq
open BookProof.FarisLavine













variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution
    (H N : D →ₗ[ℂ] F) (c d : ℝ)
    (hH : SymmetricOn D H) (hN : SymmetricOn D N)
    (hc : 0 ≤ c)
    (hNpos : ∀ x : D, 0 ≤ quadForm N x)
    (hNsurj : ∀ f : F, ∃ x : D, N x + (x : F) = f)
    (hcomm : ∀ x : D, |commForm H N x| ≤ c * quadForm N x)
    (hd : c < 2 * |d|) :
    DeficiencyTrivialAt D H ((d : ℂ) * Complex.I) := by

  intro w hw
  obtain ⟨g, hg⟩ := hNsurj w
  have key := hw g
  rw [← hg, inner_add_right, inner_add_right] at key
  have him := congrArg Complex.im key
  simp only [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.add_re] at him
  have hBim : (inner ℂ (H g) (g : F) : ℂ).im = 0 := inner_apply_self_im H hH g
  have hPim : (inner ℂ (g : F) (N g) : ℂ).im = 0 := quadForm_im N hN g
  have hQim : (inner ℂ (g : F) (g : F) : ℂ).im = 0 := by
    simpa using inner_self_im (𝕜 := ℂ) (g : F)
  have hQre : (inner ℂ (g : F) (g : F) : ℂ).re = ‖(g : F)‖ ^ 2 := by
    simpa using inner_self_eq_norm_sq (𝕜 := ℂ) (g : F)
  set t : ℝ := quadForm N g + ‖(g : F)‖ ^ 2 with ht
  have hAim : (inner ℂ (H g) (N g) : ℂ).im = d * t := by
    rw [hBim, hPim, hQim, hQre] at him
    simp only [quadForm, ht]
    linarith [him]
  have htnn : 0 ≤ t := by have := hNpos g; positivity
  have habs : |commForm H N g| = 2 * |d| * t := by
    rw [commForm_eq, hAim, abs_mul, abs_mul, abs_of_nonneg htnn]
    norm_num
    ring
  have h1 : 2 * |d| * t ≤ c * quadForm N g := habs ▸ hcomm g
  have h2 : c * quadForm N g ≤ c * t := by
    have hle : quadForm N g ≤ t := by rw [ht]; nlinarith [sq_nonneg ‖(g : F)‖]
    exact mul_le_mul_of_nonneg_left hle hc
  have ht0 : t = 0 := by nlinarith
  have hgz : (g : F) = 0 := by
    have hnn := hNpos g
    have h4 : ‖(g : F)‖ ^ 2 = 0 := by rw [ht] at ht0; nlinarith [sq_nonneg ‖(g : F)‖]
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg (g : F)])
  have hg0 : g = 0 := Subtype.ext hgz
  rw [← hg, hg0]
  simp
