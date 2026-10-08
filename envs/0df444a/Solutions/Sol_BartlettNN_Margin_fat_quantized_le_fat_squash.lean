-- Prove2me | solution 1 for BartlettNN.Margin.fat_quantized_le_fat_squash
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T12:46:07.007797+00:00
-- url     : https://prove2.me/submissions/11b08b95-85ad-4fe0-a1ed-fb839db97e2a

import Mathlib
import Definitions.Def_BartlettNN_Margin_Classification
import Definitions.Def_BartlettNN_Margin_FatShattering
import Definitions.Def_BartlettNN_Margin_Squash
import Definitions.Def_BartlettNN_Margin_Covering

set_option autoImplicit false

open MeasureTheory

open BartlettNN.Margin in
lemma dab8916b_quantize_err (α x : ℝ) (hα : 0 < α) : |quantize α x - x| ≤ α / 2 := by
  unfold quantize
  set y := (x - α / 2) / α with hy
  have h1 : y ≤ (⌈y⌉ : ℝ) := Int.le_ceil y
  have h2 : (⌈y⌉ : ℝ) < y + 1 := Int.ceil_lt_add_one y
  have hyα : y * α = x - α / 2 := by rw [hy]; field_simp
  have h1' : y * α ≤ (⌈y⌉ : ℝ) * α := mul_le_mul_of_nonneg_right h1 hα.le
  have h2' : (⌈y⌉ : ℝ) * α < (y + 1) * α := mul_lt_mul_of_pos_right h2 hα
  rw [abs_le]
  constructor <;> nlinarith

open BartlettNN.Margin in
lemma dab8916b_pm_abs (b : Bool) : |pm b| = 1 := by
  cases b <;> simp [pm]

open BartlettNN.Margin in
theorem solution {X : Type*} (H : Set (X → ℝ)) (γ : ℝ) (hγ : 0 < γ) :
    fat ((fun f => quantize (γ / 8) ∘ f) '' squashClass γ H) (γ / 8)
      ≤ fat (squashClass γ H) (γ / 16) := by
  unfold fat
  refine iSup_mono fun m => iSup_mono fun x => ?_
  refine iSup_le fun hs => ?_
  have hs' : GammaShatters (squashClass γ H) (γ / 16) x := by
    obtain ⟨r, hr⟩ := hs
    refine ⟨r, fun b => ?_⟩
    obtain ⟨h, hh, hi⟩ := hr b
    obtain ⟨f, hf, rfl⟩ := hh
    refine ⟨f, hf, fun i => ?_⟩
    have hq := dab8916b_quantize_err (γ / 8) (f (x i)) (by positivity)
    have hp := dab8916b_pm_abs (b i)
    have hi' := hi i
    simp only [Function.comp_apply] at hi'
    have key : |(quantize (γ / 8) (f (x i)) - f (x i)) * pm (b i)| ≤ γ / 16 := by
      rw [abs_mul, hp, mul_one]; linarith
    have e : (quantize (γ / 8) (f (x i)) - r i) * pm (b i)
        = (f (x i) - r i) * pm (b i) + (quantize (γ / 8) (f (x i)) - f (x i)) * pm (b i) := by
      ring
    have := (abs_le.mp key).2
    linarith
  exact le_iSup_of_le hs' le_rfl
