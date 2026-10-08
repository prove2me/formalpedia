-- Prove2me | solution 1 for BartlettNN.Margin.Ninf_squash_le_Ninf_quantized
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T12:52:53.975696+00:00
-- url     : https://prove2.me/submissions/885e0cfa-7bdd-4640-aaba-764312b0220e

import Mathlib
import Definitions.Def_BartlettNN_Margin_Classification
import Definitions.Def_BartlettNN_Margin_FatShattering
import Definitions.Def_BartlettNN_Margin_Squash
import Definitions.Def_BartlettNN_Margin_Covering

set_option autoImplicit false

open MeasureTheory

open BartlettNN.Margin in
theorem db5e8b21_quantize_close (α t : ℝ) (hα : 0 < α) :
    |quantize α t - t| ≤ α / 2 := by
  unfold quantize
  have h1 := Int.le_ceil ((t - α / 2) / α)
  have h2 := Int.ceil_lt_add_one ((t - α / 2) / α)
  have e : (t - α / 2) / α * α = t - α / 2 := by field_simp
  have a1 : t - α / 2 ≤ (⌈(t - α / 2) / α⌉ : ℝ) * α := by
    calc t - α / 2 = (t - α / 2) / α * α := e.symm
      _ ≤ _ := mul_le_mul_of_nonneg_right h1 hα.le
  have a2 : (⌈(t - α / 2) / α⌉ : ℝ) * α < t + α / 2 := by
    have := mul_lt_mul_of_pos_right h2 hα
    rw [add_mul, e] at this; linarith
  rw [abs_le]; constructor <;> linarith

open BartlettNN.Margin in
theorem db5e8b21_dInf_le {X : Type*} {n : ℕ} (x : Fin n → X) (α : ℝ) (hα : 0 < α)
    (f g : X → ℝ) :
    dInf x g f ≤ dInf x g (quantize α ∘ f) + α / 2 := by
  unfold dInf
  have hnn : 0 ≤ ⨆ i, |g (x i) - (quantize α ∘ f) (x i)| :=
    Real.iSup_nonneg (fun i => abs_nonneg _)
  refine Real.iSup_le (fun i => ?_) (by linarith)
  have hb : |g (x i) - (quantize α ∘ f) (x i)| ≤ ⨆ i, |g (x i) - (quantize α ∘ f) (x i)| :=
    le_ciSup (f := fun i => |g (x i) - (quantize α ∘ f) (x i)|) (Finite.bddAbove_range _) i
  have hq := db5e8b21_quantize_close α (f (x i)) hα
  have tri : |g (x i) - f (x i)| ≤
      |g (x i) - (quantize α ∘ f) (x i)| + |quantize α (f (x i)) - f (x i)| := by
    have := abs_sub_le (g (x i)) ((quantize α ∘ f) (x i)) (f (x i))
    simpa using this
  linarith

open BartlettNN.Margin in
theorem solution {X : Type*} (H : Set (X → ℝ)) (γ : ℝ) (hγ : 0 < γ)
    (m : ℕ) :
    Ninf (squashClass γ H) (γ / 2) (2 * m)
      ≤ Ninf ((fun f => quantize (γ / 8) ∘ f) '' squashClass γ H) (γ / 4) (2 * m) := by
  unfold Ninf
  refine iSup_le fun x => ?_
  refine le_trans ?_ (le_iSup (fun x : Fin (2 * m) → X =>
    coverNum (dInf x) ((fun f => quantize (γ / 8) ∘ f) '' squashClass γ H) (γ / 4)) x)
  unfold coverNum
  refine le_iInf₂ fun T hT => iInf₂_le T ?_
  intro f hf
  obtain ⟨g, hg, hlt⟩ := hT _ ⟨f, hf, rfl⟩
  refine ⟨g, hg, ?_⟩
  have := db5e8b21_dInf_le x (γ / 8) (by linarith) f g
  simp only at hlt
  linarith
