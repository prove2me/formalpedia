-- Prove2me | solution 1 for BandParity.card_class_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:56:35.022161+00:00
-- url     : https://prove2.me/submissions/1d2f5f29-c19d-4e6f-a61c-1e2129e9e299

module
public import Definitions.Def_BandParity_Pin
public import Definitions.Def_BandParity_FixedBase
public import Definitions.Def_BandParity_CosetSums
public import Theorems.Thm_BandParity_card_class_mul
public import Theorems.Thm_BandParity_exists_generator
public import Theorems.Thm_BandParity_gi_im
public import Theorems.Thm_BandParity_gi_re
public import Theorems.Thm_BandParity_gi_sq
public import Theorems.Thm_BandParity_quartic_apply_generator
attribute [local simp] BandParity.gi_im
attribute [local simp] BandParity.gi_re



set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ
namespace BandParity
theorem _root_.solution (z : GaussianInt) (hz : z = 1 ∨ z = gi ∨ z = -1 ∨ z = -gi) :
    (univ.filter (fun n : ZMod p => χ n = z)).card =
      (univ.filter (fun n : ZMod p => χ n = 1)).card := by
  obtain ⟨g, -, hg⟩ := exists_generator (p := p)
  have hg0 : (g : ZMod p) ≠ 0 := Units.ne_zero g
  set c : GaussianInt → ℕ := fun z => (univ.filter (fun n : ZMod p => χ n = z)).card with hc
  have step : ∀ w, c (χ g * w) = c w := fun w => card_class_mul hχ hg0 w
  rcases quartic_apply_generator χ hχ hg with h | h <;> rw [h] at step
  · have e1 := step 1; have e2 := step gi; have e3 := step (-1)
    simp only [mul_one, mul_neg, gi_sq, ← sq] at e1 e2 e3
    change c z = c 1
    rcases hz with rfl | rfl | rfl | rfl
    · rfl
    · exact e1
    · exact e2.trans e1
    · exact e3.trans (e2.trans e1)
  · have e1 := step 1; have e2 := step (-gi); have e3 := step (-1)
    simp only [mul_one, mul_neg, neg_neg, ← sq] at e1 e2 e3
    change c z = c 1
    rcases hz with rfl | rfl | rfl | rfl
    · rfl
    · exact e3.trans (e2.trans e1)
    · exact e2.trans e1
    · exact e1
end BandParity
