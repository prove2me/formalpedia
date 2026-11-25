-- Prove2me | solution 1 for FractionalColouring.fracChromaticNumber_mycielski_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:56:38.95959+00:00
-- url     : https://prove2.me/submissions/c375e98b-7c86-4dfe-8659-9cf57ee28cc3

module
public import Definitions.Def_FractionalLib_Basic
public import Definitions.Def_Mycielski_Basic
public import Definitions.Def_FractionalLib_LarsenProppUllman
public import Theorems.Thm_FractionalColouring_mycielskiColouring_sum
public import Theorems.Thm_FractionalColouring_isFracColouring_mycielskiColouring
public import Theorems.Thm_FractionalColouring_fracChromaticNumber_le
public import Theorems.Thm_FractionalColouring_one_le_fracChromaticNumber
public import Theorems.Thm_FractionalColouring_weights_nonempty


set_option autoImplicit true
@[expose] public section
public section
open Finset hiding shadow
open Mycielski
open FractionalColouring
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
variable {G}
namespace FractionalColouring
theorem _root_.solution [Nonempty V] :
    fracChromaticNumber (graph G) ≤ fracChromaticNumber G + 1 / fracChromaticNumber G := by
  have ha := one_le_fracChromaticNumber (G := G)
  have ha0 : 0 < fracChromaticNumber G := by linarith
  suffices h : fracChromaticNumber (graph G) - 1 / fracChromaticNumber G ≤ fracChromaticNumber G
    by linarith
  refine le_csInf weights_nonempty ?_
  rintro _ ⟨x, hx, rfl⟩
  have hat := fracChromaticNumber_le hx
  have ht : 1 ≤ ∑ s, x s := ha.trans hat
  have ht0 : 0 < ∑ s, x s := by linarith
  have hM := fracChromaticNumber_le (isFracColouring_mycielskiColouring hx ht rfl)
  rw [mycielskiColouring_sum, ← Finset.sum_mul, ← Finset.sum_div] at hM
  have h1 : (∑ s, x s) * ((∑ s, x s - 1) / ∑ s, x s) + (∑ s, x s) / (∑ s, x s) =
      ∑ s, x s := by field_simp; ring
  have h2 : 1 / ∑ s, x s ≤ 1 / fracChromaticNumber G :=
    one_div_le_one_div_of_le ha0 hat
  linarith
end FractionalColouring
