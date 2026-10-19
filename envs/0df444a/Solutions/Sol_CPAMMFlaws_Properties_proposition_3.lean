-- Prove2me | solution 1 for CPAMMFlaws.Properties.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-18T07:01:15.360626+00:00
-- url     : https://prove2.me/submissions/3c632491-e73c-4cbf-a892-de2edccc8313

-- Research directed by Alexander Richard Towell (queelius); formalization by OpenAI Codex.
-- Mathematics: Andreas Park, June 8, 2021 working paper, Proposition 3.
-- Platform statement/definition and existing sign/reserve repairs: mikedeng1.
-- Statement review: Shuze Chen. Prior Lemma 2/additivity/scaling proofs: carlok.
-- Lean/Mathlib contributors supplied the formal foundations.
import Mathlib
import Definitions.Def_CPAMMFlaws_Properties_Setting
set_option autoImplicit false
open CPAMMFlaws.Properties
namespace AMMResearch
lemma front_run (X Y x : ℝ) (hX : 0<X) (hY : 0<Y) (hx : 0<x) (hx2 : x<X/2) :
    -pcmm (-x) (X-2*x) (Y+pcmm (2*x) X Y) = x*X*Y/((X-x)*(X-2*x)) ∧
    -pcmm (-x) (X-2*x) (Y+pcmm (2*x) X Y)-pcmm x X Y = 2*x^2*Y/((X-x)*(X-2*x)) ∧
    0<2*x^2*Y/((X-x)*(X-2*x)) := by
  have h1 : 0<X-x := by linarith
  have h2 : 0<X-2*x := by linarith
  have h3 : X-2*x- -x = X-x := by ring
  dsimp [pcmm]
  rw [h3]
  refine ⟨?_,?_,?_⟩
  · field_simp [ne_of_gt h1,ne_of_gt h2]
    ring_nf
    field_simp [show -(x*2)+X≠0 by linarith]
    <;> ring
  · field_simp [ne_of_gt h1,ne_of_gt h2] <;> ring
  · positivity
lemma arbitrage (X Y x α : ℝ) (hX : 0<X) (hY : 0<Y) (hx : 0<x)
    (hxX : x<X) (hα : 0<α) (hα1 : α<1) :
    0 < -pcmm (-(α*x)) (X-x) (Y+pcmm x X Y)-pcmm (α*x) X Y := by
  have h1 : 0<X-x := by linarith
  have hax : α*x<x := by nlinarith
  have h2 : 0<X-α*x := by linarith
  have h3 : 0<X-x+α*x := by positivity
  have he : -pcmm (-(α*x)) (X-x) (Y+pcmm x X Y)-pcmm (α*x) X Y =
      α*(1-α)*x^2*Y*(2*X-x)/((X-x)*(X-x+α*x)*(X-α*x)) := by
    unfold pcmm
    simp only [sub_neg_eq_add]
    field_simp
    ring
  rw [he]
  exact div_pos (mul_pos (mul_pos (mul_pos (mul_pos hα (sub_pos.mpr hα1)) (sq_pos_of_pos hx)) hY) (by linarith)) (mul_pos (mul_pos h1 h3) h2)
lemma all_properties (X Y x α k : ℝ) (hX : 0<X) (hY : 0<Y)
    (hx : 0<x) (hxX : x<X) (hα : 0<α) (hα1 : α<1) (hk : 0<k) :
    pcmm (α*x) X Y+pcmm ((1-α)*x) (X-α*x) (Y+pcmm (α*x) X Y)=pcmm x X Y ∧
    (x<X/2 → 0< -pcmm x X Y-pcmm (-x) (X-2*x) (Y+pcmm (2*x) X Y)) ∧
    pcmm x X Y=k*pcmm (x/k) (X/k) (Y/k) ∧
    0< -pcmm (-(α*x)) (X-x) (Y+pcmm x X Y)-pcmm (α*x) X Y := by
  have h1 : 0<X-x := by linarith
  have h2 : 0<X-α*x := by nlinarith
  refine ⟨?_,?_,?_,arbitrage X Y x α hX hY hx hxX hα hα1⟩
  · have he : X-α*x-(1-α)*x=X-x := by ring
    unfold pcmm
    rw [he]
    field_simp
    ring
  · intro hx2
    have h := front_run X Y x hX hY hx hx2
    linarith [h.2.1,h.2.2]
  · unfold pcmm
    field_simp
end AMMResearch


theorem solution (X Y x α k : ℝ) (hX : 0 < X) (hY : 0 < Y)
    (hx : 0 < x) (hxX : x < X) (hα : 0 < α) (hα1 : α < 1) (hk : 0 < k) :
    pcmm (α * x) X Y + pcmm ((1 - α) * x) (X - α * x) (Y + pcmm (α * x) X Y) = pcmm x X Y ∧
      (x < X / 2 → 0 < -pcmm x X Y - pcmm (-x) (X - 2 * x) (Y + pcmm (2 * x) X Y)) ∧
      pcmm x X Y = k * pcmm (x / k) (X / k) (Y / k) ∧
      0 < -pcmm (-(α * x)) (X - x) (Y + pcmm x X Y) - pcmm (α * x) X Y := by
  exact AMMResearch.all_properties X Y x α k hX hY hx hxX hα hα1 hk


