-- Prove2me | solution 1 for Freiman.cert_diagonal_bilinear_interpolation
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-10T09:24:32.30535+00:00
-- url     : https://prove2.me/submissions/00f575ac-c326-465b-a70b-7cc8926081c9

import Definitions.Def_Freiman_certDiagonal
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum

open Freiman

namespace FreimanM8DiagonalInterpolation20260910

private lemma field_add (x y : CertField) :
    certFieldVal (certFieldAdd x y) = certFieldVal x + certFieldVal y := by
  simp only [certFieldVal, certFieldAdd]
  push_cast
  ring

private lemma field_scale (q : ℚ) (x : CertField) :
    certFieldVal (certFieldScale q x) = (q : ℝ) * certFieldVal x := by
  simp only [certFieldVal, certFieldScale]
  push_cast
  ring

private lemma corner_val (a b c : CertField) (r s : ℚ) :
    certFieldVal (certDiagonalCorner a b c r s) =
      certDiagonalFactor a b c r s := by
  simp only [certDiagonalCorner, field_add, field_scale, certDiagonalFactor]
  push_cast
  ring

private lemma affine_nonneg (a b l u x : ℝ) (hlu : l < u)
    (hl : l ≤ x) (hu : x ≤ u) (h0 : 0 ≤ a + b*l) (h1 : 0 ≤ a + b*u) :
    0 ≤ a + b*x := by
  have hprod : 0 ≤ (u-l)*(a+b*x) := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hu) h0,
      mul_nonneg (sub_nonneg.mpr hl) h1]
  by_contra hn
  have hneg := mul_neg_of_pos_of_neg (sub_pos.mpr hlu) (lt_of_not_ge hn)
  linarith

private lemma bilinear_nonneg (a b c d l u v w x y : ℝ)
    (hlu : l < u) (hvw : v < w) (hl : l ≤ x) (hu : x ≤ u)
    (hv : v ≤ y) (hw : y ≤ w)
    (h00 : 0 ≤ a+b*l+c*v+d*l*v) (h01 : 0 ≤ a+b*l+c*w+d*l*w)
    (h10 : 0 ≤ a+b*u+c*v+d*u*v) (h11 : 0 ≤ a+b*u+c*w+d*u*w) :
    0 ≤ a+b*x+c*y+d*x*y := by
  have h0 : 0 ≤ (a+b*l)+(c+d*l)*y :=
    affine_nonneg _ _ _ _ _ hvw hv hw (by nlinarith only [h00]) (by nlinarith only [h01])
  have h1 : 0 ≤ (a+b*u)+(c+d*u)*y :=
    affine_nonneg _ _ _ _ _ hvw hv hw (by nlinarith only [h10]) (by nlinarith only [h11])
  have h : 0 ≤ (a+c*y)+(b+d*y)*x :=
    affine_nonneg _ _ _ _ _ hlu hl hu (by nlinarith only [h0]) (by nlinarith only [h1])
  nlinarith only [h]

end FreimanM8DiagonalInterpolation20260910

open FreimanM8DiagonalInterpolation20260910

theorem solution :
    ∀ (w : CertDiagonalData), certDiagonalDataValid w → (∀ i j : Fin 2, 0 ≤ certFieldVal (w.corners i j)) → ∀ r s : ℝ, certRectangleMem w.rectangle r s → 0 ≤ (if w.positiveDirection then (1:ℝ) else -1)*certDiagonalFactor w.a w.b w.c r s := by
  intro w hvalid hcorners r s hmem
  rcases hvalid with ⟨hrect, _, _, _, _, hcorner, _⟩
  rcases hrect with ⟨hru, hsu⟩
  rcases hmem with ⟨hr0, hr1, hs0, hs1⟩
  have hru' : (w.rectangle.r0 : ℝ) < w.rectangle.r1 := by exact_mod_cast hru
  have hsu' : (w.rectangle.s0 : ℝ) < w.rectangle.s1 := by exact_mod_cast hsu
  let e : ℝ := if w.positiveDirection then 1 else -1
  have he : (((if w.positiveDirection then 1 else -1) : ℚ) : ℝ) = e := by
    dsimp [e]
    split <;> norm_num
  have hc (i j : Fin 2) : 0 ≤ e * certDiagonalFactor w.a w.b w.c
      (certRectangleR w.rectangle i) (certRectangleS w.rectangle j) := by
    have h := hcorners i j
    rw [hcorner i j, field_scale, corner_val, he] at h
    exact h
  have h00 := hc 0 0
  have h01 := hc 0 1
  have h10 := hc 1 0
  have h11 := hc 1 1
  norm_num [certRectangleR, certRectangleS] at h00 h01 h10 h11
  have h := bilinear_nonneg (e*certFieldVal w.a) (e*certFieldVal w.b)
    (e*certFieldVal w.b) (e*certFieldVal w.c)
    w.rectangle.r0 w.rectangle.r1 w.rectangle.s0 w.rectangle.s1 r s
    hru' hsu' hr0 hr1 hs0 hs1
    (by dsimp only [certDiagonalFactor] at h00; nlinarith only [h00])
    (by dsimp only [certDiagonalFactor] at h01; nlinarith only [h01])
    (by dsimp only [certDiagonalFactor] at h10; nlinarith only [h10])
    (by dsimp only [certDiagonalFactor] at h11; nlinarith only [h11])
  change 0 ≤ e * certDiagonalFactor w.a w.b w.c r s
  dsimp only [certDiagonalFactor]
  nlinarith only [h]

#print axioms solution
