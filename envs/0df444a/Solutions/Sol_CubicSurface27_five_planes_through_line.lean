-- Prove2me | solution 1 for CubicSurface27.five_planes_through_line
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-22T10:10:34.717393+00:00
-- url     : https://prove2.me/submissions/0b2ba2ee-0d89-4538-affd-8a313810c7bc

import Mathlib
import Definitions.Def_cubic_surface_27_layer

/-!
Proof of `CubicSurface27.five_planes_through_line`.

Route: pick a basis `v₀, v₁, v₂, v₃` of `ℂ⁴` with `L = span {v₀, v₁}`. In these coordinates
`F = f(x,y,z,w)` has no pure `x,y` monomials, and on the plane `P_λ = L ⊔ ℂ(v₂ + λ v₃)`
we get `f(x,y,z,λz) = z · Q_λ(x,y,z)`. The plane contains a second line iff the
(half-)determinant `Δ(λ)` of the conic `Q_λ` vanishes. `Δ` is a polynomial of degree `≤ 5`,
and smoothness makes every root simple (also at `λ = ∞`, by swapping `v₂, v₃`). Hence
exactly 5 planes.
-/

open MvPolynomial

namespace FPAux

open CubicSurface27

/-! ### Cubic forms: induction principle and Taylor expansion (from `residual_two_lines`) -/

lemma exists_single_add {n : ℕ} (m : Fin 4 →₀ ℕ) (hm : m.degree = n + 1) :
    ∃ i m', m = m' + Finsupp.single i 1 ∧ m'.degree = n := by
  have hne : m ≠ 0 := by
    rintro rfl; simp at hm
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hne
  have hle : Finsupp.single i 1 ≤ m := by
    rw [Finsupp.single_le_iff]; simp at hi; omega
  refine ⟨i, m - Finsupp.single i 1, (tsub_add_cancel_of_le hle).symm, ?_⟩
  have h := congrArg Finsupp.degree (tsub_add_cancel_of_le hle)
  rw [map_add, Finsupp.degree_single, hm] at h
  omega

lemma monomial_deg3 (m : Fin 4 →₀ ℕ) (hm : m.degree = 3) :
    ∃ a b c : Fin 4, monomial m (1 : ℂ) = X a * X b * X c := by
  obtain ⟨c, m1, rfl, h1⟩ := exists_single_add (n := 2) m hm
  obtain ⟨b, m2, rfl, h2⟩ := exists_single_add (n := 1) m1 h1
  obtain ⟨a, m3, rfl, h3⟩ := exists_single_add (n := 0) m2 h2
  rw [Finsupp.degree_eq_zero_iff] at h3
  subst h3
  refine ⟨a, b, c, ?_⟩
  simp [X, monomial_mul]

lemma cubic_induction (P : MvPolynomial (Fin 4) ℂ → Prop)
    (h0 : P 0) (hadd : ∀ F G, P F → P G → P (F + G))
    (hsmul : ∀ (r : ℂ) F, P F → P (r • F))
    (hX : ∀ a b c : Fin 4, P (X a * X b * X c))
    (F : MvPolynomial (Fin 4) ℂ) (hF : IsCubicForm F) : P F := by
  rw [F.as_sum]
  refine Finset.sum_induction _ P hadd h0 ?_
  intro m hm
  have hdeg : m.degree = 3 := by
    have := hF (mem_support_iff.mp hm)
    rw [Finsupp.degree_eq_weight_one]
    exact this
  obtain ⟨a, b, c, habc⟩ := monomial_deg3 m hdeg
  have : monomial m (coeff m F) = coeff m F • monomial m (1 : ℂ) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [this, habc]
  exact hsmul _ _ (hX a b c)

lemma taylor3 (F : MvPolynomial (Fin 4) ℂ) (hF : IsCubicForm F) (x w : Fin 4 → ℂ) :
    ∃ q : ℂ, ∀ t : ℂ, eval (x + t • w) F =
      eval x F + t * (∑ i, w i * eval x (pderiv i F)) + t ^ 2 * q + t ^ 3 * eval w F := by
  refine cubic_induction (fun F => ∃ q : ℂ, ∀ t : ℂ, eval (x + t • w) F =
      eval x F + t * (∑ i, w i * eval x (pderiv i F)) + t ^ 2 * q + t ^ 3 * eval w F)
    ?_ ?_ ?_ ?_ F hF
  · exact ⟨0, fun t => by simp⟩
  · rintro F G ⟨q1, h1⟩ ⟨q2, h2⟩
    refine ⟨q1 + q2, fun t => ?_⟩
    simp only [map_add, h1 t, h2 t, mul_add, Finset.sum_add_distrib]
    ring
  · rintro r F ⟨q, h⟩
    refine ⟨r * q, fun t => ?_⟩
    simp only [smul_eval, Derivation.map_smul, h t]
    have : ∑ i, w i * (r * eval x (pderiv i F)) = r * ∑ i, w i * eval x (pderiv i F) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [this]; ring
  · intro a b c
    refine ⟨x a * w b * w c + w a * x b * w c + w a * w b * x c, fun t => ?_⟩
    simp [Derivation.leibniz, pderiv_X, Pi.single_apply, mul_add, add_mul,
      Finset.sum_add_distrib, apply_ite (eval x), mul_ite, Finset.sum_ite_eq]
    ring

/-- The derivative of `F` at `x` in direction `w`. -/
noncomputable def D (F : MvPolynomial (Fin 4) ℂ) (x w : Fin 4 → ℂ) : ℂ :=
  ∑ i, w i * eval x (pderiv i F)

lemma D_formula (F : MvPolynomial (Fin 4) ℂ) (hF : IsCubicForm F) (x w : Fin 4 → ℂ) :
    D F x w = (eval (x + w) F - eval (x - w) F) / 2 - eval w F := by
  obtain ⟨q, hq⟩ := taylor3 F hF x w
  have e1 := hq 1
  have e2 := hq (-1)
  simp only [one_smul, neg_smul, ← sub_eq_add_neg] at e1 e2
  unfold D
  linear_combination (e2 - e1) / 2

lemma quad_root (A B C : ℂ) :
    ∃ a b : ℂ, (a ≠ 0 ∨ b ≠ 0) ∧ A * a ^ 2 + B * a * b + C * b ^ 2 = 0 := by
  by_cases hA : A = 0
  · exact ⟨1, 0, Or.inl one_ne_zero, by simp [hA]⟩
  · obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self (B ^ 2 - 4 * A * C)
    refine ⟨(-B + s) / (2 * A), 1, Or.inr one_ne_zero, ?_⟩
    field_simp
    linear_combination -hs

/-! ### A cubic form in coordinates -/

/-- A general cubic in `x, y, z, w` with 20 coefficients. -/
def fC (k : Fin 20 → ℂ) (x y z w : ℂ) : ℂ :=
  k 0 * x ^ 3 + k 1 * x ^ 2 * y + k 2 * x * y ^ 2 + k 3 * y ^ 3 +
  k 4 * x ^ 2 * z + k 5 * x ^ 2 * w + k 6 * x * y * z + k 7 * x * y * w +
  k 8 * y ^ 2 * z + k 9 * y ^ 2 * w + k 10 * x * z ^ 2 + k 11 * x * z * w + k 12 * x * w ^ 2 +
  k 13 * y * z ^ 2 + k 14 * y * z * w + k 15 * y * w ^ 2 +
  k 16 * z ^ 3 + k 17 * z ^ 2 * w + k 18 * z * w ^ 2 + k 19 * w ^ 3

def fx (k : Fin 20 → ℂ) (x y z w : ℂ) : ℂ :=
  3 * k 0 * x ^ 2 + 2 * k 1 * x * y + k 2 * y ^ 2 + 2 * k 4 * x * z + 2 * k 5 * x * w +
  k 6 * y * z + k 7 * y * w + k 10 * z ^ 2 + k 11 * z * w + k 12 * w ^ 2

def fy (k : Fin 20 → ℂ) (x y z w : ℂ) : ℂ :=
  k 1 * x ^ 2 + 2 * k 2 * x * y + 3 * k 3 * y ^ 2 + k 6 * x * z + k 7 * x * w +
  2 * k 8 * y * z + 2 * k 9 * y * w + k 13 * z ^ 2 + k 14 * z * w + k 15 * w ^ 2

def fz (k : Fin 20 → ℂ) (x y z w : ℂ) : ℂ :=
  k 4 * x ^ 2 + k 6 * x * y + k 8 * y ^ 2 + 2 * k 10 * x * z + k 11 * x * w +
  2 * k 13 * y * z + k 14 * y * w + 3 * k 16 * z ^ 2 + 2 * k 17 * z * w + k 18 * w ^ 2

def fw (k : Fin 20 → ℂ) (x y z w : ℂ) : ℂ :=
  k 5 * x ^ 2 + k 7 * x * y + k 9 * y ^ 2 + k 11 * x * z + 2 * k 12 * x * w +
  k 14 * y * z + 2 * k 15 * y * w + k 17 * z ^ 2 + 2 * k 18 * z * w + 3 * k 19 * w ^ 2

/-- Symmetrised product used for the coefficients of `expand4`. -/
def t3 (i j l : Fin 4) (u v w : Fin 4 → ℂ) : ℂ :=
  u i * v j * w l + u i * w j * v l + v i * u j * w l + v i * w j * u l +
    w i * u j * v l + w i * v j * u l

lemma expand4 (F : MvPolynomial (Fin 4) ℂ) (hF : IsCubicForm F) (p q r s : Fin 4 → ℂ) :
    ∃ k : Fin 20 → ℂ, ∀ a b c d : ℂ,
      eval (a • p + b • q + c • r + d • s) F = fC k a b c d := by
  refine cubic_induction (fun F => ∃ k : Fin 20 → ℂ, ∀ a b c d : ℂ,
      eval (a • p + b • q + c • r + d • s) F = fC k a b c d) ?_ ?_ ?_ ?_ F hF
  · exact ⟨0, fun a b c d => by simp [fC]⟩
  · rintro F G ⟨k1, h1⟩ ⟨k2, h2⟩
    refine ⟨k1 + k2, fun a b c d => ?_⟩
    simp only [map_add, h1, h2, fC, Pi.add_apply]
    ring
  · rintro t F ⟨k, h⟩
    refine ⟨t • k, fun a b c d => ?_⟩
    simp only [smul_eval, h, fC, Pi.smul_apply, smul_eq_mul]
    ring
  · intro i j l
    refine ⟨![t3 i j l p p p / 6, t3 i j l p p q / 2, t3 i j l p q q / 2, t3 i j l q q q / 6,
      t3 i j l p p r / 2, t3 i j l p p s / 2, t3 i j l p q r, t3 i j l p q s,
      t3 i j l q q r / 2, t3 i j l q q s / 2, t3 i j l p r r / 2, t3 i j l p r s,
      t3 i j l p s s / 2, t3 i j l q r r / 2, t3 i j l q r s, t3 i j l q s s / 2,
      t3 i j l r r r / 6, t3 i j l r r s / 2, t3 i j l r s s / 2, t3 i j l s s s / 6],
      fun a b c d => ?_⟩
    simp [fC, t3]
    ring

/-! ### The setup: an adapted basis and the coordinate cubic -/

structure Setup (F : MvPolynomial (Fin 4) ℂ) (L : Submodule ℂ (Fin 4 → ℂ)) where
  v0 : Fin 4 → ℂ
  v1 : Fin 4 → ℂ
  v2 : Fin 4 → ℂ
  v3 : Fin 4 → ℂ
  k : Fin 20 → ℂ
  hind : ∀ a b c d : ℂ, a • v0 + b • v1 + c • v2 + d • v3 = 0 →
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0
  hspan : ∀ x : Fin 4 → ℂ, ∃ a b c d : ℂ, x = a • v0 + b • v1 + c • v2 + d • v3
  hLmem : ∀ x, x ∈ L ↔ ∃ a b : ℂ, x = a • v0 + b • v1
  hk : ∀ a b c d : ℂ, eval (a • v0 + b • v1 + c • v2 + d • v3) F = fC k a b c d
  hk0 : k 0 = 0 ∧ k 1 = 0 ∧ k 2 = 0 ∧ k 3 = 0

/-- The permutation of coefficients induced by swapping `z` and `w`. -/
def σ : Fin 20 → Fin 20 := ![0, 1, 2, 3, 5, 4, 7, 6, 9, 8, 12, 11, 10, 15, 14, 13, 19, 18, 17, 16]

def Setup.swap {F L} (S : Setup F L) : Setup F L where
  v0 := S.v0
  v1 := S.v1
  v2 := S.v3
  v3 := S.v2
  k := fun i => S.k (σ i)
  hind := by
    intro a b c d h
    obtain ⟨h1, h2, h3, h4⟩ := S.hind a b d c (by rw [← h]; abel)
    exact ⟨h1, h2, h4, h3⟩
  hspan := by
    intro x
    obtain ⟨a, b, c, d, rfl⟩ := S.hspan x
    exact ⟨a, b, d, c, by abel⟩
  hLmem := S.hLmem
  hk := by
    intro a b c d
    rw [show a • S.v0 + b • S.v1 + c • S.v3 + d • S.v2 = a • S.v0 + b • S.v1 + d • S.v2 + c • S.v3
      by abel, S.hk]
    simp [fC, σ]
    ring
  hk0 := by simpa [σ] using S.hk0

section
variable {F : MvPolynomial (Fin 4) ℂ} {L : Submodule ℂ (Fin 4 → ℂ)}

lemma Setup.Dcoord (S : Setup F L) (hF : IsCubicForm F) (x y z w x' y' z' w' : ℂ) :
    D F (x • S.v0 + y • S.v1 + z • S.v2 + w • S.v3) (x' • S.v0 + y' • S.v1 + z' • S.v2 + w' • S.v3)
      = x' * fx S.k x y z w + y' * fy S.k x y z w + z' * fz S.k x y z w + w' * fw S.k x y z w := by
  rw [D_formula F hF]
  rw [show x • S.v0 + y • S.v1 + z • S.v2 + w • S.v3 +
      (x' • S.v0 + y' • S.v1 + z' • S.v2 + w' • S.v3) =
      (x + x') • S.v0 + (y + y') • S.v1 + (z + z') • S.v2 + (w + w') • S.v3 by module]
  rw [show x • S.v0 + y • S.v1 + z • S.v2 + w • S.v3 -
      (x' • S.v0 + y' • S.v1 + z' • S.v2 + w' • S.v3) =
      (x - x') • S.v0 + (y - y') • S.v1 + (z - z') • S.v2 + (w - w') • S.v3 by module]
  rw [S.hk, S.hk, S.hk]
  simp only [fC, fx, fy, fz, fw]
  ring

/-- Smoothness in coordinates. -/
lemma Setup.smooth (S : Setup F L) (hF : IsCubicForm F) (hsm : IsSmoothCubic F)
    (x y z w : ℂ) (hne : ¬ (x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0)) (h0 : fC S.k x y z w = 0)
    (hx : fx S.k x y z w = 0) (hy : fy S.k x y z w = 0) (hz : fz S.k x y z w = 0)
    (hw : fw S.k x y z w = 0) : False := by
  set p := x • S.v0 + y • S.v1 + z • S.v2 + w • S.v3 with hp
  have hp0 : p ≠ 0 := fun h => hne (S.hind x y z w h)
  have hFp : eval p F = 0 := by rw [hp, S.hk]; exact h0
  obtain ⟨i, hi⟩ := hsm p hp0 hFp
  obtain ⟨a, b, c, d, hab⟩ := S.hspan (Pi.single i 1)
  have hD := S.Dcoord hF x y z w a b c d
  rw [← hab, hx, hy, hz, hw] at hD
  apply hi
  simpa [D, Pi.single_apply] using hD

end

/-! ### The residual conic and its discriminant -/

def cA (k : Fin 20 → ℂ) (l : ℂ) : ℂ := k 4 + k 5 * l
def cB (k : Fin 20 → ℂ) (l : ℂ) : ℂ := k 6 + k 7 * l
def cC (k : Fin 20 → ℂ) (l : ℂ) : ℂ := k 8 + k 9 * l
def cD (k : Fin 20 → ℂ) (l : ℂ) : ℂ := k 10 + k 11 * l + k 12 * l ^ 2
def cE (k : Fin 20 → ℂ) (l : ℂ) : ℂ := k 13 + k 14 * l + k 15 * l ^ 2
def cG (k : Fin 20 → ℂ) (l : ℂ) : ℂ := k 16 + k 17 * l + k 18 * l ^ 2 + k 19 * l ^ 3
def dA (k : Fin 20 → ℂ) (_l : ℂ) : ℂ := k 5
def dB (k : Fin 20 → ℂ) (_l : ℂ) : ℂ := k 7
def dC (k : Fin 20 → ℂ) (_l : ℂ) : ℂ := k 9
def dD (k : Fin 20 → ℂ) (l : ℂ) : ℂ := k 11 + 2 * k 12 * l
def dE (k : Fin 20 → ℂ) (l : ℂ) : ℂ := k 14 + 2 * k 15 * l
def dG (k : Fin 20 → ℂ) (l : ℂ) : ℂ := k 17 + 2 * k 18 * l + 3 * k 19 * l ^ 2

/-- A ternary quadratic form. -/
def Qf (A B C D E G x y z : ℂ) : ℂ := A * x ^ 2 + B * x * y + C * y ^ 2 + D * x * z + E * y * z + G * z ^ 2

/-- Half the determinant of the Gram matrix `[[2A,B,D],[B,2C,E],[D,E,2G]]` of `Qf`. -/
def δ (A B C D E G : ℂ) : ℂ := 4 * A * C * G - A * E ^ 2 - B ^ 2 * G + B * D * E - C * D ^ 2

/-- The derivative of the determinant of a symmetric 3×3 matrix (Jacobi's formula). -/
def Jf (a b c d e f a' b' c' d' e' f' : ℂ) : ℂ :=
  (d * f - e ^ 2) * a' + (a * f - c ^ 2) * d' + (a * d - b ^ 2) * f' + 2 * (c * e - b * f) * b' +
    2 * (b * e - c * d) * c' + 2 * (b * c - a * e) * e'

section coord
variable (k : Fin 20 → ℂ) (hk0 : k 0 = 0 ∧ k 1 = 0 ∧ k 2 = 0 ∧ k 3 = 0) (l x y z : ℂ)
include hk0

lemma fC_plane : fC k x y z (l * z) =
    z * Qf (cA k l) (cB k l) (cC k l) (cD k l) (cE k l) (cG k l) x y z := by
  obtain ⟨h0, h1, h2, h3⟩ := hk0
  simp only [fC, Qf, cA, cB, cC, cD, cE, cG, h0, h1, h2, h3]; ring

lemma fx_plane : fx k x y z (l * z) = z * (2 * cA k l * x + cB k l * y + cD k l * z) := by
  obtain ⟨h0, h1, h2, h3⟩ := hk0
  simp only [fx, cA, cB, cD, h0, h1, h2]; ring

lemma fy_plane : fy k x y z (l * z) = z * (cB k l * x + 2 * cC k l * y + cE k l * z) := by
  obtain ⟨h0, h1, h2, h3⟩ := hk0
  simp only [fy, cB, cC, cE, h1, h2, h3]; ring

lemma fz_plane : fz k x y z (l * z) + l * fw k x y z (l * z) =
    Qf (cA k l) (cB k l) (cC k l) (cD k l) (cE k l) (cG k l) x y z +
      z * (cD k l * x + cE k l * y + 2 * cG k l * z) := by
  obtain ⟨h0, h1, h2, h3⟩ := hk0
  simp only [fz, fw, Qf, cA, cB, cC, cD, cE, cG]; ring

end coord

lemma fw_plane (k : Fin 20 → ℂ) (l x y z : ℂ) : fw k x y z (l * z) =
    Qf (dA k l) (dB k l) (dC k l) (dD k l) (dE k l) (dG k l) x y z := by
  simp only [fw, Qf, dA, dB, dC, dD, dE, dG]; ring

def pp (k : Fin 20 → ℂ) : Fin 3 → ℂ := ![k 4 * k 8, k 4 * k 9 + k 5 * k 8, k 5 * k 9]
def qq (k : Fin 20 → ℂ) : Fin 5 → ℂ :=
  ![k 13 ^ 2, 2 * k 13 * k 14, k 14 ^ 2 + 2 * k 13 * k 15, 2 * k 14 * k 15, k 15 ^ 2]
def rr (k : Fin 20 → ℂ) : Fin 3 → ℂ := ![k 6 ^ 2, 2 * k 6 * k 7, k 7 ^ 2]
def ss (k : Fin 20 → ℂ) : Fin 5 → ℂ :=
  ![k 10 * k 13, k 10 * k 14 + k 11 * k 13, k 10 * k 15 + k 11 * k 14 + k 12 * k 13,
    k 11 * k 15 + k 12 * k 14, k 12 * k 15]
def tt (k : Fin 20 → ℂ) : Fin 5 → ℂ :=
  ![k 10 ^ 2, 2 * k 10 * k 11, k 11 ^ 2 + 2 * k 10 * k 12, 2 * k 11 * k 12, k 12 ^ 2]

/-- The coefficients of the discriminant quintic. -/
def cc (k : Fin 20 → ℂ) : Fin 6 → ℂ := ![
  4 * (pp k 0 * k 16) - k 4 * qq k 0 - rr k 0 * k 16 + k 6 * ss k 0 - k 8 * tt k 0,
  4 * (pp k 0 * k 17 + pp k 1 * k 16) - (k 4 * qq k 1 + k 5 * qq k 0)
    - (rr k 0 * k 17 + rr k 1 * k 16) + (k 6 * ss k 1 + k 7 * ss k 0)
    - (k 8 * tt k 1 + k 9 * tt k 0),
  4 * (pp k 0 * k 18 + pp k 1 * k 17 + pp k 2 * k 16) - (k 4 * qq k 2 + k 5 * qq k 1)
    - (rr k 0 * k 18 + rr k 1 * k 17 + rr k 2 * k 16) + (k 6 * ss k 2 + k 7 * ss k 1)
    - (k 8 * tt k 2 + k 9 * tt k 1),
  4 * (pp k 0 * k 19 + pp k 1 * k 18 + pp k 2 * k 17) - (k 4 * qq k 3 + k 5 * qq k 2)
    - (rr k 0 * k 19 + rr k 1 * k 18 + rr k 2 * k 17) + (k 6 * ss k 3 + k 7 * ss k 2)
    - (k 8 * tt k 3 + k 9 * tt k 2),
  4 * (pp k 1 * k 19 + pp k 2 * k 18) - (k 4 * qq k 4 + k 5 * qq k 3)
    - (rr k 1 * k 19 + rr k 2 * k 18) + (k 6 * ss k 4 + k 7 * ss k 3)
    - (k 8 * tt k 4 + k 9 * tt k 3),
  4 * (pp k 2 * k 19) - k 5 * qq k 4 - rr k 2 * k 19 + k 7 * ss k 4 - k 9 * tt k 4]

/-- The discriminant quintic `Δ(λ)`. -/
noncomputable def Δp (k : Fin 20 → ℂ) : Polynomial ℂ :=
  Polynomial.C (cc k 0) + Polynomial.C (cc k 1) * Polynomial.X +
    Polynomial.C (cc k 2) * Polynomial.X ^ 2 + Polynomial.C (cc k 3) * Polynomial.X ^ 3 +
    Polynomial.C (cc k 4) * Polynomial.X ^ 4 + Polynomial.C (cc k 5) * Polynomial.X ^ 5

lemma Δp_eval (k : Fin 20 → ℂ) (l : ℂ) :
    (Δp k).eval l = δ (cA k l) (cB k l) (cC k l) (cD k l) (cE k l) (cG k l) := by
  simp [Δp, cc, pp, qq, rr, ss, tt, δ, cA, cB, cC, cD, cE, cG]
  ring

lemma Δp_deriv (k : Fin 20 → ℂ) (l : ℂ) :
    2 * (Polynomial.derivative (Δp k)).eval l =
      Jf (2 * cA k l) (cB k l) (cD k l) (2 * cC k l) (cE k l) (2 * cG k l)
        (2 * dA k l) (dB k l) (dD k l) (2 * dC k l) (dE k l) (2 * dG k l) := by
  simp only [Δp, Polynomial.derivative_add, Polynomial.derivative_C_mul_X_pow,
    Polynomial.derivative_C_mul_X, Polynomial.derivative_C, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_pow]
  simp [cc, pp, qq, rr, ss, tt, Jf, cA, cB, cC, cD, cE, cG, dA, dB, dC, dD, dE, dG]
  ring

lemma Δp_natDegree (k : Fin 20 → ℂ) : (Δp k).natDegree ≤ 5 := by
  unfold Δp
  compute_degree

lemma Δp_coeff5 (k : Fin 20 → ℂ) : (Δp k).coeff 5 = cc k 5 := by
  simp [Δp, Polynomial.coeff_X_pow]

lemma Δp_coeff4 (k : Fin 20 → ℂ) : (Δp k).coeff 4 = cc k 4 := by
  simp [Δp, Polynomial.coeff_X_pow]

lemma cc_swap0 (k : Fin 20 → ℂ) : cc (fun i => k (σ i)) 0 = cc k 5 := by
  simp [cc, pp, qq, rr, ss, tt, σ]

lemma cc_swap1 (k : Fin 20 → ℂ) : cc (fun i => k (σ i)) 1 = cc k 4 := by
  simp [cc, pp, qq, rr, ss, tt, σ]; ring

lemma Δp_eval_zero (k : Fin 20 → ℂ) : (Δp k).eval 0 = cc k 0 := by simp [Δp]

lemma Δp_deriv_zero (k : Fin 20 → ℂ) : (Polynomial.derivative (Δp k)).eval 0 = cc k 1 := by
  simp [Δp]

/-! ### Linear algebra of ternary quadrics -/

/-- If a conic contains the line through `p̂ = (p₁,p₂,0)` and `m̂ = (m₁,m₂,m₃)` with `m₃ ≠ 0`,
its determinant vanishes. -/
lemma conic_det (A B C D E G p1 p2 m1 m2 m3 : ℂ) (hp : ¬ (p1 = 0 ∧ p2 = 0)) (hm : m3 ≠ 0)
    (h0 : Qf A B C D E G m1 m2 m3 = 0) (h1 : Qf A B C D E G (p1 + m1) (p2 + m2) m3 = 0)
    (h2 : Qf A B C D E G (-p1 + m1) (-p2 + m2) m3 = 0) : δ A B C D E G = 0 := by
  have hQp : Qf A B C D E G p1 p2 0 = 0 := by
    unfold Qf at *; linear_combination (h1 + h2) / 2 - h0
  have hβ : 2 * A * p1 * m1 + B * (p1 * m2 + p2 * m1) + 2 * C * p2 * m2 + D * p1 * m3
      + E * p2 * m3 = 0 := by
    unfold Qf at *; linear_combination (h1 - h2) / 2
  set Qm := Qf A B C D E G m1 m2 m3
  set β := 2 * A * p1 * m1 + B * (p1 * m2 + p2 * m1) + 2 * C * p2 * m2 + D * p1 * m3
      + E * p2 * m3
  have e1 : (p2 * m3) ^ 2 * δ A B C D E G = 0 := by
    have : (p2 * m3) ^ 2 * δ A B C D E G =
        Qf A B C D E G p1 p2 0 * (2 * Qm * (2 * A) - (2 * A * m1 + B * m2 + D * m3) ^ 2)
        - β * (β * (2 * A) - 2 * (2 * A * p1 + B * p2) * (2 * A * m1 + B * m2 + D * m3)) / 2
        - Qm * (2 * A * p1 + B * p2) ^ 2 := by
      simp only [Qm, β, Qf, δ]; ring
    rw [this, hQp, hβ, h0]; ring
  have e2 : (p1 * m3) ^ 2 * δ A B C D E G = 0 := by
    have : (p1 * m3) ^ 2 * δ A B C D E G =
        Qf A B C D E G p1 p2 0 * (2 * Qm * (2 * C) - (B * m1 + 2 * C * m2 + E * m3) ^ 2)
        - β * (β * (2 * C) - 2 * (B * p1 + 2 * C * p2) * (B * m1 + 2 * C * m2 + E * m3)) / 2
        - Qm * (B * p1 + 2 * C * p2) ^ 2 := by
      simp only [Qm, β, Qf, δ]; ring
    rw [this, hQp, hβ, h0]; ring
  by_contra hδ
  apply hp
  constructor
  · have := mul_eq_zero.1 e2
    rcases this with h | h
    · exact (mul_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h)).resolve_right hm
    · exact absurd h hδ
  · have := mul_eq_zero.1 e1
    rcases this with h | h
    · exact (mul_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h)).resolve_right hm
    · exact absurd h hδ

/-- An affine conic that does not contain the line at infinity `z = 0` has a point with `z = 1`. -/
lemma affine_root (A B C D E G : ℂ) (h : ¬ (A = 0 ∧ B = 0 ∧ C = 0)) :
    ∃ a b : ℂ, Qf A B C D E G a b 1 = 0 := by
  by_cases hA : A = 0
  · by_cases hC : C = 0
    · have hB : B ≠ 0 := fun hB => h ⟨hA, hB, hC⟩
      refine ⟨-(E * ((1 - D) / B) + G), (1 - D) / B, ?_⟩
      simp only [Qf, hA, hC]; field_simp; ring
    · obtain ⟨a, b, hab, hq⟩ := quad_root C E G
      have hb : b ≠ 0 := by
        rintro rfl
        rcases hab with ha | hb
        · apply ha; simpa [hC] using hq
        · exact hb rfl
      refine ⟨0, a / b, ?_⟩
      simp only [Qf, hA]; field_simp; linear_combination hq
  · obtain ⟨a, b, hab, hq⟩ := quad_root A D G
    have hb : b ≠ 0 := by
      rintro rfl
      rcases hab with ha | hb
      · apply ha; simpa [hA] using hq
      · exact hb rfl
    refine ⟨a / b, 0, ?_⟩
    simp only [Qf]; field_simp; linear_combination hq

/-- Jacobi's formula is nonzero at a singular symmetric matrix `S₀` when every nonzero kernel
vector `n` of `S₀` has `nᵀ S₁ n ≠ 0`. -/
lemma jac_ne (a b c d e f a' b' c' d' e' f' : ℂ)
    (hdet : a * (d * f - e ^ 2) - b * (b * f - c * e) + c * (b * e - c * d) = 0)
    (H : ∀ n0 n1 n2 : ℂ, ¬ (n0 = 0 ∧ n1 = 0 ∧ n2 = 0) →
      a * n0 + b * n1 + c * n2 = 0 → b * n0 + d * n1 + e * n2 = 0 →
      c * n0 + e * n1 + f * n2 = 0 →
      a' * n0 ^ 2 + d' * n1 ^ 2 + f' * n2 ^ 2 + 2 * b' * n0 * n1 + 2 * c' * n0 * n2
        + 2 * e' * n1 * n2 ≠ 0) :
    Jf a b c d e f a' b' c' d' e' f' ≠ 0 := by
  intro hJ
  set A11 := d * f - e ^ 2
  set A22 := a * f - c ^ 2
  set A33 := a * d - b ^ 2
  set A12 := c * e - b * f
  set A13 := b * e - c * d
  set A23 := b * c - a * e
  by_cases h11 : A11 = 0
  · by_cases h22 : A22 = 0
    · by_cases h33 : A33 = 0
      · -- rank ≤ 1
        have h12 : A12 = 0 := by
          have : A12 ^ 2 = A11 * A22 - (a * (d * f - e ^ 2) - b * (b * f - c * e)
            + c * (b * e - c * d)) * f := by simp only [A11, A22, A12]; ring
          rw [h11, h22, hdet] at this; exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1
            (by rw [this]; ring)
        have h13 : A13 = 0 := by
          have : A13 ^ 2 = A11 * A33 - (a * (d * f - e ^ 2) - b * (b * f - c * e)
            + c * (b * e - c * d)) * d := by simp only [A11, A33, A13]; ring
          rw [h11, h33, hdet] at this; exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1
            (by rw [this]; ring)
        have h23 : A23 = 0 := by
          have : A23 ^ 2 = A22 * A33 - (a * (d * f - e ^ 2) - b * (b * f - c * e)
            + c * (b * e - c * d)) * a := by simp only [A22, A33, A23]; ring
          rw [h22, h33, hdet] at this; exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1
            (by rw [this]; ring)
        by_cases ha : a = 0
        · have hb : b = 0 := by
            have : b ^ 2 = 0 := by linear_combination -h33 + d * ha
            exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
          have hc : c = 0 := by
            have : c ^ 2 = 0 := by linear_combination -h22 + f * ha
            exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
          by_cases hd : d = 0
          · have he : e = 0 := by
              have : e ^ 2 = 0 := by linear_combination -h11 + f * hd
              exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
            obtain ⟨α, β, hαβ, hq⟩ := quad_root a' (2 * b') d'
            refine H α β 0 ?_ ?_ ?_ ?_ ?_
            · rintro ⟨h1, h2, -⟩; rcases hαβ with h | h <;> simp_all
            · rw [ha, hb, hc]; ring
            · rw [hb, hd, he]; ring
            · rw [hc, he]; ring
            · linear_combination hq
          · obtain ⟨α, β, hαβ, hq⟩ := quad_root a' (-2 * b' * e + 2 * c' * d)
              (d' * e ^ 2 + f' * d ^ 2 - 2 * e' * e * d)
            refine H α (-β * e) (β * d) ?_ ?_ ?_ ?_ ?_
            · rintro ⟨h1, -, h3⟩
              rcases hαβ with h | h
              · exact h h1
              · exact h ((mul_eq_zero.1 h3).resolve_right hd)
            · rw [ha, hb, hc]; ring
            · rw [hb]; ring
            · have h11' : d * f - e ^ 2 = 0 := h11
              rw [hc]; linear_combination β * h11'
            · linear_combination hq
        · obtain ⟨α, β, hαβ, hq⟩ := quad_root (a' * b ^ 2 + d' * a ^ 2 - 2 * b' * a * b)
            (2 * a' * b * c - 2 * b' * a * c - 2 * c' * a * b + 2 * e' * a ^ 2)
            (a' * c ^ 2 + f' * a ^ 2 - 2 * c' * a * c)
          refine H (-α * b - β * c) (α * a) (β * a) ?_ ?_ ?_ ?_ ?_
          · rintro ⟨-, h2, h3⟩
            rcases hαβ with h | h
            · exact h ((mul_eq_zero.1 h2).resolve_right ha)
            · exact h ((mul_eq_zero.1 h3).resolve_right ha)
          · ring
          · linear_combination α * h33 - β * h23
          · linear_combination -α * h23 + β * h22
          · linear_combination hq
      · refine H A13 A23 A33 (fun h => h33 h.2.2) ?_ ?_ ?_ ?_
        · simp only [A13, A23, A33]; ring
        · simp only [A13, A23, A33]; ring
        · simp only [A13, A23, A33]; linear_combination hdet
        · have : a' * A13 ^ 2 + d' * A23 ^ 2 + f' * A33 ^ 2 + 2 * b' * A13 * A23
              + 2 * c' * A13 * A33 + 2 * e' * A23 * A33 =
              A33 * Jf a b c d e f a' b' c' d' e' f' +
              (a * (d * f - e ^ 2) - b * (b * f - c * e) + c * (b * e - c * d)) *
                (2 * b' * b - a' * d - d' * a) := by
            simp only [A13, A23, A33, Jf]; ring
          rw [this, hJ, hdet]; ring
    · refine H A12 A22 A23 (fun h => h22 h.2.1) ?_ ?_ ?_ ?_
      · simp only [A12, A22, A23]; ring
      · simp only [A12, A22, A23]; linear_combination hdet
      · simp only [A12, A22, A23]; ring
      · have : a' * A12 ^ 2 + d' * A22 ^ 2 + f' * A23 ^ 2 + 2 * b' * A12 * A22
            + 2 * c' * A12 * A23 + 2 * e' * A22 * A23 =
            A22 * Jf a b c d e f a' b' c' d' e' f' +
            (a * (d * f - e ^ 2) - b * (b * f - c * e) + c * (b * e - c * d)) *
              (2 * c' * c - a' * f - f' * a) := by
          simp only [A12, A22, A23, Jf]; ring
        rw [this, hJ, hdet]; ring
  · refine H A11 A12 A13 (fun h => h11 h.1) ?_ ?_ ?_ ?_
    · simp only [A11, A12, A13]; linear_combination hdet
    · simp only [A11, A12, A13]; ring
    · simp only [A11, A12, A13]; ring
    · have : a' * A11 ^ 2 + d' * A12 ^ 2 + f' * A13 ^ 2 + 2 * b' * A11 * A12
          + 2 * c' * A11 * A13 + 2 * e' * A12 * A13 =
          A11 * Jf a b c d e f a' b' c' d' e' f' +
          (a * (d * f - e ^ 2) - b * (b * f - c * e) + c * (b * e - c * d)) *
            (2 * e' * e - d' * f - f' * d) := by
        simp only [A11, A12, A13, Jf]; ring
      rw [this, hJ, hdet]; ring

/-! ### Planes through `L` and the residual conic -/

section planes
variable {F : MvPolynomial (Fin 4) ℂ} {L : Submodule ℂ (Fin 4 → ℂ)}

/-- The plane `L ⊔ ℂ (v₂ + λ v₃)`. -/
def Setup.Pl (S : Setup F L) (l : ℂ) : Submodule ℂ (Fin 4 → ℂ) := L ⊔ ℂ ∙ (S.v2 + l • S.v3)

/-- A plane through `L` contains a second line. -/
def Special (F : MvPolynomial (Fin 4) ℂ) (L P : Submodule ℂ (Fin 4 → ℂ)) : Prop :=
  ∃ M ∈ linesOf F, M ≤ P ∧ M ≠ L

lemma Setup.memPl (S : Setup F L) (l : ℂ) (x : Fin 4 → ℂ) :
    x ∈ S.Pl l ↔ ∃ a b c : ℂ, x = a • S.v0 + b • S.v1 + c • (S.v2 + l • S.v3) := by
  unfold Setup.Pl
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩
    obtain ⟨a, b, rfl⟩ := (S.hLmem y).1 hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
    exact ⟨a, b, c, rfl⟩
  · rintro ⟨a, b, c, rfl⟩
    exact ⟨a • S.v0 + b • S.v1, (S.hLmem _).2 ⟨a, b, rfl⟩, c • (S.v2 + l • S.v3),
      Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), rfl⟩

lemma Setup.evalPl (S : Setup F L) (l a b c : ℂ) :
    eval (a • S.v0 + b • S.v1 + c • (S.v2 + l • S.v3)) F =
      c * Qf (cA S.k l) (cB S.k l) (cC S.k l) (cD S.k l) (cE S.k l) (cG S.k l) a b c := by
  rw [show a • S.v0 + b • S.v1 + c • (S.v2 + l • S.v3) =
    a • S.v0 + b • S.v1 + c • S.v2 + (l * c) • S.v3 by module, S.hk, fC_plane S.k S.hk0]

lemma Setup.coord_inL (S : Setup F L) (l a b c : ℂ)
    (h : a • S.v0 + b • S.v1 + c • (S.v2 + l • S.v3) ∈ L) : c = 0 := by
  obtain ⟨a', b', h'⟩ := (S.hLmem _).1 h
  have := S.hind (a - a') (b - b') c (l * c) (by rw [← sub_eq_zero.2 h']; module)
  exact this.2.2.1

lemma Setup.w_notin (S : Setup F L) (l : ℂ) : S.v2 + l • S.v3 ∉ L := by
  intro h
  have := S.coord_inL l 0 0 1 (by simpa using h)
  exact one_ne_zero this

lemma finrank_sup_singleton (L : Submodule ℂ (Fin 4 → ℂ)) (hL : Module.finrank ℂ L = 2)
    (u : Fin 4 → ℂ) (hu : u ∉ L) : Module.finrank ℂ (L ⊔ ℂ ∙ u : Submodule ℂ (Fin 4 → ℂ)) = 3 := by
  have hu0 : u ≠ 0 := fun h => hu (h ▸ L.zero_mem)
  have hdis : Disjoint L (ℂ ∙ u) := (Submodule.disjoint_span_singleton' hu0).2 hu
  have h := Submodule.finrank_sup_add_finrank_inf_eq L (ℂ ∙ u)
  rw [hdis.eq_bot, finrank_bot, hL, finrank_span_singleton hu0] at h
  omega

/-- A plane through `L` tangent along `L` would force a singular point. -/
lemma Setup.not_tangent (S : Setup F L) (hF : IsCubicForm F) (hsm : IsSmoothCubic F) (l : ℂ)
    (hA : cA S.k l = 0) (hB : cB S.k l = 0) (hC : cC S.k l = 0) : False := by
  obtain ⟨h0, h1, h2, h3⟩ := S.hk0
  obtain ⟨x, y, hxy, hq⟩ := quad_root (S.k 5) (S.k 7) (S.k 9)
  unfold cA at hA; unfold cB at hB; unfold cC at hC
  refine S.smooth hF hsm x y 0 0 ?_ ?_ ?_ ?_ ?_ ?_
  · rintro ⟨hx, hy, -⟩; rcases hxy with h | h <;> simp_all
  · simp only [fC, h0, h1, h2, h3]; ring
  · simp only [fx, h0, h1, h2]; ring
  · simp only [fy, h1, h2, h3]; ring
  · simp only [fz]
    linear_combination x ^ 2 * hA + x * y * hB + y ^ 2 * hC - l * hq
  · simp only [fw]; linear_combination hq

/-- Smoothness at a kernel vector of the conic's Gram matrix. -/
lemma Setup.kernel_ne (S : Setup F L) (hF : IsCubicForm F) (hsm : IsSmoothCubic F) (l : ℂ)
    (n0 n1 n2 : ℂ) (hn : ¬ (n0 = 0 ∧ n1 = 0 ∧ n2 = 0))
    (r0 : 2 * cA S.k l * n0 + cB S.k l * n1 + cD S.k l * n2 = 0)
    (r1 : cB S.k l * n0 + 2 * cC S.k l * n1 + cE S.k l * n2 = 0)
    (r2 : cD S.k l * n0 + cE S.k l * n1 + 2 * cG S.k l * n2 = 0) :
    2 * dA S.k l * n0 ^ 2 + 2 * dC S.k l * n1 ^ 2 + 2 * dG S.k l * n2 ^ 2
      + 2 * dB S.k l * n0 * n1 + 2 * dD S.k l * n0 * n2 + 2 * dE S.k l * n1 * n2 ≠ 0 := by
  intro hz
  have hQ : Qf (cA S.k l) (cB S.k l) (cC S.k l) (cD S.k l) (cE S.k l) (cG S.k l) n0 n1 n2 = 0 := by
    unfold Qf; linear_combination n0 / 2 * r0 + n1 / 2 * r1 + n2 / 2 * r2
  have hw : fw S.k n0 n1 n2 (l * n2) = 0 := by
    rw [fw_plane]; unfold Qf; linear_combination hz / 2
  refine S.smooth hF hsm n0 n1 n2 (l * n2) ?_ ?_ ?_ ?_ ?_ hw
  · rintro ⟨h0, h1, h2, -⟩; exact hn ⟨h0, h1, h2⟩
  · rw [fC_plane S.k S.hk0, hQ, mul_zero]
  · rw [fx_plane S.k S.hk0, r0, mul_zero]
  · rw [fy_plane S.k S.hk0, r1, mul_zero]
  · have := fz_plane S.k S.hk0 l n0 n1 n2
    rw [hw, hQ, r2] at this
    linear_combination this

/-- Every root of the discriminant quintic is simple. -/
lemma Setup.simple_root (S : Setup F L) (hF : IsCubicForm F) (hsm : IsSmoothCubic F) (l : ℂ)
    (h : (Δp S.k).eval l = 0) : (Polynomial.derivative (Δp S.k)).eval l ≠ 0 := by
  intro hd
  have h2 := Δp_deriv S.k l
  rw [hd, mul_zero] at h2
  rw [Δp_eval] at h
  refine jac_ne _ _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ h2.symm
  · unfold δ at h; linear_combination 2 * h
  · intro n0 n1 n2 hn e0 e1 e2 hz
    apply S.kernel_ne hF hsm l n0 n1 n2 hn e0 e1 e2
    linear_combination hz

/-- `F` vanishes on the span of two independent vectors: a line. -/
lemma line_of_pair (F : MvPolynomial (Fin 4) ℂ) (p q : Fin 4 → ℂ)
    (hind : ∀ s t : ℂ, s • p + t • q = 0 → s = 0 ∧ t = 0)
    (hvan : ∀ s t : ℂ, eval (s • p + t • q) F = 0) :
    Submodule.span ℂ (Set.range ![p, q]) ∈ linesOf F := by
  have hli : LinearIndependent ℂ ![p, q] := LinearIndependent.pair_iff.2 hind
  refine ⟨?_, ?_⟩
  · rw [finrank_span_eq_card hli]; simp
  · intro z hz
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hz
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    exact hvan _ _

lemma Setup.special_iff (S : Setup F L) (hF : IsCubicForm F) (hsm : IsSmoothCubic F)
    (hL : L ∈ linesOf F) (l : ℂ) : Special F L (S.Pl l) ↔ (Δp S.k).eval l = 0 := by
  rw [Δp_eval]
  set A := cA S.k l
  set B := cB S.k l
  set C := cC S.k l
  set D := cD S.k l
  set E := cE S.k l
  set G := cG S.k l
  have hP3 : Module.finrank ℂ (S.Pl l) = 3 := finrank_sup_singleton L hL.1 _ (S.w_notin l)
  constructor
  · rintro ⟨M, hM, hMP, hML⟩
    have hLP : L ≤ S.Pl l := le_sup_left
    have hLM : L ⊓ M ≠ ⊥ := by
      intro h
      have h1 := Submodule.finrank_sup_add_finrank_inf_eq L M
      rw [h, finrank_bot, hL.1, hM.1] at h1
      have h2 := Submodule.finrank_mono (sup_le hLP hMP)
      rw [hP3] at h2
      omega
    obtain ⟨p, ⟨hpL, hpM⟩, hp0⟩ := (Submodule.ne_bot_iff _).1 hLM
    obtain ⟨p1, p2, rfl⟩ := (S.hLmem p).1 hpL
    have hp12 : ¬ (p1 = 0 ∧ p2 = 0) := by
      rintro ⟨rfl, rfl⟩; exact hp0 (by simp)
    obtain ⟨m, hmM, hmL⟩ : ∃ m ∈ M, m ∉ L := by
      by_contra h
      push Not at h
      exact hML (Submodule.eq_of_le_of_finrank_eq h (by rw [hM.1, hL.1]))
    obtain ⟨m1, m2, m3, rfl⟩ := (S.memPl l m).1 (hMP hmM)
    have hm3 : m3 ≠ 0 := by
      rintro rfl
      apply hmL
      simpa using (S.hLmem _).2 ⟨m1, m2, rfl⟩
    have hs : ∀ s : ℂ, Qf A B C D E G (s * p1 + m1) (s * p2 + m2) m3 = 0 := by
      intro s
      have hv := hM.2 _ (M.add_mem (M.smul_mem s hpM) hmM)
      rw [show s • (p1 • S.v0 + p2 • S.v1) + (m1 • S.v0 + m2 • S.v1 + m3 • (S.v2 + l • S.v3)) =
        (s * p1 + m1) • S.v0 + (s * p2 + m2) • S.v1 + m3 • (S.v2 + l • S.v3) by module,
        S.evalPl] at hv
      exact (mul_eq_zero.1 hv).resolve_left hm3
    have e0 := hs 0
    have e1 := hs 1
    have e2 := hs (-1)
    simp only [zero_mul, zero_add, one_mul, neg_one_mul] at e0 e1 e2
    exact conic_det A B C D E G p1 p2 m1 m2 m3 hp12 hm3 e0 e1 e2
  · intro hδ
    -- a kernel vector of the Gram matrix
    have hdet : (!![2 * A, B, D; B, 2 * C, E; D, E, 2 * G] : Matrix (Fin 3) (Fin 3) ℂ).det = 0 := by
      rw [Matrix.det_fin_three]
      simp
      unfold δ at hδ
      linear_combination 2 * hδ
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    have r0 : 2 * A * v 0 + B * v 1 + D * v 2 = 0 := by
      have := congrFun hv 0
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this
    have r1 : B * v 0 + 2 * C * v 1 + E * v 2 = 0 := by
      have := congrFun hv 1
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this
    have r2 : D * v 0 + E * v 1 + 2 * G * v 2 = 0 := by
      have := congrFun hv 2
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this
    have hn : ¬ (v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 0) := by
      rintro ⟨h0, h1, h2⟩
      apply hv0
      funext i; fin_cases i <;> simp [h0, h1, h2]
    have hnt : ¬ (A = 0 ∧ B = 0 ∧ C = 0) := fun h => S.not_tangent hF hsm l h.1 h.2.1 h.2.2
    -- a second point `x` of the conic, independent of `v`
    obtain ⟨x0, x1, x2, hQx, hind2, hthird⟩ : ∃ x0 x1 x2 : ℂ, Qf A B C D E G x0 x1 x2 = 0 ∧
        (∀ s t : ℂ, s * v 0 + t * x0 = 0 → s * v 1 + t * x1 = 0 → s * v 2 + t * x2 = 0 →
          s = 0 ∧ t = 0) ∧ (v 2 ≠ 0 ∨ x2 ≠ 0) := by
      by_cases h2 : v 2 = 0
      · obtain ⟨a, b, hab⟩ := affine_root A B C D E G hnt
        refine ⟨a, b, 1, hab, ?_, Or.inr one_ne_zero⟩
        intro s t e0 e1 e2
        rw [h2] at e2
        have ht : t = 0 := by simpa using e2
        subst ht
        simp only [zero_mul, add_zero, mul_eq_zero] at e0 e1
        by_contra hs
        have hs' : s ≠ 0 := fun h => hs ⟨h, rfl⟩
        exact hn ⟨e0.resolve_left hs', e1.resolve_left hs', h2⟩
      · obtain ⟨a, b, hab, hq⟩ := quad_root A B C
        refine ⟨a, b, 0, by unfold Qf; linear_combination hq, ?_, Or.inl h2⟩
        intro s t e0 e1 e2
        have hs : s = 0 := by simpa [h2] using e2
        subst hs
        simp only [zero_mul, zero_add, mul_eq_zero] at e0 e1
        refine ⟨rfl, ?_⟩
        by_contra ht
        rcases hab with h | h
        · exact h (e0.resolve_left ht)
        · exact h (e1.resolve_left ht)
    set w := S.v2 + l • S.v3
    set pn := v 0 • S.v0 + v 1 • S.v1 + v 2 • w
    set px := x0 • S.v0 + x1 • S.v1 + x2 • w
    have hcomb : ∀ s t : ℂ, s • pn + t • px = (s * v 0 + t * x0) • S.v0 + (s * v 1 + t * x1) • S.v1
        + (s * v 2 + t * x2) • w := by
      intro s t; simp only [pn, px]; module
    refine ⟨Submodule.span ℂ (Set.range ![pn, px]), ?_, ?_, ?_⟩
    · refine line_of_pair F pn px ?_ ?_
      · intro s t h
        rw [hcomb] at h
        have := S.hind (s * v 0 + t * x0) (s * v 1 + t * x1) (s * v 2 + t * x2)
          (l * (s * v 2 + t * x2)) (by rw [← h]; simp only [w]; module)
        exact hind2 s t this.1 this.2.1 this.2.2.1
      · intro s t
        rw [hcomb, S.evalPl]
        have : Qf A B C D E G (s * v 0 + t * x0) (s * v 1 + t * x1) (s * v 2 + t * x2) = 0 := by
          unfold Qf at hQx ⊢
          linear_combination (s ^ 2 * v 0 / 2 + s * t * x0) * r0 +
            (s ^ 2 * v 1 / 2 + s * t * x1) * r1 + (s ^ 2 * v 2 / 2 + s * t * x2) * r2 + t ^ 2 * hQx
        rw [this, mul_zero]
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact (S.memPl l _).2 ⟨_, _, _, rfl⟩
      · exact (S.memPl l _).2 ⟨_, _, _, rfl⟩
    · intro hEq
      rcases hthird with h | h
      · apply h
        have : pn ∈ L := hEq ▸ Submodule.subset_span ⟨0, rfl⟩
        exact S.coord_inL l _ _ _ this
      · apply h
        have : px ∈ L := hEq ▸ Submodule.subset_span ⟨1, rfl⟩
        exact S.coord_inL l _ _ _ this

end planes


/-! ### Root counting (from the `Sol_HA_quintic` prototype) -/

lemma card_roots_of_simple (p : Polynomial ℂ) (hp : p ≠ 0)
    (hs : ∀ r, p.IsRoot r → (Polynomial.derivative p).eval r ≠ 0) :
    p.roots.toFinset.card = p.natDegree := by
  have hnd : p.roots.Nodup := by
    rw [Multiset.nodup_iff_count_le_one]
    intro r
    rw [Polynomial.count_roots]
    by_cases hr : p.IsRoot r
    · have h2 : ¬ 1 < p.rootMultiplicity r := by
        intro h
        rw [Polynomial.one_lt_rootMultiplicity_iff_isRoot hp] at h
        exact hs r hr h.2
      omega
    · rw [Polynomial.rootMultiplicity_eq_zero hr]; omega
  rw [Multiset.toFinset_card_of_nodup hnd]
  exact (IsAlgClosed.splits p).natDegree_eq_card_roots.symm

lemma five_roots (p : Polynomial ℂ) (hdeg : p.natDegree ≤ 5) (hp : p ≠ 0)
    (hs : ∀ r, p.IsRoot r → (Polynomial.derivative p).eval r ≠ 0)
    (hinf : p.coeff 5 = 0 → p.coeff 4 ≠ 0) :
    p.roots.toFinset.card + (if p.coeff 5 = 0 then 1 else 0) = 5 := by
  rw [card_roots_of_simple p hp hs]
  split_ifs with h5
  · have h4 : p.natDegree = 4 := by
      apply le_antisymm
      · by_contra h; push Not at h
        have : p.natDegree = 5 := by omega
        rw [← this] at h5; exact hp (Polynomial.leadingCoeff_eq_zero.1 h5)
      · exact Polynomial.le_natDegree_of_ne_zero (hinf h5)
    omega
  · have : p.natDegree = 5 := le_antisymm hdeg (Polynomial.le_natDegree_of_ne_zero h5)
    omega

/-! ### Existence of an adapted basis -/

lemma exists_setup (F : MvPolynomial (Fin 4) ℂ) (hF : IsCubicForm F)
    (L : Submodule ℂ (Fin 4 → ℂ)) (hL : L ∈ linesOf F) : Nonempty (Setup F L) := by
  let b := Module.finBasisOfFinrankEq ℂ L hL.1
  obtain ⟨L', hc⟩ := Submodule.exists_isCompl L
  have hL' : Module.finrank ℂ L' = 2 := by
    have := Submodule.finrank_add_eq_of_isCompl hc
    rw [hL.1, Module.finrank_fin_fun] at this
    omega
  let b' := Module.finBasisOfFinrankEq ℂ L' hL'
  set v0 : Fin 4 → ℂ := ((b 0 : L) : Fin 4 → ℂ)
  set v1 : Fin 4 → ℂ := ((b 1 : L) : Fin 4 → ℂ)
  set v2 : Fin 4 → ℂ := ((b' 0 : L') : Fin 4 → ℂ)
  set v3 : Fin 4 → ℂ := ((b' 1 : L') : Fin 4 → ℂ)
  have memL : ∀ x, x ∈ L ↔ ∃ a c : ℂ, x = a • v0 + c • v1 := by
    intro x
    constructor
    · intro hx
      have := b.sum_repr ⟨x, hx⟩
      rw [Fin.sum_univ_two] at this
      exact ⟨b.repr ⟨x, hx⟩ 0, b.repr ⟨x, hx⟩ 1, by
        have h := congrArg Subtype.val this
        simpa [v0, v1] using h.symm⟩
    · rintro ⟨a, c, rfl⟩
      exact L.add_mem (L.smul_mem a (b 0).2) (L.smul_mem c (b 1).2)
  have memL' : ∀ x, x ∈ L' ↔ ∃ a c : ℂ, x = a • v2 + c • v3 := by
    intro x
    constructor
    · intro hx
      have := b'.sum_repr ⟨x, hx⟩
      rw [Fin.sum_univ_two] at this
      exact ⟨b'.repr ⟨x, hx⟩ 0, b'.repr ⟨x, hx⟩ 1, by
        have h := congrArg Subtype.val this
        simpa [v2, v3] using h.symm⟩
    · rintro ⟨a, c, rfl⟩
      exact L'.add_mem (L'.smul_mem a (b' 0).2) (L'.smul_mem c (b' 1).2)
  have ind2 : ∀ (bb : Module.Basis (Fin 2) ℂ L) (a c : ℂ),
      a • (bb 0 : Fin 4 → ℂ) + c • (bb 1 : Fin 4 → ℂ) = 0 → a = 0 ∧ c = 0 := by
    intro bb a c h
    have h' : a • bb 0 + c • bb 1 = 0 := Subtype.ext (by simpa using h)
    have := Fintype.linearIndependent_iff.1 bb.linearIndependent ![a, c]
      (by simpa [Fin.sum_univ_two] using h')
    exact ⟨this 0, this 1⟩
  have ind2' : ∀ (bb : Module.Basis (Fin 2) ℂ L') (a c : ℂ),
      a • (bb 0 : Fin 4 → ℂ) + c • (bb 1 : Fin 4 → ℂ) = 0 → a = 0 ∧ c = 0 := by
    intro bb a c h
    have h' : a • bb 0 + c • bb 1 = 0 := Subtype.ext (by simpa using h)
    have := Fintype.linearIndependent_iff.1 bb.linearIndependent ![a, c]
      (by simpa [Fin.sum_univ_two] using h')
    exact ⟨this 0, this 1⟩
  obtain ⟨k, hk⟩ := expand4 F hF v0 v1 v2 v3
  have hk0 : k 0 = 0 ∧ k 1 = 0 ∧ k 2 = 0 ∧ k 3 = 0 := by
    have hA : ∀ a c : ℂ, k 0 * a ^ 3 + k 1 * a ^ 2 * c + k 2 * a * c ^ 2 + k 3 * c ^ 3 = 0 := by
      intro a c
      have h := hk a c 0 0
      have hmem : a • v0 + c • v1 + (0:ℂ) • v2 + (0:ℂ) • v3 ∈ L :=
        (memL _).2 ⟨a, c, by simp⟩
      rw [hL.2 _ hmem] at h
      simp only [fC] at h
      linear_combination -h
    have k0 : k 0 = 0 := by linear_combination hA 1 0
    have k3 : k 3 = 0 := by linear_combination hA 0 1
    refine ⟨k0, ?_, ?_, k3⟩
    · linear_combination (hA 1 1 - hA 1 (-1)) / 2 - k3
    · linear_combination (hA 1 1 + hA 1 (-1)) / 2 - k0
  refine ⟨⟨v0, v1, v2, v3, k, ?_, ?_, memL, hk, hk0⟩⟩
  · intro a c d e h
    have hu : a • v0 + c • v1 ∈ L := (memL _).2 ⟨a, c, rfl⟩
    have hu' : d • v2 + e • v3 ∈ L' := (memL' _).2 ⟨d, e, rfl⟩
    have heq : a • v0 + c • v1 = -(d • v2 + e • v3) := by
      rw [← sub_eq_zero, sub_neg_eq_add, ← h]; abel
    have h0 : a • v0 + c • v1 = 0 := by
      have hmem : a • v0 + c • v1 ∈ L ⊓ L' := ⟨hu, heq ▸ L'.neg_mem hu'⟩
      rw [hc.inf_eq_bot] at hmem
      exact hmem
    have h0' : d • v2 + e • v3 = 0 := by
      rw [h0, eq_comm, neg_eq_zero] at heq; exact heq
    exact ⟨(ind2 b a c h0).1, (ind2 b a c h0).2, (ind2' b' d e h0').1, (ind2' b' d e h0').2⟩
  · intro x
    have hx : x ∈ L ⊔ L' := by rw [hc.sup_eq_top]; trivial
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨a, c, rfl⟩ := (memL y).1 hy
    obtain ⟨d, e, rfl⟩ := (memL' z).1 hz
    exact ⟨a, c, d, e, by abel⟩

/-! ### Classification of planes through `L` -/

section classify
variable {F : MvPolynomial (Fin 4) ℂ} {L : Submodule ℂ (Fin 4 → ℂ)}

lemma Setup.classify (S : Setup F L) (hL2 : Module.finrank ℂ L = 2)
    (P : Submodule ℂ (Fin 4 → ℂ)) (hP : Module.finrank ℂ P = 3) (hLP : L ≤ P) :
    (∃ l, P = S.Pl l) ∨ P = S.swap.Pl 0 := by
  obtain ⟨u, huP, huL⟩ : ∃ u ∈ P, u ∉ L := by
    by_contra h
    push Not at h
    have := Submodule.finrank_mono (show P ≤ L from h)
    omega
  obtain ⟨a, b, c, d, rfl⟩ := S.hspan u
  have key : ∀ (w : Fin 4 → ℂ) (Q : Submodule ℂ (Fin 4 → ℂ)), Q = L ⊔ ℂ ∙ w → w ∉ L → w ∈ P →
      P = Q := by
    intro w Q hQ hw hwP
    symm
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rw [hQ]; exact sup_le hLP ((Submodule.span_singleton_le_iff_mem _ _).2 hwP)
    · rw [hQ, finrank_sup_singleton L hL2 w hw, hP]
  have hab : a • S.v0 + b • S.v1 ∈ P := hLP ((S.hLmem _).2 ⟨a, b, rfl⟩)
  by_cases hc : c = 0
  · right
    have hd : d ≠ 0 := by
      rintro rfl
      apply huL
      rw [hc]; simpa using (S.hLmem _).2 ⟨a, b, rfl⟩
    refine key _ _ rfl (S.swap.w_notin 0) ?_
    have : S.swap.v2 + (0:ℂ) • S.swap.v3 =
        d⁻¹ • ((a • S.v0 + b • S.v1 + c • S.v2 + d • S.v3) - (a • S.v0 + b • S.v1)) := by
      simp only [Setup.swap, hc]
      rw [show a • S.v0 + b • S.v1 + (0:ℂ) • S.v2 + d • S.v3 - (a • S.v0 + b • S.v1) = d • S.v3
        by module, smul_smul, inv_mul_cancel₀ hd]
      simp
    rw [this]
    exact P.smul_mem _ (P.sub_mem huP hab)
  · left
    refine ⟨d / c, key _ _ rfl (S.w_notin _) ?_⟩
    have : S.v2 + (d / c) • S.v3 =
        c⁻¹ • ((a • S.v0 + b • S.v1 + c • S.v2 + d • S.v3) - (a • S.v0 + b • S.v1)) := by
      rw [show a • S.v0 + b • S.v1 + c • S.v2 + d • S.v3 - (a • S.v0 + b • S.v1) =
        c • S.v2 + d • S.v3 by module, smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hc,
        one_smul, div_eq_inv_mul]
    rw [this]
    exact P.smul_mem _ (P.sub_mem huP hab)

lemma Setup.Pl_inj (S : Setup F L) : Function.Injective S.Pl := by
  intro l m h
  have hm : S.v2 + m • S.v3 ∈ S.Pl l := h ▸ Submodule.mem_sup_right
    (Submodule.mem_span_singleton_self _)
  obtain ⟨a, b, c, habc⟩ := (S.memPl l _).1 hm
  have := S.hind (-a) (-b) (1 - c) (m - c * l) (by
    rw [show (0 : Fin 4 → ℂ) = S.v2 + m • S.v3 - (a • S.v0 + b • S.v1 + c • (S.v2 + l • S.v3))
      by rw [← habc, sub_self]]
    module)
  have hc : c = 1 := by linear_combination -this.2.2.1
  have := this.2.2.2
  rw [hc] at this
  linear_combination -this

lemma Setup.inf_ne (S : Setup F L) (l : ℂ) : S.swap.Pl 0 ≠ S.Pl l := by
  intro h
  have hm : S.swap.v2 + (0:ℂ) • S.swap.v3 ∈ S.Pl l := h ▸ Submodule.mem_sup_right
    (Submodule.mem_span_singleton_self _)
  simp only [Setup.swap, zero_smul, add_zero] at hm
  obtain ⟨a, b, c, habc⟩ := (S.memPl l _).1 hm
  have := S.hind (-a) (-b) (-c) (1 - c * l) (by
    rw [show (0 : Fin 4 → ℂ) = S.v3 - (a • S.v0 + b • S.v1 + c • (S.v2 + l • S.v3))
      by rw [← habc, sub_self]]
    module)
  have hc : c = 0 := by linear_combination -this.2.2.1
  have := this.2.2.2
  rw [hc] at this
  simp at this

end classify

end FPAux

open CubicSurface27 FPAux in
theorem solution (F : MvPolynomial (Fin 4) ℂ)
    (hF : IsCubicForm F) (hsm : IsSmoothCubic F)
    (L : Submodule ℂ (Fin 4 → ℂ)) (hL : L ∈ linesOf F) :
    {P : Submodule ℂ (Fin 4 → ℂ) | Module.finrank ℂ P = 3 ∧ L ≤ P ∧
      ∃ M ∈ linesOf F, M ≤ P ∧ M ≠ L}.ncard = 5 := by
  obtain ⟨S⟩ := exists_setup F hF L hL
  set p := Δp S.k with hp
  have hroot : ∀ r, p.IsRoot r → (Polynomial.derivative p).eval r ≠ 0 :=
    fun r hr => S.simple_root hF hsm r hr
  have hp0 : p ≠ 0 := by
    intro h
    have h1 : p.IsRoot 0 := by rw [h]; simp
    apply hroot 0 h1
    rw [h]; simp
  have hc5 : p.coeff 5 = cc S.k 5 := Δp_coeff5 S.k
  have hinf_iff : Special F L (S.swap.Pl 0) ↔ cc S.k 5 = 0 := by
    rw [S.swap.special_iff hF hsm hL, Δp_eval_zero]
    exact Iff.of_eq (congrArg (· = (0:ℂ)) (cc_swap0 S.k))
  have hinf : p.coeff 5 = 0 → p.coeff 4 ≠ 0 := by
    intro h5
    rw [hc5] at h5
    rw [hp, Δp_coeff4]
    have h0 : (Δp S.swap.k).eval 0 = 0 := by
      rw [Δp_eval_zero]; exact (cc_swap0 S.k).trans h5
    have := S.swap.simple_root hF hsm 0 h0
    rw [Δp_deriv_zero] at this
    exact fun h4 => this ((cc_swap1 S.k).trans h4)
  have hfive := five_roots p (Δp_natDegree S.k) hp0 hroot hinf
  rw [hc5] at hfive
  have hPl3 : ∀ l, Module.finrank ℂ (S.Pl l) = 3 :=
    fun l => finrank_sup_singleton L hL.1 _ (S.w_notin l)
  have hinf3 : Module.finrank ℂ (S.swap.Pl 0) = 3 :=
    finrank_sup_singleton L hL.1 _ (S.swap.w_notin 0)
  let R := p.roots.toFinset.image S.Pl
  have hmemR : ∀ P, P ∈ R ↔ ∃ l, p.IsRoot l ∧ P = S.Pl l := by
    intro P
    simp only [R, Finset.mem_image, Multiset.mem_toFinset, Polynomial.mem_roots hp0]
    constructor
    · rintro ⟨l, hl, rfl⟩; exact ⟨l, hl, rfl⟩
    · rintro ⟨l, hl, rfl⟩; exact ⟨l, hl, rfl⟩
  have hRcard : R.card = p.roots.toFinset.card := Finset.card_image_of_injective _ S.Pl_inj
  have hnotR : S.swap.Pl 0 ∉ R := by
    rw [hmemR]; rintro ⟨l, -, hl⟩; exact S.inf_ne l hl
  let T : Finset (Submodule ℂ (Fin 4 → ℂ)) := if cc S.k 5 = 0 then insert (S.swap.Pl 0) R else R
  have hset : {P : Submodule ℂ (Fin 4 → ℂ) | Module.finrank ℂ P = 3 ∧ L ≤ P ∧
      ∃ M ∈ linesOf F, M ≤ P ∧ M ≠ L} = ↑T := by
    ext P
    simp only [Set.mem_ofPred_eq, Finset.mem_coe]
    change _ ∧ _ ∧ Special F L P ↔ _
    constructor
    · rintro ⟨hP, hLP, hsp⟩
      rcases S.classify hL.1 P hP hLP with ⟨l, rfl⟩ | rfl
      · have hl : p.IsRoot l := (S.special_iff hF hsm hL l).1 hsp
        have : S.Pl l ∈ R := (hmemR _).2 ⟨l, hl, rfl⟩
        simp only [T]; split_ifs
        · exact Finset.mem_insert_of_mem this
        · exact this
      · have h5 := hinf_iff.1 hsp
        simp only [T, if_pos h5]
        exact Finset.mem_insert_self _ _
    · intro hPT
      have hR : P ∈ R → Module.finrank ℂ P = 3 ∧ L ≤ P ∧ Special F L P := by
        intro hPR
        obtain ⟨l, hl, rfl⟩ := (hmemR P).1 hPR
        exact ⟨hPl3 l, le_sup_left, (S.special_iff hF hsm hL l).2 hl⟩
      simp only [T] at hPT
      split_ifs at hPT with h5
      · rcases Finset.mem_insert.1 hPT with rfl | hPR
        · exact ⟨hinf3, le_sup_left, hinf_iff.2 h5⟩
        · exact hR hPR
      · exact hR hPT
  rw [hset, Set.ncard_coe_finset]
  simp only [T]
  split_ifs with h5
  · rw [Finset.card_insert_of_notMem hnotR, hRcard]
    simpa [h5] using hfive
  · rw [hRcard]
    simpa [h5] using hfive
