-- Prove2me | solution 1 for FiniteEnergyPlane.bracket_le_of_norm_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-23T16:08:02.475532+00:00
-- url     : https://prove2.me/submissions/1a223037-9f76-406f-86cf-f5f5aa13d7b5

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Basic



namespace FiniteEnergyPlane

/-- Let `J₀` be a complex structure (`J₀² = -1`, `‖J₀‖ ≤ β`) on a real inner product space and
`g(v, v') = ⟪v, v'⟫ + ⟪J₀ v, J₀ v'⟫`. For an operator `A` with `‖A - J₀‖ ≤ ε` and vectors `w, x`,
with `γ = 1 + β²`:
`g(w, x) g(J₀ w, A x) - g(w, A x) g(J₀ w, x) ≤ g(w, w) g(x, x) (1 + 2 γ² β ε)` and
`g(x, x) (1 - γ β ε) ≤ g(J₀ x, A x)`. -/
theorem bracket_le_of_norm_sub_le_aux {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (J₀ A : F →L[ℝ] F) (hJ : J₀.comp J₀ = -ContinuousLinearMap.id ℝ F) {β ε : ℝ}
    (hβ : ‖J₀‖ ≤ β) (hε : ‖A - J₀‖ ≤ ε) (w x : F) :
    (inner ℝ w x + inner ℝ (J₀ w) (J₀ x)) *
        (inner ℝ (J₀ w) (A x) + inner ℝ (J₀ (J₀ w)) (J₀ (A x))) -
      (inner ℝ w (A x) + inner ℝ (J₀ w) (J₀ (A x))) *
        (inner ℝ (J₀ w) x + inner ℝ (J₀ (J₀ w)) (J₀ x)) ≤
      (inner ℝ w w + inner ℝ (J₀ w) (J₀ w)) * (inner ℝ x x + inner ℝ (J₀ x) (J₀ x)) *
        (1 + 2 * (1 + β ^ 2) ^ 2 * β * ε) ∧
    (inner ℝ x x + inner ℝ (J₀ x) (J₀ x)) * (1 - (1 + β ^ 2) * β * ε) ≤
      inner ℝ (J₀ x) (A x) + inner ℝ (J₀ (J₀ x)) (J₀ (A x)) := by
  have hJJ : ∀ v, J₀ (J₀ v) = -v := fun v => by
    simpa using congrArg (fun T : F →L[ℝ] F => T v) hJ
  set g : F → F → ℝ := fun v v' => inner ℝ v v' + inner ℝ (J₀ v) (J₀ v') with hg
  have hβ0 : 0 ≤ β := (norm_nonneg _).trans hβ
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hε
  have hJn : ∀ v, ‖J₀ v‖ ≤ β * ‖v‖ := fun v =>
    (J₀.le_opNorm v).trans (mul_le_mul_of_nonneg_right hβ (norm_nonneg _))
  -- basic identities for `g`
  have gN : ∀ v, g v v = ‖v‖ ^ 2 + ‖J₀ v‖ ^ 2 := fun v => by
    simp [hg, real_inner_self_eq_norm_sq]
  have gsymm : ∀ v v', g v v' = g v' v := fun v v' => by
    simp [hg, real_inner_comm]
  have gJ : ∀ v v', g (J₀ v) (J₀ v') = g v v' := fun v v' => by
    simp only [hg, hJJ, inner_neg_neg]; ring
  have gJ' : ∀ v v', g v (J₀ v') = -g (J₀ v) v' := fun v v' => by
    rw [← gJ v (J₀ v'), hJJ]; simp [hg, inner_neg_right]; ring
  have gadd_left : ∀ a b v v' x, g (a • v + b • v') x = a * g v x + b * g v' x := by
    intro a b v v' x
    simp only [hg, map_add, map_smul, inner_add_left, inner_smul_left]; simp; ring
  have gadd_right : ∀ x v v', g x (v + v') = g x v + g x v' := by
    intro x v v'
    simp only [hg, map_add, inner_add_right]; ring
  -- Cauchy–Schwarz for `g`
  have gcs : ∀ v v', g v v' ^ 2 ≤ g v v * g v' v' := by
    intro v v'
    rw [gN, gN]
    have h1 := abs_real_inner_le_norm v v'
    have h2 := abs_real_inner_le_norm (J₀ v) (J₀ v')
    have : |g v v'| ≤ ‖v‖ * ‖v'‖ + ‖J₀ v‖ * ‖J₀ v'‖ := (abs_add_le _ _).trans (add_le_add h1 h2)
    have h3 : g v v' ^ 2 ≤ (‖v‖ * ‖v'‖ + ‖J₀ v‖ * ‖J₀ v'‖) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
    nlinarith [sq_nonneg (‖v‖ * ‖J₀ v'‖ - ‖J₀ v‖ * ‖v'‖)]
  have gle : ∀ v v', |g v v'| ≤ (1 + β ^ 2) * ‖v‖ * ‖v'‖ := by
    intro v v'
    have h1 := abs_real_inner_le_norm v v'
    have h2 := abs_real_inner_le_norm (J₀ v) (J₀ v')
    have h4 : ‖J₀ v‖ * ‖J₀ v'‖ ≤ β * ‖v‖ * (β * ‖v'‖) :=
      mul_le_mul (hJn v) (hJn v') (norm_nonneg _) (by positivity)
    calc |g v v'| ≤ ‖v‖ * ‖v'‖ + ‖J₀ v‖ * ‖J₀ v'‖ := (abs_add_le _ _).trans (add_le_add h1 h2)
      _ ≤ (1 + β ^ 2) * ‖v‖ * ‖v'‖ := by nlinarith
  have gge : ∀ v, ‖v‖ ^ 2 ≤ g v v := fun v => by rw [gN]; nlinarith [sq_nonneg ‖J₀ v‖]
  -- Bessel: `g(w,x)² + g(J₀w,x)² ≤ g(w,w) g(x,x)`
  have bessel : g w x ^ 2 + g (J₀ w) x ^ 2 ≤ g w w * g x x := by
    set a1 := g w x
    set a2 := g (J₀ w) x
    set v := a1 • w + a2 • J₀ w
    have hv1 : g v x = a1 ^ 2 + a2 ^ 2 := by rw [gadd_left]; ring
    have hww : g w (J₀ w) = 0 := by
      have := gJ' w w; rw [gsymm (J₀ w) w] at this; linarith
    have hv2 : g v v = g w w * (a1 ^ 2 + a2 ^ 2) := by
      have e1 : g v v = a1 * g w v + a2 * g (J₀ w) v := gadd_left _ _ _ _ _
      have e2 : g w v = a1 * g w w + a2 * g w (J₀ w) := by
        rw [gsymm, gadd_left, gsymm w w, gsymm (J₀ w) w]
      have e3 : g (J₀ w) v = a1 * g (J₀ w) w + a2 * g (J₀ w) (J₀ w) := by
        rw [gsymm, gadd_left, gsymm w (J₀ w), gsymm (J₀ w) (J₀ w)]
      rw [e1, e2, e3, gJ, gsymm (J₀ w) w, hww]; ring
    have hcs := gcs v x
    rw [hv1, hv2] at hcs
    have hS : 0 ≤ a1 ^ 2 + a2 ^ 2 := by positivity
    have hx0 : 0 ≤ g x x := (sq_nonneg _).trans (gge x)
    rcases hS.lt_or_eq with hS | hS
    · nlinarith
    · rw [← hS]; exact mul_nonneg ((sq_nonneg _).trans (gge w)) hx0
  -- the error operator
  set D := A - J₀ with hD
  have hAx : A x = J₀ x + D x := by simp [hD]
  have hDx : ‖D x‖ ≤ ε * ‖x‖ :=
    (D.le_opNorm x).trans (mul_le_mul_of_nonneg_right hε (norm_nonneg _))
  have hγ : 0 ≤ 1 + β ^ 2 := by positivity
  have hJw : ‖J₀ w‖ ≤ β * ‖w‖ := hJn w
  have hJx : ‖J₀ x‖ ≤ β * ‖x‖ := hJn x
  have hw2 := gge w
  have hx2 := gge x
  refine ⟨?_, ?_⟩
  · -- the bracket
    show g w x * g (J₀ w) (A x) - g w (A x) * g (J₀ w) x ≤ g w w * g x x * _
    rw [hAx, gadd_right, gadd_right, gJ, gJ' w x]
    have e1 : |g (J₀ w) (D x)| ≤ (1 + β ^ 2) * (β * ‖w‖) * (ε * ‖x‖) :=
      (gle _ _).trans (mul_le_mul (mul_le_mul_of_nonneg_left hJw hγ) hDx (norm_nonneg _)
        (by positivity))
    have e2 : |g w (D x)| ≤ (1 + β ^ 2) * ‖w‖ * (ε * ‖x‖) :=
      (gle _ _).trans (mul_le_mul_of_nonneg_left hDx (by positivity))
    have e3 : |g w x| ≤ (1 + β ^ 2) * ‖w‖ * ‖x‖ := gle _ _
    have e4 : |g (J₀ w) x| ≤ (1 + β ^ 2) * (β * ‖w‖) * ‖x‖ :=
      (gle _ _).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hJw hγ)
        (norm_nonneg _))
    have p1 : g w x * g (J₀ w) (D x) ≤
        (1 + β ^ 2) ^ 2 * β * ε * (‖w‖ ^ 2 * ‖x‖ ^ 2) := by
      have := abs_mul (g w x) (g (J₀ w) (D x)) ▸
        mul_le_mul e3 e1 (abs_nonneg _) (by positivity)
      nlinarith [le_abs_self (g w x * g (J₀ w) (D x))]
    have p2 : -(g w (D x) * g (J₀ w) x) ≤
        (1 + β ^ 2) ^ 2 * β * ε * (‖w‖ ^ 2 * ‖x‖ ^ 2) := by
      have := abs_mul (g w (D x)) (g (J₀ w) x) ▸
        mul_le_mul e2 e4 (abs_nonneg _) (by positivity)
      nlinarith [neg_abs_le (g w (D x) * g (J₀ w) x)]
    have hwx : ‖w‖ ^ 2 * ‖x‖ ^ 2 ≤ g w w * g x x :=
      mul_le_mul hw2 hx2 (by positivity) ((sq_nonneg _).trans hw2)
    have hk : 0 ≤ (1 + β ^ 2) ^ 2 * β * ε := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hwx hk]
  · -- the area density
    show g x x * _ ≤ g (J₀ x) (A x)
    rw [hAx, gadd_right, gJ]
    have e1 : |g (J₀ x) (D x)| ≤ (1 + β ^ 2) * (β * ‖x‖) * (ε * ‖x‖) :=
      (gle _ _).trans (mul_le_mul (mul_le_mul_of_nonneg_left hJx hγ) hDx (norm_nonneg _)
        (by positivity))
    have hk : 0 ≤ (1 + β ^ 2) * β * ε := by positivity
    have : -((1 + β ^ 2) * β * ε * g x x) ≤ g (J₀ x) (D x) := by
      have h1 := neg_abs_le (g (J₀ x) (D x))
      nlinarith [mul_le_mul_of_nonneg_left hx2 hk]
    nlinarith

end FiniteEnergyPlane

open FiniteEnergyPlane

theorem solution {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (J₀ A : F →L[ℝ] F) (hJ : J₀.comp J₀ = -ContinuousLinearMap.id ℝ F) {β ε : ℝ}
    (hβ : ‖J₀‖ ≤ β) (hε : ‖A - J₀‖ ≤ ε) (w x : F) :
    (inner ℝ w x + inner ℝ (J₀ w) (J₀ x)) *
        (inner ℝ (J₀ w) (A x) + inner ℝ (J₀ (J₀ w)) (J₀ (A x))) -
      (inner ℝ w (A x) + inner ℝ (J₀ w) (J₀ (A x))) *
        (inner ℝ (J₀ w) x + inner ℝ (J₀ (J₀ w)) (J₀ x)) ≤
      (inner ℝ w w + inner ℝ (J₀ w) (J₀ w)) * (inner ℝ x x + inner ℝ (J₀ x) (J₀ x)) *
        (1 + 2 * (1 + β ^ 2) ^ 2 * β * ε) ∧
    (inner ℝ x x + inner ℝ (J₀ x) (J₀ x)) * (1 - (1 + β ^ 2) * β * ε) ≤
      inner ℝ (J₀ x) (A x) + inner ℝ (J₀ (J₀ x)) (J₀ (A x)) :=
  bracket_le_of_norm_sub_le_aux J₀ A hJ hβ hε w x
