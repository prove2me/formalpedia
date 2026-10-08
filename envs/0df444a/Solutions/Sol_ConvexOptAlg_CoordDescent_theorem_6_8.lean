-- Prove2me | solution 1 for ConvexOptAlg.CoordDescent.theorem_6_8
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T17:35:44.854986+00:00
-- url     : https://prove2.me/submissions/17dd47a4-fc09-462c-ada5-6a0d8501800d

/-
Bubeck, Convex Optimization: Algorithms and Complexity, Theorem 6.8: random coordinate descent RCD(γ) on an
`α`-strongly convex (for the norm `‖·‖_[1-γ]`), coordinate-smooth function satisfies
`E f(x_{t+1}) - f(x*) ≤ (1 - 1/κ_γ)^t (f(x_1) - f(x*))`, with `κ_γ = (∑ β_i^γ)/α`.

One step (`rcd_point`): coordinate smoothness gives `f(x - ∇_i f(x)/β_i e_i) ≤ f(x) - (∇_i f(x))²/(2β_i)` (proved along
the line `x + s u e_i`). Averaging over `i ~ p_γ` gives the decrease `(1/(2S)) ∑ (∇_i f)²/β_i^{1-γ}`, `S = ∑ β_j^γ`,
and strong convexity at `x*` with the per-coordinate bound `g d - (α/2) w d² ≤ g²/(2 α w)` gives
`∑ (∇_i f)²/β_i^{1-γ} ≥ 2α (f(x) - f(x*))`. Hence the expected value after one step satisfies
`E f(x⁺) - f* ≤ (1 - 1/κ)(f(x) - f*)`. The expectation over the `t` drawn coordinates is split with
`Fin.snoc` (`sum_snoc`) and the recursion is iterated (`rcd_main`; `decay_aux` handles the sign of `1 - 1/κ`).
-/
import Mathlib
import Definitions.Def_ConvexOptAlg_CoordDescent_Defs

set_option autoImplicit false

namespace GDLib

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem line_deriv {f : E → ℝ} {g : E → E} (hg : ∀ z, HasGradientAt f (g z) z) (x d : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (x + s • d)) (inner ℝ (g (x + t • d)) d) t := by
  have h1 : HasDerivAt (fun s : ℝ => x + s • d) d t := by
    simpa using ((hasDerivAt_id t).smul_const d).const_add x
  have h2 := (hg (x + t • d)).hasFDerivAt
  have := h2.comp_hasDerivAt t h1
  simp only [InnerProductSpace.toDual_apply_apply] at this
  exact this

/-- First-order condition for a convex differentiable function. -/
theorem first_order {f : E → ℝ} {g : E → E} (hg : ∀ z, HasGradientAt f (g z) z)
    (hconv : ConvexOn ℝ Set.univ f) (x y : E) : f x + inner ℝ (g x) (y - x) ≤ f y := by
  have hc : ConvexOn ℝ Set.univ (fun s : ℝ => f (x + s • (y - x))) := by
    have := hconv.comp_affineMap (AffineMap.lineMap x y : ℝ →ᵃ[ℝ] E)
    have e : (fun s : ℝ => f (x + s • (y - x))) = f ∘ ⇑(AffineMap.lineMap x y : ℝ →ᵃ[ℝ] E) := by
      funext s; simp [AffineMap.lineMap_apply, add_comm]
    rw [e]
    simpa using this
  have hd := line_deriv hg x (y - x) 0
  simp only [zero_smul, add_zero] at hd
  have := hc.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one hd
  simp [slope_def_field] at this
  linarith


open ConvexOptAlg.CoordDescent in
theorem coord_quad {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} {β : Fin n → ℝ}
    (hg : ∀ z, HasGradientAt f (g z) z)
    (hL : ∀ (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) (u : ℝ),
      |g (x + u • EuclideanSpace.single i 1) i - g x i| ≤ β i * |u|) (i : Fin n)
    (x : EuclideanSpace ℝ (Fin n)) (u : ℝ) :
    f (x + u • EuclideanSpace.single i 1) ≤ f x + g x i * u + β i / 2 * u ^ 2 := by
  set d : EuclideanSpace ℝ (Fin n) := u • EuclideanSpace.single i 1 with hd
  have hin : ∀ z, inner ℝ (g z) d = u * g z i := by
    intro z
    simp [hd, inner_smul_right, EuclideanSpace.inner_single_right, mul_comm]
  set ψ : ℝ → ℝ := fun t => f (x + t • d) - f x - t * (g x i * u) - β i / 2 * t ^ 2 * u ^ 2 with hψ
  have hψd : ∀ t, HasDerivAt ψ (u * g (x + t • d) i - g x i * u - β i * t * u ^ 2) t := by
    intro t
    have h1 := line_deriv hg x d t
    rw [hin] at h1
    have h2 : HasDerivAt (fun t : ℝ => t * (g x i * u)) (g x i * u) t := by
      simpa using (hasDerivAt_id t).mul_const (g x i * u)
    have h3 : HasDerivAt (fun t : ℝ => β i / 2 * t ^ 2 * u ^ 2) (β i * t * u ^ 2) t := by
      refine (((hasDerivAt_pow 2 t).const_mul (β i / 2)).mul_const (u ^ 2)).congr_deriv ?_
      rw [show (2 - 1 : ℕ) = 1 from rfl]
      push_cast
      ring
    exact (((h1.sub (hasDerivAt_const t (f x))).sub h2).sub h3).congr_deriv (by ring)
  have hanti : AntitoneOn ψ (Set.Icc 0 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 1) (fun t _ => (hψd t).continuousAt.continuousWithinAt)
      (fun t _ => (hψd t).differentiableAt.differentiableWithinAt) (fun t ht => ?_)
    rw [(hψd t).deriv]
    have ht0 : 0 ≤ t := (interior_subset ht).1
    have h := hL i x (t * u)
    have e : x + (t * u) • EuclideanSpace.single i (1 : ℝ) = x + t • d := by
      simp [hd, smul_smul]
    rw [e, abs_mul, abs_of_nonneg ht0] at h
    have h2 : u * (g (x + t • d) i - g x i) ≤ |u| * (β i * (t * |u|)) := by
      calc u * (g (x + t • d) i - g x i) ≤ |u * (g (x + t • d) i - g x i)| := le_abs_self _
        _ = |u| * |g (x + t • d) i - g x i| := abs_mul _ _
        _ ≤ |u| * (β i * (t * |u|)) := by gcongr
    have h3 : |u| * (β i * (t * |u|)) = β i * t * u ^ 2 := by
      have : |u| * |u| = u ^ 2 := by rw [← sq, sq_abs]
      calc |u| * (β i * (t * |u|)) = β i * t * (|u| * |u|) := by ring
        _ = β i * t * u ^ 2 := by rw [this]
    nlinarith [h2, h3]
  have := hanti (Set.mem_Icc.2 ⟨le_rfl, zero_le_one⟩) (Set.mem_Icc.2 ⟨zero_le_one, le_rfl⟩) zero_le_one
  simp only [hψ] at this
  simp at this
  linarith

open ConvexOptAlg.CoordDescent in
theorem rcd_point {n : ℕ} (hn : 0 < n) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} {β : Fin n → ℝ} {γ α : ℝ}
    (hβ : ∀ i, 0 < β i) (hα : 0 < α) (hsc : IsStronglyConvexWNorm f g β (1 - γ) α)
    (hsm : IsCoordSmooth f g β) (xs : EuclideanSpace ℝ (Fin n)) (hmin : ∀ y, f xs ≤ f y)
    (x : EuclideanSpace ℝ (Fin n)) :
    ∑ i, pGamma β γ i * f (rcdStep β g x i) ≤ f x - 1 / kappa β γ α * (f x - f xs) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set S : ℝ := ∑ j, β j ^ γ with hS
  have hSpos : 0 < S := Finset.sum_pos (fun j _ => Real.rpow_pos_of_pos (hβ j) γ) Finset.univ_nonempty
  have hp : ∀ i, pGamma β γ i = β i ^ γ / S := fun i => rfl
  have hpsum : ∑ i, pGamma β γ i = 1 := by
    simp only [hp, ← Finset.sum_div]; exact div_self hSpos.ne'
  have hpnn : ∀ i, 0 ≤ pGamma β γ i := fun i => by
    rw [hp]; exact div_nonneg (Real.rpow_pos_of_pos (hβ i) γ).le hSpos.le
  -- one coordinate step
  have hstep : ∀ i, f (rcdStep β g x i) ≤ f x - g x i ^ 2 / (2 * β i) := by
    intro i
    have h := coord_quad hsm.1 hsm.2 i x (-(1 / β i * g x i))
    have e : rcdStep β g x i = x + (-(1 / β i * g x i)) • EuclideanSpace.single i (1 : ℝ) := by
      simp [rcdStep, sub_eq_add_neg, neg_smul]
    rw [e]
    have hb := (hβ i).ne'
    have e2 : g x i * (-(1 / β i * g x i)) + β i / 2 * (-(1 / β i * g x i)) ^ 2 = - (g x i ^ 2 / (2 * β i)) := by
      field_simp; ring
    linarith
  -- strong convexity gives a lower bound on the squared dual gradient norm
  have hw : ∀ i, β i ^ (1 - γ) = β i / β i ^ γ := fun i => by
    rw [Real.rpow_sub (hβ i), Real.rpow_one]
  have hwpos : ∀ i, 0 < β i ^ (1 - γ) := fun i => Real.rpow_pos_of_pos (hβ i) _
  have hlow : 2 * α * (f x - f xs) ≤ ∑ i, g x i ^ 2 / β i ^ (1 - γ) := by
    have h := hsc.2 x xs
    have hnn : 0 ≤ ∑ i, β i ^ (1 - γ) * (x i - xs i) ^ 2 :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (hwpos i).le (sq_nonneg _))
    have hnorm : wnorm β (1 - γ) (x - xs) ^ 2 = ∑ i, β i ^ (1 - γ) * (x i - xs i) ^ 2 := by
      unfold wnorm
      rw [Real.sq_sqrt (by simpa using hnn)]
      simp
    rw [hnorm] at h
    have hi : ∀ i, g x i * (x i - xs i) - α / 2 * (β i ^ (1 - γ) * (x i - xs i) ^ 2) ≤
        g x i ^ 2 / β i ^ (1 - γ) / (2 * α) := by
      intro i
      have hw0 := hwpos i
      have : 0 ≤ (α * β i ^ (1 - γ) * (x i - xs i) - g x i) ^ 2 := sq_nonneg _
      rw [div_div, le_div_iff₀ (by positivity)]
      nlinarith [this]
    have hsum : ∑ i, (g x i * (x i - xs i) - α / 2 * (β i ^ (1 - γ) * (x i - xs i) ^ 2)) ≤
        ∑ i, g x i ^ 2 / β i ^ (1 - γ) / (2 * α) := Finset.sum_le_sum (fun i _ => hi i)
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
    have h2 : f x - f xs ≤ ∑ i, g x i ^ 2 / β i ^ (1 - γ) / (2 * α) := by linarith
    rw [← Finset.sum_div] at h2
    rw [le_div_iff₀ (by positivity)] at h2
    linarith
  -- expectation of one step
  have hexp : ∑ i, pGamma β γ i * f (rcdStep β g x i) ≤
      f x - (1 / (2 * S)) * ∑ i, g x i ^ 2 / β i ^ (1 - γ) := by
    calc ∑ i, pGamma β γ i * f (rcdStep β g x i)
        ≤ ∑ i, pGamma β γ i * (f x - g x i ^ 2 / (2 * β i)) :=
          Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hstep i) (hpnn i))
      _ = f x - (1 / (2 * S)) * ∑ i, g x i ^ 2 / β i ^ (1 - γ) := by
          have e : ∀ i, pGamma β γ i * (f x - g x i ^ 2 / (2 * β i)) =
              pGamma β γ i * f x - (1 / (2 * S)) * (g x i ^ 2 / β i ^ (1 - γ)) := by
            intro i
            have hb := (hβ i).ne'
            have hg0 := (Real.rpow_pos_of_pos (hβ i) γ).ne'
            rw [hp, hw]
            field_simp
          simp only [e, Finset.sum_sub_distrib, ← Finset.sum_mul, hpsum, ← Finset.mul_sum]
          ring
  have hk : 1 / kappa β γ α = α / S := by
    unfold kappa; rw [← hS]; field_simp
  rw [hk]
  have : α / S * (f x - f xs) ≤ (1 / (2 * S)) * ∑ i, g x i ^ 2 / β i ^ (1 - γ) := by
    have e : α / S * (f x - f xs) = (1 / (2 * S)) * (2 * α * (f x - f xs)) := by field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left hlow (by positivity)
  linarith

/-- A decay lemma for a nonnegative sequence with `a (t+1) ≤ q * a t`. -/
theorem decay_aux (a : ℕ → ℝ) (q : ℝ) (h0 : ∀ t, 0 ≤ a t) (hrec : ∀ t, a (t + 1) ≤ q * a t) :
    ∀ t, a t ≤ q ^ t * a 0 := by
  by_cases ha : a 0 = 0
  · have : ∀ t, a t = 0 := by
      intro t
      induction t with
      | zero => exact ha
      | succ t ih =>
        have := hrec t
        rw [ih, mul_zero] at this
        exact le_antisymm this (h0 _)
    intro t; rw [this t, ha, mul_zero]
  · have hpos : 0 < a 0 := lt_of_le_of_ne (h0 0) (Ne.symm ha)
    have hq : 0 ≤ q := by
      have := hrec 0
      have h1 := h0 1
      by_contra hneg
      push Not at hneg
      nlinarith
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      calc a (t + 1) ≤ q * a t := hrec t
        _ ≤ q * (q ^ t * a 0) := mul_le_mul_of_nonneg_left ih hq
        _ = q ^ (t + 1) * a 0 := by ring

open ConvexOptAlg.CoordDescent in
/-- The product weights of `rcdExpect` sum to one. -/
theorem rcd_weight_sum {n : ℕ} (β : Fin n → ℝ) (γ : ℝ) (hn : 0 < n) (hβ : ∀ i, 0 < β i) (t : ℕ) :
    ∑ idx : Fin t → Fin n, ∏ s, pGamma β γ (idx s) = 1 := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hSpos : 0 < ∑ j, β j ^ γ :=
    Finset.sum_pos (fun j _ => Real.rpow_pos_of_pos (hβ j) γ) Finset.univ_nonempty
  have hpsum : ∑ i, pGamma β γ i = 1 := by
    simp only [pGamma, ← Finset.sum_div]; exact div_self hSpos.ne'
  have := Finset.prod_univ_sum (fun (_ : Fin t) => (Finset.univ : Finset (Fin n)))
    (fun _ j => pGamma β γ j)
  rw [Fintype.piFinset_univ] at this
  rw [← this]
  simp [hpsum]

/-- Sum over `Fin (t+1) → Fin n` split into the first `t` coordinates and the last one. -/
theorem sum_snoc {n t : ℕ} (G : (Fin (t + 1) → Fin n) → ℝ) :
    ∑ idx : Fin (t + 1) → Fin n, G idx =
      ∑ a : Fin t → Fin n, ∑ i : Fin n, G (Fin.snoc (α := fun _ => Fin n) a i) := by
  let e : (Fin t → Fin n) × Fin n ≃ (Fin (t + 1) → Fin n) :=
    { toFun := fun p => Fin.snoc (α := fun _ => Fin n) p.1 p.2
      invFun := fun idx => (Fin.init idx, idx (Fin.last t))
      left_inv := fun p => by simp
      right_inv := fun idx => by simp }
  rw [← e.sum_comp, Fintype.sum_prod_type]
  rfl

open ConvexOptAlg.CoordDescent in
theorem rcd_main {n : ℕ} (hn : 0 < n) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} {β : Fin n → ℝ} {γ α : ℝ}
    (hβ : ∀ i, 0 < β i) (hα : 0 < α) (hsc : IsStronglyConvexWNorm f g β (1 - γ) α)
    (hsm : IsCoordSmooth f g β) (xs : EuclideanSpace ℝ (Fin n)) (hmin : ∀ y, f xs ≤ f y)
    (x₁ : EuclideanSpace ℝ (Fin n)) (t : ℕ) :
    rcdExpect β γ t (fun idx => f (rcdIter β g x₁ t idx)) - f xs ≤
      (1 - 1 / kappa β γ α) ^ t * (f x₁ - f xs) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hSpos : 0 < ∑ j, β j ^ γ :=
    Finset.sum_pos (fun j _ => Real.rpow_pos_of_pos (hβ j) γ) Finset.univ_nonempty
  have hpnn : ∀ i, 0 ≤ pGamma β γ i := fun i =>
    div_nonneg (Real.rpow_pos_of_pos (hβ i) γ).le hSpos.le
  have hwnn : ∀ (t : ℕ) (a : Fin t → Fin n), 0 ≤ ∏ s, pGamma β γ (a s) :=
    fun t a => Finset.prod_nonneg (fun s _ => hpnn _)
  set E : ℕ → ℝ := fun t => rcdExpect β γ t (fun idx => f (rcdIter β g x₁ t idx)) with hE
  set q : ℝ := 1 - 1 / kappa β γ α with hq
  have hE0 : E 0 = f x₁ := by
    simp [hE, rcdExpect, rcdIter]
  -- E t ≥ f xs
  have hEge : ∀ t, f xs ≤ E t := by
    intro t
    have h1 := rcd_weight_sum β γ hn hβ t
    calc f xs = ∑ a : Fin t → Fin n, (∏ s, pGamma β γ (a s)) * f xs := by
          rw [← Finset.sum_mul, h1, one_mul]
      _ ≤ E t := by
          simp only [hE, rcdExpect]
          exact Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hmin _) (hwnn t a))
  have hrec : ∀ t, E (t + 1) - f xs ≤ q * (E t - f xs) := by
    intro t
    have h1 := rcd_weight_sum β γ hn hβ t
    have hsplit : E (t + 1) = ∑ a : Fin t → Fin n, (∏ s, pGamma β γ (a s)) *
        ∑ i, pGamma β γ i * f (rcdStep β g (rcdIter β g x₁ t a) i) := by
      simp only [hE, rcdExpect]
      rw [sum_snoc]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Fin.prod_univ_castSucc]
      simp [rcdIter, mul_assoc]
    have hle : E (t + 1) ≤ ∑ a : Fin t → Fin n, (∏ s, pGamma β γ (a s)) *
        (f (rcdIter β g x₁ t a) - 1 / kappa β γ α * (f (rcdIter β g x₁ t a) - f xs)) := by
      rw [hsplit]
      exact Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left
        (rcd_point hn hβ hα hsc hsm xs hmin _) (hwnn t a))
    have hrhs : ∑ a : Fin t → Fin n, (∏ s, pGamma β γ (a s)) *
        (f (rcdIter β g x₁ t a) - 1 / kappa β γ α * (f (rcdIter β g x₁ t a) - f xs)) =
        q * E t + (1 / kappa β γ α) * f xs := by
      have e : ∀ a : Fin t → Fin n, (∏ s, pGamma β γ (a s)) *
          (f (rcdIter β g x₁ t a) - 1 / kappa β γ α * (f (rcdIter β g x₁ t a) - f xs)) =
          q * ((∏ s, pGamma β γ (a s)) * f (rcdIter β g x₁ t a)) +
            (1 / kappa β γ α) * f xs * (∏ s, pGamma β γ (a s)) := by
        intro a; rw [hq]; ring
      simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, h1, mul_one]
      rfl
    rw [hrhs] at hle
    rw [hq] at hle ⊢
    nlinarith [hle]
  have hdec := decay_aux (fun t => E t - f xs) q (fun t => sub_nonneg.2 (hEge t)) hrec t
  simpa [hE0] using hdec

end GDLib

open ConvexOptAlg.CoordDescent in
theorem solution {n : ℕ} (hn : 0 < n) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : Fin n → ℝ) (γ α : ℝ)
    (hγ : 0 ≤ γ) (hβ : ∀ i, 0 < β i) (hα : 0 < α)
    (hsc : IsStronglyConvexWNorm f g β (1 - γ) α) (hsm : IsCoordSmooth f g β)
    (xstar : EuclideanSpace ℝ (Fin n)) (hmin : ∀ y, f xstar ≤ f y)
    (x₁ : EuclideanSpace ℝ (Fin n)) (t : ℕ) :
    rcdExpect β γ t (fun idx => f (rcdIter β g x₁ t idx)) - f xstar ≤
      (1 - 1 / kappa β γ α) ^ t * (f x₁ - f xstar) :=
  GDLib.rcd_main hn hβ hα hsc hsm xstar hmin x₁ t
