-- Prove2me | solution 1 for CondatPD.FB.lemma_4_5
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T07:19:18.535988+00:00
-- url     : https://prove2.me/submissions/f3cbc9c6-14d5-4f3c-8807-dfaeb82f318b

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_Nonexpansive
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators

set_option autoImplicit false

open InnerProductSpace

open scoped RealInnerProductSpace in
theorem bh_inner_grad {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (z w : E) : ⟪gradient f z, w⟫ = fderiv ℝ f z w := by
  simp [gradient, InnerProductSpace.toDual_symm_apply]

open scoped RealInnerProductSpace in
theorem bh_line_deriv {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {f : E → ℝ} (hdiff : Differentiable ℝ f) (y w : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (y + s • w)) ⟪gradient f (y + t • w), w⟫ t := by
  have hl : HasDerivAt (fun s : ℝ => y + s • w) w t := by
    simpa using ((hasDerivAt_id t).smul_const w).const_add y
  have := (hdiff (y + t • w)).hasFDerivAt.comp_hasDerivAt t hl
  rw [bh_inner_grad]
  exact this

open scoped RealInnerProductSpace in
theorem bh_descent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {f : E → ℝ} {L : ℝ} (hdiff : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) (x y : E) :
    f y ≤ f x + ⟪gradient f x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2 := by
  set w := y - x
  let g : ℝ → ℝ := fun t => f (x + t • w) - t * ⟪gradient f x, w⟫ - L / 2 * t ^ 2 * ‖w‖ ^ 2
  have hg : ∀ t, HasDerivAt g (⟪gradient f (x + t • w), w⟫ - ⟪gradient f x, w⟫
      - L / 2 * (2 * t) * ‖w‖ ^ 2) t := by
    intro t
    have h1 := bh_line_deriv hdiff x w t
    have h2 : HasDerivAt (fun s : ℝ => s * ⟪gradient f x, w⟫) ⟪gradient f x, w⟫ t := by
      simpa using (hasDerivAt_id t).mul_const ⟪gradient f x, w⟫
    have h3 : HasDerivAt (fun s : ℝ => L / 2 * s ^ 2 * ‖w‖ ^ 2) (L / 2 * (2 * t) * ‖w‖ ^ 2) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (L / 2)).mul_const (‖w‖ ^ 2)
      simpa using this
    exact (h1.sub h2).sub h3
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope g _ (zero_lt_one' ℝ)
    (fun t _ => (hg t).continuousAt.continuousWithinAt) (fun t _ => hg t)
  have hle : ⟪gradient f (x + c • w), w⟫ - ⟪gradient f x, w⟫ - L / 2 * (2 * c) * ‖w‖ ^ 2 ≤ 0 := by
    have e1 : ⟪gradient f (x + c • w), w⟫ - ⟪gradient f x, w⟫ =
        ⟪gradient f (x + c • w) - gradient f x, w⟫ := by rw [inner_sub_left]
    have e2 := real_inner_le_norm (gradient f (x + c • w) - gradient f x) w
    have e3 := hgrad (x + c • w) x
    have e4 : ‖x + c • w - x‖ = c * ‖w‖ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hc.1]
    rw [e4] at e3
    have : ‖gradient f (x + c • w) - gradient f x‖ * ‖w‖ ≤ L * (c * ‖w‖) * ‖w‖ :=
      mul_le_mul_of_nonneg_right e3 (norm_nonneg _)
    nlinarith
  rw [hcd] at hle
  have : g 1 ≤ g 0 := by
    have := hle; simp only [sub_zero, div_one] at this; linarith
  simp only [g, one_smul, zero_smul, add_zero, one_mul, zero_mul, one_pow, sub_zero,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at this
  have hw : x + w = y := by simp [w]
  rw [hw] at this
  linarith

open scoped RealInnerProductSpace in
theorem bh_convex_fo {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f)
    (x y : E) : f x + ⟪gradient f x, y - x⟫ ≤ f y := by
  set w := y - x
  have hφ : ConvexOn ℝ Set.univ (fun t : ℝ => f (x + t • w)) := by
    have := hf.comp_affineMap (AffineMap.lineMap x y)
    simp only [Set.preimage_univ] at this
    have e : (fun t : ℝ => f (x + t • w)) = f ∘ AffineMap.lineMap x y := by
      funext t
      simp [AffineMap.lineMap_apply, w, add_comm]
    rw [e]; exact this
  have h := hφ.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one
    (by simpa using bh_line_deriv hdiff x w 0)
  rw [slope_def_field] at h
  simp only [zero_smul, add_zero, one_smul, sub_zero, div_one] at h
  have hw : x + w = y := by simp [w]
  rw [hw] at h
  rw [bh_inner_grad]
  linarith


/-- Descent lemma: a convex function whose subgradient selection is nonexpansive
is majorized by its tangent plus `½‖w - z‖²`. -/
theorem bh_mdescent {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (p : H → H) (φ : H → ℝ) (hL : ∀ z w, ‖p z - p w‖ ≤ ‖z - w‖)
    (hs : ∀ z u, φ z + ⟪u - z, p z⟫_ℝ ≤ φ u) (z w : H) :
    φ w - φ z - ⟪w - z, p z⟫_ℝ ≤ ‖w - z‖ ^ 2 / 2 := by
  have step : ∀ n : ℕ, ∀ z w : H,
      φ w - φ z - ⟪w - z, p z⟫_ℝ ≤ (1 / 2 + (1 / 2 : ℝ) ^ (n + 1)) * ‖w - z‖ ^ 2 := by
    intro n
    induction n with
    | zero =>
      intro z w
      have h1 := hs w z
      have h2 : ⟪z - w, p w⟫_ℝ = -⟪w - z, p w⟫_ℝ := by rw [← inner_neg_left, neg_sub]
      have h3 : ⟪w - z, p w - p z⟫_ℝ = ⟪w - z, p w⟫_ℝ - ⟪w - z, p z⟫_ℝ :=
        inner_sub_right _ _ _
      have h4 := real_inner_le_norm (w - z) (p w - p z)
      have h5 := hL w z
      have h6 := norm_nonneg (w - z)
      have h7 : ‖w - z‖ * ‖p w - p z‖ ≤ ‖w - z‖ * ‖w - z‖ := mul_le_mul_of_nonneg_left h5 h6
      have h8 : (1 / 2 + (1 / 2 : ℝ) ^ (0 + 1)) * ‖w - z‖ ^ 2 = ‖w - z‖ * ‖w - z‖ := by ring
      rw [h8]
      linarith
    | succ n ih =>
      intro z w
      have hmz : (z + (1 / 2 : ℝ) • (w - z)) - z = (1 / 2 : ℝ) • (w - z) := by abel
      have hwm : w - (z + (1 / 2 : ℝ) • (w - z)) = (1 / 2 : ℝ) • (w - z) := by
        have : w - (z + (1 / 2 : ℝ) • (w - z)) = (w - z) - (1 / 2 : ℝ) • (w - z) := by abel
        rw [this]
        nth_rewrite 1 [← one_smul ℝ (w - z)]
        rw [← sub_smul]
        norm_num
      have nhalf : ‖(1 / 2 : ℝ) • (w - z)‖ = ‖w - z‖ / 2 := by
        rw [norm_smul]; norm_num; ring
      have h1 := ih z (z + (1 / 2 : ℝ) • (w - z))
      have h2 := ih (z + (1 / 2 : ℝ) • (w - z)) w
      rw [hmz, nhalf] at h1
      rw [hwm, nhalf] at h2
      have hsplit : ⟪w - z, p z⟫_ℝ = ⟪(1 / 2 : ℝ) • (w - z), p z⟫_ℝ
          + ⟪(1 / 2 : ℝ) • (w - z), p z⟫_ℝ := by
        rw [← inner_add_left, ← add_smul]; norm_num
      have hcross : ⟪(1 / 2 : ℝ) • (w - z), p (z + (1 / 2 : ℝ) • (w - z)) - p z⟫_ℝ
          ≤ ‖w - z‖ ^ 2 / 4 := by
        have ha := real_inner_le_norm ((1 / 2 : ℝ) • (w - z))
          (p (z + (1 / 2 : ℝ) • (w - z)) - p z)
        have hb := hL (z + (1 / 2 : ℝ) • (w - z)) z
        rw [hmz, nhalf] at hb
        rw [nhalf] at ha
        have hc := mul_le_mul_of_nonneg_left hb (by positivity : (0 : ℝ) ≤ ‖w - z‖ / 2)
        nlinarith
      rw [inner_sub_right] at hcross
      have hpow : (1 / 2 : ℝ) ^ (n + 1 + 1) = (1 / 2 : ℝ) ^ (n + 1) / 2 := by
        rw [pow_succ]; ring
      rw [hpow]
      have hid : (1 / 2 + (1 / 2 : ℝ) ^ (n + 1)) * (‖w - z‖ / 2) ^ 2
          + (1 / 2 + (1 / 2 : ℝ) ^ (n + 1)) * (‖w - z‖ / 2) ^ 2 + ‖w - z‖ ^ 2 / 4
          = (1 / 2 + (1 / 2 : ℝ) ^ (n + 1) / 2) * ‖w - z‖ ^ 2 := by ring
      rw [hsplit]
      linarith
  have ht : Filter.Tendsto (fun n : ℕ => (1 / 2 + (1 / 2 : ℝ) ^ (n + 1)) * ‖w - z‖ ^ 2)
      Filter.atTop (nhds ((1 / 2 + 0) * ‖w - z‖ ^ 2)) := by
    have h0 : Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) Filter.atTop (nhds 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
        (Filter.tendsto_add_atTop_nat 1)
    exact (h0.const_add (1 / 2)).mul_const _
  have hlim := ge_of_tendsto' ht (fun n => step n z w)
  linarith

open scoped InnerProductSpace in
/-- Baillon–Haddad type co-coercivity inequality. -/
theorem bh_cocoercive {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (p : H → H) (φ : H → ℝ) (hL : ∀ z w, ‖p z - p w‖ ≤ ‖z - w‖)
    (hs : ∀ z u, φ z + ⟪u - z, p z⟫_ℝ ≤ φ u) (z w : H) :
    φ z + ⟪w - z, p z⟫_ℝ + ‖p w - p z‖ ^ 2 / 2 ≤ φ w := by
  have h1 := hs z (w - (p w - p z))
  have h2 := bh_mdescent p φ hL hs w (w - (p w - p z))
  have e1 : w - (p w - p z) - z = (w - z) - (p w - p z) := by abel
  have e2 : w - (p w - p z) - w = -(p w - p z) := by abel
  rw [e1, inner_sub_left] at h1
  rw [e2, inner_neg_left, norm_neg] at h2
  have e3 : ‖p w - p z‖ ^ 2 = ⟪p w - p z, p w⟫_ℝ - ⟪p w - p z, p z⟫_ℝ := by
    rw [← real_inner_self_eq_norm_sq, inner_sub_right]
  linarith


open scoped RealInnerProductSpace in
theorem bh_main {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    [CompleteSpace K] (J : K → ℝ) (κ : ℝ)
    (hconv : ConvexOn ℝ Set.univ J) (hdiff : Differentiable ℝ J) (hκ : 0 < κ)
    (hlip : ∀ x y : K, ‖κ • gradient J x - κ • gradient J y‖ ≤ ‖x - y‖) (x y : K) :
    κ * ‖gradient J x - gradient J y‖ ^ 2 ≤ ⟪gradient J x - gradient J y, x - y⟫_ℝ := by
  set p : K → K := fun z => κ • gradient J z with hp
  set φ : K → ℝ := fun z => κ * J z with hφ
  have hs : ∀ z u, φ z + ⟪u - z, p z⟫_ℝ ≤ φ u := by
    intro z u
    have h := bh_convex_fo hconv hdiff z u
    simp only [φ, p, real_inner_smul_right]
    rw [real_inner_comm]
    nlinarith
  have h1 := bh_cocoercive p φ hlip hs x y
  have h2 := bh_cocoercive p φ hlip hs y x
  have e : p x - p y = κ • (gradient J x - gradient J y) := by simp [p, smul_sub]
  have e' : p y - p x = -(p x - p y) := by abel
  rw [e', norm_neg] at h1
  have hsum : ‖p x - p y‖ ^ 2 ≤ ⟪x - y, p x - p y⟫_ℝ := by
    have : ⟪y - x, p x⟫_ℝ + ⟪x - y, p y⟫_ℝ = -⟪x - y, p x - p y⟫_ℝ := by
      have hn : ⟪y - x, p x⟫_ℝ = -⟪x - y, p x⟫_ℝ := by rw [← inner_neg_left, neg_sub]
      rw [inner_sub_right, hn]; ring
    linarith
  rw [e, norm_smul, real_inner_smul_right, Real.norm_eq_abs, abs_of_pos hκ, mul_pow,
    real_inner_comm] at hsum
  have : κ * (κ * ‖gradient J x - gradient J y‖ ^ 2) ≤ κ * ⟪gradient J x - gradient J y, x - y⟫_ℝ := by
    nlinarith
  exact le_of_mul_le_mul_left this hκ

open InnerProductSpace in
theorem solution {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    [CompleteSpace K] (J : K → ℝ) (κ : ℝ)
    (hconv : ConvexOn ℝ Set.univ J) (hdiff : Differentiable ℝ J) (hκ : 0 < κ)
    (hlip : ThreeOpSplitting.Convergence.IsNonexpansive (fun x => κ • gradient J x)) :
    ThreeOpSplitting.Convergence.IsCocoercive κ (gradient J) := by
  intro x y
  exact bh_main J κ hconv hdiff hκ hlip x y
