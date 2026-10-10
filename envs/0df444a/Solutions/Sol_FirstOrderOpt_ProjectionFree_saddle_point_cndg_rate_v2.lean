-- Prove2me | solution 1 for FirstOrderOpt.ProjectionFree.saddle_point_cndg_rate_v2
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-10-10T04:13:36.411451+00:00
-- url     : https://prove2.me/submissions/976c0005-056f-4dd2-b0d0-e47eb85cca71

import Mathlib

open scoped RealInnerProductSpace
open Filter Topology Set

lemma aux_deriv_ge {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {X : Set E} (hX : Convex ℝ X) {h : E → ℝ} {g : E →L[ℝ] ℝ} {x z : E}
    (hx : x ∈ X) (hz : z ∈ X) (hg : HasFDerivWithinAt h g X x) (c : ℝ)
    (hc : ∀ t : ℝ, 0 < t → t ≤ 1 → t * c ≤ h (x + t • (z - x)) - h x) :
    c ≤ g (z - x) := by
  have hlim := hg.lim (l := atTop) (c := fun n : ℕ => ((n:ℝ) + 1))
    (d := fun n : ℕ => (1 / ((n:ℝ) + 1)) • (z - x)) (v := z - x) ?_ ?_ ?_
  · refine ge_of_tendsto hlim (Eventually.of_forall fun n => ?_)
    have hn : (0:ℝ) < (n:ℝ) + 1 := by positivity
    have := hc (1 / ((n:ℝ)+1)) (by positivity)
      (by rw [div_le_one hn]; linarith [n.cast_nonneg (α := ℝ)])
    simp only [smul_eq_mul]
    calc c = ((n:ℝ)+1) * (1 / ((n:ℝ)+1) * c) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left this hn.le
  · have : Tendsto (fun n : ℕ => 1 / ((n:ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using this.smul_const (z - x)
  · refine Eventually.of_forall fun n => ?_
    apply hX.add_smul_sub_mem hx hz
    constructor
    · positivity
    · rw [div_le_one (by positivity)]; linarith [n.cast_nonneg (α := ℝ)]
  · refine tendsto_const_nhds.congr' (Eventually.of_forall fun n => ?_)
    have hn : ((n:ℝ) + 1) ≠ 0 := by positivity
    simp only
    rw [smul_smul, mul_one_div_cancel hn, one_smul]

lemma aux_deriv_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {X : Set E} (hX : Convex ℝ X) {h : E → ℝ} {g : E →L[ℝ] ℝ} {x z : E}
    (hx : x ∈ X) (hz : z ∈ X) (hg : HasFDerivWithinAt h g X x) (c : ℝ)
    (hc : ∀ t : ℝ, 0 < t → t ≤ 1 → h (x + t • (z - x)) - h x ≤ t * c) :
    g (z - x) ≤ c := by
  have := aux_deriv_ge hX hx hz hg.neg (-c) (fun t ht0 ht1 => by
    have := hc t ht0 ht1; simp only [Pi.neg_apply]; linarith)
  simp only [neg_apply] at this
  linarith

lemma aux_bdd {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {Y : Set F} (hYcompact : IsCompact Y) (hYne : Y.Nonempty)
    (A : E →L[ℝ] F) (φ : F → ℝ) (hφlsc : LowerSemicontinuousOn φ Y) (x : E) :
    BddAbove ((fun y => ⟪A x, y⟫ - φ y) '' Y) := by
  obtain ⟨m, -, hmin⟩ := hφlsc.exists_isMinOn hYne hYcompact
  obtain ⟨M, hM⟩ := hYcompact.bddAbove_image (f := fun y => ⟪A x, y⟫)
    (continuous_const.inner continuous_id).continuousOn
  refine ⟨M - φ m, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  have h1 := hM ⟨y, hy, rfl⟩
  have h2 := isMinOn_iff.mp hmin y hy
  simp only at h1 ⊢
  linarith

lemma aux_smoothing {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {Y : Set F} (hYconv : Convex ℝ Y) (hYcompact : IsCompact Y) (hYne : Y.Nonempty)
    (A : E →L[ℝ] F) (φ : F → ℝ) (hφlsc : LowerSemicontinuousOn φ Y)
    (μ : ℝ) (hμ : 0 < μ)
    (hφsc : ∀ a ∈ Y, ∀ b ∈ Y, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      φ ((1 - t) • a + t • b) + μ / 2 * t * (1 - t) * ‖a - b‖ ^ 2 ≤ (1 - t) * φ a + t * φ b)
    (S : E → ℝ) (hS : ∀ x, S x = sSup ((fun y => ⟪A x, y⟫ - φ y) '' Y)) (x : E) :
    ∃ yx ∈ Y, (∀ z, S x + ⟪A (z - x), yx⟫ ≤ S z) ∧
      (∀ z, S z ≤ S x + ⟪A (z - x), yx⟫ + ‖A‖ ^ 2 / (2 * μ) * ‖z - x‖ ^ 2) := by
  have hbdd := aux_bdd hYcompact hYne A φ hφlsc
  have hlsc : LowerSemicontinuousOn (fun y => φ y + -⟪A x, y⟫) Y :=
    hφlsc.add (((continuous_const.inner continuous_id).neg).continuousOn.lowerSemicontinuousOn)
  obtain ⟨yx, hyx, hmax⟩ := hlsc.exists_isMinOn hYne hYcompact
  have hmax' : ∀ y ∈ Y, ⟪A x, y⟫ - φ y ≤ ⟪A x, yx⟫ - φ yx := by
    intro y hy
    have := isMinOn_iff.mp hmax y hy
    linarith
  have hSx : S x = ⟪A x, yx⟫ - φ yx := by
    rw [hS]
    refine IsGreatest.csSup_eq ⟨⟨yx, hyx, rfl⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hmax' y hy
  have hQG : ∀ y ∈ Y, ⟪A x, y⟫ - φ y ≤ S x - μ / 2 * ‖y - yx‖ ^ 2 := by
    intro y hy
    set D := (⟪A x, y⟫ - φ y) - (⟪A x, yx⟫ - φ yx) with hD
    set B := μ / 2 * ‖y - yx‖ ^ 2 with hB
    have hB0 : 0 ≤ B := by positivity
    have key : ∀ t : ℝ, 0 < t → t ≤ 1 → D + (1 - t) * B ≤ 0 := by
      intro t ht0 ht1
      have hm : (1 - t) • yx + t • y ∈ Y :=
        hYconv hyx hy (by linarith) ht0.le (by ring)
      have h1 := hmax' _ hm
      have h2 := hφsc yx hyx y hy t ht0.le ht1
      have h3 : ⟪A x, (1 - t) • yx + t • y⟫ = (1 - t) * ⟪A x, yx⟫ + t * ⟪A x, y⟫ := by
        rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
      rw [norm_sub_rev] at h2
      have : t * (D + (1 - t) * B) ≤ 0 := by
        rw [hD, hB]; nlinarith
      by_contra hcon
      rw [not_le] at hcon
      have := mul_pos ht0 hcon
      linarith
    have hD0 : D ≤ 0 := by have := key 1 one_pos le_rfl; simpa using this
    rw [hSx]
    by_contra hcon
    rw [not_le] at hcon
    have hDB : 0 < D + B := by rw [hD, hB]; linarith
    have hBpos : 0 < B := by linarith
    have := key ((D + B) / (2 * B)) (by positivity)
      (by rw [div_le_one (by positivity)]; linarith)
    have e : (1 - (D + B) / (2 * B)) * B = B - (D + B) / 2 := by
      field_simp
    rw [e] at this
    linarith
  refine ⟨yx, hyx, ?_, ?_⟩
  · intro z
    have := le_csSup (hbdd z) ⟨yx, hyx, rfl⟩
    rw [← hS] at this
    simp only at this
    rw [hSx, map_sub, inner_sub_left]
    linarith
  · intro z
    rw [hS z]
    refine csSup_le (hYne.image _) ?_
    rintro _ ⟨y, hy, rfl⟩
    simp only
    have hq := hQG y hy
    have e : ⟪A z, y⟫ = ⟪A x, y⟫ + ⟪A (z - x), yx⟫ + ⟪A (z - x), y - yx⟫ := by
      simp only [map_sub, inner_sub_left, inner_sub_right]; ring
    have hcs : ⟪A (z - x), y - yx⟫ ≤ ‖A‖ * ‖z - x‖ * ‖y - yx‖ := by
      calc ⟪A (z - x), y - yx⟫ ≤ ‖A (z - x)‖ * ‖y - yx‖ := real_inner_le_norm _ _
        _ ≤ ‖A‖ * ‖z - x‖ * ‖y - yx‖ :=
          mul_le_mul_of_nonneg_right (A.le_opNorm _) (norm_nonneg _)
    have amgm : ‖A‖ * ‖z - x‖ * ‖y - yx‖ ≤
        μ / 2 * ‖y - yx‖ ^ 2 + ‖A‖ ^ 2 / (2 * μ) * ‖z - x‖ ^ 2 := by
      rw [← sub_nonneg]
      have : μ / 2 * ‖y - yx‖ ^ 2 + ‖A‖ ^ 2 / (2 * μ) * ‖z - x‖ ^ 2
          - ‖A‖ * ‖z - x‖ * ‖y - yx‖ = (μ * ‖y - yx‖ - ‖A‖ * ‖z - x‖) ^ 2 / (2 * μ) := by
        field_simp; ring
      rw [this]; positivity
    linarith


lemma aux_arith (r Δ' a Δ ηn ηn1 D2 Lh d S : ℝ) (hr : 1 ≤ r) (hLh : 0 ≤ Lh) (hd : 0 ≤ d)
    (hstep : Δ' ≤ (1 - 2 / (r + 1 + 1)) * a + Lh * (2 / (r + 1 + 1)) ^ 2 * d)
    (ha : a ≤ Δ + (ηn - ηn1) * D2)
    (IH : r * (r + 1) / 2 * (Δ + ηn * D2) ≤ S) :
    (r + 1) * (r + 1 + 1) / 2 * (Δ' + ηn1 * D2) ≤ S + ((r + 1) * ηn1 * D2 + 2 * Lh * d) := by
  have hr2 : (0:ℝ) < r + 1 + 1 := by linarith
  have e1 : (r + 1) * (r + 1 + 1) / 2 * (1 - 2 / (r + 1 + 1)) = r * (r + 1) / 2 := by
    field_simp; ring
  have e2 : (r + 1) * (r + 1 + 1) / 2 * (2 / (r + 1 + 1)) ^ 2 = 2 * (r + 1) / (r + 1 + 1) := by
    field_simp
  have e3 : 2 * (r + 1) / (r + 1 + 1) ≤ 2 := by
    rw [div_le_iff₀ hr2]; linarith
  have hw' : 0 ≤ (r + 1) * (r + 1 + 1) / 2 := by positivity
  have hw : 0 ≤ r * (r + 1) / 2 := by positivity
  have h1 := mul_le_mul_of_nonneg_left hstep hw'
  have h2 := mul_le_mul_of_nonneg_left ha hw
  have h3 : 2 * (r + 1) / (r + 1 + 1) * (Lh * d) ≤ 2 * (Lh * d) :=
    mul_le_mul_of_nonneg_right e3 (by positivity)
  have e4 : (r + 1) * (r + 1 + 1) / 2 * ((1 - 2 / (r + 1 + 1)) * a + Lh * (2 / (r + 1 + 1)) ^ 2 * d)
      = r * (r + 1) / 2 * a + 2 * (r + 1) / (r + 1 + 1) * (Lh * d) := by
    rw [← e1, ← e2]; ring
  rw [e4] at h1
  nlinarith

theorem solution {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (X : Set E) (hXconv : Convex ℝ X) (hXcompact : IsCompact X)
    (Y : Set F) (hYconv : Convex ℝ Y) (hYcompact : IsCompact Y) (hYne : Y.Nonempty)
    (A : E →L[ℝ] F) (fhat : F → ℝ) (hfhatconv : ConvexOn ℝ Y fhat)
    (hfhatlsc : LowerSemicontinuousOn fhat Y)
    (f : E → ℝ) (hf : ∀ x, f x = sSup ((fun y => ⟪A x, y⟫ - fhat y) '' Y))
    (σv : ℝ) (hσv : 0 < σv)
    (ω : F → ℝ) (dω : F → F →L[ℝ] ℝ)
    (hωdiff : ∀ y ∈ Y, HasFDerivWithinAt ω (dω y) Y y)
    (hωstrong : ∀ y ∈ Y, ∀ z ∈ Y, ω y + (dω y) (z - y) + (σv / 2) * ‖z - y‖ ^ 2 ≤ ω z)
    (c : F) (hc : c ∈ Y) (hcmin : ∀ y ∈ Y, ω c ≤ ω y)
    (VY : F → ℝ) (hVY : ∀ y, VY y = ω y - ω c - (dω c) (y - c))
    (DY : ℝ) (hDY : 0 < DY) (hDYsq : IsLUB (VY '' Y) (DY ^ 2))
    (η : ℕ → ℝ) (hηpos : ∀ k, 1 ≤ k → 0 < η k) (hηmono : ∀ k, 1 ≤ k → η (k + 1) ≤ η k)
    (fη : ℕ → E → ℝ)
    (hfη : ∀ k x, fη k x = sSup ((fun y => ⟪A x, y⟫ - fhat y - η k * VY y) '' Y))
    (fηGrad : ℕ → E → E →L[ℝ] ℝ)
    (hηGrad : ∀ k, 1 ≤ k → ∀ x ∈ X, HasFDerivWithinAt (fη k) (fηGrad k x) X x)
    (x y : ℕ → E) (hx0 : x 0 ∈ X) (hy0 : y 0 = x 0)
    (hx : ∀ k, 1 ≤ k → x k ∈ X)
    (hLO : ∀ k, 1 ≤ k → ∀ z ∈ X, (fηGrad k (y (k - 1))) (x k) ≤ (fηGrad k (y (k - 1))) z)
    (α : ℕ → ℝ) (hα : ∀ k, 1 ≤ k → α k ∈ Set.Icc (0 : ℝ) 1)
    (hyDef : ∀ k, 1 ≤ k → y k = (1 - α k) • y (k - 1) + (α k) • x k)
    (hyk_le : ∀ k, 1 ≤ k →
      fη k (y k) ≤ fη k ((1 - 2 / ((k : ℝ) + 1)) • y (k - 1) + (2 / ((k : ℝ) + 1)) • x k))
    (xstar : E) (hxstar : xstar ∈ X) (hxstar_opt : ∀ z ∈ X, f xstar ≤ f z)
    (k : ℕ) (hk : 1 ≤ k) :
    f (y k) - f xstar ≤ (2 / ((k : ℝ) * ((k : ℝ) + 1))) *
      ∑ i ∈ Finset.Icc 1 k, ((i : ℝ) * η i * DY ^ 2 +
        (‖A‖ ^ 2 / (σv * η i)) * ‖x i - y (i - 1)‖ ^ 2) := by
  -- basic facts on VY
  have hV0 : ∀ z ∈ Y, 0 ≤ VY z := by
    intro z hz
    have := hωstrong c hc z hz
    rw [hVY]
    nlinarith [sq_nonneg ‖z - c‖]
  have hVD : ∀ z ∈ Y, VY z ≤ DY ^ 2 := fun z hz => hDYsq.1 ⟨z, hz, rfl⟩
  have hωcont : ContinuousOn ω Y := fun z hz => (hωdiff z hz).continuousWithinAt
  have hVcont : ContinuousOn VY Y := by
    have : VY = fun z => ω z - ω c - (dω c) (z - c) := funext hVY
    rw [this]
    exact (hωcont.sub continuousOn_const).sub
      ((dω c).continuous.comp (continuous_id.sub continuous_const)).continuousOn
  have hωsc : ∀ a ∈ Y, ∀ b ∈ Y, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ω ((1 - t) • a + t • b) + σv / 2 * t * (1 - t) * ‖a - b‖ ^ 2
        ≤ (1 - t) * ω a + t * ω b := by
    intro a ha b hb t ht0 ht1
    set m := (1 - t) • a + t • b with hm_def
    have hm : m ∈ Y := hYconv ha hb (by linarith) ht0 (by ring)
    have h1 := hωstrong m hm a ha
    have h2 := hωstrong m hm b hb
    have ea : a - m = t • (a - b) := by rw [hm_def]; module
    have eb : b - m = (t - 1) • (a - b) := by rw [hm_def]; module
    rw [ea, map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0] at h1
    rw [eb, map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs,
      abs_of_nonpos (by linarith : t - 1 ≤ 0)] at h2
    have h1' := mul_le_mul_of_nonneg_left h1 (by linarith : (0:ℝ) ≤ 1 - t)
    have h2' := mul_le_mul_of_nonneg_left h2 ht0
    nlinarith
  have hVsc : ∀ a ∈ Y, ∀ b ∈ Y, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      VY ((1 - t) • a + t • b) + σv / 2 * t * (1 - t) * ‖a - b‖ ^ 2
        ≤ (1 - t) * VY a + t * VY b := by
    intro a ha b hb t ht0 ht1
    have h := hωsc a ha b hb t ht0 ht1
    have e : (1 - t) • a + t • b - c = (1 - t) • (a - c) + t • (b - c) := by module
    rw [hVY, hVY a, hVY b, e, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    nlinarith
  -- the smoothed problems
  have hφsc : ∀ j, 1 ≤ j → ∀ a ∈ Y, ∀ b ∈ Y, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      (fun z => fhat z + η j * VY z) ((1 - t) • a + t • b)
        + (η j * σv) / 2 * t * (1 - t) * ‖a - b‖ ^ 2
        ≤ (1 - t) * (fun z => fhat z + η j * VY z) a + t * (fun z => fhat z + η j * VY z) b := by
    intro j hj a ha b hb t ht0 ht1
    have h1 := hfhatconv.2 ha hb (by linarith : (0:ℝ) ≤ 1 - t) ht0 (by ring)
    simp only [smul_eq_mul] at h1
    have h2 := mul_le_mul_of_nonneg_left (hVsc a ha b hb t ht0 ht1) (hηpos j hj).le
    simp only
    nlinarith
  have hφlsc : ∀ j, LowerSemicontinuousOn (fun z => fhat z + η j * VY z) Y := fun j =>
    hfhatlsc.add ((continuousOn_const.mul hVcont).lowerSemicontinuousOn)
  have hS : ∀ j x, fη j x = sSup ((fun z => ⟪A x, z⟫ - (fun z => fhat z + η j * VY z) z) '' Y) := by
    intro j x
    simp only [hfη, sub_sub]
  have hsm : ∀ j, 1 ≤ j → ∀ x0 : E, ∃ yx ∈ Y, (∀ z, fη j x0 + ⟪A (z - x0), yx⟫ ≤ fη j z) ∧
      (∀ z, fη j z ≤ fη j x0 + ⟪A (z - x0), yx⟫
        + ‖A‖ ^ 2 / (2 * (η j * σv)) * ‖z - x0‖ ^ 2) := fun j hj x0 =>
    aux_smoothing hYconv hYcompact hYne A _ (hφlsc j) (η j * σv)
      (mul_pos (hηpos j hj) hσv) (hφsc j hj) (fη j) (hS j) x0
  have hbddη : ∀ j x0, BddAbove ((fun z => ⟪A x0, z⟫ - (fun z => fhat z + η j * VY z) z) '' Y) :=
    fun j x0 => aux_bdd hYcompact hYne A _ (hφlsc j) x0
  have hbddf : ∀ x0, BddAbove ((fun z => ⟪A x0, z⟫ - fhat z) '' Y) :=
    fun x0 => aux_bdd hYcompact hYne A _ hfhatlsc x0
  -- sandwich
  have hup : ∀ j, 1 ≤ j → ∀ x0, f x0 ≤ fη j x0 + η j * DY ^ 2 := by
    intro j hj x0
    rw [hf x0]
    refine csSup_le (hYne.image _) ?_
    rintro _ ⟨z, hz, rfl⟩
    have h1 := le_csSup (hbddη j x0) ⟨z, hz, rfl⟩
    rw [← hS] at h1
    have h2 := mul_le_mul_of_nonneg_left (hVD z hz) (hηpos j hj).le
    simp only at h1 ⊢
    linarith
  have hlow : ∀ j, 1 ≤ j → ∀ x0, fη j x0 ≤ f x0 := by
    intro j hj x0
    rw [hS j x0]
    refine csSup_le (hYne.image _) ?_
    rintro _ ⟨z, hz, rfl⟩
    have h1 := le_csSup (hbddf x0) ⟨z, hz, rfl⟩
    rw [← hf] at h1
    have h2 := mul_nonneg (hηpos j hj).le (hV0 z hz)
    simp only at h1 ⊢
    linarith
  have hmono : ∀ j, 1 ≤ j → ∀ x0, fη (j + 1) x0 ≤ fη j x0 + (η j - η (j + 1)) * DY ^ 2 := by
    intro j hj x0
    rw [hS (j + 1) x0]
    refine csSup_le (hYne.image _) ?_
    rintro _ ⟨z, hz, rfl⟩
    have h1 := le_csSup (hbddη j x0) ⟨z, hz, rfl⟩
    rw [← hS] at h1
    have h2 := mul_le_mul_of_nonneg_left (hVD z hz)
      (sub_nonneg.mpr (hηmono j hj))
    simp only at h1 ⊢
    nlinarith
  -- iterates stay in X
  have hyX : ∀ j, y j ∈ X := by
    intro j
    induction j with
    | zero => rw [hy0]; exact hx0
    | succ n ih =>
      have h := hyDef (n + 1) (by omega)
      simp only [Nat.add_sub_cancel] at h
      rw [h]
      obtain ⟨h0, h1⟩ := hα (n + 1) (by omega)
      exact hXconv ih (hx (n + 1) (by omega)) (by linarith) h0 (by ring)
  -- one step
  have hstep : ∀ j, 1 ≤ j → fη j (y j) - f xstar ≤
      (1 - 2 / ((j : ℝ) + 1)) * (fη j (y (j - 1)) - f xstar)
        + ‖A‖ ^ 2 / (2 * (η j * σv)) * (2 / ((j : ℝ) + 1)) ^ 2 * ‖x j - y (j - 1)‖ ^ 2 := by
    intro j hj
    set γ : ℝ := 2 / ((j : ℝ) + 1) with hγ
    have hj1 : (1:ℝ) ≤ j := by exact_mod_cast hj
    have hγ0 : 0 ≤ γ := by positivity
    have hγ1 : γ ≤ 1 := by rw [hγ, div_le_one (by positivity)]; linarith
    set xp := y (j - 1) with hxp
    have hxpX : xp ∈ X := hyX _
    have hg := hηGrad j hj xp hxpX
    set g := fηGrad j xp with hg_def
    obtain ⟨yx, hyx, h4, h3⟩ := hsm j hj xp
    have hℓ : ⟪A (x j - xp), yx⟫ ≤ g (x j - xp) := by
      refine aux_deriv_ge hXconv hxpX (hx j hj) hg _ (fun t ht0 ht1 => ?_)
      have := h4 (xp + t • (x j - xp))
      rw [add_sub_cancel_left, map_smul, real_inner_smul_left] at this
      linarith
    have hconv : g (xstar - xp) ≤ fη j xstar - fη j xp := by
      refine aux_deriv_le hXconv hxpX hxstar hg _ (fun t ht0 ht1 => ?_)
      set m := xp + t • (xstar - xp) with hm
      obtain ⟨ym, -, h4m, -⟩ := hsm j hj m
      have ha := h4m xp
      have hb := h4m xstar
      have ea : xp - m = (-t) • (xstar - xp) := by rw [hm]; module
      have eb : xstar - m = (1 - t) • (xstar - xp) := by rw [hm]; module
      rw [ea, map_smul, real_inner_smul_left] at ha
      rw [eb, map_smul, real_inner_smul_left] at hb
      have ha' := mul_le_mul_of_nonneg_left ha (by linarith : (0:ℝ) ≤ 1 - t)
      have hb' := mul_le_mul_of_nonneg_left hb ht0.le
      nlinarith
    have hLO' : g (x j - xp) ≤ g (xstar - xp) := by
      rw [map_sub, map_sub]
      have := hLO j hj xstar hxstar
      linarith
    have hlowstar := hlow j hj xstar
    have hyk := hyk_le j hj
    have ey : (1 - γ) • xp + γ • x j - xp = γ • (x j - xp) := by module
    have hsmooth := h3 ((1 - γ) • xp + γ • x j)
    rw [ey, map_smul, real_inner_smul_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hγ0,
      mul_pow] at hsmooth
    have hA : 0 ≤ ‖A‖ ^ 2 / (2 * (η j * σv)) := by
      have := hηpos j hj; positivity
    have k1 := mul_le_mul_of_nonneg_left hℓ hγ0
    have k2 := mul_le_mul_of_nonneg_left hLO' hγ0
    have k3 := mul_le_mul_of_nonneg_left hconv hγ0
    have k4 := mul_le_mul_of_nonneg_left hlowstar (by linarith : (0:ℝ) ≤ 1 - γ)
    nlinarith
  -- induction
  have hmain : ∀ n : ℕ, 1 ≤ n → (n : ℝ) * ((n : ℝ) + 1) / 2 * (fη n (y n) - f xstar + η n * DY ^ 2)
      ≤ ∑ i ∈ Finset.Icc 1 n, ((i : ℝ) * η i * DY ^ 2 +
        (‖A‖ ^ 2 / (σv * η i)) * ‖x i - y (i - 1)‖ ^ 2) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      have h := hstep 1 le_rfl
      have hη1 := hηpos 1 le_rfl
      simp only [Finset.Icc_self, Finset.sum_singleton, Nat.cast_one] at h ⊢
      have e : ‖A‖ ^ 2 / (2 * (η 1 * σv)) * (2 / (1 + 1)) ^ 2 = (‖A‖ ^ 2 / (σv * η 1)) / 2 := by
        field_simp; ring
      rw [e] at h
      have : 0 ≤ ‖A‖ ^ 2 / (σv * η 1) * ‖x 1 - y (1 - 1)‖ ^ 2 := by positivity
      norm_num at h ⊢
      nlinarith
    | succ n hn ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have h := hstep (n + 1) (by omega)
      have hm := hmono n hn (y n)
      simp only [Nat.add_sub_cancel] at h
      push_cast at h ⊢
      have hηn1 := hηpos (n + 1) (by omega)
      have e : ‖A‖ ^ 2 / (σv * η (n + 1)) * ‖x (n + 1) - y n‖ ^ 2
          = 2 * (‖A‖ ^ 2 / (2 * (η (n + 1) * σv))) * ‖x (n + 1) - y n‖ ^ 2 := by
        field_simp
      rw [e, ← add_assoc]
      have := aux_arith (n : ℝ) _ _ _ (η n) (η (n + 1)) (DY ^ 2) _ _ _ (by exact_mod_cast hn)
        (by positivity) (by positivity) h (by linarith) ih
      linarith
  -- conclusion
  have hfin := hmain k hk
  have hupk := hup k hk (y k)
  have hk1 : (0:ℝ) < k := by exact_mod_cast hk
  calc f (y k) - f xstar ≤ fη k (y k) - f xstar + η k * DY ^ 2 := by linarith
    _ = (2 / ((k : ℝ) * ((k : ℝ) + 1))) *
        ((k : ℝ) * ((k : ℝ) + 1) / 2 * (fη k (y k) - f xstar + η k * DY ^ 2)) := by
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hfin (by positivity)
