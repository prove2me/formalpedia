-- Prove2me | solution 1 for CachonCoord.InternalMarket.eq_46
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T07:05:03.28628+00:00
-- url     : https://prove2.me/submissions/f15e3ad4-206e-4efb-b029-45c6cabd0558

import Mathlib
import Definitions.Def_CachonCoord_InternalMarket_Revenue
import Definitions.Def_CachonCoord_InternalMarket_Model



namespace CachonCoord.InternalMarket

open MeasureTheory

lemma im_r_pos {η : ℝ} (hη : 1 < η) : 0 < (η - 1) / η := by
  apply div_pos <;> linarith

lemma im_r_lt_one {η : ℝ} (hη : 1 < η) : (η - 1) / η < 1 := by
  rw [div_lt_one (by linarith)]; linarith

lemma im_r_sub_one {η : ℝ} (hη : 1 < η) : (η - 1) / η - 1 = -1 / η := by
  field_simp; ring

/-- tangent inequality for t ↦ t^r -/
lemma im_tangent {r q t : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hq : 0 < q) (ht : 0 ≤ t) :
    t ^ r ≤ q ^ r + r * q ^ (r - 1) * (t - q) := by
  have h := Real.geom_mean_le_arith_mean2_weighted (w₁ := r) (w₂ := 1 - r) (p₁ := t) (p₂ := q)
    hr0.le (by linarith) ht hq.le (by ring)
  have hpos : 0 < q ^ (r - 1) := Real.rpow_pos_of_pos hq _
  have e1 : q ^ (1 - r) * q ^ (r - 1) = 1 := by
    rw [← Real.rpow_add hq]; simp
  have e2 : q * q ^ (r - 1) = q ^ r := by
    rw [show q * q ^ (r - 1) = q ^ (1:ℝ) * q ^ (r - 1) by rw [Real.rpow_one], ← Real.rpow_add hq]
    congr 1; ring
  have := mul_le_mul_of_nonneg_right h hpos.le
  calc t ^ r = t ^ r * q ^ (1 - r) * q ^ (r - 1) := by rw [mul_assoc, e1, mul_one]
    _ ≤ (r * t + (1 - r) * q) * q ^ (r - 1) := this
    _ = r * t * q ^ (r - 1) + (1 - r) * (q * q ^ (r - 1)) := by ring
    _ = q ^ r + r * q ^ (r - 1) * (t - q) := by rw [← e2]; ring

/-- uniqueness of maximizer of strictly concave function -/
lemma im_unique_max {s : Set ℝ} {f : ℝ → ℝ} (hf : StrictConcaveOn ℝ s f) {x y : ℝ}
    (hx : x ∈ s) (hy : y ∈ s) (hmx : IsMaxOn f s x) (hmy : IsMaxOn f s y) : x = y := by
  by_contra hne
  have h := hf.2 hx hy hne (show (0:ℝ) < 1/2 by norm_num) (show (0:ℝ) < 1/2 by norm_num)
    (show (1/2:ℝ) + 1/2 = 1 by norm_num)
  have hmem : (1/2 : ℝ) • x + (1/2 : ℝ) • y ∈ s :=
    hf.1 hx hy (show (0:ℝ) ≤ 1/2 by norm_num) (show (0:ℝ) ≤ 1/2 by norm_num) (by norm_num)
  have h1 : f ((1/2:ℝ) • x + (1/2:ℝ) • y) ≤ f x := hmx hmem
  have h2 : f y ≤ f x := hmx hy
  have h3 : f x ≤ f y := hmy hx
  simp only [smul_eq_mul] at h h1
  linarith

lemma im_rpow_strictConcave {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    StrictConcaveOn ℝ (Set.Ici 0) (fun x : ℝ => x ^ r) :=
  Real.strictConcaveOn_rpow hr0 hr1

lemma im_retailer_strictConcave {η αᵢ w : ℝ} (hη : 1 < η) (hα : 0 < αᵢ) :
    StrictConcaveOn ℝ (Set.Ici 0) (retailerProfit η αᵢ w) := by
  have h := im_rpow_strictConcave (im_r_pos hη) (im_r_lt_one hη)
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have := h.2 hx hy hxy ha hb hab
  simp only [smul_eq_mul, retailerProfit] at this ⊢
  have := mul_lt_mul_of_pos_left this hα
  nlinarith

lemma im_retailer_deriv {η αᵢ w q : ℝ} (hη : 1 < η) (hq : 0 < q) :
    HasDerivAt (retailerProfit η αᵢ w) ((η - 1) / η * αᵢ * q ^ (-1 / η) - w) q := by
  have h := Real.hasDerivAt_rpow_const (x := q) (p := (η - 1) / η) (Or.inl hq.ne')
  have h2 : HasDerivAt (fun y => αᵢ * y ^ ((η - 1) / η) - w * y)
      (αᵢ * ((η - 1) / η * q ^ ((η - 1) / η - 1)) - w * 1) q :=
    (h.const_mul αᵢ).sub ((hasDerivAt_id q).const_mul w)
  unfold retailerProfit
  rw [im_r_sub_one hη] at h2
  exact h2.congr_deriv (by ring)

lemma im_retailer_max_of_foc {η αᵢ w q : ℝ} (hη : 1 < η) (hα : 0 < αᵢ) (hq : 0 < q)
    (hfoc : (η - 1) / η * αᵢ * q ^ (-1 / η) - w = 0) :
    IsMaxOn (retailerProfit η αᵢ w) (Set.Ici 0) q := by
  intro t ht
  simp only [Set.mem_setOf_eq, Set.mem_Ici] at ht ⊢
  have := im_tangent (im_r_pos hη) (im_r_lt_one hη) hq ht
  rw [im_r_sub_one hη] at this
  unfold retailerProfit
  have := mul_le_mul_of_nonneg_left this hα.le
  nlinarith

lemma im_retailer_iff {η αᵢ w q0 : ℝ} (hη : 1 < η) (hα : 0 < αᵢ) (hq0 : 0 < q0)
    (hfoc : (η - 1) / η * αᵢ * q0 ^ (-1 / η) - w = 0) (q : ℝ) (hq : 0 ≤ q) :
    IsMaxOn (retailerProfit η αᵢ w) (Set.Ici 0) q ↔ q = q0 := by
  constructor
  · intro hm
    exact im_unique_max (im_retailer_strictConcave hη hα) hq hq0.le hm
      (im_retailer_max_of_foc hη hα hq0 hfoc)
  · rintro rfl; exact im_retailer_max_of_foc hη hα hq0 hfoc

theorem foc_core (η αᵢ w : ℝ) (hη : 1 < η) (hα : 0 < αᵢ) (hw : 0 < w) :
    (∀ q : ℝ, 0 < q →
      HasDerivAt (retailerProfit η αᵢ w) ((η - 1) / η * αᵢ * q ^ (-1 / η) - w) q) ∧
    ∀ q : ℝ, 0 ≤ q →
      (IsMaxOn (retailerProfit η αᵢ w) (Set.Ici 0) q ↔
        0 < q ∧ (η - 1) / η * αᵢ * q ^ (-1 / η) - w = 0) := by
  refine ⟨fun q hq => im_retailer_deriv hη hq, ?_⟩
  set q0 : ℝ := ((η - 1) / η * αᵢ / w) ^ η with hq0def
  have hbase : 0 < (η - 1) / η * αᵢ / w := div_pos (mul_pos (im_r_pos hη) hα) hw
  have hq0 : 0 < q0 := Real.rpow_pos_of_pos hbase _
  have hfoc : (η - 1) / η * αᵢ * q0 ^ (-1 / η) - w = 0 := by
    rw [hq0def, ← Real.rpow_mul hbase.le]
    have : η * (-1 / η) = -1 := by field_simp
    rw [this, Real.rpow_neg_one]
    have hne : η - 1 ≠ 0 := by linarith
    have hne2 : η ≠ 0 := by linarith
    field_simp
    ring
  intro q hq
  rw [im_retailer_iff hη hα hq0 hfoc q hq]
  constructor
  · rintro rfl; exact ⟨hq0, hfoc⟩
  · rintro ⟨hqp, hf⟩
    exact (im_retailer_iff hη hα hq0 hfoc q hq).1 (im_retailer_max_of_foc hη hα hqp hf)

lemma im_S_pos {η α₁ α₂ : ℝ} (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) : 0 < α₁ ^ η + α₂ ^ η :=
  add_pos (Real.rpow_pos_of_pos hα₁ _) (Real.rpow_pos_of_pos hα₂ _)

lemma im_one_sub_share {η α₁ α₂ : ℝ} (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) :
    1 - optShare η α₁ α₂ = α₂ ^ η / (α₁ ^ η + α₂ ^ η) := by
  have := im_S_pos (η := η) hα₁ hα₂
  unfold optShare
  field_simp
  ring

lemma im_share_pos {η α₁ α₂ : ℝ} (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) : 0 < optShare η α₁ α₂ :=
  div_pos (Real.rpow_pos_of_pos hα₁ _) (im_S_pos hα₁ hα₂)

lemma im_one_sub_share_pos {η α₁ α₂ : ℝ} (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) :
    0 < 1 - optShare η α₁ α₂ := by
  rw [im_one_sub_share hα₁ hα₂]
  exact div_pos (Real.rpow_pos_of_pos hα₂ _) (im_S_pos hα₁ hα₂)

lemma im_pow_term {η a S : ℝ} (hη : 1 < η) (ha : 0 < a) (hS : 0 < S) :
    a * (a ^ η / S) ^ ((η - 1) / η) = a ^ η / S ^ ((η - 1) / η) := by
  rw [Real.div_rpow (Real.rpow_nonneg ha.le _) hS.le, ← Real.rpow_mul ha.le]
  have h1 : η * ((η - 1) / η) = η - 1 := by field_simp
  rw [h1, ← mul_div_assoc]
  congr 1
  rw [show a * a ^ (η - 1) = a ^ (1:ℝ) * a ^ (η - 1) by rw [Real.rpow_one], ← Real.rpow_add ha]
  congr 1; ring

lemma im_coef {η α₁ α₂ : ℝ} (hη : 1 < η) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) :
    α₁ * optShare η α₁ α₂ ^ ((η - 1) / η) + α₂ * (1 - optShare η α₁ α₂) ^ ((η - 1) / η) =
      (α₁ ^ η + α₂ ^ η) ^ (1 / η) := by
  have hS := im_S_pos (η := η) hα₁ hα₂
  rw [im_one_sub_share hα₁ hα₂]
  unfold optShare
  rw [im_pow_term hη hα₁ hS, im_pow_term hη hα₂ hS, ← add_div]
  have : (1 / η) = 1 - (η - 1) / η := by field_simp; ring
  rw [this, Real.rpow_sub hS, Real.rpow_one]

theorem optrev_core (η α₁ α₂ Q : ℝ) (hη : 1 < η) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) :
    optRevenue η α₁ α₂ Q = (α₁ ^ η + α₂ ^ η) ^ (1 / η) * Q ^ ((η - 1) / η) := by
  unfold optRevenue revenue
  rw [im_coef hη hα₁ hα₂]

lemma im_neg_pow {η a S : ℝ} (hη : 1 < η) (ha : 0 < a) (hS : 0 < S) :
    (a ^ η / S) ^ (-1 / η) = a⁻¹ * S ^ (1 / η) := by
  have hb : 0 < a ^ η / S := div_pos (Real.rpow_pos_of_pos ha _) hS
  rw [show (-1 / η) = -(1 / η) by ring, Real.rpow_neg hb.le,
    Real.div_rpow (Real.rpow_nonneg ha.le _) hS.le, ← Real.rpow_mul ha.le]
  have : η * (1 / η) = 1 := by field_simp
  rw [this, Real.rpow_one]
  have : 0 < S ^ (1 / η) := Real.rpow_pos_of_pos hS _
  field_simp

lemma im_price_pos {η α₁ α₂ Q : ℝ} (hη : 1 < η) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) (hQ : 0 < Q) :
    0 < price η α₁ α₂ Q := by
  unfold price
  exact mul_pos (mul_pos (im_r_pos hη) (Real.rpow_pos_of_pos (im_S_pos hα₁ hα₂) _))
    (Real.rpow_pos_of_pos hQ _)

lemma im_foc_at {η a α₁ α₂ Q : ℝ} (hη : 1 < η) (ha : 0 < a) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂)
    (hQ : 0 < Q) :
    (η - 1) / η * a * (a ^ η / (α₁ ^ η + α₂ ^ η) * Q) ^ (-1 / η) - price η α₁ α₂ Q = 0 := by
  have hS := im_S_pos (η := η) hα₁ hα₂
  rw [Real.mul_rpow (div_pos (Real.rpow_pos_of_pos ha _) hS).le hQ.le, im_neg_pow hη ha hS]
  unfold price
  field_simp
  ring

theorem market_core (η α₁ α₂ Q : ℝ) (hη : 1 < η) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂)
    (hQ : 0 < Q) :
    (∀ q : ℝ, 0 ≤ q →
      (IsMaxOn (retailerProfit η α₁ (price η α₁ α₂ Q)) (Set.Ici 0) q ↔
        q = optShare η α₁ α₂ * Q)) ∧
    (∀ q : ℝ, 0 ≤ q →
      (IsMaxOn (retailerProfit η α₂ (price η α₁ α₂ Q)) (Set.Ici 0) q ↔
        q = (1 - optShare η α₁ α₂) * Q)) ∧
    optShare η α₁ α₂ * Q + (1 - optShare η α₁ α₂) * Q = Q ∧
    ∀ q₁ q₂ : ℝ, 0 ≤ q₁ → 0 ≤ q₂ → q₁ + q₂ ≤ Q →
      α₁ * q₁ ^ ((η - 1) / η) + α₂ * q₂ ^ ((η - 1) / η) ≤
        α₁ * (optShare η α₁ α₂ * Q) ^ ((η - 1) / η) +
          α₂ * ((1 - optShare η α₁ α₂) * Q) ^ ((η - 1) / η) := by
  have h1 : 0 < optShare η α₁ α₂ * Q := mul_pos (im_share_pos hα₁ hα₂) hQ
  have h2 : 0 < (1 - optShare η α₁ α₂) * Q := mul_pos (im_one_sub_share_pos hα₁ hα₂) hQ
  have f1 : (η - 1) / η * α₁ * (optShare η α₁ α₂ * Q) ^ (-1 / η) - price η α₁ α₂ Q = 0 := by
    unfold optShare; exact im_foc_at hη hα₁ hα₁ hα₂ hQ
  have f2 : (η - 1) / η * α₂ * ((1 - optShare η α₁ α₂) * Q) ^ (-1 / η) - price η α₁ α₂ Q = 0 := by
    rw [im_one_sub_share hα₁ hα₂]; exact im_foc_at hη hα₂ hα₁ hα₂ hQ
  refine ⟨fun q hq => im_retailer_iff hη hα₁ h1 f1 q hq,
    fun q hq => im_retailer_iff hη hα₂ h2 f2 q hq, by ring, ?_⟩
  intro q₁ q₂ hq₁ hq₂ hsum
  have t1 := im_tangent (im_r_pos hη) (im_r_lt_one hη) h1 hq₁
  have t2 := im_tangent (im_r_pos hη) (im_r_lt_one hη) h2 hq₂
  rw [im_r_sub_one hη] at t1 t2
  have t1' := mul_le_mul_of_nonneg_left t1 hα₁.le
  have t2' := mul_le_mul_of_nonneg_left t2 hα₂.le
  have hw := im_price_pos hη hα₁ hα₂ hQ
  set w := price η α₁ α₂ Q
  set A := (optShare η α₁ α₂ * Q) ^ (-1 / η)
  set B := ((1 - optShare η α₁ α₂) * Q) ^ (-1 / η)
  have e1 : α₁ * ((η - 1) / η * A * (q₁ - optShare η α₁ α₂ * Q)) =
      w * (q₁ - optShare η α₁ α₂ * Q) := by
    have : (η - 1) / η * α₁ * A = w := by linarith
    rw [← this]; ring
  have e2 : α₂ * ((η - 1) / η * B * (q₂ - (1 - optShare η α₁ α₂) * Q)) =
      w * (q₂ - (1 - optShare η α₁ α₂) * Q) := by
    have : (η - 1) / η * α₂ * B = w := by linarith
    rw [← this]; ring
  rw [mul_add, e1] at t1'
  rw [mul_add, e2] at t2'
  nlinarith

theorem marginal_core (η α₁ α₂ Q : ℝ) (hη : 1 < η) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂)
    (hQ : 0 < Q) :
    HasDerivAt (fun Q' => optRevenue η α₁ α₂ Q') (price η α₁ α₂ Q) Q := by
  have h := (Real.hasDerivAt_rpow_const (x := Q) (p := (η - 1) / η) (Or.inl hQ.ne')).const_mul
    ((α₁ ^ η + α₂ ^ η) ^ (1 / η))
  have hf : (fun Q' => optRevenue η α₁ α₂ Q') =
      fun Q' => (α₁ ^ η + α₂ ^ η) ^ (1 / η) * Q' ^ ((η - 1) / η) := by
    funext Q'; exact optrev_core η α₁ α₂ Q' hη hα₁ hα₂
  rw [hf, im_r_sub_one hη] at *
  unfold price
  exact h.congr_deriv (by ring)

theorem eq44_core (η α₁ α₂ Q : ℝ) (hη : 1 < η) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) (hQ : 0 < Q) :
    StrictConcaveOn ℝ (Set.Icc 0 1) (fun γ => revenue η α₁ α₂ γ Q) ∧
    optShare η α₁ α₂ ∈ Set.Icc (0 : ℝ) 1 ∧
    IsMaxOn (fun γ => revenue η α₁ α₂ γ Q) (Set.Icc 0 1) (optShare η α₁ α₂) ∧
    ∀ γ ∈ Set.Icc (0 : ℝ) 1,
      IsMaxOn (fun γ' => revenue η α₁ α₂ γ' Q) (Set.Icc 0 1) γ → γ = optShare η α₁ α₂ := by
  have hr0 := im_r_pos hη
  have hr1 := im_r_lt_one hη
  have hC : 0 < Q ^ ((η - 1) / η) := Real.rpow_pos_of_pos hQ _
  have hsc := im_rpow_strictConcave hr0 hr1
  have hsc' : StrictConcaveOn ℝ (Set.Icc 0 1) (fun γ => revenue η α₁ α₂ γ Q) := by
    refine ⟨convex_Icc 0 1, ?_⟩
    intro x hx y hy hxy a b ha hb hab
    have g1 := hsc.2 (show x ∈ Set.Ici (0:ℝ) from hx.1) (show y ∈ Set.Ici (0:ℝ) from hy.1)
      hxy ha hb hab
    have g2 := hsc.concaveOn.2 (show 1 - x ∈ Set.Ici (0:ℝ) by simp [hx.2])
      (show 1 - y ∈ Set.Ici (0:ℝ) by simp [hy.2]) ha.le hb.le hab
    simp only [smul_eq_mul] at g1 g2 ⊢
    have e : a * (1 - x) + b * (1 - y) = 1 - (a * x + b * y) := by
      linear_combination hab
    rw [e] at g2
    unfold revenue
    have := mul_lt_mul_of_pos_left g1 hα₁
    have := mul_le_mul_of_nonneg_left g2 hα₂.le
    have key : α₁ * (a * x ^ ((η - 1) / η) + b * y ^ ((η - 1) / η)) +
        α₂ * (a * (1 - x) ^ ((η - 1) / η) + b * (1 - y) ^ ((η - 1) / η)) <
        α₁ * (a * x + b * y) ^ ((η - 1) / η) + α₂ * (1 - (a * x + b * y)) ^ ((η - 1) / η) := by
      linarith
    have := mul_lt_mul_of_pos_right key hC
    linarith
  have hmem : optShare η α₁ α₂ ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨(im_share_pos hα₁ hα₂).le, by linarith [im_one_sub_share_pos (η := η) hα₁ hα₂]⟩
  have hmax : IsMaxOn (fun γ => revenue η α₁ α₂ γ Q) (Set.Icc 0 1) (optShare η α₁ α₂) := by
    intro γ hγ
    simp only [Set.mem_setOf_eq]
    have := (market_core η α₁ α₂ 1 hη hα₁ hα₂ one_pos).2.2.2 γ (1 - γ) hγ.1 (by linarith [hγ.2])
      (by linarith)
    simp only [mul_one] at this
    unfold revenue
    exact mul_le_mul_of_nonneg_right this hC.le
  exact ⟨hsc', hmem, hmax, fun γ hγ hm => im_unique_max hsc' hγ hmem hm hmax⟩

namespace Model

variable {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω)

lemma im_kfun_nonneg (ω : Ω) :
    0 ≤ (M.A₁ ω ^ M.η + M.A₂ ω ^ M.η) ^ (1 / M.η) * M.Y ω ^ ((M.η - 1) / M.η) :=
  mul_nonneg (Real.rpow_nonneg (im_S_pos (M.A₁_pos ω) (M.A₂_pos ω)).le _)
    (Real.rpow_nonneg (M.Y_mem ω).1 _)

lemma im_K_nonneg : 0 ≤ M.K := integral_nonneg (fun ω => M.im_kfun_nonneg ω)

lemma im_chainProfit_eq (e : ℝ) (he : 0 ≤ e) :
    M.chainProfit e = M.K * e ^ ((M.η - 1) / M.η) - M.c e := by
  unfold chainProfit K
  congr 1
  rw [← integral_mul_const]
  congr 1
  funext ω
  rw [optrev_core _ _ _ _ M.one_lt_η (M.A₁_pos ω) (M.A₂_pos ω),
    Real.mul_rpow (M.Y_mem ω).1 he]
  ring

lemma im_c_tangent {eo e : ℝ} (heo : 0 < eo) (he : 0 ≤ e) :
    M.c eo + M.c' eo * (e - eo) ≤ M.c e := by
  have hcv := M.c_strictConvex.convexOn
  have hd := M.c_hasDeriv eo heo
  rcases lt_trichotomy e eo with h | h | h
  · have := hcv.slope_le_of_hasDerivAt (show e ∈ Set.Ici (0:ℝ) from he)
      (show eo ∈ Set.Ici (0:ℝ) from heo.le) h hd
    rw [slope_def_field, div_le_iff₀ (by linarith)] at this
    nlinarith
  · subst h; simp
  · have := hcv.le_slope_of_hasDerivAt (show eo ∈ Set.Ici (0:ℝ) from heo.le)
      (show e ∈ Set.Ici (0:ℝ) from he) h hd
    rw [slope_def_field, le_div_iff₀ (by linarith)] at this
    nlinarith

theorem eq45_core :
    (∀ e : ℝ, 0 ≤ e → M.chainProfit e = M.K * e ^ ((M.η - 1) / M.η) - M.c e) ∧
    StrictConcaveOn ℝ (Set.Ici 0) M.chainProfit ∧
    (∀ e : ℝ, 0 < e →
      HasDerivAt M.chainProfit ((M.η - 1) / M.η * e ^ (-1 / M.η) * M.K - M.c' e) e) ∧
    ∀ eo : ℝ, 0 < eo →
      (IsMaxOn M.chainProfit (Set.Ici 0) eo ↔
        (M.η - 1) / M.η * eo ^ (-1 / M.η) * M.K - M.c' eo = 0) := by
  have hη := M.one_lt_η
  have hK := M.im_K_nonneg
  have hderiv : ∀ e : ℝ, 0 < e →
      HasDerivAt M.chainProfit ((M.η - 1) / M.η * e ^ (-1 / M.η) * M.K - M.c' e) e := by
    intro e he
    have h := ((Real.hasDerivAt_rpow_const (x := e) (p := (M.η - 1) / M.η)
      (Or.inl he.ne')).const_mul M.K).sub (M.c_hasDeriv e he)
    rw [im_r_sub_one hη] at h
    have h2 : HasDerivAt (fun x => M.K * x ^ ((M.η - 1) / M.η) - M.c x)
        ((M.η - 1) / M.η * e ^ (-1 / M.η) * M.K - M.c' e) e := h.congr_deriv (by ring)
    apply h2.congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds he] with x hx
    exact M.im_chainProfit_eq x hx.le
  refine ⟨M.im_chainProfit_eq, ?_, hderiv, ?_⟩
  · refine ⟨convex_Ici 0, ?_⟩
    intro x hx y hy hxy a b ha hb hab
    have hx' : (0:ℝ) ≤ x := hx
    have hy' : (0:ℝ) ≤ y := hy
    have hz : 0 ≤ a • x + b • y := by
      simp only [smul_eq_mul]; positivity
    rw [M.im_chainProfit_eq x hx', M.im_chainProfit_eq y hy', M.im_chainProfit_eq _ hz]
    have g1 := (im_rpow_strictConcave (im_r_pos hη) (im_r_lt_one hη)).concaveOn.2 hx hy
      ha.le hb.le hab
    have g2 := M.c_strictConvex.2 hx hy hxy ha hb hab
    simp only [smul_eq_mul] at g1 g2 ⊢
    have := mul_le_mul_of_nonneg_left g1 hK
    nlinarith
  · intro eo heo
    constructor
    · intro hm
      exact (hm.isLocalMax (Ici_mem_nhds heo)).hasDerivAt_eq_zero (hderiv eo heo)
    · intro hfoc e he
      have he' : (0:ℝ) ≤ e := he
      simp only [Set.mem_setOf_eq]
      rw [M.im_chainProfit_eq e he', M.im_chainProfit_eq eo heo.le]
      have t := im_tangent (im_r_pos hη) (im_r_lt_one hη) heo he'
      rw [im_r_sub_one hη] at t
      have t' := mul_le_mul_of_nonneg_left t hK
      have hc := M.im_c_tangent heo he'
      have : M.c' eo = (M.η - 1) / M.η * eo ^ (-1 / M.η) * M.K := by linarith
      rw [this] at hc
      nlinarith

lemma im_expOutput (e : ℝ) : M.expOutput e = (∫ ω, M.Y ω ∂M.P) * e := by
  unfold expOutput; exact integral_mul_const e _

lemma im_rpow_r_split {η e : ℝ} (hη : 1 < η) (he : 0 < e) :
    e ^ ((η - 1) / η) = e ^ (-1 / η) * e := by
  conv_rhs => rw [show e ^ (-1 / η) * e = e ^ (-1 / η) * e ^ (1:ℝ) by rw [Real.rpow_one]]
  rw [← Real.rpow_add he]
  congr 1; field_simp; ring

lemma im_expMarketRevenue (eo : ℝ) (heo : 0 < eo) :
    M.expMarketRevenue eo = (M.η - 1) / M.η * eo ^ ((M.η - 1) / M.η) * M.K := by
  have hη := M.one_lt_η
  unfold expMarketRevenue K
  rw [← integral_const_mul]
  congr 1
  funext ω
  have hY := (M.Y_mem ω).1
  have hQ : 0 ≤ M.Y ω * eo := mul_nonneg hY heo.le
  have key : (M.Y ω * eo) * (M.Y ω * eo) ^ (-1 / M.η) = (M.Y ω * eo) ^ ((M.η - 1) / M.η) := by
    rcases hQ.lt_or_eq with hQ' | hQ'
    · rw [im_rpow_r_split hη hQ']; ring
    · rw [← hQ', Real.zero_rpow (im_r_pos hη).ne']; simp
  unfold price
  calc M.Y ω * eo * ((M.η - 1) / M.η * (M.A₁ ω ^ M.η + M.A₂ ω ^ M.η) ^ (1 / M.η) *
        (M.Y ω * eo) ^ (-1 / M.η))
      = (M.η - 1) / M.η * (M.A₁ ω ^ M.η + M.A₂ ω ^ M.η) ^ (1 / M.η) *
        ((M.Y ω * eo) * (M.Y ω * eo) ^ (-1 / M.η)) := by ring
    _ = _ := by rw [key, Real.mul_rpow hY heo.le]; ring

theorem eq46_core (hY : 0 < ∫ ω, M.Y ω ∂M.P) (eo : ℝ) (heo : 0 < eo) :
    M.payRate eo = M.expMarketRevenue eo / M.expOutput eo := by
  rw [M.im_expMarketRevenue eo heo, M.im_expOutput, im_rpow_r_split M.one_lt_η heo]
  unfold payRate
  field_simp

theorem zero_profit_core (hY : 0 < ∫ ω, M.Y ω ∂M.P) (eo : ℝ) (heo : 0 < eo) :
    M.expMarketRevenue eo - M.payRate eo * M.expOutput eo = 0 := by
  rw [M.im_expMarketRevenue eo heo, M.im_expOutput, im_rpow_r_split M.one_lt_η heo]
  unfold payRate
  field_simp
  ring

lemma im_util_eq (hY : 0 < ∫ ω, M.Y ω ∂M.P) (eo e : ℝ) :
    M.managerUtility eo e = (M.η - 1) / M.η * eo ^ (-1 / M.η) * M.K * e - M.c e := by
  unfold managerUtility payRate
  rw [M.im_expOutput]
  field_simp

theorem manager_core (hY : 0 < ∫ ω, M.Y ω ∂M.P) (eo : ℝ) (heo : 0 < eo)
    (h45 : (M.η - 1) / M.η * eo ^ (-1 / M.η) * M.K - M.c' eo = 0) :
    (∀ e : ℝ, 0 < e → HasDerivAt (M.managerUtility eo)
      ((M.η - 1) / M.η * eo ^ (-1 / M.η) * M.K - M.c' e) e) ∧
    IsMaxOn (M.managerUtility eo) (Set.Ici 0) eo ∧
    (∀ e : ℝ, 0 ≤ e → IsMaxOn (M.managerUtility eo) (Set.Ici 0) e → e = eo) ∧
    M.expMarketRevenue eo - M.payRate eo * M.expOutput eo = 0 := by
  set L := (M.η - 1) / M.η * eo ^ (-1 / M.η) * M.K with hL
  have hfun : M.managerUtility eo = fun e => L * e - M.c e := by
    funext e; exact M.im_util_eq hY eo e
  have hmax : IsMaxOn (M.managerUtility eo) (Set.Ici 0) eo := by
    intro e he
    have he' : (0:ℝ) ≤ e := he
    simp only [Set.mem_setOf_eq]
    rw [hfun]
    have hc := M.im_c_tangent heo he'
    have : M.c' eo = L := by linarith
    rw [this] at hc
    simp only
    nlinarith
  have hsc : StrictConcaveOn ℝ (Set.Ici 0) (M.managerUtility eo) := by
    rw [hfun]
    refine ⟨convex_Ici 0, ?_⟩
    intro x hx y hy hxy a b ha hb hab
    have g2 := M.c_strictConvex.2 hx hy hxy ha hb hab
    simp only [smul_eq_mul] at g2 ⊢
    nlinarith
  refine ⟨?_, hmax, fun e he hm => im_unique_max hsc he heo.le hm hmax,
    M.zero_profit_core hY eo heo⟩
  intro e he
  rw [hfun]
  exact (((hasDerivAt_id e).const_mul L).sub (M.c_hasDeriv e he)).congr_deriv (by simp)

theorem goal_core :
    (∀ α₁ α₂ Q : ℝ, 0 < α₁ → 0 < α₂ → 0 < Q →
      (∀ q : ℝ, 0 ≤ q →
        (IsMaxOn (retailerProfit M.η α₁ (price M.η α₁ α₂ Q)) (Set.Ici 0) q ↔
          q = optShare M.η α₁ α₂ * Q)) ∧
      (∀ q : ℝ, 0 ≤ q →
        (IsMaxOn (retailerProfit M.η α₂ (price M.η α₁ α₂ Q)) (Set.Ici 0) q ↔
          q = (1 - optShare M.η α₁ α₂) * Q)) ∧
      (∀ q₁ q₂ : ℝ, 0 ≤ q₁ → 0 ≤ q₂ → q₁ + q₂ ≤ Q →
        α₁ * q₁ ^ ((M.η - 1) / M.η) + α₂ * q₂ ^ ((M.η - 1) / M.η) ≤
          α₁ * (optShare M.η α₁ α₂ * Q) ^ ((M.η - 1) / M.η) +
            α₂ * ((1 - optShare M.η α₁ α₂) * Q) ^ ((M.η - 1) / M.η)) ∧
      HasDerivAt (fun Q' => optRevenue M.η α₁ α₂ Q') (price M.η α₁ α₂ Q) Q) ∧
    (Integrable (fun ω => (M.A₁ ω ^ M.η + M.A₂ ω ^ M.η) ^ (1 / M.η) *
        M.Y ω ^ ((M.η - 1) / M.η)) M.P →
      0 < ∫ ω, M.Y ω ∂M.P →
      ∀ eo : ℝ, 0 < eo →
        (M.η - 1) / M.η * eo ^ (-1 / M.η) * M.K - M.c' eo = 0 →
        IsMaxOn (M.managerUtility eo) (Set.Ici 0) eo ∧
        (∀ e : ℝ, 0 ≤ e → IsMaxOn (M.managerUtility eo) (Set.Ici 0) e → e = eo) ∧
        M.payRate eo = M.expMarketRevenue eo / M.expOutput eo ∧
        M.expMarketRevenue eo - M.payRate eo * M.expOutput eo = 0) := by
  refine ⟨fun α₁ α₂ Q h1 h2 hQ => ?_, fun _ hY eo heo h45 => ?_⟩
  · obtain ⟨a, b, -, d⟩ := market_core M.η α₁ α₂ Q M.one_lt_η h1 h2 hQ
    exact ⟨a, b, d, marginal_core M.η α₁ α₂ Q M.one_lt_η h1 h2 hQ⟩
  · obtain ⟨-, b, c, d⟩ := M.manager_core hY eo heo h45
    exact ⟨b, c, M.eq46_core hY eo heo, d⟩

end Model

end CachonCoord.InternalMarket

open CachonCoord.InternalMarket
open MeasureTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω)
    (hint : Integrable (fun ω => (M.A₁ ω ^ M.η + M.A₂ ω ^ M.η) ^ (1 / M.η) *
      M.Y ω ^ ((M.η - 1) / M.η)) M.P)
    (hY : 0 < ∫ ω, M.Y ω ∂M.P) (eo : ℝ) (heo : 0 < eo) :
    M.payRate eo = M.expMarketRevenue eo / M.expOutput eo := by
  exact Model.eq46_core M hY eo heo
