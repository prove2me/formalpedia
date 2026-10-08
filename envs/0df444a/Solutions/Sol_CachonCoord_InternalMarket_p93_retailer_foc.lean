-- Prove2me | solution 1 for CachonCoord.InternalMarket.p93_retailer_foc
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T06:47:27.651608+00:00
-- url     : https://prove2.me/submissions/505ec5a2-35bc-4eb5-97a4-19cc93ee7a83

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

end CachonCoord.InternalMarket

open CachonCoord.InternalMarket


theorem solution (η αᵢ w : ℝ) (hη : 1 < η) (hα : 0 < αᵢ) (hw : 0 < w) :
    (∀ q : ℝ, 0 < q →
      HasDerivAt (retailerProfit η αᵢ w) ((η - 1) / η * αᵢ * q ^ (-1 / η) - w) q) ∧
    ∀ q : ℝ, 0 ≤ q →
      (IsMaxOn (retailerProfit η αᵢ w) (Set.Ici 0) q ↔
        0 < q ∧ (η - 1) / η * αᵢ * q ^ (-1 / η) - w = 0) := by
  exact foc_core η αᵢ w hη hα hw
