-- Prove2me | solution 1 for ChannelRebate.ReturnsEffort.proposition4_returns_increase_effort
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T23:46:29.152203+00:00
-- url     : https://prove2.me/submissions/8cf86211-c456-4f37-93ae-7e10234584d6

import Mathlib
import Definitions.Def_ChannelRebate_ReturnsEffort_Setting

open MeasureTheory ChannelRebate.ReturnsEffort

namespace RetEffortProp4Aux

/-- integral against the law equals integral against the density -/
lemma integral_law (D : Demand) (g : ℝ → ℝ) :
    ∫ x, g x ∂D.law = ∫ x, D.φ x * g x := by
  unfold Demand.law
  rw [integral_withDensity_eq_integral_toReal_smul (D.measurable_φ.ennreal_ofReal)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  congr 1
  ext x
  have hφ : 0 ≤ D.φ x := by
    rcases lt_or_ge x 0 with h | h
    · exact (D.φ_eq_zero_of_neg x h).ge
    · exact (D.φ_pos x h).le
  rw [ENNReal.toReal_ofReal hφ, smul_eq_mul]

lemma integral_map_mul (D : Demand) (e : ℝ) (g : ℝ → ℝ) (hg : Continuous g) :
    ∫ y, g y ∂(D.law.map (fun x => e * x)) = ∫ x, g (e * x) ∂D.law := by
  rw [integral_map (measurable_const_mul e).aemeasurable hg.aestronglyMeasurable]

/-- the "revenue" part `F_b(Q,e) = R_b(Q,e) + V(e)` -/
noncomputable def F (p w b : ℝ) (D : Demand) (Q e : ℝ) : ℝ :=
  -w * Q + p * CachonCoord.Newsvendor.expSales (D.law.map (fun x => e * x)) Q
    + b * CachonCoord.Newsvendor.expLeftover (D.law.map (fun x => e * x)) Q

lemma profit_eq (p w b : ℝ) (D : Demand) (V : EffortCost) (Q e : ℝ) :
    returnsProfit p w b D V Q e = F p w b D Q e - V.V e := rfl

lemma sales_eq (D : Demand) (Q e : ℝ) :
    CachonCoord.Newsvendor.expSales (D.law.map (fun x => e * x)) Q
      = ∫ x, D.φ x * min Q (e * x) := by
  unfold CachonCoord.Newsvendor.expSales
  rw [integral_map_mul D e (fun y => min Q y) (by fun_prop), integral_law]

lemma leftover_eq (D : Demand) (Q e : ℝ) :
    CachonCoord.Newsvendor.expLeftover (D.law.map (fun x => e * x)) Q
      = ∫ x, D.φ x * max (Q - e * x) 0 := by
  unfold CachonCoord.Newsvendor.expLeftover
  rw [integral_map_mul D e (fun y => max (Q - y) 0) (by fun_prop), integral_law]

lemma F_hom (p w b : ℝ) (D : Demand) (Q e t : ℝ) (ht : 0 ≤ t) :
    F p w b D (t * Q) (t * e) = t * F p w b D Q e := by
  unfold F
  rw [sales_eq, sales_eq, leftover_eq, leftover_eq]
  have h1 : (fun x => D.φ x * min (t * Q) (t * e * x)) = fun x => t * (D.φ x * min Q (e * x)) := by
    ext x
    rw [mul_assoc t e x, ← mul_min_of_nonneg _ _ ht]; ring
  have h2 : (fun x => D.φ x * max (t * Q - t * e * x) 0) =
      fun x => t * (D.φ x * max (Q - e * x) 0) := by
    ext x
    have : t * Q - t * e * x = t * (Q - e * x) := by ring
    rw [this, show (0:ℝ) = t * 0 by ring, ← mul_max_of_nonneg _ _ ht]; ring
  rw [h1, h2, integral_const_mul, integral_const_mul]; ring

lemma F_sub (p w b₁ b₂ : ℝ) (D : Demand) (Q e : ℝ) :
    F p w b₁ D Q e = F p w b₂ D Q e + (b₁ - b₂) * ∫ x, D.φ x * max (Q - e * x) 0 := by
  unfold F; rw [leftover_eq]; ring

lemma φ_nonneg (D : Demand) (x : ℝ) : 0 ≤ D.φ x := by
  rcases lt_or_ge x 0 with h | h
  · exact (D.φ_eq_zero_of_neg x h).ge
  · exact (D.φ_pos x h).le

lemma F_zero_effort (p w b : ℝ) (D : Demand) (Q : ℝ) (hQ : 0 ≤ Q) :
    F p w b D Q 0 = (b - w) * Q := by
  unfold F; rw [sales_eq, leftover_eq]
  have h1 : (fun x => D.φ x * min Q (0 * x)) = fun _ => (0:ℝ) := by
    ext x; simp [min_eq_right hQ]
  have h2 : (fun x => D.φ x * max (Q - 0 * x) 0) = fun x => Q * D.φ x := by
    ext x; simp [max_eq_left hQ]; ring
  rw [h1, h2, integral_const_mul, D.integral_φ]; simp; ring

lemma F_zero_order (p w b : ℝ) (D : Demand) (e : ℝ) (he : 0 ≤ e) :
    F p w b D 0 e = 0 := by
  unfold F; rw [sales_eq, leftover_eq]
  have h1 : (fun x => D.φ x * min 0 (e * x)) = fun _ => (0:ℝ) := by
    ext x
    rcases lt_or_ge x 0 with h | h
    · simp [D.φ_eq_zero_of_neg x h]
    · simp [min_eq_left (mul_nonneg he h)]
  have h2 : (fun x => D.φ x * max (0 - e * x) 0) = fun _ => (0:ℝ) := by
    ext x
    rcases lt_or_ge x 0 with h | h
    · simp [D.φ_eq_zero_of_neg x h]
    · have : 0 - e * x ≤ 0 := by nlinarith
      simp [mul_nonneg he h]
  rw [h1, h2]; simp

lemma leftover_pos (D : Demand) (Q e : ℝ) (hQ : 0 < Q) (he : 0 < e) :
    0 < ∫ x, D.φ x * max (Q - e * x) 0 := by
  have hnn : 0 ≤ fun x => D.φ x * max (Q - e * x) 0 := fun x =>
    mul_nonneg (φ_nonneg D x) (le_max_right _ _)
  have hint : Integrable (fun x => D.φ x * max (Q - e * x) 0) := by
    refine Integrable.mono' (D.integrable_φ.const_mul Q) ?_ ?_
    · exact (D.measurable_φ.mul (by fun_prop)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (hnn x)]
      rcases lt_or_ge x 0 with h | h
      · simp [D.φ_eq_zero_of_neg x h]
      · have : max (Q - e * x) 0 ≤ Q := max_le (by nlinarith) hQ.le
        nlinarith [φ_nonneg D x]
  rw [integral_pos_iff_support_of_nonneg hnn hint]
  have hsub : Set.Ico 0 (Q / e) ⊆ Function.support (fun x => D.φ x * max (Q - e * x) 0) := by
    intro x hx
    simp only [Function.mem_support]
    have h1 := D.φ_pos x hx.1
    have h2 : 0 < Q - e * x := by
      have := hx.2; rw [lt_div_iff₀ he] at this; linarith
    exact (mul_pos h1 (lt_max_of_lt_left h2)).ne'
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [Real.volume_Ico]; simp [div_pos hQ he]

/-- First-order condition along the ray through an optimal pair. -/
lemma ray_foc (p w b : ℝ) (D : Demand) (V : EffortCost) (V' : ℝ → ℝ)
    (hV' : ∀ e > 0, HasDerivAt V.V (V' e) e) (Q e : ℝ)
    (h : IsOptimalPair (returnsProfit p w b D V) Q e) (he : 0 < e) :
    V' e = F p w b D Q e / e := by
  set A := F p w b D Q e
  let h' : ℝ → ℝ := fun x => x / e * A - V.V x
  have hmax : IsLocalMax h' e := by
    have : Set.Ioi (0:ℝ) ∈ nhds e := Ioi_mem_nhds he
    filter_upwards [this] with x hx
    have hx' : (0:ℝ) < x := hx
    have ht : 0 ≤ x / e := (div_pos hx' he).le
    have key := h.2.2 (x / e * Q) x (mul_nonneg ht h.1) hx'.le
    rw [profit_eq, profit_eq] at key
    have hx2 : x = x / e * e := by field_simp
    have hh := F_hom p w b D Q e (x / e) ht
    rw [← hx2] at hh
    simp only [h']
    rw [div_self he.ne', one_mul]
    linarith
  have hd : HasDerivAt h' (1 / e * A - V' e) e := by
    have := ((hasDerivAt_id e).div_const e).mul_const A
    simp only [id] at this
    exact this.sub (hV' e he)
  have := hmax.hasDerivAt_eq_zero hd
  field_simp at this ⊢
  linarith

end RetEffortProp4Aux

open RetEffortProp4Aux in
theorem solution (p c s w : ℝ) (hc : 0 < c) (hcw : c < w)
    (hwp : w < p) (hsc : s < c) (D : Demand) (V : EffortCost) (V' : ℝ → ℝ)
    (hV' : ∀ e > 0, HasDerivAt V.V (V' e) e) (b₁ b₂ : ℝ) (hs : s ≤ b₂) (h12 : b₂ < b₁)
    (hw : b₁ < w) (Q₁ e₁ Q₂ e₂ : ℝ) (h₁ : IsOptimalPair (returnsProfit p w b₁ D V) Q₁ e₁)
    (h₂ : IsOptimalPair (returnsProfit p w b₂ D V) Q₂ e₂) (he₂ : 0 < e₂) :
    e₂ < e₁ := by
  -- Q₂ > 0
  have hQ₂ : 0 < Q₂ := by
    rcases (h₂.1).lt_or_eq with h | h
    · exact h
    · exfalso
      have key := h₂.2.2 0 0 le_rfl le_rfl
      rw [profit_eq, profit_eq, ← h, F_zero_order _ _ _ _ _ he₂.le,
        F_zero_order _ _ _ _ _ le_rfl, V.V_zero] at key
      have : V.V 0 < V.V e₂ := V.strictMonoOn (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 he₂.le) he₂
      rw [V.V_zero] at this
      linarith
  set I₂ := ∫ x, D.φ x * max (Q₂ - e₂ * x) 0 with hI₂
  have hI₂pos : 0 < I₂ := leftover_pos D Q₂ e₂ hQ₂ he₂
  set B := F p w b₂ D Q₂ e₂
  set C := F p w b₁ D Q₂ e₂
  have hC : C = B + (b₁ - b₂) * I₂ := F_sub p w b₁ b₂ D Q₂ e₂
  have hCB : B < C := by rw [hC]; nlinarith
  -- B - V e₂ ≥ 0
  have hB0 : 0 ≤ B - V.V e₂ := by
    have key := h₂.2.2 0 0 le_rfl le_rfl
    rw [profit_eq, profit_eq, F_zero_order _ _ _ _ _ le_rfl, V.V_zero] at key
    linarith
  rcases (h₁.2.1).lt_or_eq with he₁ | he₁
  · set A := F p w b₁ D Q₁ e₁
    -- (iii): (e₁/e₂) C ≤ A
    have h3 : e₁ / e₂ * C ≤ A := by
      have ht : 0 ≤ e₁ / e₂ := (div_pos he₁ he₂).le
      have key := h₁.2.2 (e₁ / e₂ * Q₂) e₁ (mul_nonneg ht h₂.1) he₁.le
      rw [profit_eq, profit_eq] at key
      have hh := F_hom p w b₁ D Q₂ e₂ (e₁ / e₂) ht
      rw [show e₁ / e₂ * e₂ = e₁ by field_simp] at hh
      linarith
    -- (i)
    have h1 : e₂ / e₁ * A - V.V e₂ ≤ A - V.V e₁ := by
      have ht : 0 ≤ e₂ / e₁ := (div_pos he₂ he₁).le
      have key := h₁.2.2 (e₂ / e₁ * Q₁) e₂ (mul_nonneg ht h₁.1) he₂.le
      rw [profit_eq, profit_eq] at key
      have hh := F_hom p w b₁ D Q₁ e₁ (e₂ / e₁) ht
      rw [show e₂ / e₁ * e₁ = e₂ by field_simp] at hh
      linarith
    -- (ii)
    have h2 : e₁ / e₂ * B - V.V e₁ ≤ B - V.V e₂ := by
      have ht : 0 ≤ e₁ / e₂ := (div_pos he₁ he₂).le
      have key := h₂.2.2 (e₁ / e₂ * Q₂) e₁ (mul_nonneg ht h₂.1) he₁.le
      rw [profit_eq, profit_eq] at key
      have hh := F_hom p w b₂ D Q₂ e₂ (e₁ / e₂) ht
      rw [show e₁ / e₂ * e₂ = e₁ by field_simp] at hh
      linarith
    have hf1 := ray_foc p w b₁ D V V' hV' Q₁ e₁ h₁ he₁
    have hf2 := ray_foc p w b₂ D V V' hV' Q₂ e₂ h₂ he₂
    -- multiply out
    have h3' : e₁ * C ≤ e₂ * A := by
      have := mul_le_mul_of_nonneg_left h3 he₂.le
      rwa [← mul_assoc, mul_div_cancel₀ _ he₂.ne'] at this
    have h1' : e₂ * A - e₁ * V.V e₂ ≤ e₁ * A - e₁ * V.V e₁ := by
      have := mul_le_mul_of_nonneg_left h1 he₁.le
      rw [mul_sub, ← mul_assoc, mul_div_cancel₀ _ he₁.ne', mul_sub] at this
      linarith
    have h2' : e₁ * B - e₂ * V.V e₁ ≤ e₂ * B - e₂ * V.V e₂ := by
      have := mul_le_mul_of_nonneg_left h2 he₂.le
      rw [mul_sub, ← mul_assoc, mul_div_cancel₀ _ he₂.ne', mul_sub] at this
      linarith
    have hge : e₂ ≤ e₁ := by
      by_contra hlt
      push Not at hlt
      have hpos : 0 < e₂ * A - e₁ * B := by nlinarith
      nlinarith [mul_pos (sub_pos.2 hlt) hpos]
    rcases hge.lt_or_eq with h | h
    · exact h
    · exfalso
      have hAB : A / e₂ = B / e₂ := by rw [← hf2, h, hf1]
      have hAB' := (div_left_inj' he₂.ne').mp hAB
      rw [h, div_self he₁.ne', one_mul] at h3
      linarith
  · exfalso
    have key := h₂.2.2 0 0 le_rfl le_rfl
    have key1 := h₁.2.2 Q₂ e₂ h₂.1 he₂.le
    rw [profit_eq, profit_eq, ← he₁, F_zero_effort _ _ _ _ _ h₁.1, V.V_zero] at key1
    have : (b₁ - w) * Q₁ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) h₁.1
    linarith
