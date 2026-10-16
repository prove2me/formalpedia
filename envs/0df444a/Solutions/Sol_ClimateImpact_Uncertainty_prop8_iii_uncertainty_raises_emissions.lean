-- Prove2me | solution 1 for ClimateImpact.Uncertainty.prop8_iii_uncertainty_raises_emissions
-- status  : ACCEPTED   (prove)
-- author  : @frknbls
-- created : 2026-10-15T17:47:14.7999+00:00
-- url     : https://prove2.me/submissions/2fb92292-34c7-4ffe-99d0-8debce1e895e

import Definitions.Def_ClimateImpact_Uncertainty_FixedPoint

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Matrix Filter

namespace ClimateImpact.Uncertainty

open ClimateImpact.Interaction

lemma c8_beta_facts (ρ T t : ℝ) (hρ : 0 < ρ) (hT : 0 < T) (ht : t ∈ Set.Icc 0 T) :
    0 ≤ beta ρ T t ∧ 0 ≤ betaC ρ T t ∧ beta ρ T t + betaC ρ T t = 1 := by
  have hE : 0 < 1 - Real.exp (-(ρ * T)) := by
    have : Real.exp (-(ρ * T)) < 1 := by
      rw [Real.exp_lt_one_iff]; nlinarith
    linarith
  have h1 : Real.exp (-(ρ * t)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [ht.1]
  have h2 : Real.exp (-(ρ * T)) ≤ Real.exp (-(ρ * t)) := by
    rw [Real.exp_le_exp]; nlinarith [ht.2]
  refine ⟨div_nonneg (by linarith) hE.le, div_nonneg (by linarith) hE.le, ?_⟩
  unfold beta betaC
  rw [← add_div, div_eq_one_iff_eq hE.ne']
  ring

lemma c8_den_pos (ρ T t α κ κc : ℝ) (hα0 : 0 < α) (hρ : 0 < ρ) (hT : 0 < T)
    (ht : t ∈ Set.Icc 0 T) (hκ : 0 < κ) (hκc : 0 < κc) (y : ℝ) (hy : 0 < y) :
    0 < α * beta ρ T t * κ * y + betaC ρ T t * κc := by
  obtain ⟨hb, hbc, hsum⟩ := c8_beta_facts ρ T t hρ hT ht
  rcases hb.lt_or_eq with h | h
  · have : 0 < α * beta ρ T t * κ * y := by positivity
    have : 0 ≤ betaC ρ T t * κc := by positivity
    linarith
  · have hc1 : betaC ρ T t = 1 := by linarith
    rw [← h, hc1]; simpa using hκc

lemma c8_sched_anti {n : ℕ} (ρ T t α κ κc : ℝ) (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hα0 : 0 < α) (hρ : 0 < ρ) (hT : 0 < T)
    (ht : t ∈ Set.Icc 0 T) (hκ : 0 < κ) (hκc : 0 < κc) (y1 y2 : ℝ) (hy1 : 0 < y1)
    (h12 : y1 ≤ y2) (i : Fin n) :
    schedule ρ T t α κ κc c y2 i ≤ schedule ρ T t α κ κc c y1 i := by
  unfold schedule
  have hd1 := c8_den_pos ρ T t α κ κc hα0 hρ hT ht hκ hκc y1 hy1
  have hb := (c8_beta_facts ρ T t hρ hT ht).1
  have hle : α * beta ρ T t * κ * y1 + betaC ρ T t * κc ≤
      α * beta ρ T t * κ * y2 + betaC ρ T t * κc := by
    have : 0 ≤ α * beta ρ T t * κ := by positivity
    nlinarith
  exact div_le_div_of_nonneg_left (hc i) hd1 hle

lemma c8_sched_nonneg {n : ℕ} (ρ T t α κ κc : ℝ) (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hα0 : 0 < α) (hρ : 0 < ρ) (hT : 0 < T)
    (ht : t ∈ Set.Icc 0 T) (hκ : 0 < κ) (hκc : 0 < κc) (y : ℝ) (hy : 0 < y) (i : Fin n) :
    0 ≤ schedule ρ T t α κ κc c y i :=
  div_nonneg (hc i) (c8_den_pos ρ T t α κ κc hα0 hρ hT ht hκ hκc y hy).le

lemma c8_ext_mono {n : ℕ} (ρ T t α κ κc κ₀ : ℝ) (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hα0 : 0 < α) (hρ : 0 < ρ) (hT : 0 < T)
    (ht : t ∈ Set.Icc 0 T) (hκ : 0 < κ) (hκc : 0 < κc) (y1 y2 : ℝ) (hy1 : 0 < y1)
    (h12 : y1 ≤ y2) (i : Fin n) :
    extAt ρ T t α κ κc κ₀ c y1 i ≤ extAt ρ T t α κ κc κ₀ c y2 i := by
  unfold extAt quadExt
  have ha := c8_sched_anti ρ T t α κ κc c hc hα0 hρ hT ht hκ hκc y1 y2 hy1 h12 i
  have hn := c8_sched_nonneg ρ T t α κ κc c hc hα0 hρ hT ht hκ hκc y2 (by linarith) i
  have hsq : schedule ρ T t α κ κc c y2 i ^ 2 ≤ schedule ρ T t α κ κc c y1 i ^ 2 :=
    pow_le_pow_left₀ hn ha 2
  have : 0 ≤ κ / 2 := by positivity
  nlinarith

lemma c8_quad_expand {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hsym : Pᵀ = P)
    (u d : Fin n → ℝ) :
    (u + d) ⬝ᵥ (P *ᵥ (u + d)) =
      u ⬝ᵥ (P *ᵥ u) + 2 * (d ⬝ᵥ (P *ᵥ u)) + d ⬝ᵥ (P *ᵥ d) := by
  have hcross : u ⬝ᵥ (P *ᵥ d) = d ⬝ᵥ (P *ᵥ u) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hsym, dotProduct_comm]
  rw [mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, hcross]
  ring

lemma c8_gStar_mono {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (α γr : ℝ) (hα0 : 0 < α) (hγr : 0 < γr)
    (ρ T t : ℝ) (hρ : 0 < ρ) (hT : 0 < T) (ht : t ∈ Set.Icc 0 T)
    (κ κc κ₀ : ℝ) (hκ : 0 < κ) (hκc : 0 < κc)
    (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (h24 : Cond24 S γr ρ T t α κ κc κ₀ c) (y1 y2 : ℝ) (hy1 : 0 < y1) (h12 : y1 ≤ y2) :
    gStar S γr ρ T t α κ κc κ₀ c y1 ≤ gStar S γr ρ T t α κ κc κ₀ c y2 := by
  set θ1 := extAt ρ T t α κ κc κ₀ c y1 with hθ1
  set θ2 := extAt ρ T t α κ κc κ₀ c y2 with hθ2
  have hP := hS.inv
  have hPsd : ∀ x : Fin n → ℝ, 0 ≤ x ⬝ᵥ (S⁻¹ *ᵥ x) := fun x => by
    simpa using hP.posSemidef.dotProduct_mulVec_nonneg x
  have hsym : (S⁻¹)ᵀ = S⁻¹ := by
    have := hP.isHermitian
    simpa [IsHermitian, conjTranspose_eq_transpose_of_trivial] using this
  set d : Fin n → ℝ := fun i => θ2 i - θ1 i with hd
  have hdn : ∀ i, 0 ≤ d i := fun i => by
    simp only [hd]
    have := c8_ext_mono ρ T t α κ κc κ₀ c hc hα0 hρ hT ht hκ hκc y1 y2 hy1 h12 i
    linarith
  have hθ2e : θ2 = θ1 + d := by funext i; simp [hd]
  set Q1 := θ1 ⬝ᵥ (S⁻¹ *ᵥ θ1)
  set Q2 := θ2 ⬝ᵥ (S⁻¹ *ᵥ θ2)
  set Qd := d ⬝ᵥ (S⁻¹ *ᵥ d)
  set X := d ⬝ᵥ (S⁻¹ *ᵥ θ1)
  have hQ : Q2 = Q1 + 2 * X + Qd := by
    simp only [Q2, Q1, X, Qd]
    rw [hθ2e]; exact c8_quad_expand _ hsym θ1 d
  have hQ2n : 0 ≤ Q2 := hPsd θ2
  have hQdn : 0 ≤ Qd := hPsd d
  have hsum : ∑ i, θ2 i = ∑ i, θ1 i + ∑ i, d i := by
    rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun i _ => ?_; simp [hd]
  -- termwise bound from Cond24
  have hterm : ∀ i, 0 ≤ d i * (1 + 2 / γr * (y1 * (S⁻¹ *ᵥ θ1) i)) := by
    intro i
    have hc24 := h24 i y1 hy1
    have hw : y1 * (S⁻¹ *ᵥ θ1) i = ∑ j, S⁻¹ i j * y1 * extAt ρ T t α κ κc κ₀ c y1 j := by
      simp only [mulVec, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hw]
    apply mul_nonneg (hdn i)
    have h2 : 0 ≤ 2 / γr := by positivity
    have := mul_le_mul_of_nonneg_left hc24 h2
    have he : 2 / γr * (-(γr / 2)) = -1 := by field_simp
    linarith
  have hlin : ∑ i, d i * (1 + 2 / γr * (y1 * (S⁻¹ *ᵥ θ1) i)) =
      ∑ i, d i + 2 * y1 / γr * X := by
    simp only [X, dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hA : 0 ≤ ∑ i, d i + 2 * y1 / γr * X := by
    rw [← hlin]; exact Finset.sum_nonneg fun i _ => hterm i
  have hB : 0 ≤ (y2 - y1) / γr * Q2 + y1 / γr * Qd := by
    have : 0 ≤ y2 - y1 := by linarith
    positivity
  have key : gStar S γr ρ T t α κ κc κ₀ c y2 - gStar S γr ρ T t α κ κc κ₀ c y1 =
      (∑ i, d i + 2 * y1 / γr * X) + ((y2 - y1) / γr * Q2 + y1 / γr * Qd) := by
    unfold gStar quadForm
    rw [← hθ1, ← hθ2]
    change (∑ i, θ2 i + y2 / γr * Q2) - (∑ i, θ1 i + y1 / γr * Q1) = _
    rw [hsum]
    have hQ1 : Q1 = Q2 - 2 * X - Qd := by linarith
    rw [hQ1]
    field_simp
    ring
  linarith

lemma c8_core (G Y : ℝ → ℝ) (K : ℝ) (hK : 0 < K)
    (hG : ∀ y1 y2, 0 < y1 → y1 ≤ y2 → G y1 ≤ G y2)
    (hY : ∀ lam : ℝ, 0 < lam → 0 < Y lam ∧ Y lam = Real.exp (-(K / lam) * G (Y lam))) :
    (0 < G 1 → StrictMonoOn Y (Set.Ioi 0) ∧ Tendsto Y atTop (nhds 1)) ∧
    (G 1 < 0 → StrictAntiOn Y (Set.Ioi 0) ∧ Tendsto Y atTop (nhds 1)) ∧
    (G 1 = 0 → ∀ lam : ℝ, 0 < lam → Y lam = 1) := by
  have hKl : Tendsto (fun lam : ℝ => K / lam) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hlim : ∀ g : ℝ, Tendsto (fun lam : ℝ => Real.exp (-(K / lam) * g)) atTop (nhds 1) := by
    intro g
    have : Tendsto (fun lam : ℝ => -(K / lam) * g) atTop (nhds (-(0:ℝ) * g)) :=
      (hKl.neg).mul_const g
    simpa [Function.comp_def] using (Real.continuous_exp.tendsto _).comp this
  have hpos : ∀ᶠ lam : ℝ in atTop, 0 < lam := eventually_gt_atTop 0
  refine ⟨fun h1 => ?_, fun h1 => ?_, fun h1 => ?_⟩
  · -- facts: Y < 1, 0 < G Y, G Y ≤ G 1
    have hlt : ∀ lam, 0 < lam → Y lam < 1 ∧ 0 < G (Y lam) := by
      intro lam hl
      obtain ⟨hy, he⟩ := hY lam hl
      have hk : 0 < K / lam := by positivity
      by_contra hcon
      rcases not_and_or.mp hcon with h | h
      · push Not at h
        have hg := hG 1 (Y lam) one_pos h
        have : Real.exp (-(K / lam) * G (Y lam)) < 1 := by
          rw [Real.exp_lt_one_iff]; nlinarith
        linarith
      · push Not at h
        have : 1 ≤ Real.exp (-(K / lam) * G (Y lam)) := by
          rw [Real.one_le_exp_iff]; nlinarith
        have hY1 : 1 ≤ Y lam := by linarith
        have hg := hG 1 (Y lam) one_pos hY1
        linarith
    refine ⟨?_, ?_⟩
    · intro l1 hl1 l2 hl2 h12
      simp only [Set.mem_Ioi] at hl1 hl2
      by_contra hcon
      push Not at hcon
      obtain ⟨hy1, he1⟩ := hY l1 hl1
      obtain ⟨hy2, he2⟩ := hY l2 hl2
      have hg := hG _ _ hy2 hcon
      have hG2 := (hlt l2 hl2).2
      have hk : K / l2 < K / l1 := div_lt_div_of_pos_left hK hl1 h12
      have hk2 : 0 < K / l2 := by positivity
      have : -(K / l1) * G (Y l1) < -(K / l2) * G (Y l2) := by nlinarith
      have := Real.exp_lt_exp.mpr this
      linarith
    · refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hlim (G 1)) tendsto_const_nhds ?_ ?_
      · filter_upwards [hpos] with lam hl
        obtain ⟨hy, he⟩ := hY lam hl
        have hk : 0 < K / lam := by positivity
        have hg := hG _ _ hy (hlt lam hl).1.le
        rw [he]
        apply Real.exp_le_exp.mpr
        nlinarith
      · filter_upwards [hpos] with lam hl
        exact (hlt lam hl).1.le
  · have hlt : ∀ lam, 0 < lam → 1 < Y lam ∧ G (Y lam) < 0 := by
      intro lam hl
      obtain ⟨hy, he⟩ := hY lam hl
      have hk : 0 < K / lam := by positivity
      by_contra hcon
      rcases not_and_or.mp hcon with h | h
      · push Not at h
        have hg := hG (Y lam) 1 hy h
        have : 1 < Real.exp (-(K / lam) * G (Y lam)) := by
          rw [Real.one_lt_exp_iff]; nlinarith
        linarith
      · push Not at h
        have : Real.exp (-(K / lam) * G (Y lam)) ≤ 1 := by
          rw [Real.exp_le_one_iff]; nlinarith
        have hY1 : Y lam ≤ 1 := by linarith
        have hg := hG (Y lam) 1 hy hY1
        linarith
    refine ⟨?_, ?_⟩
    · intro l1 hl1 l2 hl2 h12
      simp only [Set.mem_Ioi] at hl1 hl2
      by_contra hcon
      push Not at hcon
      obtain ⟨hy1, he1⟩ := hY l1 hl1
      obtain ⟨hy2, he2⟩ := hY l2 hl2
      have hg := hG _ _ hy1 hcon
      have hG2 := (hlt l2 hl2).2
      have hk : K / l2 < K / l1 := div_lt_div_of_pos_left hK hl1 h12
      have hk2 : 0 < K / l2 := by positivity
      have : -(K / l2) * G (Y l2) < -(K / l1) * G (Y l1) := by nlinarith
      have := Real.exp_lt_exp.mpr this
      linarith
    · refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hlim (G 1)) ?_ ?_
      · filter_upwards [hpos] with lam hl
        exact (hlt lam hl).1.le
      · filter_upwards [hpos] with lam hl
        obtain ⟨hy, he⟩ := hY lam hl
        have hk : 0 < K / lam := by positivity
        have hg := hG _ _ one_pos (hlt lam hl).1.le
        rw [he]
        apply Real.exp_le_exp.mpr
        nlinarith
  · intro lam hl
    obtain ⟨hy, he⟩ := hY lam hl
    have hk : 0 < K / lam := by positivity
    rcases lt_trichotomy (Y lam) 1 with h | h | h
    · exfalso
      have hg := hG _ _ hy h.le
      have : 1 ≤ Real.exp (-(K / lam) * G (Y lam)) := by
        rw [Real.one_le_exp_iff]; nlinarith
      linarith
    · exact h
    · exfalso
      have hg := hG _ _ one_pos h.le
      have : Real.exp (-(K / lam) * G (Y lam)) ≤ 1 := by
        rw [Real.exp_le_one_iff]; nlinarith
      linarith

lemma c8_ext0 {n : ℕ} (ρ T t α κ κc κ₀ : ℝ) (c : Fin n → ℝ) :
    ext0 ρ T t α κ κc κ₀ c = extAt ρ T t α κ κc κ₀ c 1 := by
  funext i
  unfold ext0 extAt schedule noInteractionRate
  rw [mul_one, add_comm]

lemma c8_sign {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (α γr : ℝ) (θ : Fin n → ℝ) :
    θ ⬝ᵥ greenPortfolio S α γr θ 1 = α * (∑ i, θ i + 1 / γr * quadForm S θ) := by
  unfold greenPortfolio quadForm
  simp only [dotProduct, mul_add, Finset.mul_sum, Finset.sum_add_distrib]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by ring
  · exact Finset.sum_congr rfl fun i _ => by ring

theorem prop8_iii_uncertainty_raises_emissions {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (α γr γg : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hγr : 0 < γr) (hγg : 0 < γg)
    (ρ T t : ℝ) (hρ : 0 < ρ) (hT : 0 < T) (ht : t ∈ Set.Icc 0 T)
    (κ κc κ₀ : ℝ) (hκ : 0 < κ) (hκc : 0 < κc) (hκ₀ : 0 < κ₀)
    (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (h24 : Cond24 S γr ρ T t α κ κc κ₀ c)
    (Y : ℝ → ℝ) (hY : ∀ lam : ℝ, 0 < lam → IsYStar S γr γg lam ρ T t α κ κc κ₀ c (Y lam)) :
    (0 < ext0 ρ T t α κ κc κ₀ c ⬝ᵥ greenPortfolio S α γr (ext0 ρ T t α κ κc κ₀ c) 1 →
      (∀ lam : ℝ, 0 < lam → 0 < Y lam) ∧ StrictMonoOn Y (Set.Ioi 0) ∧
        Filter.Tendsto Y Filter.atTop (nhds 1) ∧
        ∀ i, AntitoneOn (fun lam => schedule ρ T t α κ κc c (Y lam) i) (Set.Ioi 0)) ∧
    (ext0 ρ T t α κ κc κ₀ c ⬝ᵥ greenPortfolio S α γr (ext0 ρ T t α κ κc κ₀ c) 1 < 0 →
      (∀ lam : ℝ, 0 < lam → 0 < Y lam) ∧ StrictAntiOn Y (Set.Ioi 0) ∧
        Filter.Tendsto Y Filter.atTop (nhds 1) ∧
        ∀ i, MonotoneOn (fun lam => schedule ρ T t α κ κc c (Y lam) i) (Set.Ioi 0)) ∧
    (ext0 ρ T t α κ κc κ₀ c ⬝ᵥ greenPortfolio S α γr (ext0 ρ T t α κ κc κ₀ c) 1 = 0 →
      ∀ lam : ℝ, 0 < lam → Y lam = 1 ∧ schedule ρ T t α κ κc c (Y lam) = schedule ρ T t α κ κc c 1) := by
  set G := gStar S γr ρ T t α κ κc κ₀ c with hGdef
  have hsign : ext0 ρ T t α κ κc κ₀ c ⬝ᵥ greenPortfolio S α γr (ext0 ρ T t α κ κc κ₀ c) 1
      = α * G 1 := by
    rw [c8_ext0, c8_sign]
    simp [hGdef, gStar]
  rw [hsign]
  have hGm : ∀ y1 y2, 0 < y1 → y1 ≤ y2 → G y1 ≤ G y2 := fun y1 y2 hy1 h12 =>
    c8_gStar_mono S hS α γr hα0 hγr ρ T t hρ hT ht κ κc κ₀ hκ hκc c hc h24 y1 y2 hy1 h12
  have hYc : ∀ lam : ℝ, 0 < lam →
      0 < Y lam ∧ Y lam = Real.exp (-((α * γg) / lam) * G (Y lam)) := fun lam hl => hY lam hl
  have hK : 0 < α * γg := by positivity
  obtain ⟨c1, c2, c3⟩ := c8_core G Y (α * γg) hK hGm hYc
  have hYpos : ∀ lam : ℝ, 0 < lam → 0 < Y lam := fun lam hl => (hY lam hl).1
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have hG1 : 0 < G 1 := by
      by_contra hn; push Not at hn; nlinarith
    obtain ⟨hm, hl⟩ := c1 hG1
    refine ⟨hYpos, hm, hl, fun i => ?_⟩
    intro l1 hl1 l2 hl2 h12
    exact c8_sched_anti ρ T t α κ κc c hc hα0 hρ hT ht hκ hκc _ _ (hYpos l1 hl1)
      (hm.monotoneOn hl1 hl2 h12) i
  · have hG1 : G 1 < 0 := by
      by_contra hn; push Not at hn; nlinarith
    obtain ⟨hm, hl⟩ := c2 hG1
    refine ⟨hYpos, hm, hl, fun i => ?_⟩
    intro l1 hl1 l2 hl2 h12
    exact c8_sched_anti ρ T t α κ κc c hc hα0 hρ hT ht hκ hκc _ _ (hYpos l2 hl2)
      (hm.antitoneOn hl1 hl2 h12) i
  · have hG1 : G 1 = 0 := by
      rcases mul_eq_zero.mp h with h' | h'
      · linarith
      · exact h'
    intro lam hl
    have := c3 hG1 lam hl
    exact ⟨this, by rw [this]⟩

end ClimateImpact.Uncertainty


-- Platform entry point: restates the target verbatim.
namespace ClimateImpact.Uncertainty

/-- Proposition 8(iii) (pp. 38–39): under condition (24), the sign of `θ_t(ψ^{*,0}_t)ᵀ N^g_t`
decides whether `λ ↦ y^*_λ` increases or decreases to `1`, and with it whether more climate
uncertainty (smaller `λ`) raises or lowers the equilibrium emission schedule (22). -/
theorem _root_.solution {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (α γr γg : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hγr : 0 < γr) (hγg : 0 < γg)
    (ρ T t : ℝ) (hρ : 0 < ρ) (hT : 0 < T) (ht : t ∈ Set.Icc 0 T)
    (κ κc κ₀ : ℝ) (hκ : 0 < κ) (hκc : 0 < κc) (hκ₀ : 0 < κ₀)
    (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (h24 : Cond24 S γr ρ T t α κ κc κ₀ c)
    (Y : ℝ → ℝ) (hY : ∀ lam : ℝ, 0 < lam → IsYStar S γr γg lam ρ T t α κ κc κ₀ c (Y lam)) :
    (0 < ext0 ρ T t α κ κc κ₀ c ⬝ᵥ greenPortfolio S α γr (ext0 ρ T t α κ κc κ₀ c) 1 →
      (∀ lam : ℝ, 0 < lam → 0 < Y lam) ∧ StrictMonoOn Y (Set.Ioi 0) ∧
        Filter.Tendsto Y Filter.atTop (nhds 1) ∧
        ∀ i, AntitoneOn (fun lam => schedule ρ T t α κ κc c (Y lam) i) (Set.Ioi 0)) ∧
    (ext0 ρ T t α κ κc κ₀ c ⬝ᵥ greenPortfolio S α γr (ext0 ρ T t α κ κc κ₀ c) 1 < 0 →
      (∀ lam : ℝ, 0 < lam → 0 < Y lam) ∧ StrictAntiOn Y (Set.Ioi 0) ∧
        Filter.Tendsto Y Filter.atTop (nhds 1) ∧
        ∀ i, MonotoneOn (fun lam => schedule ρ T t α κ κc c (Y lam) i) (Set.Ioi 0)) ∧
    (ext0 ρ T t α κ κc κ₀ c ⬝ᵥ greenPortfolio S α γr (ext0 ρ T t α κ κc κ₀ c) 1 = 0 →
      ∀ lam : ℝ, 0 < lam → Y lam = 1 ∧ schedule ρ T t α κ κc c (Y lam) = schedule ρ T t α κ κc c 1) := by
  exact ClimateImpact.Uncertainty.prop8_iii_uncertainty_raises_emissions S hS α γr γg hα0 hα1 hγr hγg ρ T t hρ hT ht κ κc κ₀ hκ hκc hκ₀ c hc h24 Y hY

end ClimateImpact.Uncertainty
