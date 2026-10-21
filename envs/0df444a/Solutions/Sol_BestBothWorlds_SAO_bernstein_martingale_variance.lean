-- Prove2me | solution 1 for BestBothWorlds.SAO.bernstein_martingale_variance
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-20T08:26:23.083415+00:00
-- url     : https://prove2.me/submissions/a19ed3f2-3dc5-4541-b16e-9d4689beb681

import Mathlib

set_option autoImplicit false

open MeasureTheory

namespace Pc986c950

noncomputable def Vf {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) (ℱ : Filtration ℕ mΩ)
    (X : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  P[fun ω' => X t ω' ^ 2 | ℱ (t - 1)]

noncomputable def Zf {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) (ℱ : Filtration ℕ mΩ)
    (X : ℕ → Ω → ℝ) (Λ : Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  Real.exp (Λ ω * ∑ t ∈ Finset.Icc 1 k, X t ω - Λ ω ^ 2 * ∑ t ∈ Finset.Icc 1 k, Vf P ℱ X t ω)

lemma exp_le_quad {y : ℝ} (hy : |y| ≤ 1) : Real.exp y ≤ 1 + y + y ^ 2 := by
  have h := Real.abs_exp_sub_one_sub_id_le hy
  have := (abs_le.1 h).2
  linarith

lemma int_of_bd {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {f : Ω → ℝ} (hf : Measurable f) (C : ℝ) (h : ∀ᵐ ω ∂P, |f ω| ≤ C) : Integrable f P :=
  Integrable.of_bound hf.aestronglyMeasurable C (by
    filter_upwards [h] with ω hω
    rw [Real.norm_eq_abs]; exact hω)

lemma int_mul_condExp {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {g f : Ω → ℝ} (hg : StronglyMeasurable[m] g) (c : ℝ)
    (hgb : ∀ᵐ ω ∂P, ‖g ω‖ ≤ c) (hf : Integrable f P) :
    ∫ ω, g ω * f ω ∂P = ∫ ω, g ω * (P[f|m]) ω ∂P := by
  have h1 := condExp_stronglyMeasurable_mul_of_bound hm hg hf c hgb
  calc ∫ ω, g ω * f ω ∂P = ∫ ω, (P[g * f|m]) ω ∂P := (integral_condExp hm).symm
    _ = ∫ ω, g ω * (P[f|m]) ω ∂P := integral_congr_ae h1

lemma arith {b L W S θ s : ℝ} (hb : 0 < b) (hL : 0 < L) (hW : 0 ≤ W) (hθ : 0 < θ)
    (hs : s = Real.sqrt (4 * W / (b ^ 2 * L) + 5)) (hcov : (θ * s - 2) ^ 2 ≤ 5 * θ ^ 2)
    (h : θ / b * S - (θ / b) ^ 2 * W < L) :
    S ≤ Real.sqrt (4 * W * L + 5 * b ^ 2 * L ^ 2) := by
  have hs0 : 0 ≤ 4 * W / (b ^ 2 * L) + 5 := by positivity
  have hs2 : s ^ 2 = 4 * W / (b ^ 2 * L) + 5 := by rw [hs, Real.sq_sqrt hs0]
  have hspos : 0 ≤ s := by rw [hs]; exact Real.sqrt_nonneg _
  have hW' : W = b ^ 2 * L * (s ^ 2 - 5) / 4 := by rw [hs2]; field_simp; ring
  have hR : Real.sqrt (4 * W * L + 5 * b ^ 2 * L ^ 2) = b * L * s := by
    rw [show 4 * W * L + 5 * b ^ 2 * L ^ 2 = (b * L * s) ^ 2 by rw [hW']; ring]
    exact Real.sqrt_sq (by positivity)
  rw [hR]
  have hθb : 0 < θ / b := div_pos hθ hb
  have key : L + (θ / b) ^ 2 * W ≤ θ / b * (b * L * s) := by
    have e1 : θ / b * (b * L * s) - (L + (θ / b) ^ 2 * W)
        = L * (5 * θ ^ 2 - (θ * s - 2) ^ 2) / 4 := by
      rw [hW']; field_simp; ring
    have : 0 ≤ L * (5 * θ ^ 2 - (θ * s - 2) ^ 2) / 4 :=
      div_nonneg (mul_nonneg hL.le (by linarith)) (by norm_num)
    linarith
  have : θ / b * S < θ / b * (b * L * s) := by linarith
  exact (lt_of_mul_lt_mul_left this hθb.le).le

section
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ) (n : ℕ) (b : ℝ)

lemma measS (hmeas : ∀ t ∈ Finset.Icc 1 n, Measurable[ℱ t] (X t)) (k : ℕ) (hk : k ≤ n) :
    Measurable[ℱ k] (fun ω => ∑ t ∈ Finset.Icc 1 k, X t ω) := by
  apply Finset.measurable_sum
  intro t ht
  have ht' := Finset.mem_Icc.1 ht
  exact (hmeas t (Finset.mem_Icc.2 ⟨ht'.1, ht'.2.trans hk⟩)).mono (ℱ.mono ht'.2) le_rfl

lemma measV (t : ℕ) : Measurable[ℱ (t - 1)] (Vf P ℱ X t) :=
  stronglyMeasurable_condExp.measurable

lemma measW (k : ℕ) :
    Measurable[ℱ (k - 1)] (fun ω => ∑ t ∈ Finset.Icc 1 k, Vf P ℱ X t ω) := by
  apply Finset.measurable_sum
  intro t ht
  have ht' := Finset.mem_Icc.1 ht
  exact (measV P ℱ X t).mono (ℱ.mono (by omega)) le_rfl

lemma aeX (hbd : ∀ t ∈ Finset.Icc 1 n, ∀ᵐ ω ∂P, |X t ω| ≤ b) :
    ∀ᵐ ω ∂P, ∀ t ∈ Finset.Icc 1 n, |X t ω| ≤ b :=
  (Filter.eventually_all_finset _).2 hbd

lemma aeV (hbd : ∀ t ∈ Finset.Icc 1 n, ∀ᵐ ω ∂P, |X t ω| ≤ b) :
    ∀ᵐ ω ∂P, ∀ t ∈ Finset.Icc 1 n, 0 ≤ Vf P ℱ X t ω ∧ Vf P ℱ X t ω ≤ b ^ 2 := by
  refine (Filter.eventually_all_finset _).2 (fun t ht => ?_)
  have h0 : 0 ≤ᵐ[P] Vf P ℱ X t := by
    unfold Vf
    exact condExp_nonneg (Filter.Eventually.of_forall (fun ω => by
      simp only [Pi.zero_apply]; exact sq_nonneg _))
  have h1 : ∀ᵐ ω ∂P, |Vf P ℱ X t ω| ≤ b ^ 2 := by
    unfold Vf
    exact ae_bdd_abs_condExp_of_ae_bdd_abs (f := fun ω' => X t ω' ^ 2) (R := b ^ 2) (by
      filter_upwards [hbd t ht] with ω h
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) h 2)
  filter_upwards [h0, h1] with ω h0 h1
  exact ⟨h0, (abs_le.1 h1).2⟩

lemma aeW (hbd : ∀ t ∈ Finset.Icc 1 n, ∀ᵐ ω ∂P, |X t ω| ≤ b) :
    ∀ᵐ ω ∂P, 0 ≤ ∑ t ∈ Finset.Icc 1 n, Vf P ℱ X t ω ∧
      ∑ t ∈ Finset.Icc 1 n, Vf P ℱ X t ω ≤ n * b ^ 2 := by
  filter_upwards [aeV P ℱ X n b hbd] with ω hV
  refine ⟨Finset.sum_nonneg (fun t ht => (hV t ht).1), ?_⟩
  have := Finset.sum_le_card_nsmul (Finset.Icc 1 n) (fun t => Vf P ℱ X t ω) (b ^ 2)
    (fun t ht => (hV t ht).2)
  simpa using this

lemma Zbd (hbd : ∀ t ∈ Finset.Icc 1 n, ∀ᵐ ω ∂P, |X t ω| ≤ b)
    (Λ : Ω → ℝ) (hΛ0 : ∀ ω, 0 ≤ Λ ω) (hΛb : ∀ ω, Λ ω * b ≤ 1) (k : ℕ) (hk : k ≤ n) :
    ∀ᵐ ω ∂P, Zf P ℱ X Λ k ω ≤ Real.exp k := by
  filter_upwards [aeX P X n b hbd, aeV P ℱ X n b hbd] with ω hX hV
  unfold Zf
  apply Real.exp_le_exp.2
  have h1 : Λ ω * ∑ t ∈ Finset.Icc 1 k, X t ω ≤ k := by
    rw [Finset.mul_sum]
    calc ∑ t ∈ Finset.Icc 1 k, Λ ω * X t ω ≤ ∑ t ∈ Finset.Icc 1 k, (1:ℝ) := by
          apply Finset.sum_le_sum; intro t ht
          have ht' := Finset.mem_Icc.1 ht
          have hx := hX t (Finset.mem_Icc.2 ⟨ht'.1, ht'.2.trans hk⟩)
          calc Λ ω * X t ω ≤ Λ ω * |X t ω| := mul_le_mul_of_nonneg_left (le_abs_self _) (hΛ0 ω)
            _ ≤ Λ ω * b := mul_le_mul_of_nonneg_left hx (hΛ0 ω)
            _ ≤ 1 := hΛb ω
      _ = k := by simp
  have h2 : 0 ≤ Λ ω ^ 2 * ∑ t ∈ Finset.Icc 1 k, Vf P ℱ X t ω := by
    apply mul_nonneg (sq_nonneg _)
    apply Finset.sum_nonneg; intro t ht
    have ht' := Finset.mem_Icc.1 ht
    exact (hV t (Finset.mem_Icc.2 ⟨ht'.1, ht'.2.trans hk⟩)).1
  linarith

lemma Zmeas (hmeas : ∀ t ∈ Finset.Icc 1 n, Measurable[ℱ t] (X t))
    (Λ : Ω → ℝ) (hΛm : Measurable[ℱ 0] Λ) (k : ℕ) (hk : k ≤ n) :
    Measurable[ℱ k] (Zf P ℱ X Λ k) := by
  have hΛk : Measurable[ℱ k] Λ := hΛm.mono (ℱ.mono (Nat.zero_le k)) le_rfl
  have hW : Measurable[ℱ k] (fun ω => ∑ t ∈ Finset.Icc 1 k, Vf P ℱ X t ω) :=
    (measW P ℱ X k).mono (ℱ.mono (Nat.sub_le k 1)) le_rfl
  unfold Zf
  exact ((hΛk.mul (measS ℱ X n hmeas k hk)).sub ((hΛk.pow_const 2).mul hW)).exp

lemma Zint (hmeas : ∀ t ∈ Finset.Icc 1 n, Measurable[ℱ t] (X t))
    (hbd : ∀ t ∈ Finset.Icc 1 n, ∀ᵐ ω ∂P, |X t ω| ≤ b)
    (Λ : Ω → ℝ) (hΛm : Measurable[ℱ 0] Λ) (hΛ0 : ∀ ω, 0 ≤ Λ ω) (hΛb : ∀ ω, Λ ω * b ≤ 1)
    (k : ℕ) (hk : k ≤ n) : Integrable (Zf P ℱ X Λ k) P :=
  int_of_bd ((Zmeas P ℱ X n hmeas Λ hΛm k hk).mono (ℱ.le k) le_rfl) (Real.exp k) (by
    filter_upwards [Zbd P ℱ X n b hbd Λ hΛ0 hΛb k hk] with ω h
    rw [abs_of_pos (by unfold Zf; exact Real.exp_pos _)]; exact h)

lemma step (hb : 0 < b) (hmeas : ∀ t ∈ Finset.Icc 1 n, Measurable[ℱ t] (X t))
    (hmds : ∀ t ∈ Finset.Icc 1 n, P[X t | ℱ (t - 1)] =ᵐ[P] 0)
    (hbd : ∀ t ∈ Finset.Icc 1 n, ∀ᵐ ω ∂P, |X t ω| ≤ b)
    (Λ : Ω → ℝ) (hΛm : Measurable[ℱ 0] Λ) (hΛ0 : ∀ ω, 0 ≤ Λ ω) (hΛb : ∀ ω, Λ ω * b ≤ 1)
    (k : ℕ) (hk : k + 1 ≤ n) :
    ∫ ω, Zf P ℱ X Λ (k + 1) ω ∂P ≤ ∫ ω, Zf P ℱ X Λ k ω ∂P := by
  have hkn : k ≤ n := by omega
  have ht : k + 1 ∈ Finset.Icc 1 n := Finset.mem_Icc.2 ⟨by omega, hk⟩
  have e : k + 1 - 1 = k := Nat.add_sub_cancel k 1
  have hC0 : 0 < Real.exp k := Real.exp_pos _
  have hΛk : Measurable[ℱ k] Λ := hΛm.mono (ℱ.mono (Nat.zero_le k)) le_rfl
  have hZk : Measurable[ℱ k] (Zf P ℱ X Λ k) := Zmeas P ℱ X n hmeas Λ hΛm k hkn
  have hVk : Measurable[ℱ k] (Vf P ℱ X (k + 1)) := by
    have := measV P ℱ X (k + 1); rw [e] at this; exact this
  set G : Ω → ℝ := fun ω => Zf P ℱ X Λ k ω * Real.exp (-(Λ ω ^ 2 * Vf P ℱ X (k + 1) ω))
    with hG
  have hGm : Measurable[ℱ k] G := hZk.mul (((hΛk.pow_const 2).mul hVk).neg.exp)
  have hG1m : Measurable[ℱ k] (fun ω => G ω * Λ ω) := hGm.mul hΛk
  have hG2m : Measurable[ℱ k] (fun ω => G ω * Λ ω ^ 2) := hGm.mul (hΛk.pow_const 2)
  have hXm : Measurable (X (k + 1)) := (hmeas _ ht).mono (ℱ.le _) le_rfl
  have hle : ∀ ω, Λ ω ≤ 1 / b := fun ω => (le_div_iff₀ hb).2 (by linarith [hΛb ω])
  have hZb := Zbd P ℱ X n b hbd Λ hΛ0 hΛb k hkn
  have hgood : ∀ᵐ ω ∂P, 0 ≤ G ω ∧ G ω ≤ Real.exp k ∧ |X (k + 1) ω| ≤ b ∧
      0 ≤ Vf P ℱ X (k + 1) ω ∧ Vf P ℱ X (k + 1) ω ≤ b ^ 2 := by
    filter_upwards [hZb, aeX P X n b hbd, aeV P ℱ X n b hbd] with ω hz hX hV
    have hz0 : 0 ≤ Zf P ℱ X Λ k ω := by unfold Zf; exact (Real.exp_pos _).le
    have hv := hV _ ht
    have hE : Real.exp (-(Λ ω ^ 2 * Vf P ℱ X (k + 1) ω)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; have := mul_nonneg (sq_nonneg (Λ ω)) hv.1; linarith
    refine ⟨mul_nonneg hz0 (Real.exp_pos _).le, ?_, hX _ ht, hv.1, hv.2⟩
    calc G ω ≤ Zf P ℱ X Λ k ω * 1 := mul_le_mul_of_nonneg_left hE hz0
      _ ≤ Real.exp k := by rw [mul_one]; exact hz
  have hΛX : ∀ᵐ ω ∂P, |Λ ω * X (k + 1) ω| ≤ 1 := by
    filter_upwards [hgood] with ω h
    rw [abs_mul, abs_of_nonneg (hΛ0 ω)]
    calc Λ ω * |X (k + 1) ω| ≤ Λ ω * b := mul_le_mul_of_nonneg_left h.2.2.1 (hΛ0 ω)
      _ ≤ 1 := hΛb ω
  have iG : Integrable G P := int_of_bd (hGm.mono (ℱ.le k) le_rfl) (Real.exp k) (by
    filter_upwards [hgood] with ω h; rw [abs_of_nonneg h.1]; exact h.2.1)
  have bG1 : ∀ᵐ ω ∂P, ‖G ω * Λ ω‖ ≤ Real.exp k * (1 / b) := by
    filter_upwards [hgood] with ω h
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h.1 (hΛ0 ω))]
    exact mul_le_mul h.2.1 (hle ω) (hΛ0 ω) hC0.le
  have bG2 : ∀ᵐ ω ∂P, ‖G ω * Λ ω ^ 2‖ ≤ Real.exp k * (1 / b) ^ 2 := by
    filter_upwards [hgood] with ω h
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h.1 (sq_nonneg _))]
    exact mul_le_mul h.2.1 (pow_le_pow_left₀ (hΛ0 ω) (hle ω) 2) (sq_nonneg _) hC0.le
  have iX : Integrable (X (k + 1)) P := int_of_bd hXm b (by
    filter_upwards [hgood] with ω h; exact h.2.2.1)
  have iX2 : Integrable (fun ω => X (k + 1) ω ^ 2) P := int_of_bd (hXm.pow_const 2) (b ^ 2) (by
    filter_upwards [hgood] with ω h
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) h.2.2.1 2)
  have i1 : Integrable (fun ω => G ω * Λ ω * X (k + 1) ω) P :=
    int_of_bd ((hG1m.mono (ℱ.le k) le_rfl).mul hXm) (Real.exp k) (by
      filter_upwards [hgood, hΛX] with ω h h'
      rw [mul_assoc, abs_mul, abs_of_nonneg h.1]
      calc G ω * |Λ ω * X (k + 1) ω| ≤ Real.exp k * 1 := mul_le_mul h.2.1 h' (abs_nonneg _) hC0.le
        _ = Real.exp k := mul_one _)
  have i2 : Integrable (fun ω => G ω * Λ ω ^ 2 * X (k + 1) ω ^ 2) P :=
    int_of_bd ((hG2m.mono (ℱ.le k) le_rfl).mul (hXm.pow_const 2)) (Real.exp k) (by
      filter_upwards [hgood, hΛX] with ω h h'
      rw [show G ω * Λ ω ^ 2 * X (k + 1) ω ^ 2 = G ω * (Λ ω * X (k + 1) ω) ^ 2 by ring,
        abs_mul, abs_of_nonneg h.1, abs_pow]
      have : |Λ ω * X (k + 1) ω| ^ 2 ≤ 1 := by
        have h0 := abs_nonneg (Λ ω * X (k + 1) ω); nlinarith
      calc G ω * |Λ ω * X (k + 1) ω| ^ 2 ≤ Real.exp k * 1 :=
            mul_le_mul h.2.1 this (sq_nonneg _) hC0.le
        _ = Real.exp k := mul_one _)
  have iV : Integrable (fun ω => G ω * Λ ω ^ 2 * Vf P ℱ X (k + 1) ω) P :=
    int_of_bd ((hG2m.mul hVk).mono (ℱ.le k) le_rfl) (Real.exp k) (by
      filter_upwards [hgood] with ω h
      have h3 : Λ ω ^ 2 * Vf P ℱ X (k + 1) ω ≤ 1 := by
        calc Λ ω ^ 2 * Vf P ℱ X (k + 1) ω ≤ Λ ω ^ 2 * b ^ 2 :=
              mul_le_mul_of_nonneg_left h.2.2.2.2 (sq_nonneg _)
          _ = (Λ ω * b) ^ 2 := by ring
          _ ≤ 1 := by
            have := hΛb ω; have := mul_nonneg (hΛ0 ω) hb.le; nlinarith
      rw [mul_assoc, abs_mul, abs_of_nonneg h.1,
        abs_of_nonneg (mul_nonneg (sq_nonneg _) h.2.2.2.1)]
      calc G ω * (Λ ω ^ 2 * Vf P ℱ X (k + 1) ω) ≤ Real.exp k * 1 :=
            mul_le_mul h.2.1 h3 (mul_nonneg (sq_nonneg _) h.2.2.2.1) hC0.le
        _ = Real.exp k := mul_one _)
  have hZ1 : ∀ ω, Zf P ℱ X Λ (k + 1) ω = G ω * Real.exp (Λ ω * X (k + 1) ω) := by
    intro ω
    simp only [hG, Zf]
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1),
      Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1), ← Real.exp_add, ← Real.exp_add]
    congr 1; ring
  have hstep1 : ∫ ω, Zf P ℱ X Λ (k + 1) ω ∂P ≤ ∫ ω, (G ω + G ω * Λ ω * X (k + 1) ω +
      G ω * Λ ω ^ 2 * X (k + 1) ω ^ 2) ∂P := by
    apply integral_mono_ae
    · exact Zint P ℱ X n b hmeas hbd Λ hΛm hΛ0 hΛb (k + 1) hk
    · exact (iG.add i1).add i2
    · filter_upwards [hgood, hΛX] with ω h h'
      rw [hZ1]
      calc G ω * Real.exp (Λ ω * X (k + 1) ω)
          ≤ G ω * (1 + Λ ω * X (k + 1) ω + (Λ ω * X (k + 1) ω) ^ 2) :=
            mul_le_mul_of_nonneg_left (exp_le_quad h') h.1
        _ = G ω + G ω * Λ ω * X (k + 1) ω + G ω * Λ ω ^ 2 * X (k + 1) ω ^ 2 := by ring
  have i01 : Integrable (fun ω => G ω + G ω * Λ ω * X (k + 1) ω) P := iG.add i1
  have hsplit : ∫ ω, (G ω + G ω * Λ ω * X (k + 1) ω + G ω * Λ ω ^ 2 * X (k + 1) ω ^ 2) ∂P
      = ∫ ω, G ω ∂P + ∫ ω, G ω * Λ ω * X (k + 1) ω ∂P +
        ∫ ω, G ω * Λ ω ^ 2 * X (k + 1) ω ^ 2 ∂P := by
    rw [integral_add i01 i2, integral_add iG i1]
  have hmid : ∫ ω, G ω * Λ ω * X (k + 1) ω ∂P = 0 := by
    have h1 := int_mul_condExp (P := P) (ℱ.le k) hG1m.stronglyMeasurable
      (Real.exp k * (1 / b)) bG1 iX
    have h2 : P[X (k + 1) | ℱ k] =ᵐ[P] 0 := by
      have := hmds _ ht; rw [e] at this; exact this
    rw [h1]
    calc ∫ ω, G ω * Λ ω * (P[X (k + 1) | ℱ k]) ω ∂P = ∫ ω, (0:ℝ) ∂P :=
          integral_congr_ae (by filter_upwards [h2] with ω hω; simp [hω])
      _ = 0 := integral_zero _ _
  have hthird : ∫ ω, G ω * Λ ω ^ 2 * X (k + 1) ω ^ 2 ∂P
      = ∫ ω, G ω * Λ ω ^ 2 * Vf P ℱ X (k + 1) ω ∂P := by
    have h1 := int_mul_condExp (P := P) (ℱ.le k) hG2m.stronglyMeasurable
      (Real.exp k * (1 / b) ^ 2) bG2 iX2
    rw [h1]; unfold Vf; rw [e]
  have hlast : ∫ ω, G ω ∂P + ∫ ω, G ω * Λ ω ^ 2 * Vf P ℱ X (k + 1) ω ∂P
      ≤ ∫ ω, Zf P ℱ X Λ k ω ∂P := by
    rw [← integral_add iG iV]
    apply integral_mono_ae (iG.add iV) (Zint P ℱ X n b hmeas hbd Λ hΛm hΛ0 hΛb k hkn)
    filter_upwards [hgood] with ω h
    have hZ : Zf P ℱ X Λ k ω = G ω * Real.exp (Λ ω ^ 2 * Vf P ℱ X (k + 1) ω) := by
      simp only [hG]; rw [mul_assoc, ← Real.exp_add]; simp
    rw [hZ]
    have := Real.add_one_le_exp (Λ ω ^ 2 * Vf P ℱ X (k + 1) ω)
    calc G ω + G ω * Λ ω ^ 2 * Vf P ℱ X (k + 1) ω
        = G ω * (Λ ω ^ 2 * Vf P ℱ X (k + 1) ω + 1) := by ring
      _ ≤ G ω * Real.exp (Λ ω ^ 2 * Vf P ℱ X (k + 1) ω) := mul_le_mul_of_nonneg_left this h.1
  linarith [hstep1, hsplit, hmid, hthird, hlast]

lemma key (hb : 0 < b) (hmeas : ∀ t ∈ Finset.Icc 1 n, Measurable[ℱ t] (X t))
    (hmds : ∀ t ∈ Finset.Icc 1 n, P[X t | ℱ (t - 1)] =ᵐ[P] 0)
    (hbd : ∀ t ∈ Finset.Icc 1 n, ∀ᵐ ω ∂P, |X t ω| ≤ b)
    (Λ : Ω → ℝ) (hΛm : Measurable[ℱ 0] Λ) (hΛ0 : ∀ ω, 0 ≤ Λ ω) (hΛb : ∀ ω, Λ ω * b ≤ 1) :
    ∀ k ≤ n, ∫ ω, Zf P ℱ X Λ k ω ∂P ≤ 1 := by
  intro k
  induction k with
  | zero =>
    intro _
    have : ∀ ω, Zf P ℱ X Λ 0 ω = 1 := by intro ω; simp [Zf]
    simp [this]
  | succ k ih =>
    intro hk
    exact (step P ℱ X n b hb hmeas hmds hbd Λ hΛm hΛ0 hΛb k hk).trans (ih (by omega))

lemma markov (hb : 0 < b) (hmeas : ∀ t ∈ Finset.Icc 1 n, Measurable[ℱ t] (X t))
    (hmds : ∀ t ∈ Finset.Icc 1 n, P[X t | ℱ (t - 1)] =ᵐ[P] 0)
    (hbd : ∀ t ∈ Finset.Icc 1 n, ∀ᵐ ω ∂P, |X t ω| ≤ b)
    (Λ : Ω → ℝ) (hΛm : Measurable[ℱ 0] Λ) (hΛ0 : ∀ ω, 0 ≤ Λ ω) (hΛb : ∀ ω, Λ ω * b ≤ 1)
    (L : ℝ) :
    P.real {ω | L ≤ Λ ω * ∑ t ∈ Finset.Icc 1 n, X t ω -
      Λ ω ^ 2 * ∑ t ∈ Finset.Icc 1 n, Vf P ℱ X t ω} ≤ Real.exp (-L) := by
  have hint := Zint P ℱ X n b hmeas hbd Λ hΛm hΛ0 hΛb n le_rfl
  have hI := key P ℱ X n b hb hmeas hmds hbd Λ hΛm hΛ0 hΛb n le_rfl
  have h := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall (fun ω => by
    simp only [Pi.zero_apply]; unfold Zf; exact (Real.exp_pos _).le)) hint (Real.exp L)
  have hset : {x | Real.exp L ≤ Zf P ℱ X Λ n x} = {ω | L ≤ Λ ω * ∑ t ∈ Finset.Icc 1 n, X t ω -
      Λ ω ^ 2 * ∑ t ∈ Finset.Icc 1 n, Vf P ℱ X t ω} := by
    ext ω; simp only [Set.mem_setOf_eq, Zf, Real.exp_le_exp]
  rw [hset] at h
  calc P.real {ω | L ≤ Λ ω * ∑ t ∈ Finset.Icc 1 n, X t ω -
      Λ ω ^ 2 * ∑ t ∈ Finset.Icc 1 n, Vf P ℱ X t ω}
      = Real.exp (-L) * (Real.exp L * P.real {ω | L ≤ Λ ω * ∑ t ∈ Finset.Icc 1 n, X t ω -
      Λ ω ^ 2 * ∑ t ∈ Finset.Icc 1 n, Vf P ℱ X t ω}) := by
        rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
    _ ≤ Real.exp (-L) * 1 := mul_le_mul_of_nonneg_left (h.trans hI) (Real.exp_pos _).le
    _ = Real.exp (-L) := mul_one _

lemma final (hb : 0 < b) (hmeas : ∀ t ∈ Finset.Icc 1 n, Measurable[ℱ t] (X t))
    (hmds : ∀ t ∈ Finset.Icc 1 n, P[X t | ℱ (t - 1)] =ᵐ[P] 0)
    (hbd : ∀ t ∈ Finset.Icc 1 n, ∀ᵐ ω ∂P, |X t ω| ≤ b)
    (Λf : ℕ → Ω → ℝ) (hΛm : ∀ k, Measurable[ℱ 0] (Λf k)) (hΛ0 : ∀ k ω, 0 ≤ Λf k ω)
    (hΛb : ∀ k ω, Λf k ω * b ≤ 1) (L : ℝ) (T : Ω → ℝ)
    (hcov : ∀ᵐ ω ∂P, (∀ k ∈ Finset.range n, Λf k ω * ∑ t ∈ Finset.Icc 1 n, X t ω -
      Λf k ω ^ 2 * ∑ t ∈ Finset.Icc 1 n, Vf P ℱ X t ω < L) →
      ∑ t ∈ Finset.Icc 1 n, X t ω ≤ T ω) :
    1 - n * Real.exp (-L) ≤ P.real {ω | ∑ t ∈ Finset.Icc 1 n, X t ω ≤ T ω} := by
  set A := {ω | ∑ t ∈ Finset.Icc 1 n, X t ω ≤ T ω} with hA
  set B : ℕ → Set Ω := fun k => {ω | L ≤ Λf k ω * ∑ t ∈ Finset.Icc 1 n, X t ω -
      Λf k ω ^ 2 * ∑ t ∈ Finset.Icc 1 n, Vf P ℱ X t ω} with hB
  set N := {ω | ¬ ((∀ k ∈ Finset.range n, Λf k ω * ∑ t ∈ Finset.Icc 1 n, X t ω -
      Λf k ω ^ 2 * ∑ t ∈ Finset.Icc 1 n, Vf P ℱ X t ω < L) →
      ∑ t ∈ Finset.Icc 1 n, X t ω ≤ T ω)} with hN
  have hN0 : P.real N = 0 := by
    rw [measureReal_eq_zero_iff]; exact ae_iff.1 hcov
  have hsub : Aᶜ ⊆ N ∪ ⋃ k ∈ Finset.range n, B k := by
    intro ω hω
    by_cases h : ω ∈ N
    · exact Or.inl h
    · right
      rw [Set.mem_iUnion₂]
      by_contra hc
      push_neg at hc
      exact hω (not_not.1 h (fun k hk => not_le.1 (hc k hk)))
  have hBk : ∀ k ∈ Finset.range n, P.real (B k) ≤ Real.exp (-L) := fun k _ =>
    markov P ℱ X n b hb hmeas hmds hbd (Λf k) (hΛm k) (hΛ0 k) (hΛb k) L
  have h1 : P.real Aᶜ ≤ n * Real.exp (-L) := by
    calc P.real Aᶜ ≤ P.real (N ∪ ⋃ k ∈ Finset.range n, B k) := measureReal_mono hsub
      _ ≤ P.real N + P.real (⋃ k ∈ Finset.range n, B k) := measureReal_union_le _ _
      _ ≤ ∑ k ∈ Finset.range n, P.real (B k) := by
        rw [hN0, zero_add]; exact measureReal_biUnion_finset_le _ _
      _ ≤ ∑ k ∈ Finset.range n, Real.exp (-L) := Finset.sum_le_sum hBk
      _ = n * Real.exp (-L) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h2 := measureReal_union_le (μ := P) A Aᶜ
  rw [Set.union_compl_self, probReal_univ] at h2
  linarith

end

lemma grid_cover {n : ℕ} (hn : 1 ≤ n) {b L W : ℝ} (hb : 0 < b) (hL : 1 / 2 ≤ L) (hW : 0 ≤ W)
    (hWn : W ≤ n * b ^ 2) :
    ∃ k ∈ Finset.range n, (1 / (Real.sqrt 5 * ((k:ℝ) + 1)) *
      Real.sqrt (4 * W / (b ^ 2 * L) + 5) - 2) ^ 2 ≤
      5 * (1 / (Real.sqrt 5 * ((k:ℝ) + 1))) ^ 2 := by
  have hL0 : 0 < L := by linarith
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h5pos : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  set s := Real.sqrt (4 * W / (b ^ 2 * L) + 5) with hs
  have hs0 : 0 ≤ 4 * W / (b ^ 2 * L) := by positivity
  have hs2 : s ^ 2 = 4 * W / (b ^ 2 * L) + 5 := Real.sq_sqrt (by linarith)
  have hsge : Real.sqrt 5 ≤ s := Real.sqrt_le_sqrt (by linarith)
  have hn0 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hWL : W / (b ^ 2 * L) ≤ 2 * n := by
    rw [div_le_iff₀ (by positivity)]
    have := mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ n) (sq_nonneg b))
      (by linarith : (0:ℝ) ≤ 2 * L - 1)
    nlinarith
  have hs2' : s ^ 2 ≤ 8 * n + 5 := by
    rw [hs2]
    have : 4 * W / (b ^ 2 * L) = 4 * (W / (b ^ 2 * L)) := by ring
    linarith
  set r := s / Real.sqrt 5 with hr
  have hsr : s = Real.sqrt 5 * r := by rw [hr]; field_simp
  have hr1 : 1 ≤ r := by rw [hr, le_div_iff₀ h5pos]; linarith
  have hr2 : r ^ 2 ≤ (8 * n + 5) / 5 := by
    rw [le_div_iff₀ (by norm_num)]
    have : s ^ 2 = r ^ 2 * 5 := by rw [hsr, mul_pow, h5]; ring
    linarith
  have hrn : r < 2 * n + 1 := by
    by_contra hc
    push_neg at hc
    have : (2 * (n:ℝ) + 1) * (2 * n + 1) ≤ r * r :=
      mul_le_mul hc hc (by positivity) (by linarith)
    have : r ^ 2 * 5 ≤ 8 * n + 5 := by
      have := (le_div_iff₀ (by norm_num : (0:ℝ) < 5)).1 hr2; linarith
    nlinarith
  have hx0 : 0 ≤ (r - 1) / 2 := by linarith
  refine ⟨⌊(r - 1) / 2⌋₊, Finset.mem_range.2 ((Nat.floor_lt hx0).2 (by linarith)), ?_⟩
  set k := ⌊(r - 1) / 2⌋₊ with hk
  have hf1 := Nat.floor_le hx0
  have hf2 := Nat.lt_floor_add_one ((r - 1) / 2)
  rw [← hk] at hf1 hf2
  have hk0 : (0:ℝ) < (k:ℝ) + 1 := by positivity
  have e1 : 1 / (Real.sqrt 5 * ((k:ℝ) + 1)) * s - 2 = (r - 2 * ((k:ℝ) + 1)) / ((k:ℝ) + 1) := by
    rw [hsr]; field_simp
  have e2 : 5 * (1 / (Real.sqrt 5 * ((k:ℝ) + 1))) ^ 2 = 1 / ((k:ℝ) + 1) ^ 2 := by
    rw [div_pow, mul_pow, h5]; field_simp
  rw [e1, e2, div_pow]
  apply div_le_div_of_nonneg_right _ (by positivity)
  nlinarith

end Pc986c950

open MeasureTheory in
theorem solution {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ) (n : ℕ) (hn : 1 ≤ n)
    (b : ℝ) (hb : 0 < b)
    (hmeas : ∀ t ∈ Finset.Icc 1 n, Measurable[ℱ t] (X t))
    (hmds : ∀ t ∈ Finset.Icc 1 n, P[X t | ℱ (t - 1)] =ᵐ[P] 0)
    (hbd : ∀ t ∈ Finset.Icc 1 n, ∀ᵐ ω ∂P, |X t ω| ≤ b)
    (δ : ℝ) (hδ : 0 < δ) :
    1 - δ ≤ P.real {ω | ∑ t ∈ Finset.Icc 1 n, X t ω ≤
      Real.sqrt (4 * (∑ t ∈ Finset.Icc 1 n, P[fun ω' => X t ω' ^ 2 | ℱ (t - 1)] ω) *
          Real.log (n / δ) + 5 * b ^ 2 * Real.log (n / δ) ^ 2)} := by
  by_cases hδ1 : 1 ≤ δ
  · exact le_trans (by linarith) measureReal_nonneg
  push_neg at hδ1
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hnd : 1 < (n:ℝ) / δ := by rw [one_lt_div hδ]; linarith
  have hL0 : 0 < Real.log (n / δ) := Real.log_pos hnd
  have hexp : (n:ℝ) * Real.exp (-Real.log (n / δ)) = δ := by
    rw [Real.exp_neg, Real.exp_log (by linarith)]; field_simp
  have hW := Pc986c950.aeW P ℱ X n b hbd
  suffices H : ∃ Λf : ℕ → Ω → ℝ, (∀ k, Measurable[ℱ 0] (Λf k)) ∧ (∀ k ω, 0 ≤ Λf k ω) ∧
      (∀ k ω, Λf k ω * b ≤ 1) ∧ ∀ᵐ ω ∂P, (∀ k ∈ Finset.range n,
        Λf k ω * ∑ t ∈ Finset.Icc 1 n, X t ω -
        Λf k ω ^ 2 * ∑ t ∈ Finset.Icc 1 n, Pc986c950.Vf P ℱ X t ω < Real.log (n / δ)) →
      ∑ t ∈ Finset.Icc 1 n, X t ω ≤
        Real.sqrt (4 * (∑ t ∈ Finset.Icc 1 n, Pc986c950.Vf P ℱ X t ω) * Real.log (n / δ) +
          5 * b ^ 2 * Real.log (n / δ) ^ 2) by
    obtain ⟨Λf, h1, h2, h3, h4⟩ := H
    have := Pc986c950.final P ℱ X n b hb hmeas hmds hbd Λf h1 h2 h3 (Real.log (n / δ)) _ h4
    rw [hexp] at this
    exact this
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · -- n = 1: a random F_0-measurable lambda
    have hn1' : n = 1 := by omega
    subst hn1'
    set L := Real.log ((1:ℕ) / δ) with hL
    have hm0 : Measurable[ℱ 0] (fun ω => ∑ t ∈ Finset.Icc 1 1, Pc986c950.Vf P ℱ X t ω) := Pc986c950.measW P ℱ X 1
    set s1 : Ω → ℝ := fun ω =>
      Real.sqrt (4 * max (∑ t ∈ Finset.Icc 1 1, Pc986c950.Vf P ℱ X t ω) 0 / (b ^ 2 * L) + 5) with hs1
    have hs1m : Measurable[ℱ 0] s1 :=
      ((((hm0.max measurable_const).const_mul 4).div_const (b ^ 2 * L)).add_const 5).sqrt
    have hs1ge : ∀ ω, 2 ≤ s1 ω := by
      intro ω
      have h0 : 0 ≤ 4 * max (∑ t ∈ Finset.Icc 1 1, Pc986c950.Vf P ℱ X t ω) 0 / (b ^ 2 * L) :=
        div_nonneg (mul_nonneg (by norm_num) (le_max_right _ _)) (by positivity)
      calc (2:ℝ) = Real.sqrt (2 ^ 2) := by rw [Real.sqrt_sq (by norm_num)]
        _ ≤ s1 ω := Real.sqrt_le_sqrt (by linarith)
    refine ⟨fun _ ω => 2 / s1 ω / b, fun _ => (measurable_const.div hs1m).div_const b,
      fun _ ω => by have := hs1ge ω; positivity, fun _ ω => ?_, ?_⟩
    · have := hs1ge ω
      rw [div_mul_cancel₀ _ hb.ne', div_le_one (by linarith)]; linarith
    · filter_upwards [hW] with ω hw
      intro hall
      have hpos := hs1ge ω
      have hmax : max (∑ t ∈ Finset.Icc 1 1, Pc986c950.Vf P ℱ X t ω) 0 =
          ∑ t ∈ Finset.Icc 1 1, Pc986c950.Vf P ℱ X t ω := max_eq_left hw.1
      refine Pc986c950.arith hb hL0 hw.1 (θ := 2 / s1 ω) (s := s1 ω) (by positivity)
        (by simp only [hs1]; rw [hmax]) ?_ (hall 0 (by simp))
      rw [div_mul_cancel₀ _ (by linarith), sub_self]
      have := sq_nonneg (2 / s1 ω); nlinarith
  · -- n ≥ 2: a deterministic grid of n lambdas
    have hL2 : 1 / 2 ≤ Real.log (n / δ) := by
      have h2 : (2:ℝ) ≤ n / δ := by
        have : (2:ℝ) ≤ n := by exact_mod_cast hn2
        rw [le_div_iff₀ hδ]; linarith
      have := Real.log_le_log (by norm_num) h2
      have := Real.log_two_gt_d9
      linarith
    have h5pos : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
    have h51 : 1 ≤ Real.sqrt 5 := by
      rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
    refine ⟨fun k _ => 1 / (Real.sqrt 5 * ((k:ℝ) + 1)) / b, fun _ => measurable_const,
      fun _ _ => by positivity, fun k _ => ?_, ?_⟩
    · rw [div_mul_cancel₀ _ hb.ne', div_le_one (by positivity)]
      have : (1:ℝ) ≤ (k:ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) k; linarith
      nlinarith
    · filter_upwards [hW] with ω hw
      intro hall
      obtain ⟨k, hk, hcov⟩ := Pc986c950.grid_cover hn hb hL2 hw.1 hw.2
      exact Pc986c950.arith hb hL0 hw.1 (by positivity) rfl hcov (hall k hk)
