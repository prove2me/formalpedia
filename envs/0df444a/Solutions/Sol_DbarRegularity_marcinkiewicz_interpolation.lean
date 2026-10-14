-- Prove2me | solution 1 for DbarRegularity.marcinkiewicz_interpolation
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T00:04:40.203738+00:00
-- url     : https://prove2.me/submissions/30533a51-7bb2-41cf-b29b-6ab812b814eb

import Definitions.Def_DbarRegularity_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Theorems.Thm_DbarRegularity_lintegral_rpow_le_of_distribution_le
import Theorems.Thm_DbarRegularity_lintegral_rpow_le_of_distribution_le_two



namespace DbarRegularity

open MeasureTheory Metric Filter Topology Set
open scoped ENNReal NNReal ContDiff

theorem marcinkiewicz_interpolation (r p : ℝ≥0∞) (hr : 1 < r) (hp : 1 < p) (hpr : p < r)
    (A₁ Ar : ℝ≥0) :
    ∃ A : ℝ≥0, ∀ (d : ℕ)
      (T : (EuclideanSpace ℝ (Fin d) → ℂ) → EuclideanSpace ℝ (Fin d) → ℂ),
      (∀ f, (∃ f₁ f₂, MemLp f₁ 1 volume ∧ MemLp f₂ r volume ∧ f = f₁ + f₂) →
        AEStronglyMeasurable (T f) volume) →
      (∀ f g, (∃ f₁ f₂, MemLp f₁ 1 volume ∧ MemLp f₂ r volume ∧ f = f₁ + f₂) →
        (∃ g₁ g₂, MemLp g₁ 1 volume ∧ MemLp g₂ r volume ∧ g = g₁ + g₂) →
        ∀ᵐ x, ‖T (f + g) x‖ ≤ ‖T f x‖ + ‖T g x‖) →
      (∀ f, MemLp f 1 volume → ∀ α : ℝ≥0, 0 < α →
        volume {x | (α : ℝ≥0∞) < ‖T f x‖ₑ} ≤ (A₁ : ℝ≥0∞) / α * eLpNorm f 1 volume) →
      (r ≠ ⊤ → ∀ f, MemLp f r volume → ∀ α : ℝ≥0, 0 < α →
        volume {x | (α : ℝ≥0∞) < ‖T f x‖ₑ} ≤ ((Ar : ℝ≥0∞) / α * eLpNorm f r volume) ^ r.toReal) →
      (r = ⊤ → ∀ f, MemLp f ⊤ volume → eLpNorm (T f) ⊤ volume ≤ Ar * eLpNorm f ⊤ volume) →
      ∀ f, MemLp f p volume → eLpNorm (T f) p volume ≤ A * eLpNorm f p volume := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans hp).ne'
  have hpt : p ≠ ⊤ := hpr.ne_top
  have hr0 : r ≠ 0 := (zero_lt_one.trans hr).ne'
  set P := p.toReal with hPdef
  set R := r.toReal with hRdef
  have hP : 1 < P := by
    have := ENNReal.toReal_strict_mono hpt hp
    simpa using this
  have hP0 : 0 < P := by linarith
  -- the constants
  set κ : ℝ≥0∞ := ((Ar + 1 : ℝ≥0) : ℝ≥0∞) with hκdef
  have hκ0 : κ ≠ 0 := by simp [hκdef]
  have hκt : κ ≠ ⊤ := ENNReal.coe_ne_top
  have hArκ : (Ar : ℝ≥0∞) ≤ κ := by
    rw [hκdef, ENNReal.coe_le_coe]; exact le_add_of_nonneg_right zero_le_one
  set Kfin : ℝ≥0∞ := 2 * A₁ * ENNReal.ofReal (P / (P - 1)) +
    (2 * Ar) ^ R * ENNReal.ofReal (P / (R - P)) with hKfin
  set Ktop : ℝ≥0∞ := 2 ^ (P - 1) * (2 * A₁ * κ⁻¹) * ENNReal.ofReal (P / (P - 1)) * κ ^ P
    with hKtop
  have hKfin_ne : Kfin ≠ ⊤ := by
    have h2 : (2 * (Ar : ℝ≥0∞)) ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.coe_ne_top
    refine ENNReal.add_ne_top.2 ⟨?_, ?_⟩
    · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.coe_ne_top)
        ENNReal.ofReal_ne_top
    · exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg h2)
        ENNReal.ofReal_ne_top
  have hKtop_ne : Ktop ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ?_ ?_)
      ENNReal.ofReal_ne_top) (ENNReal.rpow_ne_top_of_nonneg hP0.le hκt)
    · exact ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofNat_ne_top
    · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.coe_ne_top)
        (ENNReal.inv_ne_top.2 hκ0)
  refine ⟨if r = ⊤ then Ktop.toNNReal ^ (1 / P) else Kfin.toNNReal ^ (1 / P),
    fun d T hmeas hsub hw1 hwr hinf f hf => ?_⟩
  -- final step: from an integral bound to the `L^p` bound
  have finish : ∀ (g : EuclideanSpace ℝ (Fin d) → ℂ) (K : ℝ≥0∞), K ≠ ⊤ →
      ∫⁻ x, ‖g x‖ₑ ^ P ≤ K * ∫⁻ x, ‖f x‖ₑ ^ P →
      eLpNorm g p volume ≤ ((K.toNNReal ^ (1 / P) : ℝ≥0) : ℝ≥0∞) * eLpNorm f p volume := by
    intro g K hK h
    rw [eLpNorm_eq_lintegral_rpow_enorm hp0 hpt, eLpNorm_eq_lintegral_rpow_enorm hp0 hpt,
      ENNReal.coe_rpow_of_nonneg _ (by positivity), ENNReal.coe_toNNReal hK,
      ← ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
    exact ENNReal.rpow_le_rpow h (by positivity)
  have hfin : ∫⁻ x, ‖f x‖ₑ ^ P < ⊤ := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hpt hf.2
  -- truncations
  have hsplit : ∀ s : ℝ≥0∞, f = {x | s < ‖f x‖ₑ}.indicator f + {x | ‖f x‖ₑ ≤ s}.indicator f := by
    intro s; funext x
    simp only [Pi.add_apply, indicator_apply, mem_setOf_eq]
    by_cases h : s < ‖f x‖ₑ
    · simp [h, not_le.2 h]
    · simp [h, not_lt.1 h]
  have mem1 : ∀ s : ℝ≥0∞, s ≠ 0 → s ≠ ⊤ → MemLp ({x | s < ‖f x‖ₑ}.indicator f) 1 volume := by
    intro s hs0 hst
    have hS : NullMeasurableSet {x | s < ‖f x‖ₑ} volume :=
      nullMeasurableSet_lt aemeasurable_const hf.1.enorm
    refine ⟨hf.1.indicator₀ hS, ?_⟩
    rw [eLpNorm_one_eq_lintegral_enorm]
    calc ∫⁻ x, ‖{x | s < ‖f x‖ₑ}.indicator f x‖ₑ
        ≤ ∫⁻ x, s ^ (1 - P) * ‖f x‖ₑ ^ P := lintegral_mono fun x => ?_
      _ = s ^ (1 - P) * ∫⁻ x, ‖f x‖ₑ ^ P :=
          lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_ne_zero hs0 hst)
      _ < ⊤ := ENNReal.mul_lt_top (ENNReal.rpow_ne_top_of_ne_zero hs0 hst).lt_top hfin
    simp only [indicator_apply, mem_setOf_eq]
    split_ifs with hx
    · set a := ‖f x‖ₑ
      have hapow : a ^ P = a * a ^ (P - 1) := by
        conv_lhs => rw [show P = 1 + (P - 1) by ring]
        rw [ENNReal.rpow_add_of_nonneg _ _ zero_le_one (by linarith), ENNReal.rpow_one]
      calc a = a * (s ^ (1 - P) * s ^ (P - 1)) := by
            rw [← ENNReal.rpow_add _ _ hs0 hst, show 1 - P + (P - 1) = 0 by ring,
              ENNReal.rpow_zero, mul_one]
        _ ≤ a * (s ^ (1 - P) * a ^ (P - 1)) := by
            gcongr
        _ = s ^ (1 - P) * a ^ P := by rw [hapow]; ring
    · simp
  have hle2 : ∀ s : ℝ≥0∞, eLpNorm ({x | ‖f x‖ₑ ≤ s}.indicator f) ⊤ volume ≤ s := by
    intro s
    rw [eLpNorm_exponent_top]
    refine eLpNormEssSup_le_of_ae_enorm_bound (ae_of_all _ fun x => ?_)
    simp only [indicator_apply, mem_setOf_eq]
    split_ifs with hx
    · exact hx
    · simp
  have hS2 : ∀ s : ℝ≥0∞, NullMeasurableSet {x | ‖f x‖ₑ ≤ s} volume := fun s =>
    nullMeasurableSet_le hf.1.enorm aemeasurable_const
  -- the `r`-th power integral of the lower truncation (finite `r`)
  have int2 : r ≠ ⊤ → ∀ s : ℝ≥0∞,
      eLpNorm ({x | ‖f x‖ₑ ≤ s}.indicator f) r volume ^ R =
        ∫⁻ x, {x | ‖f x‖ₑ ≤ s}.indicator (fun x => ‖f x‖ₑ ^ R) x := by
    intro hrt s
    have hR0 : 0 < R := ENNReal.toReal_pos hr0 hrt
    rw [eLpNorm_eq_lintegral_rpow_enorm hr0 hrt, ← ENNReal.rpow_mul, one_div,
      inv_mul_cancel₀ hR0.ne', ENNReal.rpow_one]
    refine lintegral_congr fun x => ?_
    simp only [indicator_apply, mem_setOf_eq]
    split_ifs <;> first | rfl | rw [enorm_zero, ENNReal.zero_rpow_of_pos hR0]
  have mem2 : ∀ s : ℝ≥0∞, s ≠ ⊤ → MemLp ({x | ‖f x‖ₑ ≤ s}.indicator f) r volume := by
    intro s hst
    refine ⟨hf.1.indicator₀ (hS2 s), ?_⟩
    rcases eq_or_ne r ⊤ with hrt | hrt
    · rw [hrt]; exact (hle2 s).trans_lt hst.lt_top
    have hR0 : 0 < R := ENNReal.toReal_pos hr0 hrt
    have hPR : P < R := ENNReal.toReal_strict_mono hrt hpr
    refine (ENNReal.rpow_lt_top_iff_of_pos hR0).1 ?_
    rw [int2 hrt s]
    calc ∫⁻ x, {x | ‖f x‖ₑ ≤ s}.indicator (fun x => ‖f x‖ₑ ^ R) x
        ≤ ∫⁻ x, s ^ (R - P) * ‖f x‖ₑ ^ P := lintegral_mono fun x => ?_
      _ = s ^ (R - P) * ∫⁻ x, ‖f x‖ₑ ^ P :=
          lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith) hst)
      _ < ⊤ := ENNReal.mul_lt_top (ENNReal.rpow_ne_top_of_nonneg (by linarith) hst).lt_top hfin
    simp only [indicator_apply, mem_setOf_eq]
    split_ifs with hx
    · calc ‖f x‖ₑ ^ R = ‖f x‖ₑ ^ P * ‖f x‖ₑ ^ (R - P) := by
            rw [← ENNReal.rpow_add_of_nonneg _ _ hP0.le (by linarith), add_sub_cancel]
        _ ≤ ‖f x‖ₑ ^ P * s ^ (R - P) := by
            gcongr
        _ = s ^ (R - P) * ‖f x‖ₑ ^ P := mul_comm _ _
    · exact bot_le
  -- membership in `L¹ + L^r`
  have hdec : ∀ s : ℝ≥0∞, s ≠ 0 → s ≠ ⊤ →
      (∃ f₁ f₂, MemLp f₁ 1 volume ∧ MemLp f₂ r volume ∧
        {x | s < ‖f x‖ₑ}.indicator f = f₁ + f₂) ∧
      (∃ f₁ f₂, MemLp f₁ 1 volume ∧ MemLp f₂ r volume ∧
        {x | ‖f x‖ₑ ≤ s}.indicator f = f₁ + f₂) := fun s hs0 hst =>
    ⟨⟨_, 0, mem1 s hs0 hst, MemLp.zero, (add_zero _).symm⟩,
      ⟨0, _, MemLp.zero, mem2 s hst, (zero_add _).symm⟩⟩
  have hTm : AEStronglyMeasurable (T f) volume :=
    hmeas f ⟨_, _, mem1 1 one_ne_zero ENNReal.one_ne_top, mem2 1 ENNReal.one_ne_top, hsplit 1⟩
  -- splitting the distribution function
  have dist : ∀ s : ℝ≥0∞, s ≠ 0 → s ≠ ⊤ → ∀ u : ℝ≥0,
      volume {x | (u : ℝ≥0∞) < ‖T f x‖ₑ} ≤
        volume {x | ((u / 2 : ℝ≥0) : ℝ≥0∞) < ‖T ({x | s < ‖f x‖ₑ}.indicator f) x‖ₑ} +
        volume {x | ((u / 2 : ℝ≥0) : ℝ≥0∞) < ‖T ({x | ‖f x‖ₑ ≤ s}.indicator f) x‖ₑ} := by
    intro s hs0 hst u
    have hs := hsub _ _ (hdec s hs0 hst).1 (hdec s hs0 hst).2
    rw [← hsplit s] at hs
    refine (measure_mono_ae ?_).trans (measure_union_le _ _)
    filter_upwards [hs] with x hx
    intro hlt
    change (u : ℝ≥0∞) < ‖T f x‖ₑ at hlt
    by_cases hn1 : ((u / 2 : ℝ≥0) : ℝ≥0∞) < ‖T ({x | s < ‖f x‖ₑ}.indicator f) x‖ₑ
    · exact Or.inl hn1
    by_cases hn2 : ((u / 2 : ℝ≥0) : ℝ≥0∞) < ‖T ({x | ‖f x‖ₑ ≤ s}.indicator f) x‖ₑ
    · exact Or.inr hn2
    exfalso
    have hn : _ ∧ _ := ⟨not_lt.1 hn1, not_lt.1 hn2⟩
    have hx' : ‖T f x‖ₑ ≤ ‖T ({x | s < ‖f x‖ₑ}.indicator f) x‖ₑ +
        ‖T ({x | ‖f x‖ₑ ≤ s}.indicator f) x‖ₑ := by
      simp only [enorm_eq_nnnorm]
      exact_mod_cast hx
    have : ‖T f x‖ₑ ≤ u := by
      refine hx'.trans ((add_le_add hn.1 hn.2).trans_eq ?_)
      rw [ENNReal.coe_div two_ne_zero, ENNReal.coe_ofNat, ENNReal.add_halves]
    exact absurd hlt (not_lt.2 this)
  have hhalf : ∀ (a : ℝ≥0∞) (u : ℝ≥0), a / ((u / 2 : ℝ≥0) : ℝ≥0∞) = 2 * a / u := by
    intro a u
    rw [ENNReal.coe_div two_ne_zero, ENNReal.coe_ofNat, div_eq_mul_inv a ((u : ℝ≥0∞) / 2),
      div_eq_mul_inv (u : ℝ≥0∞) 2, ENNReal.mul_inv (by simp) (by simp), inv_inv,
      div_eq_mul_inv (2 * a) (u : ℝ≥0∞)]
    ring
  have hone : ∀ s : ℝ≥0∞, eLpNorm ({x | s < ‖f x‖ₑ}.indicator f) 1 volume =
      ∫⁻ x, {x | s < ‖f x‖ₑ}.indicator (fun x => ‖f x‖ₑ) x := by
    intro s
    rw [eLpNorm_one_eq_lintegral_enorm]
    simp_rw [enorm_indicator_eq_indicator_enorm]
  by_cases hrt : r = ⊤
  · -- `r = ∞`
    rw [if_pos hrt]
    refine finish _ Ktop hKtop_ne ?_
    have H : ∀ t : ℝ≥0, 0 < t → volume {x | (t : ℝ≥0∞) < ‖T f x‖ₑ} ≤
        2 * A₁ * κ⁻¹ / t * ∫⁻ x, {x | (t : ℝ≥0∞) / 2 < κ * ‖f x‖ₑ}.indicator
          (fun x => κ * ‖f x‖ₑ) x := by
      intro t ht
      set s : ℝ≥0∞ := (t : ℝ≥0∞) / 2 / κ
      have hs0 : s ≠ 0 := by
        simp only [s]
        exact ENNReal.div_ne_zero.2 ⟨ENNReal.div_ne_zero.2 ⟨by exact_mod_cast ht.ne',
          ENNReal.ofNat_ne_top⟩, hκt⟩
      have hst : s ≠ ⊤ := ENNReal.div_ne_top (ENNReal.div_ne_top ENNReal.coe_ne_top two_ne_zero) hκ0
      have hset : {x | (t : ℝ≥0∞) / 2 < κ * ‖f x‖ₑ} = {x | s < ‖f x‖ₑ} := by
        ext x
        simp only [mem_setOf_eq, s]
        rw [ENNReal.div_lt_iff (Or.inl hκ0) (Or.inl hκt), mul_comm]
      have h2 : volume {x | ((t / 2 : ℝ≥0) : ℝ≥0∞) <
          ‖T ({x | ‖f x‖ₑ ≤ s}.indicator f) x‖ₑ} = 0 := by
        have hb : eLpNorm (T ({x | ‖f x‖ₑ ≤ s}.indicator f)) ⊤ volume ≤ ((t / 2 : ℝ≥0) : ℝ≥0∞) := by
          refine (hinf hrt _ (hrt ▸ mem2 s hst)).trans ?_
          calc (Ar : ℝ≥0∞) * eLpNorm ({x | ‖f x‖ₑ ≤ s}.indicator f) ⊤ volume
              ≤ κ * s := by gcongr; exact hle2 s
            _ = ((t / 2 : ℝ≥0) : ℝ≥0∞) := by
                simp only [s]
                rw [ENNReal.mul_div_cancel hκ0 hκt, ENNReal.coe_div two_ne_zero, ENNReal.coe_ofNat]
        rw [eLpNorm_exponent_top] at hb
        have hae : ∀ᵐ x ∂volume, ‖T ({x | ‖f x‖ₑ ≤ s}.indicator f) x‖ₑ ≤
            ((t / 2 : ℝ≥0) : ℝ≥0∞) := by
          filter_upwards [enorm_ae_le_eLpNormEssSup (T ({x | ‖f x‖ₑ ≤ s}.indicator f)) volume]
            with x hx
          exact hx.trans hb
        simpa only [not_le] using ae_iff.1 hae
      have h1 := hw1 _ (mem1 s hs0 hst) (t / 2) (half_pos ht)
      rw [hhalf, hone] at h1
      calc volume {x | (t : ℝ≥0∞) < ‖T f x‖ₑ}
          ≤ _ := dist s hs0 hst t
        _ ≤ 2 * A₁ / t * ∫⁻ x, {x | s < ‖f x‖ₑ}.indicator (fun x => ‖f x‖ₑ) x := by
            rw [h2, add_zero]; exact h1
        _ = 2 * A₁ * κ⁻¹ / t * ∫⁻ x, {x | (t : ℝ≥0∞) / 2 < κ * ‖f x‖ₑ}.indicator
              (fun x => κ * ‖f x‖ₑ) x := by
            rw [hset]
            have e : ∫⁻ x, {x | s < ‖f x‖ₑ}.indicator (fun x => κ * ‖f x‖ₑ) x =
                κ * ∫⁻ x, {x | s < ‖f x‖ₑ}.indicator (fun x => ‖f x‖ₑ) x := by
              rw [← lintegral_const_mul' _ _ hκt]
              refine lintegral_congr fun x => ?_
              simp only [indicator_apply]
              split_ifs <;> simp
            rw [e]
            calc 2 * (A₁ : ℝ≥0∞) / t * ∫⁻ x, {x | s < ‖f x‖ₑ}.indicator (fun x => ‖f x‖ₑ) x
                = 2 * A₁ / t * (∫⁻ x, {x | s < ‖f x‖ₑ}.indicator (fun x => ‖f x‖ₑ) x) *
                    (κ⁻¹ * κ) := by rw [ENNReal.inv_mul_cancel hκ0 hκt, mul_one]
              _ = _ := by simp only [div_eq_mul_inv]; ring
    have := lintegral_rpow_le_of_distribution_le volume hTm.enorm
      (hf.1.enorm.const_mul κ) hP (2 * A₁ * κ⁻¹) H
    refine this.trans (le_of_eq ?_)
    have e : ∫⁻ x, (κ * ‖f x‖ₑ) ^ P = κ ^ P * ∫⁻ x, ‖f x‖ₑ ^ P := by
      rw [← lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hP0.le hκt)]
      refine lintegral_congr fun x => ?_
      rw [ENNReal.mul_rpow_of_nonneg _ _ hP0.le]
    rw [e, hKtop]; ring
  · -- `r < ∞`
    rw [if_neg hrt]
    have hR0 : 0 < R := ENNReal.toReal_pos hr0 hrt
    have hPR : P < R := ENNReal.toReal_strict_mono hrt hpr
    refine finish _ Kfin hKfin_ne ?_
    refine lintegral_rpow_le_of_distribution_le_two volume hTm.enorm hf.1.enorm hP hPR
      (2 * A₁) (2 * Ar) fun t ht => ?_
    have hs0 : (t : ℝ≥0∞) ≠ 0 := by exact_mod_cast ht.ne'
    have hst : (t : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
    have h1 := hw1 _ (mem1 t hs0 hst) (t / 2) (half_pos ht)
    rw [hhalf, hone] at h1
    have h2 := hwr hrt _ (mem2 t hst) (t / 2) (half_pos ht)
    rw [hhalf, ENNReal.mul_rpow_of_nonneg _ _ hR0.le, int2 hrt] at h2
    exact (dist t hs0 hst t).trans (add_le_add h1 h2)

end DbarRegularity

open DbarRegularity

open MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ContDiff

theorem solution (r p : ℝ≥0∞) (hr : 1 < r) (hp : 1 < p) (hpr : p < r)
    (A₁ Ar : ℝ≥0) :
    ∃ A : ℝ≥0, ∀ (d : ℕ)
      (T : (EuclideanSpace ℝ (Fin d) → ℂ) → EuclideanSpace ℝ (Fin d) → ℂ),
      (∀ f, (∃ f₁ f₂, MemLp f₁ 1 volume ∧ MemLp f₂ r volume ∧ f = f₁ + f₂) →
        AEStronglyMeasurable (T f) volume) →
      (∀ f g, (∃ f₁ f₂, MemLp f₁ 1 volume ∧ MemLp f₂ r volume ∧ f = f₁ + f₂) →
        (∃ g₁ g₂, MemLp g₁ 1 volume ∧ MemLp g₂ r volume ∧ g = g₁ + g₂) →
        ∀ᵐ x, ‖T (f + g) x‖ ≤ ‖T f x‖ + ‖T g x‖) →
      (∀ f, MemLp f 1 volume → ∀ α : ℝ≥0, 0 < α →
        volume {x | (α : ℝ≥0∞) < ‖T f x‖ₑ} ≤ (A₁ : ℝ≥0∞) / α * eLpNorm f 1 volume) →
      (r ≠ ⊤ → ∀ f, MemLp f r volume → ∀ α : ℝ≥0, 0 < α →
        volume {x | (α : ℝ≥0∞) < ‖T f x‖ₑ} ≤ ((Ar : ℝ≥0∞) / α * eLpNorm f r volume) ^ r.toReal) →
      (r = ⊤ → ∀ f, MemLp f ⊤ volume → eLpNorm (T f) ⊤ volume ≤ Ar * eLpNorm f ⊤ volume) →
      ∀ f, MemLp f p volume → eLpNorm (T f) p volume ≤ A * eLpNorm f p volume :=
  DbarRegularity.marcinkiewicz_interpolation r p hr hp hpr A₁ Ar
