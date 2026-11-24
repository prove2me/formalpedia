-- Prove2me | solution 1 for FaulhuberTFA.ambiguity_max_at_origin
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T20:33:42.649393+00:00
-- url     : https://prove2.me/submissions/6fc04902-604e-446b-ba47-b9e7aae7076f

import Mathlib
import Definitions.Def_FaulhuberTFA_Basic

set_option autoImplicit false

open MeasureTheory Complex
open scoped InnerProductSpace

namespace FaulhuberTFA

variable {d : ℕ}

lemma uc_ePhase_norm (s : ℝ) : ‖ePhase s‖ = 1 := by
  unfold ePhase
  rw [show (2 * Real.pi * Complex.I * (s : ℂ)) = ((2 * Real.pi * s : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma uc_ePhase_cont : Continuous ePhase := by unfold ePhase; fun_prop

lemma uc_ePhase_add (a b : ℝ) : ePhase (a + b) = ePhase a * ePhase b := by
  unfold ePhase; rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma uc_f_ae_zero {f : Rd d → ℂ} (h : (fun t => ‖f t‖ ^ 2) =ᵐ[volume] 0) : f =ᵐ[volume] 0 := by
  filter_upwards [h] with t ht
  simpa using ht

/-- A nonnegative integrable function which is a.e. invariant under translation by `x ≠ 0`
vanishes a.e. -/
lemma uc_periodic_zero {u : Rd d → ℝ} (hu : Integrable u volume) (hu0 : ∀ t, 0 ≤ u t)
    {x : Rd d} (hx : x ≠ 0) (hper : (fun s => u (s + x)) =ᵐ[volume] u) : u =ᵐ[volume] 0 := by
  have hn : ∀ n : ℕ, (fun s => u (s + (n : ℝ) • x)) =ᵐ[volume] u := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 : (fun s => u (s + x + (n : ℝ) • x)) =ᵐ[volume] fun s => u (s + x) :=
        (measurePreserving_add_right volume x).quasiMeasurePreserving.ae_eq_comp ih
      refine (Filter.EventuallyEq.trans ?_ h1).trans hper
      filter_upwards with s
      congr 1; push_cast; rw [add_smul, one_smul]; abel
  have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hball : ∀ R : ℝ, ∫ t, (Metric.closedBall (0 : Rd d) R).indicator u t = 0 := by
    intro R
    set B := Metric.closedBall (0 : Rd d) R
    let F : ℕ → Rd d → ℝ := fun n => {t : Rd d | ‖t - (n : ℝ) • x‖ ≤ R}.indicator u
    have hEq : ∀ n, ∫ t, F n t = ∫ t, B.indicator u t := by
      intro n
      have h1 : ∀ t, F n t = B.indicator (fun s => u (s + (n : ℝ) • x)) (t - (n : ℝ) • x) := by
        intro t
        show {t : Rd d | ‖t - (n : ℝ) • x‖ ≤ R}.indicator u t = _
        by_cases h : ‖t - (n : ℝ) • x‖ ≤ R
        · rw [Set.indicator_of_mem (show t ∈ {t : Rd d | ‖t - (n : ℝ) • x‖ ≤ R} from h),
            Set.indicator_of_mem (show t - (n : ℝ) • x ∈ B by
              rw [Metric.mem_closedBall, dist_zero_right]; exact h), sub_add_cancel]
        · rw [Set.indicator_of_notMem (show t ∉ {t : Rd d | ‖t - (n : ℝ) • x‖ ≤ R} from h),
            Set.indicator_of_notMem (show t - (n : ℝ) • x ∉ B by
              rw [Metric.mem_closedBall, dist_zero_right]; exact h)]
      rw [integral_congr_ae (Filter.Eventually.of_forall h1)]
      rw [integral_sub_right_eq_self (fun s => B.indicator (fun s => u (s + (n : ℝ) • x)) s)]
      apply integral_congr_ae
      filter_upwards [hn n] with s hs
      by_cases hb : s ∈ B
      · rw [Set.indicator_of_mem hb, Set.indicator_of_mem hb]; exact hs
      · rw [Set.indicator_of_notMem hb, Set.indicator_of_notMem hb]
    have hT : Filter.Tendsto (fun n => ∫ t, F n t) Filter.atTop (nhds (∫ _ : Rd d, (0 : ℝ))) := by
      apply tendsto_integral_of_dominated_convergence u
      · intro n
        exact hu.1.indicator ((isClosed_le (by fun_prop) continuous_const).measurableSet)
      · exact hu
      · intro n
        refine Filter.Eventually.of_forall fun t => ?_
        calc ‖F n t‖ ≤ ‖u t‖ := norm_indicator_le_norm_self _ _
          _ = u t := Real.norm_of_nonneg (hu0 t)
      · refine Filter.Eventually.of_forall fun t => ?_
        obtain ⟨N, hN⟩ := exists_nat_gt ((R + ‖t‖) / ‖x‖)
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [Filter.eventually_ge_atTop N] with n hn
        have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
        have h2 : R + ‖t‖ < (n : ℝ) * ‖x‖ := by
          rw [div_lt_iff₀ hxpos] at hN; nlinarith
        have h3 : ‖(n : ℝ) • x‖ - ‖t‖ ≤ ‖t - (n : ℝ) • x‖ := by
          rw [norm_sub_rev]; exact norm_sub_norm_le _ _
        rw [norm_smul, Real.norm_of_nonneg (by positivity)] at h3
        have h4 : ¬ ‖t - (n : ℝ) • x‖ ≤ R := by intro h; linarith
        simp only [F, Set.indicator_apply, Set.mem_ofPred_eq, h4, if_false]
    rw [integral_zero] at hT
    exact tendsto_nhds_unique ((tendsto_const_nhds).congr fun n => (hEq n).symm) hT
  have hz : ∀ n : ℕ, (Metric.closedBall (0 : Rd d) n).indicator u =ᵐ[volume] 0 := by
    intro n
    exact (integral_eq_zero_iff_of_nonneg (Set.indicator_nonneg (fun t _ => hu0 t))
      (hu.indicator Metric.isClosed_closedBall.measurableSet)).1 (hball n)
  filter_upwards [ae_all_iff.2 hz] with t ht
  have hmem : t ∈ Metric.closedBall (0 : Rd d) (⌈‖t‖⌉₊ : ℕ) := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact Nat.le_ceil _
  have := ht ⌈‖t‖⌉₊
  rwa [Set.indicator_of_mem hmem] at this

/-- Level sets of `t ↦ e^{-2πi ω·t}` are Lebesgue-null when `ω ≠ 0`. -/
lemma uc_null_phase {ω : Rd d} (hω : ω ≠ 0) (c : ℂ) :
    volume {t : Rd d | ePhase (-⟪ω, t⟫_ℝ) = c} = 0 := by
  by_cases h : ∃ t₀, ePhase (-⟪ω, t₀⟫_ℝ) = c
  swap
  · push Not at h
    have : {t : Rd d | ePhase (-⟪ω, t⟫_ℝ) = c} = ∅ := by
      ext t; simp [h t]
    rw [this, measure_empty]
  obtain ⟨t₀, rfl⟩ := h
  set K : Submodule ℝ (Rd d) := (ℝ ∙ ω)ᗮ
  have hK : K ≠ ⊤ := by
    intro h
    have : ω ∈ K := h ▸ Submodule.mem_top
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at this
    exact hω (inner_self_eq_zero.1 this)
  have hK0 : volume (K : Set (Rd d)) = 0 := Measure.addHaar_submodule _ K hK
  have hω2 : ‖ω‖ ^ 2 ≠ 0 := by positivity
  have hsub : {t : Rd d | ePhase (-⟪ω, t⟫_ℝ) = ePhase (-⟪ω, t₀⟫_ℝ)} ⊆
      ⋃ n : ℤ, (fun t => t + (-t₀ + ((n : ℝ) / ‖ω‖ ^ 2) • ω)) ⁻¹' (K : Set (Rd d)) := by
    intro t ht
    simp only [Set.mem_ofPred_eq] at ht
    have h1 : ePhase (⟪ω, t₀⟫_ℝ - ⟪ω, t⟫_ℝ) = 1 := by
      have h0 : ePhase (-⟪ω, t₀⟫_ℝ) ≠ 0 := by
        intro h0; have := uc_ePhase_norm (-⟪ω, t₀⟫_ℝ); rw [h0, norm_zero] at this; norm_num at this
      have := uc_ePhase_add (⟪ω, t₀⟫_ℝ - ⟪ω, t⟫_ℝ) (-⟪ω, t₀⟫_ℝ)
      rw [show ⟪ω, t₀⟫_ℝ - ⟪ω, t⟫_ℝ + -⟪ω, t₀⟫_ℝ = -⟪ω, t⟫_ℝ by ring, ht] at this
      exact (mul_eq_right₀ h0).1 this.symm
    unfold ePhase at h1
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h1
    have h2 : ((⟪ω, t₀⟫_ℝ - ⟪ω, t⟫_ℝ : ℝ) : ℂ) = (n : ℂ) := by
      have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
      apply mul_left_cancel₀ hne; rw [hn]; ring
    have h3 : ⟪ω, t₀⟫_ℝ - ⟪ω, t⟫_ℝ = n := by exact_mod_cast h2
    refine Set.mem_iUnion.2 ⟨n, ?_⟩
    simp only [Set.mem_preimage, SetLike.mem_coe, K,
      Submodule.mem_orthogonal_singleton_iff_inner_right]
    rw [inner_add_right, inner_add_right, inner_neg_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
    field_simp
    linarith
  refine measure_mono_null hsub (measure_iUnion_null fun n => ?_)
  rw [measure_preimage_add_right]; exact hK0

lemma uc_amb_origin (f : Rd d → ℂ) : ambiguity f 0 0 = ((∫ t, ‖f t‖ ^ 2 : ℝ) : ℂ) := by
  unfold ambiguity crossAmbiguity
  rw [← integral_complex_ofReal]
  congr 1; funext t
  simp only [smul_zero, add_zero, sub_zero, inner_zero_left, neg_zero]
  rw [show ePhase 0 = 1 by simp [ePhase], mul_one, Complex.mul_conj, Complex.normSq_eq_norm_sq]

lemma uc_case_x {f : Rd d → ℂ} (hf : MemLp f 2 volume) (hf0 : ¬ f =ᵐ[volume] 0) {x : Rd d}
    (hx : x ≠ 0) (ω : Rd d) : ‖ambiguity f x ω‖ < ∫ t, ‖f t‖ ^ 2 := by
  set h := (1 / 2 : ℝ) • x with hh
  set a : Rd d → ℝ := fun t => ‖f (t + h)‖ with ha_def
  set b : Rd d → ℝ := fun t => ‖f (t - h)‖ with hb_def
  have ha : MemLp a 2 volume :=
    (hf.comp_measurePreserving (measurePreserving_add_right volume h)).norm
  have hb : MemLp b 2 volume :=
    (hf.comp_measurePreserving (measurePreserving_sub_right volume h)).norm
  have hle : ‖ambiguity f x ω‖ ≤ ∫ t, a t * b t := by
    unfold ambiguity crossAmbiguity
    refine (norm_integral_le_integral_norm _).trans
      (le_of_eq (integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)))
    simp only [a, b, h]
    rw [norm_mul, norm_mul, uc_ePhase_norm, mul_one, Complex.norm_conj]
  have hA : ∫ t, a t ^ 2 = ∫ t, ‖f t‖ ^ 2 := integral_add_right_eq_self (fun t => ‖f t‖ ^ 2) h
  have hB : ∫ t, b t ^ 2 = ∫ t, ‖f t‖ ^ 2 := integral_sub_right_eq_self (fun t => ‖f t‖ ^ 2) h
  have hab : ∫ t, a t * b t = (∫ t, ‖f t‖ ^ 2) - (1 / 2) * ∫ t, (a t - b t) ^ 2 := by
    have e : (fun t => a t * b t) = fun t => (1 / 2) * ((a t ^ 2 + b t ^ 2) - (a t - b t) ^ 2) := by
      funext t; ring
    rw [e, integral_const_mul, integral_sub (f := fun t => a t ^ 2 + b t ^ 2)
      (g := fun t => (a t - b t) ^ 2) (ha.integrable_sq.add hb.integrable_sq)
      (ha.sub hb).integrable_sq, integral_add (f := fun t => a t ^ 2) (g := fun t => b t ^ 2)
      ha.integrable_sq hb.integrable_sq, hA, hB]
    ring
  have hsq : 0 ≤ ∫ t, (a t - b t) ^ 2 := integral_nonneg fun t => sq_nonneg _
  by_contra hcon
  push Not at hcon
  have h0 : ∫ t, (a t - b t) ^ 2 = 0 := by linarith
  have h1 : (fun t => (a t - b t) ^ 2) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun t => sq_nonneg _) (ha.sub hb).integrable_sq).1 h0
  have h2 : a =ᵐ[volume] b := by
    filter_upwards [h1] with t ht
    have : a t - b t = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 ht
    linarith
  have h3 : (fun s => ‖f (s + x)‖ ^ 2) =ᵐ[volume] fun s => ‖f s‖ ^ 2 := by
    have := (measurePreserving_add_right volume h).quasiMeasurePreserving.ae_eq_comp h2
    filter_upwards [this] with s hs
    simp only [Function.comp, a, b] at hs
    have e1 : s + h + h = s + x := by rw [hh, add_assoc, ← add_smul]; norm_num
    rw [e1, add_sub_cancel_right] at hs
    rw [hs]
  exact hf0 (uc_f_ae_zero (uc_periodic_zero hf.norm.integrable_sq (fun t => sq_nonneg _) hx h3))

lemma uc_case_ω {f : Rd d → ℂ} (hf : MemLp f 2 volume) (hf0 : ¬ f =ᵐ[volume] 0) {ω : Rd d}
    (hω : ω ≠ 0) : ‖ambiguity f 0 ω‖ < ∫ t, ‖f t‖ ^ 2 := by
  set u : Rd d → ℝ := fun t => ‖f t‖ ^ 2 with hu_def
  have hu : Integrable u volume := hf.norm.integrable_sq
  set E : Rd d → ℂ := fun t => ePhase (-⟪ω, t⟫_ℝ) with hE_def
  have hE : ∀ t, ‖E t‖ = 1 := fun t => uc_ePhase_norm _
  have hEc : Continuous E := uc_ePhase_cont.comp (by fun_prop)
  have hamb : ambiguity f 0 ω = ∫ t, (u t : ℂ) * E t := by
    unfold ambiguity crossAmbiguity
    congr 1; funext t
    simp only [smul_zero, add_zero, sub_zero, u, E]
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  set M := ∫ t, u t with hM_def
  have hM : 0 < M := by
    rcases (integral_nonneg (fun t => sq_nonneg ‖f t‖) : 0 ≤ M).lt_or_eq with h | h
    · exact h
    · exact absurd (uc_f_ae_zero ((integral_eq_zero_iff_of_nonneg
        (fun t => sq_nonneg _) hu).1 h.symm)) hf0
  have hnorm : ∀ t, ‖(u t : ℂ) * E t‖ = u t := fun t => by
    rw [norm_mul, hE, mul_one, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
  have hint : Integrable (fun t => (u t : ℂ) * E t) volume :=
    Integrable.mono' hu ((continuous_ofReal.comp_aestronglyMeasurable hu.1).mul
      hEc.aestronglyMeasurable) (Filter.Eventually.of_forall fun t => (hnorm t).le)
  set I := ∫ t, (u t : ℂ) * E t with hI_def
  have hIle : ‖I‖ ≤ M :=
    (norm_integral_le_integral_norm _).trans
      (le_of_eq (integral_congr_ae (Filter.Eventually.of_forall hnorm)))
  rw [hamb]
  by_contra hcon
  push Not at hcon
  have hIM : ‖I‖ = M := le_antisymm hIle hcon
  set φ : Rd d → ℝ := fun t => M * u t - (starRingEnd ℂ I * ((u t : ℂ) * E t)).re with hφ_def
  have hφ_eq : ∀ t, φ t = u t * (M - (starRingEnd ℂ I * E t).re) := fun t => by
    simp only [φ]; rw [mul_left_comm, Complex.re_ofReal_mul]; ring
  have hφ0 : ∀ t, 0 ≤ φ t := fun t => by
    rw [hφ_eq]; apply mul_nonneg (sq_nonneg _)
    have := Complex.re_le_norm (starRingEnd ℂ I * E t)
    rw [norm_mul, hE, mul_one, Complex.norm_conj, hIM] at this; linarith
  have hφi : Integrable φ volume := (hu.const_mul M).sub (hint.const_mul (starRingEnd ℂ I)).re
  have hr := integral_re (𝕜 := ℂ) (hint.const_mul (starRingEnd ℂ I))
  simp only [RCLike.re_to_complex] at hr
  rw [integral_const_mul] at hr
  have hφint : ∫ t, φ t = 0 := by
    simp only [φ]
    rw [integral_sub (f := fun t => M * u t)
      (g := fun t => (starRingEnd ℂ I * ((u t : ℂ) * E t)).re) (hu.const_mul M)
      (hint.const_mul _).re, integral_const_mul, hr, ← hI_def, Complex.conj_mul', ← ofReal_pow,
      ofReal_re, hIM]
    ring
  have h1 := (integral_eq_zero_iff_of_nonneg hφ0 hφi).1 hφint
  have h2 : ∀ᵐ t ∂volume, t ∉ {t : Rd d | ePhase (-⟪ω, t⟫_ℝ) = (M : ℂ) / starRingEnd ℂ I} :=
    measure_eq_zero_iff_ae_notMem.1 (uc_null_phase hω _)
  have hI0 : I ≠ 0 := by intro h; rw [h, norm_zero] at hIM; linarith
  have h3 : u =ᵐ[volume] 0 := by
    filter_upwards [h1, h2] with t ht ht2
    rw [Pi.zero_apply, hφ_eq] at ht
    rcases mul_eq_zero.1 ht with h | h
    · exact h
    · exfalso; apply ht2
      have hz : ‖starRingEnd ℂ I * E t‖ = M := by
        rw [norm_mul, hE, mul_one, Complex.norm_conj, hIM]
      have hre : (starRingEnd ℂ I * E t).re = M := by linarith
      have him : (starRingEnd ℂ I * E t).im = 0 := by
        have := Complex.sq_norm (starRingEnd ℂ I * E t)
        rw [Complex.normSq_apply, hz, hre] at this; nlinarith
      have hzM : starRingEnd ℂ I * E t = (M : ℂ) := Complex.ext (by simp [hre]) (by simp [him])
      show E t = _
      rw [eq_div_iff ((map_ne_zero _).2 hI0), mul_comm]; exact hzM
  exact hf0 (uc_f_ae_zero h3)

end FaulhuberTFA

open FaulhuberTFA in
theorem solution {d : ℕ} {f : Rd d → ℂ} (hf : MemLp f 2 volume) (hf0 : ¬ f =ᵐ[volume] 0) :
    ambiguity f 0 0 = ((∫ t, ‖f t‖ ^ 2 : ℝ) : ℂ) ∧
    ∀ x ω : Rd d, (x, ω) ≠ (0, 0) → ‖ambiguity f x ω‖ < ∫ t, ‖f t‖ ^ 2 := by
  refine ⟨uc_amb_origin f, fun x ω hxω => ?_⟩
  by_cases hx : x = 0
  · subst hx
    have hω : ω ≠ 0 := by rintro rfl; exact hxω rfl
    exact uc_case_ω hf hf0 hω
  · exact uc_case_x hf hf0 hx ω
