-- Prove2me | solution 1 for Fcdf_at_one_ge_half
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-21T22:35:08.878779+00:00
-- url     : https://prove2.me/submissions/88644383-8f9c-4fb6-a37f-a5c5b3194bb8

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
-- Imported platform lemmas (server-side `:= by sorry` stubs); this reduction uses them.
import Theorems.Thm_Waiting_waiting_time_density
import Theorems.Thm_waiting_time_cdf_at_zero
import Theorems.Thm_waiting_time_mass_eq_one
import Theorems.Thm_waiting_time_density_integrable
import Theorems.Thm_waiting_time_t_density_integrable
import Theorems.Thm_waiting_time_tail_decay
import Theorems.Thm_survival_mean_ibp
import Theorems.Thm_waiting_time_survival_mean
import Theorems.Thm_siegel_cdf_average_ge_mean
import Theorems.Thm_siegel_symmetrized_cdf_unimodal_from_density_sign
import Theorems.Thm_moustache_value_bound_mass
import Theorems.Thm_phi_single_turning_point
import Theorems.Thm_upstream_g_sign_strict
import Theorems.Thm_waiting_time_survival_integrable
import Theorems.Thm_harmonic_tail_gt_log
import Theorems.Thm_harmonic_tail_lt_log

set_option autoImplicit false
open scoped BigOperators
open Finset MeasureTheory Set Filter Topology

theorem solution (N m : ℕ) (h : m < N) (hm1 : 1 ≤ m) :
    (1/2 : ℝ) ≤ ∑ k ∈ Finset.Ico ((N-m-1)+1) (N+1),
      (Nat.choose N k : ℝ) * (1 - Real.exp (-(Real.log ((N:ℝ)/m) * 1))) ^ k
        * (Real.exp (-(Real.log ((N:ℝ)/m) * 1))) ^ (N - k) := by
  classical
  -- ===================================================================
  -- Local definitions (tactic `let`; refer to them by name, zeta-defeq)
  -- ===================================================================
  -- The CDF F.
  let Fcdf : ℕ → ℕ → ℝ → ℝ → ℝ := fun N mp lam s =>
    ∑ k ∈ Finset.Ico (mp+1) (N+1),
      (Nat.choose N k : ℝ) * (1 - Real.exp (-(lam * s))) ^ k * (Real.exp (-(lam * s))) ^ (N - k)
  -- The density f.
  let fdens : ℕ → ℕ → ℝ → ℝ → ℝ := fun N mp lam s =>
    (N : ℝ) * (Nat.choose (N-1) mp : ℝ) * (1 - Real.exp (-(lam * s))) ^ mp
        * (Real.exp (-(lam * s))) ^ (N - mp) * lam
  -- The waiting-time log-density derivative.
  let GlogD : ℝ → ℝ → ℝ → ℝ → ℝ := fun lam m Nn s =>
    m * (lam * Real.exp (-lam * s) / (1 - Real.exp (-lam * s))) - (Nn - m) * lam
  -- The log-density.
  let Glog : ℝ → ℝ → ℝ → ℝ → ℝ := fun lam m Nn t =>
    m * Real.log (1 - Real.exp (-lam * t)) - (Nn - m) * (lam * t)
  -- survSum
  let survSum : ℕ → ℕ → ℝ → ℝ → ℝ := fun N mp lam s =>
    ∑ k ∈ Finset.range (mp+1),
      (Nat.choose N k : ℝ) * (1 - Real.exp (-(lam * s))) ^ k * (Real.exp (-(lam * s))) ^ (N - k)
  -- ===================================================================
  -- Platform nodes bound to imported theorems (each defeq to the inlined form)
  -- ===================================================================
  have node_density : ∀ (N mp : ℕ) (lam : ℝ), mp < N → ∀ (t : ℝ),
      HasDerivAt (Fcdf N mp lam) (fdens N mp lam t) t :=
    fun N mp lam h t => Waiting.waiting_time_density N mp lam h t
  have node_F0 : ∀ (N mp : ℕ) (lam : ℝ), mp < N → Fcdf N mp lam 0 = 0 :=
    fun N mp lam h => waiting_time_cdf_at_zero N mp lam h
  have node_mass : ∀ (N mp : ℕ) (lam : ℝ), mp < N → 0 < lam →
      ∫ s in Set.Ioi (0:ℝ), fdens N mp lam s = 1 :=
    fun N mp lam h hlam => waiting_time_mass_eq_one N mp lam h hlam
  have node_fint : ∀ (N mp : ℕ) (lam : ℝ), mp < N → 0 < lam →
      MeasureTheory.IntegrableOn (fdens N mp lam) (Set.Ioi (0:ℝ)) :=
    fun N mp lam h hlam => waiting_time_density_integrable N mp lam h hlam
  have node_tfint : ∀ (N mp : ℕ) (lam : ℝ), mp < N → 0 < lam →
      MeasureTheory.IntegrableOn (fun t => t * fdens N mp lam t) (Set.Ioi (0:ℝ)) :=
    fun N mp lam h hlam => waiting_time_t_density_integrable N mp lam h hlam
  have node_decay : ∀ (N mp : ℕ) (lam : ℝ), mp < N → 0 < lam →
      Filter.Tendsto (fun t => t * (1 - Fcdf N mp lam t)) Filter.atTop (nhds 0) :=
    fun N mp lam h hlam => waiting_time_tail_decay N mp lam h hlam
  have node_ibp : ∀ (F f : ℝ → ℝ), (∀ x, HasDerivAt F (f x) x) →
      MeasureTheory.IntegrableOn (fun t => t * f t) (Set.Ioi (0:ℝ)) →
      MeasureTheory.IntegrableOn (fun t => 1 - F t) (Set.Ioi (0:ℝ)) →
      Filter.Tendsto (fun t => t * (1 - F t)) Filter.atTop (nhds 0) →
      ∫ t in Set.Ioi (0:ℝ), t * f t = ∫ t in Set.Ioi (0:ℝ), (1 - F t) :=
    fun F f hF hint_tf hint_surv hdecay => survival_mean_ibp F f hF hint_tf hint_surv hdecay
  have node_survmean : ∀ (N m : ℕ) (lam : ℝ), 0 < lam → m < N →
      ∫ t in Set.Ioi (0:ℝ), ∑ k ∈ Finset.range (m+1),
          (Nat.choose N k : ℝ) * (1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k)
        = (1 / lam) * ∑ k ∈ Finset.range (m+1), (1 / ((N - k : ℕ) : ℝ)) :=
    fun N m lam hlam hm => waiting_time_survival_mean N m lam hlam hm
  have node_lemma21 : ∀ (μ : ℝ), 0 ≤ μ → ∀ (F f : ℝ → ℝ),
      (∀ x ∈ Set.Ici (0:ℝ), HasDerivAt F (f x) x) → (∀ x ∈ Set.Ici (0:ℝ), 0 ≤ f x) →
      F 0 = 0 → (∀ b : ℝ, IntervalIntegrable f MeasureTheory.volume 0 b) →
      MeasureTheory.IntegrableOn f (Set.Ioi (0:ℝ)) →
      MeasureTheory.IntegrableOn (fun t => t * f t) (Set.Ioi (0:ℝ)) →
      (∫ t in Set.Ioi (0:ℝ), f t = 1) → (∫ t in Set.Ioi (0:ℝ), t * f t = μ) →
      μ ≤ ∫ t in (0:ℝ)..(2*μ), F t :=
    fun μ hμ F f hF hfnn hF0 hf_int_loc hf_mass htf_mass hmass hmean =>
      siegel_cdf_average_ge_mean μ hμ F f hF hfnn hF0 hf_int_loc hf_mass htf_mass hmass hmean
  have node_bridge : ∀ (F f : ℝ → ℝ) (μ c : ℝ), (∀ x, HasDerivAt F (f x) x) →
      (∀ x ∈ Set.Icc (0:ℝ) c, f x - f (2 * μ - x) ≤ 0) →
      (∀ x ∈ Set.Icc c μ, 0 ≤ f x - f (2 * μ - x)) →
      AntitoneOn (fun x => (F x + F (2 * μ - x)) / 2) (Set.Icc 0 c)
        ∧ MonotoneOn (fun x => (F x + F (2 * μ - x)) / 2) (Set.Icc c μ) :=
    fun F f μ c hF hgL hgR =>
      siegel_symmetrized_cdf_unimodal_from_density_sign F f μ c hF hgL hgR
  have node_moustache_mass : ∀ (G : ℝ → ℝ) (μ c : ℝ), 0 < μ → 0 ≤ c → c < μ →
      AntitoneOn G (Set.Icc 0 c) → MonotoneOn G (Set.Icc c μ) →
      (∀ x, G (2 * μ - x) = G x) → G 0 ≤ (1/2 : ℝ) →
      IntervalIntegrable G MeasureTheory.volume 0 (2 * μ) →
      ((1 / 2 : ℝ) ≤ (1 / (2 * μ)) * ∫ x in (0:ℝ)..(2 * μ), G x) →
      (1 / 2 : ℝ) ≤ G μ :=
    fun G μ c hμ hc0 hcμ hleft hright hsym hG0 hint havg =>
      moustache_value_bound_mass G μ c hμ hc0 hcμ hleft hright hsym hG0 hint havg
  have node_phi_turn : ∀ (lam m Nn mu : ℝ),
      0 < lam → 0 < m → m < Nn → 0 < mu → Nn < (Nn - m) * Real.exp (lam * mu) →
      ∃ a ∈ Ioo (0:ℝ) mu,
        (∀ t ∈ Ioo (0:ℝ) a,
          HasDerivAt (fun y => Glog lam m Nn y - Glog lam m Nn (2*mu - y))
            (GlogD lam m Nn t + GlogD lam m Nn (2*mu - t)) t
          ∧ 0 < GlogD lam m Nn t + GlogD lam m Nn (2*mu - t))
        ∧ (∀ t ∈ Ioo a mu,
          HasDerivAt (fun y => Glog lam m Nn y - Glog lam m Nn (2*mu - y))
            (GlogD lam m Nn t + GlogD lam m Nn (2*mu - t)) t
          ∧ GlogD lam m Nn t + GlogD lam m Nn (2*mu - t) < 0) :=
    fun lam m Nn mu hlam hm hmN hmu hmean =>
      phi_single_turning_point lam m Nn mu hlam hm hmN hmu hmean
  have node_upstream_g_sign_strict : ∀ (f φ' : ℝ → ℝ) (μ a t₀ : ℝ), 0 < μ → a ∈ Ioo (0:ℝ) μ →
      (∀ x ∈ Ioo (0:ℝ) (2*μ), 0 < f x) →
      (∀ x ∈ Ioo (0:ℝ) μ,
          HasDerivAt (fun y => Real.log (f y) - Real.log (f (2*μ - y))) (φ' x) x) →
      (∀ x ∈ Ioo (0:ℝ) a, 0 < φ' x) →
      (∀ x ∈ Ioo a μ, φ' x < 0) →
      ContinuousOn (fun y => Real.log (f y) - Real.log (f (2*μ - y))) (Ioc 0 μ) →
      t₀ ∈ Ioo (0:ℝ) a → Real.log (f t₀) - Real.log (f (2*μ - t₀)) < 0 →
      f 0 - f (2*μ) ≤ 0 →
      ∃ c ∈ Ioo (0:ℝ) μ,
        (∀ x ∈ Icc (0:ℝ) c, f x - f (2*μ - x) ≤ 0)
          ∧ (∀ x ∈ Icc c μ, 0 ≤ f x - f (2*μ - x)) :=
    fun f φ' μ a t₀ hμ ha hfpos hφd hφpos hφneg hφcont ht₀ hφt₀ hg0 =>
      upstream_g_sign_strict f φ' μ a t₀ hμ ha hfpos hφd hφpos hφneg hφcont ht₀ hφt₀ hg0
  have node_survSum_int : ∀ (N mp : ℕ) (lam : ℝ), mp < N → 0 < lam →
      MeasureTheory.IntegrableOn
        (fun t => ∑ k ∈ Finset.range (mp+1),
          (Nat.choose N k : ℝ) * (1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k))
        (Set.Ioi (0:ℝ)) :=
    fun N mp lam h hlam => waiting_time_survival_integrable N mp lam h hlam
  have node_harm_gt : ∀ (a b : ℕ), a < b →
      Real.log (((b:ℝ)+1) / (a+1)) < (∑ j ∈ Finset.Ico a b, (1 : ℝ) / (j + 1)) :=
    fun a b hab => harmonic_tail_gt_log a b hab
  have node_harm_lt : ∀ (a b : ℕ), 1 ≤ a → a < b →
      (∑ j ∈ Finset.Ico a b, (1 : ℝ) / (j + 1)) < Real.log ((b:ℝ) / a) :=
    fun a b ha hab => harmonic_tail_lt_log a b ha hab
  -- ===================================================================
  -- Reused helper lemmas
  -- ===================================================================
  have fdens_nonneg : ∀ (N mp : ℕ) (lam : ℝ), 0 < lam → ∀ (s : ℝ), 0 < s →
      0 ≤ fdens N mp lam s := by
    intro N mp lam hlam s hs
    show 0 ≤ (N : ℝ) * (Nat.choose (N-1) mp : ℝ) * (1 - Real.exp (-(lam * s))) ^ mp
        * (Real.exp (-(lam * s))) ^ (N - mp) * lam
    have he : (0:ℝ) < Real.exp (-(lam * s)) := Real.exp_pos _
    have he1 : Real.exp (-(lam * s)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have : 0 < lam * s := mul_pos hlam hs
      linarith
    have h1 : (0:ℝ) ≤ 1 - Real.exp (-(lam * s)) := by linarith
    positivity
  have Fcdf_eq_intervalIntegral : ∀ (N mp : ℕ) (lam : ℝ), mp < N → ∀ (s : ℝ),
      Fcdf N mp lam s = ∫ x in (0:ℝ)..s, fdens N mp lam x := by
    intro N mp lam h s
    have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) s, HasDerivAt (Fcdf N mp lam) (fdens N mp lam x) x := by
      intro x _; exact node_density N mp lam h x
    have hcont : IntervalIntegrable (fdens N mp lam) volume 0 s := by
      apply ContinuousOn.intervalIntegrable
      have : Continuous (fdens N mp lam) := by
        show Continuous (fun s => (N : ℝ) * (Nat.choose (N-1) mp : ℝ)
          * (1 - Real.exp (-(lam * s))) ^ mp
          * (Real.exp (-(lam * s))) ^ (N - mp) * lam)
        fun_prop
      exact this.continuousOn
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont, node_F0 N mp lam h, sub_zero]
  have Fcdf_le_one : ∀ (N mp : ℕ) (lam : ℝ), mp < N → 0 < lam → ∀ (s : ℝ), 0 ≤ s →
      Fcdf N mp lam s ≤ 1 := by
    intro N mp lam h hlam s hs
    rw [Fcdf_eq_intervalIntegral N mp lam h]
    rw [intervalIntegral.integral_of_le hs]
    have hmono : (∫ x in Set.Ioc (0:ℝ) s, fdens N mp lam x)
        ≤ ∫ x in Set.Ioi (0:ℝ), fdens N mp lam x := by
      apply setIntegral_mono_set (node_fint N mp lam h hlam)
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        exact fdens_nonneg N mp lam hlam x hx
      · filter_upwards with x
        intro hx
        exact hx.1
    rw [node_mass N mp lam h hlam] at hmono
    exact hmono
  have Fcdf_nonneg : ∀ (N mp : ℕ) (lam : ℝ), mp < N → 0 < lam → ∀ (s : ℝ), 0 ≤ s →
      0 ≤ Fcdf N mp lam s := by
    intro N mp lam h hlam s hs
    rw [Fcdf_eq_intervalIntegral N mp lam h]
    rw [intervalIntegral.integral_of_le hs]
    apply setIntegral_nonneg measurableSet_Ioc
    intro x hx
    exact fdens_nonneg N mp lam hlam x hx.1
  have Fcdf_mono_on : ∀ (N mp : ℕ) (lam : ℝ), 0 < lam → mp < N → ∀ (a b : ℝ), 0 < a →
      MonotoneOn (Fcdf N mp lam) (Icc a b) := by
    intro N mp lam hlam h a b ha
    have hcont : Continuous (Fcdf N mp lam) :=
      continuous_iff_continuousAt.mpr (fun x => (node_density N mp lam h x).continuousAt)
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b) hcont.continuousOn
      (fun x hx => (node_density N mp lam h x).differentiableAt.differentiableWithinAt)
    intro x hx
    rw [interior_Icc] at hx
    rw [(node_density N mp lam h x).deriv]
    exact fdens_nonneg N mp lam hlam x (lt_trans ha hx.1)
  have full_sum_eq_one : ∀ (N : ℕ) (e : ℝ),
      (∑ k ∈ Finset.range (N+1),
          (Nat.choose N k : ℝ) * (1 - e) ^ k * e ^ (N - k)) = 1 := by
    intro N e
    have hb : ((1 - e) + e) ^ N = ∑ k ∈ Finset.range (N+1),
        (1 - e) ^ k * e ^ (N - k) * (Nat.choose N k : ℝ) := add_pow (1-e) e N
    have hcongr : (∑ k ∈ Finset.range (N+1), (Nat.choose N k : ℝ) * (1 - e) ^ k * e ^ (N - k))
        = ∑ k ∈ Finset.range (N+1), (1 - e) ^ k * e ^ (N - k) * (Nat.choose N k : ℝ) := by
      apply Finset.sum_congr rfl; intro k _; ring
    rw [hcongr, ← hb]
    norm_num
  have one_sub_Fcdf : ∀ (N mp : ℕ) (lam : ℝ), mp ≤ N → ∀ (s : ℝ),
      1 - Fcdf N mp lam s = survSum N mp lam s := by
    intro N mp lam h s
    show 1 - (∑ k ∈ Finset.Ico (mp+1) (N+1),
        (Nat.choose N k : ℝ) * (1 - Real.exp (-(lam * s))) ^ k * (Real.exp (-(lam * s))) ^ (N - k))
      = ∑ k ∈ Finset.range (mp+1),
        (Nat.choose N k : ℝ) * (1 - Real.exp (-(lam * s))) ^ k * (Real.exp (-(lam * s))) ^ (N - k)
    set e := Real.exp (-(lam * s)) with he
    have hfull := full_sum_eq_one N e
    have hsplit : Finset.range (N+1) = Finset.range (mp+1) ∪ Finset.Ico (mp+1) (N+1) := by
      rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
        Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)]
    have hdisj : Disjoint (Finset.range (mp+1)) (Finset.Ico (mp+1) (N+1)) := by
      rw [Finset.range_eq_Ico]; apply Finset.Ico_disjoint_Ico_consecutive
    rw [hsplit, Finset.sum_union hdisj] at hfull
    linarith [hfull]
  -- ===================================================================
  -- e^{-λ} = m/N when λ = log(N/m)
  -- ===================================================================
  have exp_neg_lam : ∀ (N m : ℕ), m < N → 1 ≤ m →
      Real.exp (-(Real.log ((N:ℝ)/m) * 1)) = (m:ℝ)/N := by
    intro N m h hm1
    have hmpos : (0:ℝ) < m := by exact_mod_cast hm1
    have hNnat : (0:ℕ) < N := by omega
    have hNpos : (0:ℝ) < N := by exact_mod_cast hNnat
    have hratio : (0:ℝ) < (N:ℝ)/m := by positivity
    rw [mul_one, ← Real.log_inv, Real.exp_log (by positivity)]
    rw [inv_div]
  have lam_pos : ∀ (N m : ℕ), m < N → 1 ≤ m → 0 < Real.log ((N:ℝ)/m) := by
    intro N m h hm1
    have hmpos : (0:ℝ) < m := by exact_mod_cast hm1
    have hNnat : (0:ℕ) < N := by omega
    have hNpos : (0:ℝ) < N := by exact_mod_cast hNnat
    rw [Real.log_pos_iff (by positivity)]
    rw [lt_div_iff₀ hmpos]
    have : (m:ℝ) < N := by exact_mod_cast h
    linarith
  -- ===================================================================
  -- φ-identity:  log fdens = Glog + log K  (for s>0)
  -- ===================================================================
  have log_fdens_eq : ∀ (N mp : ℕ) (lam s : ℝ), mp < N → 0 < lam → 0 < s →
      Real.log (fdens N mp lam s)
        = Glog lam (mp:ℝ) (N:ℝ) s
          + Real.log ((N:ℝ) * (Nat.choose (N-1) mp : ℝ) * lam) := by
    intro N mp lam s hmp hlam hs
    show Real.log ((N : ℝ) * (Nat.choose (N-1) mp : ℝ) * (1 - Real.exp (-(lam * s))) ^ mp
        * (Real.exp (-(lam * s))) ^ (N - mp) * lam)
      = ((mp:ℝ) * Real.log (1 - Real.exp (-lam * s)) - ((N:ℝ) - (mp:ℝ)) * (lam * s))
        + Real.log ((N:ℝ) * (Nat.choose (N-1) mp : ℝ) * lam)
    have he : (0:ℝ) < Real.exp (-(lam * s)) := Real.exp_pos _
    have he1 : Real.exp (-(lam * s)) < 1 := by
      rw [Real.exp_lt_one_iff]; have : 0 < lam * s := mul_pos hlam hs; linarith
    have hq : (0:ℝ) < 1 - Real.exp (-(lam * s)) := by linarith
    have hNnat : (0:ℕ) < N := by omega
    have hNpos : (0:ℝ) < N := by exact_mod_cast hNnat
    have hchoose : (0:ℝ) < (Nat.choose (N-1) mp : ℝ) := by
      have : 0 < Nat.choose (N-1) mp := Nat.choose_pos (by omega)
      exact_mod_cast this
    rw [Real.log_mul (by positivity) (ne_of_gt hlam)]
    rw [Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_pow, Real.log_pow]
    have hexparg : Real.exp (-(lam * s)) = Real.exp (-lam * s) := by rw [neg_mul]
    rw [Real.log_exp]
    have hcast : ((N - mp : ℕ) : ℝ) = (N:ℝ) - (mp:ℝ) := by rw [Nat.cast_sub (le_of_lt hmp)]
    rw [hcast]
    have harg : (1 - Real.exp (-(lam * s))) = (1 - Real.exp (-lam * s)) := by rw [hexparg]
    rw [harg]
    rw [Real.log_mul (by positivity) (ne_of_gt hlam)]
    ring
  have fdens_pos : ∀ (N mp : ℕ) (lam : ℝ), mp < N → 0 < lam → ∀ (s : ℝ), 0 < s →
      0 < fdens N mp lam s := by
    intro N mp lam hmp hlam s hs
    show 0 < (N : ℝ) * (Nat.choose (N-1) mp : ℝ) * (1 - Real.exp (-(lam * s))) ^ mp
        * (Real.exp (-(lam * s))) ^ (N - mp) * lam
    have he : (0:ℝ) < Real.exp (-(lam * s)) := Real.exp_pos _
    have he1 : Real.exp (-(lam * s)) < 1 := by
      rw [Real.exp_lt_one_iff]; have : 0 < lam * s := mul_pos hlam hs; linarith
    have hq : (0:ℝ) < 1 - Real.exp (-(lam * s)) := by linarith
    have hNnat : (0:ℕ) < N := by omega
    have hNpos : (0:ℝ) < N := by exact_mod_cast hNnat
    have hchoose : (0:ℝ) < (Nat.choose (N-1) mp : ℝ) := by
      have : 0 < Nat.choose (N-1) mp := Nat.choose_pos (by omega)
      exact_mod_cast this
    positivity
  have fdens_zero_at_zero : ∀ (N mp : ℕ) (lam : ℝ), 1 ≤ mp → fdens N mp lam 0 = 0 := by
    intro N mp lam hmp1
    show (N : ℝ) * (Nat.choose (N-1) mp : ℝ) * (1 - Real.exp (-(lam * 0))) ^ mp
        * (Real.exp (-(lam * 0))) ^ (N - mp) * lam = 0
    have h0 : (1 - Real.exp (-(lam * 0))) ^ mp = 0 := by
      have : (1 - Real.exp (-(lam * 0))) = 0 := by simp [Real.exp_zero]
      rw [this, zero_pow (by omega)]
    rw [h0]; ring
  -- ===================================================================
  -- CASE mp = 0 (m = N-1):  Fcdf N 0 lam 1 = 1 - (m/N)^N ≥ 1/2
  -- ===================================================================
  have Fcdf_mp0_at_one : ∀ (N : ℕ) (lam : ℝ), 1 ≤ N →
      Fcdf N 0 lam 1 = 1 - (Real.exp (-(lam * 1))) ^ N := by
    intro N lam hN
    have h0 : (0 : ℕ) < N := hN
    have hone := one_sub_Fcdf N 0 lam (by omega) 1
    have hsurv : survSum N 0 lam 1 = (Real.exp (-(lam * 1))) ^ N := by
      show (∑ k ∈ Finset.range (0+1),
          (Nat.choose N k : ℝ) * (1 - Real.exp (-(lam * 1))) ^ k
            * (Real.exp (-(lam * 1))) ^ (N - k)) = (Real.exp (-(lam * 1))) ^ N
      rw [Finset.sum_range_one]
      simp
    rw [hsurv] at hone
    linarith [hone]
  have edge_half : ∀ (N m : ℕ), m < N → 1 ≤ m → m = N - 1 →
      (1/2 : ℝ) ≤ Fcdf N (N-m-1) (Real.log ((N:ℝ)/m)) 1 := by
    intro N m h hm1 hmp0
    have hN1 : 1 ≤ N := le_of_lt (lt_of_le_of_lt hm1 h)
    have hmp : N - m - 1 = 0 := by omega
    rw [hmp]
    set lam := Real.log ((N:ℝ)/m) with hlam_def
    rw [Fcdf_mp0_at_one N lam hN1]
    rw [exp_neg_lam N m h hm1]
    have hmN : (m:ℝ) = (N:ℝ) - 1 := by
      have : m = N - 1 := hmp0
      rw [this]; push_cast [Nat.cast_sub hN1]; ring
    rw [hmN]
    have hNpos : (0:ℝ) < N := by exact_mod_cast hN1
    have hN1R : (1:ℝ) ≤ N := by exact_mod_cast hN1
    have hbase : ((N:ℝ)-1)/N = (-(1/N)) + 1 := by field_simp; ring
    have hle : ((N:ℝ)-1)/N ≤ Real.exp (-(1/N)) := by
      rw [hbase]; exact Real.add_one_le_exp _
    have hnn : (0:ℝ) ≤ ((N:ℝ)-1)/N := by apply div_nonneg _ hNpos.le; linarith
    have hpow : (((N:ℝ)-1)/N)^N ≤ (Real.exp (-(1/N)))^N := pow_le_pow_left₀ hnn hle N
    have hexp : (Real.exp (-(1/N)))^N = Real.exp (-1) := by
      rw [← Real.exp_nat_mul]; congr 1; field_simp
    rw [hexp] at hpow
    have h2 : Real.exp (-1) < (1/2 : ℝ) := by
      have hh := Real.exp_one_gt_d9
      rw [show (-1 : ℝ) = -(1:ℝ) from rfl, Real.exp_neg]
      rw [inv_lt_iff_one_lt_mul₀ (by positivity)]
      nlinarith [hh]
    linarith
  -- ===================================================================
  -- Reindex
  -- ===================================================================
  have reindex_harm : ∀ (N m : ℕ), m < N → 1 ≤ m →
      (∑ k ∈ Finset.range ((N-m-1)+1), (1 / ((N - k : ℕ) : ℝ)))
        = ∑ j ∈ Finset.Ico m N, (1 / ((j:ℝ) + 1)) := by
    intro N m h hm1
    apply Finset.sum_nbij' (fun k => N - 1 - k) (fun j => N - 1 - j)
    · intro k hk; rw [Finset.mem_range] at hk; rw [Finset.mem_Ico]; omega
    · intro j hj; rw [Finset.mem_Ico] at hj; rw [Finset.mem_range]; omega
    · intro k hk; rw [Finset.mem_range] at hk; omega
    · intro j hj; rw [Finset.mem_Ico] at hj; omega
    · intro k hk
      rw [Finset.mem_range] at hk
      have : N - k = (N - 1 - k) + 1 := by omega
      rw [this]
      push_cast [Nat.cast_sub (by omega : N - 1 - k ≤ N - 1 - k)]
      norm_num
  -- ===================================================================
  -- Glog has derivative GlogD; plus the difference deriv
  -- ===================================================================
  have Glog_hasDeriv : ∀ (lam m Nn : ℝ) (s : ℝ), 0 < s → 0 < lam →
      HasDerivAt (Glog lam m Nn) (GlogD lam m Nn s) s := by
    intro lam m Nn s hs hlam
    show HasDerivAt (fun t => m * Real.log (1 - Real.exp (-lam * t)) - (Nn - m) * (lam * t))
      (m * (lam * Real.exp (-lam * s) / (1 - Real.exp (-lam * s))) - (Nn - m) * lam) s
    have hexp : HasDerivAt (fun y => Real.exp (-lam * y)) (-lam * Real.exp (-lam * s)) s := by
      have := (((hasDerivAt_id s).const_mul (-lam)).exp); simpa [mul_comm] using this
    have hone : HasDerivAt (fun y => 1 - Real.exp (-lam * y)) (lam * Real.exp (-lam * s)) s := by
      have := hexp.const_sub 1; simpa using this
    have hposne : (1 : ℝ) - Real.exp (-lam * s) ≠ 0 := by
      have : Real.exp (-lam * s) < 1 := by rw [Real.exp_lt_one_iff]; nlinarith
      linarith
    have hlog : HasDerivAt (fun y => Real.log (1 - Real.exp (-lam * y)))
        ((lam * Real.exp (-lam * s)) / (1 - Real.exp (-lam * s))) s := hone.log hposne
    have hlin : HasDerivAt (fun y => (Nn - m) * (lam * y)) ((Nn - m) * lam) s := by
      have h2 := ((hasDerivAt_id s).const_mul lam).const_mul (Nn - m); simpa [mul_assoc] using h2
    have hd := (hlog.const_mul m).sub hlin
    exact hd
  have glog_diff_hasDeriv : ∀ (lam m Nn mu : ℝ) (t : ℝ), 0 < t → t < mu → 0 < lam →
      HasDerivAt (fun y => Glog lam m Nn y - Glog lam m Nn (2*mu - y))
        (GlogD lam m Nn t + GlogD lam m Nn (2*mu - t)) t := by
    intro lam m Nn mu t ht0 htmu hlam
    have hpt : (0:ℝ) < 2*mu - t := by linarith
    have h1 := Glog_hasDeriv lam m Nn t ht0 hlam
    have hinner : HasDerivAt (fun y => 2*mu - y) (-1 : ℝ) t := by
      have := (hasDerivAt_id t).const_sub (2*mu); simpa using this
    have h2 := Glog_hasDeriv lam m Nn (2*mu - t) hpt hlam
    have hcomp : HasDerivAt (fun y => Glog lam m Nn (2*mu - y)) (GlogD lam m Nn (2*mu - t) * (-1)) t :=
      h2.comp t hinner
    have hd := h1.sub hcomp
    exact hd.congr_deriv (by ring)
  -- ===================================================================
  -- MAIN CASE  1 ≤ m ≤ N-2  (so mp = N-m-1 ≥ 1)
  -- ===================================================================
  have main_half : ∀ (N m : ℕ), m < N → 1 ≤ m → m + 1 < N →
      (1/2 : ℝ) ≤ Fcdf N (N-m-1) (Real.log ((N:ℝ)/m)) 1 := by
    intro N m h hm1 hmN2
    set mp := N - m - 1 with hmp_def
    set lam := Real.log ((N:ℝ)/m) with hlam_def
    have hmp1 : 1 ≤ mp := by omega
    have hmpN : mp < N := by omega
    have hlam : 0 < lam := lam_pos N m h hm1
    set μ : ℝ := (1 / lam) * ∑ k ∈ Finset.range (mp+1), (1 / ((N - k : ℕ) : ℝ)) with hμ_def
    have hsum_pos : 0 < ∑ k ∈ Finset.range (mp+1), (1 / ((N - k : ℕ) : ℝ)) := by
      apply Finset.sum_pos
      · intro k hk
        rw [Finset.mem_range] at hk
        have : (0:ℕ) < N - k := by omega
        have : (0:ℝ) < ((N - k : ℕ):ℝ) := by exact_mod_cast this
        positivity
      · exact ⟨0, Finset.mem_range.mpr (by omega)⟩
    have hμpos : 0 < μ := by rw [hμ_def]; positivity
    have hlamμ : lam * μ = ∑ j ∈ Finset.Ico m N, (1 / ((j:ℝ) + 1)) := by
      rw [hμ_def]
      rw [← mul_assoc, mul_one_div, div_self (ne_of_gt hlam), one_mul]
      exact reindex_harm N m h hm1
    have hsurv_eq : ∀ t, (1 - Fcdf N mp lam t) = survSum N mp lam t :=
      fun t => one_sub_Fcdf N mp lam (le_of_lt hmpN) t
    have hsurvSum_int : MeasureTheory.IntegrableOn (survSum N mp lam) (Set.Ioi (0:ℝ)) :=
      node_survSum_int N mp lam hmpN hlam
    have hsurv_int : MeasureTheory.IntegrableOn (fun t => 1 - Fcdf N mp lam t) (Set.Ioi (0:ℝ)) := by
      apply hsurvSum_int.congr_fun _ measurableSet_Ioi
      intro t _; exact (hsurv_eq t).symm
    have hint_surv_val : (∫ t in Set.Ioi (0:ℝ), (1 - Fcdf N mp lam t)) = μ := by
      have hcong : (∫ t in Set.Ioi (0:ℝ), (1 - Fcdf N mp lam t))
          = ∫ t in Set.Ioi (0:ℝ), survSum N mp lam t := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
        intro t _; exact hsurv_eq t
      rw [hcong]
      show (∫ t in Set.Ioi (0:ℝ), ∑ k ∈ Finset.range (mp+1),
          (Nat.choose N k : ℝ) * (1 - Real.exp (-(lam * t))) ^ k
            * (Real.exp (-(lam * t))) ^ (N - k)) = μ
      rw [node_survmean N mp lam hlam hmpN]
    have hmean : (∫ t in Set.Ioi (0:ℝ), t * fdens N mp lam t) = μ := by
      rw [node_ibp (Fcdf N mp lam) (fdens N mp lam)
          (fun x => node_density N mp lam hmpN x)
          (node_tfint N mp lam hmpN hlam) hsurv_int (node_decay N mp lam hmpN hlam)]
      exact hint_surv_val
    have hcont_fdens : Continuous (fdens N mp lam) := by
      show Continuous (fun s => (N : ℝ) * (Nat.choose (N-1) mp : ℝ)
        * (1 - Real.exp (-(lam * s))) ^ mp
        * (Real.exp (-(lam * s))) ^ (N - mp) * lam)
      fun_prop
    have hlemma21 : μ ≤ ∫ t in (0:ℝ)..(2*μ), Fcdf N mp lam t := by
      apply node_lemma21 μ (le_of_lt hμpos) (Fcdf N mp lam) (fdens N mp lam)
        (fun x _ => node_density N mp lam hmpN x)
        _ (node_F0 N mp lam hmpN)
        (fun b => (hcont_fdens.intervalIntegrable 0 b))
        (node_fint N mp lam hmpN hlam) (node_tfint N mp lam hmpN hlam)
        (node_mass N mp lam hmpN hlam) hmean
      intro x hx
      rw [Set.mem_Ici] at hx
      rcases eq_or_lt_of_le hx with hx0 | hx0
      · rw [← hx0]; rw [fdens_zero_at_zero N mp lam hmp1]
      · exact le_of_lt (fdens_pos N mp lam hmpN hlam x hx0)
    set Fhat : ℝ → ℝ := fun x => (Fcdf N mp lam x + Fcdf N mp lam (2*μ - x)) / 2 with hFhat_def
    have hFhatint : (∫ x in (0:ℝ)..(2*μ), Fhat x) = ∫ x in (0:ℝ)..(2*μ), Fcdf N mp lam x := by
      have hcont_F : Continuous (Fcdf N mp lam) :=
        continuous_iff_continuousAt.mpr (fun x => (node_density N mp lam hmpN x).continuousAt)
      have hI1 : IntervalIntegrable (Fcdf N mp lam) volume 0 (2*μ) :=
        hcont_F.intervalIntegrable 0 (2*μ)
      have hI2 : IntervalIntegrable (fun x => Fcdf N mp lam (2*μ - x)) volume 0 (2*μ) := by
        apply Continuous.intervalIntegrable; exact hcont_F.comp (by fun_prop)
      have hrefl : (∫ x in (0:ℝ)..(2*μ), Fcdf N mp lam (2*μ - x))
          = ∫ x in (0:ℝ)..(2*μ), Fcdf N mp lam x := by
        rw [intervalIntegral.integral_comp_sub_left (Fcdf N mp lam) (2*μ)]
        rw [show (2*μ - 0) = 2*μ by ring, show (2*μ - 2*μ) = (0:ℝ) by ring]
      calc (∫ x in (0:ℝ)..(2*μ), Fhat x)
          = ∫ x in (0:ℝ)..(2*μ), (Fcdf N mp lam x + Fcdf N mp lam (2*μ - x)) / 2 := rfl
        _ = (∫ x in (0:ℝ)..(2*μ), Fcdf N mp lam x + Fcdf N mp lam (2*μ - x)) / 2 := by
            rw [intervalIntegral.integral_div]
        _ = ((∫ x in (0:ℝ)..(2*μ), Fcdf N mp lam x) + ∫ x in (0:ℝ)..(2*μ), Fcdf N mp lam (2*μ - x)) / 2 := by
            rw [intervalIntegral.integral_add hI1 hI2]
        _ = ((∫ x in (0:ℝ)..(2*μ), Fcdf N mp lam x) + ∫ x in (0:ℝ)..(2*μ), Fcdf N mp lam x) / 2 := by
            rw [hrefl]
        _ = ∫ x in (0:ℝ)..(2*μ), Fcdf N mp lam x := by ring
    have h2μpos : (0:ℝ) < 2*μ := by positivity
    have havg : (1 / 2 : ℝ) ≤ (1 / (2 * μ)) * ∫ x in (0:ℝ)..(2 * μ), Fhat x := by
      rw [hFhatint]
      have hI : (1/(2*μ)) * (∫ x in (0:ℝ)..(2*μ), Fcdf N mp lam x)
          = (∫ x in (0:ℝ)..(2*μ), Fcdf N mp lam x) / (2*μ) := by ring
      rw [hI, le_div_iff₀ h2μpos]
      nlinarith [hlemma21]
    have hcast_mp : (N:ℝ) - (mp:ℝ) = (m:ℝ) + 1 := by
      have hmpnat : mp = N - m - 1 := hmp_def
      have : ((mp:ℕ):ℝ) = (N:ℝ) - (m:ℝ) - 1 := by
        rw [hmpnat]
        rw [Nat.cast_sub (by omega : 1 ≤ N - m), Nat.cast_sub (by omega : m ≤ N)]
        norm_num
      rw [this]; ring
    have hmpR_pos : (0:ℝ) < (mp:ℝ) := by exact_mod_cast hmp1
    have hmpR_lt : (mp:ℝ) < (N:ℝ) := by exact_mod_cast hmpN
    have hmpos_real : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm1
    have hNnat0 : (0:ℕ) < N := by omega
    have hNpos_real : (0:ℝ) < (N:ℝ) := by exact_mod_cast hNnat0
    have hmean_turn : (N:ℝ) < ((N:ℝ) - (mp:ℝ)) * Real.exp (lam * μ) := by
      rw [hcast_mp]
      have hharm := node_harm_gt m N h
      rw [← hlamμ] at hharm
      have hexp_gt : ((N:ℝ)+1)/((m:ℝ)+1) < Real.exp (lam * μ) := by
        have := Real.exp_lt_exp.mpr hharm
        rwa [Real.exp_log (by positivity)] at this
      have hm1R : (0:ℝ) < (m:ℝ) + 1 := by positivity
      have hstep : (N:ℝ)+1 < ((m:ℝ)+1) * Real.exp (lam * μ) := by
        rw [div_lt_iff₀ hm1R] at hexp_gt; linarith [hexp_gt]
      linarith [hstep]
    set φlog : ℝ → ℝ := fun y => Real.log (fdens N mp lam y) - Real.log (fdens N mp lam (2*μ - y)) with hφlog_def
    set φGlog : ℝ → ℝ := fun y => Glog lam (mp:ℝ) (N:ℝ) y - Glog lam (mp:ℝ) (N:ℝ) (2*μ - y) with hφGlog_def
    set φ' : ℝ → ℝ := fun t => GlogD lam (mp:ℝ) (N:ℝ) t + GlogD lam (mp:ℝ) (N:ℝ) (2*μ - t) with hφ'_def
    have hidentity : Set.EqOn φlog φGlog (Ioo (0:ℝ) (2*μ)) := by
      intro y hy
      rw [Set.mem_Ioo] at hy
      have hy2 : 0 < 2*μ - y := by linarith [hy.2]
      rw [hφlog_def, hφGlog_def]
      simp only
      rw [log_fdens_eq N mp lam y hmpN hlam hy.1, log_fdens_eq N mp lam (2*μ - y) hmpN hlam hy2]
      ring
    obtain ⟨a, ha_mem, ha_pos_block, ha_neg_block⟩ :=
      node_phi_turn lam (mp:ℝ) (N:ℝ) μ hlam hmpR_pos hmpR_lt hμpos hmean_turn
    have hφd : ∀ x ∈ Ioo (0:ℝ) μ, HasDerivAt φlog (φ' x) x := by
      intro x hx
      have hglogderiv : HasDerivAt φGlog (φ' x) x := by
        rcases lt_trichotomy x a with hxa | hxa | hxa
        · exact (ha_pos_block x ⟨hx.1, hxa⟩).1
        · subst hxa
          exact glog_diff_hasDeriv lam (mp:ℝ) (N:ℝ) μ x hx.1 hx.2 hlam
        · exact (ha_neg_block x ⟨hxa, hx.2⟩).1
      apply hglogderiv.congr_of_eventuallyEq
      have hxmem : x ∈ Ioo (0:ℝ) (2*μ) := ⟨hx.1, by linarith [hx.2]⟩
      filter_upwards [isOpen_Ioo.mem_nhds hxmem] with y hy using (hidentity hy)
    have hfpos : ∀ x ∈ Ioo (0:ℝ) (2*μ), 0 < fdens N mp lam x := by
      intro x hx; exact fdens_pos N mp lam hmpN hlam x hx.1
    have hφpos : ∀ x ∈ Ioo (0:ℝ) a, 0 < φ' x := fun x hx => (ha_pos_block x hx).2
    have hφneg : ∀ x ∈ Ioo a μ, φ' x < 0 := fun x hx => (ha_neg_block x hx).2
    have hφcont : ContinuousOn φlog (Ioc 0 μ) := by
      rw [hφlog_def]
      apply ContinuousOn.sub
      · apply ContinuousOn.log
        · exact hcont_fdens.continuousOn
        · intro x hx; exact ne_of_gt (fdens_pos N mp lam hmpN hlam x hx.1)
      · apply ContinuousOn.log
        · have : Continuous (fun x => fdens N mp lam (2*μ - x)) := hcont_fdens.comp (by fun_prop)
          exact this.continuousOn
        · intro x hx
          rw [Set.mem_Ioc] at hx
          exact ne_of_gt (fdens_pos N mp lam hmpN hlam (2*μ - x) (by linarith [hx.2]))
    have hg0 : fdens N mp lam 0 - fdens N mp lam (2*μ) ≤ 0 := by
      rw [fdens_zero_at_zero N mp lam hmp1]
      have : 0 ≤ fdens N mp lam (2*μ) := le_of_lt (fdens_pos N mp lam hmpN hlam (2*μ) (by linarith))
      linarith
    obtain ⟨a0, aμ⟩ := ha_mem
    set v : ℝ := fdens N mp lam (2*μ) with hv_def
    have hvpos : 0 < v := fdens_pos N mp lam hmpN hlam (2*μ) (by linarith)
    have htend0 : Filter.Tendsto (fdens N mp lam) (𝓝[>] (0:ℝ)) (𝓝 (fdens N mp lam 0)) :=
      (hcont_fdens.continuousAt (x := (0:ℝ))).mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
    rw [fdens_zero_at_zero N mp lam hmp1] at htend0
    have htendR : Filter.Tendsto (fun t => fdens N mp lam (2*μ - t)) (𝓝[>] (0:ℝ)) (𝓝 v) := by
      have hc : Continuous (fun t => fdens N mp lam (2*μ - t)) := hcont_fdens.comp (by fun_prop)
      have hcat := hc.continuousAt (x := (0:ℝ))
      have htend : Filter.Tendsto (fun t => fdens N mp lam (2*μ - t)) (𝓝 (0:ℝ)) (𝓝 (fdens N mp lam (2*μ - 0))) := hcat
      have := htend.mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
      simpa [hv_def] using this
    have hev_lt : ∀ᶠ t in 𝓝[>] (0:ℝ), fdens N mp lam t < fdens N mp lam (2*μ - t) :=
      htend0.eventually_lt htendR (by linarith)
    have hev_lt_a : ∀ᶠ t in 𝓝[>] (0:ℝ), t < a := by
      apply eventually_nhdsWithin_of_eventually_nhds
      exact eventually_lt_nhds a0
    have hself : ∀ᶠ t in 𝓝[>] (0:ℝ), (0:ℝ) < t := by
      have : Ioi (0:ℝ) ∈ 𝓝[>] (0:ℝ) := self_mem_nhdsWithin
      filter_upwards [this] with t ht using ht
    obtain ⟨t₀, ⟨⟨ht₀lt, ht₀a⟩, ht₀pos'⟩⟩ :=
      ((hev_lt.and hev_lt_a).and hself).exists
    have ht₀_mem : t₀ ∈ Ioo (0:ℝ) a := ⟨ht₀pos', ht₀a⟩
    have ht₀μ : t₀ < μ := lt_trans ht₀a aμ
    have hφt₀ : Real.log (fdens N mp lam t₀) - Real.log (fdens N mp lam (2*μ - t₀)) < 0 := by
      have h1 : 0 < fdens N mp lam t₀ := fdens_pos N mp lam hmpN hlam t₀ ht₀pos'
      have h2 : 0 < fdens N mp lam (2*μ - t₀) := fdens_pos N mp lam hmpN hlam (2*μ - t₀) (by linarith)
      have hlog := Real.log_lt_log h1 ht₀lt
      linarith [hlog]
    obtain ⟨c, hc_mem, hgL, hgR⟩ :=
      node_upstream_g_sign_strict (fdens N mp lam) φ' μ a t₀ hμpos ⟨a0, aμ⟩
        hfpos hφd hφpos hφneg hφcont ht₀_mem hφt₀ hg0
    obtain ⟨hc0, hcμ⟩ := hc_mem
    obtain ⟨hAnti, hMono⟩ :=
      node_bridge (Fcdf N mp lam) (fdens N mp lam) μ c
        (fun x => node_density N mp lam hmpN x) hgL hgR
    have hsym : ∀ x, Fhat (2 * μ - x) = Fhat x := by
      intro x
      rw [hFhat_def]; simp only
      rw [show 2*μ - (2*μ - x) = x by ring]; ring
    have hFhatint_int : IntervalIntegrable Fhat volume 0 (2*μ) := by
      have hcont_F : Continuous (Fcdf N mp lam) :=
        continuous_iff_continuousAt.mpr (fun x => (node_density N mp lam hmpN x).continuousAt)
      have : Continuous Fhat := by
        rw [hFhat_def]
        exact (hcont_F.add (hcont_F.comp (by fun_prop))).div_const 2
      exact this.intervalIntegrable 0 (2*μ)
    have hFhat0 : Fhat 0 ≤ (1/2 : ℝ) := by
      rw [hFhat_def]; simp only
      rw [show 2*μ - 0 = 2*μ by ring, node_F0 N mp lam hmpN, zero_add]
      have : Fcdf N mp lam (2*μ) ≤ 1 := Fcdf_le_one N mp lam hmpN hlam (2*μ) (by linarith)
      linarith
    have hFhatμ : (1/2 : ℝ) ≤ Fhat μ :=
      node_moustache_mass Fhat μ c hμpos hc0.le hcμ hAnti hMono hsym hFhat0 hFhatint_int havg
    have hFhatμ_eq : Fhat μ = Fcdf N mp lam μ := by
      rw [hFhat_def]; simp only
      rw [show 2*μ - μ = μ by ring]; ring
    rw [hFhatμ_eq] at hFhatμ
    have hμlt1 : μ < 1 := by
      have hharm := node_harm_lt m N hm1 h
      rw [← hlamμ] at hharm
      have hlamlt : lam * μ < lam * 1 := by
        have : lam = Real.log ((N:ℝ)/m) := hlam_def
        rw [← this] at hharm; rw [mul_one]; exact hharm
      exact lt_of_mul_lt_mul_left hlamlt (le_of_lt hlam)
    have hmono_fcdf := Fcdf_mono_on N mp lam hlam hmpN μ 1 hμpos
    have hμ1 : Fcdf N mp lam μ ≤ Fcdf N mp lam 1 := by
      apply hmono_fcdf
      · exact ⟨le_refl μ, le_of_lt hμlt1⟩
      · exact ⟨le_of_lt hμlt1, le_refl 1⟩
      · exact le_of_lt hμlt1
    linarith [hFhatμ, hμ1]
  -- ===================================================================
  -- THE SOLUTION (reduction target)
  -- ===================================================================
  show (1/2 : ℝ) ≤ Fcdf N (N-m-1) (Real.log ((N:ℝ)/m)) 1
  rcases lt_or_ge (m+1) N with hcase | hcase
  · exact main_half N m h hm1 hcase
  · have hmp0 : m = N - 1 := by omega
    exact edge_half N m h hm1 hmp0
