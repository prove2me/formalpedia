-- Prove2me | solution 1 for BellmanDP.Variational.discrete_approximation_converges
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-31T19:32:16.713371+00:00
-- url     : https://prove2.me/submissions/39cbe2d9-a190-4666-977c-767800c60e7b

import Mathlib
import Definitions.Def_BellmanDP_Variational_Approximation

set_option autoImplicit false

open MeasureTheory Set Filter Topology

namespace FadAux
open BellmanDP.Variational

/-- Assumption (11b) extends to `x = 0` by continuity, in the `φ`-form. -/
lemma phi_bounds (G : ℝ → ℝ → ℝ) (hG : Continuous (fun z : ℝ × ℝ => G z.1 z.2)) (p q r : ℝ)
    (h : ∀ x y : ℝ, 0 < x → 0 ≤ y → y ≤ x → p * x ≤ G x y ∧ G x y ≤ q * x + r) :
    ∀ x φ : ℝ, 0 ≤ x → φ ∈ Icc (0:ℝ) 1 →
      p * x ≤ phiForm G x φ ∧ phiForm G x φ ≤ q * x + r := by
  intro x φ hx hφ
  rcases hx.lt_or_eq with hx | hx
  · exact h x (φ * x) hx (mul_nonneg hφ.1 hx.le) (mul_le_of_le_one_left hx.le hφ.2)
  · subst hx
    simp only [phiForm]
    rw [show φ * 0 = 0 from mul_zero φ]
    have hc : Continuous (fun x : ℝ => G x 0) :=
      hG.comp (continuous_id.prodMk continuous_const)
    have ht : Tendsto (fun x : ℝ => G x 0) (𝓝[>] 0) (𝓝 (G 0 0)) :=
      hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ x in 𝓝[>] (0:ℝ), p * x ≤ G x 0 ∧ G x 0 ≤ q * x + r :=
      eventually_nhdsWithin_of_forall fun x (hx : 0 < x) => h x 0 hx le_rfl hx.le
    have hlin : Tendsto (fun x : ℝ => p * x) (𝓝[>] 0) (𝓝 (p * 0)) :=
      ((continuous_const.mul continuous_id).tendsto 0).mono_left nhdsWithin_le_nhds
    have hlin2 : Tendsto (fun x : ℝ => q * x + r) (𝓝[>] 0) (𝓝 (q * 0 + r)) :=
      (((continuous_const.mul continuous_id).add continuous_const).tendsto 0).mono_left
        nhdsWithin_le_nhds
    refine ⟨le_of_tendsto_of_tendsto hlin ht (hev.mono fun _ h => h.1),
      le_of_tendsto_of_tendsto ht hlin2 (hev.mono fun _ h => h.2)⟩

/-- Lipschitz and sup bounds of `phiForm H` on the box `[-R, R] × [0, 1]`. -/
lemma box_lip (H : ℝ → ℝ → ℝ) (hH : ContDiff ℝ 2 (fun z : ℝ × ℝ => H z.1 z.2)) (R : ℝ) :
    ∃ L K : ℝ, 0 ≤ L ∧ 0 ≤ K ∧
      (∀ x₁ x₂ φ₁ φ₂ : ℝ, x₁ ∈ Icc (-R) R → x₂ ∈ Icc (-R) R → φ₁ ∈ Icc (0:ℝ) 1 →
        φ₂ ∈ Icc (0:ℝ) 1 →
        |phiForm H x₁ φ₁ - phiForm H x₂ φ₂| ≤ L * (|x₁ - x₂| + |φ₁ - φ₂|)) ∧
      (∀ x φ : ℝ, x ∈ Icc (-R) R → φ ∈ Icc (0:ℝ) 1 → |phiForm H x φ| ≤ K) := by
  set h : ℝ × ℝ → ℝ := fun z => H z.1 (z.2 * z.1) with hdef
  have hc : ContDiff ℝ 2 h :=
    hH.comp (contDiff_fst.prodMk (contDiff_snd.mul contDiff_fst))
  set s : Set (ℝ × ℝ) := Icc (-R) R ×ˢ Icc (0:ℝ) 1
  have hconv : Convex ℝ s := (convex_Icc _ _).prod (convex_Icc _ _)
  have hcpt : IsCompact s := isCompact_Icc.prod isCompact_Icc
  obtain ⟨L, hL⟩ := hc.contDiffOn.exists_lipschitzOnWith (by norm_num) hconv hcpt
  obtain ⟨K, hK⟩ := hcpt.exists_bound_of_continuousOn hc.continuous.continuousOn
  refine ⟨L, max K 0, L.2, le_max_right _ _, ?_, ?_⟩
  · intro x₁ x₂ φ₁ φ₂ hx₁ hx₂ hφ₁ hφ₂
    have := hL.dist_le_mul (x₁, φ₁) ⟨hx₁, hφ₁⟩ (x₂, φ₂) ⟨hx₂, hφ₂⟩
    rw [Real.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq] at this
    have hm : max |x₁ - x₂| |φ₁ - φ₂| ≤ |x₁ - x₂| + |φ₁ - φ₂| :=
      max_le (le_add_of_nonneg_right (abs_nonneg _)) (le_add_of_nonneg_left (abs_nonneg _))
    calc |phiForm H x₁ φ₁ - phiForm H x₂ φ₂| ≤ (L : ℝ) * max |x₁ - x₂| |φ₁ - φ₂| := this
      _ ≤ L * (|x₁ - x₂| + |φ₁ - φ₂|) := mul_le_mul_of_nonneg_left hm L.2
  · intro x φ hx hφ
    have := hK (x, φ) ⟨hx, hφ⟩
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)

lemma clamp_le (a b : ℝ) (ha : a ∈ Icc (0:ℝ) 1) : |a - max 0 (min b 1)| ≤ |a - b| := by
  obtain ⟨h0, h1⟩ := ha
  rcases le_total b 0 with hb | hb
  · rw [min_eq_left (by linarith), max_eq_left hb, abs_of_nonneg (by linarith),
      abs_of_nonneg (by linarith)]
    linarith
  · rcases le_total b 1 with hb1 | hb1
    · rw [min_eq_left hb1, max_eq_right hb]
    · rw [min_eq_right hb1, max_eq_right (by norm_num), abs_of_nonpos (by linarith),
        abs_of_nonpos (by linarith)]
      linarith

/-- L¹ approximation of a measurable `[0,1]`-valued control by a continuous `[0,1]`-valued one. -/
lemma l1_approx (T : ℝ) (hT : 0 ≤ T) (φ : ℝ → ℝ) (hφ : Measurable φ)
    (h01 : ∀ t ∈ Icc 0 T, φ t ∈ Icc (0:ℝ) 1) (η : ℝ) (hη : 0 < η) :
    ∃ ψ : ℝ → ℝ, Continuous ψ ∧ (∀ t, ψ t ∈ Icc (0:ℝ) 1) ∧
      ∫ t in (0:ℝ)..T, |φ t - ψ t| ≤ η := by
  have hint : IntegrableOn φ (Icc 0 T) :=
    Measure.integrableOn_of_bounded (M := 1) (by simp) hφ.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun t ht => by
        rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [(h01 t ht).1, (h01 t ht).2]))
  have hf : Integrable ((Icc 0 T).indicator φ) := hint.integrable_indicator measurableSet_Icc
  obtain ⟨g, -, hg, gc, gi⟩ := hf.exists_hasCompactSupport_integral_sub_le hη
  refine ⟨fun t => max 0 (min (g t) 1), continuous_const.max (gc.min continuous_const),
    fun t => ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩, ?_⟩
  rw [intervalIntegral.integral_of_le hT]
  have hψc : Continuous (fun t => max 0 (min (g t) 1)) :=
    continuous_const.max (gc.min continuous_const)
  have i1 : IntegrableOn (fun t => |φ t - max 0 (min (g t) 1)|) (Ioc 0 T) := by
    refine Measure.integrableOn_of_bounded (M := 2) (by simp)
      ((hφ.sub hψc.measurable).abs).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun t ht => ?_))
    have h1 := h01 t (Ioc_subset_Icc_self ht)
    have h2 : max 0 (min (g t) 1) ∈ Icc (0:ℝ) 1 :=
      ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩
    rw [Real.norm_eq_abs, abs_abs, abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have i2 : Integrable (fun t => ‖(Icc 0 T).indicator φ t - g t‖) := (hf.sub gi).norm
  calc ∫ t in Ioc 0 T, |φ t - max 0 (min (g t) 1)|
      ≤ ∫ t in Ioc 0 T, ‖(Icc 0 T).indicator φ t - g t‖ := by
        refine setIntegral_mono_on i1 i2.integrableOn measurableSet_Ioc fun t ht => ?_
        rw [indicator_of_mem (Ioc_subset_Icc_self ht), Real.norm_eq_abs]
        exact clamp_le _ _ (h01 t (Ioc_subset_Icc_self ht))
    _ ≤ ∫ t, ‖(Icc 0 T).indicator φ t - g t‖ :=
        setIntegral_le_integral i2 (Eventually.of_forall fun _ => norm_nonneg _)
    _ ≤ η := hg

/-- Sampling a continuous control on the grid `k / n` converges in L¹. -/
lemma sample_l1 (T : ℝ) (hT : 0 ≤ T) (ψ : ℝ → ℝ) (hψ : Continuous ψ) (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∫ t in (0:ℝ)..T, |ψ t - stepControl n (fun k => ψ (k / n)) t| ≤ ε := by
  have huc : UniformContinuousOn ψ (Icc 0 T) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hψ.continuousOn
  have hε' : 0 < ε / (T + 1) := div_pos hε (by linarith)
  obtain ⟨δ, hδ, hδε⟩ := Metric.uniformContinuousOn_iff.1 huc _ hε'
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (1 / δ)
  refine ⟨n₀, fun n hn => ?_⟩
  have hnpos : (0:ℝ) < n := by
    have : (0:ℝ) < n₀ := lt_trans (by positivity) hn₀
    exact lt_of_lt_of_le this (by exact_mod_cast hn)
  have hn1 : 1 / δ < n := lt_of_lt_of_le hn₀ (by exact_mod_cast hn)
  have hpt : ∀ t ∈ Set.uIoc (0:ℝ) T,
      ‖|ψ t - stepControl n (fun k => ψ (k / n)) t|‖ ≤ ε / (T + 1) := by
    intro t ht
    rw [uIoc_of_le hT] at ht
    have ht0 : 0 ≤ t * n := mul_nonneg ht.1.le hnpos.le
    have hfl := Nat.floor_le ht0
    have hfl2 := Nat.lt_floor_add_one (t * n)
    set m := ⌊t * n⌋₊
    have hs0 : 0 ≤ (m : ℝ) / n := by positivity
    have hst : (m : ℝ) / n ≤ t := by rw [div_le_iff₀ hnpos]; exact hfl
    have hst2 : t - (m : ℝ) / n < 1 / n := by
      have h' : t < ((m : ℝ) + 1) / n := by rw [lt_div_iff₀ hnpos]; linarith
      have h'' : ((m : ℝ) + 1) / n = (m : ℝ) / n + 1 / n := by ring
      linarith
    have h1n : 1 / (n : ℝ) < δ := by
      rw [div_lt_iff₀ hnpos]; rw [div_lt_iff₀ hδ] at hn1; linarith
    have hd : dist t ((m : ℝ) / n) < δ := by
      rw [Real.dist_eq, abs_of_nonneg (by linarith)]; linarith
    have := hδε t ⟨ht.1.le, ht.2⟩ ((m : ℝ) / n) ⟨hs0, hst.trans ht.2⟩ hd
    rw [Real.dist_eq] at this
    simp only [stepControl, Real.norm_eq_abs, abs_abs]
    exact this.le
  have := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ T - 0), sub_zero] at this
  calc ∫ t in (0:ℝ)..T, |ψ t - stepControl n (fun k => ψ (k / n)) t|
      ≤ ‖∫ t in (0:ℝ)..T, |ψ t - stepControl n (fun k => ψ (k / n)) t|‖ := le_abs_self _
    _ ≤ ε / (T + 1) * T := this
    _ ≤ ε := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]; nlinarith

/-- Discrete a priori bound on the Euler states. -/
lemma euler_apriori (g : ℝ → ℝ → ℝ) (p q r : ℝ)
    (hb : ∀ x φ : ℝ, 0 ≤ x → φ ∈ Icc (0:ℝ) 1 → p * x ≤ g x φ ∧ g x φ ≤ q * x + r)
    (c : ℝ) (hc : 0 ≤ c) (n : ℕ) (hn : |p| ≤ n) (hn1 : 1 ≤ n) (φs : ℕ → ℝ) (m : ℕ)
    (hφ : ∀ k < m, φs k ∈ Icc (0:ℝ) 1) :
    ∀ k ≤ m, 0 ≤ eulerTraj g c n φs k ∧
      eulerTraj g c n φs k ≤ (c + |r| * k / n) * Real.exp (|q| * k / n) := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn1
  intro k
  induction k with
  | zero => intro _; simp [eulerTraj, hc]
  | succ k ih =>
    intro hk
    obtain ⟨h0, h1⟩ := ih (by omega)
    obtain ⟨hl, hu⟩ := hb _ _ h0 (hφ k (by omega))
    set X := eulerTraj g c n φs k
    have hstep : eulerTraj g c n φs (k + 1) = X + g X (φs k) / n := rfl
    rw [hstep]
    have hp : -1 ≤ p / n := by
      rw [le_div_iff₀ hnpos]; linarith [neg_abs_le p]
    constructor
    · have : p * X / n ≤ g X (φs k) / n := div_le_div_of_nonneg_right hl hnpos.le
      have h2 : X + p * X / n = X * (1 + p / n) := by ring
      have h3 : 0 ≤ X * (1 + p / n) := mul_nonneg h0 (by linarith)
      linarith
    · set B := c + |r| * k / n
      set E := Real.exp (|q| * k / n)
      set E1 := Real.exp (|q| / n)
      have hE : 1 ≤ E := Real.one_le_exp (by positivity)
      have hE1 : 1 + |q| / n ≤ E1 := by
        have := Real.add_one_le_exp (|q| / n); linarith
      have hEE : E * E1 = Real.exp (|q| * ((k + 1 : ℕ) : ℝ) / n) := by
        rw [← Real.exp_add]; congr 1; push_cast; ring
      have hB : 0 ≤ B := by positivity
      have hup : X + g X (φs k) / n ≤ X * (1 + |q| / n) + |r| / n := by
        have : g X (φs k) / n ≤ (q * X + r) / n := div_le_div_of_nonneg_right hu hnpos.le
        have hq : q * X ≤ |q| * X := mul_le_mul_of_nonneg_right (le_abs_self q) h0
        have hr : r ≤ |r| := le_abs_self r
        have : (q * X + r) / n ≤ (|q| * X + |r|) / n :=
          div_le_div_of_nonneg_right (by linarith) hnpos.le
        have h5 : X * (1 + |q| / n) + |r| / n = X + (|q| * X + |r|) / n := by ring
        linarith
      have h6 : X * (1 + |q| / n) ≤ B * E * E1 :=
        mul_le_mul h1 hE1 (by positivity) (by positivity)
      have h7 : |r| / n ≤ |r| / n * (E * E1) :=
        le_mul_of_one_le_right (by positivity) (one_le_mul_of_one_le_of_one_le hE (Real.one_le_exp (by positivity)))
      have h8 : (c + |r| * ((k + 1 : ℕ) : ℝ) / n) = B + |r| / n := by
        simp only [B]; push_cast; ring
      rw [h8, ← hEE]
      nlinarith



/-- One cell of the Euler comparison. -/
lemma cell_est (m : ℝ → ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ x₁ x₂ φ₁ φ₂ : ℝ, φ₁ ∈ Icc (0:ℝ) 1 → φ₂ ∈ Icc (0:ℝ) 1 →
      |m x₁ φ₁ - m x₂ φ₂| ≤ L * (|x₁ - x₂| + |φ₁ - φ₂|))
    (a b : ℝ) (hab : a ≤ b) (x ψ : ℝ → ℝ) (xk φk δ : ℝ) (hφk : φk ∈ Icc (0:ℝ) 1)
    (hψ : ∀ s ∈ Icc a b, ψ s ∈ Icc (0:ℝ) 1) (hx : ∀ s ∈ Icc a b, |x s - xk| ≤ δ)
    (hi1 : IntervalIntegrable (fun s => m (x s) (ψ s)) volume a b)
    (hi2 : IntervalIntegrable (fun s => |ψ s - φk|) volume a b) :
    |(b - a) * m xk φk - ∫ s in a..b, m (x s) (ψ s)| ≤
      L * δ * (b - a) + L * ∫ s in a..b, |ψ s - φk| := by
  have h1 : (b - a) * m xk φk = ∫ _ in a..b, m xk φk := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
  have hc : IntervalIntegrable (fun _ : ℝ => m xk φk) volume a b := intervalIntegrable_const
  rw [h1, ← intervalIntegral.integral_sub hc hi1]
  refine (intervalIntegral.abs_integral_le_integral_abs hab).trans ?_
  have hi3 : IntervalIntegrable (fun s => L * δ + L * |ψ s - φk|) volume a b :=
    intervalIntegrable_const.add (hi2.const_mul L)
  calc ∫ s in a..b, |m xk φk - m (x s) (ψ s)|
      ≤ ∫ s in a..b, (L * δ + L * |ψ s - φk|) := by
        refine intervalIntegral.integral_mono_on hab (hc.sub hi1).abs hi3 fun s hs => ?_
        have h0 := hLip xk (x s) φk (ψ s) hφk (hψ s hs)
        have h2 : |xk - x s| ≤ δ := by rw [abs_sub_comm]; exact hx s hs
        rw [abs_sub_comm φk] at h0
        calc |m xk φk - m (x s) (ψ s)| ≤ L * (|xk - x s| + |ψ s - φk|) := h0
          _ ≤ L * (δ + |ψ s - φk|) := mul_le_mul_of_nonneg_left (by linarith) hL
          _ = L * δ + L * |ψ s - φk| := by ring
    _ = L * δ * (b - a) + L * ∫ s in a..b, |ψ s - φk| := by
        rw [intervalIntegral.integral_add intervalIntegrable_const (hi2.const_mul L),
          intervalIntegral.integral_const, intervalIntegral.integral_const_mul, smul_eq_mul]
        ring

/-- Euler comparison: the Euler scheme with grid controls `φs` tracks any trajectory with
control `ψ`, with error controlled by `1/n` plus the L¹ distance of `ψ` to the step control. -/
lemma euler_compare (h ℓ : ℝ → ℝ → ℝ) (L K : ℝ) (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hLh : ∀ x₁ x₂ φ₁ φ₂ : ℝ, φ₁ ∈ Icc (0:ℝ) 1 → φ₂ ∈ Icc (0:ℝ) 1 →
      |h x₁ φ₁ - h x₂ φ₂| ≤ L * (|x₁ - x₂| + |φ₁ - φ₂|))
    (hLl : ∀ x₁ x₂ φ₁ φ₂ : ℝ, φ₁ ∈ Icc (0:ℝ) 1 → φ₂ ∈ Icc (0:ℝ) 1 →
      |ℓ x₁ φ₁ - ℓ x₂ φ₂| ≤ L * (|x₁ - x₂| + |φ₁ - φ₂|))
    (hKh : ∀ x φ : ℝ, φ ∈ Icc (0:ℝ) 1 → |h x φ| ≤ K)
    (hKl : ∀ x φ : ℝ, φ ∈ Icc (0:ℝ) 1 → |ℓ x φ| ≤ K)
    (T : ℝ) (hT : 0 ≤ T) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (c : ℝ) (n : ℕ) (ψ x : ℝ → ℝ) (φs : ℕ → ℝ), 1 ≤ n → Measurable ψ →
      (∀ t ∈ Icc 0 T, ψ t ∈ Icc (0:ℝ) 1) → IsTrajectory h c ψ T x →
      IntegrableOn (fun t => ℓ (x t) (ψ t)) (Icc 0 T) →
      (∀ k ≤ horizonSteps T n, φs k ∈ Icc (0:ℝ) 1) →
      (∀ k ≤ horizonSteps T n, |eulerTraj h c n φs k - x (k / n)| ≤
        B * (1 / n + ∫ t in (0:ℝ)..T, |ψ t - stepControl n φs t|)) ∧
      |discretePayoff ℓ h c n φs (horizonSteps T n) - ∫ t in (0:ℝ)..T, ℓ (x t) (ψ t)| ≤
        B * (1 / n + ∫ t in (0:ℝ)..T, |ψ t - stepControl n φs t|) := by
  set E0 := (L * K * T + L) * Real.exp (L * T) with hE0def
  have hE0 : 0 ≤ E0 := by positivity
  refine ⟨E0 * (1 + L * T) + L * T * K + L + 2 * K, by positivity, ?_⟩
  intro c n ψ x φs hn hψm hψ hx hℓi hφs
  obtain ⟨-, hhi, hxeq⟩ := hx
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have hinv : (0:ℝ) ≤ 1 / n := by positivity
  set N := horizonSteps T n with hNdef
  have hTn : 0 ≤ T * n := by positivity
  have hN1 : (N : ℝ) ≤ T * n := Nat.floor_le hTn
  have hN2 : T * n < N + 1 := Nat.lt_floor_add_one _
  set a : ℕ → ℝ := fun k => (k : ℝ) / n with hadef
  have ha0 : a 0 = 0 := by simp [a]
  have hasucc : ∀ k, a (k + 1) - a k = 1 / n := by
    intro k; simp only [a]; push_cast; ring
  have hamono : ∀ k, a k ≤ a (k + 1) := fun k => by linarith [hasucc k]
  have haN : a N ≤ T := by simp only [a]; rw [div_le_iff₀ hnpos]; exact hN1
  have hTaN : T - a N ≤ 1 / n := by
    have : T ≤ ((N : ℝ) + 1) / n := by rw [le_div_iff₀ hnpos]; linarith
    have h2 : ((N : ℝ) + 1) / n = a N + 1 / n := by simp only [a]; ring
    linarith
  have ha_nonneg : ∀ k, 0 ≤ a k := fun k => by positivity
  have ha_le : ∀ k ≤ N, a k ≤ T := fun k hk =>
    le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hk) hnpos.le) haN
  have iiOn : ∀ f : ℝ → ℝ, IntegrableOn f (Icc 0 T) → ∀ u v : ℝ, 0 ≤ u → u ≤ v → v ≤ T →
      IntervalIntegrable f volume u v := by
    intro f hf u v hu huv hv
    exact (hf.mono_set (by rw [uIcc_of_le huv]; exact Icc_subset_Icc hu hv)).intervalIntegrable
  have hψi : IntegrableOn ψ (Icc 0 T) :=
    Measure.integrableOn_of_bounded (M := 1) (by simp) hψm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun t ht => by
        rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [(hψ t ht).1, (hψ t ht).2]))
  have hψci : ∀ v : ℝ, IntegrableOn (fun s => |ψ s - v|) (Icc 0 T) := fun v =>
    Integrable.abs (Integrable.sub hψi (continuous_const : Continuous fun _ : ℝ => v).integrableOn_Icc)
  have hstepm : Measurable (stepControl n φs) :=
    (measurable_from_nat (f := φs)).comp (Nat.measurable_floor.comp (measurable_id.mul_const _))
  have hstep01 : ∀ t ∈ Icc 0 T, stepControl n φs t ∈ Icc (0:ℝ) 1 := by
    intro t ht
    exact hφs _ (Nat.floor_le_floor (mul_le_mul_of_nonneg_right ht.2 hnpos.le))
  have hdi : IntegrableOn (fun s => |ψ s - stepControl n φs s|) (Icc 0 T) :=
    Measure.integrableOn_of_bounded (M := 2) (by simp)
      ((hψm.sub hstepm).abs).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun t ht => by
        rw [Real.norm_eq_abs, abs_abs, abs_le]
        constructor <;> linarith [(hψ t ht).1, (hψ t ht).2, (hstep01 t ht).1, (hstep01 t ht).2]))
  set Δ := ∫ t in (0:ℝ)..T, |ψ t - stepControl n φs t| with hΔdef
  have hΔ : 0 ≤ Δ := intervalIntegral.integral_nonneg hT fun _ _ => abs_nonneg _
  set D := 1 / (n : ℝ) + Δ with hDdef
  set I : ℕ → ℝ := fun k => ∫ s in a k..a (k + 1), |ψ s - φs k| with hIdef
  have hI0 : ∀ k, 0 ≤ I k := fun k =>
    intervalIntegral.integral_nonneg (hamono k) fun _ _ => abs_nonneg _
  -- the cell integrals of `|ψ - φs k|` sum to at most `Δ`
  have hcell : ∀ k < N, I k = ∫ s in a k..a (k + 1), |ψ s - stepControl n φs s| := by
    intro k hk
    have hne : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ a (k + 1) := by
      have := compl_mem_ae_iff.2 (measure_singleton (μ := (volume : Measure ℝ)) (a (k + 1)))
      filter_upwards [this] with s hs using hs
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hne] with s hs hsI
    rw [uIoc_of_le (hamono k)] at hsI
    have hs1 : (k : ℝ) / n < s := hsI.1
    have hs2 : s < ((k + 1 : ℕ) : ℝ) / n := lt_of_le_of_ne hsI.2 hs
    have hfl : ⌊s * n⌋₊ = k := by
      rw [Nat.floor_eq_iff (by nlinarith [ha_nonneg k])]
      rw [div_lt_iff₀ hnpos] at hs1
      rw [lt_div_iff₀ hnpos] at hs2
      push_cast at hs2
      constructor <;> linarith
    simp only [stepControl, hfl]
  have hS : ∑ k ∈ Finset.range N, I k ≤ Δ := by
    rw [Finset.sum_congr rfl fun k hk => hcell k (Finset.mem_range.1 hk),
      intervalIntegral.sum_integral_adjacent_intervals fun k hk =>
        iiOn _ (hdi) _ _ (ha_nonneg k) (hamono k) (ha_le (k + 1) hk), ha0]
    exact intervalIntegral.integral_mono_interval le_rfl (ha_nonneg N) haN
      (Eventually.of_forall fun _ => abs_nonneg _) (iiOn _ hdi 0 T le_rfl hT le_rfl)
  -- Euler states and errors
  set X : ℕ → ℝ := fun k => eulerTraj h c n φs k with hXdef
  set e : ℕ → ℝ := fun k => |X k - x (a k)| with hedef
  have hxa : ∀ k < N, ∀ s ∈ Icc (a k) (a (k + 1)), |x s - X k| ≤ K / n + e k := by
    intro k hk s hs
    have hs0 : 0 ≤ s := (ha_nonneg k).trans hs.1
    have hsT : s ≤ T := hs.2.trans (ha_le (k + 1) hk)
    have hdiff : x s - x (a k) = ∫ τ in a k..s, h (x τ) (ψ τ) := by
      rw [hxeq s ⟨hs0, hsT⟩, hxeq (a k) ⟨ha_nonneg k, (ha_le k hk.le)⟩, add_sub_add_left_eq_sub,
        intervalIntegral.integral_interval_sub_left (iiOn _ hhi 0 s le_rfl hs0 hsT)
          (iiOn _ hhi 0 (a k) le_rfl (ha_nonneg k) (ha_le k hk.le))]
    have hb : |x s - x (a k)| ≤ K * |s - a k| := by
      rw [hdiff, ← Real.norm_eq_abs]
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun τ hτ => ?_
      rw [uIoc_of_le hs.1] at hτ
      rw [Real.norm_eq_abs]
      exact hKh _ _ (hψ τ ⟨(ha_nonneg k).trans hτ.1.le, hτ.2.trans hsT⟩)
    have h1 : |s - a k| ≤ 1 / n := by
      rw [abs_of_nonneg (by linarith [hs.1])]; linarith [hs.2, hasucc k]
    have h2 : K * |s - a k| ≤ K * (1 / n) := mul_le_mul_of_nonneg_left h1 hK
    have h3 : |x s - X k| ≤ |x s - x (a k)| + |x (a k) - X k| := abs_sub_le _ _ _
    have h4 : |x (a k) - X k| = e k := abs_sub_comm _ _
    have h5 : K * (1 / n) = K / n := by ring
    linarith
  have hrec : ∀ k < N, e (k + 1) ≤ (1 + L / n) * e k + (L * (K / n) * (1 / n) + L * I k) := by
    intro k hk
    have i1 := iiOn _ hhi 0 (a k) le_rfl (ha_nonneg k) (ha_le k hk.le)
    have i2 := iiOn _ hhi (a k) (a (k + 1)) (ha_nonneg k) (hamono k) (ha_le (k + 1) hk)
    have hxs : x (a (k + 1)) = x (a k) + ∫ s in a k..a (k + 1), h (x s) (ψ s) := by
      rw [hxeq (a (k + 1)) ⟨ha_nonneg _, ha_le _ hk⟩, hxeq (a k) ⟨ha_nonneg _, ha_le k hk.le⟩,
        add_assoc, intervalIntegral.integral_add_adjacent_intervals i1 i2]
    have hcl := cell_est h L hL hLh (a k) (a (k + 1)) (hamono k) x ψ (X k) (φs k) (K / n + e k)
      (hφs k (by omega)) (fun s hs => hψ s ⟨(ha_nonneg k).trans hs.1, hs.2.trans (ha_le _ hk)⟩)
      (hxa k hk) i2
      (iiOn _ (hψci (φs k)) _ _ (ha_nonneg k) (hamono k) (ha_le (k + 1) hk))
    rw [hasucc k] at hcl
    have hXs : X (k + 1) = X k + h (X k) (φs k) / n := rfl
    have heq : X (k + 1) - x (a (k + 1)) = (X k - x (a k)) +
        (1 / n * h (X k) (φs k) - ∫ s in a k..a (k + 1), h (x s) (ψ s)) := by
      rw [hXs, hxs]; ring
    have habs : e (k + 1) ≤ e k + |1 / n * h (X k) (φs k) - ∫ s in a k..a (k + 1), h (x s) (ψ s)| := by
      show |X (k + 1) - x (a (k + 1))| ≤ _
      rw [heq]; exact abs_add_le _ _
    have hexp : L * (K / n + e k) * (1 / n) = L / n * e k + L * (K / n) * (1 / n) := by ring
    have hI : I k = ∫ s in a k..a (k + 1), |ψ s - φs k| := rfl
    rw [← hI] at hcl
    nlinarith [hcl, habs, hexp]
  -- discrete Grönwall
  set eb := (L * K * T / n + L * Δ) * Real.exp (L * T) with hebdef
  have he : ∀ k ≤ N, e k ≤ eb := by
    set u : ℕ → ℝ := fun j => e (min j N) with hudef
    have hb0 : ∀ j, 0 ≤ L * (K / n) * (1 / n) + L * I j := fun j => by
      have := hI0 j; positivity
    have hc0 : ∀ _j : ℕ, 0 ≤ L / (n : ℝ) := fun _ => by positivity
    have hu0 : u 0 = 0 := by
      simp only [u, e, X, Nat.zero_min, ha0]
      rw [hxeq 0 ⟨le_rfl, hT⟩, intervalIntegral.integral_same, add_zero]
      simp [eulerTraj]
    have hu : ∀ j ≥ 0, u (j + 1) ≤ (1 + L / n) * u j + (L * (K / n) * (1 / n) + L * I j) := by
      intro j _
      by_cases hj : j < N
      · simp only [u]
        rw [Nat.min_eq_left (by omega : j + 1 ≤ N), Nat.min_eq_left hj.le]
        exact hrec j hj
      · simp only [u]
        rw [Nat.min_eq_right (by omega : N ≤ j + 1), Nat.min_eq_right (by omega : N ≤ j)]
        have h1 : 0 ≤ e N := abs_nonneg _
        have h2 : 0 ≤ L / n * e N := mul_nonneg (hc0 0) h1
        nlinarith [hb0 j]
    intro k hk
    have hg := discrete_gronwall (u := u) (n₀ := 0) (by rw [hu0]) hu (fun j _ => hc0 j)
      (fun j _ => hb0 j) (Nat.zero_le k)
    have hek : e k = u k := by simp only [u, Nat.min_eq_left hk]
    rw [hek]
    refine hg.trans ?_
    rw [hu0, zero_add, Nat.Ico_zero_eq_range]
    have hsum1 : ∑ i ∈ Finset.range k, (L * (K / n) * (1 / n) + L * I i) ≤
        L * K * T / n + L * Δ := by
      have hsub : ∑ i ∈ Finset.range k, (L * (K / n) * (1 / n) + L * I i) ≤
          ∑ i ∈ Finset.range N, (L * (K / n) * (1 / n) + L * I i) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hk) fun j _ _ => hb0 j
      have hN' : ∑ i ∈ Finset.range N, (L * (K / n) * (1 / n) + L * I i) =
          (N : ℝ) * (L * (K / n) * (1 / n)) + L * ∑ i ∈ Finset.range N, I i := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          ← Finset.mul_sum]
      have hNn : (N : ℝ) * (L * (K / n) * (1 / n)) ≤ L * K * T / n := by
        have : (N : ℝ) * (L * (K / n) * (1 / n)) = (N / n) * (L * K / n) := by ring
        rw [this]
        have hNT : (N : ℝ) / n ≤ T := by rw [div_le_iff₀ hnpos]; exact hN1
        have : (N : ℝ) / n * (L * K / n) ≤ T * (L * K / n) :=
          mul_le_mul_of_nonneg_right hNT (by positivity)
        linarith [show T * (L * K / n) = L * K * T / n by ring]
      have hLS : L * ∑ i ∈ Finset.range N, I i ≤ L * Δ := mul_le_mul_of_nonneg_left hS hL
      linarith
    have hsum2 : ∑ i ∈ Finset.range k, L / (n : ℝ) ≤ L * T := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hkT : (k : ℝ) / n ≤ T := ha_le k hk
      have : (k : ℝ) * (L / n) = L * ((k : ℝ) / n) := by ring
      rw [this]; exact mul_le_mul_of_nonneg_left hkT hL
    have hpos : 0 ≤ L * K * T / n + L * Δ := by positivity
    calc (∑ i ∈ Finset.range k, (L * (K / n) * (1 / n) + L * I i)) *
          Real.exp (∑ i ∈ Finset.range k, L / (n : ℝ))
        ≤ (L * K * T / n + L * Δ) * Real.exp (∑ i ∈ Finset.range k, L / (n : ℝ)) :=
          mul_le_mul_of_nonneg_right hsum1 (Real.exp_pos _).le
      _ ≤ eb := mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hsum2) hpos
  have hebD : eb ≤ E0 * D := by
    have h1 : L * K * T / n ≤ L * K * T * D := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h2 : L * Δ ≤ L * D := mul_le_mul_of_nonneg_left (by linarith) hL
    have h3 : L * K * T / n + L * Δ ≤ (L * K * T + L) * D := by nlinarith
    calc eb ≤ (L * K * T + L) * D * Real.exp (L * T) :=
          mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
      _ = E0 * D := by rw [hE0def]; ring
  have hD : 0 ≤ D := by positivity
  have hB1 : E0 * D ≤ (E0 * (1 + L * T) + L * T * K + L + 2 * K) * D := by
    apply mul_le_mul_of_nonneg_right _ hD
    have : 0 ≤ E0 * (L * T) := by positivity
    have h1 : E0 * (1 + L * T) = E0 + E0 * (L * T) := by ring
    have h2 : 0 ≤ L * T * K := by positivity
    linarith
  refine ⟨fun k hk => (he k hk).trans (hebD.trans hB1), ?_⟩
  -- payoff comparison
  have hJ : ∫ t in (0:ℝ)..T, ℓ (x t) (ψ t) =
      ∑ k ∈ Finset.range N, (∫ s in a k..a (k + 1), ℓ (x s) (ψ s)) +
        ∫ s in a N..T, ℓ (x s) (ψ s) := by
    rw [intervalIntegral.sum_integral_adjacent_intervals fun k hk =>
        iiOn _ hℓi _ _ (ha_nonneg k) (hamono k) (ha_le (k + 1) hk), ha0,
      intervalIntegral.integral_add_adjacent_intervals
        (iiOn _ hℓi 0 (a N) le_rfl (ha_nonneg N) haN) (iiOn _ hℓi (a N) T (ha_nonneg N) haN le_rfl)]
  have hP : discretePayoff ℓ h c n φs N =
      ∑ k ∈ Finset.range N, (1 / n * ℓ (X k) (φs k)) + ℓ (X N) (φs N) / n := by
    simp only [discretePayoff, Finset.sum_range_succ, X]
    congr 1
    refine Finset.sum_congr rfl fun k _ => by ring
  rw [hJ, hP]
  have hcellℓ : ∀ k ∈ Finset.range N,
      |1 / n * ℓ (X k) (φs k) - ∫ s in a k..a (k + 1), ℓ (x s) (ψ s)| ≤
        L * (K / n + eb) * (1 / n) + L * I k := by
    intro k hk
    have hk' := Finset.mem_range.1 hk
    have hcl := cell_est ℓ L hL hLl (a k) (a (k + 1)) (hamono k) x ψ (X k) (φs k) (K / n + e k)
      (hφs k (by omega)) (fun s hs => hψ s ⟨(ha_nonneg k).trans hs.1, hs.2.trans (ha_le _ hk')⟩)
      (hxa k hk')
      (iiOn _ hℓi _ _ (ha_nonneg k) (hamono k) (ha_le (k + 1) hk'))
      (iiOn _ (hψci (φs k)) _ _ (ha_nonneg k) (hamono k) (ha_le (k + 1) hk'))
    rw [hasucc k] at hcl
    have hI : I k = ∫ s in a k..a (k + 1), |ψ s - φs k| := rfl
    rw [← hI] at hcl
    have h1 : L * (K / n + e k) * (1 / n) ≤ L * (K / n + eb) * (1 / n) := by
      have := he k hk'.le
      apply mul_le_mul_of_nonneg_right _ hinv
      exact mul_le_mul_of_nonneg_left (by linarith) hL
    exact hcl.trans (by linarith)
  have hsumc : |∑ k ∈ Finset.range N, (1 / n * ℓ (X k) (φs k) -
      ∫ s in a k..a (k + 1), ℓ (x s) (ψ s))| ≤ T * L * (K / n + eb) + L * Δ := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hcellℓ).trans ?_)
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      ← Finset.mul_sum]
    have hNT : (N : ℝ) / n ≤ T := by rw [div_le_iff₀ hnpos]; exact hN1
    have h1 : (N : ℝ) * (L * (K / n + eb) * (1 / n)) = (N / n) * (L * (K / n + eb)) := by ring
    have hpos : 0 ≤ L * (K / n + eb) := by
      have : 0 ≤ eb := (abs_nonneg _).trans (he 0 (Nat.zero_le _))
      positivity
    have h2 : (N : ℝ) / n * (L * (K / n + eb)) ≤ T * (L * (K / n + eb)) :=
      mul_le_mul_of_nonneg_right hNT hpos
    have h3 : L * ∑ i ∈ Finset.range N, I i ≤ L * Δ := mul_le_mul_of_nonneg_left hS hL
    have h4 : T * (L * (K / n + eb)) = T * L * (K / n + eb) := by ring
    rw [h1]; linarith
  have hlast : |ℓ (X N) (φs N) / n| ≤ K / n := by
    rw [abs_div, abs_of_pos hnpos]
    exact div_le_div_of_nonneg_right (hKl _ _ (hφs N le_rfl)) hnpos.le
  have htail : |∫ s in a N..T, ℓ (x s) (ψ s)| ≤ K / n := by
    rw [← Real.norm_eq_abs]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a N) (b := T) (C := K)
      (f := fun s => ℓ (x s) (ψ s)) fun τ hτ => by
        rw [uIoc_of_le haN] at hτ
        rw [Real.norm_eq_abs]
        exact hKl _ _ (hψ τ ⟨(ha_nonneg N).trans hτ.1.le, hτ.2⟩)
    rw [abs_of_nonneg (by linarith)] at this
    refine this.trans ?_
    calc K * (T - a N) ≤ K * (1 / n) := mul_le_mul_of_nonneg_left hTaN hK
      _ = K / n := by ring
  have hsplit : (∑ k ∈ Finset.range N, (1 / n * ℓ (X k) (φs k)) + ℓ (X N) (φs N) / n) -
      ((∑ k ∈ Finset.range N, ∫ s in a k..a (k + 1), ℓ (x s) (ψ s)) +
        ∫ s in a N..T, ℓ (x s) (ψ s)) =
      (∑ k ∈ Finset.range N, (1 / n * ℓ (X k) (φs k) -
        ∫ s in a k..a (k + 1), ℓ (x s) (ψ s))) + (ℓ (X N) (φs N) / n -
        ∫ s in a N..T, ℓ (x s) (ψ s)) := by
    rw [Finset.sum_sub_distrib]; ring
  rw [hsplit]
  have htot := abs_add_le (∑ k ∈ Finset.range N, (1 / n * ℓ (X k) (φs k) -
        ∫ s in a k..a (k + 1), ℓ (x s) (ψ s))) (ℓ (X N) (φs N) / n -
        ∫ s in a N..T, ℓ (x s) (ψ s))
  have hlt := abs_sub (ℓ (X N) (φs N) / n) (∫ s in a N..T, ℓ (x s) (ψ s))
  -- final arithmetic
  have k1 : T * L * (K / n) ≤ T * L * K * D := by
    rw [show T * L * (K / n) = T * L * K * (1 / n) by ring]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have k2 : T * L * eb ≤ T * L * (E0 * D) := mul_le_mul_of_nonneg_left hebD (by positivity)
  have k3 : L * Δ ≤ L * D := mul_le_mul_of_nonneg_left (by linarith) hL
  have k4 : 2 * (K / n) ≤ 2 * K * D := by
    rw [show 2 * (K / n) = 2 * K * (1 / n) by ring]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have k5 : T * L * (K / n + eb) = T * L * (K / n) + T * L * eb := by ring
  have k6 : (E0 * (1 + L * T) + L * T * K + L + 2 * K) * D =
      E0 * D + T * L * (E0 * D) + T * L * K * D + L * D + 2 * K * D := by ring
  have k7 : 0 ≤ E0 * D := by positivity
  linarith



lemma clamp_mem (R x : ℝ) (hR : 0 ≤ R) : max (-R) (min x R) ∈ Icc (-R) R :=
  ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩

lemma clamp_lip (R x₁ x₂ : ℝ) : |max (-R) (min x₁ R) - max (-R) (min x₂ R)| ≤ |x₁ - x₂| := by
  have h1 := abs_max_sub_max_le_max (-R) (min x₁ R) (-R) (min x₂ R)
  have h2 := abs_min_sub_min_le_max x₁ R x₂ R
  simp only [sub_self, abs_zero] at h1 h2
  have h3 : max 0 |min x₁ R - min x₂ R| = |min x₁ R - min x₂ R| :=
    max_eq_right (abs_nonneg _)
  have h4 : max |x₁ - x₂| 0 = |x₁ - x₂| := max_eq_left (abs_nonneg _)
  rw [h3] at h1; rw [h4] at h2
  exact h1.trans h2

lemma clamp_eq (R x : ℝ) (hx : x ∈ Icc (-R) R) : max (-R) (min x R) = x := by
  rw [min_eq_left hx.2, max_eq_right hx.1]

/-- The clamped field is globally Lipschitz and bounded. -/
lemma clamp_field (g : ℝ → ℝ → ℝ) (R L K : ℝ) (hR : 0 ≤ R)
    (hL : ∀ x₁ x₂ φ₁ φ₂ : ℝ, x₁ ∈ Icc (-R) R → x₂ ∈ Icc (-R) R → φ₁ ∈ Icc (0:ℝ) 1 →
        φ₂ ∈ Icc (0:ℝ) 1 → |g x₁ φ₁ - g x₂ φ₂| ≤ L * (|x₁ - x₂| + |φ₁ - φ₂|))
    (hL0 : 0 ≤ L)
    (hK : ∀ x φ : ℝ, x ∈ Icc (-R) R → φ ∈ Icc (0:ℝ) 1 → |g x φ| ≤ K) :
    (∀ x₁ x₂ φ₁ φ₂ : ℝ, φ₁ ∈ Icc (0:ℝ) 1 → φ₂ ∈ Icc (0:ℝ) 1 →
        |g (max (-R) (min x₁ R)) φ₁ - g (max (-R) (min x₂ R)) φ₂| ≤
          L * (|x₁ - x₂| + |φ₁ - φ₂|)) ∧
      (∀ x φ : ℝ, φ ∈ Icc (0:ℝ) 1 → |g (max (-R) (min x R)) φ| ≤ K) := by
  refine ⟨fun x₁ x₂ φ₁ φ₂ h₁ h₂ => ?_, fun x φ hφ => hK _ _ (clamp_mem R x hR) hφ⟩
  refine (hL _ _ _ _ (clamp_mem R x₁ hR) (clamp_mem R x₂ hR) h₁ h₂).trans ?_
  exact mul_le_mul_of_nonneg_left (by linarith [clamp_lip R x₁ x₂]) hL0

/-- Existence of a continuous trajectory for a continuous control, for a globally Lipschitz
bounded field (Picard–Lindelöf). -/
lemma exists_traj (h : ℝ → ℝ → ℝ) (hc : Continuous (fun z : ℝ × ℝ => h z.1 z.2)) (L K : ℝ)
    (hL0 : 0 ≤ L) (hK0 : 0 ≤ K)
    (hLip : ∀ x₁ x₂ φ : ℝ, φ ∈ Icc (0:ℝ) 1 → |h x₁ φ - h x₂ φ| ≤ L * |x₁ - x₂|)
    (hKb : ∀ x φ : ℝ, φ ∈ Icc (0:ℝ) 1 → |h x φ| ≤ K) (T : ℝ) (hT : 0 ≤ T) (c : ℝ)
    (ψ : ℝ → ℝ) (hψc : Continuous ψ) (hψ01 : ∀ t, ψ t ∈ Icc (0:ℝ) 1) :
    ∃ x : ℝ → ℝ, Continuous x ∧ ∀ t ∈ Icc 0 T, x t = c + ∫ s in (0:ℝ)..t, h (x s) (ψ s) := by
  set f : ℝ → ℝ → ℝ := fun t x => h x (ψ t)
  let t₀ : Icc (0:ℝ) T := ⟨0, le_rfl, hT⟩
  let an : NNReal := ⟨K * T, by positivity⟩
  let Kn : NNReal := ⟨K, hK0⟩
  let Ln : NNReal := ⟨L, hL0⟩
  have hf : IsPicardLindelof f t₀ c an 0 Kn Ln := by
    refine ⟨fun t _ => ?_, fun x _ => ?_, fun t _ x _ => ?_, ?_⟩
    · refine LipschitzOnWith.of_dist_le_mul fun x₁ _ x₂ _ => ?_
      simp only [Real.dist_eq, f, Ln, NNReal.coe_mk]
      exact hLip _ _ _ (hψ01 t)
    · exact (hc.comp (continuous_const.prodMk hψc)).continuousOn
    · simp only [f, Real.norm_eq_abs, Kn, NNReal.coe_mk]
      exact hKb _ _ (hψ01 t)
    · simp only [an, Kn, NNReal.coe_mk, NNReal.coe_zero, sub_zero, t₀]
      rw [max_eq_left (by linarith)]
      exact le_rfl
  obtain ⟨α, hα⟩ := ODE.FunSpace.exists_isFixedPt_next hf (Metric.mem_closedBall_self le_rfl)
  refine ⟨(ODE.FunSpace.next hf (Metric.mem_closedBall_self le_rfl) α).compProj,
    ODE.FunSpace.continuous_compProj _, fun t ht => ?_⟩
  rw [ODE.FunSpace.compProj_apply, ODE.FunSpace.next_apply, hα, projIcc_of_mem _ ht]
  rfl

/-- The Euler scheme only sees the field on the region the states visit. -/
lemma euler_eq (g g' : ℝ → ℝ → ℝ) (R : ℝ) (hgg : ∀ x φ : ℝ, x ∈ Icc (-R) R → g' x φ = g x φ)
    (c : ℝ) (n : ℕ) (φs : ℕ → ℝ) (m : ℕ)
    (hmem : ∀ k ≤ m, eulerTraj g c n φs k ∈ Icc (-R) R) :
    ∀ k ≤ m, eulerTraj g' c n φs k = eulerTraj g c n φs k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    have e1 := ih (by omega)
    show eulerTraj g' c n φs k + g' (eulerTraj g' c n φs k) (φs k) / n =
      eulerTraj g c n φs k + g (eulerTraj g c n φs k) (φs k) / n
    rw [e1, hgg _ _ (hmem k (by omega))]

lemma payoff_eq (f f' g g' : ℝ → ℝ → ℝ) (R : ℝ)
    (hff : ∀ x φ : ℝ, x ∈ Icc (-R) R → f' x φ = f x φ)
    (hgg : ∀ x φ : ℝ, x ∈ Icc (-R) R → g' x φ = g x φ)
    (c : ℝ) (n : ℕ) (φs : ℕ → ℝ) (m : ℕ)
    (hmem : ∀ k ≤ m, eulerTraj g c n φs k ∈ Icc (-R) R) :
    discretePayoff f' g' c n φs m = discretePayoff f g c n φs m := by
  unfold discretePayoff
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  rw [euler_eq g g' R hgg c n φs m hmem k hk', hff _ _ (hmem k hk')]


/-- Uniform bounds for the discrete problems (states in `[0, M']`, payoffs bounded). -/
lemma discrete_bound (F G : ℝ → ℝ → ℝ) (hF : ContDiff ℝ 2 (fun z : ℝ × ℝ => F z.1 z.2))
    (p q r : ℝ)
    (hb : ∀ x φ : ℝ, 0 ≤ x → φ ∈ Icc (0:ℝ) 1 → p * x ≤ phiForm G x φ ∧ phiForm G x φ ≤ q * x + r)
    (c T : ℝ) (hc : 0 ≤ c) (hT : 0 ≤ T) :
    ∃ Kd : ℝ, ∀ n : ℕ, 1 ≤ n → |p| ≤ n → ∀ φs : ℕ → ℝ,
      (∀ k ≤ horizonSteps T n, φs k ∈ Icc (0:ℝ) 1) →
      (∀ k ≤ horizonSteps T n, eulerTraj (phiForm G) c n φs k ∈
        Icc 0 ((c + |r| * (T + 1)) * Real.exp (|q| * (T + 1)))) ∧
      |discretePayoff (phiForm F) (phiForm G) c n φs (horizonSteps T n)| ≤ Kd := by
  set M' := (c + |r| * (T + 1)) * Real.exp (|q| * (T + 1)) with hM'
  obtain ⟨Lf, Kf, -, hKf0, -, hKf⟩ := box_lip F hF M'
  refine ⟨(T + 1) * Kf, fun n hn hpn φs hφs => ?_⟩
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  set N := horizonSteps T n
  have hN1 : (N : ℝ) ≤ T * n := Nat.floor_le (by positivity)
  have hst := euler_apriori (phiForm G) p q r hb c hc n hpn hn φs N
    (fun k hk => hφs k hk.le)
  have hmem : ∀ k ≤ N, eulerTraj (phiForm G) c n φs k ∈ Icc 0 M' := by
    intro k hk
    obtain ⟨h0, h1⟩ := hst k hk
    have hkT : (k : ℝ) / n ≤ T + 1 := by
      rw [div_le_iff₀ hnpos]
      have : (k : ℝ) ≤ N := by exact_mod_cast hk
      nlinarith
    have e1 : |r| * k / n ≤ |r| * (T + 1) := by
      rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left hkT (abs_nonneg _)
    have e2 : |q| * k / n ≤ |q| * (T + 1) := by
      rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left hkT (abs_nonneg _)
    refine ⟨h0, h1.trans ?_⟩
    exact mul_le_mul (by linarith) (Real.exp_le_exp.2 e2) (Real.exp_pos _).le
      (by positivity)
  refine ⟨hmem, ?_⟩
  have hM0 : 0 ≤ M' := by positivity
  unfold discretePayoff
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ k ∈ Finset.range (N + 1),
      |phiForm F (eulerTraj (phiForm G) c n φs k) (φs k) / n| ≤ Kf / n := by
    intro k hk
    have hk' : k ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    rw [abs_div, abs_of_pos hnpos]
    refine div_le_div_of_nonneg_right (hKf _ _ ?_ (hφs k hk')) hnpos.le
    exact ⟨by linarith [(hmem k hk').1], (hmem k hk').2⟩
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h1 : ((N + 1 : ℕ) : ℝ) / n ≤ T + 1 := by
    rw [div_le_iff₀ hnpos]; push_cast
    have : (1:ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  calc ((N + 1 : ℕ) : ℝ) * (Kf / n) = ((N + 1 : ℕ) : ℝ) / n * Kf := by ring
    _ ≤ (T + 1) * Kf := mul_le_mul_of_nonneg_right h1 hKf0


/-- The clamped `φ`-form field. -/
noncomputable def clampF (H : ℝ → ℝ → ℝ) (R x φ : ℝ) : ℝ := phiForm H (max (-R) (min x R)) φ

lemma clampF_eq (H : ℝ → ℝ → ℝ) (R x φ : ℝ) (hx : x ∈ Icc (-R) R) :
    clampF H R x φ = phiForm H x φ := by
  unfold clampF; rw [clamp_eq R x hx]

lemma clamp_cont (H : ℝ → ℝ → ℝ) (hH : ContDiff ℝ 2 (fun z : ℝ × ℝ => H z.1 z.2)) (R : ℝ) :
    Continuous (fun z : ℝ × ℝ => clampF H R z.1 z.2) := by
  have hcl : Continuous (fun z : ℝ × ℝ => max (-R) (min z.1 R)) :=
    continuous_const.max (continuous_fst.min continuous_const)
  exact hH.continuous.comp (hcl.prodMk (continuous_snd.mul hcl))

lemma clamp_pair (F G : ℝ → ℝ → ℝ) (hF : ContDiff ℝ 2 (fun z : ℝ × ℝ => F z.1 z.2))
    (hG : ContDiff ℝ 2 (fun z : ℝ × ℝ => G z.1 z.2)) (R : ℝ) (hR : 0 ≤ R) :
    ∃ L K : ℝ, 0 ≤ L ∧ 0 ≤ K ∧
      (∀ x₁ x₂ φ₁ φ₂ : ℝ, φ₁ ∈ Icc (0:ℝ) 1 → φ₂ ∈ Icc (0:ℝ) 1 →
        |clampF F R x₁ φ₁ - clampF F R x₂ φ₂| ≤ L * (|x₁ - x₂| + |φ₁ - φ₂|)) ∧
      (∀ x₁ x₂ φ₁ φ₂ : ℝ, φ₁ ∈ Icc (0:ℝ) 1 → φ₂ ∈ Icc (0:ℝ) 1 →
        |clampF G R x₁ φ₁ - clampF G R x₂ φ₂| ≤ L * (|x₁ - x₂| + |φ₁ - φ₂|)) ∧
      (∀ x φ : ℝ, φ ∈ Icc (0:ℝ) 1 → |clampF F R x φ| ≤ K) ∧
      (∀ x φ : ℝ, φ ∈ Icc (0:ℝ) 1 → |clampF G R x φ| ≤ K) := by
  obtain ⟨L1, K1, hL1, hK1, hl1, hk1⟩ := box_lip F hF R
  obtain ⟨L2, K2, hL2, hK2, hl2, hk2⟩ := box_lip G hG R
  have hlF : ∀ x₁ x₂ φ₁ φ₂ : ℝ, x₁ ∈ Icc (-R) R → x₂ ∈ Icc (-R) R → φ₁ ∈ Icc (0:ℝ) 1 →
      φ₂ ∈ Icc (0:ℝ) 1 → |phiForm F x₁ φ₁ - phiForm F x₂ φ₂| ≤
        max L1 L2 * (|x₁ - x₂| + |φ₁ - φ₂|) := fun a b u v ha hb hu hv =>
    (hl1 a b u v ha hb hu hv).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hlG : ∀ x₁ x₂ φ₁ φ₂ : ℝ, x₁ ∈ Icc (-R) R → x₂ ∈ Icc (-R) R → φ₁ ∈ Icc (0:ℝ) 1 →
      φ₂ ∈ Icc (0:ℝ) 1 → |phiForm G x₁ φ₁ - phiForm G x₂ φ₂| ≤
        max L1 L2 * (|x₁ - x₂| + |φ₁ - φ₂|) := fun a b u v ha hb hu hv =>
    (hl2 a b u v ha hb hu hv).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  have hkF : ∀ x φ : ℝ, x ∈ Icc (-R) R → φ ∈ Icc (0:ℝ) 1 → |phiForm F x φ| ≤ max K1 K2 :=
    fun a u ha hu => (hk1 a u ha hu).trans (le_max_left _ _)
  have hkG : ∀ x φ : ℝ, x ∈ Icc (-R) R → φ ∈ Icc (0:ℝ) 1 → |phiForm G x φ| ≤ max K1 K2 :=
    fun a u ha hu => (hk2 a u ha hu).trans (le_max_right _ _)
  obtain ⟨cF1, cF2⟩ := clamp_field (phiForm F) R (max L1 L2) (max K1 K2) hR hlF
    (le_max_of_le_left hL1) hkF
  obtain ⟨cG1, cG2⟩ := clamp_field (phiForm G) R (max L1 L2) (max K1 K2) hR hlG
    (le_max_of_le_left hL1) hkG
  exact ⟨max L1 L2, max K1 K2, le_max_of_le_left hL1, le_max_of_le_left hK1, cF1, cG1, cF2, cG2⟩

lemma ii_abs_sub (T : ℝ) (hT : 0 ≤ T) (a b : ℝ → ℝ) (ha : Measurable a) (hb : Measurable b)
    (ha1 : ∀ t ∈ Icc 0 T, a t ∈ Icc (0:ℝ) 1) (hb1 : ∀ t ∈ Icc 0 T, b t ∈ Icc (0:ℝ) 1) :
    IntervalIntegrable (fun t => |a t - b t|) volume 0 T := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hT]
  refine Measure.integrableOn_of_bounded (M := 1) (by simp [Real.volume_Icc])
    ((continuous_abs.measurable.comp (ha.sub hb)).aestronglyMeasurable) ?_
  refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun t ht => ?_)
  have h1 := ha1 t ht
  have h2 := hb1 t ht
  rw [Real.norm_eq_abs, abs_abs, abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

lemma step_meas (n : ℕ) (φs : ℕ → ℝ) : Measurable (stepControl n φs) := by
  unfold stepControl
  exact (measurable_from_nat (f := φs)).comp (Nat.measurable_floor.comp (measurable_id.mul_const _))

lemma n0_spec (p : ℝ) (n : ℕ) (hn : max 1 ⌈|p|⌉₊ ≤ n) : 1 ≤ n ∧ |p| ≤ n :=
  ⟨le_of_max_le_left hn, (Nat.le_ceil _).trans (by exact_mod_cast le_of_max_le_right hn)⟩

lemma dv_le (F G : ℝ → ℝ → ℝ) (c T : ℝ) (n : ℕ) (a : ℝ)
    (h : ∀ φs : ℕ → ℝ, (∀ k ≤ horizonSteps T n, φs k ∈ Icc (0:ℝ) 1) →
      discretePayoff F G c n φs (horizonSteps T n) ≤ a) :
    discreteValue F G c T n ≤ a := by
  unfold discreteValue
  refine csSup_le ⟨_, fun _ => 0, fun _ _ => ⟨le_rfl, zero_le_one⟩, rfl⟩ ?_
  rintro _ ⟨φs, hφs, rfl⟩
  exact h φs hφs

lemma dv_ge (F G : ℝ → ℝ → ℝ) (c T : ℝ) (n : ℕ) (K : ℝ)
    (hK : ∀ φs : ℕ → ℝ, (∀ k ≤ horizonSteps T n, φs k ∈ Icc (0:ℝ) 1) →
      discretePayoff F G c n φs (horizonSteps T n) ≤ K)
    (φs : ℕ → ℝ) (hφs : ∀ k ≤ horizonSteps T n, φs k ∈ Icc (0:ℝ) 1) :
    discretePayoff F G c n φs (horizonSteps T n) ≤ discreteValue F G c T n := by
  unfold discreteValue
  refine le_csSup ⟨K, ?_⟩ ⟨φs, hφs, rfl⟩
  rintro _ ⟨ψs, hψs, rfl⟩
  exact hK ψs hψs

/-- Lower comparison: every continuous payoff is almost attained by the discrete problems. -/
lemma lower (F G : ℝ → ℝ → ℝ) (hF : ContDiff ℝ 2 (fun z : ℝ × ℝ => F z.1 z.2))
    (hG : ContDiff ℝ 2 (fun z : ℝ × ℝ => G z.1 z.2)) (p q r : ℝ)
    (hb : ∀ x φ : ℝ, 0 ≤ x → φ ∈ Icc (0:ℝ) 1 → p * x ≤ phiForm G x φ ∧ phiForm G x φ ≤ q * x + r)
    (c T : ℝ) (hc : 0 ≤ c) (hT : 0 ≤ T) (J : ℝ)
    (hJ : J ∈ contPayoffs (phiForm F) (phiForm G) c T) (ε : ℝ) (hε : 0 < ε) :
    ∃ n₁ : ℕ, ∀ n : ℕ, n₁ ≤ n → ∃ φs : ℕ → ℝ, (∀ k ≤ horizonSteps T n, φs k ∈ Icc (0:ℝ) 1) ∧
      J - ε ≤ discretePayoff (phiForm F) (phiForm G) c n φs (horizonSteps T n) := by
  obtain ⟨φ, x, hφm, hφ01, ⟨hxc, hxi, hxeq⟩, hfi, rfl⟩ := hJ
  obtain ⟨Kd, hDB⟩ := discrete_bound F G hF p q r hb c T hc hT
  set M' := (c + |r| * (T + 1)) * Real.exp (|q| * (T + 1)) with hM'
  have hM0 : 0 ≤ M' := by positivity
  obtain ⟨Rx, hRx⟩ := isCompact_Icc.exists_bound_of_continuousOn hxc
  set R := max Rx M' with hRdef
  have hR : 0 ≤ R := le_max_of_le_right hM0
  obtain ⟨L, K, hL, hK, hLf, hLg, hKf, hKg⟩ := clamp_pair F G hF hG R hR
  obtain ⟨B, hB0, hB⟩ := euler_compare (clampF G R) (clampF F R) L K hL hK hLg hLf hKg hKf T hT
  have hxR : ∀ t ∈ Icc 0 T, x t ∈ Icc (-R) R := fun t ht => by
    have h := hRx t ht
    rw [Real.norm_eq_abs] at h
    have h2 : Rx ≤ R := le_max_left _ _
    exact ⟨by linarith [neg_abs_le (x t)], by linarith [le_abs_self (x t)]⟩
  have hsub : ∀ t ∈ Icc 0 T, uIcc 0 t ⊆ Icc 0 T := fun t ht s hs => by
    rw [uIcc_of_le ht.1] at hs
    exact ⟨hs.1, hs.2.trans ht.2⟩
  have hgg : EqOn (fun s => clampF G R (x s) (φ s)) (fun s => phiForm G (x s) (φ s)) (Icc 0 T) :=
    fun s hs => clampF_eq G R _ _ (hxR s hs)
  have hff : EqOn (fun s => clampF F R (x s) (φ s)) (fun s => phiForm F (x s) (φ s)) (Icc 0 T) :=
    fun s hs => clampF_eq F R _ _ (hxR s hs)
  have htraj : IsTrajectory (clampF G R) c φ T x := by
    refine ⟨hxc, hxi.congr_fun hgg.symm measurableSet_Icc, fun t ht => ?_⟩
    rw [hxeq t ht]
    congr 1
    exact intervalIntegral.integral_congr (hgg.symm.mono (hsub t ht))
  have hfi' : IntegrableOn (fun s => clampF F R (x s) (φ s)) (Icc 0 T) :=
    hfi.congr_fun hff.symm measurableSet_Icc
  have hJeq : ∫ s in (0:ℝ)..T, clampF F R (x s) (φ s) = ∫ s in (0:ℝ)..T, phiForm F (x s) (φ s) :=
    intervalIntegral.integral_congr (hff.mono (hsub T ⟨hT, le_rfl⟩))
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = ε / (4 * (B + 1)) := ⟨_, rfl⟩
  have hB1 : 4 * (B + 1) ≠ 0 := by
    have : (0:ℝ) < 4 * (B + 1) := by linarith
    exact this.ne'
  have hη : 0 < η := by rw [hηdef]; exact div_pos hε (by linarith)
  have hηε : η * (4 * (B + 1)) = ε := by rw [hηdef]; field_simp
  obtain ⟨ψ, hψc, hψ01, hψη⟩ := l1_approx T hT φ hφm hφ01 η hη
  obtain ⟨ns, hns⟩ := sample_l1 T hT ψ hψc η hη
  refine ⟨max (max 1 ⌈|p|⌉₊) (max ns ⌈1 / η⌉₊), fun n hn => ?_⟩
  obtain ⟨hn1, hpn⟩ := n0_spec p n (le_of_max_le_left hn)
  have hns' : ns ≤ n := le_of_max_le_left (le_of_max_le_right hn)
  have hnη : 1 / η ≤ n :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_of_max_le_right (le_of_max_le_right hn))
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn1
  have h1n : 1 / (n:ℝ) ≤ η := by rw [one_div_le hnpos hη]; exact hnη
  set φs : ℕ → ℝ := fun k => ψ (k / n) with hφsdef
  have hadm : ∀ k ≤ horizonSteps T n, φs k ∈ Icc (0:ℝ) 1 := fun k _ => hψ01 _
  refine ⟨φs, hadm, ?_⟩
  obtain ⟨-, hE⟩ := hB c n φ x φs hn1 hφm hφ01 htraj hfi' hadm
  have hstep01 : ∀ t ∈ Icc 0 T, stepControl n φs t ∈ Icc (0:ℝ) 1 := fun t _ => hψ01 _
  have hI : ∫ t in (0:ℝ)..T, |φ t - stepControl n φs t| ≤ 2 * η := by
    have hA := ii_abs_sub T hT φ ψ hφm hψc.measurable hφ01 (fun t _ => hψ01 t)
    have hC := ii_abs_sub T hT ψ (stepControl n φs) hψc.measurable (step_meas n φs)
      (fun t _ => hψ01 t) hstep01
    have hD := ii_abs_sub T hT φ (stepControl n φs) hφm (step_meas n φs) hφ01 hstep01
    calc ∫ t in (0:ℝ)..T, |φ t - stepControl n φs t|
        ≤ ∫ t in (0:ℝ)..T, (|φ t - ψ t| + |ψ t - stepControl n φs t|) :=
          intervalIntegral.integral_mono_on hT hD (hA.add hC) (fun t _ => abs_sub_le _ _ _)
      _ = (∫ t in (0:ℝ)..T, |φ t - ψ t|) + ∫ t in (0:ℝ)..T, |ψ t - stepControl n φs t| :=
          intervalIntegral.integral_add hA hC
      _ ≤ η + η := add_le_add hψη (hns n hns')
      _ = 2 * η := by ring
  have hmem : ∀ k ≤ horizonSteps T n, eulerTraj (phiForm G) c n φs k ∈ Icc (-R) R :=
    fun k hk => by
      have h := (hDB n hn1 hpn φs hadm).1 k hk
      exact ⟨by linarith [h.1], h.2.trans (le_max_right _ _)⟩
  rw [← payoff_eq (phiForm F) (clampF F R) (phiForm G) (clampF G R) R
    (fun x φ hx => clampF_eq F R x φ hx) (fun x φ hx => clampF_eq G R x φ hx) c n φs _ hmem,
    ← hJeq]
  have hBI : B * (1 / n + ∫ t in (0:ℝ)..T, |φ t - stepControl n φs t|) ≤ ε := by
    have h3 : 1 / (n:ℝ) + ∫ t in (0:ℝ)..T, |φ t - stepControl n φs t| ≤ 3 * η := by linarith
    calc _ ≤ B * (3 * η) := mul_le_mul_of_nonneg_left h3 hB0
      _ ≤ ε := by nlinarith [mul_nonneg hB0 hη.le, hηε]
  linarith [(abs_le.1 hE).1]

/-- Upper comparison: every discrete payoff is almost bounded by a continuous payoff. -/
lemma upper (F G : ℝ → ℝ → ℝ) (hF : ContDiff ℝ 2 (fun z : ℝ × ℝ => F z.1 z.2))
    (hG : ContDiff ℝ 2 (fun z : ℝ × ℝ => G z.1 z.2)) (p q r : ℝ)
    (hb : ∀ x φ : ℝ, 0 ≤ x → φ ∈ Icc (0:ℝ) 1 → p * x ≤ phiForm G x φ ∧ phiForm G x φ ≤ q * x + r)
    (c T : ℝ) (hc : 0 ≤ c) (hT : 0 ≤ T) (ε : ℝ) (hε : 0 < ε) :
    ∃ n₃ : ℕ, ∀ n : ℕ, n₃ ≤ n → ∀ φs : ℕ → ℝ, (∀ k ≤ horizonSteps T n, φs k ∈ Icc (0:ℝ) 1) →
      ∃ J ∈ contPayoffs (phiForm F) (phiForm G) c T,
        discretePayoff (phiForm F) (phiForm G) c n φs (horizonSteps T n) ≤ J + ε := by
  obtain ⟨Kd, hDB⟩ := discrete_bound F G hF p q r hb c T hc hT
  set M' := (c + |r| * (T + 1)) * Real.exp (|q| * (T + 1)) with hM'
  have hM0 : 0 ≤ M' := by positivity
  set R := M' + 1 with hRdef
  have hR : 0 ≤ R := by linarith
  obtain ⟨L, K, hL, hK, hLf, hLg, hKf, hKg⟩ := clamp_pair F G hF hG R hR
  obtain ⟨B, hB0, hB⟩ := euler_compare (clampF G R) (clampF F R) L K hL hK hLg hLf hKg hKf T hT
  set A := 2 * B + K with hA
  have hA0 : 0 ≤ A := by rw [hA]; linarith
  refine ⟨max (max 1 ⌈|p|⌉₊) (max ⌈A⌉₊ ⌈A / ε⌉₊), fun n hn φs hφs => ?_⟩
  obtain ⟨hn1, hpn⟩ := n0_spec p n (le_of_max_le_left hn)
  have hnA : A ≤ n :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_of_max_le_left (le_of_max_le_right hn))
  have hnAε : A / ε ≤ n :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_of_max_le_right (le_of_max_le_right hn))
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn1
  have hAn1 : A / n ≤ 1 := by rw [div_le_iff₀ hnpos]; linarith
  have hAnε : A / n ≤ ε := by
    rw [div_le_iff₀ hε] at hnAε
    rw [div_le_iff₀ hnpos]; linarith
  have hstep01 : ∀ t ∈ Icc 0 T, stepControl n φs t ∈ Icc (0:ℝ) 1 := fun t ht =>
    hφs _ (Nat.floor_mono (mul_le_mul_of_nonneg_right ht.2 hnpos.le))
  obtain ⟨ψ, hψc, hψ01, hψI⟩ := l1_approx T hT (stepControl n φs) (step_meas n φs) hstep01
    (1 / n) (one_div_pos.2 hnpos)
  have hLx : ∀ x₁ x₂ φ : ℝ, φ ∈ Icc (0:ℝ) 1 →
      |clampF G R x₁ φ - clampF G R x₂ φ| ≤ L * |x₁ - x₂| := fun x₁ x₂ φ hφ => by
    have := hLg x₁ x₂ φ φ hφ hφ
    simpa only [sub_self, abs_zero, add_zero] using this
  obtain ⟨y, hyc, hyeq⟩ := exists_traj (clampF G R) (clamp_cont G hG R) L K hL hK hLx hKg T hT c
    ψ hψc hψ01
  have hgyc : Continuous (fun s => clampF G R (y s) (ψ s)) :=
    (clamp_cont G hG R).comp (hyc.prodMk hψc)
  have hfyc : Continuous (fun s => clampF F R (y s) (ψ s)) :=
    (clamp_cont F hF R).comp (hyc.prodMk hψc)
  have htraj : IsTrajectory (clampF G R) c ψ T y := ⟨hyc.continuousOn, hgyc.integrableOn_Icc, hyeq⟩
  obtain ⟨hE1, hE2⟩ := hB c n ψ y φs hn1 hψc.measurable (fun t _ => hψ01 t) htraj
    hfyc.integrableOn_Icc hφs
  have hI : ∫ t in (0:ℝ)..T, |ψ t - stepControl n φs t| ≤ 1 / n := by
    rw [intervalIntegral.integral_congr (g := fun t => |stepControl n φs t - ψ t|)
      (fun t _ => abs_sub_comm _ _)]
    exact hψI
  have hBn : B * (1 / n + ∫ t in (0:ℝ)..T, |ψ t - stepControl n φs t|) ≤ 2 * B / n := by
    calc _ ≤ B * (1 / n + 1 / n) := mul_le_mul_of_nonneg_left (by linarith) hB0
      _ = 2 * B / n := by ring
  have h2B : 2 * B / n ≤ A / n := div_le_div_of_nonneg_right (by rw [hA]; linarith) hnpos.le
  have hDBn := hDB n hn1 hpn φs hφs
  have hmem : ∀ k ≤ horizonSteps T n, eulerTraj (phiForm G) c n φs k ∈ Icc (-R) R :=
    fun k hk => ⟨by linarith [(hDBn.1 k hk).1], (hDBn.1 k hk).2.trans (by linarith)⟩
  have heul := euler_eq (phiForm G) (clampF G R) R (fun x φ hx => clampF_eq G R x φ hx) c n φs _
    hmem
  have hyR : ∀ t ∈ Icc 0 T, y t ∈ Icc (-R) R := by
    intro t ht
    have ht0 : 0 ≤ t * n := mul_nonneg ht.1 hnpos.le
    have hk : ⌊t * n⌋₊ ≤ horizonSteps T n :=
      Nat.floor_mono (mul_le_mul_of_nonneg_right ht.2 hnpos.le)
    have hkle : (⌊t * n⌋₊ : ℝ) / n ≤ t := by rw [div_le_iff₀ hnpos]; exact Nat.floor_le ht0
    have hklt : t < ((⌊t * n⌋₊ : ℝ) + 1) / n := by
      rw [lt_div_iff₀ hnpos]; exact Nat.lt_floor_add_one _
    have hk0 : 0 ≤ (⌊t * n⌋₊ : ℝ) / n := by positivity
    have hkT : (⌊t * n⌋₊ : ℝ) / n ∈ Icc 0 T := ⟨hk0, hkle.trans ht.2⟩
    have e1 := hE1 _ hk
    rw [heul _ hk] at e1
    have e2 : |y t - y ((⌊t * n⌋₊ : ℝ) / n)| ≤ K * (1 / n) := by
      rw [hyeq t ht, hyeq _ hkT, add_sub_add_left_eq_sub,
        intervalIntegral.integral_interval_sub_left (hgyc.intervalIntegrable _ _)
          (hgyc.intervalIntegrable _ _), ← Real.norm_eq_abs]
      refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := K) fun s _ => ?_).trans ?_
      · rw [Real.norm_eq_abs]; exact hKg _ _ (hψ01 s)
      · rw [abs_of_nonneg (sub_nonneg.2 hkle)]
        refine mul_le_mul_of_nonneg_left ?_ hK
        have : ((⌊t * n⌋₊ : ℝ) + 1) / n = (⌊t * n⌋₊ : ℝ) / n + 1 / n := by ring
        linarith
    have hX := hDBn.1 _ hk
    have hBA : B * (1 / n + ∫ t in (0:ℝ)..T, |ψ t - stepControl n φs t|) ≤
        A / n - K * (1 / n) := by
      have : A / n - K * (1 / n) = 2 * B / n := by rw [hA]; ring
      rw [this]; exact hBn
    rw [abs_le] at e1 e2
    constructor <;> linarith [hX.1, hX.2, e1.1, e1.2, e2.1, e2.2]
  have hsub : ∀ t ∈ Icc 0 T, uIcc 0 t ⊆ Icc 0 T := fun t ht s hs => by
    rw [uIcc_of_le ht.1] at hs
    exact ⟨hs.1, hs.2.trans ht.2⟩
  have hgg : EqOn (fun s => clampF G R (y s) (ψ s)) (fun s => phiForm G (y s) (ψ s)) (Icc 0 T) :=
    fun s hs => clampF_eq G R _ _ (hyR s hs)
  have hff : EqOn (fun s => clampF F R (y s) (ψ s)) (fun s => phiForm F (y s) (ψ s)) (Icc 0 T) :=
    fun s hs => clampF_eq F R _ _ (hyR s hs)
  refine ⟨∫ t in (0:ℝ)..T, phiForm F (y t) (ψ t), ⟨ψ, y, hψc.measurable, fun t _ => hψ01 t,
    ⟨hyc.continuousOn, hgyc.integrableOn_Icc.congr_fun hgg measurableSet_Icc, fun t ht => ?_⟩,
    hfyc.integrableOn_Icc.congr_fun hff measurableSet_Icc, rfl⟩, ?_⟩
  · rw [hyeq t ht]
    congr 1
    exact intervalIntegral.integral_congr (hgg.mono (hsub t ht))
  · rw [← payoff_eq (phiForm F) (clampF F R) (phiForm G) (clampF G R) R
      (fun x φ hx => clampF_eq F R x φ hx) (fun x φ hx => clampF_eq G R x φ hx) c n φs _ hmem,
      ← intervalIntegral.integral_congr (hff.mono (hsub T ⟨hT, le_rfl⟩))]
    linarith [(abs_le.1 hE2).2]

end FadAux

open BellmanDP.Variational Filter Topology in
theorem solution (F G : ℝ → ℝ → ℝ) (hFG : Assumptions11 F G)
    (c T : ℝ) (hc : 0 ≤ c) (hT : 0 < T) :
    (contPayoffs (phiForm F) (phiForm G) c T).Nonempty ∧
      BddAbove (contPayoffs (phiForm F) (phiForm G) c T) ∧
      Tendsto (fun n : ℕ => discreteValue (phiForm F) (phiForm G) c T n) atTop
        (𝓝 (contValue (phiForm F) (phiForm G) c T)) := by
  obtain ⟨hF, hG, ⟨p, q, r, hpqr⟩, -⟩ := hFG
  have hb := FadAux.phi_bounds G hG.continuous p q r hpqr
  have hT0 : 0 ≤ T := hT.le
  obtain ⟨Kd, hDB⟩ := FadAux.discrete_bound F G hF p q r hb c T hc hT0
  have hne : (contPayoffs (phiForm F) (phiForm G) c T).Nonempty := by
    obtain ⟨n₃, hn₃⟩ := FadAux.upper F G hF hG p q r hb c T hc hT0 1 one_pos
    obtain ⟨J, hJ, -⟩ := hn₃ n₃ le_rfl (fun _ => 0) (fun _ _ => ⟨le_rfl, zero_le_one⟩)
    exact ⟨J, hJ⟩
  have hbdd : BddAbove (contPayoffs (phiForm F) (phiForm G) c T) := by
    refine ⟨Kd + 1, fun J hJ => ?_⟩
    obtain ⟨n₁, hn₁⟩ := FadAux.lower F G hF hG p q r hb c T hc hT0 J hJ 1 one_pos
    obtain ⟨hn1, hpn⟩ := FadAux.n0_spec p (max n₁ (max 1 ⌈|p|⌉₊)) (le_max_right _ _)
    obtain ⟨φs, hφs, hJφ⟩ := hn₁ (max n₁ (max 1 ⌈|p|⌉₊)) (le_max_left _ _)
    have := (abs_le.1 ((hDB _ hn1 hpn φs hφs).2)).2
    linarith
  refine ⟨hne, hbdd, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨n₃, hn₃⟩ := FadAux.upper F G hF hG p q r hb c T hc hT0 (ε / 2) (by positivity)
  obtain ⟨J₀, hJ₀, hJ₀lt⟩ := exists_lt_of_lt_csSup hne
    (show contValue (phiForm F) (phiForm G) c T - ε / 2 < contValue (phiForm F) (phiForm G) c T
      by linarith)
  obtain ⟨n₁, hn₁⟩ := FadAux.lower F G hF hG p q r hb c T hc hT0 J₀ hJ₀ (ε / 2) (by positivity)
  refine ⟨max (max n₁ n₃) (max 1 ⌈|p|⌉₊), fun n hn => ?_⟩
  obtain ⟨hn1, hpn⟩ := FadAux.n0_spec p n (le_of_max_le_right hn)
  have hup : discreteValue (phiForm F) (phiForm G) c T n ≤
      contValue (phiForm F) (phiForm G) c T + ε / 2 := by
    refine FadAux.dv_le _ _ c T n _ fun φs hφs => ?_
    obtain ⟨J, hJ, hle⟩ := hn₃ n (le_of_max_le_right (le_of_max_le_left hn)) φs hφs
    have := le_csSup hbdd hJ
    unfold contValue
    linarith
  have hlo : contValue (phiForm F) (phiForm G) c T - ε <
      discreteValue (phiForm F) (phiForm G) c T n := by
    obtain ⟨φs, hφs, hge⟩ := hn₁ n (le_of_max_le_left (le_of_max_le_left hn))
    have := FadAux.dv_ge _ _ c T n Kd
      (fun ψs hψs => (abs_le.1 ((hDB n hn1 hpn ψs hψs).2)).2) φs hφs
    linarith
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith
