-- Prove2me | solution 1 for ChanceStateCtrl.General.theorem_2_2_e_lipschitz_moderate
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T07:31:25.094159+00:00
-- url     : https://prove2.me/submissions/e19efe0c-3c71-48f8-a64e-5020fd929970

import Mathlib
import Definitions.Def_ChanceStateCtrl_General_Setting
import Definitions.Def_ChanceStateCtrl_General_Radial
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped MatrixOrder Pointwise

namespace S163

open ChanceStateCtrl.General

lemma sqrtCov_inj {m : ℕ} (Sigma : Matrix (Fin m) (Fin m) ℝ) (hS : Sigma.PosDef)
    (x : EuclideanSpace ℝ (Fin m)) (hx : sqrtCov Sigma x = 0) : x = 0 := by
  have h0 : (0 : Matrix (Fin m) (Fin m) ℝ) ≤ Sigma := hS.posSemidef.nonneg
  have hmul : CFC.sqrt Sigma * CFC.sqrt Sigma = Sigma := CFC.sqrt_mul_sqrt_self Sigma h0
  have h2 : Matrix.toEuclideanCLM (𝕜 := ℝ) Sigma x = 0 := by
    rw [← hmul, map_mul]
    change sqrtCov Sigma (sqrtCov Sigma x) = 0
    rw [hx, map_zero]
  by_contra hne
  have hne' : WithLp.ofLp x ≠ 0 := by
    intro h; apply hne; exact (WithLp.ofLp_eq_zero 2).mp h
  have := hS.dotProduct_mulVec_pos hne'
  have h3 : Sigma.mulVec (WithLp.ofLp x) = 0 := by
    rw [← Matrix.ofLp_toEuclideanCLM, h2]; rfl
  rw [h3] at this; simp at this

lemma sqrtCov_lower {m : ℕ} (Sigma : Matrix (Fin m) (Fin m) ℝ) (hS : Sigma.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
      c ≤ ‖sqrtCov Sigma (v : EuclideanSpace ℝ (Fin m))‖ := by
  rcases (Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1).eq_empty_or_nonempty with h | h
  · refine ⟨1, one_pos, fun v => ?_⟩
    obtain ⟨x, hx⟩ := v; rw [h] at hx; exact hx.elim
  obtain ⟨x0, hx0, hmin⟩ := (isCompact_sphere (0 : EuclideanSpace ℝ (Fin m)) 1).exists_isMinOn h
    ((sqrtCov Sigma).continuous.norm.continuousOn)
  refine ⟨‖sqrtCov Sigma x0‖, ?_, fun v => hmin v.2⟩
  rw [norm_pos_iff]
  intro h0
  have := sqrtCov_inj Sigma hS x0 h0
  rw [this] at hx0; simp at hx0

end S163

namespace S163

lemma fin_pos_lb {ι : Type*} (t : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ t, 0 < f i) :
    ∃ ε > 0, ∀ i ∈ t, ε ≤ f i := by
  rcases t.eq_empty_or_nonempty with h | h
  · exact ⟨1, one_pos, by simp [h]⟩
  · refine ⟨t.inf' h f, (Finset.lt_inf'_iff h).2 hf, fun i hi => Finset.inf'_le f hi⟩

lemma unif_lip {U E : Type*} [PseudoMetricSpace U] [PseudoMetricSpace E] (F : U × E → ℝ)
    (hF : LocallyLipschitz F) (u0 : U) (K : Set E) (hK : IsCompact K) :
    ∃ ε > 0, ∃ L : ℝ, 0 ≤ L ∧ ∀ u ∈ Metric.ball u0 ε, ∀ u' ∈ Metric.ball u0 ε, ∀ z ∈ K,
      |F (u, z) - F (u', z)| ≤ L * dist u u' := by
  have key : ∀ z ∈ K, ∃ r > 0, ∃ L : NNReal, ∀ p ∈ Metric.ball u0 r ×ˢ Metric.ball z r,
      ∀ q ∈ Metric.ball u0 r ×ˢ Metric.ball z r, dist (F p) (F q) ≤ L * dist p q := by
    intro z _
    obtain ⟨L, t, ht, hlip⟩ := hF (u0, z)
    obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.1 ht
    refine ⟨r, hr, L, fun p hp q hq => ?_⟩
    rw [← ball_prod_same] at hsub
    exact hlip.dist_le_mul p (hsub hp) q (hsub hq)
  choose r hr L hL using key
  obtain ⟨t, ht⟩ := hK.elim_nhds_subcover' (fun z hz => Metric.ball z (r z hz))
    (fun z hz => Metric.ball_mem_nhds z (hr z hz))
  obtain ⟨ε, hε, hεle⟩ := fin_pos_lb t (fun x => r x.1 x.2) (fun x _ => hr x.1 x.2)
  refine ⟨ε, hε, ∑ x ∈ t, (L x.1 x.2 : ℝ), Finset.sum_nonneg (fun _ _ => NNReal.coe_nonneg _),
    fun u hu u' hu' z hz => ?_⟩
  have hz' := ht hz
  simp only [Set.mem_iUnion] at hz'
  obtain ⟨x, hxt, hzx⟩ := hz'
  have hrx := hεle x hxt
  have hu1 : u ∈ Metric.ball u0 (r x.1 x.2) := Metric.ball_subset_ball hrx hu
  have hu2 : u' ∈ Metric.ball u0 (r x.1 x.2) := Metric.ball_subset_ball hrx hu'
  have := hL x.1 x.2 (u, z) ⟨hu1, hzx⟩ (u', z) ⟨hu2, hzx⟩
  rw [Real.dist_eq, Prod.dist_eq, dist_self, max_eq_left dist_nonneg] at this
  refine this.trans (mul_le_mul_of_nonneg_right ?_ dist_nonneg)
  exact Finset.single_le_sum (f := fun x : K => (L x.1 x.2 : ℝ))
    (fun _ _ => NNReal.coe_nonneg _) hxt

end S163

namespace S163
lemma conv_aux {E : Type*} [AddCommGroup E] [Module ℝ E] (f : E → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (z : E) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    f (t • z) ≤ t * f z + (1 - t) * f 0 := by
  have := hf.2 (Set.mem_univ z) (Set.mem_univ 0) h0 (by linarith : 0 ≤ 1 - t) (by ring)
  simpa using this

end S163

namespace S164
open ChanceStateCtrl.General

lemma clarke_bound {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] (f : U → ℝ)
    (hf : LocallyLipschitz f) (y h : U) (r : ℝ) (hr : clarkeDir f y h < r) :
    ∀ᶠ τ in 𝓝[>] (0 : ℝ), (f (y + τ • h) - f y) / τ < r := by
  obtain ⟨K, t, ht, hK⟩ := hf y
  have hcont : Tendsto (fun q : U × ℝ => q.1 + q.2 • h) (𝓝 y ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 y) := by
    have : Tendsto (fun q : U × ℝ => q.1 + q.2 • h) (𝓝 (y, (0:ℝ))) (𝓝 (y + (0:ℝ) • h)) :=
      (continuous_fst.add (continuous_snd.smul continuous_const)).tendsto _
    rw [zero_smul, add_zero] at this
    refine this.mono_left ?_
    rw [nhds_prod_eq]; exact Filter.prod_mono le_rfl nhdsWithin_le_nhds
  have h1 : ∀ᶠ q : U × ℝ in 𝓝 y ×ˢ 𝓝[>] (0 : ℝ), q.1 ∈ t :=
    Filter.eventually_prod_iff.2 ⟨fun a => a ∈ t, ht, fun _ => True, univ_mem, fun ha _ _ => ha⟩
  have h2 : ∀ᶠ q : U × ℝ in 𝓝 y ×ˢ 𝓝[>] (0 : ℝ), q.1 + q.2 • h ∈ t := hcont ht
  have h3 : ∀ᶠ q : U × ℝ in 𝓝 y ×ˢ 𝓝[>] (0 : ℝ), 0 < q.2 :=
    Filter.eventually_prod_iff.2 ⟨fun _ => True, univ_mem, fun b => 0 < b, self_mem_nhdsWithin,
      fun {_} _ {_} hb => hb⟩
  have hbd : IsBoundedUnder (· ≤ ·) (𝓝 y ×ˢ 𝓝[>] (0 : ℝ))
      (fun q : U × ℝ => (f (q.1 + q.2 • h) - f q.1) / q.2) := by
    refine Filter.isBoundedUnder_of_eventually_le (a := K * ‖h‖) ?_
    filter_upwards [h1, h2, h3] with q hq1 hq2 hq3
    have := hK.dist_le_mul _ hq2 _ hq1
    rw [Real.dist_eq, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg hq3.le] at this
    rw [div_le_iff₀ hq3]
    calc _ ≤ |f (q.1 + q.2 • h) - f q.1| := le_abs_self _
      _ ≤ _ := this
      _ = _ := by ring
  have := eventually_lt_of_limsup_lt hr hbd
  exact this.curry.self_of_nhds

lemma clarke_lip {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] (f : U → ℝ)
    (hf : LocallyLipschitz f) (V : Set U) (hVc : Convex ℝ V) (M : ℝ)
    (hM : ∀ x ∈ V, ∀ h, clarkeDir f x h ≤ M * ‖h‖) :
    ∀ u ∈ V, ∀ u' ∈ V, f u' - f u ≤ M * ‖u' - u‖ := by
  intro u hu u' hu'
  set h := u' - u
  set φ : ℝ → ℝ := fun τ => f (u + τ • h)
  have hφc : Continuous φ :=
    hf.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))
  have key := image_le_of_liminf_slope_right_le_deriv_boundary (f := φ) (a := 0) (b := 1)
    hφc.continuousOn (B := fun τ => f u + M * ‖h‖ * τ) (B' := fun _ => M * ‖h‖)
    (by simp [φ]) (by fun_prop)
    (fun x _ => by
      simpa using ((hasDerivWithinAt_id x (Ici x)).const_mul (M * ‖h‖)).const_add (f u))
    (fun x hx r hr => by
      have hy : u + x • h ∈ V := hVc.add_smul_sub_mem hu hu' ⟨hx.1, hx.2.le⟩
      have hev := clarke_bound f hf (u + x • h) h r (lt_of_le_of_lt (hM _ hy h) hr)
      have htend : Tendsto (fun z : ℝ => z - x) (𝓝[>] x) (𝓝[>] 0) := by
        refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
        · have : Tendsto (fun z : ℝ => z - x) (𝓝 x) (𝓝 (x - x)) :=
            (continuous_id.sub continuous_const).tendsto x
          rw [sub_self] at this; exact this.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with z hz
          exact sub_pos.2 (mem_Ioi.1 hz)
      refine (Filter.Eventually.frequently ?_)
      filter_upwards [htend hev] with z hz
      rw [slope_def_field]
      simp only [φ]
      have : u + z • h = u + x • h + (z - x) • h := by rw [sub_smul]; abel
      rw [this]; exact hz)
  have := key (show (1:ℝ) ∈ Icc 0 1 by simp)
  simp [φ, h] at this; linarith


noncomputable def fch (m : ℕ) (t : ℝ) : ℝ := t ^ (m - 1) * Real.exp (-t ^ 2 / 2)

lemma fch_cont (m : ℕ) : Continuous (fch m) := by unfold fch; fun_prop

lemma M1 (m : ℕ) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    chiLaw m (Ioc a b) ≤ ENNReal.ofReal (|chiConst m| * ∫ t in a..b, fch m t) := by
  unfold chiLaw
  rw [withDensity_apply _ measurableSet_Ioc]
  have hint : IntegrableOn (fun t => |chiConst m| * fch m t) (Ioc a b) :=
    ((continuous_const.mul (fch_cont m)).continuousOn.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  calc ∫⁻ t in Ioc a b, ENNReal.ofReal (chiDensity m t)
      ≤ ∫⁻ t in Ioc a b, ENNReal.ofReal (|chiConst m| * fch m t) := by
        apply setLIntegral_mono' measurableSet_Ioc
        intro t ht
        apply ENNReal.ofReal_le_ofReal
        have ht0 : 0 ≤ t := ha.trans ht.1.le
        unfold chiDensity fch
        rw [if_pos ht0, mul_assoc]
        exact mul_le_mul_of_nonneg_right (le_abs_self _)
          (mul_nonneg (pow_nonneg ht0 _) (Real.exp_pos _).le)
    _ = ENNReal.ofReal (∫ t in Ioc a b, |chiConst m| * fch m t) := by
        rw [ofReal_integral_eq_lintegral_ofReal hint]
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        have ht0 : 0 ≤ t := ha.trans ht.1.le
        exact mul_nonneg (abs_nonneg _) (mul_nonneg (pow_nonneg ht0 _) (Real.exp_pos _).le)
    _ = _ := by
        rw [integral_const_mul, intervalIntegral.integral_of_le hab]

lemma M2 (m : ℕ) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, fch m t ≤ (b - a) * (b ^ (m - 1) * Real.exp (-a ^ 2 / 2)) := by
  have := intervalIntegral.integral_mono_on hab ((fch_cont m).intervalIntegrable (μ := volume) a b)
    (intervalIntegrable_const (c := b ^ (m - 1) * Real.exp (-a ^ 2 / 2)))
    (fun t ht => by
      unfold fch
      have ht0 : 0 ≤ t := ha.trans ht.1
      apply mul_le_mul (pow_le_pow_left₀ ht0 ht.2 _) _ (Real.exp_pos _).le
        (pow_nonneg (ha.trans hab) _)
      apply Real.exp_le_exp.2
      have : a ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ ha ht.1 2
      linarith)
  simp at this; linarith

lemma M3 (m : ℕ) (hm : 0 < m) (a b : ℝ) (ha : 0 ≤ a) (ha2 : (m : ℝ) + 1 ≤ a ^ 2) (hab : a ≤ b) :
    ∫ t in a..b, fch m t ≤ a ^ m * Real.exp (-a ^ 2 / 2) := by
  set G : ℝ → ℝ := fun t => -(t ^ m * Real.exp (-t ^ 2 / 2))
  set G' : ℝ → ℝ := fun t => -((m : ℝ) * t ^ (m - 1) * Real.exp (-t ^ 2 / 2) +
    t ^ m * (Real.exp (-t ^ 2 / 2) * (-(2 * t) / 2)))
  have hG : ∀ t, HasDerivAt G (G' t) t := by
    intro t
    have h1 := hasDerivAt_pow m t
    have h2 : HasDerivAt (fun t : ℝ => -t ^ 2 / 2) (-(2 * t) / 2) t := by
      have := ((hasDerivAt_pow 2 t).neg).div_const 2
      simpa using this
    exact (h1.mul h2.exp).neg
  have hG'c : Continuous G' := by simp only [G']; fun_prop
  have hle := intervalIntegral.integral_mono_on hab ((fch_cont m).intervalIntegrable (μ := volume) a b)
    (hG'c.intervalIntegrable (μ := volume) a b)
    (fun t ht => by
      have ht0 : 0 ≤ t := ha.trans ht.1
      have ht2 : a ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ ha ht.1 2
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      simp only [fch, G', Nat.add_sub_cancel]
      have hE := (Real.exp_pos (-t ^ 2 / 2)).le
      have hp := pow_nonneg ht0 k
      have : ((k + 1 : ℕ) : ℝ) + 1 ≤ t ^ 2 := ha2.trans ht2
      push_cast at this
      have e : t ^ (k + 1) * (Real.exp (-t ^ 2 / 2) * (-(2 * t) / 2)) =
          -(t ^ k * t ^ 2 * Real.exp (-t ^ 2 / 2)) := by ring
      rw [e]; push_cast
      have : t ^ k * Real.exp (-t ^ 2 / 2) * ((k:ℝ) + 2) ≤ t ^ k * Real.exp (-t ^ 2 / 2) * t ^ 2 :=
        mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hp hE)
      nlinarith)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hG t)
    (hG'c.intervalIntegrable (μ := volume) a b)] at hle
  have : 0 ≤ b ^ m * Real.exp (-b ^ 2 / 2) :=
    mul_nonneg (pow_nonneg (ha.trans hab) _) (Real.exp_pos _).le
  simp only [G] at hle
  linarith


lemma fch_int_nonneg (m : ℕ) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) : 0 ≤ ∫ t in a..b, fch m t :=
  intervalIntegral.integral_nonneg hab (fun t ht =>
    mul_nonneg (pow_nonneg (ha.trans ht.1) _) (Real.exp_pos _).le)

/-- Large-radius case. -/
lemma PLL (m : ℕ) (hm : 0 < m) (A δ d s r R0 : ℝ) (hA : 0 ≤ A) (hδ : 0 < δ) (hd : 0 ≤ d)
    (hR0 : 1 ≤ R0) (hR02 : (m : ℝ) + 1 ≤ R0 ^ 2) (hs : R0 ≤ s) (hsr : s ≤ r)
    (hkey : (r - s) * δ ≤ r * (A * δ * (s ^ m)⁻¹ * Real.exp (s ^ 2 / 2) * d)) :
    ∫ t in s..r, fch m t ≤ 2 ^ m * A * d := by
  have hs0 : 0 < s := lt_of_lt_of_le one_pos (hR0.trans hs)
  have hs2 : (m : ℝ) + 1 ≤ s ^ 2 := hR02.trans (pow_le_pow_left₀ (by linarith) hs 2)
  set E := Real.exp (s ^ 2 / 2) with hE
  have hEpos : 0 < E := Real.exp_pos _
  have hEinv : Real.exp (-s ^ 2 / 2) = E⁻¹ := by rw [hE, ← Real.exp_neg]; ring_nf
  have hsm : 0 < s ^ m := pow_pos hs0 m
  set X := A * (s ^ m)⁻¹ * E * d with hX
  have hX0 : 0 ≤ X := by positivity
  have hrs : r - s ≤ r * X := by
    have : (r - s) * δ ≤ (r * X) * δ := by rw [hX]; nlinarith
    exact le_of_mul_le_mul_right this hδ
  have h2m : (2 : ℝ) ≤ 2 ^ m := by
    calc (2:ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm
  have hAd : 0 ≤ A * d := mul_nonneg hA hd
  by_cases hXh : 1 / 2 ≤ X
  · have h3 := M3 m hm s r hs0.le hs2 hsr
    rw [hEinv] at h3
    have : s ^ m * E⁻¹ ≤ 2 * A * d := by
      rw [← div_eq_mul_inv, div_le_iff₀ hEpos]
      have : s ^ m * X = A * E * d := by rw [hX]; field_simp
      nlinarith
    nlinarith
  · push Not at hXh
    have hr2 : r ≤ 2 * s := by nlinarith
    have h2 := M2 m s r hs0.le hsr
    rw [hEinv] at h2
    have hrpow : r ^ (m - 1) ≤ 2 ^ (m - 1) * s ^ (m - 1) := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (hs0.le.trans hsr) hr2 _
    have hsm' : s ^ m = s * s ^ (m - 1) := by
      rw [← pow_succ']; congr 1; omega
    have h2m' : (2:ℝ) ^ m = 2 * 2 ^ (m - 1) := by
      rw [← pow_succ']; congr 1; omega
    -- (r - s) r^{m-1} E⁻¹ ≤ r X 2^{m-1} s^{m-1} E⁻¹ ≤ 2 s X 2^{m-1} s^{m-1} E⁻¹ = 2^m A d
    have hEi : 0 < E⁻¹ := inv_pos.2 hEpos
    have hsp : 0 ≤ s ^ (m - 1) := pow_nonneg hs0.le _
    have hrp : 0 ≤ r ^ (m - 1) := pow_nonneg (hs0.le.trans hsr) _
    have hstep1 : (r - s) * (r ^ (m - 1) * E⁻¹) ≤ (2 * s * X) * (2 ^ (m - 1) * s ^ (m - 1) * E⁻¹) := by
      apply mul_le_mul (by nlinarith) (mul_le_mul_of_nonneg_right hrpow hEi.le)
        (mul_nonneg hrp hEi.le) (by positivity)
    have hval : (2 * s * X) * (2 ^ (m - 1) * s ^ (m - 1) * E⁻¹) = 2 ^ m * A * d := by
      rw [hX, h2m']
      have : s * s ^ (m - 1) = s ^ m := hsm'.symm
      field_simp
      rw [← this]; ring
    linarith


lemma PLL' (m : ℕ) (hm : 0 < m) (A δ d R0 s r : ℝ) (G1 G2 : ℝ → ℝ) (hA : 0 ≤ A) (hδ : 0 < δ)
    (hd : 0 ≤ d) (hR0 : 1 ≤ R0) (hR02 : (m : ℝ) + 1 ≤ R0 ^ 2) (hs : R0 ≤ s) (hsr : s ≤ r)
    (hG1r : G1 r ≤ 0) (hG2s : 0 ≤ G2 s)
    (h1 : ∀ a b, 0 ≤ a → a ≤ b → 0 < b → G1 b ≤ 0 → G1 a ≤ -(1 - a / b) * δ)
    (hB : ∀ a, R0 ≤ a → G2 a ≤ G1 a + A * δ * (a ^ m)⁻¹ * Real.exp (a ^ 2 / 2) * d) :
    ∫ t in s..r, fch m t ≤ 2 ^ m * A * d := by
  have hs0 : 0 < s := lt_of_lt_of_le one_pos (hR0.trans hs)
  have hr0 : 0 < r := hs0.trans_le hsr
  apply PLL m hm A δ d s r R0 hA hδ hd hR0 hR02 hs hsr
  have e1 := h1 s r hs0.le hsr hr0 hG1r
  have e2 := hB s hs
  have : (1 - s / r) * r = r - s := by field_simp
  set Λ := A * δ * (s ^ m)⁻¹ * Real.exp (s ^ 2 / 2) * d
  have : (1 - s / r) * δ ≤ Λ := by linarith
  have := mul_le_mul_of_nonneg_left this hr0.le
  nlinarith

lemma PL (m : ℕ) (hm : 0 < m) (A δ d L R0 s r : ℝ) (G1 G2 : ℝ → ℝ) (hA : 0 ≤ A) (hδ : 0 < δ)
    (hd : 0 ≤ d) (hL : 0 ≤ L) (hR0 : 1 ≤ R0) (hR02 : (m : ℝ) + 1 ≤ R0 ^ 2) (hs0 : 0 ≤ s)
    (hsr : s ≤ r) (hG1r : G1 r ≤ 0) (hG2s : 0 ≤ G2 s)
    (h1 : ∀ a b, 0 ≤ a → a ≤ b → 0 < b → G1 b ≤ 0 → G1 a ≤ -(1 - a / b) * δ)
    (hup : ∀ a b, 0 ≤ a → a ≤ b → 0 ≤ G2 a → 0 ≤ G2 b)
    (hS : ∀ a, 0 ≤ a → a ≤ R0 → G2 a ≤ G1 a + L * d)
    (hB : ∀ a, R0 ≤ a → G2 a ≤ G1 a + A * δ * (a ^ m)⁻¹ * Real.exp (a ^ 2 / 2) * d) :
    ∫ t in s..r, fch m t ≤ (R0 ^ m * L / δ + 2 ^ m * A) * d := by
  have hR0p : 0 < R0 := lt_of_lt_of_le one_pos hR0
  have hpos2 : 0 ≤ 2 ^ m * A * d := by positivity
  have hpos1 : 0 ≤ R0 ^ m * L / δ * d := by positivity
  by_cases hsR : R0 ≤ s
  · have := PLL' m hm A δ d R0 s r G1 G2 hA hδ hd hR0 hR02 hsR hsr hG1r hG2s h1 hB
    nlinarith
  push Not at hsR
  set r1 := min r R0 with hr1
  have hsr1 : s ≤ r1 := le_min hsr hsR.le
  have hr1R : r1 ≤ R0 := min_le_right _ _
  have hr1r : r1 ≤ r := min_le_left _ _
  -- first piece
  have hI1 : ∫ t in s..r1, fch m t ≤ R0 ^ m * L / δ * d := by
    rcases hsr1.eq_or_lt with h | h
    · rw [h, intervalIntegral.integral_same]; exact hpos1
    have hr1p : 0 < r1 := hs0.trans_lt h
    have hG1r1 : G1 r1 ≤ 0 := by
      rcases eq_or_lt_of_le hr1r with h' | h'
      · rw [h']; exact hG1r
      · have := h1 r1 r hr1p.le h'.le (hr1p.trans h') hG1r
        have : r1 / r ≤ 1 := (div_le_one (hr1p.trans h')).2 h'.le
        nlinarith
    have e1 := h1 s r1 hs0 hsr1 hr1p hG1r1
    have e2 := hS s hs0 hsR.le
    have hk : (r1 - s) * δ ≤ R0 * (L * d) := by
      have : (1 - s / r1) * r1 = r1 - s := by field_simp
      have : (1 - s / r1) * δ ≤ L * d := by linarith
      have := mul_le_mul_of_nonneg_left this hr1p.le
      have : r1 * (L * d) ≤ R0 * (L * d) := mul_le_mul_of_nonneg_right hr1R (by positivity)
      nlinarith
    have h2 := M2 m s r1 hs0 hsr1
    have hE : Real.exp (-s ^ 2 / 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg s]
    have hpw : r1 ^ (m - 1) ≤ R0 ^ (m - 1) := pow_le_pow_left₀ hr1p.le hr1R _
    have hR0m : R0 ^ m = R0 * R0 ^ (m - 1) := by rw [← pow_succ']; congr 1; omega
    have h3 : r1 ^ (m - 1) * Real.exp (-s ^ 2 / 2) ≤ R0 ^ (m - 1) := by
      calc _ ≤ r1 ^ (m - 1) * 1 :=
            mul_le_mul_of_nonneg_left hE (pow_nonneg hr1p.le _)
        _ ≤ _ := by rw [mul_one]; exact hpw
    have h4 : (r1 - s) ≤ R0 * (L * d) / δ := by rw [le_div_iff₀ hδ]; exact hk
    calc _ ≤ (r1 - s) * (r1 ^ (m - 1) * Real.exp (-s ^ 2 / 2)) := h2
      _ ≤ (R0 * (L * d) / δ) * R0 ^ (m - 1) :=
          mul_le_mul h4 h3 (mul_nonneg (pow_nonneg hr1p.le _) (Real.exp_pos _).le) (by positivity)
      _ = R0 ^ m * L / δ * d := by rw [hR0m]; field_simp
  have hI2 : ∫ t in r1..r, fch m t ≤ 2 ^ m * A * d := by
    rcases le_or_gt r R0 with h | h
    · have : r1 = r := min_eq_left h
      rw [this, intervalIntegral.integral_same]; exact hpos2
    · have : r1 = R0 := min_eq_right h.le
      rw [this]
      exact PLL' m hm A δ d R0 R0 r G1 G2 hA hδ hd hR0 hR02 le_rfl h.le hG1r
        (hup s R0 hs0 hsR.le hG2s) h1 hB
  rw [← intervalIntegral.integral_add_adjacent_intervals ((fch_cont m).intervalIntegrable (μ := volume) s r1)
    ((fch_cont m).intervalIntegrable (μ := volume) r1 r)]
  nlinarith

lemma unbdd_eq (S : Set ℝ) (hdown : ∀ s ∈ S, ∀ r, 0 ≤ r → r ≤ s → r ∈ S) (hb : ¬ BddAbove S) :
    Ici 0 ⊆ S := by
  intro x hx
  rw [not_bddAbove_iff] at hb
  obtain ⟨y, hy, hxy⟩ := hb x
  exact hdown y hy x hx hxy.le

lemma tail_bound (μ : Measure ℝ) (a c : ℝ) (hB : ∀ n : ℕ, μ (Ioc a (a + n)) ≤ ENNReal.ofReal c) :
    μ (Ioi a) ≤ ENNReal.ofReal c := by
  have hU : Ioi a = ⋃ n : ℕ, Ioc a (a + n) := by
    ext x; simp only [mem_Ioi, mem_iUnion, mem_Ioc]
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_ge (x - a)
      exact ⟨n, hx, by linarith⟩
    · rintro ⟨n, hx, _⟩; exact hx
  rw [hU, Monotone.measure_iUnion]
  · exact iSup_le hB
  · intro i j hij
    apply Ioc_subset_Ioc le_rfl
    have : (i : ℝ) ≤ j := by exact_mod_cast hij
    linarith

lemma MEAS (μ : Measure ℝ) (S1 S2 : Set ℝ) (c : ℝ)
    (h1sub : S1 ⊆ Ici 0) (h1c : IsClosed S2 ∧ IsClosed S1) (h02 : (0:ℝ) ∈ S2)
    (hd1 : ∀ s ∈ S1, ∀ r, 0 ≤ r → r ≤ s → r ∈ S1)
    (hd2 : ∀ s ∈ S2, ∀ r, 0 ≤ r → r ≤ s → r ∈ S2)
    (hB : ∀ s r, 0 ≤ s → s ≤ r → r ∈ S1 → s ∈ S2 → (∀ t, s < t → t ∉ S2) →
      μ (Ioc s r) ≤ ENNReal.ofReal c) :
    μ S1 ≤ μ S2 + ENNReal.ofReal c := by
  by_cases hb2 : BddAbove S2
  swap
  · have : S1 ⊆ S2 := h1sub.trans (unbdd_eq S2 hd2 hb2)
    exact (measure_mono this).trans le_self_add
  set ρ' := sSup S2
  have hρ'mem : ρ' ∈ S2 := h1c.1.csSup_mem ⟨0, h02⟩ hb2
  have hρ'0 : 0 ≤ ρ' := le_csSup hb2 h02
  have hout : ∀ t, ρ' < t → t ∉ S2 := fun t ht hmem => absurd (le_csSup hb2 hmem) (not_le.2 ht)
  have hsub : S1 ⊆ S2 ∪ (S1 ∩ Ioi ρ') := by
    intro x hx
    by_cases h : x ≤ ρ'
    · exact Or.inl (hd2 ρ' hρ'mem x (h1sub hx) h)
    · exact Or.inr ⟨hx, not_le.1 h⟩
  have htail : μ (S1 ∩ Ioi ρ') ≤ ENNReal.ofReal c := by
    by_cases hb1 : BddAbove S1
    · rcases (S1 ∩ Ioi ρ').eq_empty_or_nonempty with he | hne
      · rw [he, measure_empty]; exact bot_le
      obtain ⟨x, hx1, hx2⟩ := hne
      set ρ := sSup S1
      have hρmem : ρ ∈ S1 := h1c.2.csSup_mem ⟨x, hx1⟩ hb1
      have hxρ : x ≤ ρ := le_csSup hb1 hx1
      calc μ (S1 ∩ Ioi ρ') ≤ μ (Ioc ρ' ρ) :=
            measure_mono (fun y hy => ⟨hy.2, le_csSup hb1 hy.1⟩)
        _ ≤ _ := hB ρ' ρ hρ'0 (le_trans (le_of_lt hx2) hxρ) hρmem hρ'mem hout
    · have hall := unbdd_eq S1 hd1 hb1
      calc μ (S1 ∩ Ioi ρ') ≤ μ (Ioi ρ') := measure_mono inter_subset_right
        _ ≤ _ := tail_bound μ ρ' c (fun n => hB ρ' (ρ' + n) hρ'0 (by simp)
            (hall (by simp only [mem_Ici]; positivity)) hρ'mem hout)
  calc μ S1 ≤ μ (S2 ∪ (S1 ∩ Ioi ρ')) := measure_mono hsub
    _ ≤ μ S2 + μ (S1 ∩ Ioi ρ') := measure_union_le _ _
    _ ≤ _ := by gcongr

end S164

namespace S164
open ChanceStateCtrl.General

lemma FIN (m : ℕ) (hm : 0 < m) : chiLaw m (Ici 0) ≠ ⊤ := by
  set R : ℝ := m + 1
  have hR1 : 1 ≤ R := by simp only [R]; linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
  have hR2 : (m : ℝ) + 1 ≤ R ^ 2 := by nlinarith
  have hRm : R ^ m = R * R ^ (m - 1) := by rw [← pow_succ']; congr 1; omega
  have hb : ∀ n : ℕ, chiLaw m (Ioc 0 (0 + n)) ≤ ENNReal.ofReal (|chiConst m| * (2 * R ^ m)) := by
    intro n
    refine (M1 m 0 (0 + n) le_rfl (by simp)).trans (ENNReal.ofReal_le_ofReal ?_)
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    simp only [zero_add]
    have hE0 : Real.exp (-(0:ℝ) ^ 2 / 2) = 1 := by simp
    have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
    have hRm0 : 0 ≤ R ^ m := by positivity
    rcases le_or_gt (n : ℝ) R with h | h
    · have := M2 m 0 n le_rfl hn0
      rw [hE0, sub_zero, mul_one] at this
      have : (n : ℝ) * (n : ℝ) ^ (m - 1) ≤ R * R ^ (m - 1) :=
        mul_le_mul h (pow_le_pow_left₀ hn0 h _) (by positivity) (by positivity)
      nlinarith
    · rw [← intervalIntegral.integral_add_adjacent_intervals
        ((fch_cont m).intervalIntegrable (μ := volume) 0 R)
        ((fch_cont m).intervalIntegrable (μ := volume) R n)]
      have h1 := M2 m 0 R le_rfl (by linarith)
      rw [hE0, sub_zero, mul_one] at h1
      have h2 := M3 m hm R n (by linarith) hR2 h.le
      have : Real.exp (-R ^ 2 / 2) ≤ 1 := by rw [Real.exp_le_one_iff]; nlinarith
      have : R ^ m * Real.exp (-R ^ 2 / 2) ≤ R ^ m := by
        calc _ ≤ R ^ m * 1 := mul_le_mul_of_nonneg_left this hRm0
          _ = _ := mul_one _
      nlinarith
  have htail := tail_bound (chiLaw m) 0 _ hb
  have h0 : chiLaw m {0} = 0 := by
    unfold chiLaw
    rw [withDensity_apply _ (measurableSet_singleton 0)]
    exact setLIntegral_measure_zero _ _ (by simp)
  have : Ici (0:ℝ) = {0} ∪ Ioi 0 := by ext x; simp [le_iff_eq_or_lt, eq_comm]
  rw [this]
  apply ne_top_of_le_ne_top _ (measure_union_le _ _)
  rw [h0, zero_add]
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top htail


lemma LAM {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] {m : ℕ}
    (g : U → EuclideanSpace ℝ (Fin m) → ℝ) (hloc : LocallyLipschitz (Function.uncurry g))
    (V : Set U) (hV : Convex ℝ V) (l σ N a : ℝ) (hl : 0 < l) (hσ : 0 < σ)
    (w : EuclideanSpace ℝ (Fin m)) (hw1 : σ ≤ ‖w‖) (hw2 : ‖w‖ ≤ N) (ha0 : 0 < a)
    (hal : l ≤ a * σ)
    (hgrow : ∀ h : U, ∀ u ∈ V, ∀ z : EuclideanSpace ℝ (Fin m), l ≤ ‖z‖ →
      clarkeDir (fun y => g y z) u h ≤
        l * ‖z‖ ^ (-(m : ℤ)) * Real.exp (‖z‖ ^ 2 / (2 * N ^ 2)) * ‖h‖)
    (x : U) (hx : x ∈ V) (x' : U) (hx' : x' ∈ V) :
    g x' (a • w) ≤ g x (a • w) +
      l * (σ ^ m)⁻¹ * (a ^ m)⁻¹ * Real.exp (a ^ 2 / 2) * dist x x' := by
  have hzn : ‖a • w‖ = a * ‖w‖ := by rw [norm_smul, Real.norm_of_nonneg ha0.le]
  have hzl : l ≤ ‖a • w‖ := by
    rw [hzn]; exact hal.trans (mul_le_mul_of_nonneg_left hw1 ha0.le)
  have hlip := clarke_lip (fun y => g y (a • w))
    (hloc.comp (LocallyLipschitz.prodMk_right (a • w))) V hV _
    (fun y hy h => hgrow h y hy (a • w) hzl) x hx x' hx'
  rw [← dist_eq_norm, dist_comm] at hlip
  have hl0 : 0 ≤ l := hl.le
  have e1 : ‖a • w‖ ^ (-(m : ℤ)) ≤ (σ ^ m)⁻¹ * (a ^ m)⁻¹ := by
    rw [zpow_neg, zpow_natCast, ← mul_inv, ← mul_pow]
    apply inv_anti₀ (by positivity)
    apply pow_le_pow_left₀ (by positivity)
    rw [hzn, mul_comm σ a]; exact mul_le_mul_of_nonneg_left hw1 ha0.le
  have hNpos : 0 < N := hσ.trans_le (hw1.trans hw2)
  have e2 : Real.exp (‖a • w‖ ^ 2 / (2 * N ^ 2)) ≤ Real.exp (a ^ 2 / 2) := by
    apply Real.exp_le_exp.2
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : ‖a • w‖ ≤ a * N := by rw [hzn]; exact mul_le_mul_of_nonneg_left hw2 ha0.le
    have : ‖a • w‖ ^ 2 ≤ (a * N) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
    nlinarith
  have hΛ : l * ‖a • w‖ ^ (-(m : ℤ)) * Real.exp (‖a • w‖ ^ 2 / (2 * N ^ 2)) ≤
      l * (σ ^ m)⁻¹ * (a ^ m)⁻¹ * Real.exp (a ^ 2 / 2) := by
    calc _ ≤ l * ((σ ^ m)⁻¹ * (a ^ m)⁻¹) * Real.exp (a ^ 2 / 2) := by gcongr
      _ = _ := by ring
  have := mul_le_mul_of_nonneg_right hΛ (dist_nonneg (x := x) (y := x'))
  linarith

theorem main {Ω U : Type*} [MeasurableSpace Ω] [NormedAddCommGroup U]
    [NormedSpace ℝ U] {m : ℕ}
    (P : Measure Ω) (ξ : Ω → EuclideanSpace ℝ (Fin m)) (Sigma : Matrix (Fin m) (Fin m) ℝ)
    (g : U → EuclideanSpace ℝ (Fin m) → ℝ) (hA : Assumption21 P ξ Sigma g)
    (ub : U) (h10 : g ub 0 < 0) (h12 : ModerateGrowth g Sigma ub) :
    ∃ K : NNReal, ∃ t ∈ 𝓝 ub, ∀ v : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
      LipschitzOnWith K (fun u => radialProb Sigma g u v) t := by
  obtain ⟨l, hl, hgrow⟩ := h12
  have hm := hA.dim_pos
  obtain ⟨σ, hσ, hσle⟩ := S163.sqrtCov_lower Sigma hA.posDef
  set N := ‖sqrtCov Sigma‖ with hN
  have hN0 : 0 ≤ N := norm_nonneg _
  set R0 : ℝ := l / σ + m + 1 with hR0def
  have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
  have hlσ : 0 ≤ l / σ := by positivity
  have hR0 : 1 ≤ R0 := by linarith
  have hR0σ : l ≤ R0 * σ := by
    have : l / σ * σ = l := div_mul_cancel₀ _ hσ.ne'
    nlinarith
  have hR02 : (m : ℝ) + 1 ≤ R0 ^ 2 := by nlinarith
  obtain ⟨ε₀, hε₀, L, hL0, hL⟩ := S163.unif_lip (Function.uncurry g) hA.locLip ub
    (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) (R0 * N)) (isCompact_closedBall _ _)
  simp only [Function.uncurry_apply_pair] at hL
  set δ₀ := -g ub 0 with hδ₀
  have hδ₀pos : 0 < δ₀ := by linarith
  set ε := min ε₀ (min (δ₀ / (2 * (L + 1))) (1 / l)) with hεdef
  have hεpos : 0 < ε := lt_min hε₀ (lt_min (by positivity) (by positivity))
  have hball : ∀ u ∈ Metric.ball ub ε, u ∈ Metric.ball ub ε₀ :=
    fun u hu => Metric.ball_subset_ball (min_le_left _ _) hu
  have hballl : ∀ u ∈ Metric.ball ub ε, u ∈ Metric.ball ub (1 / l) :=
    fun u hu => Metric.ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hu
  have hub : ub ∈ Metric.ball ub ε₀ := Metric.mem_ball_self hε₀
  set δ := δ₀ / 2 with hδdef
  have hδpos : 0 < δ := by positivity
  have hg0 : ∀ u ∈ Metric.ball ub ε, g u 0 ≤ -δ := by
    intro u hu
    have h1 := hL u (hball u hu) ub hub 0 (Metric.mem_closedBall_self (by positivity))
    have h2 : dist u ub ≤ δ₀ / (2 * (L + 1)) :=
      (Metric.mem_ball.1 hu).le.trans ((min_le_right _ _).trans (min_le_left _ _))
    rw [le_div_iff₀ (by positivity)] at h2
    have hd := dist_nonneg (x := u) (y := ub)
    rw [abs_le] at h1
    nlinarith
  have hcont : ∀ u, Continuous (g u) := fun u =>
    hA.locLip.continuous.comp (Continuous.prodMk continuous_const continuous_id)
  set A : ℝ := l * (σ ^ m)⁻¹ / δ with hAdef
  have hA0 : 0 ≤ A := by positivity
  set K : ℝ := |chiConst m| * (R0 ^ m * L / δ + 2 ^ m * A) with hKdef
  have hK0 : 0 ≤ K := by positivity
  refine ⟨K.toNNReal, Metric.ball ub ε, Metric.ball_mem_nhds _ hεpos, fun v => ?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro u hu u' hu'
  rw [Real.coe_toNNReal _ hK0]
  set w := sqrtCov Sigma (v : EuclideanSpace ℝ (Fin m)) with hwdef
  have hw1 : σ ≤ ‖w‖ := hσle v
  have hw2 : ‖w‖ ≤ N := by
    have := (sqrtCov Sigma).le_opNorm (v : EuclideanSpace ℝ (Fin m))
    rwa [show ‖(v : EuclideanSpace ℝ (Fin m))‖ = 1 from by simp, mul_one] at this
  set S : U → Set ℝ := fun x => {r : ℝ | 0 ≤ r ∧ g x (r • w) ≤ 0} with hSdef
  have hrad : ∀ x, radialProb Sigma g x v = (chiLaw m (S x)).toReal := fun x => rfl
  rw [hrad, hrad, Real.dist_eq]
  -- general facts
  have hconv : ∀ x ∈ Metric.ball ub ε, ∀ a b : ℝ, 0 ≤ a → a ≤ b → 0 < b →
      g x (a • w) ≤ (a / b) * g x (b • w) + (1 - a / b) * g x 0 := by
    intro x _ a b ha hab hb
    have := S163.conv_aux (g x) (hA.convex_snd x) (b • w) (a / b) (by positivity)
      ((div_le_one hb).2 hab)
    rwa [smul_smul, div_mul_cancel₀ _ hb.ne'] at this
  have h1 : ∀ x ∈ Metric.ball ub ε, ∀ a b : ℝ, 0 ≤ a → a ≤ b → 0 < b → g x (b • w) ≤ 0 →
      g x (a • w) ≤ -(1 - a / b) * δ := by
    intro x hx a b ha hab hb hgb
    have e := hconv x hx a b ha hab hb
    have : 0 ≤ a / b := by positivity
    have : 0 ≤ 1 - a / b := by rw [sub_nonneg]; exact (div_le_one hb).2 hab
    have := hg0 x hx
    nlinarith
  have hup : ∀ x ∈ Metric.ball ub ε, ∀ a b : ℝ, 0 ≤ a → a ≤ b → 0 ≤ g x (a • w) →
      0 ≤ g x (b • w) := by
    intro x hx a b ha hab hga
    by_contra hneg
    push Not at hneg
    have hg := hg0 x hx
    rcases (ha.trans hab).eq_or_lt with hb | hb
    · have : a = 0 := by linarith
      rw [this, zero_smul] at hga; linarith
    have e := hconv x hx a b ha hab hb
    have : 0 ≤ a / b := by positivity
    have h1t : 0 ≤ 1 - a / b := by rw [sub_nonneg]; exact (div_le_one hb).2 hab
    have hmx : max (g x (b • w)) (g x 0) < 0 := max_lt hneg (by linarith)
    have k1 := mul_le_mul_of_nonneg_left (le_max_left (g x (b • w)) (g x 0)) this
    have k2 := mul_le_mul_of_nonneg_left (le_max_right (g x (b • w)) (g x 0)) h1t
    nlinarith
  have h0S : ∀ x ∈ Metric.ball ub ε, (0:ℝ) ∈ S x := fun x hx =>
    ⟨le_rfl, by rw [zero_smul]; linarith [hg0 x hx]⟩
  have hdown : ∀ x ∈ Metric.ball ub ε, ∀ s ∈ S x, ∀ r, 0 ≤ r → r ≤ s → r ∈ S x := by
    intro x hx s ⟨hs0, hs⟩ r hr0 hrs
    refine ⟨hr0, ?_⟩
    rcases hs0.eq_or_lt with h | h
    · have : r = 0 := le_antisymm (h ▸ hrs) hr0
      rw [this, zero_smul]; linarith [hg0 x hx]
    have := h1 x hx r s hr0 hrs h hs
    have : r / s ≤ 1 := (div_le_one h).2 hrs
    nlinarith
  have hclosed : ∀ x, IsClosed (S x) := by
    intro x
    exact isClosed_Ici.inter (isClosed_le ((hcont x).comp (continuous_id.smul continuous_const))
      continuous_const)
  have hsubI : ∀ x, S x ⊆ Ici 0 := fun x r hr => hr.1
  have hfin : ∀ x, chiLaw m (S x) ≠ ⊤ := fun x =>
    ne_top_of_le_ne_top (FIN m hm) (measure_mono (hsubI x))
  -- the one-sided estimate
  have hone : ∀ x ∈ Metric.ball ub ε, ∀ x' ∈ Metric.ball ub ε,
      chiLaw m (S x) ≤ chiLaw m (S x') + ENNReal.ofReal (K * dist x x') := by
    intro x hx x' hx'
    set d := dist x x'
    have hd : 0 ≤ d := dist_nonneg
    apply MEAS (chiLaw m) (S x) (S x') (K * d) (hsubI x) ⟨hclosed x', hclosed x⟩ (h0S x' hx')
      (hdown x hx) (hdown x' hx')
    intro s r hs hsr hr hsS hout
    -- 0 ≤ g x' (s • w)
    have hG2s : 0 ≤ g x' (s • w) := by
      by_contra hlt
      push Not at hlt
      have hev : ∀ᶠ t in 𝓝 s, g x' (t • w) < 0 :=
        ((hcont x').comp (continuous_id.smul continuous_const)).continuousAt.eventually
          (gt_mem_nhds hlt)
      obtain ⟨t, ht1, ht2⟩ := ((eventually_nhdsWithin_of_eventually_nhds (s := Ioi s) hev).and
        self_mem_nhdsWithin).exists
      exact hout t ht2 ⟨hs.trans (le_of_lt ht2), ht1.le⟩
    have hS' : ∀ a, 0 ≤ a → a ≤ R0 → g x' (a • w) ≤ g x (a • w) + L * d := by
      intro a ha haR
      have hz : a • w ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) (R0 * N) := by
        rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg ha]
        exact mul_le_mul haR hw2 (norm_nonneg _) (by linarith)
      have := hL x (hball x hx) x' (hball x' hx') (a • w) hz
      rw [abs_le] at this
      linarith
    have hB' : ∀ a, R0 ≤ a → g x' (a • w) ≤ g x (a • w) +
        A * δ * (a ^ m)⁻¹ * Real.exp (a ^ 2 / 2) * d := by
      intro a ha
      have ha0 : 0 < a := lt_of_lt_of_le one_pos (hR0.trans ha)
      have hal : l ≤ a * σ := hR0σ.trans (mul_le_mul_of_nonneg_right ha hσ.le)
      have := LAM g hA.locLip (Metric.ball ub (1 / l)) (convex_ball _ _) l σ N a hl hσ w hw1 hw2 ha0
        hal hgrow x (hballl x hx) x' (hballl x' hx')
      have e : A * δ = l * (σ ^ m)⁻¹ := by rw [hAdef]; field_simp
      rw [e]; exact this
    have hint := PL m hm A δ d L R0 s r (fun a => g x (a • w)) (fun a => g x' (a • w)) hA0 hδpos hd
      hL0 hR0 hR02 hs hsr hr.2 hG2s (h1 x hx) (hup x' hx') hS' hB'
    refine (M1 m s r hs hsr).trans (ENNReal.ofReal_le_ofReal ?_)
    calc |chiConst m| * ∫ t in s..r, fch m t
        ≤ |chiConst m| * ((R0 ^ m * L / δ + 2 ^ m * A) * d) :=
          mul_le_mul_of_nonneg_left hint (abs_nonneg _)
      _ = K * d := by rw [hKdef]; ring
  have hKd : 0 ≤ K * dist u u' := mul_nonneg hK0 dist_nonneg
  have k1 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin u', ENNReal.ofReal_ne_top⟩)
    (hone u hu u' hu')
  have k2 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin u, ENNReal.ofReal_ne_top⟩)
    (hone u' hu' u hu)
  rw [ENNReal.toReal_add (hfin u') ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hKd] at k1
  rw [ENNReal.toReal_add (hfin u) ENNReal.ofReal_ne_top, dist_comm,
    ENNReal.toReal_ofReal hKd] at k2
  rw [abs_sub_le_iff]; constructor <;> linarith

end S164

theorem solution {Ω U : Type*} [MeasurableSpace Ω] [NormedAddCommGroup U]
    [NormedSpace ℝ U] {m : ℕ}
    (P : Measure Ω) (ξ : Ω → EuclideanSpace ℝ (Fin m)) (Sigma : Matrix (Fin m) (Fin m) ℝ)
    (g : U → EuclideanSpace ℝ (Fin m) → ℝ) (hA : ChanceStateCtrl.General.Assumption21 P ξ Sigma g)
    (ub : U) (h10 : g ub 0 < 0) (h12 : ChanceStateCtrl.General.ModerateGrowth g Sigma ub) :
    ∃ K : NNReal, ∃ t ∈ 𝓝 ub, ∀ v : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
      LipschitzOnWith K (fun u => ChanceStateCtrl.General.radialProb Sigma g u v) t :=
  S164.main P ξ Sigma g hA ub h10 h12
