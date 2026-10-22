-- Prove2me | solution 1 for DelegStop.Commit.proposition_3c
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T13:51:29.330774+00:00
-- url     : https://prove2.me/submissions/f936ea91-fafb-4dbd-9bd1-233946cfd93d

import Mathlib
import Definitions.Def_DelegStop_Commit_Model

namespace DelegStop.Commit.Aux

open MeasureTheory Set Filter Topology Real

lemma hasDerivAt_expk (k v : ℝ) :
    HasDerivAt (fun v => Real.exp (-v / k)) (Real.exp (-v / k) * (-1 / k)) v := by
  have h1 : HasDerivAt (fun v : ℝ => -v / k) (-1 / k) v := by
    simpa using ((hasDerivAt_id v).neg.div_const k)
  exact h1.exp

lemma tendsto_expk (k : ℝ) (hk : 0 < k) :
    Tendsto (fun v : ℝ => Real.exp (-v / k)) atTop (𝓝 0) := by
  have : Tendsto (fun v : ℝ => -v / k) atTop atBot := by
    have := (tendsto_id (α := ℝ)).atTop_div_const hk
    simpa [neg_div] using this
  exact Real.tendsto_exp_atBot.comp this

lemma tendsto_v_expk (k c : ℝ) (hk : 0 < k) :
    Tendsto (fun v : ℝ => Real.exp (-v / k) * (v + c)) atTop (𝓝 0) := by
  have h0 : Tendsto (fun x : ℝ => x ^ 1 * Real.exp (-x)) atTop (𝓝 0) :=
    Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have h1 : Tendsto (fun v : ℝ => v / k) atTop atTop := (tendsto_id).atTop_div_const hk
  have h2 := h0.comp h1
  have h3 : Tendsto (fun v : ℝ => k * ((v / k) ^ 1 * Real.exp (-(v / k)))
      + c * Real.exp (-v / k)) atTop (𝓝 (k * 0 + c * 0)) :=
    (h2.const_mul k).add ((tendsto_expk k hk).const_mul c)
  simp only [mul_zero, add_zero] at h3
  refine h3.congr' (Eventually.of_forall fun v => ?_)
  simp only [pow_one, neg_div]
  field_simp

/-- `∫_{a}^{∞} (1/k) e^{-v/k} dv = e^{-a/k}`. -/
lemma int0 (k a : ℝ) (hk : 0 < k) :
    ∫ v in Ioi a, (1 / k * Real.exp (-v / k)) = Real.exp (-a / k) := by
  have := integral_Ioi_of_hasDerivAt_of_nonneg' (g := fun v => -Real.exp (-v / k))
    (g' := fun v => 1 / k * Real.exp (-v / k)) (a := a) (l := 0)
    (fun x _ => by
      have h := (hasDerivAt_expk k x).neg
      have e : -(Real.exp (-x / k) * (-1 / k)) = 1 / k * Real.exp (-x / k) := by ring
      rw [e] at h; exact h)
    (fun x _ => by positivity)
    (by simpa using (tendsto_expk k hk).neg)
  simpa using this

lemma intOn0 (k a : ℝ) (hk : 0 < k) :
    IntegrableOn (fun v => 1 / k * Real.exp (-v / k)) (Ioi a) :=
  integrableOn_Ioi_deriv_of_nonneg' (g := fun v => -Real.exp (-v / k)) (l := 0)
    (fun x _ => by
      have h := (hasDerivAt_expk k x).neg
      have e : -(Real.exp (-x / k) * (-1 / k)) = 1 / k * Real.exp (-x / k) := by ring
      rw [e] at h; exact h)
    (fun x _ => by positivity)
    (by simpa using (tendsto_expk k hk).neg)

lemma deriv1 (k x : ℝ) (hk : 0 < k) :
    HasDerivAt (fun v => -(Real.exp (-v / k) * (v + k))) (x * (1 / k * Real.exp (-x / k))) x := by
  have h := ((hasDerivAt_expk k x).mul ((hasDerivAt_id x).add_const k)).neg
  have e : -(Real.exp (-x / k) * (-1 / k) * (id x + k) + Real.exp (-x / k) * 1)
      = x * (1 / k * Real.exp (-x / k)) := by
    simp only [id]; field_simp; ring
  rw [e] at h; exact h

/-- `∫_{a}^{∞} v (1/k) e^{-v/k} dv = e^{-a/k}(a+k)` for `a ≥ 0`. -/
lemma int1 (k a : ℝ) (hk : 0 < k) (ha : 0 ≤ a) :
    ∫ v in Ioi a, v * (1 / k * Real.exp (-v / k)) = Real.exp (-a / k) * (a + k) := by
  have := integral_Ioi_of_hasDerivAt_of_nonneg' (g := fun v => -(Real.exp (-v / k) * (v + k)))
    (g' := fun v => v * (1 / k * Real.exp (-v / k))) (a := a) (l := 0)
    (fun x _ => deriv1 k x hk)
    (fun x hx => by have : 0 ≤ x := le_trans ha (le_of_lt hx); positivity)
    (by simpa using (tendsto_v_expk k k hk).neg)
  simpa using this

lemma intOn1 (k a : ℝ) (hk : 0 < k) (ha : 0 ≤ a) :
    IntegrableOn (fun v => v * (1 / k * Real.exp (-v / k))) (Ioi a) :=
  integrableOn_Ioi_deriv_of_nonneg' (g := fun v => -(Real.exp (-v / k) * (v + k))) (l := 0)
    (fun x _ => deriv1 k x hk)
    (fun x hx => by have : 0 ≤ x := le_trans ha (le_of_lt hx); positivity)
    (by simpa using (tendsto_v_expk k k hk).neg)

lemma qd_eq (μ k v : ℝ) : qualDensity μ k v = μ * (1 / k * Real.exp (-v / k)) := by
  unfold qualDensity; ring

lemma int_qd (μ k a : ℝ) (hk : 0 < k) :
    ∫ v in Ioi a, qualDensity μ k v = μ * Real.exp (-a / k) := by
  simp_rw [qd_eq]
  rw [integral_const_mul, int0 k a hk]

lemma int_vp_qd (μ k a p : ℝ) (hk : 0 < k) (ha : 0 ≤ a) :
    ∫ v in Ioi a, (v - p) * qualDensity μ k v = μ * Real.exp (-a / k) * (a + k - p) := by
  have e : ∀ v, (v - p) * qualDensity μ k v
      = μ * (v * (1 / k * Real.exp (-v / k))) - (μ * p) * (1 / k * Real.exp (-v / k)) := by
    intro v; rw [qd_eq]; ring
  simp_rw [e]
  rw [integral_sub ((intOn1 k a hk ha).const_mul μ) ((intOn0 k a hk).const_mul (μ * p)),
    integral_const_mul, integral_const_mul, int1 k a hk ha, int0 k a hk]
  ring

lemma intOn_vp_qd (μ k a p : ℝ) (hk : 0 < k) (ha : 0 ≤ a) :
    IntegrableOn (fun v => (v - p) * qualDensity μ k v) (Ioi a) := by
  have e : (fun v => (v - p) * qualDensity μ k v)
      = fun v => μ * (v * (1 / k * Real.exp (-v / k))) - (μ * p) * (1 / k * Real.exp (-v / k)) := by
    funext v; rw [qd_eq]; ring
  rw [e]
  exact ((intOn1 k a hk ha).const_mul μ).sub ((intOn0 k a hk).const_mul (μ * p))

lemma intOn_qd (μ k a : ℝ) (hk : 0 < k) :
    IntegrableOn (fun v => qualDensity μ k v) (Ioi a) := by
  simp_rw [qd_eq]
  exact (intOn0 k a hk).const_mul μ


/-! ### Closed forms for the model -/

variable (P : Params)

lemma Phi_zero (e : Effort) : P.Phi e 0 = 1 - P.mu e := by
  simp [Params.Phi, qualCDF]

lemma Phi_eq (e : Effort) (v : ℝ) : P.Phi e v = 1 - P.mu e * Real.exp (-v / P.k) := rfl

lemma int_vp_dens (e : Effort) (a p : ℝ) (hk : 0 < P.k) (ha : 0 ≤ a) :
    ∫ v in Ioi a, (v - p) * P.dens e v = P.mu e * Real.exp (-a / P.k) * (a + P.k - p) :=
  int_vp_qd (P.mu e) P.k a p hk ha

lemma contValF_eq (cI p : ℝ) (e : Effort) (v1 : ℝ) (hk : 0 < P.k) (hv : 0 ≤ v1) :
    contValF P cI p e v1 = -cI + P.mu e * P.k * Real.exp (-v1 / P.k) + v1 - p := by
  unfold contValF
  rw [int_vp_dens P e v1 p hk hv, Phi_eq]
  ring

lemma effort2Fplus_eq (p : ℝ) (h : P.cl < P.ch) : effort2Fplus P p = .low := by
  unfold effort2Fplus best
  rw [if_neg]
  simp only [Params.cost]
  intro h'
  nlinarith

lemma effort2Fminus_eq (p : ℝ) : effort2Fminus P p = effort2C P p := by
  unfold effort2Fminus effort2C
  congr 1
  funext e
  ring

lemma effort2C_eq (p : ℝ) :
    effort2C P p = if P.ch - P.cl ≤ (P.μh - P.μl) * p then .high else .low := by
  unfold effort2C best
  simp only [Phi_zero, Params.mu, Params.cost]
  split_ifs with h1 h2 h2
  · rfl
  · exfalso; apply h2; nlinarith
  · exfalso; apply h1; nlinarith
  · rfl

lemma U2C_eq (p : ℝ) : U2C P p = -P.cost (effort2C P p) + P.mu (effort2C P p) * p := by
  unfold U2C; rw [Phi_zero]; ring

lemma U2Fplus_eq (p : ℝ) (h : P.cl < P.ch) : U2Fplus P p = p - P.cl := by
  unfold U2Fplus; rw [effort2Fplus_eq P p h, Phi_zero]; simp only [Params.cost]; ring

lemma U2Fminus_eq (p : ℝ) : U2Fminus P p = U2C P p := by
  unfold U2Fminus U2C; rw [effort2Fminus_eq]; ring

lemma PiC2_eq (cI p : ℝ) (e : Effort) (hk : 0 < P.k) :
    PiC2 P cI p e = -cI + P.mu e * (P.k - p) := by
  unfold PiC2; rw [int_vp_dens P e 0 p hk le_rfl]; simp

lemma PiFminus2_eq (cI p : ℝ) (e : Effort) (hk : 0 < P.k) :
    PiFminus2 P cI p e = -cI + P.mu e * (P.k - p) := by
  unfold PiFminus2; rw [int_vp_dens P e 0 p hk le_rfl]; simp

lemma stopsF_iff (cI p v1 : ℝ) (hk : 0 < P.k) (h : P.cl < P.ch) (hv : 0 ≤ v1) :
    stopsF P cI p v1 ↔ P.μl * P.k * Real.exp (-v1 / P.k) ≤ cI := by
  unfold stopsF
  rw [contValF_eq P cI p _ v1 hk hv, effort2Fplus_eq P p h]
  simp only [Params.mu]
  constructor <;> intro h' <;> linarith

lemma thr_le_iff (a k cI v : ℝ) (ha : 0 < a) (hk : 0 < k) (hc : 0 < cI) :
    a * Real.exp (-v / k) ≤ cI ↔ -k * Real.log (cI / a) ≤ v := by
  rw [← le_div_iff₀' ha, ← Real.le_log_iff_exp_le (div_pos hc ha), div_le_iff₀ hk]
  constructor <;> intro h <;> nlinarith

lemma thr_ge_iff (a k cI v : ℝ) (ha : 0 < a) (hk : 0 < k) (hc : 0 < cI) :
    cI ≤ a * Real.exp (-v / k) ↔ v ≤ -k * Real.log (cI / a) := by
  rw [← div_le_iff₀' ha, ← Real.log_le_iff_le_exp (div_pos hc ha), le_div_iff₀ hk]
  constructor <;> intro h <;> nlinarith

lemma exp_thr (a k cI : ℝ) (ha : 0 < a) (hk : 0 < k) (hc : 0 < cI) :
    Real.exp (-(-k * Real.log (cI / a)) / k) = cI / a := by
  have : -(-k * Real.log (cI / a)) / k = Real.log (cI / a) := by field_simp
  rw [this, Real.exp_log (div_pos hc ha)]

lemma probStop_eq (cI p : ℝ) (e : Effort) (hk : 0 < P.k) (hμ : 0 < P.μl) (h : P.cl < P.ch)
    (hc : 0 < cI) :
    probStop P cI p e = P.mu e * min 1 (cI / (P.μl * P.k)) := by
  have ha : 0 < P.μl * P.k := mul_pos hμ hk
  unfold probStop
  by_cases hcase : P.μl * P.k ≤ cI
  · have hset : stopSet P cI p = Ioi 0 := by
      ext v
      simp only [stopSet, mem_setOf_eq, mem_Ioi, and_iff_left_iff_imp]
      intro hv
      rw [stopsF_iff P cI p v hk h hv.le]
      have : Real.exp (-v / P.k) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : 0 ≤ v / P.k := div_nonneg hv.le hk.le
        rw [neg_div]; linarith
      nlinarith
    rw [hset]
    have : min 1 (cI / (P.μl * P.k)) = 1 := by
      apply min_eq_left; rw [le_div_iff₀ ha]; linarith
    rw [this]
    show ∫ v in Ioi 0, qualDensity (P.mu e) P.k v = _
    rw [int_qd _ _ _ hk]; simp
  · push_neg at hcase
    set vs := -P.k * Real.log (cI / (P.μl * P.k)) with hvs
    have hlog : Real.log (cI / (P.μl * P.k)) < 0 := by
      apply Real.log_neg (div_pos hc ha)
      rw [div_lt_one ha]; exact hcase
    have hvs0 : 0 < vs := by rw [hvs]; nlinarith
    have hset : stopSet P cI p = Ici vs := by
      ext v
      simp only [stopSet, mem_setOf_eq, mem_Ici]
      constructor
      · rintro ⟨hv, hs⟩
        rw [stopsF_iff P cI p v hk h hv.le, thr_le_iff _ _ _ _ ha hk hc] at hs
        exact hs
      · intro hv
        have hv0 : 0 < v := lt_of_lt_of_le hvs0 hv
        refine ⟨hv0, ?_⟩
        rw [stopsF_iff P cI p v hk h hv0.le, thr_le_iff _ _ _ _ ha hk hc]
        exact hv
    rw [hset, integral_Ici_eq_integral_Ioi]
    show ∫ v in Ioi vs, qualDensity (P.mu e) P.k v = _
    rw [int_qd _ _ _ hk, hvs, exp_thr _ _ _ ha hk hc]
    have : min 1 (cI / (P.μl * P.k)) = cI / (P.μl * P.k) := by
      apply min_eq_right; rw [div_le_one ha]; exact hcase.le
    rw [this]


/-! ### The integral of the flexible round-2 value -/

lemma m_nonneg_bound (a k cI v : ℝ) (ha : 0 < a) (hk : 0 < k) (hc : 0 < cI) (hv : 0 ≤ v) :
    max 0 (a * Real.exp (-v / k) - cI) ≤ a := by
  have : Real.exp (-v / k) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ v / k := div_nonneg hv hk.le
    rw [neg_div]; linarith
  apply max_le ha.le; nlinarith

lemma intOn_m (a k cI : ℝ) (ha : 0 < a) (hk : 0 < k) (hc : 0 < cI) :
    IntegrableOn (fun v => max 0 (a * Real.exp (-v / k) - cI) * (1 / k * Real.exp (-v / k)))
      (Ioi 0) := by
  refine Integrable.mono' ((intOn0 k 0 hk).const_mul a) ?_ ?_
  · apply Continuous.aestronglyMeasurable
    fun_prop
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun v hv => ?_)
    have hb : 0 ≤ 1 / k * Real.exp (-v / k) := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_max_left _ _) hb)]
    exact mul_le_mul_of_nonneg_right (m_nonneg_bound a k cI v ha hk hc (le_of_lt hv)) hb

lemma int_m (a k cI : ℝ) (ha : 0 < a) (hk : 0 < k) (hc : 0 < cI) :
    ∫ v in Ioi 0, max 0 (a * Real.exp (-v / k) - cI) * (1 / k * Real.exp (-v / k))
      = (max 0 (a - cI)) ^ 2 / (2 * a) := by
  by_cases hcase : a ≤ cI
  · have h0 : max 0 (a - cI) = 0 := max_eq_left (by linarith)
    rw [h0]
    have : ∫ v in Ioi 0, max 0 (a * Real.exp (-v / k) - cI) * (1 / k * Real.exp (-v / k))
        = ∫ v in Ioi (0:ℝ), (0:ℝ) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v hv
      have : Real.exp (-v / k) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : 0 ≤ v / k := div_nonneg (le_of_lt hv) hk.le
        rw [neg_div]; linarith
      have : max 0 (a * Real.exp (-v / k) - cI) = 0 := max_eq_left (by nlinarith)
      simp only [this, zero_mul]
    rw [this]; simp
  · push_neg at hcase
    set vs := -k * Real.log (cI / a) with hvs
    have hlog : Real.log (cI / a) < 0 := by
      apply Real.log_neg (div_pos hc ha)
      rw [div_lt_one ha]; exact hcase
    have hvs0 : 0 < vs := by rw [hvs]; nlinarith
    have hI := intOn_m a k cI ha hk hc
    rw [← Ioc_union_Ioi_eq_Ioi hvs0.le,
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        (hI.mono_set Ioc_subset_Ioi_self) (hI.mono_set (Ioi_subset_Ioi hvs0.le))]
    have h2 : ∫ v in Ioi vs, max 0 (a * Real.exp (-v / k) - cI) * (1 / k * Real.exp (-v / k))
        = ∫ v in Ioi vs, (0:ℝ) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v hv
      have : a * Real.exp (-v / k) ≤ cI := (thr_le_iff a k cI v ha hk hc).mpr (le_of_lt hv)
      have : max 0 (a * Real.exp (-v / k) - cI) = 0 := max_eq_left (by linarith)
      simp only [this, zero_mul]
    have h1 : ∫ v in Ioc 0 vs, max 0 (a * Real.exp (-v / k) - cI) * (1 / k * Real.exp (-v / k))
        = ∫ v in Ioc 0 vs, (a * Real.exp (-v / k) - cI) * (1 / k * Real.exp (-v / k)) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro v hv
      have : cI ≤ a * Real.exp (-v / k) := (thr_ge_iff a k cI v ha hk hc).mpr hv.2
      have : max 0 (a * Real.exp (-v / k) - cI) = a * Real.exp (-v / k) - cI :=
        max_eq_right (by linarith)
      simp only [this]
    rw [h1, h2, integral_zero, add_zero, ← intervalIntegral.integral_of_le hvs0.le]
    have hderiv : ∀ x ∈ uIcc 0 vs, HasDerivAt
        (fun v => -(a / 2) * Real.exp (-v / k) ^ 2 + cI * Real.exp (-v / k))
        ((a * Real.exp (-x / k) - cI) * (1 / k * Real.exp (-x / k))) x := by
      intro x _
      have h := (((hasDerivAt_expk k x).pow 2).const_mul (-(a / 2))).add
        ((hasDerivAt_expk k x).const_mul cI)
      have e : -(a / 2) * (((2:ℕ):ℝ) * Real.exp (-x / k) ^ (2 - 1)
          * (Real.exp (-x / k) * (-1 / k))) + cI * (Real.exp (-x / k) * (-1 / k))
          = (a * Real.exp (-x / k) - cI) * (1 / k * Real.exp (-x / k)) := by
        field_simp; ring
      rw [e] at h; exact h
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (by apply Continuous.intervalIntegrable; fun_prop)]
    rw [hvs, exp_thr a k cI ha hk hc]
    have h0 : max 0 (a - cI) = a - cI := max_eq_right (by linarith)
    rw [h0]
    simp only [neg_zero, zero_div, Real.exp_zero]
    field_simp
    ring

lemma PiFplus2_eq (cI p v : ℝ) (hk : 0 < P.k) (h : P.cl < P.ch) (hv : 0 ≤ v) :
    PiFplus2 P cI p .low v = (v - p) + max 0 (P.μl * P.k * Real.exp (-v / P.k) - cI) := by
  unfold PiFplus2
  rw [contValF_eq P cI p _ v hk hv]
  simp only [Params.mu]
  rw [← max_add_add_left]
  congr 1 <;> ring

lemma int_PiFplus2 (cI p : ℝ) (e : Effort) (hk : 0 < P.k) (hμ : 0 < P.μl) (h : P.cl < P.ch)
    (hc : 0 < cI) :
    ∫ v in Ioi 0, PiFplus2 P cI p .low v * P.dens e v
      = P.mu e * (P.k - p) + P.mu e * ((max 0 (P.μl * P.k - cI)) ^ 2 / (2 * (P.μl * P.k))) := by
  have ha : 0 < P.μl * P.k := mul_pos hμ hk
  have hcongr : ∫ v in Ioi 0, PiFplus2 P cI p .low v * P.dens e v
      = ∫ v in Ioi 0, ((v - p) * qualDensity (P.mu e) P.k v
        + P.mu e * (max 0 (P.μl * P.k * Real.exp (-v / P.k) - cI)
          * (1 / P.k * Real.exp (-v / P.k)))) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    simp only
    rw [PiFplus2_eq P cI p v hk h (le_of_lt hv)]
    show _ * qualDensity (P.mu e) P.k v = _
    rw [qd_eq]; ring
  rw [hcongr, integral_add (intOn_vp_qd _ _ _ _ hk le_rfl)
    ((intOn_m _ _ _ ha hk hc).const_mul _), integral_const_mul, int_vp_qd _ _ _ _ hk le_rfl,
    int_m _ _ _ ha hk hc]
  simp


/-! ### Profits and round-1 efforts -/

lemma valueC_eq (cI p : ℝ) (e1 e2 : Effort) (hk : 0 < P.k) :
    valueC P cI p e1 e2
      = -cI + P.mu e1 * (P.k - p) + (1 - P.mu e1) * (-cI + P.mu e2 * (P.k - p)) := by
  unfold valueC
  rw [int_vp_dens P e1 0 p hk le_rfl, Phi_zero, PiC2_eq P cI p e2 hk]
  simp only [neg_zero, zero_div, Real.exp_zero]
  ring

lemma valueF_eq (cI p : ℝ) (e1 e2 : Effort) (hk : 0 < P.k) (hμ : 0 < P.μl) (h : P.cl < P.ch)
    (hc : 0 < cI) :
    valueF P cI p e1 .low e2
      = -cI + P.mu e1 * (P.k - p)
        + P.mu e1 * ((max 0 (P.μl * P.k - cI)) ^ 2 / (2 * (P.μl * P.k)))
        + (1 - P.mu e1) * (-cI + P.mu e2 * (P.k - p)) := by
  unfold valueF
  rw [int_PiFplus2 P cI p e1 hk hμ h hc, Phi_zero, PiFminus2_eq P cI p e2 hk]
  ring

lemma profit_diff (cI p : ℝ) (hk : 0 < P.k) (hμ : 0 < P.μl) (h : P.cl < P.ch) (hc : 0 < cI) :
    profitF P cI p - profitC P cI p
      = (P.mu (effort1F P cI p) - P.mu (effort1C P p))
          * ((P.k - p) + cI - P.mu (effort2C P p) * (P.k - p))
        + P.mu (effort1F P cI p) * ((max 0 (P.μl * P.k - cI)) ^ 2 / (2 * (P.μl * P.k))) := by
  unfold profitF profitC
  rw [effort2Fplus_eq P p h, effort2Fminus_eq, valueF_eq P cI p _ _ hk hμ h hc, valueC_eq P cI p _ _ hk]
  ring

lemma effort1C_eq (p : ℝ) :
    effort1C P p = if P.ch - P.cl ≤ (P.μh - P.μl) * (p - U2C P p) then .high else .low := by
  unfold effort1C best
  simp only [Phi_zero, Params.mu, Params.cost]
  split_ifs with h1 h2 h2
  · rfl
  · exfalso; apply h2; nlinarith
  · exfalso; apply h1; nlinarith
  · rfl

lemma effort1F_eq (cI p : ℝ) (hk : 0 < P.k) (hμ : 0 < P.μl) (h : P.cl < P.ch) (hc : 0 < cI) :
    effort1F P cI p = if P.ch - P.cl + (P.μh - P.μl) * (1 - min 1 (cI / (P.μl * P.k))) * P.cl
        ≤ (P.μh - P.μl) * (p - U2C P p) then .high else .low := by
  unfold effort1F best
  simp only [probStop_eq P cI p _ hk hμ h hc, U2Fplus_eq P p h, U2Fminus_eq, Phi_zero, Params.mu,
    Params.cost]
  split_ifs with h1 h2 h2
  · rfl
  · exfalso; apply h2; nlinarith
  · exfalso; apply h1; nlinarith
  · rfl

lemma sqrt_iff (k Δ y R : ℝ) (hk : 0 < k) (hΔ : 0 < Δ) (hy : 0 < y) :
    y ^ 2 / (2 * k) + Δ * y < R ↔ y < k * (Real.sqrt (Δ ^ 2 + 2 * max R 0 / k) - Δ) := by
  by_cases hR : R ≤ 0
  · rw [max_eq_right hR]
    simp only [mul_zero, zero_div, add_zero, Real.sqrt_sq hΔ.le, sub_self]
    have : 0 < y ^ 2 / (2 * k) := by positivity
    constructor <;> intro h' <;> nlinarith
  · push_neg at hR
    rw [max_eq_left hR.le]
    have e1 : y < k * (Real.sqrt (Δ ^ 2 + 2 * R / k) - Δ)
        ↔ y / k + Δ < Real.sqrt (Δ ^ 2 + 2 * R / k) := by
      rw [div_add' _ _ _ hk.ne', div_lt_iff₀ hk]
      constructor <;> intro h' <;> nlinarith
    rw [e1, Real.lt_sqrt (by positivity)]
    have key : (y / k + Δ) ^ 2 - (Δ ^ 2 + 2 * R / k) = 2 / k * (y ^ 2 / (2 * k) + Δ * y - R) := by
      field_simp; ring
    have hk2 : 0 < 2 / k := by positivity
    constructor
    · intro h'
      have : 2 / k * (y ^ 2 / (2 * k) + Δ * y - R) < 0 := mul_neg_of_pos_of_neg hk2 (by linarith)
      linarith
    · intro h'
      have h3 : 2 / k * (y ^ 2 / (2 * k) + Δ * y - R) < 0 := by linarith
      by_contra hcon
      push_neg at hcon
      have : 0 ≤ 2 / k * (y ^ 2 / (2 * k) + Δ * y - R) := mul_nonneg hk2.le (by linarith)
      linarith


/-! ### The three regimes -/

lemma gg_nonneg (cI : ℝ) (hk : 0 < P.k) (hμ : 0 < P.μl) :
    0 ≤ (max 0 (P.μl * P.k - cI)) ^ 2 / (2 * (P.μl * P.k)) :=
  div_nonneg (sq_nonneg _) (by have := mul_pos hμ hk; linarith)

lemma case_low (hS : EffortStanding P.μl P.μh P.cl P.ch) (hk : 0 < P.k) (cI p : ℝ) (hc : 0 < cI)
    (hp0 : p < (P.ch - P.cl) / (P.μh - P.μl)) : ¬ profitF P cI p < profitC P cI p := by
  obtain ⟨hμl, hμlh, hμh1, hcl0, hclh, hcross⟩ := hS
  have hΔ : 0 < P.μh - P.μl := by linarith
  have hp0' : (P.μh - P.μl) * p < P.ch - P.cl := by
    rw [lt_div_iff₀ hΔ] at hp0; linarith
  have h2 : effort2C P p = .low := by rw [effort2C_eq, if_neg]; push_neg; exact hp0'
  have hU : U2C P p = -P.cl + P.μl * p := by rw [U2C_eq, h2]; simp [Params.cost, Params.mu]
  have hCcond : ¬ (P.ch - P.cl ≤ (P.μh - P.μl) * (p - U2C P p)) := by
    rw [hU]; intro h
    have h1 : (P.μh - P.μl) * p * (1 - P.μl) < (P.ch - P.cl) * (1 - P.μl) :=
      mul_lt_mul_of_pos_right hp0' (by linarith)
    nlinarith
  have h1C : effort1C P p = .low := by rw [effort1C_eq, if_neg hCcond]
  have h1F : effort1F P cI p = .low := by
    rw [effort1F_eq P cI p hk hμl hclh hc, if_neg]
    intro h; apply hCcond
    have hs : min 1 (cI / (P.μl * P.k)) ≤ 1 := min_le_left _ _
    have : 0 ≤ (P.μh - P.μl) * (1 - min 1 (cI / (P.μl * P.k))) * P.cl :=
      mul_nonneg (mul_nonneg hΔ.le (by linarith)) hcl0
    linarith
  have hd := profit_diff P cI p hk hμl hclh hc
  rw [h1F, h1C] at hd
  simp only [Params.mu, sub_self, zero_mul, zero_add] at hd
  have hg := gg_nonneg P cI hk hμl
  intro hlt
  nlinarith [mul_nonneg hμl.le hg]

lemma case_mid (hS : EffortStanding P.μl P.μh P.cl P.ch) (hk : 0 < P.k) (cI p : ℝ) (hc : 0 < cI)
    (hp0 : (P.ch - P.cl) / (P.μh - P.μl) ≤ p)
    (hbad : ¬ (0 ≤ (P.μh - P.μl) * (p - (-P.ch + P.μh * p)) - (P.ch - P.cl) ∧ 0 < P.cl)) :
    ¬ profitF P cI p < profitC P cI p := by
  obtain ⟨hμl, hμlh, hμh1, hcl0, hclh, hcross⟩ := hS
  have hΔ : 0 < P.μh - P.μl := by linarith
  have hp0' : P.ch - P.cl ≤ (P.μh - P.μl) * p := by
    rw [div_le_iff₀ hΔ] at hp0; linarith
  have h2 : effort2C P p = .high := by rw [effort2C_eq, if_pos hp0']
  have hU : U2C P p = -P.ch + P.μh * p := by rw [U2C_eq, h2]; simp [Params.cost, Params.mu]
  have hd := profit_diff P cI p hk hμl hclh hc
  have hg := gg_nonneg P cI hk hμl
  have hs : min 1 (cI / (P.μl * P.k)) ≤ 1 := min_le_left _ _
  by_cases hE : 0 ≤ (P.μh - P.μl) * (p - (-P.ch + P.μh * p)) - (P.ch - P.cl)
  · have hcl : P.cl = 0 := by
      have : ¬ 0 < P.cl := fun h => hbad ⟨hE, h⟩
      linarith
    have h1C : effort1C P p = .high := by rw [effort1C_eq, if_pos]; rw [hU]; linarith
    have h1F : effort1F P cI p = .high := by
      rw [effort1F_eq P cI p hk hμl hclh hc, if_pos]; rw [hU, hcl]; rw [hcl] at hE; linarith
    rw [h1F, h1C] at hd
    simp only [Params.mu, sub_self, zero_mul, zero_add] at hd
    intro hlt
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ P.μh) hg]
  · have hCcond : ¬ (P.ch - P.cl ≤ (P.μh - P.μl) * (p - U2C P p)) := by
      rw [hU]; intro h; apply hE; linarith
    have h1C : effort1C P p = .low := by rw [effort1C_eq, if_neg hCcond]
    have h1F : effort1F P cI p = .low := by
      rw [effort1F_eq P cI p hk hμl hclh hc, if_neg]
      intro h; apply hCcond
      have : 0 ≤ (P.μh - P.μl) * (1 - min 1 (cI / (P.μl * P.k))) * P.cl :=
        mul_nonneg (mul_nonneg hΔ.le (by linarith)) hcl0
      linarith
    rw [h1F, h1C] at hd
    simp only [Params.mu, sub_self, zero_mul, zero_add] at hd
    intro hlt
    nlinarith [mul_nonneg hμl.le hg]

lemma case_good (hS : EffortStanding P.μl P.μh P.cl P.ch) (hk : 0 < P.k) (cI p : ℝ) (hc : 0 < cI)
    (hp0 : (P.ch - P.cl) / (P.μh - P.μl) ≤ p)
    (hE : 0 ≤ (P.μh - P.μl) * (p - (-P.ch + P.μh * p)) - (P.ch - P.cl)) (hcl : 0 < P.cl) :
    profitF P cI p < profitC P cI p ↔
      (P.μl * P.k - P.k * (Real.sqrt ((P.μh - P.μl) ^ 2
          + 2 * max ((P.μh - P.μl) * ((1 - P.μh) * (P.k - p) + P.μl * P.k)) 0 / P.k)
          - (P.μh - P.μl)) < cI ∧
        cI < P.μl * P.k * (1 - ((P.μh - P.μl) * (p - (-P.ch + P.μh * p)) - (P.ch - P.cl))
          / ((P.μh - P.μl) * P.cl))) := by
  obtain ⟨hμl, hμlh, hμh1, hcl0, hclh, hcross⟩ := hS
  have hΔ : 0 < P.μh - P.μl := by linarith
  have hp0' : P.ch - P.cl ≤ (P.μh - P.μl) * p := by
    rw [div_le_iff₀ hΔ] at hp0; linarith
  have h2 : effort2C P p = .high := by rw [effort2C_eq, if_pos hp0']
  have hU : U2C P p = -P.ch + P.μh * p := by rw [U2C_eq, h2]; simp [Params.cost, Params.mu]
  have hd := profit_diff P cI p hk hμl hclh hc
  have hg := gg_nonneg P cI hk hμl
  have ha : 0 < P.μl * P.k := mul_pos hμl hk
  set a := P.μl * P.k with ha_def
  set Δ := P.μh - P.μl with hΔ_def
  set E := Δ * (p - (-P.ch + P.μh * p)) - (P.ch - P.cl) with hE_def
  set q := E / (Δ * P.cl) with hq_def
  have hΔcl : 0 < Δ * P.cl := mul_pos hΔ hcl
  have hq : q * (Δ * P.cl) = E := div_mul_cancel₀ _ hΔcl.ne'
  have hq0 : 0 ≤ q := div_nonneg hE hΔcl.le
  have h1C : effort1C P p = .high := by rw [effort1C_eq, if_pos]; rw [hU]; linarith
  rw [h1C, h2] at hd
  simp only [Params.mu] at hd
  set s := min 1 (cI / a) with hs_def
  have hs1 : s ≤ 1 := min_le_left _ _
  have hF := effort1F_eq P cI p hk hμl hclh hc
  rw [← ha_def, ← hs_def, ← hΔ_def] at hF
  clear_value s q E Δ a
  generalize profitF P cI p = PF at hd ⊢
  generalize profitC P cI p = PC at hd ⊢
  by_cases hFc : P.ch - P.cl + Δ * (1 - s) * P.cl ≤ Δ * (p - U2C P p)
  · have h1F : effort1F P cI p = .high := by
      rw [hF, if_pos hFc]
    rw [h1F] at hd
    simp only [sub_self, zero_mul, zero_add] at hd
    rw [hU] at hFc
    constructor
    · intro hlt
      exfalso
      linarith [mul_nonneg (by linarith : (0:ℝ) ≤ P.μh) hg]
    · rintro ⟨_, hlt⟩
      exfalso
      have hca : cI < a := by linarith [mul_nonneg ha.le hq0]
      have hsv : s = cI / a := by
        rw [hs_def]; exact min_eq_right (by rw [div_le_one ha]; exact hca.le)
      have hsa : s * a = cI := by rw [hsv]; field_simp
      have h3' : s * a < (1 - q) * a := by linarith
      have h3 : s < 1 - q := lt_of_mul_lt_mul_right h3' ha.le
      have h4 : q * (Δ * P.cl) < (1 - s) * (Δ * P.cl) :=
        mul_lt_mul_of_pos_right (by linarith) hΔcl
      linarith
  · have h1F : effort1F P cI p = .low := by
      rw [hF, if_neg hFc]
    rw [h1F] at hd
    simp only at hd
    rw [hU] at hFc
    push_neg at hFc
    have hca : cI < a := by
      by_contra hcon
      push_neg at hcon
      have : s = 1 := by rw [hs_def]; exact min_eq_left (by rw [le_div_iff₀ ha]; linarith)
      rw [this] at hFc
      linarith
    have hsv : s = cI / a := by
      rw [hs_def]; exact min_eq_right (by rw [div_le_one ha]; exact hca.le)
    have hsa : s * a = cI := by rw [hsv]; field_simp
    have hbar : cI < a * (1 - q) := by
      have h4 : q * (Δ * P.cl) < (1 - s) * (Δ * P.cl) := by linarith
      have h5 : q < 1 - s := lt_of_mul_lt_mul_right h4 hΔcl.le
      have h6 : s * a < (1 - q) * a := mul_lt_mul_of_pos_right (by linarith) ha
      linarith
    have hmax : max 0 (a - cI) = a - cI := max_eq_right (by linarith)
    rw [hmax] at hd
    have hgg : P.μl * ((a - cI) ^ 2 / (2 * a)) = (a - cI) ^ 2 / (2 * P.k) := by
      have h2a : (2 * a) ≠ 0 := ne_of_gt (by linarith)
      have h2k : (2 * P.k) ≠ 0 := ne_of_gt (by linarith)
      rw [mul_div_assoc', div_eq_div_iff h2a h2k]
      rw [ha_def]; ring
    have hΔ' : P.μl - P.μh = -Δ := by rw [hΔ_def]; ring
    rw [hΔ', hgg] at hd
    have hid : Δ * (a - cI) + Δ * cI = Δ * (P.μl * P.k) := by rw [ha_def]; ring
    have hy : 0 < a - cI := by linarith
    have key := sqrt_iff P.k Δ (a - cI) (Δ * ((1 - P.μh) * (P.k - p) + a)) hk hΔ hy
    constructor
    · intro hlt
      refine ⟨?_, hbar⟩
      have h7 : (a - cI) ^ 2 / (2 * P.k) + Δ * (a - cI)
          < Δ * ((1 - P.μh) * (P.k - p) + a) := by linarith
      have := key.mp h7
      linarith
    · rintro ⟨hlo, _⟩
      have : a - cI < P.k * (Real.sqrt (Δ ^ 2
          + 2 * max (Δ * ((1 - P.μh) * (P.k - p) + a)) 0 / P.k) - Δ) := by linarith
      have h6 := key.mpr this
      linarith



/-! ### Extra lemmas for the milestones -/

lemma mu_pos (hS : EffortStanding P.μl P.μh P.cl P.ch) (e : Effort) : 0 < P.mu e := by
  obtain ⟨hμl, hμlh, -, -, -, -⟩ := hS
  cases e
  · exact hμl
  · show 0 < P.μh; linarith

lemma PiFplus2_eq_gen (cI p v : ℝ) (e2 : Effort) (hk : 0 < P.k) (hv : 0 ≤ v) :
    PiFplus2 P cI p e2 v = (v - p) + max 0 (P.mu e2 * P.k * Real.exp (-v / P.k) - cI) := by
  unfold PiFplus2
  rw [contValF_eq P cI p _ v hk hv]
  rw [← max_add_add_left]
  congr 1 <;> ring

lemma int_PiFplus2_gen (cI p : ℝ) (e e2 : Effort) (hk : 0 < P.k) (hμ : 0 < P.mu e2)
    (hc : 0 < cI) :
    ∫ v in Ioi 0, PiFplus2 P cI p e2 v * P.dens e v
      = P.mu e * (P.k - p)
        + P.mu e * ((max 0 (P.mu e2 * P.k - cI)) ^ 2 / (2 * (P.mu e2 * P.k))) := by
  have ha : 0 < P.mu e2 * P.k := mul_pos hμ hk
  have hcongr : ∫ v in Ioi 0, PiFplus2 P cI p e2 v * P.dens e v
      = ∫ v in Ioi 0, ((v - p) * qualDensity (P.mu e) P.k v
        + P.mu e * (max 0 (P.mu e2 * P.k * Real.exp (-v / P.k) - cI)
          * (1 / P.k * Real.exp (-v / P.k)))) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    simp only
    rw [PiFplus2_eq_gen P cI p v e2 hk (le_of_lt hv)]
    show _ * qualDensity (P.mu e) P.k v = _
    rw [qd_eq]; ring
  rw [hcongr, integral_add (intOn_vp_qd _ _ _ _ hk le_rfl)
    ((intOn_m _ _ _ ha hk hc).const_mul _), integral_const_mul, int_vp_qd _ _ _ _ hk le_rfl,
    int_m _ _ _ ha hk hc]
  simp

lemma low_regime (hS : EffortStanding P.μl P.μh P.cl P.ch) (hk : 0 < P.k) (cI p : ℝ)
    (hc : 0 < cI) (hp0 : p < (P.ch - P.cl) / (P.μh - P.μl)) :
    effort2C P p = .low ∧ effort1C P p = .low ∧ effort1F P cI p = .low := by
  obtain ⟨hμl, hμlh, hμh1, hcl0, hclh, hcross⟩ := hS
  have hΔ : 0 < P.μh - P.μl := by linarith
  have hp0' : (P.μh - P.μl) * p < P.ch - P.cl := by
    rw [lt_div_iff₀ hΔ] at hp0; linarith
  have h2 : effort2C P p = .low := by rw [effort2C_eq, if_neg]; push_neg; exact hp0'
  have hU : U2C P p = -P.cl + P.μl * p := by rw [U2C_eq, h2]; simp [Params.cost, Params.mu]
  have hCcond : ¬ (P.ch - P.cl ≤ (P.μh - P.μl) * (p - U2C P p)) := by
    rw [hU]; intro h
    have h1 : (P.μh - P.μl) * p * (1 - P.μl) < (P.ch - P.cl) * (1 - P.μl) :=
      mul_lt_mul_of_pos_right hp0' (by linarith)
    nlinarith
  have h1C : effort1C P p = .low := by rw [effort1C_eq, if_neg hCcond]
  have h1F : effort1F P cI p = .low := by
    rw [effort1F_eq P cI p hk hμl hclh hc, if_neg]
    intro h; apply hCcond
    have hs : min 1 (cI / (P.μl * P.k)) ≤ 1 := min_le_left _ _
    have : 0 ≤ (P.μh - P.μl) * (1 - min 1 (cI / (P.μl * P.k))) * P.cl :=
      mul_nonneg (mul_nonneg hΔ.le (by linarith)) hcl0
    linarith
  exact ⟨h2, h1C, h1F⟩

lemma high_regime (hS : EffortStanding P.μl P.μh P.cl P.ch) (p : ℝ)
    (hp0 : (P.ch - P.cl) / (P.μh - P.μl) ≤ p) :
    effort2C P p = .high ∧ U2C P p = -P.ch + P.μh * p := by
  obtain ⟨hμl, hμlh, hμh1, hcl0, hclh, hcross⟩ := hS
  have hΔ : 0 < P.μh - P.μl := by linarith
  have hp0' : P.ch - P.cl ≤ (P.μh - P.μl) * p := by
    rw [div_le_iff₀ hΔ] at hp0; linarith
  have h2 : effort2C P p = .high := by rw [effort2C_eq, if_pos hp0']
  exact ⟨h2, by rw [U2C_eq, h2]; simp [Params.cost, Params.mu]⟩

end DelegStop.Commit.Aux

open DelegStop.Commit DelegStop.Commit.Aux

namespace DelegStop.Commit.Aux

lemma key_iff (Δ m t pB p c : ℝ) (hΔ : 0 < Δ) (hm : 0 < m) (hpB : pB * m = t - c) :
    t * Δ ≤ Δ * (p * m + c) ↔ pB ≤ p := by
  constructor
  · intro h
    have h1 : t ≤ p * m + c := le_of_mul_le_mul_left (by linarith) hΔ
    have h2 : pB * m ≤ p * m := by linarith
    exact le_of_mul_le_mul_right h2 hm
  · intro h
    have h2 : pB * m ≤ p * m := mul_le_mul_of_nonneg_right h hm.le
    have h1 : t ≤ p * m + c := by linarith
    have := mul_le_mul_of_nonneg_left h1 hΔ.le
    linarith

lemma thr_eq (f : ℝ → Prop) (a b : ℝ) (ha : 0 < a) (hA : ∀ p, 0 < p → (f p ↔ a ≤ p))
    (hB : ∀ p, 0 < p → (f p ↔ b ≤ p)) : b = a := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have hp : 0 < (max b 0 + a) / 2 := by have := le_max_right b 0; linarith
    have h1 : f ((max b 0 + a) / 2) := (hB _ hp).mpr (by have := le_max_left b 0; linarith)
    have h2 := (hA _ hp).mp h1
    have : max b 0 < a := max_lt h ha
    linarith
  · have hp : 0 < (b + a) / 2 := by linarith
    have h1 : f ((b + a) / 2) := (hA _ hp).mpr (by linarith)
    have h2 := (hB _ hp).mp h1
    linarith

/-- The committed round-1 threshold. -/
noncomputable def pBC (P : Params) : ℝ :=
  ((P.ch - P.cl) / (P.μh - P.μl) - P.ch) / (1 - P.μh)

/-- The flexible round-1 threshold. -/
noncomputable def pBF (P : Params) (cI : ℝ) : ℝ :=
  ((P.ch - P.cl) / (P.μh - P.μl) + (1 - min 1 (cI / (P.μl * P.k))) * P.cl - P.ch) / (1 - P.μh)

lemma p0_le_pBC (P : Params) (hS : EffortStanding P.μl P.μh P.cl P.ch) :
    0 < (P.ch - P.cl) / (P.μh - P.μl) ∧ (P.ch - P.cl) / (P.μh - P.μl) ≤ pBC P := by
  obtain ⟨hμl, hμlh, hμh1, hcl0, hclh, hcross⟩ := hS
  have hΔ : 0 < P.μh - P.μl := by linarith
  have h1μ : 0 < 1 - P.μh := by linarith
  refine ⟨div_pos (by linarith) hΔ, ?_⟩
  set p0 := (P.ch - P.cl) / (P.μh - P.μl) with hp0_def
  have hp0 : p0 * (P.μh - P.μl) = P.ch - P.cl := div_mul_cancel₀ _ hΔ.ne'
  have hpB : pBC P * (1 - P.μh) = p0 - P.ch := div_mul_cancel₀ _ h1μ.ne'
  have h1 : P.ch * (P.μh - P.μl) ≤ P.μh * (P.ch - P.cl) := by nlinarith
  have h2 : P.ch ≤ P.μh * p0 := by
    rw [← hp0] at h1
    exact le_of_mul_le_mul_right (by linarith : P.ch * (P.μh - P.μl) ≤ (P.μh * p0) * (P.μh - P.μl)) hΔ
  have h3 : p0 * (1 - P.μh) ≤ pBC P * (1 - P.μh) := by rw [hpB]; linarith
  exact le_of_mul_le_mul_right h3 h1μ

lemma pBC_le_pBF (P : Params) (hS : EffortStanding P.μl P.μh P.cl P.ch) (cI : ℝ) :
    pBC P ≤ pBF P cI := by
  obtain ⟨hμl, hμlh, hμh1, hcl0, hclh, hcross⟩ := hS
  have h1μ : 0 < 1 - P.μh := by linarith
  unfold pBC pBF
  apply div_le_div_of_nonneg_right _ h1μ.le
  have : min 1 (cI / (P.μl * P.k)) ≤ 1 := min_le_left _ _
  have : 0 ≤ (1 - min 1 (cI / (P.μl * P.k))) * P.cl := mul_nonneg (by linarith) hcl0
  linarith

lemma C_char (P : Params) (hS : EffortStanding P.μl P.μh P.cl P.ch) (hk : 0 < P.k) (p : ℝ) :
    effort1C P p = .high ↔ pBC P ≤ p := by
  have hS' := hS
  obtain ⟨hμl, hμlh, hμh1, hcl0, hclh, hcross⟩ := hS
  have hΔ : 0 < P.μh - P.μl := by linarith
  have h1μ : 0 < 1 - P.μh := by linarith
  obtain ⟨_, hle⟩ := p0_le_pBC P hS'
  by_cases hp : p < (P.ch - P.cl) / (P.μh - P.μl)
  · obtain ⟨-, e1, -⟩ := low_regime P hS' hk 1 p one_pos hp
    rw [e1]
    constructor
    · intro h; cases h
    · intro h; linarith
  · push_neg at hp
    obtain ⟨-, hU⟩ := high_regime P hS' p hp
    have hp0 : (P.ch - P.cl) / (P.μh - P.μl) * (P.μh - P.μl) = P.ch - P.cl :=
      div_mul_cancel₀ _ hΔ.ne'
    have hpB : pBC P * (1 - P.μh) = (P.ch - P.cl) / (P.μh - P.μl) - P.ch :=
      div_mul_cancel₀ _ h1μ.ne'
    have hk' := key_iff (P.μh - P.μl) (1 - P.μh) ((P.ch - P.cl) / (P.μh - P.μl)) (pBC P) p P.ch
      hΔ h1μ hpB
    have e : (P.ch - P.cl ≤ (P.μh - P.μl) * (p - U2C P p)) ↔
        ((P.ch - P.cl) / (P.μh - P.μl) * (P.μh - P.μl)
          ≤ (P.μh - P.μl) * (p * (1 - P.μh) + P.ch)) := by
      rw [hp0, hU]; constructor <;> intro h <;> linarith
    rw [effort1C_eq]
    split_ifs with hc
    · simp only [true_iff]; exact hk'.mp (e.mp hc)
    · simp only [reduceCtorEq, false_iff]; intro h; exact hc (e.mpr (hk'.mpr h))

lemma F_char (P : Params) (hS : EffortStanding P.μl P.μh P.cl P.ch) (hk : 0 < P.k) (cI p : ℝ)
    (hc : 0 < cI) :
    effort1F P cI p = .high ↔ pBF P cI ≤ p := by
  have hS' := hS
  obtain ⟨hμl, hμlh, hμh1, hcl0, hclh, hcross⟩ := hS
  have hΔ : 0 < P.μh - P.μl := by linarith
  have h1μ : 0 < 1 - P.μh := by linarith
  obtain ⟨_, hle⟩ := p0_le_pBC P hS'
  have hle2 := pBC_le_pBF P hS' cI
  by_cases hp : p < (P.ch - P.cl) / (P.μh - P.μl)
  · obtain ⟨-, -, e1⟩ := low_regime P hS' hk cI p hc hp
    rw [e1]
    constructor
    · intro h; cases h
    · intro h; linarith
  · push_neg at hp
    obtain ⟨-, hU⟩ := high_regime P hS' p hp
    set s := min 1 (cI / (P.μl * P.k)) with hs_def
    have hp0 : (P.ch - P.cl) / (P.μh - P.μl) * (P.μh - P.μl) = P.ch - P.cl :=
      div_mul_cancel₀ _ hΔ.ne'
    have hpB : pBF P cI * (1 - P.μh)
        = ((P.ch - P.cl) / (P.μh - P.μl) + (1 - s) * P.cl) - P.ch :=
      div_mul_cancel₀ _ h1μ.ne'
    have hk' := key_iff (P.μh - P.μl) (1 - P.μh) ((P.ch - P.cl) / (P.μh - P.μl) + (1 - s) * P.cl)
      (pBF P cI) p P.ch hΔ h1μ hpB
    have e : (P.ch - P.cl + (P.μh - P.μl) * (1 - s) * P.cl ≤ (P.μh - P.μl) * (p - U2C P p)) ↔
        (((P.ch - P.cl) / (P.μh - P.μl) + (1 - s) * P.cl) * (P.μh - P.μl)
          ≤ (P.μh - P.μl) * (p * (1 - P.μh) + P.ch)) := by
      have e2 : ((P.ch - P.cl) / (P.μh - P.μl) + (1 - s) * P.cl) * (P.μh - P.μl)
          = P.ch - P.cl + (P.μh - P.μl) * (1 - s) * P.cl := by rw [add_mul, hp0]; ring
      rw [e2, hU]; constructor <;> intro h <;> linarith
    rw [effort1F_eq P cI p hk hμl hclh hc, ← hs_def]
    split_ifs with hcc
    · simp only [true_iff]; exact hk'.mp (e.mp hcc)
    · simp only [reduceCtorEq, false_iff]; intro h; exact hcc (e.mpr (hk'.mpr h))

lemma pBarC_eq (P : Params) (hS : EffortStanding P.μl P.μh P.cl P.ch) (hk : 0 < P.k)
    (pLow pBarC : ℝ) (h : CommittedEffortThresholds P pLow pBarC) : pBarC = pBC P := by
  obtain ⟨hpos, hle⟩ := p0_le_pBC P hS
  apply thr_eq (fun p => effort1C P p = .high) (pBC P) pBarC (by linarith)
    (fun p _ => C_char P hS hk p)
  intro p hp
  obtain ⟨h1, h2, h3⟩ := h p hp
  constructor
  · intro he
    by_contra hlt
    push_neg at hlt
    by_cases hl : p < pLow
    · have := congrArg Prod.fst (h1 hl); simp only at this; rw [he] at this; cases this
    · push_neg at hl
      have := congrArg Prod.fst (h2 hl hlt); simp only at this; rw [he] at this; cases this
  · intro hle'
    have := congrArg Prod.fst (h3 hle'); simpa using this

lemma pBarF_eq (P : Params) (hS : EffortStanding P.μl P.μh P.cl P.ch) (hk : 0 < P.k)
    (cI : ℝ) (hc : 0 < cI)
    (pLow pBarF : ℝ) (h : FlexibleEffortThresholds P cI pLow pBarF) : pBarF = pBF P cI := by
  obtain ⟨hpos, hle⟩ := p0_le_pBC P hS
  have hle2 := pBC_le_pBF P hS cI
  apply thr_eq (fun p => effort1F P cI p = .high) (pBF P cI) pBarF (by linarith)
    (fun p _ => F_char P hS hk cI p hc)
  intro p hp
  obtain ⟨h1, h2, h3⟩ := h p hp
  constructor
  · intro he
    by_contra hlt
    push_neg at hlt
    by_cases hl : p < pLow
    · have := congrArg Prod.fst (h1 hl); simp only at this; rw [he] at this; cases this
    · push_neg at hl
      have := congrArg Prod.fst (h2 hl hlt); simp only at this; rw [he] at this; cases this
  · intro hle'
    have := congrArg Prod.fst (h3 hle'); simpa using this

end DelegStop.Commit.Aux

theorem solution (P : Params) (hP : P.Standing) (cI : ℝ) (hcI : 0 < cI) :
    (∀ pLow pBarC pLow₁ pBarF : ℝ,
      CommittedEffortThresholds P pLow pBarC → FlexibleEffortThresholds P cI pLow₁ pBarF →
        pBarC ≤ pBarF) ∧
    (∀ k₂ : ℝ, P.k ≤ k₂ → ∀ pLow pBarC pLow₁ pBarF qLow qBarC qLow₁ qBarF : ℝ,
      CommittedEffortThresholds P pLow pBarC → FlexibleEffortThresholds P cI pLow₁ pBarF →
      CommittedEffortThresholds { P with k := k₂ } qLow qBarC →
      FlexibleEffortThresholds { P with k := k₂ } cI qLow₁ qBarF →
        pBarF - pBarC ≤ qBarF - qBarC) ∧
    (∀ cI₂ : ℝ, cI ≤ cI₂ → ∀ pLow pBarC pLow₁ pBarF pLow₂ pBarF₂ : ℝ,
      CommittedEffortThresholds P pLow pBarC → FlexibleEffortThresholds P cI pLow₁ pBarF →
      FlexibleEffortThresholds P cI₂ pLow₂ pBarF₂ →
        pBarF₂ - pBarC ≤ pBarF - pBarC) := by
  obtain ⟨hS, hk⟩ := hP
  have hμl := hS.1
  have hμh1 := hS.2.2.1
  have hcl0 := hS.2.2.2.1
  have h1μ : 0 < 1 - P.μh := by linarith
  refine ⟨fun pLow pBarC pLow₁ pBarF h1 h2 => ?_, fun k₂ hk₂ pLow pBarC pLow₁ pBarF qLow qBarC
    qLow₁ qBarF h1 h2 h3 h4 => ?_, fun cI₂ hcI₂ pLow pBarC pLow₁ pBarF pLow₂ pBarF₂ h1 h2 h3 => ?_⟩
  · rw [pBarC_eq P hS hk _ _ h1, pBarF_eq P hS hk cI hcI _ _ h2]
    exact pBC_le_pBF P hS cI
  · have hk2 : 0 < k₂ := lt_of_lt_of_le hk hk₂
    rw [pBarC_eq P hS hk _ _ h1, pBarF_eq P hS hk cI hcI _ _ h2,
      pBarC_eq ({ P with k := k₂ } : Params) hS hk2 _ _ h3,
      pBarF_eq ({ P with k := k₂ } : Params) hS hk2 cI hcI _ _ h4]
    unfold pBC pBF
    simp only
    rw [← sub_div, ← sub_div]
    apply div_le_div_of_nonneg_right _ h1μ.le
    have hm : min 1 (cI / (P.μl * k₂)) ≤ min 1 (cI / (P.μl * P.k)) := by
      apply min_le_min le_rfl
      apply div_le_div_of_nonneg_left hcI.le (mul_pos hμl hk)
      exact mul_le_mul_of_nonneg_left hk₂ hμl.le
    nlinarith
  · have hc2 : 0 < cI₂ := lt_of_lt_of_le hcI hcI₂
    rw [pBarC_eq P hS hk _ _ h1, pBarF_eq P hS hk cI hcI _ _ h2, pBarF_eq P hS hk cI₂ hc2 _ _ h3]
    unfold pBC pBF
    rw [← sub_div, ← sub_div]
    apply div_le_div_of_nonneg_right _ h1μ.le
    have hm : min 1 (cI / (P.μl * P.k)) ≤ min 1 (cI₂ / (P.μl * P.k)) := by
      apply min_le_min le_rfl
      exact div_le_div_of_nonneg_right hcI₂ (mul_pos hμl hk).le
    nlinarith
