-- Prove2me | solution 1 for CachonCoord.CapacityForecast.p104_forced_compliance_separating
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T06:02:44.965336+00:00
-- url     : https://prove2.me/submissions/6d70ea16-085f-4842-8d72-2e8d12127f21

import Mathlib
import Definitions.Def_CachonCoord_CapacityForecast_Model
import Definitions.Def_CachonCoord_CapacityForecast_Contracts

open MeasureTheory ProbabilityTheory


namespace CachonCoord.CapacityForecast

namespace Model
variable (M : Model)

lemma ae_nonneg_cc (θ : DemandType) : ∀ᵐ d ∂(M.μ θ), 0 ≤ d := by
  have h : M.μ θ (Set.Iio 0) = 0 := by
    have : Set.Iio (0:ℝ) = ⋃ n : ℕ, Set.Iic (-(1/((n:ℝ)+1))) := by
      ext y; simp only [Set.mem_Iio, Set.mem_iUnion, Set.mem_Iic]
      constructor
      · intro hy
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (neg_pos.mpr hy)
        exact ⟨n, by linarith⟩
      · rintro ⟨n, hn⟩
        have : 0 < 1/((n:ℝ)+1) := by positivity
        linarith
    rw [this, measure_iUnion_null_iff]
    intro n
    have h1 := M.cdf_neg θ (-(1/((n:ℝ)+1)))
      (by have : 0 < 1/((n:ℝ)+1) := by positivity
          linarith)
    rw [← ofReal_cdf, h1]; simp
  rw [ae_iff]
  simp only [not_le]
  exact h

theorem S_eq_cc (θ : DemandType) (x : ℝ) :
    M.S θ x = x - ∫ y in (0:ℝ)..x, cdf (M.μ θ) y := by
  unfold S
  congr 1
  rcases le_or_gt 0 x with hx | hx
  · have hint : Integrable (fun d => max (x - d) 0) (M.μ θ) := by
      refine Integrable.mono' (integrable_const x) ?_ ?_
      · exact (by fun_prop : Continuous fun d : ℝ => max (x-d) 0).aestronglyMeasurable
      · filter_upwards [M.ae_nonneg_cc θ] with d hd
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
        exact max_le (by linarith) hx
    rw [hint.integral_eq_integral_Ioc_meas_le (M := x)
      (Filter.Eventually.of_forall fun d => le_max_right _ _)]
    · have h2 : ∫ t in Set.Ioc 0 x, (M.μ θ).real {a | t ≤ max (x - a) 0}
          = ∫ t in Set.Ioc 0 x, cdf (M.μ θ) (x - t) := by
        refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
        have : {a : ℝ | t ≤ max (x - a) 0} = Set.Iic (x - t) := by
          ext a; simp only [Set.mem_setOf_eq, Set.mem_Iic]
          constructor
          · intro h; rcases le_max_iff.mp h with h | h
            · linarith
            · linarith [ht.1]
          · intro h; exact le_max_of_le_left (by linarith)
        rw [this, cdf_eq_real]
      rw [h2, ← intervalIntegral.integral_of_le hx, intervalIntegral.integral_comp_sub_left]
      simp
    · filter_upwards [M.ae_nonneg_cc θ] with d hd
      exact max_le (by linarith) hx
  · have h1 : ∫ d, max (x - d) 0 ∂(M.μ θ) = 0 := by
      rw [integral_congr_ae (g := fun _ => (0:ℝ))]
      · simp
      filter_upwards [M.ae_nonneg_cc θ] with d hd
      exact max_eq_right (by linarith)
    have h2 : ∫ y in (0:ℝ)..x, cdf (M.μ θ) y = ∫ y in (0:ℝ)..x, (0:ℝ) := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [Measure.ae_ne volume (0:ℝ)] with y hy hmem
      rw [Set.uIoc_of_ge hx.le] at hmem
      exact M.cdf_neg θ y (lt_of_le_of_ne hmem.2 hy)
    rw [h1, h2]; simp

lemma cdf_ii_cc (θ : DemandType) (a b : ℝ) : IntervalIntegrable (cdf (M.μ θ)) volume a b :=
  (monotone_cdf _).intervalIntegrable

lemma continuous_S_cc (θ : DemandType) : Continuous (M.S θ) := by
  have hS : M.S θ = fun x => x - ∫ y in (0:ℝ)..x, cdf (M.μ θ) y := funext (M.S_eq_cc θ)
  rw [hS]
  exact continuous_id.sub (intervalIntegral.continuous_primitive (fun a b => M.cdf_ii_cc θ a b) 0)

lemma hasDerivAt_S_cc (θ : DemandType) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (M.S θ) (1 - cdf (M.μ θ) x) x := by
  have hS : M.S θ = fun x => x - ∫ y in (0:ℝ)..x, cdf (M.μ θ) y := funext (M.S_eq_cc θ)
  rw [hS]
  have := intervalIntegral.integral_hasDerivAt_right (M.cdf_ii_cc θ 0 x)
    ((monotone_cdf _).measurable.stronglyMeasurable.stronglyMeasurableAtFilter)
    (M.differentiable θ x hx).continuousAt
  exact (hasDerivAt_id' x).sub this

noncomputable def linCC (θ : DemandType) (a b : ℝ) (x : ℝ) : ℝ := a * M.S θ x - b * x

lemma hasDerivAt_lin_cc (θ : DemandType) (a b : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (M.linCC θ a b) (a * (1 - cdf (M.μ θ) x) - b) x := by
  unfold linCC
  exact (((M.hasDerivAt_S_cc θ hx).const_mul a).sub ((hasDerivAt_id' x).const_mul b)).congr_deriv
    (by ring)

lemma continuous_lin_cc (θ : DemandType) (a b : ℝ) : Continuous (M.linCC θ a b) := by
  unfold linCC
  have := M.continuous_S_cc θ
  fun_prop

lemma concave_lin_cc (θ : DemandType) (a b : ℝ) (ha : 0 ≤ a) :
    ConcaveOn ℝ (Set.Ici 0) (M.linCC θ a b) := by
  apply AntitoneOn.concaveOn_of_deriv (convex_Ici 0) (M.continuous_lin_cc θ a b).continuousOn
  · rw [interior_Ici]
    intro z hz
    exact (M.hasDerivAt_lin_cc θ a b hz).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]
    intro y hy z hz hyz
    rw [(M.hasDerivAt_lin_cc θ a b hy).deriv, (M.hasDerivAt_lin_cc θ a b hz).deriv]
    have := monotone_cdf (M.μ θ) hyz
    nlinarith

lemma deriv_zero_of_max_cc (θ : DemandType) (a b : ℝ) {k : ℝ} (hk : 0 < k)
    (h : IsMaxOn (M.linCC θ a b) (Set.Ici 0) k) : a * (1 - cdf (M.μ θ) k) = b := by
  have hl : IsLocalMax (M.linCC θ a b) k := h.isLocalMax (Ici_mem_nhds hk)
  have := hl.hasDerivAt_eq_zero (M.hasDerivAt_lin_cc θ a b hk)
  linarith

lemma max_of_deriv_zero_cc (θ : DemandType) (a b : ℝ) (ha : 0 ≤ a) {k : ℝ} (hk : 0 < k)
    (h0 : a * (1 - cdf (M.μ θ) k) = b) : IsMaxOn (M.linCC θ a b) (Set.Ici 0) k := by
  rw [isMaxOn_iff]
  intro y hy
  rw [Set.mem_Ici] at hy
  rcases le_total y k with hyk | hyk
  · have hmono : MonotoneOn (M.linCC θ a b) (Set.Icc y k) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc y k) (M.continuous_lin_cc θ a b).continuousOn
      · intro z hz; rw [interior_Icc] at hz
        exact (M.hasDerivAt_lin_cc θ a b (lt_of_le_of_lt hy hz.1)).differentiableAt.differentiableWithinAt
      · intro z hz; rw [interior_Icc] at hz
        rw [(M.hasDerivAt_lin_cc θ a b (lt_of_le_of_lt hy hz.1)).deriv]
        have := monotone_cdf (M.μ θ) hz.2.le
        nlinarith
    exact hmono ⟨le_rfl, hyk⟩ ⟨hyk, le_rfl⟩ hyk
  · have hanti : AntitoneOn (M.linCC θ a b) (Set.Icc k y) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc k y) (M.continuous_lin_cc θ a b).continuousOn
      · intro z hz; rw [interior_Icc] at hz
        exact (M.hasDerivAt_lin_cc θ a b (lt_trans hk hz.1)).differentiableAt.differentiableWithinAt
      · intro z hz; rw [interior_Icc] at hz
        rw [(M.hasDerivAt_lin_cc θ a b (lt_trans hk hz.1)).deriv]
        have := monotone_cdf (M.μ θ) hz.1.le
        nlinarith
    exact hanti ⟨le_rfl, hyk⟩ ⟨hyk, le_rfl⟩ hyk

lemma isMaxOn_lin_iff_cc (θ : DemandType) (a b : ℝ) (ha : 0 ≤ a) {k : ℝ} (hk : 0 < k) :
    IsMaxOn (M.linCC θ a b) (Set.Ici 0) k ↔ a * (1 - cdf (M.μ θ) k) = b :=
  ⟨M.deriv_zero_of_max_cc θ a b hk, M.max_of_deriv_zero_cc θ a b ha hk⟩

lemma Omega_eq_cc (θ : DemandType) : M.Omega θ = M.linCC θ (M.r - M.cp) M.ck := by
  funext x; rfl

lemma rcp_pos_cc : 0 < M.r - M.cp := by linarith [M.margin, M.ck_pos]

theorem p99_core (θ : DemandType) :
    ConcaveOn ℝ (Set.Ici 0) (M.Omega θ) ∧
      ∀ k : ℝ, 0 < k →
        (IsMaxOn (M.Omega θ) (Set.Ici 0) k ↔ 1 - cdf (M.μ θ) k = M.ck / (M.r - M.cp)) := by
  have hrc := M.rcp_pos_cc
  rw [M.Omega_eq_cc θ]
  refine ⟨M.concave_lin_cc θ _ _ hrc.le, fun k hk => ?_⟩
  rw [M.isMaxOn_lin_iff_cc θ _ _ hrc.le hk, eq_div_iff hrc.ne']
  constructor <;> intro h <;> linear_combination h

lemma optimal_cond_cc (θ : DemandType) {k : ℝ} (hk : 0 < k)
    (h : IsMaxOn (M.Omega θ) (Set.Ici 0) k) : (M.r - M.cp) * (1 - cdf (M.μ θ) k) = M.ck := by
  rw [M.Omega_eq_cc θ] at h
  exact M.deriv_zero_of_max_cc θ _ _ hk h

lemma cdf_h_le_l_cc (x : ℝ) : cdf (M.μ DemandType.h) x ≤ cdf (M.μ DemandType.l) x := by
  rcases le_or_gt 0 x with hx | hx
  · exact (M.dominance x hx).le
  · rw [M.cdf_neg _ x hx, M.cdf_neg _ x hx]

lemma S_lt_cc {k : ℝ} (hk : 0 < k) : M.S DemandType.l k < M.S DemandType.h k := by
  rw [M.S_eq_cc, M.S_eq_cc]
  have : ∫ y in (0:ℝ)..k, cdf (M.μ DemandType.h) y < ∫ y in (0:ℝ)..k, cdf (M.μ DemandType.l) y := by
    apply intervalIntegral.integral_lt_integral_of_ae_le_of_measure_setOfPred_lt_ne_zero hk.le
      (M.cdf_ii_cc _ 0 k) (M.cdf_ii_cc _ 0 k)
    · exact Filter.Eventually.of_forall (fun x => M.cdf_h_le_l_cc x)
    · rw [Measure.restrict_apply' measurableSet_Ioc]
      have : {x | cdf (M.μ DemandType.h) x < cdf (M.μ DemandType.l) x} ∩ Set.Ioc 0 k
          = Set.Ioc 0 k := by
        ext x; simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Ioc]
        constructor
        · exact fun h => h.2
        · intro h; exact ⟨M.dominance x h.1.le, h⟩
      rw [this, Real.volume_Ioc]
      simp [hk]
  linarith

theorem p104_omega_core (kh kl : ℝ)
    (hkh : IsMaxOn (M.Omega DemandType.h) (Set.Ici 0) kh)
    (hkl : IsMaxOn (M.Omega DemandType.l) (Set.Ici 0) kl) (hkl_pos : 0 < kl) :
    (∀ k : ℝ, 0 < k → M.Omega DemandType.l k < M.Omega DemandType.h k) ∧
      M.Omega DemandType.l kl < M.Omega DemandType.h kh := by
  have h1 : ∀ k : ℝ, 0 < k → M.Omega DemandType.l k < M.Omega DemandType.h k := by
    intro k hk
    unfold Omega
    have := M.S_lt_cc hk
    have := M.rcp_pos_cc
    nlinarith
  refine ⟨h1, lt_of_lt_of_le (h1 kl hkl_pos) ?_⟩
  exact (isMaxOn_iff.mp hkh) kl (Set.mem_Ici.mpr hkl_pos.le)

lemma mfr_eq_cc (θ : DemandType) (lam we wo : ℝ)
    (hwe : M.r - we = lam * (M.r - M.cp)) (hwo : wo = lam * M.ck) (qi : ℝ) :
    M.mfrProfit θ we wo qi = lam * M.Omega θ qi := by
  unfold mfrProfit Omega; rw [hwe, hwo]; ring

lemma sup_eq_cc (θ : DemandType) (lam we wo : ℝ)
    (hwe : M.r - we = lam * (M.r - M.cp)) (hwo : wo = lam * M.ck) (qi : ℝ) :
    M.supProfit θ we wo qi = (1 - lam) * M.Omega θ qi := by
  have : we = M.r - lam * (M.r - M.cp) := by linarith
  unfold supProfit Omega; rw [this, hwo]; ring

theorem p99_opt_core (θ : DemandType) (lam we wo : ℝ)
    (hwe : M.r - we = lam * (M.r - M.cp)) (hwo : wo = lam * M.ck)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (ko : ℝ) (hko : IsMaxOn (M.Omega θ) (Set.Ici 0) ko) :
    (∀ qi : ℝ, M.mfrProfit θ we wo qi = lam * M.Omega θ qi) ∧
      (∀ qi : ℝ, M.supProfit θ we wo qi = (1 - lam) * M.Omega θ qi) ∧
      IsMaxOn (fun qi => M.mfrProfit θ we wo qi) (Set.Ici 0) ko ∧
      IsMaxOn (fun qi => M.supProfit θ we wo qi) (Set.Ici 0) ko := by
  have h1 := M.mfr_eq_cc θ lam we wo hwe hwo
  have h2 := M.sup_eq_cc θ lam we wo hwe hwo
  refine ⟨h1, h2, ?_, ?_⟩
  · rw [isMaxOn_iff]; intro y hy
    simp only [h1]
    exact mul_le_mul_of_nonneg_left ((isMaxOn_iff.mp hko) y hy) hlam0
  · rw [isMaxOn_iff]; intro y hy
    simp only [h2]
    exact mul_le_mul_of_nonneg_left ((isMaxOn_iff.mp hko) y hy) (by linarith)

theorem p100_core (θ : DemandType) (lam we wo : ℝ)
    (hwe : M.r - we = lam * (M.r - M.cp)) (hwo : wo = lam * M.ck)
    (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
    (ko : ℝ) (hko : IsMaxOn (M.Omega θ) (Set.Ici 0) ko) (hko_pos : 0 < ko) :
    (∀ k qi : ℝ, M.supVoluntaryProfit θ we wo k qi
        = (1 - lam) * (M.r - M.cp) * M.S θ k - M.ck * (k - lam * qi)) ∧
      (∃ d : ℝ, d < 0 ∧ HasDerivAt (fun k => M.supVoluntaryProfit θ we wo k ko) d ko) ∧
      ¬ IsMaxOn (fun k => M.supVoluntaryProfit θ we wo k ko) (Set.Icc 0 ko) ko := by
  have h1 : ∀ k qi : ℝ, M.supVoluntaryProfit θ we wo k qi
        = (1 - lam) * (M.r - M.cp) * M.S θ k - M.ck * (k - lam * qi) := by
    intro k qi
    have : we = M.r - lam * (M.r - M.cp) := by linarith
    unfold supVoluntaryProfit; rw [this, hwo]; ring
  have hopt := M.optimal_cond_cc θ hko_pos hko
  have hck := M.ck_pos
  have hfun : (fun k => M.supVoluntaryProfit θ we wo k ko)
      = fun k => (1 - lam) * (M.r - M.cp) * M.S θ k - M.ck * (k - lam * ko) := by
    funext k; exact h1 k ko
  have hd : HasDerivAt (fun k => M.supVoluntaryProfit θ we wo k ko) (-(lam * M.ck)) ko := by
    rw [hfun]
    exact (((M.hasDerivAt_S_cc θ hko_pos).const_mul ((1 - lam) * (M.r - M.cp))).sub
      (((hasDerivAt_id' ko).sub_const (lam * ko)).const_mul M.ck)).congr_deriv
      (by linear_combination (1 - lam) * hopt)
  refine ⟨h1, ⟨_, by nlinarith, hd⟩, ?_⟩
  intro hmax
  set g := fun k => M.supVoluntaryProfit θ we wo k ko with hg
  have ht := hasDerivAt_iff_tendsto_slope.mp hd
  have ht' : Filter.Tendsto (slope g ko) (nhdsWithin ko (Set.Iio ko)) (nhds (-(lam * M.ck))) :=
    ht.mono_left (nhdsWithin_mono _ (fun z hz => ne_of_lt hz))
  have e1 : ∀ᶠ z in nhdsWithin ko (Set.Iio ko), slope g ko z < 0 :=
    (tendsto_order.1 ht').2 0 (by nlinarith)
  have e2 : ∀ᶠ z in nhdsWithin ko (Set.Iio ko), z ∈ Set.Ioo 0 ko := Ioo_mem_nhdsLT hko_pos
  obtain ⟨z, hz1, hz2⟩ := (e1.and e2).exists
  rw [slope_def_field] at hz1
  have hle := (isMaxOn_iff.mp hmax) z ⟨hz2.1.le, hz2.2.le⟩
  have hneg : z - ko < 0 := by linarith [hz2.2]
  rcases div_neg_iff.mp hz1 with h | h
  · linarith [h.1]
  · linarith [h.2]

lemma wholesale_eq_cc (θ : DemandType) (w : ℝ) :
    M.supWholesaleProfit θ w = M.linCC θ (w - M.cp) M.ck := by funext x; rfl

theorem p101_core (θ : DemandType) (k w : ℝ) (hk : 0 < k) :
    IsMaxOn (M.supWholesaleProfit θ w) (Set.Ici 0) k ↔
      (0 < 1 - cdf (M.μ θ) k ∧ w = M.wInduce θ k) := by
  rw [M.wholesale_eq_cc θ w]
  have hck := M.ck_pos
  have hF1 := cdf_le_one (M.μ θ) k
  constructor
  · intro h
    have h0 := M.deriv_zero_of_max_cc θ _ _ hk h
    have hpos : 0 < 1 - cdf (M.μ θ) k := by
      rcases (sub_nonneg.mpr hF1).lt_or_eq with h' | h'
      · exact h'
      · rw [← h'] at h0; linarith
    refine ⟨hpos, ?_⟩
    unfold wInduce
    field_simp
    linarith
  · rintro ⟨hpos, hw⟩
    unfold wInduce at hw
    have hwc : w - M.cp = M.ck / (1 - cdf (M.μ θ) k) := by linarith
    apply M.max_of_deriv_zero_cc θ _ _ _ hk
    · rw [hwc]; field_simp
    · rw [hwc]; positivity

lemma S_pos_cc (θ : DemandType) {x : ℝ} (hx : 0 < x) (hF : 0 < 1 - cdf (M.μ θ) x) :
    0 < M.S θ x := by
  rw [M.S_eq_cc]
  have : ∫ y in (0:ℝ)..x, cdf (M.μ θ) y ≤ ∫ y in (0:ℝ)..x, cdf (M.μ θ) x := by
    apply intervalIntegral.integral_mono_on hx.le (M.cdf_ii_cc θ 0 x) intervalIntegrable_const
    intro y hy; exact monotone_cdf _ hy.2
  rw [intervalIntegral.integral_const, smul_eq_mul] at this
  nlinarith

theorem p102_core (θ : DemandType) (kstar fk : ℝ) (hks : 0 < kstar)
    (hFbar : 0 < 1 - cdf (M.μ θ) kstar)
    (hf : HasDerivAt (cdf (M.μ θ)) fk kstar) (hfk : 0 < fk)
    (hstat : HasDerivAt (M.mfrWholesaleProfit θ) 0 kstar)
    (ko : ℝ) (hko : IsMaxOn (M.Omega θ) (Set.Ici 0) ko) (hko_pos : 0 < ko) :
    1 - cdf (M.μ θ) kstar
        = M.ck / (M.r - M.cp) * (1 + fk / (1 - cdf (M.μ θ) kstar) ^ 2 * M.S θ kstar) ∧
      1 - cdf (M.μ θ) kstar
        = (1 - cdf (M.μ θ) ko) * (1 + fk / (1 - cdf (M.μ θ) kstar) ^ 2 * M.S θ kstar) ∧
      kstar < ko := by
  have hrc := M.rcp_pos_cc
  have hck := M.ck_pos
  have hune : 1 - cdf (M.μ θ) kstar ≠ 0 := hFbar.ne'
  have hdiv : HasDerivAt (fun k => M.ck / (1 - cdf (M.μ θ) k))
      (M.ck * fk / (1 - cdf (M.μ θ) kstar) ^ 2) kstar := by
    have := (hasDerivAt_const kstar M.ck).div (hf.const_sub 1) hune
    exact this.congr_deriv (by ring)
  have hP : HasDerivAt (M.mfrWholesaleProfit θ)
      ((-(M.ck * fk / (1 - cdf (M.μ θ) kstar) ^ 2)) * M.S θ kstar
        + (M.r - (M.ck / (1 - cdf (M.μ θ) kstar) + M.cp)) * (1 - cdf (M.μ θ) kstar)) kstar := by
    have := ((hasDerivAt_const kstar M.r).sub (hdiv.add_const M.cp)).mul (M.hasDerivAt_S_cc θ hks)
    unfold mfrWholesaleProfit wInduce
    exact this.congr_deriv (by simp only [Pi.sub_apply]; ring)
  set u := 1 - cdf (M.μ θ) kstar with hu
  have heq := hstat.unique hP
  set S := M.S θ kstar with hS
  have key : u * (M.r - M.cp) = M.ck * (1 + fk / u ^ 2 * S) := by
    field_simp at heq ⊢
    linear_combination -heq
  have e1 : u = M.ck / (M.r - M.cp) * (1 + fk / u ^ 2 * S) := by
    rw [div_mul_eq_mul_div, eq_div_iff hrc.ne']; exact key
  have hopt := M.optimal_cond_cc θ hko_pos hko
  have hko' : 1 - cdf (M.μ θ) ko = M.ck / (M.r - M.cp) := by
    rw [eq_div_iff hrc.ne']; linarith
  refine ⟨e1, by rw [hko']; exact e1, ?_⟩
  by_contra hcon
  push_neg at hcon
  have hmon := monotone_cdf (M.μ θ) hcon
  have hSpos : 0 < S := M.S_pos_cc θ hks hFbar
  have hpos : 0 < fk / u ^ 2 * S := by positivity
  have hq : 0 < M.ck / (M.r - M.cp) := by positivity
  have : M.ck / (M.r - M.cp) < u := by rw [e1]; nlinarith
  rw [hu] at this
  linarith

lemma alg_cc (A B C Ohkl p : ℝ) (hp : 0 < p) (hpA : p < A) (hC : 0 < C) (hCA : C < A)
    (hAB : A < B) (hOh : Ohkl ≤ B) :
    (0 < 1 - p / A ∧ 1 - p / A < 1 ∧ 0 < min (1 - p / B) ((A - p) / C) ∧
        min (1 - p / B) ((A - p) / C) < 1) ∧
    (1 - p / A < 1 - p / B ∧ 1 - p / A < (A - p) / C ∧
        1 - p / A < min (1 - p / B) ((A - p) / C)) ∧
    (1 - p / A) * Ohkl < min (1 - p / B) ((A - p) / C) * B ∧
    min (1 - p / B) ((A - p) / C) * C ≤ (1 - p / A) * A ∧
    (1 - (1 - p / A)) * A = p ∧
    p ≤ (1 - min (1 - p / B) ((A - p) / C)) * B ∧
    (1 - p / B ≤ (A - p) / C → (1 - min (1 - p / B) ((A - p) / C)) * B = p) := by
  have hA : 0 < A := by linarith
  have hB : 0 < B := by linarith
  have hpA' : p / A < 1 := (div_lt_one hA).mpr hpA
  have hpA0 : 0 < p / A := div_pos hp hA
  have hpB : p / B < p / A := div_lt_div_of_pos_left hp hA hAB
  have hL : 1 - p / A = (A - p) / A := by field_simp
  have hhat : (A - p) / A < (A - p) / C := div_lt_div_of_pos_left (by linarith) hC hCA
  have hm1 : min (1 - p / B) ((A - p) / C) ≤ 1 - p / B := min_le_left _ _
  have hm2 : min (1 - p / B) ((A - p) / C) ≤ (A - p) / C := min_le_right _ _
  have hlt : 1 - p / A < min (1 - p / B) ((A - p) / C) := lt_min (by linarith) (by linarith)
  have hpB0 : 0 < p / B := div_pos hp hB
  refine ⟨⟨by linarith, by linarith, by linarith, by linarith⟩, ⟨by linarith, by linarith, hlt⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  · calc (1 - p / A) * Ohkl ≤ (1 - p / A) * B := mul_le_mul_of_nonneg_left hOh (by linarith)
      _ < min (1 - p / B) ((A - p) / C) * B := mul_lt_mul_of_pos_right hlt hB
  · calc min (1 - p / B) ((A - p) / C) * C ≤ (A - p) / C * C :=
          mul_le_mul_of_nonneg_right hm2 hC.le
      _ = (1 - p / A) * A := by field_simp
  · field_simp; ring
  · have : (1 - (1 - p / B)) * B = p := by field_simp; ring
    nlinarith
  · intro h
    rw [min_eq_left h]; field_simp; ring

lemma mfr_opt_cc (θ : DemandType) (lam q : ℝ) :
    M.mfrProfit θ (M.optWe lam) (M.optWo lam) q = lam * M.Omega θ q :=
  M.mfr_eq_cc θ lam _ _ (by unfold optWe; ring) rfl q

lemma sup_opt_cc (θ : DemandType) (lam q : ℝ) :
    M.supProfit θ (M.optWe lam) (M.optWo lam) q = (1 - lam) * M.Omega θ q :=
  M.sup_eq_cc θ lam _ _ (by unfold optWe; ring) rfl q

theorem goal_core (kh kl piHat : ℝ)
    (hkh : IsMaxOn (M.Omega DemandType.h) (Set.Ici 0) kh) (hkh_pos : 0 < kh)
    (hkl : IsMaxOn (M.Omega DemandType.l) (Set.Ici 0) kl) (hkl_pos : 0 < kl)
    (hpi_pos : 0 < piHat) (hpi_lt : piHat < M.Omega DemandType.l kl)
    (hcross : 0 < M.Omega DemandType.l kh) :
    let lamL := M.shareLow kl piHat
    let lamH := min (M.shareHigh kh piHat) (M.shareHighHat kh kl piHat)
    (0 < lamL ∧ lamL < 1 ∧ 0 < lamH ∧ lamH < 1) ∧
    (lamL < M.shareHigh kh piHat ∧ lamL < M.shareHighHat kh kl piHat ∧ lamL < lamH) ∧
    M.mfrProfit DemandType.h (M.optWe lamL) (M.optWo lamL) kl
      < M.mfrProfit DemandType.h (M.optWe lamH) (M.optWo lamH) kh ∧
    M.mfrProfit DemandType.l (M.optWe lamH) (M.optWo lamH) kh
      ≤ M.mfrProfit DemandType.l (M.optWe lamL) (M.optWo lamL) kl ∧
    M.supProfit DemandType.l (M.optWe lamL) (M.optWo lamL) kl = piHat ∧
    piHat ≤ M.supProfit DemandType.h (M.optWe lamH) (M.optWo lamH) kh ∧
    (M.shareHigh kh piHat ≤ M.shareHighHat kh kl piHat →
      M.supProfit DemandType.h (M.optWe lamH) (M.optWo lamH) kh = piHat) ∧
    IsMaxOn (fun q => M.mfrProfit DemandType.l (M.optWe lamL) (M.optWo lamL) q) (Set.Ici 0) kl ∧
    IsMaxOn (fun q => M.supProfit DemandType.l (M.optWe lamL) (M.optWo lamL) q) (Set.Ici 0) kl ∧
    IsMaxOn (fun q => M.mfrProfit DemandType.h (M.optWe lamH) (M.optWo lamH) q) (Set.Ici 0) kh ∧
    IsMaxOn (fun q => M.supProfit DemandType.h (M.optWe lamH) (M.optWo lamH) q) (Set.Ici 0) kh := by
  intro lamL lamH
  have hCA_le : M.Omega DemandType.l kh ≤ M.Omega DemandType.l kl :=
    (isMaxOn_iff.mp hkl) kh (Set.mem_Ici.mpr hkh_pos.le)
  have hCA : M.Omega DemandType.l kh < M.Omega DemandType.l kl := by
    rcases hCA_le.lt_or_eq with h | h
    · exact h
    · exfalso
      have hmax : IsMaxOn (M.Omega DemandType.l) (Set.Ici 0) kh := by
        rw [isMaxOn_iff]; intro y hy; rw [h]; exact (isMaxOn_iff.mp hkl) y hy
      have c1 := M.optimal_cond_cc DemandType.l hkh_pos hmax
      have c2 := M.optimal_cond_cc DemandType.h hkh_pos hkh
      have hd := M.dominance kh hkh_pos.le
      have hrc := M.rcp_pos_cc
      nlinarith
  have hAB := (M.p104_omega_core kh kl hkh hkl hkl_pos).2
  have hOh : M.Omega DemandType.h kl ≤ M.Omega DemandType.h kh :=
    (isMaxOn_iff.mp hkh) kl (Set.mem_Ici.mpr hkl_pos.le)
  have key := alg_cc _ _ _ _ _ hpi_pos hpi_lt hcross hCA hAB hOh
  have hLdef : lamL = 1 - piHat / M.Omega DemandType.l kl := rfl
  have hHdef : lamH = min (1 - piHat / M.Omega DemandType.h kh)
      ((M.Omega DemandType.l kl - piHat) / M.Omega DemandType.l kh) := rfl
  have hsh : M.shareHigh kh piHat = 1 - piHat / M.Omega DemandType.h kh := rfl
  have hshh : M.shareHighHat kh kl piHat
      = (M.Omega DemandType.l kl - piHat) / M.Omega DemandType.l kh := rfl
  simp only [M.mfr_opt_cc, M.sup_opt_cc]
  rw [hsh, hshh, hLdef, hHdef]
  obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := key
  rw [hLdef, hHdef] at *
  have hcoord : ∀ (θ : DemandType) (lam ko : ℝ), 0 ≤ lam → lam ≤ 1 →
      IsMaxOn (M.Omega θ) (Set.Ici 0) ko →
      IsMaxOn (fun q => lam * M.Omega θ q) (Set.Ici 0) ko ∧
      IsMaxOn (fun q => (1 - lam) * M.Omega θ q) (Set.Ici 0) ko := by
    intro θ lam ko h0 h1 hko
    have := M.p99_opt_core θ lam (M.optWe lam) (M.optWo lam) (by unfold optWe; ring) rfl h0 h1 ko hko
    simp only [M.mfr_opt_cc, M.sup_opt_cc] at this
    exact ⟨this.2.2.1, this.2.2.2⟩
  have cL := hcoord DemandType.l _ kl k1.1.le k1.2.1.le hkl
  have cH := hcoord DemandType.h _ kh k1.2.2.1.le k1.2.2.2.le hkh
  exact ⟨k1, k2, k3, k4, k5, k6, k7, cL.1, cL.2, cH.1, cH.2⟩

end Model

end CachonCoord.CapacityForecast

open CachonCoord.CapacityForecast


theorem solution (M : Model) (kh kl piHat : ℝ)
    (hkh : IsMaxOn (M.Omega DemandType.h) (Set.Ici 0) kh) (hkh_pos : 0 < kh)
    (hkl : IsMaxOn (M.Omega DemandType.l) (Set.Ici 0) kl) (hkl_pos : 0 < kl)
    (hpi_pos : 0 < piHat) (hpi_lt : piHat < M.Omega DemandType.l kl)
    (hcross : 0 < M.Omega DemandType.l kh) :
    let lamL := M.shareLow kl piHat
    let lamH := min (M.shareHigh kh piHat) (M.shareHighHat kh kl piHat)
    -- the shares are admissible and the high type's share is larger
    (0 < lamL ∧ lamL < 1 ∧ 0 < lamH ∧ lamH < 1) ∧
    (lamL < M.shareHigh kh piHat ∧ lamL < M.shareHighHat kh kl piHat ∧ lamL < lamH) ∧
    -- the high type does not mimic the low type
    M.mfrProfit DemandType.h (M.optWe lamL) (M.optWo lamL) kl
      < M.mfrProfit DemandType.h (M.optWe lamH) (M.optWo lamH) kh ∧
    -- the low type does not mimic the high type
    M.mfrProfit DemandType.l (M.optWe lamH) (M.optWo lamH) kh
      ≤ M.mfrProfit DemandType.l (M.optWe lamL) (M.optWo lamL) kl ∧
    -- the supplier's participation
    M.supProfit DemandType.l (M.optWe lamL) (M.optWo lamL) kl = piHat ∧
    piHat ≤ M.supProfit DemandType.h (M.optWe lamH) (M.optWo lamH) kh ∧
    (M.shareHigh kh piHat ≤ M.shareHighHat kh kl piHat →
      M.supProfit DemandType.h (M.optWe lamH) (M.optWo lamH) kh = piHat) ∧
    -- coordination: each type's initial order is optimal for her and for the supplier
    IsMaxOn (fun q => M.mfrProfit DemandType.l (M.optWe lamL) (M.optWo lamL) q) (Set.Ici 0) kl ∧
    IsMaxOn (fun q => M.supProfit DemandType.l (M.optWe lamL) (M.optWo lamL) q) (Set.Ici 0) kl ∧
    IsMaxOn (fun q => M.mfrProfit DemandType.h (M.optWe lamH) (M.optWo lamH) q) (Set.Ici 0) kh ∧
    IsMaxOn (fun q => M.supProfit DemandType.h (M.optWe lamH) (M.optWo lamH) q) (Set.Ici 0) kh := by
  exact M.goal_core kh kl piHat hkh hkh_pos hkl hkl_pos hpi_pos hpi_lt hcross
