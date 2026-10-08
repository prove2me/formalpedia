-- Prove2me | solution 1 for CachonCoord.CapacityForecast.p98_expected_sales
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T06:03:17.045159+00:00
-- url     : https://prove2.me/submissions/cfc0e540-8935-456c-9dd6-dd4352d8213c

import Mathlib
import Definitions.Def_CachonCoord_CapacityForecast_Model

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

end Model

end CachonCoord.CapacityForecast

open CachonCoord.CapacityForecast


theorem solution (M : Model) (θ : DemandType) (x : ℝ) :
    M.S θ x = x - ∫ y in (0 : ℝ)..x, cdf (M.μ θ) y := by
  exact M.S_eq_cc θ x
