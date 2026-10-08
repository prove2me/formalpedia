-- Prove2me | solution 1 for CachonCoord.Proportional.eq_20
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T07:57:09.75417+00:00
-- url     : https://prove2.me/submissions/a8175aa2-15d9-44a1-97ca-36e0d38a1513

import Mathlib
import Definitions.Def_CachonCoord_Proportional_Demand
import Definitions.Def_CachonCoord_Proportional_Nash
import Definitions.Def_CachonCoord_Proportional_Game

open MeasureTheory ProbabilityTheory Filter Topology

namespace CachonCoord.Proportional

namespace Model

variable (M : Model)

lemma cpF_nonneg (y : ℝ) : 0 ≤ M.F y := by
  haveI := M.isProb; exact cdf_nonneg _ _

lemma cpF_le_one (y : ℝ) : M.F y ≤ 1 := by
  haveI := M.isProb; exact cdf_le_one _ _

lemma cpF_mono : Monotone M.F := monotone_cdf _

lemma cpF_zero : M.F 0 = 0 := M.cdf_zero

lemma cpF_nonpos (y : ℝ) (hy : y ≤ 0) : M.F y = 0 :=
  le_antisymm (by have := M.cpF_mono hy; rwa [M.cpF_zero] at this) (M.cpF_nonneg y)

lemma cpF_strict {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) : M.F x < M.F y :=
  M.strictMonoOn_cdf (Set.mem_Ici.2 hx) (Set.mem_Ici.2 (by linarith)) hxy

lemma cpF_lt_one (y : ℝ) (hy : 0 ≤ y) : M.F y < 1 :=
  lt_of_lt_of_le (M.cpF_strict hy (lt_add_one y)) (M.cpF_le_one _)

lemma cpF_pos (y : ℝ) (hy : 0 < y) : 0 < M.F y := by
  have := M.cpF_strict le_rfl hy; rwa [M.cpF_zero] at this

lemma cpF_cont : Continuous M.F := by
  rw [continuous_iff_continuousAt]; intro y
  rcases lt_trichotomy y 0 with h | h | h
  · have : M.F =ᶠ[𝓝 y] fun _ => (0:ℝ) := by
      filter_upwards [Iio_mem_nhds h] with z hz; exact M.cpF_nonpos z (le_of_lt hz)
    exact (continuousAt_const).congr this.symm
  · subst h
    have hr : ContinuousWithinAt M.F (Set.Ici 0) 0 := (cdf M.law).right_continuous 0
    have hl : ContinuousWithinAt M.F (Set.Iic 0) 0 := by
      apply (continuousWithinAt_const (b := (0:ℝ))).congr
      · intro z hz; exact M.cpF_nonpos z hz
      · exact M.cpF_nonpos 0 le_rfl
    exact continuousAt_iff_continuous_left_right.2 ⟨hl, hr⟩
  · exact (M.hasDerivAt_cdf y h).continuousAt

lemma cpF_tendsto_top : Tendsto M.F atTop (𝓝 1) := by
  haveI := M.isProb; exact tendsto_cdf_atTop M.law

lemma density_nonneg (y : ℝ) (hy : 0 < y) : 0 ≤ M.density y :=
  (M.hasDerivAt_cdf y hy).nonneg_of_monotone (monotone_cdf _)

/-- `G(q) = ∫_0^q F`. -/
noncomputable def cpG (q : ℝ) : ℝ := ∫ x in (0:ℝ)..q, M.F x

lemma cpG_deriv (q : ℝ) : HasDerivAt M.cpG (M.F q) q :=
  (M.cpF_cont.integral_hasStrictDerivAt 0 q).hasDerivAt

lemma cpG_cont : Continuous M.cpG :=
  continuous_iff_continuousAt.2 fun q => (M.cpG_deriv q).continuousAt

lemma cpG_zero : M.cpG 0 = 0 := by simp [cpG]

lemma avgF_eq (q : ℝ) : M.avgF q = M.cpG q / q := by
  simp only [avgF, cpG]; ring

lemma cpG_lt (q : ℝ) (hq : 0 < q) : M.cpG q < q * M.F q := by
  have h := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (f := M.F) (g := fun _ => M.F q) hq M.cpF_cont.continuousOn continuousOn_const
    (fun x hx => M.cpF_mono hx.2) ⟨0, ⟨le_rfl, hq.le⟩, by rw [M.cpF_zero]; exact M.cpF_pos q hq⟩
  simpa [cpG, mul_comm] using h

lemma cpG_pos (q : ℝ) (hq : 0 < q) : 0 < M.cpG q := by
  have h := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (f := fun _ => (0:ℝ)) (g := M.F) hq continuousOn_const M.cpF_cont.continuousOn
    (fun x _ => M.cpF_nonneg x) ⟨q, ⟨hq.le, le_rfl⟩, M.cpF_pos q hq⟩
  simpa [cpG] using h

lemma cpG_nonneg (q : ℝ) (hq : 0 ≤ q) : 0 ≤ M.cpG q := by
  rcases eq_or_lt_of_le hq with h | h
  · rw [← h, M.cpG_zero]
  · exact (M.cpG_pos q h).le

lemma avg_lt_F (q : ℝ) (hq : 0 < q) : M.cpG q / q < M.F q := by
  rw [div_lt_iff₀ hq]; linarith [M.cpG_lt q hq]

lemma avg_nonneg (q : ℝ) (hq : 0 < q) : 0 ≤ M.cpG q / q :=
  div_nonneg (M.cpG_nonneg q hq.le) hq.le

lemma cp_ae_nonneg : ∀ᵐ d ∂M.law, 0 ≤ d := by
  rw [ae_iff]; simp only [not_le]; exact M.nonneg

lemma cp_I_eq (x : ℝ) : M.I x = M.cpG x := by
  haveI := M.isProb
  unfold I cpG
  rcases le_or_gt 0 x with hx | hx
  · have hint : Integrable (fun d => max (x - d) 0) M.law := by
      refine Integrable.mono' (integrable_const x) ?_ ?_
      · exact (by fun_prop : Continuous fun d : ℝ => max (x-d) 0).aestronglyMeasurable
      · filter_upwards [M.cp_ae_nonneg] with d hd
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
        exact max_le (by linarith) hx
    rw [hint.integral_eq_integral_Ioc_meas_le (M := x)
      (Filter.Eventually.of_forall fun d => le_max_right _ _)]
    · have h2 : ∫ t in Set.Ioc 0 x, M.law.real {a | t ≤ max (x - a) 0}
          = ∫ t in Set.Ioc 0 x, M.F (x - t) := by
        refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
        have : {a : ℝ | t ≤ max (x - a) 0} = Set.Iic (x - t) := by
          ext a; simp only [Set.mem_setOf_eq, Set.mem_Iic]
          constructor
          · intro h; rcases le_max_iff.mp h with h | h
            · linarith
            · linarith [ht.1]
          · intro h; exact le_max_of_le_left (by linarith)
        rw [this]; simp only [F]; rw [cdf_eq_real]
      rw [h2, ← intervalIntegral.integral_of_le hx, intervalIntegral.integral_comp_sub_left]
      simp
    · filter_upwards [M.cp_ae_nonneg] with d hd
      exact max_le (by linarith) hx
  · have h1 : ∫ d, max (x - d) 0 ∂M.law = 0 := by
      rw [integral_congr_ae (g := fun _ => (0:ℝ))]
      · simp
      filter_upwards [M.cp_ae_nonneg] with d hd
      exact max_eq_right (by linarith)
    have h2 : ∫ y in (0:ℝ)..x, M.F y = ∫ y in (0:ℝ)..x, (0:ℝ) := by
      refine intervalIntegral.integral_congr ?_
      intro y hy
      rw [Set.uIcc_of_ge hx.le] at hy
      exact M.cpF_nonpos y (by linarith [hy.2])
    rw [h1, h2]; simp

lemma cp_int_min (q : ℝ) : Integrable (fun d => min q d) M.law := by
  haveI := M.isProb
  refine Integrable.mono' ((integrable_const |q|).add M.integrable.norm) ?_ ?_
  · exact (by fun_prop : Continuous fun d : ℝ => min q d).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun d => ?_)
    simp only [Real.norm_eq_abs, Pi.add_apply]
    rcases le_total q d with h | h
    · rw [min_eq_left h]; linarith [abs_nonneg d, le_abs_self q, neg_abs_le q, le_abs_self d, neg_abs_le d]
    · rw [min_eq_right h]; linarith [abs_nonneg q, le_abs_self q, neg_abs_le q, le_abs_self d, neg_abs_le d]

lemma cp_int_max (q : ℝ) : Integrable (fun d => max (q - d) 0) M.law := by
  haveI := M.isProb
  have : (fun d => max (q - d) 0) = fun d => q - min q d := by
    funext d; rcases le_total q d with h | h
    · rw [min_eq_left h, max_eq_right (by linarith)]; ring
    · rw [min_eq_right h, max_eq_left (by linarith)]
  rw [this]; exact (integrable_const q).sub (M.cp_int_min q)

lemma cp_S_eq (q : ℝ) : M.S q = q - M.cpG q := by
  haveI := M.isProb
  rw [← M.cp_I_eq]
  unfold S I
  have : (fun d => min q d) = fun d => q - max (q - d) 0 := by
    funext d; rcases le_total q d with h | h
    · rw [min_eq_left h, max_eq_right (by linarith)]; ring
    · rw [min_eq_right h, max_eq_left (by linarith)]; ring
  rw [this, integral_sub (integrable_const q) (M.cp_int_max q)]
  simp

lemma chain_eq (q : ℝ) : M.chainProfit q = M.p * (q - M.cpG q) - M.c * q := by
  rw [chainProfit, M.cp_S_eq]

/-- p. 50 formula for the retailer profit. -/
lemma rp_eq (w b x s : ℝ) (hx : 0 ≤ x) (hs : 0 ≤ s) :
    M.retailerProfit w b x s =
      (M.p - w) * x - (M.p - b) * (x / (x + s)) * M.cpG (x + s) := by
  haveI := M.isProb
  rcases eq_or_lt_of_le (add_nonneg hx hs) with h | h
  · have hx0 : x = 0 := by linarith
    have hs0 : s = 0 := by linarith
    subst hx0 hs0; simp [retailerProfit]
  · have ht : 0 ≤ x / (x + s) := div_nonneg hx h.le
    have hxq : x / (x + s) * (x + s) = x := div_mul_cancel₀ x h.ne'
    have hfun : (fun d => M.p * min x (x / (x + s) * d) + b * max (x - x / (x + s) * d) 0 - w * x)
        = fun d => x / (x + s) * (M.p * min (x + s) d + b * max ((x + s) - d) 0) - w * x := by
      funext d
      have e1 : min x (x / (x + s) * d) = x / (x + s) * min (x + s) d := by
        rw [mul_min_of_nonneg _ _ ht, hxq]
      have e2 : max (x - x / (x + s) * d) 0 = x / (x + s) * max ((x + s) - d) 0 := by
        rw [mul_max_of_nonneg _ _ ht, mul_zero, mul_sub, hxq]
      rw [e1, e2]; ring
    unfold retailerProfit
    rw [hfun, integral_sub, integral_const_mul, integral_add, integral_const_mul,
      integral_const_mul]
    · have hS := M.cp_S_eq (x + s)
      have hI := M.cp_I_eq (x + s)
      unfold S at hS; unfold I at hI
      rw [hS, hI]; simp
      linear_combination M.p * hxq
    · exact (M.cp_int_min _).const_mul _
    · exact (M.cp_int_max _).const_mul _
    · exact (((M.cp_int_min _).const_mul _).add ((M.cp_int_max _).const_mul _)).const_mul _
    · exact integrable_const _

theorem p50_core (w b x s : ℝ) (hx : 0 ≤ x) (hs : 0 ≤ s) :
    M.retailerProfit w b x s =
      (M.p - w) * x - (M.p - b) * (x / (x + s)) * ∫ y in (0 : ℝ)..(x + s), M.F y :=
  M.rp_eq w b x s hx hs
lemma p_pos : 0 < M.p := lt_trans M.c_pos M.c_lt_p

lemma phi_pos : 0 < (M.p - M.c) / M.p := div_pos (by linarith [M.c_lt_p]) M.p_pos

lemma phi_lt_one : (M.p - M.c) / M.p < 1 := by
  rw [div_lt_one M.p_pos]; linarith [M.c_pos]

lemma qo_pos (qo : ℝ) (h : M.F qo = (M.p - M.c) / M.p) : 0 < qo := by
  by_contra hc; push_neg at hc
  have := M.cpF_nonpos qo hc; rw [this] at h; linarith [M.phi_pos]

lemma chain_hasDeriv (q : ℝ) : HasDerivAt M.chainProfit (M.p - M.p * M.F q - M.c) q := by
  have h : M.chainProfit = fun q => M.p * (q - M.cpG q) - M.c * q := funext M.chain_eq
  rw [h]
  have := (((hasDerivAt_id' q).sub (M.cpG_deriv q)).const_mul M.p).sub
    ((hasDerivAt_id' q).const_mul M.c)
  exact this.congr_deriv (by ring)

lemma chain_strict (qo : ℝ) (hqo : M.F qo = (M.p - M.c) / M.p) (q : ℝ) (hq : 0 ≤ q)
    (hne : q ≠ qo) : M.chainProfit q < M.chainProfit qo := by
  have hqo0 := M.qo_pos qo hqo
  have hcont : Continuous M.chainProfit :=
    continuous_iff_continuousAt.2 fun x => (M.chain_hasDeriv x).continuousAt
  have e : M.p * ((M.p - M.c) / M.p) = M.p - M.c := by field_simp [M.p_pos.ne']
  have hderiv : ∀ x, deriv M.chainProfit x = M.p * ((M.p - M.c) / M.p - M.F x) := by
    intro x; rw [(M.chain_hasDeriv x).deriv]; linear_combination -e
  rcases lt_or_gt_of_ne hne with h | h
  · have hm : StrictMonoOn M.chainProfit (Set.Icc 0 qo) :=
      strictMonoOn_of_deriv_pos (convex_Icc 0 qo) hcont.continuousOn (by
        intro x hx; rw [interior_Icc] at hx; rw [hderiv]; apply mul_pos M.p_pos
        rw [← hqo]; linarith [M.cpF_strict hx.1.le hx.2])
    exact hm ⟨hq, h.le⟩ ⟨hqo0.le, le_rfl⟩ h
  · have ha : StrictAntiOn M.chainProfit (Set.Ici qo) :=
      strictAntiOn_of_deriv_neg (convex_Ici qo) hcont.continuousOn (by
        intro x hx; rw [interior_Ici] at hx; rw [hderiv]; apply mul_neg_of_pos_of_neg M.p_pos
        rw [← hqo]; linarith [M.cpF_strict hqo0.le hx])
    exact ha (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 h.le) h

lemma exists_F_eq (v : ℝ) (h0 : 0 < v) (h1 : v < 1) : ∃ q, 0 < q ∧ M.F q = v := by
  obtain ⟨B, hB⟩ := ((M.cpF_tendsto_top.eventually (lt_mem_nhds h1)).and
    (eventually_ge_atTop 0)).exists
  obtain ⟨c, hc, hFc⟩ := intermediate_value_Icc hB.2 M.cpF_cont.continuousOn
    ⟨by rw [M.cpF_zero]; exact h0.le, hB.1.le⟩
  refine ⟨c, ?_, hFc⟩
  rcases eq_or_lt_of_le hc.1 with h | h
  · rw [← h, M.cpF_zero] at hFc; linarith
  · exact h

theorem eq20_core : (∃ qo : ℝ, 0 < qo ∧ M.F qo = (M.p - M.c) / M.p) ∧
      ∀ q : ℝ, 0 ≤ q →
        (IsMaxOn M.chainProfit (Set.Ici 0) q ↔ M.F q = (M.p - M.c) / M.p) := by
  obtain ⟨qo, hqo0, hqo⟩ := M.exists_F_eq _ M.phi_pos M.phi_lt_one
  refine ⟨⟨qo, hqo0, hqo⟩, fun q hq => ⟨fun hmax => ?_, fun hF => ?_⟩⟩
  · by_contra hne
    have hne' : q ≠ qo := fun h => hne (h ▸ hqo)
    have h1 := M.chain_strict qo hqo q hq hne'
    have h2 := isMaxOn_iff.1 hmax qo (Set.mem_Ici.2 hqo0.le)
    linarith
  · refine isMaxOn_iff.2 fun y hy => ?_
    rcases eq_or_ne y q with h | h
    · rw [h]
    · exact (M.chain_strict q hF y hy h).le

lemma avg_deriv (q : ℝ) (hq : 0 < q) :
    HasDerivAt (fun q => M.cpG q / q) ((M.F q * q - M.cpG q) / q ^ 2) q := by
  have h : HasDerivAt (fun y => M.cpG y / y) ((M.F q * q - M.cpG q * 1) / q ^ 2) q :=
    (M.cpG_deriv q).div (hasDerivAt_id' q) hq.ne'
  exact h.congr_deriv (by ring)

lemma avg_strictMono : StrictMonoOn (fun q => M.cpG q / q) (Set.Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · intro x hx; exact (M.avg_deriv x hx).continuousAt.continuousWithinAt
  · intro x hx; rw [interior_Ioi] at hx; rw [(M.avg_deriv x hx).deriv]
    have hx' : (0:ℝ) < x := hx
    apply div_pos _ (by positivity); linarith [M.cpG_lt x hx', mul_comm x (M.F x)]

lemma lhs_eq (n : ℕ) (q : ℝ) :
    M.lhs22 n q = 1 / (n : ℝ) * M.F q + ((n : ℝ) - 1) / n * (M.cpG q / q) := by
  rw [lhs22, avgF_eq]

lemma lhs_eq2 (n : ℕ) (hn : 1 ≤ n) (q : ℝ) :
    M.lhs22 n q = M.cpG q / q + (M.F q - M.cpG q / q) / n := by
  rw [M.lhs_eq]
  have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  generalize M.cpG q / q = A
  field_simp; ring

lemma lhs_bounds (n : ℕ) (hn : 1 ≤ n) (q : ℝ) (hq : 0 < q) :
    0 < M.lhs22 n q ∧ M.cpG q / q ≤ M.lhs22 n q ∧ M.lhs22 n q ≤ M.F q ∧ M.lhs22 n q < 1 := by
  rw [M.lhs_eq2 n hn]
  have hFA := M.avg_lt_F q hq
  have hA0 := M.avg_nonneg q hq
  have hF1 := M.cpF_lt_one q hq.le
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have h1 : 0 < (M.F q - M.cpG q / q) / n := div_pos (by linarith) (by linarith)
  have h2 : (M.F q - M.cpG q / q) / n ≤ M.F q - M.cpG q / q := div_le_self (by linarith) hn'
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

lemma lhs_lt_F (n : ℕ) (hn : 2 ≤ n) (q : ℝ) (hq : 0 < q) : M.lhs22 n q < M.F q := by
  rw [M.lhs_eq2 n (by omega)]
  have hFA := M.avg_lt_F q hq
  have hn' : (1:ℝ) < n := by exact_mod_cast hn
  have h2 : (M.F q - M.cpG q / q) / n < M.F q - M.cpG q / q := div_lt_self (by linarith) hn'
  linarith

lemma lhs_strictMono (n : ℕ) (hn : 1 ≤ n) : StrictMonoOn (M.lhs22 n) (Set.Ioi 0) := by
  intro x hx y hy hxy
  rw [M.lhs_eq, M.lhs_eq]
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have h1 : 0 < 1 / (n : ℝ) := by positivity
  have h2 : 0 ≤ ((n : ℝ) - 1) / n := div_nonneg (by linarith) (by linarith)
  have hx' : (0:ℝ) < x := hx
  have hF := M.cpF_strict hx'.le hxy
  have hA : M.cpG x / x < M.cpG y / y := M.avg_strictMono hx hy hxy
  nlinarith [mul_lt_mul_of_pos_left hF h1, mul_le_mul_of_nonneg_left hA.le h2]

lemma lhs_cont (n : ℕ) : ContinuousOn (M.lhs22 n) (Set.Ioi 0) := by
  have : Set.EqOn (M.lhs22 n)
      (fun q => 1 / (n : ℝ) * M.F q + ((n : ℝ) - 1) / n * (M.cpG q / q)) (Set.Ioi 0) :=
    fun q _ => M.lhs_eq n q
  refine ContinuousOn.congr ?_ this
  exact (continuousOn_const.mul M.cpF_cont.continuousOn).add (continuousOn_const.mul
    (M.cpG_cont.continuousOn.div continuousOn_id (fun x hx => ne_of_gt hx)))

lemma lhs_tendsto0 (n : ℕ) (hn : 1 ≤ n) : Tendsto (M.lhs22 n) (𝓝[>] 0) (𝓝 0) := by
  have hF : Tendsto M.F (𝓝[>] 0) (𝓝 0) := by
    have := (M.cpF_cont.continuousAt (x := 0)).tendsto
    rw [M.cpF_zero] at this; exact this.mono_left nhdsWithin_le_nhds
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hF
  · filter_upwards [self_mem_nhdsWithin] with q hq; exact (M.lhs_bounds n hn q hq).1.le
  · filter_upwards [self_mem_nhdsWithin] with q hq; exact (M.lhs_bounds n hn q hq).2.2.1

lemma avg_ge (B q : ℝ) (hB : 0 ≤ B) (hq : B ≤ q) : (q - B) * M.F B ≤ M.cpG q := by
  have hsplit : M.cpG q = M.cpG B + ∫ x in B..q, M.F x := by
    unfold cpG
    rw [intervalIntegral.integral_add_adjacent_intervals] <;>
      exact M.cpF_cont.intervalIntegrable _ _
  have hmono : ∫ x in B..q, M.F B ≤ ∫ x in B..q, M.F x :=
    intervalIntegral.integral_mono_on hq intervalIntegrable_const
      (M.cpF_cont.intervalIntegrable _ _) (fun x hx => M.cpF_mono hx.1)
  simp at hmono
  linarith [M.cpG_nonneg B hB]

lemma lhs_tendsto_top (n : ℕ) (hn : 1 ≤ n) : Tendsto (M.lhs22 n) atTop (𝓝 1) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨B, hB⟩ := ((M.cpF_tendsto_top.eventually
    (lt_mem_nhds (show 1 - ε / 2 < 1 by linarith))).and (eventually_ge_atTop 0)).exists
  refine ⟨max (B + 1) (2 * B / ε + 1), fun q hq => ?_⟩
  have hq1 : B + 1 ≤ q := le_trans (le_max_left _ _) hq
  have hq2 : 2 * B / ε + 1 ≤ q := le_trans (le_max_right _ _) hq
  have hqpos : 0 < q := by linarith [hB.2]
  have hA : (q - B) * M.F B ≤ M.cpG q := M.avg_ge B q hB.2 (by linarith)
  have hFB := hB.1
  have hFB1 := M.cpF_le_one B
  have h2B : 2 * B < ε * q := by
    have := (div_lt_iff₀ hε).1 (show 2 * B / ε < q by linarith); linarith
  have hb := M.lhs_bounds n hn q hqpos
  have hAq : 1 - ε < M.cpG q / q := by
    rw [lt_div_iff₀ hqpos]
    nlinarith [mul_lt_mul_of_pos_left hFB hqpos, mul_le_mul_of_nonneg_left hFB1 hB.2]
  rw [Real.dist_eq, abs_sub_lt_iff]; constructor <;> linarith [hb.2.1, hb.2.2.2]

lemma lhs_root (n : ℕ) (hn : 1 ≤ n) (r : ℝ) (h0 : 0 < r) (h1 : r < 1) :
    ∃! qs : ℝ, 0 < qs ∧ M.lhs22 n qs = r := by
  obtain ⟨a, ha1, ha2⟩ :=
    (((M.lhs_tendsto0 n hn).eventually (gt_mem_nhds h0)).and self_mem_nhdsWithin).exists
  obtain ⟨b, hb1, hb2⟩ :=
    (((M.lhs_tendsto_top n hn).eventually (lt_mem_nhds h1)).and (eventually_ge_atTop a)).exists
  have ha : (0:ℝ) < a := ha2
  obtain ⟨c, hc, hLc⟩ := intermediate_value_Icc hb2
    ((M.lhs_cont n).mono (fun x hx => lt_of_lt_of_le ha hx.1)) ⟨ha1.le, hb1.le⟩
  refine ⟨c, ⟨lt_of_lt_of_le ha hc.1, hLc⟩, fun y hy => ?_⟩
  exact (M.lhs_strictMono n hn).injOn hy.1 (lt_of_lt_of_le ha hc.1) (hy.2.trans hLc.symm)

lemma r_bounds (w b : ℝ) (hbw : b < w) (hwp : w < M.p) :
    0 < (M.p - w) / (M.p - b) ∧ (M.p - w) / (M.p - b) < 1 :=
  ⟨div_pos (by linarith) (by linarith), (div_lt_one (by linarith)).2 (by linarith)⟩

theorem eq22_core (n : ℕ) (hn : 2 ≤ n) :
    StrictMonoOn (M.lhs22 n) (Set.Ioi 0) ∧
      Tendsto (M.lhs22 n) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (M.lhs22 n) atTop (𝓝 1) ∧
      ∀ w b : ℝ, b < w → w < M.p →
        ∃! qs : ℝ, 0 < qs ∧ M.lhs22 n qs = (M.p - w) / (M.p - b) :=
  ⟨M.lhs_strictMono n (by omega), M.lhs_tendsto0 n (by omega), M.lhs_tendsto_top n (by omega),
    fun w b hbw hwp => M.lhs_root n (by omega) _ (M.r_bounds w b hbw hwp).1
      (M.r_bounds w b hbw hwp).2⟩

theorem p51_core (m n : ℕ) (hm : 1 ≤ m) (hmn : m < n) :
    (∀ q : ℝ, 0 < q → M.lhs22 n q < M.lhs22 m q) ∧
      ∀ w b : ℝ, b < w → w < M.p → ∀ qm qn : ℝ, 0 < qm → 0 < qn →
        M.lhs22 m qm = (M.p - w) / (M.p - b) → M.lhs22 n qn = (M.p - w) / (M.p - b) →
        qm < qn := by
  have hlt : ∀ q : ℝ, 0 < q → M.lhs22 n q < M.lhs22 m q := by
    intro q hq
    rw [M.lhs_eq2 n (by omega), M.lhs_eq2 m hm]
    have hFA := M.avg_lt_F q hq
    have hm' : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have hmn' : (m:ℝ) < n := by exact_mod_cast hmn
    have := div_lt_div_of_pos_left (sub_pos.2 hFA) hm' hmn'
    linarith
  refine ⟨hlt, fun w b hbw hwp qm qn hqm hqn hm1 hn1 => ?_⟩
  have : M.lhs22 m qm < M.lhs22 m qn := by rw [hm1, ← hn1]; exact hlt qn hqn
  exact ((M.lhs_strictMono m hm).lt_iff_lt hqm hqn).1 this

lemma what_eq (n : ℕ) (q : ℝ) : M.what n q = M.p * (1 - M.lhs22 n q) := by
  unfold what lhs22; ring

theorem what_core (n : ℕ) (hn : 2 ≤ n) (qo : ℝ) (hqo : M.F qo = (M.p - M.c) / M.p) :
    M.c < M.what n qo ∧ 0 < M.supplierProfit (M.what n qo) 0 qo := by
  have hq := M.qo_pos qo hqo
  have hb := M.lhs_lt_F n hn qo hq
  rw [hqo] at hb
  have e : M.p * ((M.p - M.c) / M.p) = M.p - M.c := by field_simp [M.p_pos.ne']
  have hc : M.c < M.what n qo := by
    rw [M.what_eq]; nlinarith [mul_lt_mul_of_pos_left hb M.p_pos]
  refine ⟨hc, ?_⟩
  simp only [supplierProfit, zero_mul, sub_zero]
  nlinarith [mul_pos (sub_pos.2 hc) hq]

lemma supplier_wb (n : ℕ) (hn : 1 ≤ n) (b qo : ℝ) (hqo : M.F qo = (M.p - M.c) / M.p) :
    M.supplierProfit (M.wb n b qo) b qo =
      (M.p * ((n : ℝ) - 1) + b) / (M.p * n) * M.chainProfit qo := by
  have hq := M.qo_pos qo hqo
  have hp := M.p_pos
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  unfold supplierProfit wb
  rw [M.cp_I_eq, M.chain_eq, M.avgF_eq]
  field_simp
  ring

lemma chain_pos (qo : ℝ) (hqo : M.F qo = (M.p - M.c) / M.p) : 0 < M.chainProfit qo := by
  have hq := M.qo_pos qo hqo
  have hG := M.cpG_lt qo hq
  rw [hqo] at hG
  rw [M.chain_eq]
  have e : qo * ((M.p - M.c) / M.p) * M.p = qo * (M.p - M.c) := by field_simp [M.p_pos.ne']
  nlinarith [mul_lt_mul_of_pos_left hG M.p_pos]

theorem p53_core (n : ℕ) (hn : 2 ≤ n) (qo : ℝ) (hqo : M.F qo = (M.p - M.c) / M.p) :
    0 < M.chainProfit qo ∧
      M.supplierProfit (M.wb n 0 qo) 0 qo / M.chainProfit qo = ((n : ℝ) - 1) / n := by
  have hP := M.chain_pos qo hqo
  refine ⟨hP, ?_⟩
  rw [M.supplier_wb n (by omega) 0 qo hqo, mul_div_assoc, div_self hP.ne', mul_one, add_zero,
    mul_div_mul_left _ _ M.p_pos.ne']

theorem dev_core (n : ℕ) (hn : 2 ≤ n) (qo : ℝ) (hqo : M.F qo = (M.p - M.c) / M.p)
    (hf : 0 < M.density qo) :
    HasDerivAt (fun q => M.supplierProfit (M.what n q) 0 q)
        (-(qo * M.p * M.density qo) / n) qo ∧
      -(qo * M.p * M.density qo) / n < 0 := by
  have hq := M.qo_pos qo hqo
  have hn' : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hp := M.p_pos
  refine ⟨?_, ?_⟩
  · have hfun : (fun q => M.supplierProfit (M.what n q) 0 q) = fun q =>
        M.p * (1 - 1 / (n : ℝ) * M.F q - ((n : ℝ) - 1) / n * (q⁻¹ * M.cpG q)) * q - M.c * q := by
      funext q; simp only [supplierProfit, what, avgF, cpG, zero_mul, sub_zero, one_div]
    rw [hfun]
    have hF : HasDerivAt M.F (M.density qo) qo := M.hasDerivAt_cdf qo hq
    have hinv : HasDerivAt (fun q : ℝ => q⁻¹) (-(qo ^ 2)⁻¹) qo := hasDerivAt_inv hq.ne'
    have h : HasDerivAt (fun q =>
        M.p * (1 - 1 / (n : ℝ) * M.F q - ((n : ℝ) - 1) / n * (q⁻¹ * M.cpG q)) * q - M.c * q)
        (M.p * (0 - 1 / (n : ℝ) * M.density qo - ((n : ℝ) - 1) / n * (-(qo ^ 2)⁻¹ * M.cpG qo +
          qo⁻¹ * M.F qo)) * qo + M.p * (1 - 1 / (n : ℝ) * M.F qo - ((n : ℝ) - 1) / n *
          (qo⁻¹ * M.cpG qo)) * 1 - M.c * 1) qo := (((((hasDerivAt_const qo (1:ℝ)).sub (hF.const_mul (1 / (n : ℝ)))).sub
      ((hinv.mul (M.cpG_deriv qo)).const_mul (((n : ℝ) - 1) / n))).const_mul M.p).mul
      (hasDerivAt_id' qo)).sub ((hasDerivAt_id' qo).const_mul M.c)
    refine h.congr_deriv ?_
    rw [hqo]; field_simp; ring
  · have := mul_pos (mul_pos hq M.p_pos) hf
    exact div_neg_of_neg_of_pos (by linarith) hn'

end Model

end CachonCoord.Proportional

open CachonCoord.Proportional


theorem solution (M : Model) :
    (∃ qo : ℝ, 0 < qo ∧ M.F qo = (M.p - M.c) / M.p) ∧
      ∀ q : ℝ, 0 ≤ q →
        (IsMaxOn M.chainProfit (Set.Ici 0) q ↔ M.F q = (M.p - M.c) / M.p) := by
  exact M.eq20_core
