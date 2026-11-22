-- Prove2me | solution 1 for ExplicitFormula.mellin_entire_and_inv_bound_of_piecewise_smooth
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T15:38:30.996833+00:00
-- url     : https://prove2.me/submissions/ec18e1c1-b301-4a83-af91-aca302268c97

import Mathlib

open Filter Topology
open scoped Real ContDiff

set_option autoImplicit false

namespace Sol_ExplicitFormula_mellin_entire_and_inv_bound_of_piecewise_smooth

open MeasureTheory Set
open scoped Asymptotics

/-- Change of variables `y = exp x` on the whole line. -/
theorem integral_comp_exp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℝ → E) :
    ∫ x : ℝ, Real.exp x • g (Real.exp x) = ∫ y in Ioi (0 : ℝ), g y := by
  have h := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn g
  rw [image_univ, Real.range_exp] at h
  rw [h, Measure.restrict_univ]
  simp only [abs_of_pos (Real.exp_pos _)]

theorem integrable_comp_exp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℝ → E) :
    Integrable (fun x : ℝ => Real.exp x • g (Real.exp x)) ↔ IntegrableOn g (Ioi (0 : ℝ)) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn g
  rw [image_univ, Real.range_exp] at h
  rw [h, integrableOn_univ]
  simp only [abs_of_pos (Real.exp_pos _)]

/-- An exponential growth bound becomes a real-power bound after composition with `log`. -/
theorem isBigO_comp_log_rpow_of_isBigO_exp {g : ℝ → ℂ} {c : ℝ} {l L : Filter ℝ}
    (h : g =O[l] (fun x ↦ Real.exp (c * x)))
    (ht : Tendsto Real.log L l) (hpos : ∀ᶠ t in L, 0 < t) :
    (fun t ↦ g (Real.log t)) =O[L] (fun t ↦ t ^ c) := by
  apply (h.comp_tendsto ht).congr' EventuallyEq.rfl
  filter_upwards [hpos] with t ht
  simp only [Function.comp_apply, Real.rpow_def_of_pos ht, mul_comm]

theorem mellinConvergent_of_integrable_logWeight (f : ℝ → ℂ) (s : ℂ)
    (h : Integrable (fun x : ℝ ↦ (Real.exp (s.re * x) : ℂ) * f x)) :
    MellinConvergent (fun t ↦ f (Real.log t)) s := by
  let phase (x : ℝ) := Complex.exp ((x : ℂ) * (s - s.re))
  have hc : Continuous phase := by
    dsimp [phase]
    fun_prop
  have hunit (x : ℝ) : ‖phase x‖ ≤ 1 := by
    simp [phase, Complex.norm_exp, Complex.mul_re]
  apply (integrable_comp_exp _).mp
  apply (h.bdd_mul hc.aestronglyMeasurable (Eventually.of_forall hunit)).congr
  filter_upwards with x
  simp only [Real.log_exp, Complex.real_smul, smul_eq_mul]
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos x).ne'),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp]
  simp only [phase, Complex.ofReal_exp, Complex.ofReal_mul, ← mul_assoc, ← Complex.exp_add]
  congr 2
  ring


section jumps

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {f g l r : ℝ → E}

private theorem intervalIntegral_deriv_eq_sub_add_sum_jumps (S : Finset ℝ)
    (hg : Integrable g)
    (hl : ∀ x ∈ S, Tendsto f (𝓝[<] x) (𝓝 (l x)))
    (hr : ∀ x ∈ S, Tendsto f (𝓝[>] x) (𝓝 (r x)))
    {a b : ℝ} {fa fb : E} (hab : a < b)
    (ha : Tendsto f (𝓝[>] a) (𝓝 fa)) (hb : Tendsto f (𝓝[<] b) (𝓝 fb))
    (hderiv : ∀ x ∈ Ioo a b, x ∉ S → HasDerivAt f (g x) x) :
    (∫ x in a..b, g x) = fb - fa + ∑ x ∈ S, if x ∈ Ioo a b then l x - r x else 0 := by
  classical
  induction S using Finset.induction_on generalizing a b fa fb with
  | empty =>
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hab
      (fun x hx ↦ hderiv x hx (Finset.notMem_empty x)) hg.intervalIntegrable ha hb
  | @insert c S hc ih =>
    rw [Finset.sum_insert hc]
    have hlS x (hx : x ∈ S) := hl x (Finset.mem_insert_of_mem hx)
    have hrS x (hx : x ∈ S) := hr x (Finset.mem_insert_of_mem hx)
    by_cases hcI : c ∈ Ioo a b
    · rw [if_pos hcI, ← intervalIntegral.integral_add_adjacent_intervals
        (f := g) (b := c) hg.intervalIntegrable hg.intervalIntegrable]
      have habS : ∀ x ∈ Ioo a b, x ∉ S → x ≠ c → HasDerivAt f (g x) x :=
        fun x hx hxS hxc ↦ hderiv x hx (by simpa [hxc] using hxS)
      rw [ih hlS hrS hcI.1 ha (hl c (Finset.mem_insert_self c S))
        (fun x hx hxS ↦ habS x ⟨hx.1, hx.2.trans hcI.2⟩ hxS hx.2.ne),
        ih hlS hrS hcI.2 (hr c (Finset.mem_insert_self c S)) hb
        (fun x hx hxS ↦ habS x ⟨hcI.1.trans hx.1, hx.2⟩ hxS hx.1.ne')]
      have hsum : (∑ x ∈ S, if x ∈ Ioo a c then l x - r x else 0) +
          (∑ x ∈ S, if x ∈ Ioo c b then l x - r x else 0) =
          ∑ x ∈ S, if x ∈ Ioo a b then l x - r x else 0 := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun x hx ↦ ?_
        rcases lt_or_gt_of_ne (ne_of_mem_of_not_mem hx hc) with hxc | hcx
        · have hiff : x ∈ Ioo a c ↔ x ∈ Ioo a b :=
            ⟨fun h ↦ ⟨h.1, hxc.trans hcI.2⟩, fun h ↦ ⟨h.1, hxc⟩⟩
          simp [hiff, hxc.not_gt]
        · have hiff : x ∈ Ioo c b ↔ x ∈ Ioo a b :=
            ⟨fun h ↦ ⟨hcI.1.trans hcx, h.2⟩, fun h ↦ ⟨hcx, h.2⟩⟩
          simp [hiff, hcx.not_gt]
      rw [← hsum]
      abel
    · rw [if_neg hcI, zero_add]
      exact ih hlS hrS hab ha hb fun x hx hxS ↦
        hderiv x hx (by simpa [ne_of_mem_of_not_mem hx hcI] using hxS)

/-- If an integrable function is the derivative of a function off finitely many jump points,
its integral equals the difference of the limits at infinity plus the sum of the left limits
minus the right limits at the jumps. -/
theorem integral_deriv_eq_sub_add_sum_jumps (S : Finset ℝ) (hg : Integrable g)
    (hderiv : ∀ x ∉ S, HasDerivAt f (g x) x)
    (hl : ∀ x ∈ S, Tendsto f (𝓝[<] x) (𝓝 (l x)))
    (hr : ∀ x ∈ S, Tendsto f (𝓝[>] x) (𝓝 (r x)))
    {fa fb : E} (ha : Tendsto f atBot (𝓝 fa)) (hb : Tendsto f atTop (𝓝 fb)) :
    (∫ x, g x) = fb - fa + ∑ x ∈ S, (l x - r x) := by
  classical
  have hlim := intervalIntegral_tendsto_integral hg tendsto_neg_atTop_atBot
    (tendsto_id : Tendsto (fun x : ℝ ↦ x) atTop atTop)
  refine tendsto_nhds_unique hlim (((hb.sub (ha.comp tendsto_neg_atTop_atBot)).add
    (tendsto_const_nhds (x := ∑ x ∈ S, (l x - r x)))).congr' ?_)
  have hS : ∀ᶠ t : ℝ in atTop, ∀ x ∈ S, x ∈ Ioo (-t) t := by
    apply (Filter.eventually_all_finset S).mpr
    intro x _
    filter_upwards [eventually_gt_atTop (-x), eventually_gt_atTop x] with t h₁ h₂
    exact ⟨neg_lt.mp h₁, h₂⟩
  filter_upwards [hS, eventually_gt_atTop (0 : ℝ)] with t htS ht
  have hleft := (hderiv (-t) (fun h ↦ (htS _ h).1.false)).continuousAt
  have hright := (hderiv t (fun h ↦ (htS _ h).2.false)).continuousAt
  change f t - f (-t) + _ = ∫ x in -t..t, g x
  rw [intervalIntegral_deriv_eq_sub_add_sum_jumps S hg hl hr ((neg_lt_zero.mpr ht).trans ht)
    hleft.continuousWithinAt hright.continuousWithinAt (fun x _ hx ↦ hderiv x hx)]
  congr 1
  exact Finset.sum_congr rfl fun x hx ↦ (if_pos (htS x hx)).symm

end jumps

/-- The hypotheses of the target on the logarithmic profile. -/
def IsPiecewiseSmoothMellinTest (f : ℝ → ℂ) : Prop :=
  (∃ S : Finset ℝ, ContDiffOn ℝ ∞ f (S : Set ℝ)ᶜ ∧
    ∀ (j : ℕ) (x : ℝ), x ∈ S →
      (∃ l : ℂ, Tendsto (iteratedDeriv j f) (𝓝[<] x) (𝓝 l)) ∧
      (∃ r : ℂ, Tendsto (iteratedDeriv j f) (𝓝[>] x) (𝓝 r))) ∧
  ∀ N : ℕ, ∃ C > (0 : ℝ), ∃ T > (0 : ℝ), ∀ x : ℝ, T < |x| →
    ‖f x‖ < C * Real.exp (-(N : ℝ) * |x|) ∧
    ‖deriv f x‖ < C * Real.exp (-(N : ℝ) * |x|)

local notation "logMellin" =>
  (fun (f : ℝ → ℂ) ↦ mellin (fun t ↦ f (Real.log t)))

theorem mellinConvergent_of_piecewiseSmoothMellinTest
    {f : ℝ → ℂ} (hf : IsPiecewiseSmoothMellinTest f) (s : ℂ) :
    MellinConvergent (fun t ↦ f (Real.log t)) s := by
  obtain ⟨⟨S, hsmooth, hlimits⟩, hdecay⟩ := hf
  apply mellinConvergent_of_integrable_logWeight
  let w (x : ℝ) : ℂ := Real.exp (s.re * x)
  let g (x : ℝ) := w x * f x
  change Integrable g
  have hw : Continuous w := by
    dsimp [w]
    fun_prop
  have hcont : ContinuousOn g (S : Set ℝ)ᶜ :=
    hw.continuousOn.mul hsmooth.continuousOn
  have hmeas : Measurable g :=
    measurable_of_measurable_on_compl_finite _ S.finite_toSet
      (continuousOn_iff_continuous_domRestrict.mp hcont).measurable
  -- The weighted profile is locally integrable even at the jumps.
  have hloc : LocallyIntegrable g := by
    intro x
    by_cases hx : x ∈ S
    · obtain ⟨⟨l, hl⟩, ⟨r, hr⟩⟩ := hlimits 0 x hx
      simp only [iteratedDeriv_zero] at hl hr
      rw [← nhdsNE_sup_pure x, ← nhdsLT_sup_nhdsGT x, IntegrableAtFilter.sup_iff,
        IntegrableAtFilter.sup_iff]
      have hside {u : Set ℝ} {a : ℂ} (hu : MeasurableSet u)
          (ha : Tendsto f (𝓝[u] x) (𝓝 a)) : IntegrableAtFilter g (𝓝[u] x) volume := by
        have := hu.nhdsWithin_isMeasurablyGenerated x
        exact ((hw.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).mul ha).integrableAtFilter
          hmeas.aestronglyMeasurable.stronglyMeasurableAtFilter (volume.finiteAt_nhdsWithin x u)
      exact ⟨⟨hside measurableSet_Iio hl, hside measurableSet_Ioi hr⟩,
        ⟨{x}, by simp, integrableOn_singleton (hx := measure_singleton_lt_top)⟩⟩
    · have hx' : (S : Set ℝ)ᶜ ∈ 𝓝 x :=
        S.finite_toSet.isClosed.isOpen_compl.mem_nhds hx
      exact ((hcont x hx).continuousAt hx').integrableAtFilter
        hmeas.aestronglyMeasurable.stronglyMeasurableAtFilter (volume.finiteAt_nhds x)
  -- Dominate both tails by a constant times exp (-|x|).
  obtain ⟨N, hN⟩ := exists_nat_gt (|s.re| + 1)
  obtain ⟨C, hC, T, hT, htail⟩ := hdecay N
  have hbound (x : ℝ) (hx : T < |x|) : ‖g x‖ ≤ C * Real.exp (-|x|) := by
    have hprod : s.re * x ≤ |s.re| * |x| := by
      rw [← abs_mul]
      exact le_abs_self _
    have hrate : (|s.re| + 1) * |x| ≤ (N : ℝ) * |x| :=
      mul_le_mul_of_nonneg_right hN.le (abs_nonneg x)
    rw [show ‖g x‖ = Real.exp (s.re * x) * ‖f x‖ by
      simp only [g, w, norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le]]
    calc
      _ ≤ Real.exp (s.re * x) * (C * Real.exp (-(N : ℝ) * |x|)) :=
        mul_le_mul_of_nonneg_left (htail x hx).1.le (Real.exp_pos _).le
      _ = C * Real.exp (s.re * x + -(N : ℝ) * |x|) := by rw [Real.exp_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hprod, hrate])) hC.le
  refine integrable_iff_integrableAtFilter_atBot_atTop.mpr ⟨⟨?_, ?_⟩, hloc⟩
  · refine ⟨Iio (-T), Iio_mem_atBot _, ?_⟩
    refine (((integrableOn_exp_Iic (-T)).mono_set Iio_subset_Iic_self).const_mul C).mono'
      hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Iio] with x hx
    have hx' : x < -T := hx
    have hneg : x < 0 := hx'.trans (neg_neg_of_pos hT)
    have hTx : T < -x := by linarith only [hx']
    simpa only [abs_of_neg hneg, neg_neg] using
      hbound x (by rwa [abs_of_neg hneg])
  · refine ⟨Ioi T, Ioi_mem_atTop _, ?_⟩
    refine ((integrableOn_exp_neg_Ioi T).const_mul C).mono'
      hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hpos : 0 < x := hT.trans hx
    simpa [abs_of_pos hpos] using hbound x (by simpa [abs_of_pos hpos] using hx)

/-- Paper: Lemma B.4.1.1, p. 607. The Mellin transform of a test function
with finitely many jumps is entire. -/
theorem differentiable_mellin_of_piecewiseSmoothMellinTest
    {f : ℝ → ℂ} (hf : IsPiecewiseSmoothMellinTest f) :
    Differentiable ℂ (logMellin f) := by
  obtain ⟨⟨S, hsmooth, hlimits⟩, hdecay⟩ := hf
  have hcont := hsmooth.continuousOn
  have hmeas : Measurable f :=
    hcont.measurable_of_countable_compl (by simpa using S.finite_toSet.countable)
  have hbounded (x : ℝ) : (𝓝 x).IsBoundedUnder (· ≤ ·) (fun y ↦ ‖f y‖) := by
    by_cases hx : x ∈ S
    · obtain ⟨⟨l, hl⟩, ⟨r, hr⟩⟩ := hlimits 0 x hx
      simp only [iteratedDeriv_zero] at hl hr
      rw [← nhdsNE_sup_pure x, ← nhdsLT_sup_nhdsGT x, IsBoundedUnder, Filter.map_sup, Filter.map_sup]
      exact isBounded_sup (isBounded_sup hl.norm.isBoundedUnder_le hr.norm.isBoundedUnder_le)
        ⟨‖f x‖, by simp⟩
    · have hfx := (hcont x hx).continuousAt (S.finite_toSet.isClosed.isOpen_compl.mem_nhds hx)
      exact hfx.tendsto.norm.isBoundedUnder_le
  have hloc : LocallyIntegrableOn (fun t ↦ f (Real.log t)) (Ioi 0) := by
    intro t ht
    have ht' : 0 < t := ht
    have hlog := (Real.continuousAt_log ht'.ne').tendsto
    exact ((volume.finiteAt_nhds t).integrableAtFilter
      (hmeas.comp Real.measurable_log).aestronglyMeasurable.stronglyMeasurableAtFilter
      (hlog.isBoundedUnder_comp (hbounded (Real.log t)))).filter_mono nhdsWithin_le_nhds
  intro s
  obtain ⟨N, hN⟩ := exists_nat_gt |s.re|
  obtain ⟨C, _, T, hT, hbound⟩ := hdecay N
  have htop : f =O[atTop] (fun x ↦ Real.exp (-(N : ℝ) * x)) := by
    apply Asymptotics.IsBigO.of_bound C
    filter_upwards [eventually_gt_atTop T] with x hx
    have hx' := hT.trans hx
    simpa only [abs_of_pos hx', Real.norm_of_nonneg (Real.exp_pos _).le]
      using (hbound x (by simpa only [abs_of_pos hx'] using hx)).1.le
  have hbot : f =O[atBot] (fun x ↦ Real.exp ((N : ℝ) * x)) := by
    apply Asymptotics.IsBigO.of_bound C
    filter_upwards [eventually_lt_atBot (-T)] with x hx
    have hx' : x < 0 := hx.trans (neg_lt_zero.mpr hT)
    have hTx : T < |x| := by rw [abs_of_neg hx']; linarith
    simpa only [abs_of_neg hx', neg_mul_neg, Real.norm_of_nonneg (Real.exp_pos _).le]
      using (hbound x hTx).1.le
  exact mellin_differentiableAt_of_isBigO_rpow hloc
    (isBigO_comp_log_rpow_of_isBigO_exp htop Real.tendsto_log_atTop (eventually_gt_atTop 0))
    ((le_abs_self _).trans_lt hN)
    (isBigO_comp_log_rpow_of_isBigO_exp (by simpa only [neg_neg] using hbot)
      Real.tendsto_log_nhdsGT_zero self_mem_nhdsWithin)
    (neg_lt.mp ((neg_le_abs _).trans_lt hN))


/-- Paper: Lemma B.4.1.1, p. 607. The Mellin transform satisfies the bound
(B.4.1.3) of order one over the modulus, uniformly on each bounded-width strip. -/
theorem mellin_inverseNormBound_of_piecewiseSmoothMellinTest
    {f : ℝ → ℂ} (hf : IsPiecewiseSmoothMellinTest f) (a b : ℝ) :
    ∃ C > (0 : ℝ), ∃ R > (0 : ℝ), ∀ s : ℂ, s.re ∈ Icc a b → R < ‖s‖ →
      ‖logMellin f s‖ ≤ C / ‖s‖ := by
  classical
  obtain ⟨⟨S, hsmooth, hlimits⟩, hdecay⟩ := hf
  have hopen : IsOpen (S : Set ℝ)ᶜ := S.finite_toSet.isClosed.isOpen_compl
  have hcont := hsmooth.continuousOn
  have hcont' := hsmooth.continuousOn_deriv_of_isOpen hopen (by simp)
  have hlim₀ x (hx : x ∈ S) :
      (∃ l, Tendsto f (𝓝[<] x) (𝓝 l)) ∧ (∃ r, Tendsto f (𝓝[>] x) (𝓝 r)) := by
    simpa only [iteratedDeriv_zero] using hlimits 0 x hx
  have hlim₁ x (hx : x ∈ S) :
      (∃ l, Tendsto (deriv f) (𝓝[<] x) (𝓝 l)) ∧
        (∃ r, Tendsto (deriv f) (𝓝[>] x) (𝓝 r)) := by
    simpa only [iteratedDeriv_one] using hlimits 1 x hx
  let M := max |a| |b|
  have hM : 0 ≤ M := (abs_nonneg a).trans (le_max_left _ _)
  obtain ⟨N, hN⟩ := exists_nat_gt (M + 1)
  obtain ⟨C, hC, T, _, htail⟩ := hdecay N
  -- One-sided limits bound both profiles on the compact interval between the tails.
  have hcompact {g : ℝ → ℂ} (hg : ContinuousOn g (S : Set ℝ)ᶜ)
      (hlim : ∀ x ∈ S, (∃ l, Tendsto g (𝓝[<] x) (𝓝 l)) ∧
        (∃ r, Tendsto g (𝓝[>] x) (𝓝 r))) :
      ∃ B : ℝ, ∀ x ∈ Icc (-T) T, ‖g x‖ ≤ B := by
    have hloc (x : ℝ) : (𝓝 x).IsBoundedUnder (· ≤ ·) (fun y ↦ ‖g y‖) := by
      by_cases hx : x ∈ S
      · obtain ⟨⟨l, hl⟩, ⟨r, hr⟩⟩ := hlim x hx
        rw [← nhdsNE_sup_pure x, ← nhdsLT_sup_nhdsGT x, IsBoundedUnder, map_sup, map_sup]
        exact isBounded_sup (isBounded_sup hl.norm.isBoundedUnder_le hr.norm.isBoundedUnder_le)
          ⟨‖g x‖, by simp⟩
      · exact ((hg x hx).continuousAt (hopen.mem_nhds hx)).tendsto.norm.isBoundedUnder_le
    have hbounded : Bornology.IsBounded (g '' Icc (-T) T) := by
      apply Bornology.isBounded_image_of_isLocallyBounded_of_isCompact isCompact_Icc
      intro x
      obtain ⟨B, hB⟩ := hloc x
      exact ⟨{y | ‖g y‖ ≤ B}, eventually_map.mp hB,
        isBounded_iff_forall_norm_le.mpr ⟨B, forall_mem_image.mpr fun _ hy ↦ hy⟩⟩
    obtain ⟨B, hB⟩ := hbounded.exists_norm_le
    exact ⟨B, fun x hx ↦ hB _ (mem_image_of_mem g hx)⟩
  obtain ⟨U, hU⟩ := hcompact hcont hlim₀
  obtain ⟨V, hV⟩ := hcompact hcont' hlim₁
  let A := C + (|U| + |V|) * Real.exp ((M + 1) * T)
  have hCA : C ≤ A :=
    le_add_of_nonneg_right (mul_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))
      (Real.exp_pos _).le)
  have hA := hC.trans_le hCA
  have hdecay' (x y : ℝ) (hy₀ : x ∈ Icc (-T) T → y ≤ |U| + |V|)
      (hy₁ : T < |x| → y ≤ C * Real.exp (-(N : ℝ) * |x|)) :
      y ≤ A * Real.exp (-(M + 1) * |x|) := by
    by_cases hx : T < |x|
    · exact (hy₁ hx).trans (mul_le_mul hCA
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hN.le) (abs_nonneg x)))
        (Real.exp_pos _).le hA.le)
    · have hx' := le_of_not_gt hx
      -- Multiply by the reciprocal of the desired exponential factor.
      rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)]
      calc
        _ ≤ (|U| + |V|) * Real.exp ((M + 1) * T) :=
          mul_le_mul (hy₀ (abs_le.mp hx'))
            (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx' (by positivity)))
            (Real.exp_pos _).le (by positivity)
        _ ≤ A := le_add_of_nonneg_left hC.le
  -- This majorant absorbs every exponential weight in the strip.
  let B (x : ℝ) := A * Real.exp (-|x|)
  have hB : Integrable B := by
    apply Integrable.const_mul (f := fun x : ℝ ↦ Real.exp (-|x|)) _ A
    rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
    exact ⟨(integrableOn_exp_Iic 0).congr_fun
      (fun x hx ↦ by rw [abs_of_nonpos hx, neg_neg]) measurableSet_Iic,
      (integrableOn_exp_neg_Ioi 0).congr_fun
        (fun x hx ↦ by rw [abs_of_pos hx]) measurableSet_Ioi⟩
  let K : ℝ := (∫ x, B x) + (S.card : ℝ) * (A + A)
  have hK : 0 ≤ K := add_nonneg (integral_nonneg (fun _ ↦ by positivity)) (by positivity)
  refine ⟨K + 1, by positivity, 1, one_pos, fun s hs hsnorm ↦ ?_⟩
  apply (le_div_iff₀ (zero_lt_one.trans hsnorm)).mpr
  let w (x : ℝ) := Complex.exp (s * x)
  let F (x : ℝ) := w x * f x
  let G (x : ℝ) := w x * deriv f x
  have hw : Continuous w := by
    dsimp [w]
    fun_prop
  have hweight (x : ℝ) : ‖w x‖ ≤ Real.exp (M * |x|) := by
    have hsM : |s.re| ≤ M := abs_le.mpr
      ⟨(neg_le_neg (le_max_left |a| |b|)).trans ((neg_abs_le a).trans hs.1),
        hs.2.trans ((le_abs_self b).trans (le_max_right |a| |b|))⟩
    simp only [w, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    exact Real.exp_le_exp.mpr ((le_abs_self (s.re * x)).trans
      (by rw [abs_mul]; exact mul_le_mul_of_nonneg_right hsM (abs_nonneg x)))
  have hweighted (x : ℝ) {z : ℂ} (hz : ‖z‖ ≤ A * Real.exp (-(M + 1) * |x|)) :
      ‖w x * z‖ ≤ B x := by
    rw [norm_mul]
    calc
      _ ≤ Real.exp (M * |x|) * (A * Real.exp (-(M + 1) * |x|)) :=
        mul_le_mul (hweight x) hz (norm_nonneg _) (Real.exp_pos _).le
      _ = B x := by
        rw [mul_left_comm, ← Real.exp_add]
        congr 2
        ring
  have hFbound x : ‖F x‖ ≤ B x := hweighted x (hdecay' x _
    (fun hx ↦ (hU x hx).trans ((le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _))))
    (fun hx ↦ (htail x hx).1.le))
  have hGbound x : ‖G x‖ ≤ B x := hweighted x (hdecay' x _
    (fun hx ↦ (hV x hx).trans ((le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _))))
    (fun hx ↦ (htail x hx).2.le))
  have hint {g : ℝ → ℂ} (hg : ContinuousOn g (S : Set ℝ)ᶜ) (hbound : ∀ x, ‖g x‖ ≤ B x) :
      Integrable g :=
    hB.mono' (hg.measurable_of_countable_compl (by simpa using S.finite_toSet.countable)
      |>.aestronglyMeasurable) (Eventually.of_forall hbound)
  have hF : Integrable F := hint (hw.continuousOn.mul hcont) hFbound
  have hG : Integrable G := hint (hw.continuousOn.mul hcont') hGbound
  have hFtop : Tendsto F atTop (𝓝 0) := squeeze_zero_norm hFbound <| by
    apply (by simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul A :
      Tendsto (fun x : ℝ ↦ A * Real.exp (-x)) atTop (𝓝 0)).congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    simp [B, abs_of_nonneg hx]
  have hFbot : Tendsto F atBot (𝓝 0) := squeeze_zero_norm hFbound <| by
    apply (by simpa using Real.tendsto_exp_atBot.const_mul A :
      Tendsto (fun x : ℝ ↦ A * Real.exp x) atBot (𝓝 0)).congr'
    filter_upwards [eventually_le_atBot (0 : ℝ)] with x hx
    simp [B, abs_of_nonpos hx]
  let l (x : ℝ) := limUnder (𝓝[<] x) f
  let r (x : ℝ) := limUnder (𝓝[>] x) f
  have hl x (hx : x ∈ S) : Tendsto F (𝓝[<] x) (𝓝 (w x * l x)) := by
    obtain ⟨v, hv⟩ := (hlim₀ x hx).1
    simpa only [l, hv.limUnder_eq] using (hw.continuousAt.continuousWithinAt.tendsto.mul hv)
  have hr x (hx : x ∈ S) : Tendsto F (𝓝[>] x) (𝓝 (w x * r x)) := by
    obtain ⟨v, hv⟩ := (hlim₀ x hx).2
    simpa only [r, hv.limUnder_eq] using (hw.continuousAt.continuousWithinAt.tendsto.mul hv)
  have hderiv x (hx : x ∉ S) : HasDerivAt F (s * F x + G x) x := by
    have hw' : HasDerivAt w (w x * s) x := by
      simpa [w, mul_comm] using
        ((Complex.ofRealCLM.hasDerivAt (x := x)).const_mul s).cexp
    have hf' := ((hsmooth x hx).contDiffAt (hopen.mem_nhds hx)).differentiableAt
      (by simp : (∞ : ℕ∞ω) ≠ 0)
    refine (hw'.mul hf'.hasDerivAt).congr_deriv ?_
    simp only [F, G]
    ring
  have heq := integral_deriv_eq_sub_add_sum_jumps S ((hF.const_mul s).add hG)
    hderiv hl hr hFbot hFtop
  change (∫ x, s * F x + G x) = (0 : ℂ) - 0 + _ at heq
  rw [sub_self, zero_add, integral_add (hF.const_mul s) hG, integral_const_mul] at heq
  have htransform : logMellin f s = ∫ x, F x := by
    change mellin (fun t ↦ f (Real.log t)) s = _
    rw [mellin, ← integral_comp_exp]
    apply integral_congr_ae
    filter_upwards with x
    simp only [Real.log_exp, Complex.real_smul, smul_eq_mul]
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos x).ne'),
      ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp]
    simp only [F, w, Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  have hFle (x : ℝ) : ‖F x‖ ≤ A := (hFbound x).trans
    (mul_le_of_le_one_right hA.le (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg x))))
  have hjump : ‖∑ x ∈ S, (w x * l x - w x * r x)‖ ≤ (S.card : ℝ) * (A + A) := by
    calc
      _ ≤ ∑ x ∈ S, ‖w x * l x - w x * r x‖ := norm_sum_le _ _
      _ ≤ ∑ _x ∈ S, (A + A) := Finset.sum_le_sum fun x hx ↦
        (norm_sub_le _ _).trans (add_le_add
          (le_of_tendsto (hl x hx).norm (Eventually.of_forall hFle))
          (le_of_tendsto (hr x hx).norm (Eventually.of_forall hFle)))
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  rw [htransform, mul_comm, ← norm_mul, eq_sub_of_add_eq heq]
  exact ((norm_sub_le _ _).trans (add_le_add hjump
    (norm_integral_le_of_norm_le hB (Eventually.of_forall hGbound)))).trans (by
      dsimp [K]
      linarith)

end Sol_ExplicitFormula_mellin_entire_and_inv_bound_of_piecewise_smooth

open Sol_ExplicitFormula_mellin_entire_and_inv_bound_of_piecewise_smooth in
theorem solution
    (g : ℝ → ℂ) (S : Finset ℝ)
    (hsmooth : ContDiffOn ℝ ∞ g (S : Set ℝ)ᶜ)
    (hlim : ∀ (j : ℕ) (x : ℝ), x ∈ S →
      (∃ l : ℂ, Tendsto (iteratedDeriv j g) (𝓝[<] x) (𝓝 l)) ∧
      (∃ r : ℂ, Tendsto (iteratedDeriv j g) (𝓝[>] x) (𝓝 r)))
    (hdecay : ∀ N : ℕ, ∃ C > (0 : ℝ), ∃ T > (0 : ℝ), ∀ x : ℝ, T < |x| →
      ‖g x‖ < C * Real.exp (-(N : ℝ) * |x|) ∧ ‖deriv g x‖ < C * Real.exp (-(N : ℝ) * |x|)) :
    (∀ s : ℂ, MellinConvergent (fun t : ℝ => g (Real.log t)) s) ∧
    Differentiable ℂ (mellin (fun t : ℝ => g (Real.log t))) ∧
    ∀ a b : ℝ, ∃ C > (0 : ℝ), ∃ R > (0 : ℝ), ∀ s : ℂ, a ≤ s.re → s.re ≤ b → R < ‖s‖ →
      ‖mellin (fun t : ℝ => g (Real.log t)) s‖ ≤ C / ‖s‖ := by
  have hf : IsPiecewiseSmoothMellinTest g := ⟨⟨S, hsmooth, hlim⟩, hdecay⟩
  refine ⟨mellinConvergent_of_piecewiseSmoothMellinTest hf,
    differentiable_mellin_of_piecewiseSmoothMellinTest hf, fun a b => ?_⟩
  obtain ⟨C, hC, R, hR, hbound⟩ := mellin_inverseNormBound_of_piecewiseSmoothMellinTest hf a b
  exact ⟨C, hC, R, hR, fun s h1 h2 hs => hbound s ⟨h1, h2⟩ hs⟩
