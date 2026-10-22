-- Prove2me | solution 1 for CrowdContest.Pooling.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T00:19:47.04337+00:00
-- url     : https://prove2.me/submissions/9ca2a420-799b-449a-9d94-f91ef9bb312c

import Mathlib
import Definitions.Def_LogConcaveOn
import Definitions.Def_CrowdContest_Pooling_Density
import Definitions.Def_CrowdContest_Pooling_Setting

open MeasureTheory

open CrowdContest.Pooling



lemma CCP_L4_le_zero (ψ : ℝ → ℝ) (hψ : IsSymLogConcaveDensity ψ) (x : ℝ) : ψ x ≤ ψ 0 := by
  obtain ⟨⟨_, hnn, _⟩, hsym, ⟨_, hlc⟩⟩ := hψ
  have h := hlc x (Set.mem_univ _) (-x) (Set.mem_univ _) (1/2) (1/2) (by norm_num) (by norm_num)
    (by norm_num)
  rw [hsym x] at h
  have e : (1/2 : ℝ) • x + (1/2 : ℝ) • (-x) = 0 := by simp [smul_eq_mul]
  rw [e, ← Real.rpow_add' (hnn x) (by norm_num)] at h
  norm_num at h
  exact h

lemma CCP_L4_integrable (ψ : ℝ → ℝ) (hψ : IsSymLogConcaveDensity ψ) : Integrable ψ := by
  obtain ⟨⟨_, _, hint1⟩, _, _⟩ := hψ
  by_contra h
  rw [integral_undef h] at hint1
  norm_num at hint1

lemma CCP_L4_pos_zero (ψ : ℝ → ℝ) (hψ : IsSymLogConcaveDensity ψ) : 0 < ψ 0 := by
  have hnn := hψ.1.2.1
  rcases (hnn 0).lt_or_eq with h | h
  · exact h
  · exfalso
    have hz : ∀ x, ψ x = 0 := fun x => le_antisymm (h ▸ CCP_L4_le_zero ψ hψ x) (hnn x)
    have := hψ.1.2.2
    simp [hz] at this

lemma CCP_L4_tail (ψ : ℝ → ℝ) (hψ : IsSymLogConcaveDensity ψ) :
    ∃ b > 0, ∀ x, 0 ≤ x → ψ x ≤ 2 * ψ 0 * Real.exp (-b * x) := by
  have hnn := hψ.1.2.1
  have hint := CCP_L4_integrable ψ hψ
  have h0 := CCP_L4_pos_zero ψ hψ
  have hle := CCP_L4_le_zero ψ hψ
  -- find r > 0 with ψ r ≤ ψ 0 / 2
  obtain ⟨r, hr0, hr⟩ : ∃ r, 0 < r ∧ ψ r ≤ ψ 0 / 2 := by
    by_contra hcon
    push_neg at hcon
    set N := 4 / ψ 0 with hN
    have hNpos : 0 < N := by positivity
    have h1 : ∫ x in Set.Icc 0 N, ψ x ≤ ∫ x, ψ x :=
      setIntegral_le_integral hint (Filter.Eventually.of_forall hnn)
    have h2 : ∫ x in Set.Icc 0 N, (ψ 0 / 2) ≤ ∫ x in Set.Icc 0 N, ψ x := by
      apply setIntegral_mono_on (integrableOn_const (by simp)) hint.integrableOn measurableSet_Icc
      intro x hx
      rcases hx.1.lt_or_eq with hx0 | hx0
      · exact (hcon x hx0).le
      · rw [← hx0]; linarith
    rw [setIntegral_const, Real.volume_real_Icc_of_le hNpos.le, smul_eq_mul] at h2
    rw [hψ.1.2.2] at h1
    have : (N - 0) * (ψ 0 / 2) = 2 := by rw [hN]; field_simp; ring
    linarith
  refine ⟨Real.log 2 / r, by positivity, fun x hx => ?_⟩
  by_cases hxr : x < r
  · have : 1 / 2 ≤ Real.exp (-(Real.log 2 / r) * x) := by
      have e1 : Real.exp (-(Real.log 2 / r) * r) = 1 / 2 := by
        rw [show -(Real.log 2 / r) * r = -Real.log 2 by field_simp, Real.exp_neg,
          Real.exp_log (by norm_num)]
        norm_num
      rw [← e1]
      apply Real.exp_le_exp.2
      have : 0 < Real.log 2 / r := by positivity
      nlinarith
    nlinarith [hle x]
  push_neg at hxr
  have hxpos : 0 < x := lt_of_lt_of_le hr0 hxr
  rcases (hnn x).lt_or_eq with hpx | hpx
  swap
  · rw [← hpx]; positivity
  -- log-concavity at r = t x + (1-t) 0 with t = r / x
  set t := r / x with ht
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1 := by rw [ht, div_le_one hxpos]; exact hxr
  have hlc := hψ.2.2.2 x (Set.mem_univ _) 0 (Set.mem_univ _) t (1 - t) ht0.le (by linarith)
    (by ring)
  have e : t • x + (1 - t) • (0 : ℝ) = r := by
    simp [smul_eq_mul, ht]; field_simp
  rw [e] at hlc
  -- take logarithms
  have hA : 0 < ψ x ^ t := Real.rpow_pos_of_pos hpx t
  have hB : 0 < ψ 0 ^ (1 - t) := Real.rpow_pos_of_pos h0 _
  have hlog : t * Real.log (ψ x) + (1 - t) * Real.log (ψ 0) ≤ Real.log (ψ 0) - Real.log 2 := by
    have := Real.log_le_log (mul_pos hA hB) (hlc.trans hr)
    rw [Real.log_mul hA.ne' hB.ne', Real.log_rpow hpx, Real.log_rpow h0,
      Real.log_div h0.ne' (by norm_num)] at this
    exact this
  have hlog2 : Real.log (ψ x) ≤ Real.log (ψ 0) - Real.log 2 * x / r := by
    have h' : t * (Real.log (ψ x) - Real.log (ψ 0)) ≤ -Real.log 2 := by linarith
    have h'' : Real.log (ψ x) - Real.log (ψ 0) ≤ -Real.log 2 / t := by
      rw [le_div_iff₀ ht0]; linarith
    have : -Real.log 2 / t = - (Real.log 2 * x / r) := by rw [ht]; field_simp
    linarith
  have : ψ x ≤ ψ 0 * Real.exp (-(Real.log 2 / r) * x) := by
    rw [← Real.exp_log hpx, ← Real.exp_log h0, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have : -(Real.log 2 / r) * x = -(Real.log 2 * x / r) := by ring
    linarith
  have hex : 0 < Real.exp (-(Real.log 2 / r) * x) := Real.exp_pos _
  nlinarith

lemma CCP_L4_moment (ψ : ℝ → ℝ) (hψ : IsSymLogConcaveDensity ψ) :
    Integrable (fun x => x * ψ x) := by
  obtain ⟨b, hb, htail⟩ := CCP_L4_tail ψ hψ
  have hmeas := hψ.1.1
  have hnn := hψ.1.2.1
  have hsym := hψ.2.1
  -- k(x) = 1_{x>0} x e^{-bx}
  set k : ℝ → ℝ := (Set.Ioi (0 : ℝ)).indicator (fun x => x * Real.exp (-b * x)) with hk
  have hk_int : Integrable k := by
    rw [hk, integrable_indicator_iff measurableSet_Ioi]
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (b := b) (by norm_num)
      (by norm_num) hb
    refine this.congr_fun (fun x hx => ?_) measurableSet_Ioi
    simp [Real.rpow_one]
  have hbound_int : Integrable (fun x => 2 * ψ 0 * (k x + k (-x))) :=
    (hk_int.add hk_int.comp_neg).const_mul _
  refine hbound_int.mono' ((measurable_id.mul hmeas).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall (fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hnn x)]
  have h0 := CCP_L4_pos_zero ψ hψ
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have hkx : k x = 0 := by rw [hk]; exact Set.indicator_of_notMem (by simp; linarith) _
    have hkn : k (-x) = -x * Real.exp (-b * -x) := by
      rw [hk]; exact Set.indicator_of_mem (by simp; linarith) _
    rw [hkx, hkn, abs_of_neg hx, ← hsym x]
    have := htail (-x) (by linarith)
    have : 0 ≤ -x := by linarith
    nlinarith
  · subst hx; simp
    have : 0 ≤ k 0 := by rw [hk]; simp
    positivity
  · have hkx : k x = x * Real.exp (-b * x) := by
      rw [hk]; exact Set.indicator_of_mem (by simp; linarith) _
    have hkn : k (-x) = 0 := by rw [hk]; exact Set.indicator_of_notMem (by simp; linarith) _
    rw [hkx, hkn, abs_of_pos hx]
    have := htail x hx.le
    nlinarith




lemma CCP_L4_conv_eq (ψ : ℝ → ℝ) :
    convDensity ψ = convolution ψ ψ (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
  funext x
  rw [convolution_def]
  simp [convDensity, smul_eq_mul]

lemma CCP_L4_slice_int (ψ : ℝ → ℝ) (hψ : IsSymLogConcaveDensity ψ) (x : ℝ) :
    Integrable (fun t => ψ t * ψ (x - t)) := by
  have hint := CCP_L4_integrable ψ hψ
  refine hint.mul_bdd (c := ψ 0) ((hψ.1.1.comp (measurable_const.sub measurable_id)).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall (fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (hψ.1.2.1 _)]
  exact CCP_L4_le_zero ψ hψ _

lemma CCP_L4_conv_meas (ψ : ℝ → ℝ) (hψ : IsSymLogConcaveDensity ψ) :
    Measurable (convDensity ψ) := by
  have hmeas := hψ.1.1
  have hf : StronglyMeasurable (fun p : ℝ × ℝ => ψ p.2 * ψ (p.1 - p.2)) :=
    ((hmeas.comp measurable_snd).mul (hmeas.comp (measurable_fst.sub measurable_snd))).stronglyMeasurable
  exact (hf.integral_prod_right' (ν := volume)).measurable

lemma CCP_L4_conv_density (ψ : ℝ → ℝ) (hψ : IsSymLogConcaveDensity ψ) :
    IsDensity (convDensity ψ) := by
  refine ⟨CCP_L4_conv_meas ψ hψ, fun x => integral_nonneg (fun t => mul_nonneg (hψ.1.2.1 _) (hψ.1.2.1 _)), ?_⟩
  have hint := CCP_L4_integrable ψ hψ
  have := integral_convolution (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume) (ν := volume)
    hint hint
  rw [CCP_L4_conv_eq]
  convert this using 1
  simp [hψ.1.2.2]

lemma CCP_L4_conv_symm (ψ : ℝ → ℝ) (hψ : IsSymLogConcaveDensity ψ) (x : ℝ) :
    convDensity ψ (-x) = convDensity ψ x := by
  unfold convDensity
  rw [← integral_neg_eq_self (fun t => ψ t * ψ (-x - t)) volume]
  congr 1
  funext t
  rw [hψ.2.1 t]
  congr 1
  rw [← hψ.2.1 (x - t)]
  ring_nf

lemma CCP_L4_conv_moment (ψ : ℝ → ℝ) (hψ : IsSymLogConcaveDensity ψ) :
    Integrable (fun x => x * convDensity ψ x) := by
  have hint := CCP_L4_integrable ψ hψ
  have hmom := CCP_L4_moment ψ hψ
  have hmeas := hψ.1.1
  have hnn := hψ.1.2.1
  have hM := CCP_L4_le_zero ψ hψ
  set a : ℝ → ℝ := fun t => |t| * ψ t with ha
  have ha_int : Integrable a := by
    have := hmom.norm
    refine this.congr (Filter.Eventually.of_forall (fun t => ?_))
    simp [ha, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hnn t)]
  have hc1 := ha_int.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hint (μ := volume)
  have hc2 := hint.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) ha_int (μ := volume)
  refine (hc1.add hc2).mono' ((measurable_id.mul (CCP_L4_conv_meas ψ hψ)).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall (fun x => ?_)
  simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul, Pi.add_apply]
  -- pointwise integrability
  have i1 : Integrable (fun t => a t * ψ (x - t)) := by
    refine ha_int.mul_bdd (c := ψ 0) ((hmeas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall (fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn _)]; exact hM _
  have i2 : Integrable (fun t => ψ t * a (x - t)) := by
    refine (ha_int.comp_sub_left x).bdd_mul (c := ψ 0) hmeas.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn _)]; exact hM _
  rw [← integral_add i1 i2, Real.norm_eq_abs, abs_mul, convDensity,
    abs_of_nonneg (integral_nonneg (fun t => mul_nonneg (hnn _) (hnn _))), ← integral_const_mul]
  apply integral_mono ((CCP_L4_slice_int ψ hψ x).const_mul _) (i1.add i2)
  intro t
  simp only [ha, Pi.add_apply]
  have h1 : |x| ≤ |t| + |x - t| := by
    calc |x| = |t + (x - t)| := by ring_nf
      _ ≤ |t| + |x - t| := abs_add_le _ _
  have p1 := hnn t
  have p2 := hnn (x - t)
  have : 0 ≤ ψ t * ψ (x - t) := mul_nonneg p1 p2
  nlinarith




lemma CCP_L4_struct (φ : ℝ → ℝ) (hφ : IsDensity φ) :
    (∀ u ∈ Set.Ioo (0 : ℝ) 1, cdf φ (quantile (cdf φ) u) = u) ∧ Continuous (cdf φ) ∧
    AEMeasurable (quantile (cdf φ)) (volume.restrict (Set.Ioo (0 : ℝ) 1)) ∧
    (volume.restrict (Set.Ioo (0 : ℝ) 1)).map (quantile (cdf φ)) =
      volume.withDensity (fun x => (((φ x).toNNReal : NNReal) : ENNReal)) := by
  obtain ⟨hmeas, hnn, hint1⟩ := hφ
  have hint : Integrable φ := by
    by_contra h
    rw [integral_undef h] at hint1
    norm_num at hint1
  set F := cdf φ with hFdef
  let f : ℝ → NNReal := fun x => (φ x).toNNReal
  let μ : Measure ℝ := volume.withDensity (fun x => (f x : ENNReal))
  have hF0 : ∀ x, 0 ≤ F x := fun x => setIntegral_nonneg measurableSet_Iic (fun t _ => hnn t)
  have hμset : ∀ s, MeasurableSet s → μ s = ENNReal.ofReal (∫ t in s, φ t) := by
    intro s hs
    rw [withDensity_apply _ hs, ofReal_integral_eq_lintegral_ofReal hint.integrableOn
      (Filter.Eventually.of_forall (fun t => hnn t))]
    rfl
  have hμIic : ∀ x, μ (Set.Iic x) = ENNReal.ofReal (F x) := fun x => hμset _ measurableSet_Iic
  have hμuniv : μ Set.univ = 1 := by
    rw [hμset _ MeasurableSet.univ, Measure.restrict_univ, hint1, ENNReal.ofReal_one]
  have : IsProbabilityMeasure μ := ⟨hμuniv⟩
  have hFcdf : F = ProbabilityTheory.cdf μ := by
    funext x
    have h := ProbabilityTheory.ofReal_cdf μ x
    rw [hμIic] at h
    exact ((ENNReal.ofReal_eq_ofReal_iff (ProbabilityTheory.cdf_nonneg μ x) (hF0 x)).1 h).symm
  have hmono : Monotone F := hFcdf ▸ ProbabilityTheory.monotone_cdf μ
  have hbot : Filter.Tendsto F Filter.atBot (nhds 0) := hFcdf ▸ ProbabilityTheory.tendsto_cdf_atBot μ
  have htop : Filter.Tendsto F Filter.atTop (nhds 1) := hFcdf ▸ ProbabilityTheory.tendsto_cdf_atTop μ
  have hcont : Continuous F := by
    have h1 : ∀ x, F x = F 0 + ∫ t in (0 : ℝ)..x, φ t := by
      intro x
      have := intervalIntegral.integral_Iic_sub_Iic (μ := volume) (f := φ) (a := 0) (b := x)
        hint.integrableOn hint.integrableOn
      simp only [hFdef, cdf] at this ⊢
      linarith
    have h2 : Continuous fun x => ∫ t in (0 : ℝ)..x, φ t :=
      intervalIntegral.continuous_primitive (fun a b => hint.intervalIntegrable) 0
    have : F = fun x => F 0 + ∫ t in (0 : ℝ)..x, φ t := funext h1
    rw [this]
    exact continuous_const.add h2
  set Q := quantile F with hQdef
  have hQ : ∀ u ∈ Set.Ioo (0 : ℝ) 1, (∀ x, Q u ≤ x ↔ u ≤ F x) ∧ F (Q u) = u := by
    intro u hu
    obtain ⟨hu0, hu1⟩ := hu
    have hne : ({x | u ≤ F x} : Set ℝ).Nonempty := by
      obtain ⟨x, hx⟩ := ((tendsto_order.1 htop).1 u hu1).exists
      exact ⟨x, hx.le⟩
    obtain ⟨y, hy⟩ := Filter.eventually_atBot.1 ((tendsto_order.1 hbot).2 u hu0)
    have hbdd : BddBelow ({x | u ≤ F x} : Set ℝ) := by
      refine ⟨y, fun x hx => ?_⟩
      by_contra hxy
      push_neg at hxy
      have := hy x hxy.le
      simp only [Set.mem_setOf_eq] at hx
      linarith
    have hclosed : IsClosed ({x | u ≤ F x} : Set ℝ) := isClosed_le continuous_const hcont
    have hmem : u ≤ F (Q u) := hclosed.csInf_mem hne hbdd
    have hiff : ∀ x, Q u ≤ x ↔ u ≤ F x := by
      intro x
      constructor
      · intro hx; exact le_trans hmem (hmono hx)
      · intro hx; exact csInf_le hbdd hx
    refine ⟨hiff, le_antisymm ?_ hmem⟩
    have hyQ : y ≤ Q u := by
      by_contra h
      push_neg at h
      have := hy (Q u) h.le
      linarith
    have hIVT := intermediate_value_Icc hyQ hcont.continuousOn
    have hyu : u ∈ Set.Icc (F y) (F (Q u)) := ⟨(hy y le_rfl).le, hmem⟩
    obtain ⟨z, hz, hFz⟩ := hIVT hyu
    have hQz : Q u ≤ z := (hiff z).2 hFz.ge
    have : z = Q u := le_antisymm hz.2 hQz
    rw [← this, hFz]
  have hQmono : MonotoneOn Q (Set.Ioo (0 : ℝ) 1) := by
    intro u hu v hv huv
    rw [(hQ u hu).1]
    rw [(hQ v hv).2]
    exact huv
  have hQae : AEMeasurable Q (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
    aemeasurable_restrict_of_monotoneOn measurableSet_Ioo hQmono
  set ν : Measure ℝ := (volume.restrict (Set.Ioo (0 : ℝ) 1)).map Q with hν
  have hνIic : ∀ x, μ (Set.Iic x) = ν (Set.Iic x) := by
    intro x
    rw [hμIic, hν, Measure.map_apply_of_aemeasurable hQae measurableSet_Iic,
      Measure.restrict_apply' measurableSet_Ioo]
    have hset : Q ⁻¹' Set.Iic x ∩ Set.Ioo 0 1 = Set.Ioo 0 1 ∩ Set.Iic (F x) := by
      ext u
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h2, ((hQ u h2).1 x).1 h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨((hQ u h1).1 x).2 h2, h1⟩
    rw [hset]
    have hF1 : F x ≤ 1 := hFcdf ▸ ProbabilityTheory.cdf_le_one μ x
    rcases hF1.lt_or_eq with hlt | heq
    · have : Set.Ioo (0 : ℝ) 1 ∩ Set.Iic (F x) = Set.Ioc 0 (F x) := by
        ext u
        simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Iic, Set.mem_Ioc]
        constructor
        · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
        · rintro ⟨h1, h3⟩; exact ⟨⟨h1, by linarith⟩, h3⟩
      rw [this, Real.volume_Ioc, sub_zero]
    · have : Set.Ioo (0 : ℝ) 1 ∩ Set.Iic (F x) = Set.Ioo 0 1 := by
        rw [heq]
        exact Set.inter_eq_left.2 (fun u hu => le_of_lt hu.2)
      rw [this, Real.volume_Ioo, heq, sub_zero]
  have hμν : μ = ν := Measure.ext_of_Iic μ ν hνIic
  exact ⟨fun u hu => (hQ u hu).2, hcont, hQae, hμν.symm⟩

lemma CCP_L4_transfer (φ : ℝ → ℝ) (hφ : IsDensity φ) (g : ℝ → ℝ) (hg : Continuous g) :
    (∫ x, φ x * g x = ∫ u in Set.Ioo (0 : ℝ) 1, g (quantile (cdf φ) u)) ∧
    (Integrable (fun x => φ x * g x) →
      IntegrableOn (fun u => g (quantile (cdf φ) u)) (Set.Ioo (0 : ℝ) 1)) := by
  obtain ⟨_, _, hQae, hmap⟩ := CCP_L4_struct φ hφ
  have hf : Measurable (fun x => (φ x).toNNReal) := hφ.1.real_toNNReal
  have hsm : ∀ x, φ x * g x = (φ x).toNNReal • g x := by
    intro x
    rw [NNReal.smul_def, Real.coe_toNNReal _ (hφ.2.1 x), smul_eq_mul]
  constructor
  · have h1 : ∫ x, φ x * g x = ∫ x, g x ∂(volume.withDensity
        (fun x => (((φ x).toNNReal : NNReal) : ENNReal))) := by
      rw [integral_withDensity_eq_integral_smul hf]
      simp_rw [hsm]
    rw [h1, ← hmap, integral_map hQae hg.aestronglyMeasurable]
  · intro hi
    have h1 : Integrable g (volume.withDensity (fun x => (((φ x).toNNReal : NNReal) : ENNReal))) := by
      rw [integrable_withDensity_iff_integrable_smul hf]
      simp_rw [← hsm]
      exact hi
    rw [← hmap, integrable_map_measure hg.aestronglyMeasurable hQae] at h1
    exact h1




/-- Quantile facts for a symmetric density with a finite first moment. -/
lemma CCP_L4_quant (φ : ℝ → ℝ) (hφ : IsDensity φ) (hsym : ∀ x, φ (-x) = φ x)
    (hmom : Integrable (fun x => x * φ x)) (n : ℕ) :
    expMax φ n = ∫ u in Set.Ioo (0 : ℝ) 1, quantile (cdf φ) u * ((n : ℝ) * u ^ (n - 1)) ∧
    IntegrableOn (quantile (cdf φ)) (Set.Ioo (0 : ℝ) 1) ∧
    ∫ u in Set.Ioo (0 : ℝ) 1, quantile (cdf φ) u = 0 := by
  obtain ⟨hFQ, hcont, _, _⟩ := CCP_L4_struct φ hφ
  have T1 := CCP_L4_transfer φ hφ (fun x => x * ((n : ℝ) * cdf φ x ^ (n - 1)))
    (continuous_id.mul (continuous_const.mul (hcont.pow _)))
  have T2 := CCP_L4_transfer φ hφ (fun x => x) continuous_id
  refine ⟨?_, ?_, ?_⟩
  · have : expMax φ n = ∫ x, φ x * (x * ((n : ℝ) * cdf φ x ^ (n - 1))) := by
      unfold expMax; congr 1; funext x; ring
    rw [this, T1.1]
    refine setIntegral_congr_fun measurableSet_Ioo (fun u hu => ?_)
    simp only [hFQ u hu]
  · apply T2.2
    refine hmom.congr (Filter.Eventually.of_forall (fun x => ?_))
    simp only; ring
  · rw [← T2.1]
    have h := integral_neg_eq_self (fun x => φ x * x) volume
    simp only [hsym, mul_neg, integral_neg] at h
    linarith

lemma CCP_L4_intmul (f : ℝ → ℝ) (hf : IntegrableOn f (Set.Ioo (0 : ℝ) 1)) (c : ℝ → ℝ)
    (hc : Continuous c) : IntegrableOn (fun u => f u * c u) (Set.Ioo (0 : ℝ) 1) := by
  have h1 : IntegrableOn f (Set.Icc (0 : ℝ) 1) :=
    (integrableOn_Icc_iff_integrableOn_Ioo (f := f) (μ := volume) (a := 0) (b := 1)).2 hf
  exact (h1.mul_continuousOn hc.continuousOn isCompact_Icc).mono_set Set.Ioo_subset_Icc_self

lemma CCP_L4_pos (f : ℝ → ℝ) (hf : IntegrableOn f (Set.Ioo (0 : ℝ) 1)) (a b : ℝ) (hab : a < b)
    (hsub : Set.Ioo a b ⊆ Set.Ioo 0 1) (hnn : ∀ u ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ f u)
    (hpos : ∀ u ∈ Set.Ioo a b, 0 < f u) : 0 < ∫ u in Set.Ioo (0 : ℝ) 1, f u := by
  rw [setIntegral_pos_iff_support_of_nonneg_ae (ae_restrict_of_forall_mem measurableSet_Ioo hnn) hf]
  have : Set.Ioo a b ⊆ Function.support f ∩ Set.Ioo 0 1 :=
    fun u hu => ⟨(hpos u hu).ne', hsub hu⟩
  refine lt_of_lt_of_le ?_ (measure_mono this)
  rw [Real.volume_Ioo]
  exact ENNReal.ofReal_pos.2 (by linarith)

theorem solution (n : ℕ) (hn : 2 ≤ n) (ψ : ℝ → ℝ) (hψ : IsSymLogConcaveDensity ψ)
    (hR : AssumptionR ψ) :
    expMax (convDensity ψ) n < expMax ψ n + expMax ψ n := by
  obtain ⟨E1, IQ, ZQ⟩ := CCP_L4_quant ψ hψ.1 hψ.2.1 (CCP_L4_moment ψ hψ) n
  obtain ⟨E2, IP, ZP⟩ := CCP_L4_quant (convDensity ψ) (CCP_L4_conv_density ψ hψ)
    (CCP_L4_conv_symm ψ hψ) (CCP_L4_conv_moment ψ hψ) n
  obtain ⟨u₀, hneg, hposR⟩ := hR
  set Q := quantile (cdf ψ)
  set P := quantile (cdf (convDensity ψ))
  set G : ℝ → ℝ := fun u => 2 * Q u - P u with hG
  have IG : IntegrableOn G (Set.Ioo (0 : ℝ) 1) := (IQ.const_mul 2).sub IP
  have ZG : ∫ u in Set.Ioo (0 : ℝ) 1, G u = 0 := by
    rw [hG, integral_sub (IQ.const_mul 2) IP, integral_const_mul, ZQ, ZP]; ring
  -- u₀ ∈ (0,1)
  have hu0 : 0 < u₀ := by
    by_contra h
    push_neg at h
    have : 0 < ∫ u in Set.Ioo (0 : ℝ) 1, G u :=
      CCP_L4_pos G IG 0 1 one_pos subset_rfl
        (fun u hu => (hposR u ⟨by linarith [hu.1], hu.2⟩).le)
        (fun u hu => hposR u ⟨by linarith [hu.1], hu.2⟩)
    linarith
  have hu1 : u₀ < 1 := by
    by_contra h
    push_neg at h
    have : 0 < ∫ u in Set.Ioo (0 : ℝ) 1, -G u :=
      CCP_L4_pos (fun u => -G u) IG.neg 0 1 one_pos subset_rfl
        (fun u hu => by have := hneg u ⟨hu.1, by linarith [hu.2]⟩; simp only [hG]; linarith)
        (fun u hu => by have := hneg u ⟨hu.1, by linarith [hu.2]⟩; simp only [hG]; linarith)
    rw [integral_neg] at this
    linarith
  -- the weights
  set w : ℝ → ℝ := fun u => (n : ℝ) * u ^ (n - 1) with hw
  have hwc : Continuous w := continuous_const.mul (continuous_pow _)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hwmono : ∀ a b : ℝ, 0 ≤ a → a < b → w a < w b := by
    intro a b ha hab
    simp only [hw]
    have := pow_lt_pow_left₀ hab ha (show n - 1 ≠ 0 by omega)
    exact mul_lt_mul_of_pos_left this hnpos
  set H : ℝ → ℝ := fun u => G u * (w u - w u₀) with hH
  have IH : IntegrableOn H (Set.Ioo (0 : ℝ) 1) :=
    CCP_L4_intmul G IG (fun u => w u - w u₀) (hwc.sub continuous_const)
  have IQw := CCP_L4_intmul Q IQ w hwc
  have IPw := CCP_L4_intmul P IP w hwc
  have hHint : ∫ u in Set.Ioo (0 : ℝ) 1, H u = expMax ψ n + expMax ψ n - expMax (convDensity ψ) n := by
    have e1 : ∀ u, H u = 2 * (Q u * w u) - P u * w u - w u₀ * G u := by
      intro u; simp only [hH, hG]; ring
    simp_rw [e1]
    have a1 := integral_sub (μ := volume.restrict (Set.Ioo (0 : ℝ) 1))
      (f := fun u => 2 * (Q u * w u) - P u * w u) (g := fun u => w u₀ * G u)
      ((IQw.const_mul 2).sub IPw) (IG.const_mul _)
    have a2 := integral_sub (μ := volume.restrict (Set.Ioo (0 : ℝ) 1))
      (f := fun u => 2 * (Q u * w u)) (g := fun u => P u * w u) (IQw.const_mul 2) IPw
    have a3 := integral_const_mul (μ := volume.restrict (Set.Ioo (0 : ℝ) 1)) (2 : ℝ)
      (fun u => Q u * w u)
    have a4 := integral_const_mul (μ := volume.restrict (Set.Ioo (0 : ℝ) 1)) (w u₀) G
    rw [a1, a2, a3, a4, ZG, E1, E2]
    ring
  have hpos : 0 < ∫ u in Set.Ioo (0 : ℝ) 1, H u := by
    refine CCP_L4_pos H IH u₀ 1 hu1 (Set.Ioo_subset_Ioo_left hu0.le) ?_ ?_
    · intro u hu
      rcases lt_trichotomy u u₀ with h | h | h
      · have g1 := hneg u ⟨hu.1, h⟩
        have g2 := hwmono u u₀ hu.1.le h
        simp only [hH]
        nlinarith
      · simp [hH, h]
      · have g1 := hposR u ⟨h, hu.2⟩
        have g2 := hwmono u₀ u hu0.le h
        simp only [hH]
        nlinarith
    · intro u hu
      have g1 := hposR u hu
      have g2 := hwmono u₀ u hu0.le hu.1
      simp only [hH]
      exact mul_pos g1 (by linarith)
  linarith

