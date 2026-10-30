-- Prove2me | solution 1 for FragileBandit.CauchyTail.dinf_eq_dP
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T13:00:06.164806+00:00
-- url     : https://prove2.me/submissions/a57765b8-fbc3-4e65-abc4-136829c0606a

import Mathlib
import Definitions.Def_FragileBandit_CauchyTail_Setting

open MeasureTheory ProbabilityTheory Filter BanditAlgorithm FragileBandit.CauchyTail
open scoped ENNReal Topology

namespace CTExpFam

variable {P : Measure ℝ} [IsProbabilityMeasure P]

/-- The normalizer `Z(s) = ∫ e^{s x} dP`. -/
noncomputable def Z (P : Measure ℝ) (s : ℝ) : ℝ := ∫ x, Real.exp (s * x) ∂P

/-- The tilted mean. -/
noncomputable def mn (P : Measure ℝ) (s : ℝ) : ℝ := ∫ x, x ∂(tilt P s)

instance tilt_isFinite (s : ℝ) : IsFiniteMeasure (tilt P s) := by
  unfold tilt; infer_instance

lemma Z_pos {s : ℝ} (hs : s ∈ natParamSet P) : 0 < Z P s := integral_exp_pos hs

lemma tilt_isProb {s : ℝ} (hs : s ∈ natParamSet P) : IsProbabilityMeasure (tilt P s) :=
  isProbabilityMeasure_tilted hs

lemma tilt_ac (s : ℝ) : tilt P s ≪ P := tilted_absolutelyContinuous _ _

lemma ac_tilt {s : ℝ} (hs : s ∈ natParamSet P) : P ≪ tilt P s := absolutelyContinuous_tilted hs

lemma llr_tilt {s s' : ℝ} (hs : s ∈ natParamSet P) (hs' : s' ∈ natParamSet P) :
    llr (tilt P s) (tilt P s') =ᵐ[P]
      fun x => (s - s') * x - Real.log (Z P s) + Real.log (Z P s') := by
  have h1 := llr_tilted_left (μ := P) (ν := tilt P s') (f := fun x => s * x) (ac_tilt hs') hs
    (measurable_const.mul measurable_id).aemeasurable
  have h2 := llr_tilted_right (μ := P) (ν := P) (f := fun x => s' * x)
    Measure.AbsolutelyContinuous.rfl hs'
  have h3 := llr_self P
  unfold tilt at h1 ⊢
  filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
  rw [hx1, hx2, hx3]
  simp only [Z, Pi.zero_apply]
  ring

lemma tilt_ac_tilt {s s' : ℝ} (hs' : s' ∈ natParamSet P) : tilt P s ≪ tilt P s' :=
  (tilt_ac s).trans (ac_tilt hs')

lemma integrable_llr_tilt {s s' : ℝ} (hs : s ∈ natParamSet P) (hs' : s' ∈ natParamSet P)
    (hint : Integrable id (tilt P s)) : Integrable (llr (tilt P s) (tilt P s')) (tilt P s) := by
  have := tilt_isProb hs
  have hae : llr (tilt P s) (tilt P s') =ᵐ[tilt P s]
      fun x => (s - s') * x - Real.log (Z P s) + Real.log (Z P s') :=
    (tilt_ac s).ae_le (llr_tilt hs hs')
  refine Integrable.congr ?_ hae.symm
  exact ((hint.const_mul (s - s')).sub (integrable_const _)).add (integrable_const _)

lemma integral_llr_tilt {s s' : ℝ} (hs : s ∈ natParamSet P) (hs' : s' ∈ natParamSet P)
    (hint : Integrable id (tilt P s)) :
    ∫ x, llr (tilt P s) (tilt P s') x ∂(tilt P s) =
      (s - s') * mn P s - Real.log (Z P s) + Real.log (Z P s') := by
  have := tilt_isProb hs
  have hae : llr (tilt P s) (tilt P s') =ᵐ[tilt P s]
      fun x => (s - s') * x - Real.log (Z P s) + Real.log (Z P s') :=
    (tilt_ac s).ae_le (llr_tilt hs hs')
  rw [integral_congr_ae hae]
  rw [integral_add, integral_sub, integral_const_mul, integral_const, integral_const]
  · simp [mn]
  · exact hint.const_mul _
  · exact integrable_const _
  · exact (hint.const_mul _).sub (integrable_const _)
  · exact integrable_const _

/-- The real KL divergence between tilts is nonnegative. -/
lemma kl_real_nonneg {s s' : ℝ} (hs : s ∈ natParamSet P) (hs' : s' ∈ natParamSet P)
    (hint : Integrable id (tilt P s)) :
    0 ≤ (s - s') * mn P s - Real.log (Z P s) + Real.log (Z P s') := by
  have := tilt_isProb hs
  have := tilt_isProb hs'
  have := InformationTheory.integral_llr_add_sub_measure_univ_nonneg (tilt_ac_tilt (s := s) hs')
    (integrable_llr_tilt hs hs' hint)
  rw [integral_llr_tilt hs hs' hint] at this
  simpa using this

lemma kl_tilt {s s' : ℝ} (hs : s ∈ natParamSet P) (hs' : s' ∈ natParamSet P)
    (hint : Integrable id (tilt P s)) :
    InformationTheory.klDiv (tilt P s) (tilt P s') =
      ENNReal.ofReal ((s - s') * mn P s - Real.log (Z P s) + Real.log (Z P s')) := by
  have := tilt_isProb hs
  have := tilt_isProb hs'
  rw [InformationTheory.klDiv_of_ac_of_integrable (tilt_ac_tilt hs')
    (integrable_llr_tilt hs hs' hint), integral_llr_tilt hs hs' hint]
  simp

lemma mn_mono {s s' : ℝ} (hs : s ∈ natParamSet P) (hs' : s' ∈ natParamSet P)
    (hint : Integrable id (tilt P s)) (hint' : Integrable id (tilt P s')) (hss : s ≤ s') :
    mn P s ≤ mn P s' := by
  have h1 := kl_real_nonneg hs hs' hint
  have h2 := kl_real_nonneg hs' hs hint'
  rcases eq_or_lt_of_le hss with h | h
  · rw [h]
  · have : 0 ≤ (s' - s) * (mn P s' - mn P s) := by nlinarith
    have hpos : 0 < s' - s := by linarith
    nlinarith

lemma tilt_eq_of_mn_eq {s s' : ℝ} (hs : s ∈ natParamSet P) (hs' : s' ∈ natParamSet P)
    (hint : Integrable id (tilt P s)) (hint' : Integrable id (tilt P s'))
    (heq : mn P s = mn P s') : tilt P s = tilt P s' := by
  have := tilt_isProb hs
  have := tilt_isProb hs'
  have h1 := kl_real_nonneg hs hs' hint
  have h2 := kl_real_nonneg hs' hs hint'
  have h0 : (s - s') * mn P s - Real.log (Z P s) + Real.log (Z P s') = 0 := by
    rw [heq] at h1 ⊢; nlinarith
  have hkl := kl_tilt hs hs' hint
  rw [h0, ENNReal.ofReal_zero] at hkl
  exact InformationTheory.klDiv_eq_zero_iff.1 hkl


lemma mn_const_of_tilt_eq {s s' : ℝ} (hs : s ∈ natParamSet P) (hs' : s' ∈ natParamSet P)
    (hss : s ≠ s') (heq : tilt P s = tilt P s') :
    ∀ u ∈ natParamSet P, mn P u = mn P s := by
  have h1 := rnDeriv_tilted_left_self (μ := P) (f := fun x => s * x)
    (measurable_const.mul measurable_id).aemeasurable
  have h2 := rnDeriv_tilted_left_self (μ := P) (f := fun x => s' * x)
    (measurable_const.mul measurable_id).aemeasurable
  have heq' : P.tilted (fun x => s * x) = P.tilted (fun x => s' * x) := heq
  rw [heq'] at h1
  have hZs := Z_pos hs
  have hZs' := Z_pos hs'
  set c : ℝ := Real.log (Z P s' / Z P s) / (s' - s) with hc
  have hsub : s' - s ≠ 0 := sub_ne_zero.2 (Ne.symm hss)
  have hx : ∀ᵐ x ∂P, x = c := by
    filter_upwards [h1, h2] with x hx1 hx2
    rw [hx2] at hx1
    have hr := (ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)).1 hx1
    change Real.exp (s' * x) / Z P s' = Real.exp (s * x) / Z P s at hr
    -- exp(s' x)/Z s' = exp(s x)/Z s
    have hr' : Real.exp ((s' - s) * x) = Z P s' / Z P s := by
      rw [div_eq_div_iff hZs'.ne' hZs.ne'] at hr
      rw [eq_div_iff hZs.ne', sub_mul, Real.exp_sub]
      field_simp
      simpa [mul_comm] using hr
    have := congrArg Real.log hr'
    rw [Real.log_exp] at this
    rw [hc, ← this]
    field_simp
  have hmn : ∀ u ∈ natParamSet P, mn P u = c := by
    intro u hu
    have hZu : Z P u = Real.exp (u * c) := by
      unfold Z
      have hae : (fun x => Real.exp (u * x)) =ᵐ[P] fun _ => Real.exp (u * c) :=
        hx.mono (fun x hx => by rw [hx])
      rw [integral_congr_ae hae]
      simp
    unfold mn tilt
    rw [integral_tilted]
    have hae : (fun x => (Real.exp (u * x) / ∫ x, Real.exp (u * x) ∂P) • x) =ᵐ[P]
        fun _ => (Real.exp (u * c) / Z P u) • c := by
      filter_upwards [hx] with x hx
      rw [hx]; rfl
    rw [integral_congr_ae hae, hZu]
    simp only [integral_const, probReal_univ, one_smul, smul_eq_mul]
    field_simp
  intro u hu
  rw [hmn u hu, hmn s hs]

lemma natParamSet_eq (P : Measure ℝ) : natParamSet P = integrableExpSet id P := by
  ext t; rfl

lemma integrable_id_of_interior {s : ℝ} (hs : s ∈ interior (natParamSet P)) :
    Integrable id (tilt P s) := by
  have hs' : s ∈ natParamSet P := interior_subset hs
  unfold tilt
  rw [integrable_tilted_iff hs']
  rw [natParamSet_eq] at hs
  have := integrable_pow_mul_exp_of_mem_interior_integrableExpSet (X := id) (μ := P) hs 1
  refine this.congr (Eventually.of_forall (fun x => ?_))
  simp [mul_comm]

lemma continuousAt_logZ {s : ℝ} (hs : s ∈ interior (natParamSet P)) :
    ContinuousAt (fun u => Real.log (Z P u)) s := by
  have hZ : (fun u => Z P u) = mgf id P := by
    funext u; rfl
  have hc : ContinuousAt (fun u => Z P u) s := by
    rw [hZ]
    rw [natParamSet_eq] at hs
    exact continuousOn_mgf.continuousAt (isOpen_interior.mem_nhds hs)
  exact hc.log (Z_pos (interior_subset hs)).ne'

lemma theta_spec {z : ℝ} (hz : z ∈ meanSet P) :
    thetaOf P z ∈ natParamSet P ∧ Integrable id (tilt P (thetaOf P z)) ∧
      mn P (thetaOf P z) = z := by
  have hz' : ∃ θ ∈ natParamSet P, Integrable id (tilt P θ) ∧ ∫ x, x ∂(tilt P θ) = z := hz
  unfold thetaOf
  rw [dif_pos hz']
  exact ⟨hz'.choose_spec.1, hz'.choose_spec.2.1, hz'.choose_spec.2.2⟩

end CTExpFam

open CTExpFam in
theorem solution (P : Measure ℝ) [IsProbabilityMeasure P]
    (hP : (0 : ℝ) ∈ interior (natParamSet P)) (μ μ' : ℝ)
    (hμ : μ ∈ meanSet P) (hμ' : μ' ∈ meanSet P) (hlt : μ < μ')
    (habove : ∃ z ∈ meanSet P, μ' < z) :
    banditDInf (model P) (expFam P μ) μ' = dP P μ μ' := by
  obtain ⟨z1, hz1, hz1lt⟩ := habove
  obtain ⟨hs0, hint0, hm0⟩ := theta_spec hμ
  obtain ⟨hs1, hint1, hm1⟩ := theta_spec hμ'
  obtain ⟨hs2, hint2, hm2⟩ := theta_spec hz1
  set s0 := thetaOf P μ with hs0def
  set s1 := thetaOf P μ' with hs1def
  set s2 := thetaOf P z1 with hs2def
  have hs01 : s0 < s1 := by
    by_contra h; push_neg at h
    have := mn_mono hs1 hs0 hint1 hint0 h; linarith
  have hs12 : s1 < s2 := by
    by_contra h; push_neg at h
    have := mn_mono hs2 hs1 hint2 hint1 h; linarith
  have hconv : Convex ℝ (natParamSet P) := by
    rw [natParamSet_eq]; exact convex_integrableExpSet
  have hIoo : Set.Ioo s0 s2 ⊆ interior (natParamSet P) := by
    apply interior_maximal _ isOpen_Ioo
    intro u hu
    exact hconv.ordConnected.out hs0 hs2 ⟨hu.1.le, hu.2.le⟩
  have hs1int : s1 ∈ interior (natParamSet P) := hIoo ⟨hs01, hs12⟩
  set F : ℝ → ℝ := fun u => (s0 - u) * μ - Real.log (Z P s0) + Real.log (Z P u) with hF
  have hKL : ∀ u, u ∈ natParamSet P →
      InformationTheory.klDiv (tilt P s0) (tilt P u) = ENNReal.ofReal (F u) := by
    intro u hu
    rw [kl_tilt hs0 hu hint0, hm0]
  have hdP : dP P μ μ' = ENNReal.ofReal (F s1) := hKL s1 hs1
  -- strictness: equal means at different parameters would force all means equal
  have hstrict : ∀ u, s1 < u → u ∈ natParamSet P → Integrable id (tilt P u) → μ' < mn P u := by
    intro u hu humem huint
    rcases lt_or_eq_of_le (show μ' ≤ mn P u from hm1 ▸ mn_mono hs1 humem hint1 huint hu.le)
      with h | h
    · exact h
    · exfalso
      have heq := tilt_eq_of_mn_eq hs1 humem hint1 huint (by rw [hm1, h])
      have := mn_const_of_tilt_eq hs1 humem hu.ne heq s0 hs0
      rw [hm0, hm1] at this
      linarith
  rw [hdP]
  apply le_antisymm
  · -- upper bound: approach `µ'` from above
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    have hFc : ContinuousAt F s1 := by
      have h1 : ContinuousAt (fun u : ℝ => (s0 - u) * μ - Real.log (Z P s0)) s1 := by fun_prop
      exact h1.add (continuousAt_logZ hs1int)
    obtain ⟨δ, hδ, hδF⟩ := Metric.continuousAt_iff.1 hFc ε (by exact_mod_cast hε)
    set u : ℝ := s1 + min (δ / 2) ((s2 - s1) / 2) with hu
    have hmin_pos : 0 < min (δ / 2) ((s2 - s1) / 2) := lt_min (by linarith) (by linarith)
    have hu1 : s1 < u := by rw [hu]; linarith
    have hu2 : u < s2 := by
      have := min_le_right (δ / 2) ((s2 - s1) / 2)
      rw [hu]; linarith
    have hudist : dist u s1 < δ := by
      rw [Real.dist_eq, abs_of_pos (by linarith)]
      have := min_le_left (δ / 2) ((s2 - s1) / 2)
      rw [hu]; linarith
    have huint' : u ∈ interior (natParamSet P) := hIoo ⟨by linarith, hu2⟩
    have humem : u ∈ natParamSet P := interior_subset huint'
    have huint : Integrable id (tilt P u) := integrable_id_of_interior huint'
    set z := mn P u with hz
    have hzmem : z ∈ meanSet P := ⟨u, humem, huint, rfl⟩
    have hzgt : μ' < z := hstrict u hu1 humem huint
    have hQ : expFam P z = tilt P u := by
      obtain ⟨hθ, hθint, hθm⟩ := theta_spec hzmem
      exact tilt_eq_of_mn_eq hθ humem hθint huint hθm
    have hmeanQ : ∫ x, x ∂(expFam P z) = z := by rw [hQ]; rfl
    calc banditDInf (model P) (expFam P μ) μ'
        ≤ InformationTheory.klDiv (expFam P μ) (expFam P z) := by
          unfold banditDInf
          exact iInf₂_le (expFam P z) ⟨⟨z, hzmem, rfl⟩, by rw [hmeanQ]; exact hzgt⟩
      _ = ENNReal.ofReal (F u) := by rw [hQ]; exact hKL u humem
      _ ≤ ENNReal.ofReal (F s1 + ε) := by
          apply ENNReal.ofReal_le_ofReal
          have := hδF hudist
          rw [Real.dist_eq] at this
          linarith [(abs_lt.1 this).2]
      _ ≤ ENNReal.ofReal (F s1) + ε := by
          calc ENNReal.ofReal (F s1 + ε) ≤ ENNReal.ofReal (F s1) + ENNReal.ofReal ε :=
                ENNReal.ofReal_add_le
            _ = ENNReal.ofReal (F s1) + ε := by rw [ENNReal.ofReal_coe_nnreal]
  · -- lower bound: every admissible `Q` is a tilt with parameter `≥ θ(µ')`
    unfold banditDInf
    apply le_iInf₂
    rintro Q ⟨⟨z, hz, rfl⟩, hmeanQ⟩
    obtain ⟨hθ, hθint, hθm⟩ := theta_spec hz
    have hzgt : μ' < z := by
      have : ∫ x, x ∂(expFam P z) = z := hθm
      rw [this] at hmeanQ; exact hmeanQ
    have hθs1 : s1 ≤ thetaOf P z := by
      by_contra h; push_neg at h
      have := mn_mono hθ hs1 hθint hint1 h.le
      rw [hθm, hm1] at this; linarith
    show ENNReal.ofReal (F s1) ≤ InformationTheory.klDiv (tilt P s0) (tilt P (thetaOf P z))
    rw [hKL _ hθ]
    apply ENNReal.ofReal_le_ofReal
    have hnn := kl_real_nonneg hs1 hθ hint1
    rw [hm1] at hnn
    simp only [hF]
    nlinarith
