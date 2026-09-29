-- Prove2me | solution 1 for BanditAlgorithm.bayesian_ts_conditional_information_gain_chain_rule
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-02T02:41:30.019948+00:00
-- url     : https://prove2.me/submissions/7728d814-5bb2-4862-982b-1d0eb208a348

import Definitions.Def_BayesianTSRoundConditionalGains
import Theorems.Thm_InformationTheory_klDiv_compProd_self_eq_lintegral_of_ae
import Theorems.Thm_InformationTheory_klDiv_map_measurableEmbedding
import Theorems.Thm_InformationTheory_finite_range_mutualInformation_le_marginal_entropy
import Theorems.Thm_InformationTheory_categorical_toReal_klDiv_eq_sum
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal ProbabilityTheory

namespace InformationTheory

theorem finite_range_mutualInformation_ne_top
    {Omega Alpha : Type*} {mOmega : MeasurableSpace Omega}
    {mAlpha : MeasurableSpace Alpha} {k : ℕ} [NeZero k]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (f : Omega → Alpha) (g : Omega → Fin k)
    (hf : Measurable f) (hg : Measurable g) :
    klDiv (mu.map (fun x ↦ (f x, g x)))
      ((mu.map f).prod (mu.map g)) ≠ ∞ := by
  let rho : Measure (Alpha × Fin k) := mu.map (fun x ↦ (f x, g x))
  let muF : Measure Alpha := mu.map f
  let kappa : Kernel Alpha (Fin k) := rho.condKernel
  let p : Measure (Fin k) := mu.map g
  letI : IsProbabilityMeasure rho := by
    dsimp [rho]
    exact Measure.isProbabilityMeasure_map (hf.prod hg).aemeasurable
  letI : IsProbabilityMeasure muF := by
    dsimp [muF]
    exact Measure.isProbabilityMeasure_map hf.aemeasurable
  letI : IsProbabilityMeasure p := by
    dsimp [p]
    exact Measure.isProbabilityMeasure_map hg.aemeasurable
  letI : IsMarkovKernel kappa := by
    dsimp [kappa]
    infer_instance
  have hfst : rho.fst = muF := by
    dsimp [rho, muF]
    exact Measure.fst_map_prodMk hg
  have hrho : muF ⊗ₘ kappa = rho := by
    rw [← hfst]
    exact rho.disintegrate rho.condKernel
  have hmarg : kappa ∘ₘ muF = p := by
    calc
      kappa ∘ₘ muF = (muF ⊗ₘ kappa).snd := by rw [Measure.snd_compProd]
      _ = rho.snd := by rw [hrho]
      _ = p := by
        dsimp [rho, p]
        exact Measure.snd_map_prodMk hf
  have hac : ∀ᵐ x ∂muF, kappa x ≪ p := by
    have hsingle (a : Fin k) (ha : p {a} = 0) :
        ∀ᵐ x ∂muF, kappa x {a} = 0 := by
      rw [← hmarg] at ha
      rw [Measure.bind_apply (MeasurableSet.singleton a) kappa.aemeasurable] at ha
      rw [lintegral_eq_zero_iff
        (Kernel.measurable_coe kappa (MeasurableSet.singleton a))] at ha
      exact ha
    have hall : ∀ᵐ x ∂muF, ∀ a : Fin k, p {a} = 0 → kappa x {a} = 0 := by
      rw [ae_all_iff]
      intro a
      by_cases ha : p {a} = 0
      · filter_upwards [hsingle a ha] with x hx
        exact fun _ ↦ hx
      · exact Filter.Eventually.of_forall fun _ h ↦ (ha h).elim
    filter_upwards [hall] with x hx
    apply Measure.AbsolutelyContinuous.mk
    intro s _ hs
    have hs' : p (↑s.toFinite.toFinset : Set (Fin k)) = 0 := by simpa using hs
    have hzero : ∀ a ∈ s.toFinite.toFinset, kappa x {a} = 0 := by
      intro a ha
      apply hx a
      exact measure_mono_null (Set.singleton_subset_iff.mpr ha) hs'
    rw [← Set.Finite.coe_toFinset s.toFinite, ← sum_measure_singleton]
    exact Finset.sum_eq_zero hzero
  have hlt : ∀ᵐ x ∂muF, klDiv (kappa x) p < ∞ := by
    filter_upwards [hac] with x hx
    exact lt_top_iff_ne_top.mpr (klDiv_ne_top hx Integrable.of_finite)
  let q : Fin k → Alpha → ℝ := fun a x ↦ (kappa x).real {a}
  have hq_meas (a : Fin k) : Measurable (q a) :=
    (Kernel.measurable_coe kappa (MeasurableSet.singleton a)).ennreal_toReal
  have hq0 (a : Fin k) (x : Alpha) : 0 ≤ q a x := by positivity
  have hq1 (a : Fin k) (x : Alpha) : q a x ≤ 1 := by
    dsimp [q]
    calc
      (kappa x).real {a} ≤ (kappa x).real Set.univ :=
        ENNReal.toReal_mono (measure_ne_top (kappa x) Set.univ)
          (measure_mono (Set.subset_univ _))
      _ = 1 := by simp
  have hq_int (a : Fin k) : Integrable (q a) muF := by
    apply Integrable.of_bound (hq_meas a).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (hq0 a x)]
      exact hq1 a x
  have hneg_int (a : Fin k) :
      Integrable (fun x ↦ Real.negMulLog (q a x)) muF := by
    apply Integrable.of_bound
      (Real.continuous_negMulLog.measurable.comp (hq_meas a)).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun x ↦ by
      change ‖Real.negMulLog (q a x)‖ ≤ 1
      rw [Real.norm_eq_abs,
        abs_of_nonneg (Real.negMulLog_nonneg (hq0 a x) (hq1 a x))]
      exact (Real.negMulLog_le_one_sub_self (hq0 a x)).trans (by linarith [hq0 a x])
  let F : Alpha → ℝ := fun x ↦
    ∑ a, (-Real.negMulLog (q a x) - q a x * Real.log (p.real {a}))
  have hF_int : Integrable F muF := by
    apply integrable_finset_sum
    intro a _
    exact (hneg_int a).neg.sub ((hq_int a).mul_const _)
  have hkl_eq : (fun x ↦ (klDiv (kappa x) p).toReal) =ᵐ[muF] F := by
    filter_upwards [hac] with x hx
    rw [categorical_toReal_klDiv_eq_sum (kappa x) p hx]
    apply Finset.sum_congr rfl
    intro a _
    by_cases hpa : p {a} = 0
    · have hqa_measure : kappa x {a} = 0 := hx hpa
      simp [q, measureReal_def, hpa, hqa_measure, Real.negMulLog]
    · have hpa_real : p.real {a} ≠ 0 := by
        rw [measureReal_def, ENNReal.toReal_ne_zero]
        exact ⟨hpa, measure_ne_top p {a}⟩
      by_cases hqa_real : q a x = 0
      · change q a x * Real.log (q a x / p.real {a}) =
          -Real.negMulLog (q a x) - q a x * Real.log (p.real {a})
        rw [hqa_real]
        simp only [zero_div, zero_mul, Real.negMulLog_zero, neg_zero, zero_sub]
      · rw [Real.log_div hqa_real hpa_real]
        simp only [Real.negMulLog]
        ring
  have hkl_ennreal : (fun x ↦ klDiv (kappa x) p) =ᵐ[muF]
      fun x ↦ ENNReal.ofReal (F x) := by
    filter_upwards [hlt, hkl_eq] with x hx heq
    calc
      klDiv (kappa x) p = ENNReal.ofReal (klDiv (kappa x) p).toReal :=
        (ENNReal.ofReal_toReal hx.ne).symm
      _ = ENNReal.ofReal (F x) := by rw [heq]
  change klDiv rho (muF.prod p) ≠ ∞
  rw [← hrho, ← Measure.compProd_const,
    klDiv_compProd_self_eq_lintegral_of_ae muF kappa (Kernel.const Alpha p)
      (by simpa using hac)]
  simp only [Kernel.const_apply]
  rw [lintegral_congr_ae hkl_ennreal]
  apply ne_of_lt
  exact lt_of_le_of_lt
    (lintegral_mono fun x ↦ Real.ofReal_le_enorm (F x))
    (hasFiniteIntegral_iff_enorm.mp hF_int.hasFiniteIntegral)

private def rotate {H A Y : Type*} : (H × A) × Y → (H × Y) × A :=
  fun z ↦ ((z.1.1, z.2), z.1.2)

private def unrotate {H A Y : Type*} : (H × Y) × A → (H × A) × Y :=
  fun z ↦ ((z.1.1, z.2), z.1.2)

private theorem measurableEmbedding_rotate
    {H A Y : Type*} [MeasurableSpace H] [MeasurableSpace A] [MeasurableSpace Y] :
    MeasurableEmbedding (rotate : (H × A) × Y → (H × Y) × A) := by
  refine ⟨?_, ?_, ?_⟩
  · intro z
    intro z'
    simp only [rotate]
    aesop
  · exact ((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk
      (measurable_snd.comp measurable_fst)
  · intro s hs
    have hu : Measurable (unrotate : (H × Y) × A → (H × A) × Y) :=
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk
        (measurable_snd.comp measurable_fst)
    rw [show rotate '' s = unrotate ⁻¹' s by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact hw
      · intro hz
        exact ⟨unrotate z, hz, by cases z with | mk hy a => cases hy; rfl⟩]
    exact hs.preimage hu

theorem conditionalMutualInformation_chain_rule
    {Omega H Y : Type*} {mOmega : MeasurableSpace Omega}
    {mH : MeasurableSpace H} {mY : MeasurableSpace Y}
    [StandardBorelSpace H] [StandardBorelSpace Y]
    [Nonempty Y]
    {k : ℕ} [NeZero k]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (hist : Omega → H) (obs : Omega → Y) (act : Omega → Fin k)
    (hhist : Measurable hist) (hobs : Measurable obs) (hact : Measurable act) :
    (∫ h, (klDiv (condDistrib (fun w ↦ (act w, obs w)) hist mu h)
          ((condDistrib act hist mu h).prod (condDistrib obs hist mu h))).toReal
        ∂mu.map hist) ≤
      (klDiv (mu.map (fun w ↦ ((hist w, obs w), act w)))
        ((mu.map (fun w ↦ (hist w, obs w))).prod (Measure.map act mu))).toReal -
      (klDiv (mu.map (fun w ↦ (hist w, act w)))
        ((Measure.map hist mu).prod (Measure.map act mu))).toReal := by
  let nu : Measure H := mu.map hist
  let pA : Measure (Fin k) := mu.map act
  let kA : Kernel H (Fin k) := condDistrib act hist mu
  let kY : Kernel H Y := condDistrib obs hist mu
  let kAY : Kernel H (Fin k × Y) := condDistrib (fun w ↦ (act w, obs w)) hist mu
  let muHA : Measure (H × Fin k) := mu.map (fun w ↦ (hist w, act w))
  let kYHA : Kernel (H × Fin k) Y := condDistrib obs (fun w ↦ (hist w, act w)) mu
  let kYH : Kernel (H × Fin k) Y := Kernel.prodMkRight (Fin k) kY
  let P : Measure ((H × Fin k) × Y) := muHA ⊗ₘ kYHA
  let U : Measure ((H × Fin k) × Y) := muHA ⊗ₘ kYH
  let V : Measure ((H × Fin k) × Y) := (nu.prod pA) ⊗ₘ kYH
  have hP : P = mu.map (fun w ↦ ((hist w, act w), obs w)) := by
    dsimp [P, muHA, kYHA]
    exact compProd_map_condDistrib hobs.aemeasurable
  have hHA : nu ⊗ₘ kA = muHA := by
    dsimp [nu, kA, muHA]
    exact compProd_map_condDistrib hact.aemeasurable
  have hHY : nu ⊗ₘ kY = mu.map (fun w ↦ (hist w, obs w)) := by
    dsimp [nu, kY]
    exact compProd_map_condDistrib hobs.aemeasurable
  have hchain : klDiv P V = klDiv muHA (nu.prod pA) + klDiv P U := by
    dsimp [P, V, U]
    exact klDiv_compProd_eq_add muHA (nu.prod pA) kYHA kYH
  have hPmap : P.map rotate = mu.map (fun w ↦ ((hist w, obs w), act w)) := by
    rw [hP, Measure.map_map measurableEmbedding_rotate.measurable
      ((hhist.prodMk hact).prodMk hobs)]
    rfl
  have hVmap : V.map rotate = (mu.map (fun w ↦ (hist w, obs w))).prod pA := by
    rw [← hHY]
    apply Measure.ext_prod₃'
    intro s t u hs ht hu
    rw [Measure.map_apply measurableEmbedding_rotate.measurable ((hs.prod ht).prod hu)]
    rw [show rotate ⁻¹' ((s ×ˢ t) ×ˢ u) = (s ×ˢ u) ×ˢ t by
      ext z
      rcases z with ⟨⟨h, a⟩, y⟩
      simp only [Set.mem_preimage, Set.mem_prod, rotate]
      aesop]
    change V ((s ×ˢ u) ×ˢ t) = (nu ⊗ₘ kY).prod pA ((s ×ˢ t) ×ˢ u)
    rw [Measure.prod_prod, Measure.compProd_apply_prod (hs.prod hu) ht,
      Measure.compProd_apply_prod hs ht]
    change (∫⁻ z in s ×ˢ u, kY z.1 t ∂nu.prod pA) =
      (∫⁻ h in s, kY h t ∂nu) * pA u
    rw [MeasureTheory.setLIntegral_prod]
    · simp only [MeasureTheory.setLIntegral_const]
      exact MeasureTheory.lintegral_mul_const (pA u) (Kernel.measurable_coe kY ht)
    · exact ((Kernel.measurable_coe kY ht).comp measurable_fst).aemeasurable.restrict
  let W : Measure (H × (Fin k × Y)) := nu ⊗ₘ kAY
  let Z : Measure (H × (Fin k × Y)) := nu ⊗ₘ (kA.prod kY)
  have hW : W = mu.map (fun w ↦ (hist w, (act w, obs w))) := by
    dsimp [W, nu, kAY]
    exact compProd_map_condDistrib (hact.prodMk hobs).aemeasurable
  have hkprod : kA ⊗ₖ kYH = kA.prod kY := by
    ext h s hs
    rw [Kernel.compProd_apply hs, Kernel.prod_apply, Measure.prod_apply hs]
    rfl
  have hWmap : W.map MeasurableEquiv.prodAssoc.symm = P := by
    rw [hW, Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable
      (hhist.prodMk (hact.prodMk hobs)), hP]
    rfl
  have hZmap : Z.map MeasurableEquiv.prodAssoc.symm = U := by
    dsimp [Z]
    rw [← hkprod, Measure.compProd_assoc, hHA]
  have hnextKL : klDiv P V =
      klDiv (mu.map (fun w ↦ ((hist w, obs w), act w)))
        ((mu.map (fun w ↦ (hist w, obs w))).prod pA) := by
    rw [← hPmap, ← hVmap]
    exact (klDiv_map_measurableEmbedding measurableEmbedding_rotate P V).symm
  have hcondKL : klDiv P U = klDiv W Z := by
    rw [← hWmap, ← hZmap]
    exact klDiv_map_measurableEmbedding
      MeasurableEquiv.prodAssoc.symm.measurableEmbedding W Z
  have hnext_ne :
      klDiv (mu.map (fun w ↦ ((hist w, obs w), act w)))
        ((mu.map (fun w ↦ (hist w, obs w))).prod pA) ≠ ∞ := by
    exact finite_range_mutualInformation_ne_top mu
      (fun w ↦ (hist w, obs w)) act (hhist.prodMk hobs) hact
  have hprev_ne : klDiv muHA (nu.prod pA) ≠ ∞ := by
    exact finite_range_mutualInformation_ne_top mu hist act hhist hact
  have hcond_ne : klDiv P U ≠ ∞ := by
    apply ne_top_of_le_ne_top (hnextKL ▸ hnext_ne)
    rw [hchain]
    exact le_add_self
  have hWZ_ne : klDiv W Z ≠ ∞ := by
    rw [← hcondKL]
    exact hcond_ne
  have hWZac : W ≪ Z := (klDiv_ne_top_iff.mp hWZ_ne).1
  have hlocal_ac : ∀ᵐ h ∂nu, kAY h ≪ (kA.prod kY) h :=
    Measure.AbsolutelyContinuous.kernel_of_compProd hWZac
  have hlin : klDiv W Z =
      ∫⁻ h, klDiv (kAY h) ((kA.prod kY) h) ∂nu := by
    exact klDiv_compProd_self_eq_lintegral_of_ae nu kAY (kA.prod kY) hlocal_ac
  have hchain' :
      klDiv (mu.map (fun w ↦ ((hist w, obs w), act w)))
          ((mu.map (fun w ↦ (hist w, obs w))).prod pA) =
        klDiv muHA (nu.prod pA) + klDiv W Z := by
    rw [← hnextKL, ← hcondKL]
    exact hchain
  have hrealchain :
      (klDiv W Z).toReal =
        (klDiv (mu.map (fun w ↦ ((hist w, obs w), act w)))
          ((mu.map (fun w ↦ (hist w, obs w))).prod pA)).toReal -
        (klDiv muHA (nu.prod pA)).toReal := by
    have hadd := congrArg ENNReal.toReal hchain'
    rw [ENNReal.toReal_add hprev_ne hWZ_ne] at hadd
    linarith
  let gain : H → ℝ≥0∞ := fun h ↦ klDiv (kAY h) ((kA h).prod (kY h))
  have hAmap : kA =ᵐ[nu] kAY.map Prod.fst := by
    dsimp [kA, kAY, nu]
    simpa [Function.comp_def] using
      (condDistrib_comp hist (hact.prodMk hobs).aemeasurable measurable_fst)
  have hYmap : kY =ᵐ[nu] kAY.map Prod.snd := by
    dsimp [kY, kAY, nu]
    simpa [Function.comp_def] using
      (condDistrib_comp hist (hact.prodMk hobs).aemeasurable measurable_snd)
  have hgain_lt : ∀ᵐ h ∂nu, gain h < ∞ := by
    filter_upwards [hAmap, hYmap] with h hhA hhY
    have hswap_ne := finite_range_mutualInformation_ne_top (kAY h)
      (fun z : Fin k × Y ↦ z.2) (fun z : Fin k × Y ↦ z.1)
      measurable_snd measurable_fst
    have hmap := klDiv_map_measurableEmbedding
      (MeasurableEquiv.prodComm.measurableEmbedding :
        MeasurableEmbedding (Prod.swap : Fin k × Y → Y × Fin k))
      (kAY h) ((kA h).prod (kY h))
    change klDiv (Measure.map Prod.swap (kAY h))
      (Measure.map Prod.swap ((kA h).prod (kY h))) =
        klDiv (kAY h) ((kA h).prod (kY h)) at hmap
    rw [Measure.prod_swap, hhA, hhY] at hmap
    dsimp [gain]
    rw [hhA, hhY, ← hmap]
    apply lt_top_iff_ne_top.mpr
    have hswap_ne' : klDiv (Measure.map Prod.swap (kAY h))
        (((kAY.map Prod.snd) h).prod ((kAY.map Prod.fst) h)) ≠ ∞ := by
      rw [Kernel.map_apply kAY measurable_snd h,
        Kernel.map_apply kAY measurable_fst h]
      exact hswap_ne
    exact hswap_ne'
  have hlin' : klDiv W Z = ∫⁻ h, gain h ∂nu := by
    simpa only [gain, Kernel.prod_apply] using hlin
  by_cases hgain : AEMeasurable gain nu
  · have hgain_lintegral : (∫⁻ h, gain h ∂nu) ≠ ∞ := by
      exact hlin' ▸ hWZ_ne
    have hresult : (∫ h, (gain h).toReal ∂nu) ≤
        (klDiv (mu.map (fun w ↦ ((hist w, obs w), act w)))
          ((mu.map (fun w ↦ (hist w, obs w))).prod pA)).toReal -
        (klDiv muHA (nu.prod pA)).toReal := by
      rw [integral_toReal hgain hgain_lt, ← hlin']
      exact le_of_eq hrealchain
    simpa [gain, kAY, kA, kY, nu, pA, muHA] using hresult
  · have hnotint : ¬ Integrable (fun h ↦ (gain h).toReal) nu := by
      intro hint
      have hen : gain =ᵐ[nu] fun h ↦ ENNReal.ofReal (gain h).toReal := by
        filter_upwards [hgain_lt] with h hh
        exact (ENNReal.ofReal_toReal hh.ne).symm
      apply hgain
      exact hint.1.aemeasurable.ennreal_ofReal.congr hen.symm
    have hresult : (∫ h, (gain h).toReal ∂nu) ≤
        (klDiv (mu.map (fun w ↦ ((hist w, obs w), act w)))
          ((mu.map (fun w ↦ (hist w, obs w))).prod pA)).toReal -
        (klDiv muHA (nu.prod pA)).toReal := by
      rw [integral_undef hnotint]
      have hnonneg : 0 ≤ (klDiv W Z).toReal := ENNReal.toReal_nonneg
      rw [hrealchain] at hnonneg
      exact hnonneg
    simpa [gain, kAY, kA, kY, nu, pA, muHA] using hresult

end InformationTheory

open MeasureTheory ProbabilityTheory InformationTheory

namespace BanditAlgorithm

private theorem measurable_optimal_info_chain {k n : ℕ} [NeZero k] :
    Measurable (bayesianOptimalAction : (Fin n → Fin k → ℝ) → Fin k) := by
  apply measurable_minArgmax.comp
  apply measurable_pi_lambda
  intro a
  exact Finset.measurable_sum Finset.univ fun t _ ↦
    (measurable_pi_apply a).comp (measurable_pi_apply t)

theorem _root_.solution
    {k n : ℕ} [NeZero k]
    (Q : Measure (Fin n → Fin k → ℝ)) [IsProbabilityMeasure Q]
    {pi : BanditPolicy k} (t : Fin n) :
    let history := fun p : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
      fun s : Fin t.1 ↦ p.2 (Fin.castLE (Nat.le_of_lt t.2) s)
    let nu := Measure.map history (bayesianAdversarialMeasure Q pi n le_rfl)
    (∫ h, bayesianTSRoundConditionalInformationGain Q pi t h ∂nu) ≤
      bayesianHistoryMutualInformation Q pi (t.1 + 1) (Nat.succ_le_iff.mpr t.2) -
        bayesianHistoryMutualInformation Q pi t.1 (Nat.le_of_lt t.2) := by
  dsimp only
  let mu := bayesianAdversarialMeasure Q pi n le_rfl
  let hist := fun p : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
    fun s : Fin t.1 ↦ p.2 (Fin.castLE (Nat.le_of_lt t.2) s)
  let histNext := fun p : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
    fun s : Fin (t.1 + 1) ↦ p.2 (Fin.castLE (Nat.succ_le_iff.mpr t.2) s)
  let obs := fun p : (Fin n → Fin k → ℝ) × BanditHistory k n ↦ p.2 t
  let act := fun p : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
    bayesianOptimalAction p.1
  have hhist : Measurable hist := by
    apply measurable_pi_lambda
    intro s
    exact (measurable_pi_apply (Fin.castLE (Nat.le_of_lt t.2) s)).comp measurable_snd
  have hhistNext : Measurable histNext := by
    apply measurable_pi_lambda
    intro s
    exact (measurable_pi_apply (Fin.castLE (Nat.succ_le_iff.mpr t.2) s)).comp measurable_snd
  have hobs : Measurable obs := (measurable_pi_apply t).comp measurable_snd
  have hact : Measurable act := measurable_optimal_info_chain.comp measurable_fst
  let e : BanditHistory k (t.1 + 1) ≃ᵐ
      (BanditHistory k t.1 × (Fin k × ℝ)) :=
    (MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (t.1 + 1) ↦ Fin k × ℝ) (Fin.last t.1)).trans
        MeasurableEquiv.prodComm
  have heval (p : (Fin n → Fin k → ℝ) × BanditHistory k n) :
      e (histNext p) = (hist p, obs p) := by
    apply Prod.ext
    · funext s
      simp [e, histNext, hist, MeasurableEquiv.piFinSuccAbove]
      apply congrArg p.2
      apply Fin.ext
      simp
    · simp [e, histNext, obs, MeasurableEquiv.piFinSuccAbove]
      apply congrArg p.2
      apply Fin.ext
      simp
  let E : (BanditHistory k (t.1 + 1) × Fin k) ≃ᵐ
      ((BanditHistory k t.1 × (Fin k × ℝ)) × Fin k) :=
    MeasurableEquiv.prodCongr e (MeasurableEquiv.refl (Fin k))
  have hhistmap : (mu.map histNext).map e =
      mu.map (fun p ↦ (hist p, obs p)) := by
    rw [Measure.map_map e.measurable hhistNext]
    apply Measure.map_congr
    exact Filter.Eventually.of_forall fun p ↦ by
      simp only [Function.comp_apply]
      exact heval p
  have hjoint : (mu.map (fun p ↦ (histNext p, act p))).map E =
      mu.map (fun p ↦ ((hist p, obs p), act p)) := by
    rw [Measure.map_map E.measurable (hhistNext.prodMk hact)]
    apply Measure.map_congr
    exact Filter.Eventually.of_forall fun p ↦ by
      simp only [Function.comp_apply]
      apply Prod.ext
      · exact heval p
      · rfl
  have hprod : ((mu.map histNext).prod (mu.map act)).map E =
      (mu.map (fun p ↦ (hist p, obs p))).prod (mu.map act) := by
    change Measure.map (Prod.map e id) ((mu.map histNext).prod (mu.map act)) = _
    rw [← Measure.map_prod_map (mu.map histNext) (mu.map act)
      e.measurable measurable_id, hhistmap, Measure.map_id]
  have hgeneric := conditionalMutualInformation_chain_rule mu hist obs act
    hhist hobs hact
  refine hgeneric.trans_eq ?_
  dsimp [bayesianHistoryMutualInformation]
  congr 1
  have hKL := klDiv_map_measurableEmbedding E.measurableEmbedding
    (mu.map (fun p ↦ (histNext p, act p)))
    ((mu.map histNext).prod (mu.map act))
  rw [hjoint, hprod] at hKL
  exact congrArg ENNReal.toReal hKL

end BanditAlgorithm
