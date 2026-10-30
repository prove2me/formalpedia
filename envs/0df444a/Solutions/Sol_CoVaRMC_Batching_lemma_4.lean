-- Prove2me | solution 1 for CoVaRMC.Batching.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T22:54:24.483972+00:00
-- url     : https://prove2.me/submissions/99555512-b096-4f23-ba9a-7a4efc5b316f

import Mathlib
import Definitions.Def_CoVaRMC_Batching_Setting
import Theorems.Thm_EthierKurtz_berry_esseen_bounded_independent

open MeasureTheory ProbabilityTheory Filter Topology

namespace CoVaRL4Aux


lemma measurableSet_sort_eq {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (X : Fin N → Ω → ℝ)
    (hX : ∀ j, Measurable (X j)) (σ : Equiv.Perm (Fin N)) :
    MeasurableSet {ω | Tuple.sort (fun j => X j ω) = σ} := by
  have : {ω | Tuple.sort (fun j => X j ω) = σ} =
      (⋂ i : Fin N, ⋂ j : Fin N, {ω | i ≤ j → X (σ i) ω ≤ X (σ j) ω}) ∩
      (⋂ i : Fin N, ⋂ j : Fin N, {ω | i < j → X (σ i) ω = X (σ j) ω → σ i < σ j}) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    rw [eq_comm, Tuple.eq_sort_iff]
    rfl
  rw [this]
  refine MeasurableSet.inter (MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_)
    (MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_)
  · by_cases hij : i ≤ j
    · simp only [hij, true_implies]
      exact measurableSet_le (hX _) (hX _)
    · simp [hij]
  · by_cases hij : i < j
    · by_cases hs : σ i < σ j
      · simp [hs]
      · simp only [hij, hs, true_implies, imp_false]
        exact (measurableSet_eq_fun (hX _) (hX _)).compl
    · simp [hij]

lemma measurable_induced {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (X A : Fin N → Ω → ℝ)
    (hX : ∀ j, Measurable (X j)) (hA : ∀ j, Measurable (A j)) (r : Fin N) :
    Measurable (fun ω => A (Tuple.sort (fun j => X j ω) r) ω) := by
  have heq : (fun ω => A (Tuple.sort (fun j => X j ω) r) ω) = fun ω =>
      ∑ σ : Equiv.Perm (Fin N),
        Set.indicator {ω | Tuple.sort (fun j => X j ω) = σ} (A (σ r)) ω := by
    funext ω
    rw [Finset.sum_eq_single (Tuple.sort (fun j => X j ω))]
    · simp
    · intro σ _ hσ
      rw [Set.indicator_of_notMem]
      simp only [Set.mem_ofPred_eq]
      exact fun h => hσ h.symm
    · simp
  rw [heq]
  exact Finset.measurable_sum _ fun σ _ =>
    (hA _).indicator (measurableSet_sort_eq X hX σ)

/-- Standard normal cdf is continuous. -/
lemma continuous_Phi : Continuous (cdf (gaussianReal 0 1)) := by
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  rw [continuous_iff_continuousAt]
  intro x
  have hm : Monotone (cdf (gaussianReal 0 1)) := monotone_cdf _
  rw [hm.continuousAt_iff_leftLim_eq_rightLim, StieltjesFunction.rightLim_eq]
  have h1 := (cdf (gaussianReal 0 1)).measure_singleton x
  rw [measure_cdf, measure_singleton, eq_comm, ENNReal.ofReal_eq_zero] at h1
  have h2 := hm.leftLim_le (le_refl x)
  linarith

end CoVaRL4Aux

open CoVaRL4Aux

open CoVaRMC.Batching in
theorem solution (D : JointDensity) (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : ℕ × ℕ → Ω → ℝ × ℝ) (hSm : ∀ p, Measurable (S p)) (hSi : iIndepFun S P)
    (hSl : ∀ p, P.map (S p) = D.law)
    (k m : ℕ) (hk : 0 < k) (hm : 0 < m) (y : ℝ) (hσ : 0 < sigmaHat P S α m y) (t : ℝ) :
    |(P {ω | √(k : ℝ) / sigmaHat P S α m y * (FkHat S α k m y ω - pHat P S α m y) ≤ t}).toReal
        - cdf (gaussianReal 0 1) t|
      ≤ 33 / 4 * (1 / (sigmaHat P S α m y ^ 3 * √(k : ℝ))) := by
  have hμ : IsProbabilityMeasure D.law := by
    rw [← hSl (0, 0)]; exact Measure.isProbabilityMeasure_map (hSm _).aemeasurable
  set μ := D.law with hμdef
  set Q : Measure (Fin k → Fin m → ℝ × ℝ) := Measure.pi (fun _ => Measure.pi (fun _ => μ)) with hQdef
  -- the law of the array of batches is `Q`
  set B : Ω → (Fin k → Fin m → ℝ × ℝ) := fun ω i j => S ((i : ℕ), (j : ℕ)) ω with hBdef
  have hBm : Measurable B :=
    measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => hSm _
  have hPB : P.map B = Q := by
    set Sf : Ω → (Fin k × Fin m → ℝ × ℝ) := fun ω p => S ((p.1 : ℕ), (p.2 : ℕ)) ω with hSfdef
    have hSfm : Measurable Sf := measurable_pi_lambda _ fun p => hSm _
    have hind : iIndepFun (fun p : Fin k × Fin m => S ((p.1 : ℕ), (p.2 : ℕ))) P :=
      hSi.precomp (g := fun p : Fin k × Fin m => ((p.1 : ℕ), (p.2 : ℕ)))
        (by
          intro a b h
          simp only [Prod.mk.injEq] at h
          exact Prod.ext (Fin.ext h.1) (Fin.ext h.2))
    have hflat : P.map Sf = Measure.pi (fun _ : Fin k × Fin m => μ) := by
      rw [(iIndepFun_iff_map_fun_eq_pi_map (fun p => (hSm _).aemeasurable)).mp hind]
      congr 1; funext p; exact hSl _
    set F : (Fin k → Fin m → ℝ × ℝ) → (Fin k × Fin m → ℝ × ℝ) := fun w p => w p.1 p.2 with hFdef
    have hFm : Measurable F := measurable_pi_lambda _ fun p =>
      (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)
    set G : (Fin k × Fin m → ℝ × ℝ) → (Fin k → Fin m → ℝ × ℝ) := fun v i j => v (i, j) with hGdef
    have hGm : Measurable G :=
      measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => measurable_pi_apply _
    have hQF : Q.map F = Measure.pi (fun _ : Fin k × Fin m => μ) := by
      refine (Measure.pi_eq fun s hs => ?_).symm
      rw [Measure.map_apply hFm (MeasurableSet.univ_pi hs)]
      have : F ⁻¹' Set.univ.pi s = Set.univ.pi (fun i => Set.univ.pi (fun j => s (i, j))) := by
        ext w; simp [hFdef]
      rw [this, hQdef, Measure.pi_pi]
      simp_rw [Measure.pi_pi]
      rw [← Fintype.prod_prod_type']
    have hBG : B = G ∘ Sf := rfl
    have hGF : G ∘ F = id := rfl
    rw [hBG, ← Measure.map_map hGm hSfm, hflat, ← hQF, Measure.map_map hGm hFm, hGF, Measure.map_id]
  -- block statistic
  set r := rankIdx α m hm with hrdef
  set Yb : (Fin m → ℝ × ℝ) → ℝ := fun b => (b (Tuple.sort (fun j => (b j).1) r)).2 with hYbdef
  have hYbm : Measurable Yb :=
    measurable_induced (fun j (b : Fin m → ℝ × ℝ) => (b j).1) (fun j (b : Fin m → ℝ × ℝ) => (b j).2)
      (fun j => (measurable_pi_apply j).fst) (fun j => (measurable_pi_apply j).snd) r
  have hYhat : ∀ (i : Fin k) ω, Yhat S α m i ω = Yb (B ω i) := by
    intro i ω
    simp only [Yhat, dif_pos hm, ImpactInvesting.Portfolio.inducedOrderStat]
    rfl
  set I : (Fin m → ℝ × ℝ) → ℝ := fun b => (Set.Iic y).indicator (fun _ => (1 : ℝ)) (Yb b) with hIdef
  have hIm : Measurable I := (measurable_const.indicator measurableSet_Iic).comp hYbm
  have hI01 : ∀ b, I b = 0 ∨ I b = 1 := by
    intro b; simp only [hIdef]; by_cases h : Yb b ∈ Set.Iic y <;> simp [h]
  have hIsq : ∀ b, I b ^ 2 = I b := by
    intro b; rcases hI01 b with h | h <;> rw [h] <;> norm_num
  set p := pHat P S α m y with hpdef
  have hEI : ∀ i : Fin k, ∫ w, I (w i) ∂Q = p := by
    intro i
    have hev := measurePreserving_eval (fun _ : Fin k => Measure.pi (fun _ : Fin m => μ)) i
    rw [← integral_map (measurable_pi_apply i).aemeasurable hIm.aestronglyMeasurable, hev.map_eq]
    have hI : I = {b | Yb b ≤ y}.indicator 1 := by
      funext b; simp only [hIdef]
      by_cases h : Yb b ≤ y
      · rw [Set.indicator_of_mem (show Yb b ∈ Set.Iic y from h),
          Set.indicator_of_mem (show b ∈ {b | Yb b ≤ y} from h)]; rfl
      · rw [Set.indicator_of_notMem (show Yb b ∉ Set.Iic y from h),
          Set.indicator_of_notMem (show b ∉ {b | Yb b ≤ y} from h)]
    rw [hI, integral_indicator_one (measurableSet_le hYbm measurable_const)]
    -- compare with batch `0`
    set i0 : Fin k := ⟨0, hk⟩
    have hev0 := measurePreserving_eval (fun _ : Fin k => Measure.pi (fun _ : Fin m => μ)) i0
    have h0 : {ω | Yhat S α m 0 ω ≤ y} = B ⁻¹' ((fun w : Fin k → Fin m → ℝ × ℝ => w i0) ⁻¹'
        {b | Yb b ≤ y}) := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_preimage]
      rw [show (0 : ℕ) = ((i0 : Fin k) : ℕ) from rfl, hYhat]
    simp only [hpdef, pHat]
    rw [h0, ← measureReal_def, ← map_measureReal_apply hBm
      ((measurableSet_le hYbm measurable_const).preimage (measurable_pi_apply i0)), hPB,
      ← map_measureReal_apply (measurable_pi_apply i0) (measurableSet_le hYbm measurable_const),
      hev0.map_eq]
  set σ := sigmaHat P S α m y with hσdef
  have hσsq : σ ^ 2 = p * (1 - p) := by
    have hpp : 0 ≤ p * (1 - p) := by
      by_contra h; push Not at h
      have : σ = 0 := by simp only [hσdef, sigmaHat, ← hpdef]; exact Real.sqrt_eq_zero'.mpr h.le
      linarith
    simp only [hσdef, sigmaHat, ← hpdef]; exact Real.sq_sqrt hpp
  have hσle : σ ^ 2 ≤ 1 / 4 := by rw [hσsq]; nlinarith [sq_nonneg (p - 1 / 2)]
  have hp01 : 0 ≤ p ∧ p ≤ 1 := by
    simp only [hpdef, pHat]
    exact ⟨ENNReal.toReal_nonneg, by
      have := prob_le_one (μ := P) (s := {ω | Yhat S α m 0 ω ≤ y})
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)⟩
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hsk : 0 < √(k : ℝ) := Real.sqrt_pos.mpr hkR
  set c := σ * √(k : ℝ) with hcdef
  have hcpos : 0 < c := mul_pos hσ hsk
  set ξ : Fin k → (Fin k → Fin m → ℝ × ℝ) → ℝ := fun i w => (I (w i) - p) / c with hξdef
  have hξm : ∀ i, Measurable (ξ i) := fun i =>
    ((hIm.comp (measurable_pi_apply i)).sub measurable_const).div_const _
  -- the event, transported to the block space
  have hsum : ∀ ω, √(k : ℝ) / σ * (FkHat S α k m y ω - p) = ∑ i, ξ i (B ω) := by
    intro ω
    have hF : FkHat S α k m y ω = (k : ℝ)⁻¹ * ∑ i : Fin k, I (B ω i) := by
      simp only [FkHat, empCDF]
      congr 1
      rw [Finset.card_filter]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hIdef]
      rw [hYhat]
      by_cases h : Yb (B ω i) ≤ y
      · rw [if_pos h, Set.indicator_of_mem (show Yb (B ω i) ∈ Set.Iic y from h)]
      · rw [if_neg h, Set.indicator_of_notMem (show Yb (B ω i) ∉ Set.Iic y from h)]
    rw [hF]
    simp only [hξdef, ← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, hcdef]
    have hkk : √(k : ℝ) * √(k : ℝ) = k := Real.mul_self_sqrt hkR.le
    field_simp
    rw [Real.sq_sqrt hkR.le]
  have hset : {ω | √(k : ℝ) / σ * (FkHat S α k m y ω - p) ≤ t} =
      B ⁻¹' {w | ∑ i, ξ i w ≤ t} := by
    ext ω; simp only [Set.mem_ofPred_eq, Set.mem_preimage, hsum]
  have hsm : Measurable (fun w => ∑ i, ξ i w) := Finset.measurable_sum _ fun i _ => hξm i
  rw [hset, ← Measure.map_apply hBm (measurableSet_le hsm measurable_const), hPB]
  set Φ := cdf (gaussianReal 0 1) with hΦ
  have hRHS : 33 / 4 * (1 / (σ ^ 3 * √(k : ℝ))) = 33 / 4 / σ ^ 2 * (1 / c) := by
    simp only [hcdef]; field_simp
  by_cases hδ : 1 / c ≤ 1
  · have hind : iIndepFun ξ Q := by
      have := iIndepFun_pi (μ := fun _ : Fin k => Measure.pi (fun _ : Fin m => μ))
        (X := fun i b => (I b - p) / c) (fun i => ((hIm.sub measurable_const).div_const _).aemeasurable)
      exact this
    have hb : ∀ i w, |ξ i w| ≤ 1 / c := by
      intro i w
      simp only [hξdef, abs_div, abs_of_pos hcpos]
      apply div_le_div_of_nonneg_right _ hcpos.le
      rcases hI01 (w i) with h | h <;> rw [h, abs_le] <;> constructor <;> linarith [hp01.1, hp01.2]
    have hmean : ∀ i, ∫ w, ξ i w ∂Q = 0 := by
      intro i
      simp only [hξdef]
      rw [integral_div, integral_sub _ (integrable_const p), hEI i, integral_const, probReal_univ,
        one_smul, sub_self, zero_div]
      exact Integrable.mono' (integrable_const (1 : ℝ)) (hIm.comp (measurable_pi_apply i)).aestronglyMeasurable
        (Eventually.of_forall fun w => by
          rw [Real.norm_eq_abs]; rcases hI01 (w i) with h | h <;> rw [h] <;> norm_num)
    have hvar : ∑ i, ∫ w, ξ i w ^ 2 ∂Q = 1 := by
      have hIint : ∀ i, Integrable (fun w : Fin k → Fin m → ℝ × ℝ => I (w i)) Q := fun i =>
        Integrable.mono' (integrable_const (1 : ℝ)) (hIm.comp (measurable_pi_apply i)).aestronglyMeasurable
          (Eventually.of_forall fun w => by
            rw [Real.norm_eq_abs]; rcases hI01 (w i) with h | h <;> rw [h] <;> norm_num)
      have hterm : ∀ i, ∫ w, ξ i w ^ 2 ∂Q = 1 / k := by
        intro i
        have : (fun w => ξ i w ^ 2) = fun w => ((1 - 2 * p) / c ^ 2) * I (w i) + p ^ 2 / c ^ 2 := by
          funext w
          simp only [hξdef]
          have := hIsq (w i)
          field_simp
          nlinarith [this]
        rw [this, integral_add ((hIint i).const_mul _) (integrable_const _), integral_const_mul, hEI i,
          integral_const, probReal_univ, one_smul]
        have hc2 : c ^ 2 = p * (1 - p) * k := by
          simp only [hcdef]; rw [mul_pow, hσsq, Real.sq_sqrt hkR.le]
        rw [hc2]
        have hp0 : 0 < p * (1 - p) := by rw [← hσsq]; positivity
        rw [div_mul_eq_mul_div, ← add_div, div_eq_div_iff (by positivity) (by positivity)]
        ring
      simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    have hBE := EthierKurtz.berry_esseen_bounded_independent (P := Q) ξ hind hξm
      (one_div_pos.mpr hcpos) hb hmean hvar hδ
    simp only [← hΦ] at hBE
    -- from `<` to `≤`
    have hup : Q.real {w | ∑ i, ξ i w ≤ t} ≤ Φ t + 7 * (1 / c) := by
      have hT : Tendsto (fun ε => Φ (t + ε) + 7 * (1 / c)) (𝓝[>] 0) (𝓝 (Φ t + 7 * (1 / c))) := by
        have : Tendsto (fun ε : ℝ => Φ (t + ε) + 7 * (1 / c)) (𝓝 0) (𝓝 (Φ (t + 0) + 7 * (1 / c))) :=
          ((continuous_Phi.comp (continuous_const.add continuous_id)).tendsto 0).add tendsto_const_nhds
        rw [add_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      refine ge_of_tendsto hT ?_
      filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      have h1 := (abs_le.mp (hBE (t + ε))).2
      have h2 : Q.real {w | ∑ i, ξ i w ≤ t} ≤ Q.real {w | ∑ i, ξ i w < t + ε} :=
        measureReal_mono (fun w (h : ∑ i, ξ i w ≤ t) => (by linarith : ∑ i, ξ i w < t + ε))
      simp only [measureReal_def] at h2 ⊢
      linarith
    have hlow : Φ t - 7 * (1 / c) ≤ Q.real {w | ∑ i, ξ i w ≤ t} := by
      have h1 := (abs_le.mp (hBE t)).1
      have h2 : Q.real {w | ∑ i, ξ i w < t} ≤ Q.real {w | ∑ i, ξ i w ≤ t} :=
        measureReal_mono (fun w (h : ∑ i, ξ i w < t) => (le_of_lt h : ∑ i, ξ i w ≤ t))
      simp only [measureReal_def] at h2 ⊢
      linarith
    have h7 : 7 * (1 / c) ≤ 33 / 4 / σ ^ 2 * (1 / c) := by
      apply mul_le_mul_of_nonneg_right _ (one_div_pos.mpr hcpos).le
      rw [le_div_iff₀ (by positivity)]
      linarith
    rw [hRHS, ← measureReal_def, abs_le]
    constructor <;> linarith
  · push Not at hδ
    have hprob : 0 ≤ (Q {w | ∑ i, ξ i w ≤ t}).toReal ∧ (Q {w | ∑ i, ξ i w ≤ t}).toReal ≤ 1 :=
      ⟨ENNReal.toReal_nonneg, by
        have := prob_le_one (μ := Q) (s := {w | ∑ i, ξ i w ≤ t})
        exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)⟩
    have hΦ01 : 0 ≤ Φ t ∧ Φ t ≤ 1 := ⟨cdf_nonneg _ _, cdf_le_one _ _⟩
    have hbig : 1 ≤ 33 / 4 / σ ^ 2 * (1 / c) := by
      have h4 : 4 ≤ 1 / σ ^ 2 := by
        rw [le_div_iff₀ (by positivity)]; linarith
      have : 33 / 4 / σ ^ 2 = 33 / 4 * (1 / σ ^ 2) := by ring
      rw [this]
      nlinarith
    rw [hRHS, abs_le]
    constructor <;> linarith
