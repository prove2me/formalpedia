-- Prove2me | solution 1 for DistCov.Hilbert.finite_projections_agree
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T20:45:35.200777+00:00
-- url     : https://prove2.me/submissions/941399a5-2f10-4acf-9f7e-a93c283636e5

import Theorems.Thm_DistCov_Hilbert_gaussian_series

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace MeasureTheory.Measure
open scoped Topology NNReal
namespace DistCovProj
open DistCov.Hilbert
abbrev H := DistCov.Indep.L2N
abbrev Ω := ℕ → ℝ
abbrev P := Ω × ℝ
local instance : IsProbabilityMeasure rho := by unfold rho; infer_instance

def S (w : Ω) (u : H) (N : ℕ) : ℝ := ∑ n ∈ Finset.range N, u n * w n

def Converges (w : Ω) (u : H) : Prop := ∃ a : ℝ, Tendsto (S w u) atTop (𝓝 a)

@[fun_prop] lemma S_meas (N : ℕ) : Measurable (fun q : H × Ω => S q.2 q.1 N) := by
  unfold S
  apply Finset.measurable_sum
  intro n hn
  have hc : Continuous (fun u : H => u n) :=
    (continuous_apply n).comp lp.uniformContinuous_coe.continuous
  exact (hc.measurable.comp measurable_fst).mul ((measurable_pi_apply n).comp measurable_snd)

lemma converges_meas : MeasurableSet {q : H × Ω | Converges q.2 q.1} :=
  StronglyMeasurable.measurableSet_exists_tendsto (fun N => (S_meas N).stronglyMeasurable)

lemma converges_ae (u : H) : ∀ᵐ w ∂rho, Converges w u :=
  (gaussian_series u).1.mono fun w hw => ⟨wEval w u, hw⟩

lemma ae_converges_under (μ : Measure H) [SFinite μ] :
    ∀ᵐ w ∂rho, ∀ᵐ u ∂μ, Converges w u := by
  exact (ae_ae_comm converges_meas).mp (Eventually.of_forall fun u => converges_ae u)

@[fun_prop] lemma eval_meas : Measurable (fun q : H × Ω => wEval q.2 q.1) := by
  unfold wEval
  exact Measurable.limsup (fun N => S_meas N)

@[fun_prop] lemma eval_left_meas (w : Ω) : Measurable (fun u : H => wEval w u) :=
  @Measurable.comp H (H × Ω) ℝ _ _ _ (fun q => wEval q.2 q.1) (fun u => (u,w))
    eval_meas (measurable_id.prodMk measurable_const)

lemma S_splice (K N : ℕ) (hKN : K ≤ N) (v : Fin K → ℝ) (w : Ω) (u : H) :
    S (splice K v w) u N = S w u N +
      ∑ n ∈ Finset.range K, u n * (splice K v w n - w n) := by
  have he : ∑ n ∈ Finset.range N, u n * (splice K v w n - w n) =
      ∑ n ∈ Finset.range K, u n * (splice K v w n - w n) := by
    symm
    apply Finset.sum_subset (Finset.range_mono hKN)
    intro n hnN hnK
    have hn : ¬ n < K := by simpa only [Finset.mem_range] using hnK
    simp [splice, hn]
  unfold S
  rw [← he, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  ring

lemma eval_splice (K : ℕ) (v : Fin K → ℝ) (w : Ω) (u : H) (hu : Converges w u) :
    wEval (splice K v w) u = wEval w u +
      ∑ n ∈ Finset.range K, u n * (splice K v w n - w n) := by
  obtain ⟨a, ha⟩ := hu
  have he : S (splice K v w) u =ᶠ[atTop]
      (fun N => S w u N + ∑ n ∈ Finset.range K, u n * (splice K v w n - w n)) := by
    filter_upwards [eventually_ge_atTop K] with N hN
    exact S_splice K N hN v w u
  have ht := (ha.add_const (∑ n ∈ Finset.range K, u n * (splice K v w n - w n))).congr' he.symm
  change limsup (S (splice K v w) u) atTop = limsup (S w u) atTop + _
  rw [ht.limsup_eq, ha.limsup_eq]

lemma stieltjes_eq_of_ae (f g : StieltjesFunction ℝ) (h : (f : ℝ → ℝ) =ᵐ[volume] g) : f = g := by
  have hd : Dense {s : ℝ | f s = g s} := dense_of_ae h
  apply StieltjesFunction.ext
  intro s
  obtain ⟨t, _, ht, hlim⟩ := hd.exists_seq_strictAnti_tendsto s
  have hmem : ∀ᶠ n in atTop, t n ∈ Ici s := Eventually.of_forall fun n => (show s < t n from (ht n).1).le
  have hf := (f.right_continuous s).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hlim,hmem⟩)
  have hg := (g.right_continuous s).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hlim,hmem⟩)
  exact tendsto_nhds_unique hf (hg.congr' (Eventually.of_forall fun n => (ht n).2.symm))

lemma real_law_eq_of_ae_thresholds (μ ν : Measure H) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (w : Ω)
    (h : ∀ᵐ s ∂volume, μ.real {u : H | wEval w u ≤ s} = ν.real {u : H | wEval w u ≤ s}) :
    μ.map (fun u : H => wEval w u) = ν.map (fun u : H => wEval w u) := by
  let e : H → ℝ := fun u => wEval w u
  have hm : Measurable e := eval_left_meas w
  let : IsProbabilityMeasure (μ.map e) := isProbabilityMeasure_map hm.aemeasurable
  let : IsProbabilityMeasure (ν.map e) := isProbabilityMeasure_map hm.aemeasurable
  apply Measure.eq_of_cdf
  apply stieltjes_eq_of_ae
  filter_upwards [h] with s hs
  simp only [cdf_eq_real]
  change (μ.map e).real (Iic s) = (ν.map e).real (Iic s)
  rw [map_measureReal_apply (μ := μ) hm measurableSet_Iic,
    map_measureReal_apply (μ := ν) hm measurableSet_Iic]
  exact hs

lemma c_pos : 0 < cGauss := by
  have hi : Integrable (fun z : ℝ => |z|) (gaussianReal 0 1) :=
    ((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num)).abs
  let : NullSingletonClass (gaussianReal 0 1) :=
    nullSingletonClass_gaussianReal (by norm_num : (1 : ℝ≥0) ≠ 0)
  unfold cGauss
  apply (integral_pos_iff_support_of_nonneg (fun z => abs_nonneg z) hi).mpr
  have he : Function.support (fun z : ℝ => |z|) = ({0} : Set ℝ)ᶜ := by
    ext z; simp [Function.support]
  rw [he, measure_compl (measurableSet_singleton 0) (by simp)]
  simp
lemma law_eq_of_all_thresholds (μ ν : Measure H) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (w : Ω) (h : ∀ s, baryDiff μ ν (w,s) = 0) :
    μ.map (fun u : H => wEval w u) = ν.map (fun u : H => wEval w u) := by
  apply real_law_eq_of_ae_thresholds μ ν w
  filter_upwards [] with s
  have he : cGauss * (s / cGauss) = s := by field_simp [c_pos.ne']
  have hh := sub_eq_zero.mp (h (s / cGauss))
  change μ.real {u : H | wEval w u ≤ cGauss * (s / cGauss)} =
    ν.real {u : H | wEval w u ≤ cGauss * (s / cGauss)} at hh
  simpa only [he] using hh

def coeff (L : ℕ) (v : Fin L → ℝ) (n : ℕ) : ℝ := if h : n < L then v ⟨n,h⟩ else 0
def projection (L : ℕ) (v : Fin L → ℝ) (u : H) : ℝ := ∑ i : Fin L, u i * v i
def extend (L K : ℕ) (v : Fin L → ℝ) : Fin K → ℝ := fun i => coeff L v i

@[fun_prop] lemma projection_meas (L : ℕ) (v : Fin L → ℝ) : Measurable (projection L v) := by
  unfold projection
  apply Finset.measurable_sum
  intro i hi
  exact ((continuous_apply i.val).comp lp.uniformContinuous_coe.continuous).measurable.mul_const _

lemma coeff_sum (L K : ℕ) (hLK : L ≤ K) (v : Fin L → ℝ) (u : H) :
    ∑ n ∈ Finset.range K, u n * coeff L v n = projection L v u := by
  have he : ∑ n ∈ Finset.range L, u n * coeff L v n =
      ∑ n ∈ Finset.range K, u n * coeff L v n := by
    apply Finset.sum_subset (Finset.range_mono hLK)
    intro n hn hnL
    simp [coeff, show ¬ n < L by simpa using hnL]
  rw [← he]
  unfold projection
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  simp [coeff, i.isLt]

lemma eval_limit (L : ℕ) (v : Fin L → ℝ) (w : Ω) (u : H) (hu : Converges w u) :
    Tendsto (fun N => wEval (splice (N+L) (extend L (N+L) v) w) u)
      atTop (𝓝 (projection L v u)) := by
  obtain ⟨a,ha⟩ := hu
  have ha' : Tendsto (S w u) atTop (𝓝 (wEval w u)) := by
    change Tendsto (S w u) atTop (𝓝 (limsup (S w u) atTop))
    rw [ha.limsup_eq]
    exact ha
  have he (N : ℕ) : wEval (splice (N+L) (extend L (N+L) v) w) u =
      projection L v u + wEval w u - S w u (N+L) := by
    rw [eval_splice _ _ w u ⟨a,ha⟩]
    have hd : (∑ n ∈ Finset.range (N+L), u n *
        (splice (N+L) (extend L (N+L) v) w n - w n)) =
        projection L v u - S w u (N+L) := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib]
      have hh : (∑ n ∈ Finset.range (N+L), u n * splice (N+L) (extend L (N+L) v) w n) =
          ∑ n ∈ Finset.range (N+L), u n * coeff L v n := by
        apply Finset.sum_congr rfl
        intro n hn
        simp [splice, extend, Finset.mem_range.mp hn]
      rw [hh, coeff_sum L (N+L) (by omega)]
      rfl
    rw [hd]
    ring
  simp_rw [he]
  simpa using (tendsto_const_nhds (x := projection L v u + wEval w u)).sub (ha'.comp (tendsto_add_atTop_nat L))

lemma char_limit (μ : Measure H) [IsFiniteMeasure μ] (L : ℕ) (v : Fin L → ℝ)
    (w : Ω) (hw : ∀ᵐ (u : H) ∂μ, Converges w u) (t : ℝ) :
    Tendsto (fun N => charFun (μ.map (fun u : H => wEval (splice (N+L) (extend L (N+L) v) w) u)) t)
      atTop (𝓝 (charFun (μ.map (projection L v)) t)) := by
  have he (f : H → ℝ) (hf : Measurable f) : charFun (μ.map f) t =
      ∫ u, Complex.exp ((t : ℂ) * (f u : ℂ) * Complex.I) ∂μ := by
    rw [charFun_apply_real, integral_map hf.aemeasurable (by fun_prop)]
  simp_rw [he _ (eval_left_meas _)]
  rw [he _ (projection_meas L v)]
  apply tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
  · intro N
    exact (Complex.measurable_exp.comp (measurable_const.mul
      (eval_left_meas _).complex_ofReal |>.mul_const Complex.I)).aestronglyMeasurable
  · exact integrable_const 1
  · intro N
    filter_upwards [] with u
    simpa only [← Complex.ofReal_mul] using (Complex.norm_exp_ofReal_mul_I (t * wEval (splice (N+L) (extend L (N+L) v) w) u)).le
  · filter_upwards [hw] with u hu
    exact Complex.continuous_exp.continuousAt.tendsto.comp
      ((tendsto_const_nhds.mul (Complex.continuous_ofReal.continuousAt.tendsto.comp
        (eval_limit L v w u hu))).mul tendsto_const_nhds)

lemma finite_laws (μ ν : Measure H) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ K : ℕ, ∀ᵐ w ∂rho, ∀ (v : Fin K → ℝ) (s : ℝ), baryDiff μ ν (splice K v w,s) = 0)
    (L : ℕ) (v : Fin L → ℝ) : μ.map (projection L v) = ν.map (projection L v) := by
  have hg : ∀ᵐ w ∂rho, (∀ K, ∀ (v : Fin K → ℝ) (s : ℝ), baryDiff μ ν (splice K v w,s) = 0) ∧
      (∀ᵐ (u : H) ∂μ, Converges w u) ∧ (∀ᵐ (u : H) ∂ν, Converges w u) := by
    filter_upwards [ae_all_iff.mpr h, ae_converges_under μ, ae_converges_under ν] with w hh hμ hν
    exact ⟨hh,hμ,hν⟩
  obtain ⟨w,hh,hμ,hν⟩ := hg.exists
  apply Measure.ext_of_charFun
  funext t
  have he (N : ℕ) := law_eq_of_all_thresholds μ ν
    (splice (N+L) (extend L (N+L) v) w) (hh (N+L) (extend L (N+L) v))
  exact tendsto_nhds_unique (char_limit μ L v w hμ t)
    ((char_limit ν L v w hν t).congr' (Eventually.of_forall fun N => congrArg (fun M : Measure ℝ => charFun M t) (he N).symm))
end DistCovProj

open DistCov.Hilbert
 theorem solution (μ₁ μ₂ : Measure DistCov.Indep.L2N)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (h₁ : DistCov.Indep.FiniteFirstMoment μ₁) (h₂ : DistCov.Indep.FiniteFirstMoment μ₂)
    (h : ∀ K : ℕ, ∀ᵐ w ∂rho, ∀ (v : Fin K → ℝ) (s : ℝ), baryDiff μ₁ μ₂ (splice K v w, s) = 0) :
    ∀ (L : ℕ) (v : Fin L → ℝ) (s : ℝ),
      μ₁ {u : DistCov.Indep.L2N | ∑ i : Fin L, u i * v i ≤ s} =
      μ₂ {u : DistCov.Indep.L2N | ∑ i : Fin L, u i * v i ≤ s} := by
  intro L v s
  have he := congrArg (fun M : Measure ℝ => M (Iic s)) (DistCovProj.finite_laws μ₁ μ₂ h L v)
  rw [Measure.map_apply (DistCovProj.projection_meas L v) measurableSet_Iic,
    Measure.map_apply (DistCovProj.projection_meas L v) measurableSet_Iic] at he
  exact he
#print axioms solution
