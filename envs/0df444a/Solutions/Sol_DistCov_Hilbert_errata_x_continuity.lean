-- Prove2me | solution 1 for DistCov.Hilbert.errata_x_continuity
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T20:09:51.060648+00:00
-- url     : https://prove2.me/submissions/cba3303f-d2e2-4f36-aadf-f658eb7ca39d

import Theorems.Thm_DistCov_Hilbert_gaussian_series

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace MeasureTheory.Measure
open scoped Topology NNReal
namespace DistCovErrata
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

lemma ae_eval_splice_all (μ : Measure H) [SFinite μ] (K : ℕ) :
    ∀ᵐ w ∂rho, ∀ᵐ (u : H) ∂μ, ∀ v : Fin K → ℝ,
      wEval (splice K v w) u = wEval w u +
        ∑ n ∈ Finset.range K, u n * (splice K v w n - w n) := by
  filter_upwards [ae_converges_under μ] with w hw
  exact hw.mono fun u hu v => eval_splice K v w u hu

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



def head (K : ℕ) (w : Ω) : Fin K → ℝ := fun i => w i

def γ (K : ℕ) : Measure (Fin K → ℝ) := Measure.pi (fun _ => gaussianReal 0 1)

lemma head_preserving (K : ℕ) : MeasurePreserving (head K) rho (γ K) := by
  refine ⟨by unfold head; fun_prop, ?_⟩
  unfold rho γ head
  rw [Measure.map_infinitePi_infinitePi_of_inj (fun i j h => Fin.ext h),
    Measure.infinitePi_eq_pi]

local instance (K : ℕ) : IsOpenPosMeasure (γ K) := by
  let : IsOpenPosMeasure (gaussianReal 0 1) :=
    (gaussianReal_absolutelyContinuous' 0 (by norm_num : (1 : ℝ≥0) ≠ 0)).isOpenPosMeasure
  unfold γ
  infer_instance

lemma mix_preserving (K : ℕ) :
    MeasurePreserving (fun q : Ω × Ω => splice K (head K q.1) q.2) (rho.prod rho) rho := by
  let e : (Ω × Ω) ≃ᵐ (Fin 2 → Ω) := MeasurableEquiv.finTwoArrow.symm
  have he : (rho.prod rho).map e = Measure.infinitePi (fun _ : Fin 2 => rho) := by
    rw [Measure.infinitePi_eq_pi]
    exact (MeasurePreserving.symm MeasurableEquiv.finTwoArrow (measurePreserving_finTwoArrow rho)).map_eq
  let c : (Fin 2 → Ω) ≃ᵐ (Fin 2 × ℕ → ℝ) := (MeasurableEquiv.curry (Fin 2) ℕ ℝ).symm
  have hc : ((rho.prod rho).map e).map c =
      Measure.infinitePi (fun _ : Fin 2 × ℕ => gaussianReal 0 1) := by
    rw [he]
    exact Measure.infinitePi_map_curry_symm (fun (_ : Fin 2) (_ : ℕ) => gaussianReal 0 1)
  let k : ℕ → Fin 2 × ℕ := fun n => (if n < K then 0 else 1, n)
  have hk : Function.Injective k := by intro i j h; exact congrArg Prod.snd h
  have hm : Measurable (fun q : Ω × Ω => splice K (head K q.1) q.2) := by
    unfold splice head
    apply measurable_pi_lambda
    intro n
    split_ifs <;> fun_prop
  refine ⟨hm, ?_⟩
  have hp := Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : Fin 2 × ℕ => gaussianReal 0 1) hk
  have hfun : (fun q : Ω × Ω => splice K (head K q.1) q.2) =
      ((fun z : Fin 2 × ℕ → ℝ => fun n => z (k n)) ∘ c) ∘ e := by
    funext q n
    dsimp [splice, head, k, c, e, MeasurableEquiv.curry]
    split_ifs <;> rfl
  rw [hfun]
  rw [← Measure.map_map
    (g := (fun z : Fin 2 × ℕ → ℝ => fun n => z (k n)) ∘ c)
    (f := e) (by fun_prop) e.measurable]
  rw [← Measure.map_map (g := fun z : Fin 2 × ℕ → ℝ => fun n => z (k n))
    (f := c) (by fun_prop) c.measurable, hc]
  exact hp

lemma scaled_threshold (w : Ω) (s : ℝ) :
    {u : H | wEval w u / cGauss ≤ s} = {u : H | wEval w u ≤ cGauss * s} := by
  ext u
  simp only [mem_ofPred_eq, div_le_iff₀ c_pos]
  rw [mul_comm s cGauss]

lemma all_thresholds_of_ae (μ ν : Measure H) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (w : Ω) (h : ∀ᵐ s ∂volume, baryDiff μ ν (w,s) = 0) :
    ∀ s : ℝ, baryDiff μ ν (w,s) = 0 := by
  let e : H → ℝ := fun u => wEval w u / cGauss
  have hm : Measurable e := (eval_left_meas w).div_const cGauss
  let : IsProbabilityMeasure (μ.map e) := isProbabilityMeasure_map hm.aemeasurable
  let : IsProbabilityMeasure (ν.map e) := isProbabilityMeasure_map hm.aemeasurable
  have hc : cdf (μ.map e) = cdf (ν.map e) := by
    apply stieltjes_eq_of_ae
    filter_upwards [h] with s hs
    simp only [cdf_eq_real]
    rw [map_measureReal_apply (μ := μ) hm measurableSet_Iic,
      map_measureReal_apply (μ := ν) hm measurableSet_Iic]
    change μ.real {u : H | wEval w u / cGauss ≤ s} =
      ν.real {u : H | wEval w u / cGauss ≤ s}
    rw [scaled_threshold]
    exact sub_eq_zero.mp hs
  have he := Measure.eq_of_cdf (μ.map e) (ν.map e) hc
  intro s
  have hs := congrArg (fun M : Measure ℝ => M.real (Iic s)) he
  rw [map_measureReal_apply (μ := μ) hm measurableSet_Iic,
    map_measureReal_apply (μ := ν) hm measurableSet_Iic] at hs
  change μ.real {u : H | wEval w u / cGauss ≤ s} =
    ν.real {u : H | wEval w u / cGauss ≤ s} at hs
  rw [scaled_threshold] at hs
  exact sub_eq_zero.mpr hs

lemma ae_all_thresholds (μ ν : Measure H) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (h : baryDiff μ ν =ᵐ[rho.prod volume] 0) :
    ∀ᵐ w ∂rho, ∀ s : ℝ, baryDiff μ ν (w,s) = 0 := by
  filter_upwards [ae_ae_of_ae_prod h] with w hw
  exact all_thresholds_of_ae μ ν w hw

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

lemma all_thresholds_of_law_eq (μ ν : Measure H) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (w : Ω)
    (h : μ.map (fun u : H => wEval w u) = ν.map (fun u : H => wEval w u)) :
    ∀ s, baryDiff μ ν (w,s) = 0 := by
  intro s
  have he := congrArg (fun M : Measure ℝ => M.real (Iic (cGauss * s))) h
  rw [map_measureReal_apply (μ := μ) (eval_left_meas w) measurableSet_Iic,
    map_measureReal_apply (μ := ν) (eval_left_meas w) measurableSet_Iic] at he
  exact sub_eq_zero.mpr he


def delta (K : ℕ) (v : Fin K → ℝ) (w : Ω) (u : H) : ℝ :=
  ∑ n ∈ Finset.range K, u n * (splice K v w n - w n)

@[fun_prop] lemma delta_left_meas (K : ℕ) (v : Fin K → ℝ) (w : Ω) :
    Measurable (fun u : H => delta K v w u) := by
  unfold delta
  apply Finset.measurable_sum
  intro n hn
  have hc : Continuous (fun u : H => u n) :=
    (continuous_apply n).comp lp.uniformContinuous_coe.continuous
  exact hc.measurable.mul_const _

@[fun_prop] lemma delta_right_cont (K : ℕ) (w : Ω) (u : H) :
    Continuous (fun v : Fin K → ℝ => delta K v w u) := by
  unfold delta
  apply continuous_finsetSum
  intro n hn
  unfold splice
  split_ifs <;> fun_prop

def phi (μ : Measure H) (K : ℕ) (w : Ω) (v : Fin K → ℝ) (t : ℝ) : ℂ :=
  ∫ u, Complex.exp ((t : ℂ) * ((wEval w u + delta K v w u : ℝ) : ℂ) * Complex.I) ∂μ

lemma phi_cont (μ : Measure H) [IsFiniteMeasure μ] (K : ℕ) (w : Ω) (t : ℝ) :
    Continuous (fun v => phi μ K w v t) := by
  unfold phi
  apply continuous_of_dominated (bound := fun _ => (1 : ℝ))
  · intro v
    exact (Complex.measurable_exp.comp (measurable_const.mul
      ((eval_left_meas w).add (delta_left_meas K v w)).complex_ofReal |>.mul_const Complex.I)).aestronglyMeasurable
  · intro v
    filter_upwards [] with u
    simpa only [← Complex.ofReal_mul] using
      (Complex.norm_exp_ofReal_mul_I (t * (wEval w u + delta K v w u))).le
  · exact integrable_const 1
  · filter_upwards [] with u
    have hd := delta_right_cont K w u
    fun_prop

lemma phi_eq_char (μ : Measure H) [IsFiniteMeasure μ] (K : ℕ) (w : Ω)
    (hw : ∀ᵐ u ∂μ, Converges w u) (v : Fin K → ℝ) (t : ℝ) :
    phi μ K w v t = charFun (μ.map (fun u : H => wEval (splice K v w) u)) t := by
  rw [charFun_apply_real, integral_map (eval_left_meas (splice K v w)).aemeasurable (by fun_prop)]
  unfold phi
  apply integral_congr_ae
  filter_upwards [hw] with u hu
  rw [eval_splice K v w u hu]
  rfl

lemma replacements_of_ae (μ ν : Measure H) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (K : ℕ) (w : Ω) (hμ : ∀ᵐ u ∂μ, Converges w u) (hν : ∀ᵐ u ∂ν, Converges w u)
    (h : ∀ᵐ w' ∂rho, ∀ s : ℝ, baryDiff μ ν (splice K (head K w') w,s) = 0) :
    ∀ v : Fin K → ℝ, ∀ s : ℝ, baryDiff μ ν (splice K v w,s) = 0 := by
  have hphi (t : ℝ) : ∀ v : Fin K → ℝ, phi μ K w v t = phi ν K w v t := by
    have he : (fun w' => phi μ K w (head K w') t) =ᵐ[rho]
        (fun w' => phi ν K w (head K w') t) := by
      filter_upwards [h] with w' hw'
      rw [phi_eq_char μ K w hμ, phi_eq_char ν K w hν,
        law_eq_of_all_thresholds μ ν (splice K (head K w') w) hw']
    have hγ : (fun v => phi μ K w v t) =ᵐ[γ K] (fun v => phi ν K w v t) := by
      rw [← (head_preserving K).map_eq]
      apply (ae_map_iff (head_preserving K).aemeasurable
        (measurableSet_eq_fun (phi_cont μ K w t).measurable (phi_cont ν K w t).measurable)).mpr
      exact he
    exact fun v => congrFun (eq_of_ae_eq hγ (phi_cont μ K w t) (phi_cont ν K w t)) v
  intro v
  apply all_thresholds_of_law_eq
  apply Measure.ext_of_charFun
  funext t
  rw [← phi_eq_char μ K w hμ, ← phi_eq_char ν K w hν]
  exact hphi t v

lemma all_replacements (μ ν : Measure H) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (K : ℕ) (h : baryDiff μ ν =ᵐ[rho.prod volume] 0) :
    ∀ᵐ w ∂rho, ∀ (v : Fin K → ℝ) (s : ℝ), baryDiff μ ν (splice K v w,s) = 0 := by
  have hmix := (mix_preserving K).quasiMeasurePreserving.ae (ae_all_thresholds μ ν h)
  have hswap := (measurePreserving_swap (μ := rho) (ν := rho)).quasiMeasurePreserving.ae hmix
  filter_upwards [ae_ae_of_ae_prod hswap, ae_converges_under μ, ae_converges_under ν] with w hh hμ hν
  exact replacements_of_ae μ ν K w hμ hν hh

end DistCovErrata
#print axioms DistCovErrata.ae_eval_splice_all
#print axioms DistCovErrata.real_law_eq_of_ae_thresholds

open DistCov.Hilbert

theorem solution (μ₁ μ₂ : Measure DistCov.Indep.L2N) [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] (_h₁ : DistCov.Indep.FiniteFirstMoment μ₁)
    (_h₂ : DistCov.Indep.FiniteFirstMoment μ₂) (K : ℕ)
    (h : baryDiff μ₁ μ₂ =ᵐ[rho.prod volume] 0) :
    ∀ᵐ w ∂rho, ∀ (v : Fin K → ℝ) (s : ℝ), baryDiff μ₁ μ₂ (splice K v w,s) = 0 :=
  DistCovErrata.all_replacements μ₁ μ₂ K h

#print axioms solution
