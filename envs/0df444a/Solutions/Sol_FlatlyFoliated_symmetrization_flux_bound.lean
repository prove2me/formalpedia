-- Prove2me | solution 1 for FlatlyFoliated.symmetrization_flux_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T19:07:57.826951+00:00
-- url     : https://prove2.me/submissions/38ca96f2-aa4f-4bab-9fc2-fa8746ae0223

import Theorems.Thm_FlatlyFoliated_orthogonal_spherical_average
import Theorems.Thm_EuclideanSpace_integral_divergence_ball_three
import Theorems.Thm_FlatlyFoliated_identity_82_83
import Mathlib.Analysis.Calculus.ParametricIntegral

open scoped ContDiff Topology
open FlatlyFoliated MeasureTheory Metric Set Filter

namespace SymmetrizationFlux

set_option backward.isDefEq.respectTransparency false

private abbrev L := R3 →L[ℝ] R3
private abbrev K := {A : L // A ∈ closedBall 0 1}
private instance : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : L) 1)

private lemma c_int {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (ν : Measure K) [IsFiniteMeasure ν] {g : K → V} (hg : Continuous g) : Integrable g ν := by
  simpa using hg.continuousOn.integrableOn_compact (μ := ν) isCompact_univ

private noncomputable def dx {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : R3 × L → V) (p : R3 × L) : R3 →L[ℝ] V :=
  (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ R3 L)

private lemma smooth_dx {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {F : R3 × L → V} (hf : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (dx F) :=
  (hf.fderiv_right (m := ∞) le_rfl).clm_comp contDiff_const

private lemma ci {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] (ν : Measure K) [IsFiniteMeasure ν]
    {F : R3 × L → V} (hf : Continuous F) :
    Continuous (fun x => ∫ A : K, F (x, A.1) ∂ν) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have hc : Continuous (fun p : R3 × K => F (p.1, p.2.1)) :=
    hf.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  obtain ⟨C, hC⟩ := ((isCompact_closedBall x 1).prod isCompact_univ).exists_bound_of_continuousOn
    hc.continuousOn
  apply continuousAt_of_dominated (bound := fun _ => C)
  · exact Eventually.of_forall fun y => (hc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [closedBall_mem_nhds x (by norm_num : (0 : ℝ) < 1)] with y hy
    exact Eventually.of_forall fun A => hC (y, A) ⟨hy, mem_univ A⟩
  · exact integrable_const C
  · exact Eventually.of_forall fun A => (hc.comp (continuous_id.prodMk continuous_const)).continuousAt

private lemma deriv_int {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] (ν : Measure K) [IsFiniteMeasure ν]
    {F : R3 × L → V} (hf : ContDiff ℝ ∞ F) (x : R3) :
    HasFDerivAt (fun y => ∫ A : K, F (y, A.1) ∂ν)
      (∫ A : K, dx F (x, A.1) ∂ν) x := by
  have hc : Continuous (fun p : R3 × K => dx F (p.1, p.2.1)) :=
    (smooth_dx hf).continuous.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  obtain ⟨C, hC⟩ := ((isCompact_closedBall x 1).prod isCompact_univ).exists_bound_of_continuousOn
    hc.continuousOn
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := ν) (F := fun y (A : K) => F (y, A.1))
    (s := closedBall x 1) (bound := fun _ => C) (F' := fun y (A : K) => dx F (y, A.1))
    (closedBall_mem_nhds x (by norm_num))
  · exact Eventually.of_forall fun y => (hf.continuous.comp
      (continuous_const.prodMk continuous_subtype_val)).aestronglyMeasurable
  · exact c_int ν (hf.continuous.comp (continuous_const.prodMk continuous_subtype_val))
  · exact (hc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact Eventually.of_forall fun A y hy => hC (y, A) ⟨hy, mem_univ A⟩
  · exact integrable_const C
  · exact Eventually.of_forall fun A y _ =>
      ((hf.differentiable (by simp) (y, A.1)).hasFDerivAt.comp y
        ((hasFDerivAt_id y).prodMk (hasFDerivAt_const A.1 y)))

private lemma smooth_int {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] (ν : Measure K) [IsFiniteMeasure ν]
    {F : R3 × L → V} (hf : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun x => ∫ A : K, F (x, A.1) ∂ν) := by
  apply contDiff_infty.mpr
  intro n
  induction n generalizing V with
  | zero => exact contDiff_zero.mpr (ci ν hf.continuous)
  | succ n ih =>
      apply contDiff_succ_iff_hasFDerivAt.mpr
      exact ⟨_, ih (smooth_dx hf), deriv_int ν hf⟩

private noncomputable abbrev e (i : Fin 3) : R3 := EuclideanSpace.single i 1

private lemma fixed_deriv {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {F : R3 × L → V} (hf : ContDiff ℝ ∞ F) (A : L) (x : R3) :
    HasFDerivAt (fun y => F (y, A)) (dx F (x, A)) x := by
  exact ((hf.differentiable (by simp) (x, A)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).prodMk (hasFDerivAt_const A x)))

private lemma pd_fixed {F : R3 × L → ℝ} (hf : ContDiff ℝ ∞ F) (A : L) (x : R3)
    (i : Fin 3) : pd i (fun y => F (y, A)) x = dx F (x, A) (e i) := by
  rw [pd, (fixed_deriv hf A x).fderiv]

private lemma pd_int (ν : Measure K) [IsFiniteMeasure ν]
    {F : R3 × L → ℝ} (hf : ContDiff ℝ ∞ F) (x : R3) (i : Fin 3) :
    pd i (fun y => ∫ A : K, F (y, A.1) ∂ν) x =
      ∫ A : K, pd i (fun y => F (y, A.1)) x ∂ν := by
  simp_rw [pd_fixed hf]
  rw [pd, (deriv_int ν hf x).fderiv]
  exact ContinuousLinearMap.integral_apply (φ := fun A : K => dx F (x, A.1))
    (c_int ν ((smooth_dx hf).continuous.comp (continuous_const.prodMk continuous_subtype_val))) (e i)

private lemma pd2_int (ν : Measure K) [IsFiniteMeasure ν]
    {F : R3 × L → ℝ} (hf : ContDiff ℝ ∞ F) (x : R3) (i j : Fin 3) :
    pd j (pd i (fun y => ∫ A : K, F (y, A.1) ∂ν)) x =
      ∫ A : K, pd j (pd i (fun y => F (y, A.1))) x ∂ν := by
  have hG : ContDiff ℝ ∞ (fun p => dx F p (e i)) :=
    (smooth_dx hf).clm_apply contDiff_const
  have hp : pd i (fun y => ∫ A : K, F (y, A.1) ∂ν) =
      (fun y => ∫ A : K, dx F (y, A.1) (e i) ∂ν) := by
    funext y
    rw [pd_int ν hf]
    simp_rw [pd_fixed hf]
  rw [hp, pd_int ν hG]
  congr 1
  funext A
  congr 2
  funext y
  exact (pd_fixed hf A.1 y i).symm

private lemma smooth_eval {f : R3 → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun p : R3 × L => f (p.2 p.1)) :=
  hf.comp (contDiff_snd.clm_apply contDiff_fst)

private lemma pd2_linear {f : R3 → ℝ} (hf : ContDiff ℝ ∞ f) (A : L)
    (x : R3) (i j : Fin 3) :
    pd j (pd i (fun y => f (A y))) x =
      (fderiv ℝ (fderiv ℝ f) (A x) (A (e j))) (A (e i)) := by
  have hd := (hf.fderiv_right (m := ∞) le_rfl).differentiable (by simp)
  have hp : pd i (fun y => f (A y)) = (fun y => (fderiv ℝ f (A y)) (A (e i))) := by
    funext y
    exact congrArg (fun B : R3 →L[ℝ] ℝ => B (e i))
      (show fderiv ℝ (fun y => f (A y)) y = (fderiv ℝ f (A y)).comp A from
        (hf.differentiable (by simp) (A y)).hasFDerivAt.comp y A.hasFDerivAt |>.fderiv)
  rw [hp, pd]
  have hh := ((hd (A x)).hasFDerivAt.comp x A.hasFDerivAt).clm_apply
    (hasFDerivAt_const (A (e i)) x)
  have heq := congrArg (fun B : R3 →L[ℝ] ℝ => B (e j)) hh.fderiv
  simpa only [Function.comp_def, add_apply,
    ContinuousLinearMap.comp_apply, zero_apply, add_zero,
    ContinuousLinearMap.flip_apply, map_zero, zero_add] using heq

private lemma expand (x : R3) : (∑ i, x i • e i) = x := by
  ext j
  simp [e, Pi.single_apply, mul_ite]

private lemma pd2_coeff {f : R3 → ℝ} (hf : ContDiff ℝ ∞ f) (A : L)
    (x : R3) (i j : Fin 3) :
    pd j (pd i (fun y => f (A y))) x =
      ∑ a, ∑ b, A (e i) a * A (e j) b * pd b (pd a f) (A x) := by
  rw [pd2_linear hf]
  have hp (a b : Fin 3) : pd b (pd a f) (A x) =
      (fderiv ℝ (fderiv ℝ f) (A x) (e b)) (e a) := by
    simpa using pd2_linear hf (ContinuousLinearMap.id ℝ R3) (A x) a b
  simp_rw [hp]
  conv_lhs => rw [← expand (A (e j)), map_sum]
  simp only [sum_apply, map_smul, smul_apply, smul_eq_mul]
  conv_lhs => arg 2; intro b; rw [← expand (A (e i)), map_sum]
  simp only [map_smul, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

private lemma coeff (T : R3 ≃ₗᵢ[ℝ] R3) (a i : Fin 3) :
    T (e i) a = T.symm (e a) i := by
  simpa only [e, EuclideanSpace.inner_single_right, EuclideanSpace.inner_single_left,
    one_mul, mul_one, starRingEnd_apply, star_trivial] using T.inner_map_eq_flip (e i) (e a)

private lemma rows (T : R3 ≃ₗᵢ[ℝ] R3) (a b : Fin 3) :
    (∑ i, T (e i) a * T (e i) b) = if a = b then 1 else 0 := by
  simp only [coeff T a, coeff T b]
  have hi := T.symm.inner_map_map (e b) (e a)
  change (∑ i, T.symm (e a) i * T.symm (e b) i) = inner ℝ (e b) (e a) at hi
  simpa only [e, EuclideanSpace.inner_single_right, PiLp.single_apply, starRingEnd_apply,
    star_trivial, mul_one, one_mul, eq_comm] using hi

private lemma squares (T : R3 ≃ₗᵢ[ℝ] R3) (v : Fin 3 → ℝ) :
    (∑ i, (∑ a, v a * T (e i) a) ^ 2) = ∑ a, v a ^ 2 := by
  let z : R3 := WithLp.toLp 2 v
  have hc (i : Fin 3) : (∑ a, v a * T (e i) a) = T.symm z i := by
    calc
      _ = inner ℝ z (T (e i)) := by simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, z, mul_comm]
      _ = inner ℝ (T.symm z) (e i) := by
        rw [← T.inner_map_map (T.symm z) (e i), T.apply_symm_apply]
      _ = _ := by simp only [e, EuclideanSpace.inner_single_right, one_mul, starRingEnd_apply, star_trivial]
  simp_rw [hc]
  have hn := congrArg (fun r : ℝ => r ^ 2) (T.symm.norm_map z)
  simpa only [EuclideanSpace.real_norm_sq_eq, z, PiLp.toLp_apply] using hn

private lemma trace_invariant {f : R3 → ℝ} (hf : ContDiff ℝ ∞ f)
    (T : R3 ≃ₗᵢ[ℝ] R3) (x : R3) :
    lap (fun y => f (T y)) x = lap f (T x) := by
  have hp (i j : Fin 3) : pd j (pd i (fun y => f (T y))) x =
      ∑ a, ∑ b, T (e i) a * T (e j) b * pd b (pd a f) (T x) :=
    pd2_coeff hf T.toContinuousLinearEquiv.toContinuousLinearMap x i j
  simp only [lap]
  simp_rw [hp]
  change (∑ i, ∑ a, ∑ b, T (e i) a * T (e i) b * pd b (pd a f) (T x)) = _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, rows]
  simp

private lemma norm_invariant {f : R3 → ℝ} (hf : ContDiff ℝ ∞ f)
    (T : R3 ≃ₗᵢ[ℝ] R3) (x : R3) :
    hessNormSq (fun y => f (T y)) x = hessNormSq f (T x) := by
  have hp (i j : Fin 3) : pd j (pd i (fun y => f (T y))) x =
      ∑ a, ∑ b, T (e i) a * T (e j) b * pd b (pd a f) (T x) :=
    pd2_coeff hf T.toContinuousLinearEquiv.toContinuousLinearMap x i j
  simp only [hessNormSq]
  simp_rw [hp]
  change (∑ i, ∑ j, (∑ a, ∑ b, T (e i) a * T (e j) b * pd b (pd a f) (T x)) ^ 2) = _
  have hm (i j : Fin 3) :
      (∑ a, ∑ b, T (e i) a * T (e j) b * pd b (pd a f) (T x)) =
      ∑ b, (∑ a, T (e i) a * pd b (pd a f) (T x)) * T (e j) b := by
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro a _
    ring
  simp_rw [hm, squares]
  rw [Finset.sum_comm]
  have hm2 (b i : Fin 3) : (∑ a, T (e i) a * pd b (pd a f) (T x)) =
      ∑ a, pd b (pd a f) (T x) * T (e i) a := by congr 1; funext a; ring
  simp_rw [hm2, squares]
  exact Finset.sum_comm

private lemma pd2_fixed {F : R3 × L → ℝ} (hf : ContDiff ℝ ∞ F)
    (A : L) (x : R3) (i j : Fin 3) :
    pd j (pd i (fun y => F (y, A))) x =
      dx (fun p => dx F p (e i)) (x, A) (e j) := by
  have he : pd i (fun y => F (y, A)) = (fun y => dx F (y, A) (e i)) :=
    funext fun y => pd_fixed hf A y i
  rw [he]
  exact pd_fixed ((smooth_dx hf).clm_apply contDiff_const) A x j

private lemma c_pd2 {f : R3 → ℝ} (hf : ContDiff ℝ ∞ f)
    (x : R3) (i j : Fin 3) :
    Continuous (fun A : L => pd j (pd i (fun y => f (A y))) x) := by
  simp_rw [pd2_fixed (smooth_eval hf)]
  exact (((smooth_dx ((smooth_dx (smooth_eval hf)).clm_apply contDiff_const)).clm_apply
    contDiff_const).continuous.comp (continuous_const.prodMk continuous_id))

private lemma c_lap {f : R3 → ℝ} (hf : ContDiff ℝ ∞ f) (x : R3) :
    Continuous (fun A : L => lap (fun y => f (A y)) x) :=
  continuous_finsetSum _ (fun i _ => c_pd2 hf x i i)

private lemma lap_int (ν : Measure K) [IsFiniteMeasure ν]
    {f : R3 → ℝ} (hf : ContDiff ℝ ∞ f) (x : R3) :
    (∫ A : K, lap (fun y => f (A.1 y)) x ∂ν) =
      lap (fun y => ∫ A : K, f (A.1 y) ∂ν) x := by
  simp only [lap]
  exact (integral_finsetSum Finset.univ
    (f := fun i (A : K) => pd i (pd i (fun y => f (A.1 y))) x)
    (fun i _ => c_int ν ((c_pd2 hf x i i).comp continuous_subtype_val))).trans
      (Finset.sum_congr rfl (fun i _ => (pd2_int ν (smooth_eval hf) x i i).symm))


private lemma smooth_pd {u : R3 → ℝ} (hu : ContDiff ℝ ∞ u) (i : Fin 3) :
    ContDiff ℝ ∞ (pd i u) :=
  (hu.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const

private lemma smooth_lap {u : R3 → ℝ} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (lap u) :=
  ContDiff.sum (fun i _ => smooth_pd (smooth_pd hu i) i)

private noncomputable def q (u : R3 → ℝ) (x : R3) : ℝ := lap u x ^ 2 - hessNormSq u x
private noncomputable def mix (u v : R3 → ℝ) (x : R3) : ℝ :=
  lap u x * lap v x - ∑ i, ∑ j, pd j (pd i u) x * pd j (pd i v) x

private lemma smooth_mix {u v : R3 → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) :
    ContDiff ℝ ∞ (mix u v) := by
  exact ((smooth_lap hu).mul (smooth_lap hv)).sub
    (ContDiff.sum fun i _ => ContDiff.sum fun j _ =>
      (smooth_pd (smooth_pd hu i) j).mul (smooth_pd (smooth_pd hv i) j))

private lemma pd_add {u v : R3 → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (i : Fin 3) :
    pd i (u + v) = pd i u + pd i v := by
  ext x
  exact congrArg (fun D : R3 →L[ℝ] ℝ => D (e i))
    ((hu.differentiable (by simp) x).hasFDerivAt.add (hv.differentiable (by simp) x).hasFDerivAt).fderiv

private lemma q_add {u v : R3 → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (x : R3) :
    q (u + v) x = q u x + q v x + 2 * mix u v x := by
  have hp (i j : Fin 3) : pd j (pd i (u + v)) x = pd j (pd i u) x + pd j (pd i v) x := by
    rw [pd_add hu hv, pd_add (smooth_pd hu i) (smooth_pd hv i)]; rfl
  have hl : lap (u + v) x = lap u x + lap v x := by
    simp only [lap, hp, Finset.sum_add_distrib]
  simp only [q, mix, hl, hessNormSq, hp, add_sq, Finset.sum_add_distrib]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  ring

private lemma mix_self (u : R3 → ℝ) (x : R3) : mix u u x = q u x := by
  simp [mix, q, hessNormSq, pow_two]

private lemma mix_invariant {u v : R3 → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (T : R3 ≃ₗᵢ[ℝ] R3) (x : R3) :
    mix (fun y => u (T y)) (fun y => v (T y)) x = mix u v (T x) := by
  have hq {w : R3 → ℝ} (hw : ContDiff ℝ ∞ w) :
      q (fun y => w (T y)) x = q w (T x) := by
    simp only [q, trace_invariant hw T, norm_invariant hw T]
  have hu' : ContDiff ℝ ∞ (fun y => u (T y)) := hu.comp T.contDiff
  have hv' : ContDiff ℝ ∞ (fun y => v (T y)) := hv.comp T.contDiff
  have he := q_add hu' hv' x
  change q (fun y => (u + v) (T y)) x = _ at he
  have h1 := hq (w := u + v) (hu.add hv)
  have h2 := hq hu
  have h3 := hq hv
  rw [h1, h2, h3, q_add hu hv] at he
  linarith

private lemma c_mix_param {u v : R3 → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) :
    Continuous (fun p : K × R3 => mix u (fun y => v (p.1.1 y)) p.2) := by
  have hh (i j : Fin 3) : Continuous
      (fun p : K × R3 => pd j (pd i (fun y => v (p.1.1 y))) p.2) := by
    simp_rw [pd2_fixed (smooth_eval hv)]
    exact (((smooth_dx ((smooth_dx (smooth_eval hv)).clm_apply contDiff_const)).clm_apply
      contDiff_const).continuous.comp (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst)))
  exact (((smooth_lap hu).continuous.comp continuous_snd).mul
    (continuous_finsetSum _ (fun i _ => hh i i))).sub
    (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      (((smooth_pd (smooth_pd hu i) j).continuous.comp continuous_snd).mul (hh i j)))

private lemma mix_average (ν : Measure K) [IsFiniteMeasure ν]
    {u v : R3 → ℝ} (_hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (x : R3) :
    (∫ A : K, mix u (fun y => v (A.1 y)) x ∂ν) =
      mix u (fun y => ∫ A : K, v (A.1 y) ∂ν) x := by
  have hi (i j : Fin 3) : Integrable (fun A : K => pd j (pd i (fun y => v (A.1 y))) x) ν :=
    c_int ν ((c_pd2 hv x i j).comp continuous_subtype_val)
  have hl : Integrable (fun A : K => lap (fun y => v (A.1 y)) x) ν :=
    c_int ν ((c_lap hv x).comp continuous_subtype_val)
  unfold mix
  rw [integral_sub (hl.const_mul _) (integrable_finsetSum _ (fun i _ =>
      integrable_finsetSum _ (fun j _ => (hi i j).const_mul _))), integral_const_mul,
    lap_int ν hv]
  congr 1
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => (hi i j).const_mul _))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => (hi i j).const_mul _)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul, ← pd2_int ν (smooth_eval hv)]

private lemma int_ball_isometry (T : R3 ≃ₗᵢ[ℝ] R3) (S : ℝ) (v : R3 → ℝ) :
    (∫ x in ball (0 : R3) S, v (T x)) = ∫ x in ball (0 : R3) S, v x := by
  have hp : T ⁻¹' ball (0 : R3) S = ball (0 : R3) S := by
    ext x; simp
  have hm := T.measurePreserving.setIntegral_preimage_emb
    T.toHomeomorph.measurableEmbedding v (ball (0 : R3) S)
  rwa [hp] at hm

private lemma int_mix_average {u v : R3 → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hs : IsSphSymm u) (S : ℝ) :
    (∫ x in ball (0 : R3) S, mix u v x) =
      ∫ x in ball (0 : R3) S, mix u (sphSymmetrization v) x := by
  obtain ⟨ν, hν, horth, _, hav⟩ := orthogonal_spherical_average
  let _ := hν
  have he : (fun y => ∫ A : K, v (A.1 y) ∂ν) = sphSymmetrization v := funext (hav v hv.continuous)
  have hi : Integrable (fun p : K × R3 => mix u (fun y => v (p.1.1 y)) p.2)
      (ν.prod (volume.restrict (ball (0 : R3) S))) := by
    have hc := (c_mix_param hu hv).continuousOn.integrableOn_compact
      (μ := ν.prod volume) (isCompact_univ.prod (isCompact_closedBall (0 : R3) S))
    have hi := hc.mono_set (Set.prod_mono (Subset.refl _) ball_subset_closedBall)
    simpa only [IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ] using hi
  calc
    _ = ∫ A : K, (∫ x in ball (0 : R3) S, mix u (fun y => v (A.1 y)) x) ∂ν := by
      have hae : (fun A : K => ∫ x : R3 in ball (0 : R3) S, mix u (fun y => v (A.1 y)) x) =ᵐ[ν]
          (fun _ : K => ∫ x : R3 in ball (0 : R3) S, mix u v x) := by
        filter_upwards [horth] with A hA
        obtain ⟨T, hT⟩ := hA
        have huT : (fun y => u (T y)) = u := funext (hs T)
        have hm (x : R3) : mix u (fun y => v (A.1 y)) x = mix u v (T x) := by
          rw [hT]
          have hh := mix_invariant hu hv T x
          rw [huT] at hh
          exact hh
        simp_rw [hm]
        exact int_ball_isometry T S (mix u v)
      rw [integral_congr_ae hae, integral_const]
      simp
    _ = ∫ x in ball (0 : R3) S, ∫ A : K, mix u (fun y => v (A.1 y)) x ∂ν :=
      integral_integral_swap hi
    _ = _ := by simp_rw [mix_average ν hu hv, he]

private lemma pd_sub {u v : R3 → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (i : Fin 3) :
    pd i (u - v) = pd i u - pd i v := by
  ext x
  exact congrArg (fun D : R3 →L[ℝ] ℝ => D (e i))
    ((hu.differentiable (by simp) x).hasFDerivAt.sub (hv.differentiable (by simp) x).hasFDerivAt).fderiv

private lemma mix_sub {u v w : R3 → ℝ} (_hu : ContDiff ℝ ∞ u)
    (hv : ContDiff ℝ ∞ v) (hw : ContDiff ℝ ∞ w) (x : R3) :
    mix u (v - w) x = mix u v x - mix u w x := by
  have hp (i j : Fin 3) : pd j (pd i (v - w)) x = pd j (pd i v) x - pd j (pd i w) x := by
    rw [pd_sub hv hw, pd_sub (smooth_pd hv i) (smooth_pd hw i)]; rfl
  have hl : lap (v - w) x = lap v x - lap w x := by
    simp only [lap, hp, Finset.sum_sub_distrib]
  simp only [mix, hl, hp, mul_sub, Finset.sum_sub_distrib]
  ring

private lemma q_decompose {u v : R3 → ℝ} (hu : ContDiff ℝ ∞ u)
    (hv : ContDiff ℝ ∞ v) (x : R3) :
    q v x = q u x + q (v - u) x + 2 * mix u (v - u) x := by
  have hv' : ContDiff ℝ ∞ (v - u) := hv.sub hu
  have he : u + (v - u) = v := by ext y; simp
  simpa only [he] using q_add hu hv' x

private lemma int_mix_zero {f : R3 → ℝ} (hf : ContDiff ℝ ∞ f)
    (hs : ContDiff ℝ ∞ (sphSymmetrization f)) (S : ℝ) :
    (∫ x in ball (0 : R3) S, mix (sphSymmetrization f) (f - sphSymmetrization f) x) = 0 := by
  have hrad : IsSphSymm (sphSymmetrization f) := by
    intro T x; simp only [sphSymmetrization, T.norm_map]
  have he := int_mix_average hs hf hrad S
  simp_rw [mix_self] at he
  have hi := (smooth_mix hs hf).continuous.continuousOn.integrableOn_compact (μ := volume)
    (isCompact_closedBall (0 : R3) S)
  have hj := (smooth_mix hs hs).continuous.continuousOn.integrableOn_compact (μ := volume)
    (isCompact_closedBall (0 : R3) S)
  simp_rw [mix_sub hs hf hs]
  rw [integral_sub (hi.mono_set ball_subset_closedBall) (hj.mono_set ball_subset_closedBall)]
  simp_rw [mix_self]
  linarith

private noncomputable def flux (g : R3 → ℝ) (x : R3) : R3 :=
  (InnerProductSpace.toDual ℝ R3).symm
    (lap g x • fderiv ℝ g x - (fderiv ℝ (fderiv ℝ g) x).flip (grad g x))

private lemma grad_dual (g : R3 → ℝ) (x : R3) :
    grad g x = (InnerProductSpace.toDual ℝ R3).symm (fderiv ℝ g x) := by
  ext i
  have hh := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := R3)
    (x := e i) (y := fderiv ℝ g x)
  have hc : ((InnerProductSpace.toDual ℝ R3).symm (fderiv ℝ g x)) i = pd i g x := by
    simpa only [e, EuclideanSpace.inner_single_right, starRingEnd_apply, star_trivial,
      mul_one, one_mul, pd] using hh
  rw [hc]
  simp [grad, Pi.single_apply]

private lemma hess_entry {g : R3 → ℝ} (hg : ContDiff ℝ ∞ g) (x : R3) (i j : Fin 3) :
    pd j (pd i g) x = (fderiv ℝ (fderiv ℝ g) x (e j)) (e i) := by
  simpa using pd2_linear hg (ContinuousLinearMap.id ℝ R3) x i j

private lemma flux_coord {g : R3 → ℝ} (hg : ContDiff ℝ ∞ g) (x : R3) (j : Fin 3) :
    flux g x j = lap g x * pd j g x - ∑ i, pd j (pd i g) x * pd i g x := by
  have hh := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := R3)
    (x := e j) (y := lap g x • fderiv ℝ g x - (fderiv ℝ (fderiv ℝ g) x).flip (grad g x))
  change inner ℝ (flux g x) (e j) = _ at hh
  simp only [e, EuclideanSpace.inner_single_right, starRingEnd_apply, star_trivial,
    one_mul, sub_apply, smul_apply, smul_eq_mul,
    ContinuousLinearMap.flip_apply, grad, map_sum, map_smul, sum_apply] at hh
  rw [hh]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [hess_entry hg]
  dsimp [pd, e]
  ring

private lemma smooth_flux {g : R3 → ℝ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (flux g) := by
  have he : flux g = (fun x => ∑ j : Fin 3,
      (lap g x * pd j g x - ∑ i, pd j (pd i g) x * pd i g x) • e j) := by
    funext x
    conv_lhs => rw [← expand (flux g x)]
    simp_rw [flux_coord hg]
  rw [he]
  exact ContDiff.sum fun j _ => (((smooth_lap hg).mul (smooth_pd hg j)).sub
    (ContDiff.sum fun i _ => (smooth_pd (smooth_pd hg i) j).mul (smooth_pd hg i))).smul contDiff_const

private lemma div_flux {g : R3 → ℝ} (hg : ContDiff ℝ ∞ g) (x : R3) :
    (∑ i : Fin 3, (fderiv ℝ (flux g) x (e i)) i) = q g x := by
  have hh := identity_82_83 0 g hg x
  simp only [mul_zero, zero_mul, zero_div, sub_zero] at hh
  change _ = q g x at hh
  rw [← hh]
  apply Finset.sum_congr rfl
  intro j _
  have hc : (fun y => (flux g y) j) =
      fun y => lap g y * pd j g y - ∑ i, pd j (pd i g) y * pd i g y :=
    funext fun y => flux_coord hg y j
  rw [← hc, pd]
  have hf := ((EuclideanSpace.proj j : R3 →L[ℝ] ℝ).hasFDerivAt.comp x
    ((smooth_flux hg).differentiable (by simp) x).hasFDerivAt).fderiv
  exact congrArg (fun D : R3 →L[ℝ] ℝ => D (e j)) hf.symm

private lemma norm_e (i : Fin 3) : ‖e i‖ = 1 := by simp [e]

private lemma lap_bound {g : R3 → ℝ} (hg : ContDiff ℝ ∞ g) (x : R3) :
    |lap g x| ≤ 3 * ‖fderiv ℝ (fderiv ℝ g) x‖ := by
  calc
    _ ≤ ∑ i : Fin 3, |pd i (pd i g) x| := by
      exact norm_sum_le Finset.univ (fun i => pd i (pd i g) x)
    _ ≤ ∑ i : Fin 3, ‖fderiv ℝ (fderiv ℝ g) x‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [hess_entry hg]
      have hh := (fderiv ℝ (fderiv ℝ g) x).le_opNorm₂ (e i) (e i)
      simpa only [norm_e, mul_one, Real.norm_eq_abs] using hh
    _ = _ := by simp

private lemma flux_bound {g : R3 → ℝ} (hg : ContDiff ℝ ∞ g) (x : R3) :
    ‖flux g x‖ ≤ 4 * (‖fderiv ℝ (fderiv ℝ g) x‖ * ‖fderiv ℝ g x‖) := by
  rw [flux, LinearIsometryEquiv.norm_map]
  have hn : ‖grad g x‖ = ‖fderiv ℝ g x‖ := by rw [grad_dual, LinearIsometryEquiv.norm_map]
  calc
    _ ≤ ‖lap g x • fderiv ℝ g x‖ + ‖(fderiv ℝ (fderiv ℝ g) x).flip (grad g x)‖ := norm_sub_le _ _
    _ ≤ |lap g x| * ‖fderiv ℝ g x‖ + ‖fderiv ℝ (fderiv ℝ g) x‖ * ‖fderiv ℝ g x‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      exact add_le_add_right (by simpa only [ContinuousLinearMap.opNorm_flip, hn] using
        (ContinuousLinearMap.le_opNorm (fderiv ℝ (fderiv ℝ g) x).flip (grad g x))) _
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right (lap_bound hg x) (norm_nonneg (fderiv ℝ g x))]

private lemma smooth_average {f : R3 → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (sphSymmetrization f) := by
  obtain ⟨ν, hν, _, _, hav⟩ := orthogonal_spherical_average
  let _ := hν
  have he : (fun y => ∫ A : K, f (A.1 y) ∂ν) = sphSymmetrization f := funext (hav f hf.continuous)
  rw [← he]
  exact smooth_int ν (smooth_eval hf)

private lemma smooth_q {u : R3 → ℝ} (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (q u) := by
  have he : q u = mix u u := funext fun x => (mix_self u x).symm
  rw [he]; exact smooth_mix hu hu

private lemma int_q_difference (Λ : ℝ) {f : R3 → ℝ} (hf : ContDiff ℝ ∞ f)
    (heq : ∀ x, q f x = 2 * Λ) (S : ℝ) :
    (∫ x in ball (0 : R3) S, q (sphSymmetrization f) x - 2 * Λ) =
      -(∫ x in ball (0 : R3) S, q (f - sphSymmetrization f) x) := by
  have hs := smooth_average hf
  have hg : ContDiff ℝ ∞ (f - sphSymmetrization f) := hf.sub hs
  have hpt (x : R3) : q (sphSymmetrization f) x - 2 * Λ =
      -q (f - sphSymmetrization f) x - 2 * mix (sphSymmetrization f) (f - sphSymmetrization f) x := by
    have hh := q_decompose hs hf x
    rw [heq x] at hh
    linarith
  have hi := (smooth_q hg).continuous.continuousOn.integrableOn_compact (μ := volume)
    (isCompact_closedBall (0 : R3) S)
  have hj := (smooth_mix hs hg).continuous.continuousOn.integrableOn_compact (μ := volume)
    (isCompact_closedBall (0 : R3) S)
  simp_rw [hpt]
  rw [integral_sub (f := fun x => -q (f - sphSymmetrization f) x)
    (g := fun x => 2 * mix (sphSymmetrization f) (f - sphSymmetrization f) x)
    ((hi.mono_set ball_subset_closedBall).neg)
    ((hj.mono_set ball_subset_closedBall).const_mul 2), integral_neg, integral_const_mul,
    int_mix_zero hf hs]
  ring

private lemma int_q_bound {g : R3 → ℝ} (hg : ContDiff ℝ ∞ g) {S δ : ℝ} (hS : 0 < S)
    (hb : ∀ x : R3, ‖x‖ = S →
      S ^ 2 * (‖fderiv ℝ (fderiv ℝ g) x‖ * ‖fderiv ℝ g x‖) ≤ δ) :
    |∫ x in ball (0 : R3) S, q g x| ≤
      4 * δ * (volume : Measure R3).toSphere.real univ := by
  let σ := (volume : Measure R3).toSphere
  have hd := EuclideanSpace.integral_divergence_ball_three (flux g) ((smooth_flux hg).of_le (by simp)) S hS
  simp_rw [show (fun x : R3 => ∑ i : Fin 3, (fderiv ℝ (flux g) x (e i)) i) = q g from funext (div_flux hg)] at hd
  have hsc : Continuous (fun u : sphere (0 : R3) 1 => S • (u.1 : R3)) :=
    (S • ContinuousLinearMap.id ℝ R3).continuous.comp continuous_subtype_val
  have hfc : Continuous (fun u : sphere (0 : R3) 1 => flux g (S • u.1)) :=
    (smooth_flux hg).continuous.comp hsc
  have hc : Continuous (fun u : sphere (0 : R3) 1 => inner ℝ (flux g (S • u.1)) u.1) :=
    hfc.inner continuous_subtype_val
  have hi := hc.continuousOn.integrableOn_compact (μ := σ) isCompact_univ
  have hi' : Integrable (fun u : sphere (0 : R3) 1 =>
      |S ^ 2 * inner ℝ (flux g (S • u.1)) u.1|) σ := by
    simpa only [Real.norm_eq_abs, Measure.restrict_univ] using (hi.const_mul (S ^ 2)).norm
  have hp (u : sphere (0 : R3) 1) :
      |S ^ 2 * inner ℝ (flux g (S • u.1)) u.1| ≤ 4 * δ := by
    have hu : ‖u.1‖ = 1 := mem_sphere_zero_iff_norm.mp u.2
    have hn : ‖S • u.1‖ = S := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hS, hu, mul_one]
    calc
      _ = S ^ 2 * |inner ℝ (flux g (S • u.1)) u.1| := by rw [abs_mul, abs_of_nonneg (sq_nonneg S)]
      _ ≤ S ^ 2 * ‖flux g (S • u.1)‖ := mul_le_mul_of_nonneg_left
        (by simpa [hu] using abs_real_inner_le_norm (flux g (S • u.1)) u.1) (sq_nonneg S)
      _ ≤ S ^ 2 * (4 * (‖fderiv ℝ (fderiv ℝ g) (S • u.1)‖ * ‖fderiv ℝ g (S • u.1)‖)) :=
        mul_le_mul_of_nonneg_left (flux_bound hg _) (sq_nonneg S)
      _ ≤ _ := by nlinarith [hb (S • u.1) hn]
  change (∫ x in ball (0 : R3) S, q g x) = _ at hd
  rw [hd, ← integral_const_mul]
  calc
    _ ≤ ∫ u : sphere (0 : R3) 1, |S ^ 2 * inner ℝ (flux g (S • u.1)) u.1| ∂σ :=
      by simpa only [Real.norm_eq_abs] using (norm_integral_le_integral_norm (μ := σ)
        (fun u : sphere (0 : R3) 1 => S ^ 2 * inner ℝ (flux g (S • u.1)) u.1))
    _ ≤ ∫ _ : sphere (0 : R3) 1, 4 * δ ∂σ := integral_mono hi' (integrable_const _) hp
    _ = _ := by rw [integral_const]; simp only [smul_eq_mul, mul_comm]; rfl

end SymmetrizationFlux

open SymmetrizationFlux

theorem solution (Λ : ℝ) (f : R3 → ℝ)
    (hf : ContDiff ℝ ∞ f) (happrox : FlatlyFoliated.ApproxSphSymmAtInfty f)
    (heq : ∀ x, FlatlyFoliated.lap f x ^ 2 - FlatlyFoliated.hessNormSq f x = 2 * Λ) :
    ContDiff ℝ ∞ (FlatlyFoliated.sphSymmetrization f) ∧
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∀ S : ℝ, R ≤ S →
      (∫ x in ball (0 : FlatlyFoliated.R3) S,
        (FlatlyFoliated.lap (FlatlyFoliated.sphSymmetrization f) x ^ 2 -
          FlatlyFoliated.hessNormSq (FlatlyFoliated.sphSymmetrization f) x - 2 * Λ)) ≤ ε := by
  have hs := smooth_average hf
  refine ⟨hs, ?_⟩
  intro ε hε
  let M := (volume : Measure R3).toSphere.real univ
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  let δ := ε / (4 * M + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδε : 4 * δ * M ≤ ε := by
    have hh : δ * (4 * M + 1) = ε := div_mul_cancel₀ ε (by positivity)
    nlinarith
  obtain ⟨R₀, hR₀⟩ := happrox.2 δ hδ
  refine ⟨max 1 R₀, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro S hS
  have hSpos : 0 < S := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hS)
  have hb : ∀ x : R3, ‖x‖ = S → S ^ 2 *
      (‖fderiv ℝ (fderiv ℝ (f - sphSymmetrization f)) x‖ *
        ‖fderiv ℝ (f - sphSymmetrization f) x‖) ≤ δ := by
    intro x hx
    have hh := hR₀ x ((le_max_right _ _).trans hS |>.trans_eq hx.symm)
    change ‖x‖ ^ 2 * (‖fderiv ℝ (fderiv ℝ (f - sphSymmetrization f)) x‖ *
      ‖fderiv ℝ (f - sphSymmetrization f) x‖) ≤ δ at hh
    simpa only [hx] using hh
  change (∫ x in ball (0 : R3) S, q (sphSymmetrization f) x - 2 * Λ) ≤ ε
  rw [int_q_difference Λ hf heq S]
  exact (neg_le_abs _).trans ((int_q_bound (hf.sub hs) hSpos hb).trans hδε)
