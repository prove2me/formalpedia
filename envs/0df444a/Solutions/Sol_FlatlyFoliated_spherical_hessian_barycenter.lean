-- Prove2me | solution 1 for FlatlyFoliated.spherical_hessian_barycenter
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T18:40:45.662038+00:00
-- url     : https://prove2.me/submissions/d03f39f0-7fb7-4671-b7f4-1b52fbfe9055

import Theorems.Thm_FlatlyFoliated_orthogonal_spherical_average
import Mathlib.Analysis.Calculus.ParametricIntegral

open scoped ContDiff Topology
open FlatlyFoliated MeasureTheory Metric Set Filter

namespace HessianBarycenter

set_option backward.isDefEq.respectTransparency false
attribute [local instance] PiLp.normedAddCommGroup PiLp.normedSpace

private abbrev L := R3 →L[ℝ] R3
private abbrev K := {A : L // A ∈ closedBall 0 1}
private abbrev H := EuclideanSpace ℝ (Fin 3 × Fin 3)
private abbrev J := ℝ × H
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

private noncomputable def hess (f : R3 → ℝ) (x : R3) : H :=
  WithLp.toLp 2 (fun ij => pd ij.2 (pd ij.1 f) x)

private lemma hess_norm (f : R3 → ℝ) (x : R3) : ‖hess f x‖ ^ 2 = hessNormSq f x := by
  simp [EuclideanSpace.real_norm_sq_eq, hess, hessNormSq, Fintype.sum_prod_type]

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

private lemma c_hess {f : R3 → ℝ} (hf : ContDiff ℝ ∞ f) (x : R3) :
    Continuous (fun A : L => hess (fun y => f (A y)) x) := by
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi (fun ij => c_pd2 hf x ij.1 ij.2))

private lemma c_lap {f : R3 → ℝ} (hf : ContDiff ℝ ∞ f) (x : R3) :
    Continuous (fun A : L => lap (fun y => f (A y)) x) :=
  continuous_finsetSum _ (fun i _ => c_pd2 hf x i i)

private lemma hess_int (ν : Measure K) [IsFiniteMeasure ν]
    {f : R3 → ℝ} (hf : ContDiff ℝ ∞ f) (x : R3) :
    (∫ A : K, hess (fun y => f (A.1 y)) x ∂ν) =
      hess (fun y => ∫ A : K, f (A.1 y) ∂ν) x := by
  have hh : Integrable (fun A : K => hess (fun y => f (A.1 y)) x) ν :=
    c_int ν ((c_hess hf x).comp continuous_subtype_val)
  ext ij
  have he := (EuclideanSpace.proj ij : H →L[ℝ] ℝ).integral_comp_comm hh
  change (∫ A : K, hess (fun y => f (A.1 y)) x ∂ν) ij = _
  calc
    _ = ∫ A : K, (hess (fun y => f (A.1 y)) x) ij ∂ν := he.symm
    _ = _ := (pd2_int ν (smooth_eval hf) x ij.1 ij.2).symm

private lemma lap_int (ν : Measure K) [IsFiniteMeasure ν]
    {f : R3 → ℝ} (hf : ContDiff ℝ ∞ f) (x : R3) :
    (∫ A : K, lap (fun y => f (A.1 y)) x ∂ν) =
      lap (fun y => ∫ A : K, f (A.1 y) ∂ν) x := by
  simp only [lap]
  exact (integral_finsetSum Finset.univ
    (f := fun i (A : K) => pd i (pd i (fun y => f (A.1 y))) x)
    (fun i _ => c_int ν ((c_pd2 hf x i i).comp continuous_subtype_val))).trans
      (Finset.sum_congr rfl (fun i _ => (pd2_int ν (smooth_eval hf) x i i).symm))

private lemma smooth_pd {f : R3 → ℝ} (hf : ContDiff ℝ ∞ f) (i : Fin 3) :
    ContDiff ℝ ∞ (pd i f) :=
  (hf.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const

private lemma jet_sphere_measurable {f : R3 → ℝ} (hf : ContDiff ℝ ∞ f) (x : R3) :
    MeasurableSet {p : J | ∃ y : R3, ‖y‖ = ‖x‖ ∧
      p.1 = lap f y ∧ ‖p.2‖ ^ 2 = hessNormSq f y} := by
  have hl : Continuous (lap f) :=
    continuous_finsetSum _ (fun i _ => (smooth_pd (smooth_pd hf i) i).continuous)
  have hh : Continuous (hessNormSq f) :=
    continuous_finsetSum _ (fun i _ => continuous_finsetSum _
      (fun j _ => ((smooth_pd (smooth_pd hf i) j).continuous).pow 2))
  let q : R3 → ℝ × ℝ := fun y => (lap f y, hessNormSq f y)
  have hq : Continuous q := hl.prodMk hh
  have he : {p : J | ∃ y : R3, ‖y‖ = ‖x‖ ∧
      p.1 = lap f y ∧ ‖p.2‖ ^ 2 = hessNormSq f y} =
      (fun p : J => (p.1, ‖p.2‖ ^ 2)) ⁻¹' (q '' sphere (0 : R3) ‖x‖) := by
    ext p
    constructor
    · rintro ⟨y, hy, ht, hh⟩
      exact ⟨y, by simpa using hy, Prod.ext ht.symm hh.symm⟩
    · rintro ⟨y, hy, he⟩
      exact ⟨y, by simpa using hy, (congrArg Prod.fst he).symm, (congrArg Prod.snd he).symm⟩
  rw [he]
  exact (((isCompact_sphere (0 : R3) ‖x‖).image hq).isClosed.preimage
    (continuous_fst.prodMk (continuous_snd.norm.pow 2))).measurableSet

end HessianBarycenter

open HessianBarycenter

theorem solution (f : FlatlyFoliated.R3 → ℝ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (FlatlyFoliated.sphSymmetrization f) ∧
    ∀ x : FlatlyFoliated.R3,
      ∃ μ : Measure (ℝ × EuclideanSpace ℝ (Fin 3 × Fin 3)),
        IsProbabilityMeasure μ ∧
        Integrable (fun p => p.1) μ ∧ Integrable (fun p => p.2) μ ∧
        (∫ p, p.1 ∂μ) = FlatlyFoliated.lap (FlatlyFoliated.sphSymmetrization f) x ∧
        (∫ p, p.2 ∂μ) = WithLp.toLp 2
          (fun ij : Fin 3 × Fin 3 => FlatlyFoliated.pd ij.2
            (FlatlyFoliated.pd ij.1 (FlatlyFoliated.sphSymmetrization f)) x) ∧
        (∀ᵐ p ∂μ, ∃ y : FlatlyFoliated.R3, ‖y‖ = ‖x‖ ∧
          p.1 = FlatlyFoliated.lap f y ∧ ‖p.2‖ ^ 2 = FlatlyFoliated.hessNormSq f y) ∧
        (FlatlyFoliated.lap f x, WithLp.toLp 2
          (fun ij : Fin 3 × Fin 3 => FlatlyFoliated.pd ij.2 (FlatlyFoliated.pd ij.1 f) x))
            ∈ μ.support := by
  obtain ⟨ν, hν, horth, hid, havg⟩ := FlatlyFoliated.orthogonal_spherical_average
  let := hν
  have heq : (fun y => ∫ A : K, f (A.1 y) ∂ν) = sphSymmetrization f :=
    funext (havg f hf.continuous)
  refine ⟨?_, ?_⟩
  · rw [← heq]
    exact smooth_int ν (smooth_eval hf)
  intro x
  let jet : K → J := fun A => (lap (fun y => f (A.1 y)) x, hess (fun y => f (A.1 y)) x)
  have hj : Continuous jet :=
    ((c_lap hf x).comp continuous_subtype_val).prodMk ((c_hess hf x).comp continuous_subtype_val)
  have hli : Integrable (fun A : K => (jet A).1) ν :=
    c_int ν (continuous_fst.comp hj)
  have hhi : Integrable (fun A : K => (jet A).2) ν :=
    c_int ν (continuous_snd.comp hj)
  let μ := ν.map jet
  have hprob : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map hj.aemeasurable
  have hfst : Integrable (fun p : J => p.1) μ :=
    (integrable_map_measure continuous_fst.aestronglyMeasurable hj.aemeasurable).mpr hli
  have hsnd : Integrable (fun p : J => p.2) μ :=
    (integrable_map_measure continuous_snd.aestronglyMeasurable hj.aemeasurable).mpr hhi
  refine ⟨μ, hprob, hfst, hsnd, ?_, ?_, ?_, ?_⟩
  · rw [integral_map hj.aemeasurable continuous_fst.aestronglyMeasurable]
    change (∫ A : K, lap (fun y => f (A.1 y)) x ∂ν) = _
    rw [lap_int ν hf, heq]
  · rw [integral_map hj.aemeasurable continuous_snd.aestronglyMeasurable]
    change (∫ A : K, hess (fun y => f (A.1 y)) x ∂ν) = _
    rw [hess_int ν hf, heq]
    rfl
  · apply (ae_map_iff hj.aemeasurable (jet_sphere_measurable hf x)).mpr
    filter_upwards [horth] with A hA
    obtain ⟨T, hT⟩ := hA
    refine ⟨T x, T.norm_map x, ?_, ?_⟩
    · change lap (fun y => f (A.1 y)) x = _
      rw [hT]
      exact trace_invariant hf T x
    · change ‖hess (fun y => f (A.1 y)) x‖ ^ 2 = _
      rw [hess_norm, hT]
      exact norm_invariant hf T x
  · let idK : K := ⟨ContinuousLinearMap.id ℝ R3, by simp⟩
    have hjet : jet idK = (lap f x, hess f x) := rfl
    change (lap f x, hess f x) ∈ μ.support
    rw [← hjet]
    apply (Measure.mem_support_iff_forall _).mpr
    intro U hU
    have hpre : jet ⁻¹' U ∈ 𝓝 idK := hj.continuousAt.preimage_mem_nhds hU
    have hm := (Measure.mem_support_iff_forall idK).mp hid _ hpre
    exact hm.trans_le (Measure.le_map_apply hj.aemeasurable U)
