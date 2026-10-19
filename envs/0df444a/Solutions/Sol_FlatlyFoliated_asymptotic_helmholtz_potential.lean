-- Prove2me | solution 1 for FlatlyFoliated.asymptotic_helmholtz_potential
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T19:37:19.742335+00:00
-- url     : https://prove2.me/submissions/fcbd3817-2479-45c7-952f-87a8c1355d60

import Theorems.Thm_FlatlyFoliated_compact_poisson_potential_three
import Theorems.Thm_FlatlyFoliated_orthogonal_spherical_average
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

open scoped ContDiff Topology
open FlatlyFoliated MeasureTheory Metric Set Filter

namespace HelmholtzPotential
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

private noncomputable abbrev axis (r : ℝ) : R3 := EuclideanSpace.single 0 r

private lemma axis_norm {r : ℝ} (hr : 0 ≤ r) : ‖axis r‖ = r := by
  simp [axis, Real.norm_eq_abs, abs_of_nonneg hr]

private lemma axis_deriv (r : ℝ) : HasDerivAt axis (axis 1) r := by
  have h := (hasDerivAt_id r).smul_const (axis 1)
  simp only [id_eq, one_smul] at h
  convert! h using 1
  ext s i
  simp [axis]

private lemma smooth_comp {w : R3 → R3} (hw : ContDiff ℝ ∞ w) (i : Fin 3) :
    ContDiff ℝ ∞ (comp w i) :=
  (EuclideanSpace.proj i : R3 →L[ℝ] ℝ).contDiff.comp hw

private lemma smooth_pd {u : R3 → ℝ} (hu : ContDiff ℝ ∞ u) (i : Fin 3) :
    ContDiff ℝ ∞ (pd i u) :=
  (hu.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const

private lemma profile_deriv {u : R3 → ℝ} (hu : ContDiff ℝ ∞ u) (r : ℝ) :
    HasDerivAt (fun s => u (axis s)) (pd 0 u (axis r)) r :=
  (hu.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt r (axis_deriv r)

private lemma radial_repr {w : R3 → R3} {η : R3 → ℝ} {R : ℝ}
    (hs : ∀ (T : R3 ≃ₗᵢ[ℝ] R3) (x : R3), R ≤ ‖x‖ →
      η (T x) = η x ∧ w (T x) = T (w x))
    {x : R3} (hx : R ≤ ‖x‖) (hx0 : 0 < ‖x‖) :
    w x = (w (axis ‖x‖) 0 / ‖x‖) • x ∧ η x = η (axis ‖x‖) := by
  let y := axis ‖x‖
  have hy : ‖y‖ = ‖x‖ := axis_norm (norm_nonneg x)
  have hfix : (Submodule.span ℝ {y}).reflection y = y :=
    Submodule.reflection_mem_subspace_eq_self (Submodule.mem_span_singleton_self y)
  have hwy : (Submodule.span ℝ {y}).reflection (w y) = w y := by
    have h := (hs (Submodule.span ℝ {y}).reflection y (by simpa [hy] using hx)).2
    rw [hfix] at h
    exact h.symm
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
    ((Submodule.reflection_eq_self_iff (w y)).mp hwy)
  have hc0 : c = w y 0 / ‖x‖ := by
    have h := congrArg (fun z : R3 => z 0) hc
    change c * ‖x‖ = w y 0 at h
    exact (eq_div_iff (ne_of_gt hx0)).mpr h
  let T := (Submodule.span ℝ {y - x})ᗮ.reflection
  have ht : T y = x := Submodule.reflection_sub hy
  have hh := hs T y (by simpa [hy] using hx)
  rw [ht] at hh
  constructor
  · calc
      w x = T (w y) := hh.2
      _ = T (c • y) := congrArg T hc.symm
      _ = c • x := by rw [map_smul, ht]
      _ = _ := by rw [hc0]
  · exact hh.1


private lemma norm_deriv {x : R3} (hx : 0 < ‖x‖) :
    HasFDerivAt (fun y : R3 => ‖y‖) ((‖x‖)⁻¹ • innerSL ℝ x) x := by
  have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt (pow_ne_zero 2 (ne_of_gt hx))
  simp only [Real.sqrt_sq (norm_nonneg _)] at h
  have he : (‖x‖)⁻¹ • innerSL ℝ x = (1 / (2 * ‖x‖)) • 2 • innerSL ℝ x := by
    ext v
    simp only [two_smul, add_apply, smul_apply, smul_eq_mul]
    field_simp
    ring
  rw [← he] at h
  exact h

private lemma inner_axis (x : R3) (j : Fin 3) :
    innerSL ℝ x (EuclideanSpace.single j 1) = x j := by
  simp [innerSL_apply_apply, EuclideanSpace.inner_single_right]


private lemma radial_split (w : R3 → R3) (hw : ContDiff ℝ ∞ w)
    (hs : ∃ R : ℝ, 0 < R ∧ ∀ (T : R3 ≃ₗᵢ[ℝ] R3) (x : R3),
      R ≤ ‖x‖ → w (T x) = T (w x)) :
    ∃ p : R3 → ℝ, ContDiff ℝ ∞ p ∧ IsSphSymm p ∧
      HasCompactSupport (fun x => w x - grad p x) := by
  obtain ⟨R, hR, hs⟩ := hs
  let b : ℝ → ℝ := fun r => Real.smoothTransition (r - R) * w (axis r) 0
  have hb : ContDiff ℝ ∞ b :=
    (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)).mul
      ((smooth_comp hw 0).comp (by
        change ContDiff ℝ ∞ (fun r : ℝ => EuclideanSpace.single 0 r)
        convert! (contDiff_id.smul (contDiff_const (c := axis 1)) : ContDiff ℝ ∞ (fun r : ℝ => r • axis 1)) using 1
        ext r i
        simp [axis]))
  let H : ℝ → ℝ := fun r => ∫ t in (0 : ℝ)..r, b t
  have hH (r : ℝ) : HasDerivAt H (b r) r :=
    intervalIntegral.integral_hasDerivAt_right (hb.continuous.intervalIntegrable _ _)
      (hb.continuous.stronglyMeasurableAtFilter volume (𝓝 r)) hb.continuous.continuousAt
  have hHs : ContDiff ℝ ∞ H := contDiff_infty_iff_deriv.mpr
    ⟨fun r => (hH r).differentiableAt, by simpa only [funext fun r => (hH r).deriv] using hb⟩
  have hHz {r : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R) : H r = 0 := by
    change (∫ t in (0 : ℝ)..r, b t) = 0
    calc
      _ = ∫ t in (0 : ℝ)..r, (0 : ℝ) := intervalIntegral.integral_congr fun t ht => by
        have ht' : t ∈ Icc 0 r := by simpa only [uIcc_of_le hr] using ht
        have htR : t ≤ R := le_trans ht'.2 hrR
        simp [b, Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr htR)]
      _ = 0 := by simp
  let p : R3 → ℝ := fun x => H ‖x‖
  have hp : ContDiff ℝ ∞ p := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x = 0
    · subst x
      apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [ball_mem_nhds (0 : R3) hR] with y hy
      exact (hHz (norm_nonneg y) (le_of_lt (by simpa only [mem_ball_zero_iff] using hy)))
    · exact hHs.contDiffAt.comp x (contDiffAt_norm ℝ hx)
  have hgrad {x : R3} (hx : R + 1 ≤ ‖x‖) : grad p x = w x := by
    have hx0 : 0 < ‖x‖ := by linarith
    have hd : HasFDerivAt p (b ‖x‖ • ((‖x‖)⁻¹ • innerSL ℝ x)) x :=
      (hH ‖x‖).comp_hasFDerivAt x (norm_deriv hx0)
    have heq : grad p x = (b ‖x‖ / ‖x‖) • x := by
      ext i
      simp [grad, pd, hd.fderiv, inner_axis, div_eq_mul_inv, Pi.single_apply, mul_ite]
      ring
    rw [heq]
    have hb1 : Real.smoothTransition (‖x‖ - R) = 1 :=
      Real.smoothTransition.one_of_one_le (by linarith)
    have he := (radial_repr (w := w) (η := fun _ => 0) (R := R)
      (fun T y hy => ⟨rfl, hs T y hy⟩) (by linarith) hx0).1
    simpa [b, hb1] using he.symm
  refine ⟨p, hp, ?_, ?_⟩
  · intro T x
    exact congrArg H (T.norm_map x)
  · apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : R3) (R + 1))
    intro x hx
    by_contra h
    have hnorm : R + 1 ≤ ‖x‖ := le_of_lt (by simpa [mem_closedBall_zero_iff] using h)
    exact hx (sub_eq_zero.mpr (hgrad hnorm).symm)

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


private lemma smooth_eval {h : R3 → ℝ} (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (fun p : R3 × L => h (p.2 p.1)) :=
  hh.comp (contDiff_snd.clm_apply contDiff_fst)

private lemma fixed_deriv {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {F : R3 × L → V} (hf : ContDiff ℝ ∞ F) (A : L) (x : R3) :
    HasFDerivAt (fun y => F (y, A)) (dx F (x, A)) x := by
  exact ((hf.differentiable (by simp) (x, A)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).prodMk (hasFDerivAt_const A x)))

private lemma dx_eval {h : R3 → ℝ} (hh : ContDiff ℝ ∞ h) (x : R3) (A : L) :
    dx (fun p : R3 × L => h (p.2 p.1)) (x, A) = (fderiv ℝ h (A x)).comp A := by
  have hd := ((hh.differentiable (by simp) (A x)).hasFDerivAt.comp x A.hasFDerivAt)
  have hf := fixed_deriv (smooth_eval hh) A x
  exact hf.unique hd

private lemma dx2_eval {h : R3 → ℝ} (hh : ContDiff ℝ ∞ h) (x : R3) (A : L) :
    dx (dx (fun p : R3 × L => h (p.2 p.1))) (x, A) =
      ((ContinuousLinearMap.compL ℝ R3 R3 ℝ).flip A).comp
        ((fderiv ℝ (fderiv ℝ h) (A x)).comp A) := by
  have hd := (((hh.fderiv_right (m := ∞) le_rfl).differentiable (by simp) (A x)).hasFDerivAt.comp x A.hasFDerivAt).clm_comp
    (hasFDerivAt_const A x)
  have hfun : (fun y => dx (fun p : R3 × L => h (p.2 p.1)) (y, A)) =
      (fun y => (fderiv ℝ h (A y)).comp A) := funext fun y => dx_eval hh y A
  have hf := fixed_deriv (smooth_dx (smooth_eval hh)) A x
  rw [hfun] at hf
  convert! hf.unique hd using 1
  ext u v
  simp

private lemma average_bounds (h : R3 → ℝ) (hh : ContDiff ℝ ∞ h)
    (C : ℝ) (hC : 0 < C)
    (hb : ∀ x : R3, |h x| ≤ C / (1 + ‖x‖) ∧
      ‖fderiv ℝ h x‖ ≤ C / (1 + ‖x‖) ^ 2 ∧
      ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ C / (1 + ‖x‖) ^ 3) :
    ContDiff ℝ ∞ (sphSymmetrization h) ∧ ∀ x : R3,
      |sphSymmetrization h x| ≤ C / (1 + ‖x‖) ∧
      ‖fderiv ℝ (sphSymmetrization h) x‖ ≤ C / (1 + ‖x‖) ^ 2 ∧
      ‖fderiv ℝ (fderiv ℝ (sphSymmetrization h)) x‖ ≤ C / (1 + ‖x‖) ^ 3 := by
  obtain ⟨ν, hν, ho, _, havg⟩ := FlatlyFoliated.orthogonal_spherical_average
  let : IsProbabilityMeasure ν := hν
  let F : R3 × L → ℝ := fun p => h (p.2 p.1)
  have hF : ContDiff ℝ ∞ F := smooth_eval hh
  have he : sphSymmetrization h = fun x => ∫ A : K, F (x, A.1) ∂ν := by
    funext x
    exact (havg h hh.continuous x).symm
  have hd : fderiv ℝ (sphSymmetrization h) = fun x => ∫ A : K, dx F (x, A.1) ∂ν := by
    funext x
    rw [he]
    exact (deriv_int ν hF x).fderiv
  have hdd (x : R3) : fderiv ℝ (fderiv ℝ (sphSymmetrization h)) x =
      ∫ A : K, dx (dx F) (x, A.1) ∂ν := by
    rw [hd]
    exact (deriv_int ν (smooth_dx hF) x).fderiv
  refine ⟨by rw [he]; exact smooth_int ν hF, ?_⟩
  intro x
  have hA (A : K) : ‖A.1‖ ≤ 1 := by simpa only [mem_closedBall_zero_iff] using A.2
  have hbound : ∀ᵐ A : K ∂ν,
      |F (x, A.1)| ≤ C / (1 + ‖x‖) ∧
      ‖dx F (x, A.1)‖ ≤ C / (1 + ‖x‖) ^ 2 ∧
      ‖dx (dx F) (x, A.1)‖ ≤ C / (1 + ‖x‖) ^ 3 := by
    filter_upwards [ho] with A horth
    obtain ⟨T, hT⟩ := horth
    have hnorm (z : R3) : ‖A.1 z‖ = ‖z‖ := by rw [hT]; exact T.norm_map z
    have hn := hnorm x
    refine ⟨by simpa only [F, hn] using (hb (A.1 x)).1, ?_, ?_⟩
    · rw [show dx F (x, A.1) = _ from dx_eval hh x A.1]
      calc
        ‖(fderiv ℝ h (A.1 x)).comp A.1‖ ≤ ‖fderiv ℝ h (A.1 x)‖ * ‖A.1‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ‖fderiv ℝ h (A.1 x)‖ := mul_le_of_le_one_right (norm_nonneg _) (hA A)
        _ ≤ _ := by simpa only [hn] using (hb (A.1 x)).2.1
    · rw [show dx (dx F) (x, A.1) = _ from dx2_eval hh x A.1]
      apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      intro u
      apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      intro v
      change ‖(fderiv ℝ (fderiv ℝ h) (A.1 x) (A.1 u)) (A.1 v)‖ ≤ _
      calc
        _ ≤ ‖fderiv ℝ (fderiv ℝ h) (A.1 x)‖ * ‖A.1 u‖ * ‖A.1 v‖ := by
          exact (ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _))
        _ = ‖fderiv ℝ (fderiv ℝ h) (A.1 x)‖ * ‖u‖ * ‖v‖ := by rw [hnorm u, hnorm v]
        _ ≤ _ := by gcongr; simpa only [hn] using (hb (A.1 x)).2.2
  constructor
  · rw [he]
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
      (norm_integral_le_of_norm_le_const (f := fun A : K => F (x, A.1))
        (hbound.mono fun A hA => by simpa only [Real.norm_eq_abs] using hA.1))
  constructor
  · rw [congrFun hd x]
    simpa only [probReal_univ, mul_one] using
      (norm_integral_le_of_norm_le_const (hbound.mono fun A hA => hA.2.1))
  · rw [hdd]
    simpa only [probReal_univ, mul_one] using
      (norm_integral_le_of_norm_le_const (hbound.mono fun A hA => hA.2.2))

private lemma approx_decay (h : R3 → ℝ) (hh : ContDiff ℝ ∞ h)
    (C : ℝ) (hC : 0 < C)
    (hb : ∀ x : R3, |h x| ≤ C / (1 + ‖x‖) ∧
      ‖fderiv ℝ h x‖ ≤ C / (1 + ‖x‖) ^ 2 ∧
      ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ C / (1 + ‖x‖) ^ 3) :
    ApproxSphSymmAtInfty h := by
  obtain ⟨havg, hba⟩ := average_bounds h hh C hC hb
  let g : R3 → ℝ := fun x => h x - sphSymmetrization h x
  have hd : fderiv ℝ g = fun x => fderiv ℝ h x - fderiv ℝ (sphSymmetrization h) x := by
    funext x
    exact fderiv_fun_sub (hh.differentiable (by simp) x) (havg.differentiable (by simp) x)
  have hdd (x : R3) : fderiv ℝ (fderiv ℝ g) x =
      fderiv ℝ (fderiv ℝ h) x - fderiv ℝ (fderiv ℝ (sphSymmetrization h)) x := by
    rw [hd]
    exact fderiv_fun_sub ((hh.fderiv_right (m := ∞) le_rfl).differentiable (by simp) x)
      ((havg.fderiv_right (m := ∞) le_rfl).differentiable (by simp) x)
  have hgb (x : R3) : ‖fderiv ℝ g x‖ ≤ 2 * C / (1 + ‖x‖) ^ 2 ∧
      ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ 2 * C / (1 + ‖x‖) ^ 3 := by
    constructor
    · rw [congrFun hd x]
      exact (norm_sub_le _ _).trans ((add_le_add (hb x).2.1 (hba x).2.1).trans_eq (by ring))
    · rw [hdd]
      calc
        ‖fderiv ℝ (fderiv ℝ h) x - fderiv ℝ (fderiv ℝ (sphSymmetrization h)) x‖ ≤
            ‖fderiv ℝ (fderiv ℝ h) x‖ + ‖fderiv ℝ (fderiv ℝ (sphSymmetrization h)) x‖ := by
          convert! norm_sub_le (fderiv ℝ (fderiv ℝ h) x)
            (fderiv ℝ (fderiv ℝ (sphSymmetrization h)) x) using 1
        _ ≤ C / (1 + ‖x‖) ^ 3 + C / (1 + ‖x‖) ^ 3 := add_le_add (hb x).2.2 (hba x).2.2
        _ = 2 * C / (1 + ‖x‖) ^ 3 := by ring
  constructor
  · refine ⟨2 * C, fun x => ?_⟩
    calc
      |h x - sphSymmetrization h x| ≤ |h x| + |sphSymmetrization h x| := abs_sub _ _
      _ ≤ 2 * C / (1 + ‖x‖) := (add_le_add (hb x).1 (hba x).1).trans_eq (by ring)
      _ ≤ 2 * C := (div_le_iff₀ (by positivity)).mpr (by nlinarith [norm_nonneg x])
  · intro ε hε
    refine ⟨4 * C ^ 2 / ε, fun x hx => ?_⟩
    have ht : 0 < 1 + ‖x‖ := by positivity
    have hcub : 1 + ‖x‖ ≤ (1 + ‖x‖) ^ 3 := by
      nlinarith [norm_nonneg x, sq_nonneg ‖x‖, mul_nonneg (norm_nonneg x) (sq_nonneg ‖x‖)]
    change ‖x‖ ^ 2 * (‖fderiv ℝ (fderiv ℝ g) x‖ * ‖fderiv ℝ g x‖) ≤ ε
    calc
      _ ≤ (1 + ‖x‖) ^ 2 *
          ((2 * C / (1 + ‖x‖) ^ 3) * (2 * C / (1 + ‖x‖) ^ 2)) := by
        gcongr
        · nlinarith [norm_nonneg x]
        · exact (hgb x).2
        · exact (hgb x).1
      _ = 4 * C ^ 2 / (1 + ‖x‖) ^ 3 := by field_simp; ring
      _ ≤ 4 * C ^ 2 / (1 + ‖x‖) := div_le_div_of_nonneg_left (by positivity) ht hcub
      _ ≤ ε := (div_le_iff₀ ht).mpr (by
        have hx' := (div_le_iff₀ hε).mp hx
        nlinarith)

private lemma average_radial_add {p h : R3 → ℝ} (hp : ContDiff ℝ ∞ p)
    (hh : ContDiff ℝ ∞ h) (hs : IsSphSymm p) :
    sphSymmetrization (fun x => p x + h x) = fun x => p x + sphSymmetrization h x := by
  obtain ⟨ν, hν, ho, _, havg⟩ := FlatlyFoliated.orthogonal_spherical_average
  let : IsProbabilityMeasure ν := hν
  funext x
  have hip : Integrable (fun A : K => p (A.1 x)) ν := c_int ν
    (hp.continuous.comp (continuous_subtype_val.clm_apply continuous_const))
  have hih : Integrable (fun A : K => h (A.1 x)) ν := c_int ν
    (hh.continuous.comp (continuous_subtype_val.clm_apply continuous_const))
  rw [← havg (fun y => p y + h y) (hp.continuous.add hh.continuous) x,
    integral_add hip hih, havg h hh.continuous x]
  congr 1
  apply integral_eq_const
  filter_upwards [ho] with A hA
  obtain ⟨T, hT⟩ := hA
  rw [hT]
  exact hs T x

private lemma grad_add {p h : R3 → ℝ} (hp : ContDiff ℝ ∞ p) (hh : ContDiff ℝ ∞ h) :
    grad (fun x => p x + h x) = fun x => grad p x + grad h x := by
  funext x
  have hd := fderiv_fun_add (hp.differentiable (by simp) x) (hh.differentiable (by simp) x)
  simp only [grad, pd, hd, add_apply, add_smul, Finset.sum_add_distrib]

private lemma grad_norm (h : R3 → ℝ) (x : R3) : ‖grad h x‖ ≤ 3 * ‖fderiv ℝ h x‖ := by
  calc
    ‖grad h x‖ ≤ ∑ i : Fin 3, ‖pd i h x • EuclideanSpace.single i (1 : ℝ)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, ‖fderiv ℝ h x‖ := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [norm_smul, PiLp.norm_single, norm_one, mul_one, pd] using
        (ContinuousLinearMap.le_opNorm (fderiv ℝ h x) (EuclideanSpace.single i 1))
    _ = 3 * ‖fderiv ℝ h x‖ := by simp [nsmul_eq_mul]

private lemma grad_decay (h : R3 → ℝ) (C : ℝ) (_hC : 0 < C)
    (hb : ∀ x : R3, ‖fderiv ℝ h x‖ ≤ C / (1 + ‖x‖) ^ 2) :
    Tendsto (grad h) (Bornology.cobounded R3) (𝓝 0) := by
  apply squeeze_zero_norm (fun x => (grad_norm h x).trans (mul_le_mul_of_nonneg_left (hb x) (by norm_num)))
  have ht : Tendsto (fun x : R3 => (1 + ‖x‖) ^ 2) (Bornology.cobounded R3) atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
      (tendsto_const_nhds.add_atTop tendsto_norm_cobounded_atTop)
  simpa only [Function.comp_def, div_eq_mul_inv, mul_assoc, mul_zero] using
    tendsto_const_nhds.mul (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp ht))

private lemma divg_grad (p : R3 → ℝ) : divg (grad p) = lap p := by
  have he (i : Fin 3) : comp (grad p) i = pd i p := by
    funext x
    simp [comp, grad, Pi.single_apply, mul_ite]
  unfold divg lap
  simp_rw [he]

private lemma divg_sub {u v : R3 → R3} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) :
    divg (fun x => u x - v x) = fun x => divg u x - divg v x := by
  funext x
  have he (i : Fin 3) : comp (fun x => u x - v x) i = fun x => comp u i x - comp v i x := rfl
  simp only [divg, he, pd, fderiv_fun_sub ((smooth_comp hu _).differentiable (by simp) x)
    ((smooth_comp hv _).differentiable (by simp) x), sub_apply, Finset.sum_sub_distrib]

private lemma smooth_grad {p : R3 → ℝ} (hp : ContDiff ℝ ∞ p) : ContDiff ℝ ∞ (grad p) := by
  apply ContDiff.sum
  intro i _
  exact (smooth_pd hp i).smul contDiff_const

end HelmholtzPotential

open HelmholtzPotential

theorem solution
    (w : R3 → R3) (hw : ContDiff ℝ ∞ w)
    (hs : ∃ R : ℝ, 0 < R ∧ ∀ (T : R3 ≃ₗᵢ[ℝ] R3) (x : R3),
      R ≤ ‖x‖ → w (T x) = T (w x)) :
    ∃ f : R3 → ℝ, ContDiff ℝ ∞ f ∧ (∀ x, lap f x = divg w x) ∧
      ApproxSphSymmAtInfty f ∧
      Tendsto (fun x => w x - grad f x) (Bornology.cobounded R3) (𝓝 0) := by
  obtain ⟨p, hp, hps, hpc⟩ := radial_split w hw hs
  let v : R3 → R3 := fun x => w x - grad p x
  have hv : ContDiff ℝ ∞ v := hw.sub (smooth_grad hp)
  have hvc : HasCompactSupport v := hpc
  have hq : ContDiff ℝ ∞ (divg v) := by
    apply ContDiff.sum
    intro i _
    exact smooth_pd (smooth_comp hv i) i
  have hqc : HasCompactSupport (divg v) := by
    change HasCompactSupport (∑ i : Fin 3, pd i (comp v i))
    apply HasCompactSupport.finset_sum
    intro i _
    exact (hvc.comp_left (g := fun z : R3 => z i) rfl).fderiv_apply ℝ (EuclideanSpace.single i (1 : ℝ))
  obtain ⟨h, hh, hΔ, C, hC, hb⟩ := FlatlyFoliated.compact_poisson_potential_three (divg v) hq hqc
  refine ⟨fun x => p x + h x, hp.add hh, ?_, ?_, ?_⟩
  · have hpd (u t : R3 → ℝ) (hu : ContDiff ℝ ∞ u) (ht : ContDiff ℝ ∞ t) (i : Fin 3) :
        pd i (fun x => u x + t x) = fun x => pd i u x + pd i t x := by
      funext x
      simp only [pd, fderiv_fun_add (hu.differentiable (by simp) x) (ht.differentiable (by simp) x), add_apply]
    have hsum : lap (fun x => p x + h x) = fun x => lap p x + lap h x := by
      funext x
      simp only [lap, hpd p h hp hh]
      simp only [hpd (pd _ p) (pd _ h) (smooth_pd hp _) (smooth_pd hh _), Finset.sum_add_distrib]
    intro x
    rw [hsum]
    change lap p x + lap h x = _
    rw [hΔ]
    have hdiv := congrFun (divg_sub hw (smooth_grad hp)) x
    rw [divg_grad] at hdiv
    change divg v x = divg w x - lap p x at hdiv
    linarith
  · have he : (fun x => (p x + h x) - sphSymmetrization (fun y => p y + h y) x) =
        (fun x => h x - sphSymmetrization h x) := by
      rw [average_radial_add hp hh hps]
      funext x
      ring
    have ha := approx_decay h hh C hC hb
    change (∃ D : ℝ, ∀ x, |((fun y => (p y + h y) - sphSymmetrization (fun z => p z + h z) y) x)| ≤ D) ∧ _
    rw [he]
    exact ha
  · rw [grad_add hp hh]
    have hz : Tendsto v (Bornology.cobounded R3) (𝓝 0) := by
      rw [Metric.cobounded_eq_cocompact]
      exact hvc.is_zero_at_infty
    have hd := hz.sub (grad_decay h C hC fun x => (hb x).2.1)
    convert hd using 1
    · funext x
      change w x - (grad p x + grad h x) = (w x - grad p x) - grad h x
      abel
    · simp
