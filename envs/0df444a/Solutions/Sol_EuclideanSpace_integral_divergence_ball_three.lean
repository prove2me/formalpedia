-- Prove2me | solution 1 for EuclideanSpace.integral_divergence_ball_three
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T19:21:32.62311+00:00
-- url     : https://prove2.me/submissions/82dbb173-e657-4f3c-addd-0ae2b851ca0c

import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open scoped Topology ContDiff
open MeasureTheory Metric Set Filter
noncomputable section
namespace BallGauss
abbrev E := EuclideanSpace ℝ (Fin 3)
abbrev S := sphere (0 : E) 1
abbrev σ : Measure S := (volume : Measure E).toSphere
instance : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_sphere 0 1)

lemma polar (g : E → ℝ) (hg : Integrable g) :
    (∫ x, g x) = ∫ r in Ioi (0 : ℝ), r ^ 2 * ∫ u : S, g (r • u.1) ∂σ := by
  let e := homeomorphUnitSphereProd E
  have hm := (volume : Measure E).measurePreserving_homeomorphUnitSphereProd
  simp only [finrank_euclideanSpace_fin, Nat.reduceSub] at hm
  change MeasurePreserving e _ (σ.prod (Measure.volumeIoiPow 2)) at hm
  have hi : Integrable (fun p : S × Ioi (0 : ℝ) => g (p.2.1 • p.1.1))
      (σ.prod (Measure.volumeIoiPow 2)) := by
    have hsub : Integrable (fun x : ({(0 : E)}ᶜ : Set E) => g x.1)
        ((volume : Measure E).comap Subtype.val) := by
      exact (integrableOn_iff_comap_subtypeVal (measurableSet_singleton _).compl).mp hg.integrableOn
    have hp := hm.integrable_comp_emb e.measurableEmbedding
      (g := fun p => g (e.symm p).1)
    apply hp.mp
    simpa only [Function.comp_def, e.symm_apply_apply] using hsub
  calc
    _ = ∫ x : ({(0 : E)}ᶜ : Set E), g x.1 ∂((volume : Measure E).comap Subtype.val) := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl, restrict_compl_singleton]
    _ = ∫ p : S × Ioi (0 : ℝ), g (p.2.1 • p.1.1) ∂(σ.prod (Measure.volumeIoiPow 2)) := by
      simpa [e, homeomorphUnitSphereProd] using
        hm.integral_comp e.measurableEmbedding (fun p => g (e.symm p).1)
    _ = ∫ r : Ioi (0 : ℝ), (∫ u : S, g (r.1 • u.1) ∂σ) ∂Measure.volumeIoiPow 2 :=
      integral_prod_symm _ hi
    _ = _ := by
      simp only [Measure.volumeIoiPow, ENNReal.ofReal]
      rw [integral_withDensity_eq_integral_smul]
      · simp only [NNReal.smul_def, Real.coe_toNNReal _ (sq_nonneg _), smul_eq_mul]
        convert! integral_subtype_comap measurableSet_Ioi
          (fun r : ℝ => r ^ 2 * ∫ u : S, g (r • u.1) ∂σ) using 1
      · exact (measurable_subtype_coe.pow_const _).real_toNNReal

lemma norm_deriv (x : E) (hx : x ≠ 0) :
    HasFDerivAt (fun y : E => ‖y‖) (‖x‖⁻¹ • innerSL ℝ x) x := by
  have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt (by positivity : ‖x‖ ^ 2 ≠ 0)
  convert! h using 1
  · simp
  · ext v
    simp [Real.sqrt_sq (norm_nonneg x)]
    ring

def cut (R ε r : ℝ) := Real.smoothTransition ((R + ε - r) / ε)
lemma cut_smooth (R ε : ℝ) : ContDiff ℝ ∞ (cut R ε) :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const ε)
lemma cut_one (R ε r : ℝ) (hε : 0 < ε) (hr : r ≤ R) : cut R ε r = 1 := by
  apply Real.smoothTransition.one_of_one_le
  exact (le_div_iff₀ hε).mpr (by linarith)
lemma cut_zero (R ε r : ℝ) (hε : 0 < ε) (hr : R + ε ≤ r) : cut R ε r = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
lemma cut_deriv (R ε r : ℝ) :
    deriv (cut R ε) r = -(ε⁻¹) * deriv Real.smoothTransition ((R+ε-r)/ε) := by
  have h := ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero _).hasDerivAt.comp r
    (((hasDerivAt_const r (R+ε)).sub (hasDerivAt_id r)).div_const ε)
  change HasDerivAt (cut R ε) _ r at h
  simpa [div_eq_mul_inv, mul_comm] using h.deriv

lemma radial_cut_smooth (R ε : ℝ) (hR : 0 < R) (hε : 0 < ε) :
    ContDiff ℝ 1 (fun x : E => cut R ε ‖x‖) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    apply (contDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq
    filter_upwards [ball_mem_nhds (0 : E) hR] with x hx
    exact (cut_one R ε ‖x‖ hε (by simpa [mem_ball, dist_zero_right] using (show dist x 0 < R from hx).le))
  · exact (cut_smooth R ε).contDiffAt.of_le (by simp) |>.comp x (contDiffAt_norm ℝ hx)

lemma radial_cut_support (R ε : ℝ) (hε : 0 < ε) :
    HasCompactSupport (fun x : E => cut R ε ‖x‖) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 (R+ε))
  intro x hx
  by_contra hn
  apply hx
  exact cut_zero R ε ‖x‖ hε (by simpa [mem_closedBall, dist_zero_right] using (show R+ε < ‖x‖ from by simpa [mem_closedBall, dist_zero_right] using hn).le)

lemma cut_deriv_zero_left (R ε r : ℝ) (hε : 0 < ε) (hr : r < R) :
    deriv (cut R ε) r = 0 := by
  have he : cut R ε =ᶠ[𝓝 r] fun _ => (1 : ℝ) := by
    filter_upwards [Iio_mem_nhds hr] with s hs using cut_one R ε s hε hs.le
  simpa using he.deriv_eq

lemma cut_deriv_zero_right (R ε r : ℝ) (hε : 0 < ε) (hr : R+ε < r) :
    deriv (cut R ε) r = 0 := by
  have he : cut R ε =ᶠ[𝓝 r] fun _ => (0 : ℝ) := by
    filter_upwards [Ioi_mem_nhds hr] with s hs using cut_zero R ε s hε hs.le
  simpa using he.deriv_eq

lemma radial_cut_deriv (R ε : ℝ) (hR : 0 < R) (hε : 0 < ε) (x v : E) :
    fderiv ℝ (fun x : E => cut R ε ‖x‖) x v =
      deriv (cut R ε) ‖x‖ * ‖x‖⁻¹ * inner ℝ x v := by
  by_cases hx : x = 0
  · subst x
    have he : (fun y : E => cut R ε ‖y‖) =ᶠ[𝓝 0] fun _ => (1 : ℝ) := by
      filter_upwards [ball_mem_nhds (0 : E) hR] with y hy
      exact cut_one R ε ‖y‖ hε (by simpa [mem_ball, dist_zero_right] using (show dist y 0 < R from hy).le)
    rw [he.fderiv_eq]
    simp
  · have h := ((cut_smooth R ε).differentiable (by simp) ‖x‖).hasDerivAt.comp_hasFDerivAt x (norm_deriv x hx)
    change HasFDerivAt (fun x : E => cut R ε ‖x‖) _ x at h
    rw [h.fderiv]
    simp [mul_assoc]

abbrev div (F : E → E) (x : E) : ℝ :=
  ∑ i : Fin 3, (fderiv ℝ F x (EuclideanSpace.single i 1)) i

lemma cont_div {F : E → E} (hF : ContDiff ℝ 1 F) : Continuous (div F) := by
  apply continuous_finsetSum
  intro i _
  exact (EuclideanSpace.proj i : E →L[ℝ] ℝ).continuous.comp
    ((hF.continuous_fderiv one_ne_zero).clm_apply continuous_const)

lemma weighted_ibp {F : E → E} (hF : ContDiff ℝ 1 F)
    (R ε : ℝ) (hR : 0 < R) (hε : 0 < ε) :
    (∫ x, cut R ε ‖x‖ * div F x) =
      -(∫ x, deriv (cut R ε) ‖x‖ * ‖x‖⁻¹ * inner ℝ (F x) x) := by
  let c := fun x : E => cut R ε ‖x‖
  have hc : ContDiff ℝ 1 c := radial_cut_smooth R ε hR hε
  have hs : HasCompactSupport c := radial_cut_support R ε hε
  have hdc (i : Fin 3) : Continuous (fun x => fderiv ℝ c x (EuclideanSpace.single i 1)) :=
    (hc.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hFi (i : Fin 3) : ContDiff ℝ 1 (fun x => (F x) i) :=
    (EuclideanSpace.proj i : E →L[ℝ] ℝ).contDiff.comp hF
  have hdFi (i : Fin 3) : ∀ x v, fderiv ℝ (fun x => (F x) i) x v = (fderiv ℝ F x v) i := by
    intro x v
    exact congrArg (fun A : E →L[ℝ] ℝ => A v)
      (((EuclideanSpace.proj i : E →L[ℝ] ℝ).hasFDerivAt.comp x
        (hF.differentiable one_ne_zero x).hasFDerivAt).fderiv)
  have h1 (i : Fin 3) : Integrable (fun x => c x * (fderiv ℝ F x (EuclideanSpace.single i 1)) i) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact hc.continuous.mul ((EuclideanSpace.proj i : E →L[ℝ] ℝ).continuous.comp
        ((hF.continuous_fderiv one_ne_zero).clm_apply continuous_const))
    · exact hs.mul_right
  have h2 (i : Fin 3) : Integrable (fun x => fderiv ℝ c x (EuclideanSpace.single i 1) * (F x) i) :=
    ((hdc i).mul (hFi i).continuous).integrable_of_hasCompactSupport
      ((hs.fderiv_apply (𝕜 := ℝ) _).mul_right)
  have he (i : Fin 3) :
      (∫ x, c x * (fderiv ℝ F x (EuclideanSpace.single i 1)) i) =
      -(∫ x, fderiv ℝ c x (EuclideanSpace.single i 1) * (F x) i) := by
    simpa only [hdFi] using integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (f := c) (g := fun x => (F x) i) (v := EuclideanSpace.single i 1)
      (h2 i) (by simpa only [hdFi] using h1 i)
      ((hc.continuous.mul (hFi i).continuous).integrable_of_hasCompactSupport hs.mul_right)
      (fun x _ => hc.differentiable one_ne_zero x)
      (fun x _ => (hFi i).differentiable one_ne_zero x)
  change (∫ x, c x * div F x) = _
  simp_rw [div, Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => h1 i)]
  simp_rw [he]
  rw [Finset.sum_neg_distrib]
  rw [← integral_finsetSum _ (fun i _ => h2 i)]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [c, radial_cut_deriv R ε hR hε, EuclideanSpace.inner_single_right,
    mul_assoc, ← Finset.mul_sum]
  congr 1
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]

def boundary (F : E → E) (r : ℝ) := r ^ 2 * ∫ u : S, inner ℝ (F (r • u.1)) u.1 ∂σ

lemma boundary_cont {F : E → E} (hF : Continuous F) : Continuous (boundary F) := by
  have hi : Continuous (fun r : ℝ => ∫ u : S, inner ℝ (F (r • u.1)) u.1 ∂σ) := by
    have h := continuous_parametric_integral_of_continuous
      (μ := σ) (f := fun r : ℝ => fun u : S => inner ℝ (F (r • u.1)) u.1)
      (by fun_prop) isCompact_univ
    simpa using h
  exact (continuous_id.pow 2).mul hi

lemma contraction (R ε : ℝ) (hR : 0 < R) (hε : 0 < ε) (F : E → E) (x : E) :
    (∑ i : Fin 3, fderiv ℝ (fun y : E => cut R ε ‖y‖) x (EuclideanSpace.single i 1) * (F x) i) =
    deriv (cut R ε) ‖x‖ * ‖x‖⁻¹ * inner ℝ (F x) x := by
  simp only [radial_cut_deriv R ε hR hε, EuclideanSpace.inner_single_right,
    mul_assoc, ← Finset.mul_sum]
  congr 1
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]

lemma cutoff_flux {F : E → E} (hF : ContDiff ℝ 1 F)
    (R ε : ℝ) (hR : 0 < R) (hε : 0 < ε) :
    (∫ x, cut R ε ‖x‖ * div F x) =
      -(∫ r in R..R+ε, deriv (cut R ε) r * boundary F r) := by
  rw [weighted_ibp hF R ε hR hε]
  congr 1
  let c := fun x : E => cut R ε ‖x‖
  let g := fun x : E => deriv (cut R ε) ‖x‖ * ‖x‖⁻¹ * inner ℝ (F x) x
  have hc : ContDiff ℝ 1 c := radial_cut_smooth R ε hR hε
  have hs : HasCompactSupport c := radial_cut_support R ε hε
  have hg : Integrable g := by
    have he : g = fun x => ∑ i : Fin 3, fderiv ℝ c x (EuclideanSpace.single i 1) * (F x) i :=
      funext fun x => (contraction R ε hR hε F x).symm
    rw [he]
    apply integrable_finsetSum
    intro i _
    exact (((hc.continuous_fderiv one_ne_zero).clm_apply continuous_const).mul
      ((EuclideanSpace.proj i : E →L[ℝ] ℝ).continuous.comp hF.continuous)).integrable_of_hasCompactSupport
      ((hs.fderiv_apply (𝕜 := ℝ) _).mul_right)
  calc
    _ = ∫ r in Ioi (0 : ℝ), r ^ 2 * ∫ u : S, g (r • u.1) ∂σ := polar g hg
    _ = ∫ r in Ioi (0 : ℝ), deriv (cut R ε) r * boundary F r := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      have hrp : 0 < r := hr
      have hnorm (u : S) : ‖r • u.1‖ = r := by
        have hu : ‖u.1‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using u.2
        simp [norm_smul, hu, abs_of_pos hrp]
      simp only [g, hnorm, inner_smul_right, mul_assoc, ← integral_const_mul, boundary]
      rw [integral_const_mul]
      field_simp
      simp_rw [integral_const_mul]
      ring
    _ = ∫ r in Icc R (R+ε), deriv (cut R ε) r * boundary F r := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
        (fun r hr => hR.trans_le hr.1)
      intro r hr
      have hh : r < R ∨ R+ε < r := by simpa only [mem_Icc, not_and_or, not_le] using hr.2
      rcases hh with hh | hh
      · simp [cut_deriv_zero_left R ε r hε hh]
      · simp [cut_deriv_zero_right R ε r hε hh]
    _ = _ := by rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (by linarith)]

lemma cutoff_fixed {F : E → E} (hF : ContDiff ℝ 1 F)
    (R ε : ℝ) (hR : 0 < R) (hε : 0 < ε) :
    (∫ x, cut R ε ‖x‖ * div F x) =
      ∫ t in (0 : ℝ)..1, deriv Real.smoothTransition t * boundary F (R+ε-ε*t) := by
  rw [cutoff_flux hF R ε hR hε]
  let H := fun t => deriv Real.smoothTransition t * boundary F (R+ε-ε*t)
  have he : (fun r => deriv (cut R ε) r * boundary F r) =
      fun r => -(ε⁻¹) * H ((R+ε-r)/ε) := by
    funext r
    dsimp [H]
    rw [cut_deriv]
    have harg : R+ε-ε*((R+ε-r)/ε) = r := by field_simp; ring
    rw [harg]
    ring
  rw [he, intervalIntegral.integral_const_mul]
  simp_rw [sub_div]
  rw [intervalIntegral.integral_comp_sub_div H hε.ne' ((R+ε)/ε)]
  have hend : (R+ε)/ε-R/ε = 1 := by field_simp; ring
  simp [smul_eq_mul, hε.ne', hend, H]

lemma cutoff_limit {F : E → E} (hF : ContDiff ℝ 1 F) (R : ℝ) (hR : 0 < R) :
    Tendsto (fun n : ℕ => ∫ x, cut R (1 / (n+1 : ℝ)) ‖x‖ * div F x) atTop
      (𝓝 (∫ x in ball (0 : E) R, div F x)) := by
  let ε := fun n : ℕ => 1 / (n+1 : ℝ)
  have hp (n) : 0 < ε n := by dsimp [ε]; positivity
  have hle (n) : ε n ≤ 1 := by dsimp [ε]; apply (div_le_one (by positivity)).mpr; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hl : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let K := closedBall (0 : E) (R+1)
  have hbound : IntegrableOn (fun x => ‖div F x‖) K :=
    (cont_div hF).norm.continuousOn.integrableOn_compact (isCompact_closedBall _ _)
  have ht := tendsto_integral_of_dominated_convergence (μ := volume.restrict K)
    (F := fun n x => cut R (ε n) ‖x‖ * div F x)
    (f := (closedBall (0 : E) R).indicator (div F)) (fun x => ‖div F x‖)
    (fun n => (((radial_cut_smooth R (ε n) hR (hp n)).continuous).mul (cont_div hF)).aestronglyMeasurable)
    hbound
    (fun n => .of_forall fun x => by
      rw [norm_mul]
      have hh : ‖cut R (ε n) ‖x‖‖ ≤ 1 := by
        unfold cut
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg _)]
        exact Real.smoothTransition.le_one _
      exact mul_le_of_le_one_left (norm_nonneg _) hh)
    (.of_forall fun x => by
      by_cases hx : ‖x‖ ≤ R
      · have he (n) : cut R (ε n) ‖x‖ = 1 := cut_one R (ε n) ‖x‖ (hp n) hx
        simp [he, indicator_of_mem (show x ∈ closedBall (0 : E) R from by simpa using hx)]
      · have hev : ∀ᶠ n in atTop, ε n < ‖x‖-R :=
          (tendsto_order.mp hl).2 _ (by linarith)
        have hez : (fun n => cut R (ε n) ‖x‖ * div F x) =ᶠ[atTop] fun _ => (0 : ℝ) := by
          filter_upwards [hev] with n hn
          rw [cut_zero R (ε n) ‖x‖ (hp n) (by linarith), zero_mul]
        simpa [indicator_of_notMem (show x ∉ closedBall (0 : E) R from by simpa using hx)]
          using tendsto_const_nhds.congr' hez.symm)
  have he (n) : (∫ x in K, cut R (ε n) ‖x‖ * div F x) =
      ∫ x, cut R (ε n) ‖x‖ * div F x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [cut_zero R (ε n) ‖x‖ (hp n) (by
      have hh : R+1 < ‖x‖ := by simpa [K, mem_closedBall, dist_zero_right] using hx
      linarith [hle n]), zero_mul]
  have hsub : closedBall (0 : E) R ⊆ K := closedBall_subset_closedBall (by linarith)
  have hind : (∫ x in K, (closedBall (0 : E) R).indicator (div F) x) =
      ∫ x in closedBall (0 : E) R, div F x := by
    rw [setIntegral_indicator measurableSet_closedBall, inter_eq_right.mpr hsub]
  have hae : closedBall (0 : E) R =ᵐ[volume] ball (0 : E) R := by
    have hz : ∀ᵐ x : E ∂volume, x ∉ sphere (0 : E) R := by
      rw [ae_iff]
      simpa [sphere, dist_zero_right] using Measure.addHaar_sphere (volume : Measure E) (0 : E) R
    filter_upwards [hz] with x hx
    simp only [mem_sphere, dist_zero_right] at hx
    apply propext
    change dist x 0 ≤ R ↔ dist x 0 < R
    simp only [dist_zero_right]
    exact ⟨fun h => lt_of_le_of_ne h hx, le_of_lt⟩
  simpa only [he, hind, setIntegral_congr_set hae, ε] using ht

lemma flux_limit {F : E → E} (hF : ContDiff ℝ 1 F) (R : ℝ) :
    Tendsto (fun n : ℕ => ∫ t in (0 : ℝ)..1,
      deriv Real.smoothTransition t * boundary F (R+1/(n+1:ℝ)-(1/(n+1:ℝ))*t)) atTop
      (𝓝 (boundary F R)) := by
  have hd : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv_one
  let G := fun ε : ℝ => ∫ t in (0 : ℝ)..1,
      deriv Real.smoothTransition t * boundary F (R+ε-ε*t)
  have hc : Continuous G := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (by exact (hd.comp continuous_snd).mul ((boundary_cont hF.continuous).comp (by fun_prop))) 0 1
  have hmass : (∫ t in (0 : ℝ)..1, deriv Real.smoothTransition t) = 1 := by
    rw [intervalIntegral.integral_deriv_eq_sub
      (fun _ _ => (Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero _) (hd.intervalIntegrable 0 1)]
    simp
  have hg : G 0 = boundary F R := by
    simp [G, intervalIntegral.integral_mul_const, hmass]
  simpa only [G, hg, Function.comp_def] using hc.continuousAt.tendsto.comp
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

end BallGauss

open BallGauss in
theorem solution
    (F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hF : ContDiff ℝ 1 F) (R : ℝ) (hR : 0 < R) :
    (∫ x in ball (0 : EuclideanSpace ℝ (Fin 3)) R,
      ∑ i : Fin 3, (fderiv ℝ F x (EuclideanSpace.single i 1)) i) =
    R ^ 2 * ∫ u : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      inner ℝ (F (R • u.1)) u.1 ∂((volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere) := by
  have ht := (flux_limit hF R).congr' (.of_forall fun (n : ℕ) =>
    (cutoff_fixed hF R (1/(n+1:ℝ)) hR (by positivity)).symm)
  exact tendsto_nhds_unique (cutoff_limit hF R hR) ht

