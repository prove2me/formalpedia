-- Prove2me | solution 1 for GenNewtonSubgrad.ProxReg.lemma_5_5
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T18:41:46.510767+00:00
-- url     : https://prove2.me/submissions/bebe8f6b-5146-41ac-8942-56bcd7833353

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_GenNewtonSubgrad_ProxReg_VarAnalysis

open Filter Topology MeasureTheory
open scoped InnerProductSpace NNReal ENNReal

section Helpers

open GenNewtonSubgrad.ProxReg

private lemma fderiv_gradient_symm {n : ℕ} {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    {B : Set (EuclideanSpace ℝ (Fin n))} (hB : IsOpen B)
    (hdiff : ∀ z ∈ B, DifferentiableAt ℝ φ z)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ B)
    (hFy : DifferentiableAt ℝ (gradient φ) y)
    (a b : EuclideanSpace ℝ (Fin n)) :
    ⟪fderiv ℝ (gradient φ) y a, b⟫_ℝ = ⟪a, fderiv ℝ (gradient φ) y b⟫_ℝ := by
  let T : EuclideanSpace ℝ (Fin n) →L[ℝ] StrongDual ℝ (EuclideanSpace ℝ (Fin n)) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).toContinuousLinearMap
  have hcomp : T ∘ gradient φ = fderiv ℝ φ := by
    funext z
    exact toDual_gradient
  have h1 : ∀ᶠ z in 𝓝 y, HasFDerivAt φ (fderiv ℝ φ z) z := by
    filter_upwards [hB.mem_nhds hy] with z hz
    exact (hdiff z hz).hasFDerivAt
  have h2 : HasFDerivAt (fderiv ℝ φ) (T.comp (fderiv ℝ (gradient φ) y)) y := by
    rw [← hcomp]
    exact T.hasFDerivAt.comp y hFy.hasFDerivAt
  have hsym := second_derivative_symmetric_of_eventually_of_real h1 h2 a b
  simp only [ContinuousLinearMap.comp_apply] at hsym
  change (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)) (fderiv ℝ (gradient φ) y a)) b =
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)) (fderiv ℝ (gradient φ) y b)) a at hsym
  simp only [InnerProductSpace.toDual_apply_apply] at hsym
  rw [hsym, real_inner_comm]

private lemma hasFDerivAt_regNormal_gph {n : ℕ}
    {F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {y : EuclideanSpace ℝ (Fin n)}
    (hFy : HasFDerivAt F A y)
    (hsymm : ∀ a b, ⟪A a, b⟫_ℝ = ⟪a, A b⟫_ℝ)
    (w : EuclideanSpace ℝ (Fin n)) :
    (A w, -w) ∈ regNormal (gph (sv F)) (y, F y) := by
  refine ⟨rfl, fun ε hε => ?_⟩
  have hε' : 0 < ε / (‖w‖ + 1) := div_pos hε (by positivity)
  have hlittle := hFy.isLittleO.bound hε'
  have hpull : ∀ᶠ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) in 𝓝 (y, F y),
      ‖F p.1 - F y - A (p.1 - y)‖ ≤ (ε / (‖w‖ + 1)) * ‖p.1 - y‖ :=
    (continuous_fst.continuousAt.tendsto (x := (y, F y))).eventually hlittle
  filter_upwards [hpull] with p hp hpgph
  have hp2 : p.2 = F p.1 := hpgph
  have hpair : pairInner (A w, -w) (p - (y, F y)) = -⟪w, F p.1 - F y - A (p.1 - y)⟫_ℝ := by
    simp only [pairInner, Prod.fst_sub, Prod.snd_sub, hp2, inner_neg_left, hsymm w (p.1 - y),
      inner_sub_right]
    ring
  rw [hpair]
  have hcs : -⟪w, F p.1 - F y - A (p.1 - y)⟫_ℝ ≤ ‖w‖ * ‖F p.1 - F y - A (p.1 - y)‖ :=
    (neg_le_abs _).trans (abs_real_inner_le_norm _ _)
  have hw_le : ‖w‖ * (ε / (‖w‖ + 1)) ≤ ε := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg w]
  calc -⟪w, F p.1 - F y - A (p.1 - y)⟫_ℝ
      ≤ ‖w‖ * ‖F p.1 - F y - A (p.1 - y)‖ := hcs
    _ ≤ ‖w‖ * ((ε / (‖w‖ + 1)) * ‖p.1 - y‖) := by gcongr
    _ = (‖w‖ * (ε / (‖w‖ + 1))) * ‖p.1 - y‖ := by ring
    _ ≤ ε * ‖p.1 - y‖ := by gcongr
    _ ≤ ε * ‖p - (y, F y)‖ := by
        gcongr
        exact norm_fst_le (p - (y, F y))

private lemma hasFDerivAt_coderiv_gph {n : ℕ}
    {F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {y : EuclideanSpace ℝ (Fin n)}
    (hFy : HasFDerivAt F A y)
    (hsymm : ∀ a b, ⟪A a, b⟫_ℝ = ⟪a, A b⟫_ℝ)
    (w : EuclideanSpace ℝ (Fin n)) :
    A w ∈ coderiv (sv F) y (F y) w := by
  refine ⟨rfl, fun _ => (y, F y), fun _ => (A w, -w), fun _ => rfl,
    tendsto_const_nhds, tendsto_const_nhds, fun _ => hasFDerivAt_regNormal_gph hFy hsymm w⟩

private lemma ae_slice_notMem_of_measure_zero {n : ℕ}
    {N : Set (EuclideanSpace ℝ (Fin n))} (hN : volume N = 0)
    (d x : EuclideanSpace ℝ (Fin n)) {t δ : ℝ} (hδ : 0 < δ) :
    ∃ z ∈ Metric.ball x δ, ∀ᵐ s ∂(volume.restrict (Set.Icc 0 t)), z + s • d ∉ N := by
  obtain ⟨M, hNM, hM_meas, hM_zero⟩ := exists_measurable_superset_of_null hN
  let f : EuclideanSpace ℝ (Fin n) → ℝ → ℝ≥0∞ := fun z s => M.indicator 1 (z + s • d)
  have hf_meas : Measurable (Function.uncurry f) := by
    have hadd : Measurable (fun p : EuclideanSpace ℝ (Fin n) × ℝ => p.1 + p.2 • d) :=
      (continuous_fst.add (continuous_snd.smul continuous_const)).measurable
    exact (measurable_const.indicator hM_meas).comp hadd
  let μI : Measure ℝ := volume.restrict (Set.Icc 0 t)
  have hswap : ∫⁻ z, (∫⁻ s, f z s ∂μI) ∂volume = ∫⁻ s, (∫⁻ z, f z s ∂volume) ∂μI :=
    lintegral_lintegral_swap hf_meas.aemeasurable
  have hinner_zero : ∀ s : ℝ, ∫⁻ z, f z s ∂volume = 0 := fun s => by
    change ∫⁻ z, M.indicator 1 (z + s • d) ∂volume = 0
    rw [lintegral_add_right_eq_self (fun z => M.indicator (1 : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) z) (s • d)]
    rw [lintegral_indicator_one hM_meas, hM_zero]
  have htotal : ∫⁻ z, (∫⁻ s, f z s ∂μI) ∂volume = 0 := by
    rw [hswap]
    simp [hinner_zero]
  have hmeas_outer : Measurable (fun z => ∫⁻ s, f z s ∂μI) := hf_meas.lintegral_prod_right'
  have hae_z : ∀ᵐ z ∂volume, ∫⁻ s, f z s ∂μI = 0 :=
    (lintegral_eq_zero_iff hmeas_outer).mp htotal
  have hball_ne : volume (Metric.ball x δ) ≠ 0 :=
    Metric.isOpen_ball.measure_ne_zero volume (Metric.nonempty_ball.mpr hδ)
  have hex : ∃ z ∈ Metric.ball x δ, ∫⁻ s, f z s ∂μI = 0 := by
    by_contra h
    push Not at h
    have hsub : Metric.ball x δ ⊆ {z | ∫⁻ s, f z s ∂μI ≠ 0} := fun z hz => h z hz
    have hzero : volume {z | ∫⁻ s, f z s ∂μI ≠ 0} = 0 := ae_iff.mp hae_z
    exact hball_ne (measure_mono_null hsub hzero)
  obtain ⟨z, hz_ball, hz_zero⟩ := hex
  refine ⟨z, hz_ball, ?_⟩
  have hmeas_z : Measurable (f z) := hf_meas.comp (measurable_const.prodMk measurable_id)
  have hae_s : ∀ᵐ s ∂μI, f z s = 0 := (lintegral_eq_zero_iff hmeas_z).mp hz_zero
  filter_upwards [hae_s] with s hs hmem
  have hM : z + s • d ∈ M := hNM hmem
  simp [f, Set.indicator_of_mem hM] at hs

private lemma mem_closure_convexHull_of_regNormal {n : ℕ}
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} {xbar : EuclideanSpace ℝ (Fin n)}
    {r₀ : ℝ} {L : ℝ≥0}
    (hdiff : ∀ y ∈ Metric.ball xbar r₀, DifferentiableAt ℝ φ y)
    (hlip : LipschitzOnWith L (gradient φ) (Metric.ball xbar r₀))
    {x u' w : EuclideanSpace ℝ (Fin n)} {ρ : ℝ}
    (hρ : 0 < ρ) (hBρ : Metric.ball x ρ ⊆ Metric.ball xbar r₀)
    (hreg : (u', -w) ∈ regNormal (gph (sv (gradient φ))) (x, gradient φ x)) :
    u' ∈ closure (convexHull ℝ
      {v | ∃ y ∈ Metric.ball x ρ, DifferentiableAt ℝ (gradient φ) y ∧
        v = fderiv ℝ (gradient φ) y w}) := by
  set F := gradient φ
  set B₀ := Metric.ball xbar r₀
  set S := {v | ∃ y ∈ Metric.ball x ρ, DifferentiableAt ℝ F y ∧ v = fderiv ℝ F y w}
  set K := closure (convexHull ℝ S)
  by_contra hu'
  have hK_conv : Convex ℝ K := (convex_convexHull ℝ S).closure
  have hK_closed : IsClosed K := isClosed_closure
  obtain ⟨f, β, hfK, hβu'⟩ := geometric_hahn_banach_closed_point hK_conv hK_closed hu'
  let d : EuclideanSpace ℝ (Fin n) := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm f
  have hf_eq : ∀ a : EuclideanSpace ℝ (Fin n), f a = ⟪a, d⟫_ℝ := fun a => by
    have := InnerProductSpace.toDual_symm_apply (x := a) (y := f)
    rw [real_inner_comm]
    exact this.symm
  have hβu'_inner : β < ⟪u', d⟫_ℝ := by rwa [← hf_eq u']
  have hK_inner : ∀ a ∈ K, ⟪a, d⟫_ℝ < β := fun a ha => by rw [← hf_eq a]; exact hfK a ha
  set α : ℝ := ⟪u', d⟫_ℝ - β
  have hα : 0 < α := sub_pos.mpr hβu'_inner
  -- Step 1: lower bound on ⟪w, F (x + t • d) - F x⟫ from regNormal
  set C_lip : ℝ := max 1 (L : ℝ)
  have hC_lip : 1 ≤ C_lip := le_max_left _ _
  have hL_le : (L : ℝ) ≤ C_lip := le_max_right _ _
  set ε : ℝ := α / (2 * (C_lip * ‖d‖ + 1))
  have hε : 0 < ε := div_pos hα (by positivity)
  have hxB₀ : x ∈ B₀ := hBρ (Metric.mem_ball_self hρ)
  have hF_contAt : ContinuousAt F x :=
    (hlip.continuousOn).continuousAt (Metric.isOpen_ball.mem_nhds hxB₀)
  have hreg_ev := hreg.2 ε hε
  have hmap_cont : ContinuousAt (fun z => (z, F z)) x := continuousAt_id.prodMk hF_contAt
  have hreg_x : ∀ᶠ z in 𝓝 x, pairInner (u', -w) ((z, F z) - (x, F x)) ≤ ε * ‖(z, F z) - (x, F x)‖ := by
    filter_upwards [hmap_cont.tendsto.eventually hreg_ev] with z hz
    exact hz rfl
  obtain ⟨η₁, hη₁_pos, hη₁⟩ := Metric.eventually_nhds_iff.mp hreg_x
  set η : ℝ := min η₁ ρ
  have hη_pos : 0 < η := lt_min hη₁_pos hρ
  set t : ℝ := η / (4 * (‖d‖ + 1))
  have ht_pos : 0 < t := div_pos hη_pos (by positivity)
  have htd_lt : t * ‖d‖ < η / 2 := by
    have h1 : ‖d‖ < ‖d‖ + 1 := lt_add_one _
    calc t * ‖d‖ = η / 4 * (‖d‖ / (‖d‖ + 1)) := by dsimp only [t]; field_simp
      _ ≤ η / 4 * 1 := by
          gcongr
          exact (div_le_one (by positivity)).mpr (le_of_lt h1)
      _ < η / 2 := by linarith
  have hxt_ball_η : x + t • d ∈ Metric.ball x η := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos ht_pos]
    linarith
  have hxt_ball_ρ : x + t • d ∈ Metric.ball x ρ :=
    Metric.ball_subset_ball (min_le_right _ _) hxt_ball_η
  have hxt_B₀ : x + t • d ∈ B₀ := hBρ hxt_ball_ρ
  have hreg_xt : pairInner (u', -w) ((x + t • d, F (x + t • d)) - (x, F x)) ≤
      ε * ‖(x + t • d, F (x + t • d)) - (x, F x)‖ :=
    hη₁ (lt_of_lt_of_le (Metric.mem_ball.mp hxt_ball_η) (min_le_left _ _))
  have hnorm_prod : ‖(x + t • d, F (x + t • d)) - (x, F x)‖ ≤ C_lip * (t * ‖d‖) := by
    rw [Prod.mk_sub_mk, Prod.norm_def]
    simp only [add_sub_cancel_left]
    have h1 : ‖t • d‖ = t * ‖d‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht_pos]
    have h2 : ‖F (x + t • d) - F x‖ ≤ (L : ℝ) * (t * ‖d‖) := by
      have := hlip.dist_le_mul (x + t • d) hxt_B₀ x hxB₀
      rw [dist_eq_norm, dist_eq_norm, add_sub_cancel_left, h1] at this
      exact this
    exact max_le (by rw [h1]; nlinarith [mul_nonneg ht_pos.le (norm_nonneg d)])
      (h2.trans (by gcongr))
  have hε_bound : ε * (C_lip * (t * ‖d‖)) ≤ (α / 2) * t := by
    have h1 : C_lip * ‖d‖ ≤ C_lip * ‖d‖ + 1 := by linarith
    have h2 : ε * (C_lip * ‖d‖) ≤ α / 2 := by
      simp only [ε]
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    calc ε * (C_lip * (t * ‖d‖)) = (ε * (C_lip * ‖d‖)) * t := by ring
      _ ≤ (α / 2) * t := by gcongr
  have hlower : (β + α / 2) * t ≤ ⟪w, F (x + t • d) - F x⟫_ℝ := by
    have hpair : pairInner (u', -w) ((x + t • d, F (x + t • d)) - (x, F x)) =
        t * ⟪u', d⟫_ℝ - ⟪w, F (x + t • d) - F x⟫_ℝ := by
      simp only [pairInner, Prod.mk_sub_mk, add_sub_cancel_left, inner_smul_right, inner_neg_left]
      ring
    rw [hpair] at hreg_xt
    have hprod_le : ε * ‖(x + t • d, F (x + t • d)) - (x, F x)‖ ≤ (α / 2) * t :=
      (mul_le_mul_of_nonneg_left hnorm_prod hε.le).trans hε_bound
    have hu'd : ⟪u', d⟫_ℝ = β + α := by simp [α]
    nlinarith
  -- Step 2: upper bound ⟪w, F (x + t • d) - F x⟫ ≤ β * t via Rademacher + Fubini + AC FTC
  let N : Set (EuclideanSpace ℝ (Fin n)) := {y ∈ B₀ | ¬ DifferentiableAt ℝ F y}
  have hN_zero : volume N = 0 := by
    have hrad := hlip.ae_differentiableWithinAt_of_mem (μ := volume)
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hrad] with y hy hmem
    exact hmem.2 ((hy hmem.1).differentiableAt (Metric.isOpen_ball.mem_nhds hmem.1))
  have hstep_z : ∀ k : ℕ, ∃ z ∈ Metric.ball x (min (ρ / 2) ((k + 1 : ℝ)⁻¹)),
      ⟪w, F (z + t • d) - F z⟫_ℝ ≤ β * t := by
    intro k
    have hδk : 0 < min (ρ / 2) ((k + 1 : ℝ)⁻¹) := lt_min (half_pos hρ) (by positivity)
    obtain ⟨z, hz_ball, hz_ae⟩ := ae_slice_notMem_of_measure_zero hN_zero d x (t := t) hδk
    refine ⟨z, hz_ball, ?_⟩
    have hz_seg : ∀ s ∈ Set.Icc 0 t, z + s • d ∈ Metric.ball x ρ := fun s hs => by
      rw [Metric.mem_ball, dist_eq_norm]
      have hzx : ‖z - x‖ < ρ / 2 :=
        lt_of_lt_of_le (Metric.mem_ball.mp hz_ball) (min_le_left _ _)
      have hsd : ‖s • d‖ ≤ t * ‖d‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
        exact mul_le_mul_of_nonneg_right hs.2 (norm_nonneg d)
      have htri : ‖z + s • d - x‖ ≤ ‖z - x‖ + ‖s • d‖ := by
        simpa [add_sub_right_comm] using norm_add_le (z - x) (s • d)
      have hηρ : η / 2 ≤ ρ / 2 := by linarith [min_le_right η₁ ρ]
      linarith
    let h : ℝ → ℝ := fun s => ⟪w, F (z + s • d)⟫_ℝ
    have hh_lip : LipschitzOnWith (‖w‖₊ * L * ‖d‖₊) h (Set.uIcc 0 t) := by
      rw [Set.uIcc_of_le ht_pos.le]
      intro s₁ hs₁ s₂ hs₂
      rw [edist_dist, edist_dist]
      have hdist : dist (h s₁) (h s₂) ≤ (‖w‖ * (L : ℝ) * ‖d‖) * dist s₁ s₂ := by
        simp only [h, Real.dist_eq, ← inner_sub_right]
        calc |⟪w, F (z + s₁ • d) - F (z + s₂ • d)⟫_ℝ|
            ≤ ‖w‖ * ‖F (z + s₁ • d) - F (z + s₂ • d)‖ := abs_real_inner_le_norm _ _
          _ ≤ ‖w‖ * ((L : ℝ) * ‖(z + s₁ • d) - (z + s₂ • d)‖) := by
              gcongr
              have := hlip.dist_le_mul (z + s₁ • d) (hBρ (hz_seg s₁ hs₁))
                (z + s₂ • d) (hBρ (hz_seg s₂ hs₂))
              simpa [dist_eq_norm] using this
          _ = ‖w‖ * ((L : ℝ) * (|s₁ - s₂| * ‖d‖)) := by
              congr 2
              rw [add_sub_add_left_eq_sub, ← sub_smul, norm_smul, Real.norm_eq_abs]
          _ = (‖w‖ * (L : ℝ) * ‖d‖) * |s₁ - s₂| := by ring
      calc ENNReal.ofReal (dist (h s₁) (h s₂))
          ≤ ENNReal.ofReal ((‖w‖ * (L : ℝ) * ‖d‖) * dist s₁ s₂) := ENNReal.ofReal_le_ofReal hdist
        _ = (↑(‖w‖₊ * L * ‖d‖₊) : ℝ≥0∞) * ENNReal.ofReal (dist s₁ s₂) := by
            have hcoe : (‖w‖ * (L : ℝ) * ‖d‖) = ((‖w‖₊ * L * ‖d‖₊ : ℝ≥0) : ℝ) := by
              simp [coe_nnnorm]
            rw [ENNReal.ofReal_mul (by positivity), hcoe, ENNReal.ofReal_coe_nnreal]
    have hh_ac : AbsolutelyContinuousOnInterval h 0 t := hh_lip.absolutelyContinuousOnInterval
    have hftc : ∫ s in (0 : ℝ)..t, deriv h s = h t - h 0 := hh_ac.integral_deriv_eq_sub
    have hae_deriv : deriv h ≤ᵐ[volume.restrict (Set.Icc 0 t)] fun _ => β := by
      filter_upwards [ae_restrict_mem measurableSet_Icc, hz_ae] with s hs hsN
      have hy_ball : z + s • d ∈ Metric.ball x ρ := hz_seg s hs
      have hy_B₀ : z + s • d ∈ B₀ := hBρ hy_ball
      have hy_diff : DifferentiableAt ℝ F (z + s • d) := by
        by_contra hnd
        exact hsN ⟨hy_B₀, hnd⟩
      have hline : HasDerivAt (fun r : ℝ => z + r • d) d s := by
        simpa using (hasDerivAt_id s).smul_const d |>.const_add z
      have hFline : HasDerivAt (fun r : ℝ => F (z + r • d)) (fderiv ℝ F (z + s • d) d) s := by
        change HasDerivAt (F ∘ fun r : ℝ => z + r • d) (fderiv ℝ F (z + s • d) d) s
        exact hy_diff.hasFDerivAt.comp_hasDerivAt s hline
      have hh_deriv : HasDerivAt h ⟪w, fderiv ℝ F (z + s • d) d⟫_ℝ s := by
        change HasDerivAt ((innerSL ℝ w) ∘ fun r : ℝ => F (z + r • d))
          ((innerSL ℝ w) (fderiv ℝ F (z + s • d) d)) s
        exact (innerSL ℝ w).hasFDerivAt.comp_hasDerivAt s hFline
      rw [hh_deriv.deriv]
      have hsymm := fderiv_gradient_symm Metric.isOpen_ball hdiff hy_B₀ hy_diff w d
      rw [← hsymm]
      have hmemK : fderiv ℝ F (z + s • d) w ∈ K :=
        subset_closure (subset_convexHull ℝ S ⟨z + s • d, hy_ball, hy_diff, rfl⟩)
      exact le_of_lt (hK_inner _ hmemK)
    have hmono : ∫ s in (0 : ℝ)..t, deriv h s ≤ ∫ _ in (0 : ℝ)..t, β :=
      intervalIntegral.integral_mono_ae_restrict ht_pos.le hh_ac.intervalIntegrable_deriv
        intervalIntegrable_const hae_deriv
    rw [hftc, intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hmono
    have hsub : h t - h 0 = ⟪w, F (z + t • d) - F z⟫_ℝ := by
      simp [h, inner_sub_right]
    linarith
  choose zs hzs_ball hzs_le using hstep_z
  have hzs_tendsto : Tendsto zs atTop (𝓝 x) := by
    rw [Metric.tendsto_atTop]
    intro r hr
    obtain ⟨N₀, hN₀⟩ := exists_nat_one_div_lt hr
    refine ⟨N₀, fun k hk => ?_⟩
    have h1 : dist (zs k) x < min (ρ / 2) ((k + 1 : ℝ)⁻¹) := Metric.mem_ball.mp (hzs_ball k)
    have h2 : ((k + 1 : ℝ)⁻¹) ≤ ((N₀ + 1 : ℝ)⁻¹) := by
      gcongr
    have h3 : ((N₀ + 1 : ℝ)⁻¹) < r := by simpa [one_div] using hN₀
    exact lt_trans (lt_of_lt_of_le (lt_of_lt_of_le h1 (min_le_right _ _)) h2) h3
  have hF_contAt_xt : ContinuousAt F (x + t • d) :=
    (hlip.continuousOn).continuousAt (Metric.isOpen_ball.mem_nhds hxt_B₀)
  have hval_tendsto : Tendsto (fun k => ⟪w, F (zs k + t • d) - F (zs k)⟫_ℝ) atTop
      (𝓝 ⟪w, F (x + t • d) - F x⟫_ℝ) := by
    have h1 : Tendsto (fun k => F (zs k + t • d)) atTop (𝓝 (F (x + t • d))) :=
      hF_contAt_xt.tendsto.comp (hzs_tendsto.add tendsto_const_nhds)
    have h2 : Tendsto (fun k => F (zs k)) atTop (𝓝 (F x)) :=
      hF_contAt.tendsto.comp hzs_tendsto
    exact tendsto_const_nhds.inner (h1.sub h2)
  have hupper : ⟪w, F (x + t • d) - F x⟫_ℝ ≤ β * t :=
    le_of_tendsto hval_tendsto (Eventually.of_forall hzs_le)
  nlinarith

private lemma semismooth_at_diff_pts {n : ℕ}
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} {xbar : EuclideanSpace ℝ (Fin n)}
    {r₀ : ℝ} {L : ℝ≥0} (hr₀ : 0 < r₀)
    (hdiff : ∀ y ∈ Metric.ball xbar r₀, DifferentiableAt ℝ φ y)
    (hlip : LipschitzOnWith L (gradient φ) (Metric.ball xbar r₀))
    (hss : IsSemismoothStar (sv (gradient φ)) xbar (gradient φ xbar)) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ δ < r₀ ∧
      ∀ y ∈ Metric.closedBall xbar δ, DifferentiableAt ℝ (gradient φ) y →
        ‖gradient φ y - gradient φ xbar - fderiv ℝ (gradient φ) y (y - xbar)‖ ≤
          ε * ‖y - xbar‖ := by
  set F := gradient φ
  intro ε hε
  by_contra h
  push Not at h
  have hseq : ∀ k : ℕ, ∃ y ∈ Metric.closedBall xbar (min (r₀ / 2) ((k + 1 : ℝ)⁻¹)),
      DifferentiableAt ℝ F y ∧
      ε * ‖y - xbar‖ < ‖F y - F xbar - fderiv ℝ F y (y - xbar)‖ := by
    intro k
    have hδk_pos : 0 < min (r₀ / 2) ((k + 1 : ℝ)⁻¹) := lt_min (half_pos hr₀) (by positivity)
    have hδk_lt : min (r₀ / 2) ((k + 1 : ℝ)⁻¹) < r₀ :=
      lt_of_le_of_lt (min_le_left _ _) (half_lt_self hr₀)
    exact h (min (r₀ / 2) ((k + 1 : ℝ)⁻¹)) hδk_pos hδk_lt
  choose y hy_ball hy_diff hy_gt using hseq
  have hy_B₀ : ∀ k, y k ∈ Metric.ball xbar r₀ := fun k =>
    Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp (hy_ball k))
      (lt_of_le_of_lt (min_le_left _ _) (half_lt_self hr₀)))
  have ht_pos : ∀ k, 0 < ‖y k - xbar‖ := fun k => by
    by_contra h0
    have heq : y k = xbar := sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (not_lt.mp h0) (norm_nonneg _)))
    have := hy_gt k
    simp [heq] at this
  let ts : ℕ → ℝ := fun k => ‖y k - xbar‖
  let us : ℕ → EuclideanSpace ℝ (Fin n) := fun k => (ts k)⁻¹ • (y k - xbar)
  let vs : ℕ → EuclideanSpace ℝ (Fin n) := fun k => (ts k)⁻¹ • (F (y k) - F xbar)
  let As : ℕ → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) := fun k => fderiv ℝ F (y k)
  have hts_tendsto : Tendsto ts atTop (𝓝 0) := by
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    have h1 : dist (y k) xbar ≤ min (r₀ / 2) ((k + 1 : ℝ)⁻¹) := Metric.mem_closedBall.mp (hy_ball k)
    simpa [ts, dist_eq_norm, one_div] using h1.trans (min_le_right _ _)
  have hus_norm : ∀ k, ‖us k‖ = 1 := fun k => by
    have htk : 0 < ts k := ht_pos k
    simp only [us, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos htk]
    exact inv_mul_cancel₀ htk.ne'
  have hvs_norm : ∀ k, ‖vs k‖ ≤ (L : ℝ) := fun k => by
    have htk : 0 < ts k := ht_pos k
    simp only [vs, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos htk]
    have h1 := hlip.dist_le_mul (y k) (hy_B₀ k) xbar (Metric.mem_ball_self hr₀)
    rw [dist_eq_norm, dist_eq_norm] at h1
    calc (ts k)⁻¹ * ‖F (y k) - F xbar‖
        ≤ (ts k)⁻¹ * ((L : ℝ) * ts k) := by gcongr
      _ = (L : ℝ) := by field_simp [htk.ne']
  have hAs_norm : ∀ k, ‖As k‖ ≤ (L : ℝ) := fun k =>
    norm_fderiv_le_of_lipschitzOn ℝ (Metric.isOpen_ball.mem_nhds (hy_B₀ k)) hlip
  let P : ℕ → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ×
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
    fun k => (us k, vs k, As k)
  have hP_bdd : ∀ k, P k ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n) ×
      EuclideanSpace ℝ (Fin n) × (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
      (max 1 (L : ℝ)) := fun k => by
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Prod.norm_def]
    refine max_le ?_ (max_le ?_ ?_)
    · rw [hus_norm k]; exact le_max_left _ _
    · exact (hvs_norm k).trans (le_max_right _ _)
    · exact (hAs_norm k).trans (le_max_right _ _)
  have hcomp : IsCompact (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n) ×
      EuclideanSpace ℝ (Fin n) × (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
      (max 1 (L : ℝ))) := isCompact_closedBall _ _
  obtain ⟨⟨u, v, A⟩, _, σ, hσ_mono, hσ_tendsto⟩ := hcomp.tendsto_subseq hP_bdd
  have hu_tend : Tendsto (us ∘ σ) atTop (𝓝 u) :=
    (continuous_fst.tendsto _).comp hσ_tendsto
  have hv_tend : Tendsto (vs ∘ σ) atTop (𝓝 v) :=
    (continuous_fst.comp continuous_snd |>.tendsto _).comp hσ_tendsto
  have hA_tend : Tendsto (As ∘ σ) atTop (𝓝 A) :=
    (continuous_snd.comp continuous_snd |>.tendsto _).comp hσ_tendsto
  have ht_tend : Tendsto (ts ∘ σ) atTop (𝓝 0) :=
    hts_tendsto.comp hσ_mono.tendsto_atTop
  have hAu_tend : Tendsto (fun k => As (σ k) (us (σ k))) atTop (𝓝 (A u)) :=
    (isBoundedBilinearMap_apply.continuous.tendsto (A, u)).comp (hA_tend.prodMk_nhds hu_tend)
  have herr_gt : ∀ k, ε < ‖vs (σ k) - As (σ k) (us (σ k))‖ := fun k => by
    have hgt := hy_gt (σ k)
    have ht' : 0 < ts (σ k) := ht_pos (σ k)
    have heq : vs (σ k) - As (σ k) (us (σ k)) =
        (ts (σ k))⁻¹ • (F (y (σ k)) - F xbar - As (σ k) (y (σ k) - xbar)) := by
      dsimp only [vs, us]
      rw [map_smul, ← smul_sub]
    rw [heq, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht']
    rw [inv_mul_eq_div, lt_div_iff₀ ht']
    simpa [ts, mul_comm] using hgt
  have herr_ge : ε ≤ ‖v - A u‖ :=
    ge_of_tendsto (hv_tend.sub hAu_tend).norm (Eventually.of_forall fun k => (herr_gt k).le)
  have hA_symm : ∀ a b, ⟪A a, b⟫_ℝ = ⟪a, A b⟫_ℝ := fun a b => by
    have h1 : Tendsto (fun k => ⟪As (σ k) a, b⟫_ℝ) atTop (𝓝 ⟪A a, b⟫_ℝ) :=
      ((isBoundedBilinearMap_apply.continuous.tendsto (A, a)).comp
        (hA_tend.prodMk_nhds tendsto_const_nhds)).inner tendsto_const_nhds
    have h2 : Tendsto (fun k => ⟪a, As (σ k) b⟫_ℝ) atTop (𝓝 ⟪a, A b⟫_ℝ) :=
      tendsto_const_nhds.inner ((isBoundedBilinearMap_apply.continuous.tendsto (A, b)).comp
        (hA_tend.prodMk_nhds tendsto_const_nhds))
    have heq : (fun k => ⟪As (σ k) a, b⟫_ℝ) = (fun k => ⟪a, As (σ k) b⟫_ℝ) := by
      funext k
      exact fderiv_gradient_symm Metric.isOpen_ball hdiff (hy_B₀ (σ k)) (hy_diff (σ k)) a b
    rw [heq] at h1
    exact tendsto_nhds_unique h1 h2
  set w : EuclideanSpace ℝ (Fin n) := v - A u
  have hmem_dir : A w ∈ dirCoderiv (sv F) xbar (F xbar) u v w := by
    refine ⟨rfl, ts ∘ σ, fun k => (us (σ k), vs (σ k)), fun k => (As (σ k) w, -w),
      fun k => ht_pos (σ k), ht_tend, hu_tend.prodMk_nhds hv_tend, ?_, ?_⟩
    · have hAw : Tendsto (fun k => As (σ k) w) atTop (𝓝 (A w)) :=
        (isBoundedBilinearMap_apply.continuous.tendsto (A, w)).comp
          (hA_tend.prodMk_nhds tendsto_const_nhds)
      exact hAw.prodMk_nhds tendsto_const_nhds
    · intro k
      dsimp only [Function.comp_apply]
      have htk : ts (σ k) ≠ 0 := (ht_pos (σ k)).ne'
      have hpt : (xbar, F xbar) + (ts (σ k)) • (us (σ k), vs (σ k)) = (y (σ k), F (y (σ k))) := by
        refine Prod.ext ?_ ?_
        · simp only [Prod.fst_add, Prod.smul_fst, us, smul_smul, mul_inv_cancel₀ htk, one_smul,
            add_sub_cancel]
        · simp only [Prod.snd_add, Prod.smul_snd, vs, smul_smul, mul_inv_cancel₀ htk, one_smul,
            add_sub_cancel]
      rw [hpt]
      exact hasFDerivAt_regNormal_gph (hy_diff (σ k)).hasFDerivAt
        (fderiv_gradient_symm Metric.isOpen_ball hdiff (hy_B₀ (σ k)) (hy_diff (σ k))) w
  have hss_eq : ⟪A w, u⟫_ℝ = ⟪w, v⟫_ℝ := hss.2 u v w (A w) hmem_dir
  rw [hA_symm w u] at hss_eq
  have hw0 : ⟪w, w⟫_ℝ = 0 := by
    change ⟪w, v - A u⟫_ℝ = 0
    rw [inner_sub_right, hss_eq, sub_self]
  have hwnorm0 : ‖w‖ = 0 := by
    rw [real_inner_self_eq_norm_sq] at hw0
    exact sq_eq_zero_iff.mp hw0
  linarith

end Helpers

open GenNewtonSubgrad.ProxReg

theorem solution {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → ℝ) (xbar : EuclideanSpace ℝ (Fin n))
    (hφ : IsC11Around φ xbar) :
    IsSemismoothStar (sv (gradient φ)) xbar (gradient φ xbar) ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Metric.closedBall xbar δ,
        ∀ v ∈ coderiv (sv (gradient φ)) x (gradient φ x) (x - xbar),
          ‖gradient φ x - gradient φ xbar - v‖ ≤ ε * ‖x - xbar‖ := by
  set F := gradient φ
  obtain ⟨U, hU_nhds, hU_diff, L, hU_lip⟩ := hφ
  obtain ⟨r₀, hr₀, hB₀_sub⟩ := Metric.mem_nhds_iff.mp hU_nhds
  have hdiff : ∀ y ∈ Metric.ball xbar r₀, DifferentiableAt ℝ φ y :=
    fun y hy => hU_diff y (hB₀_sub hy)
  have hlip : LipschitzOnWith L F (Metric.ball xbar r₀) := hU_lip.mono hB₀_sub
  constructor
  · -- Forward direction: IsSemismoothStar → o(‖x - xbar‖) bound
    intro hss ε hε
    obtain ⟨δ₁, hδ₁_pos, hδ₁_lt, hdiff_est⟩ :=
      semismooth_at_diff_pts hr₀ hdiff hlip hss (ε / 2) (half_pos hε)
    set δ : ℝ := δ₁ / 2
    have hδ_pos : 0 < δ := half_pos hδ₁_pos
    refine ⟨δ, hδ_pos, fun x hx v hv => ?_⟩
    obtain ⟨_, zs, as, hzs_gph, hzs_tend, has_tend, hreg_k⟩ := hv
    let xs : ℕ → EuclideanSpace ℝ (Fin n) := fun k => (zs k).1
    let vs : ℕ → EuclideanSpace ℝ (Fin n) := fun k => (as k).1
    let ws : ℕ → EuclideanSpace ℝ (Fin n) := fun k => -(as k).2
    have hzs_eq : ∀ k, zs k = (xs k, F (xs k)) := fun k => by
      have h1 : (zs k).2 = F (zs k).1 := hzs_gph k
      exact Prod.ext rfl h1
    have has_eq : ∀ k, as k = (vs k, -ws k) := fun k => by
      exact Prod.ext rfl (by simp [ws])
    have hxs_tend : Tendsto xs atTop (𝓝 x) := (continuous_fst.tendsto _).comp hzs_tend
    have hvs_tend : Tendsto vs atTop (𝓝 v) := (continuous_fst.tendsto _).comp has_tend
    have hws_tend : Tendsto ws atTop (𝓝 (x - xbar)) := by
      have h1 : Tendsto (fun k => (as k).2) atTop (𝓝 (-(x - xbar))) :=
        (continuous_snd.tendsto _).comp has_tend
      simpa [ws] using h1.neg
    have hx_ball : x ∈ Metric.ball xbar δ₁ :=
      Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hx) (half_lt_self hδ₁_pos))
    have hxs_ev : ∀ᶠ k in atTop, xs k ∈ Metric.ball xbar δ₁ :=
      hxs_tend.eventually (Metric.isOpen_ball.mem_nhds hx_ball)
    have hbound_k : ∀ᶠ k in atTop,
        ‖F (xs k) - F xbar - vs k‖ ≤ (ε / 2) * ‖xs k - xbar‖ + (L : ℝ) * ‖xs k - xbar - ws k‖ := by
      filter_upwards [hxs_ev] with k hk
      set ρ_max : ℝ := δ₁ - dist (xs k) xbar
      have hρ_max_pos : 0 < ρ_max := sub_pos.mpr (Metric.mem_ball.mp hk)
      have hfor_ρ : ∀ ρ : ℝ, 0 < ρ → ρ < ρ_max →
          ‖F (xs k) - F xbar - vs k‖ ≤
            (ε / 2) * ‖xs k - xbar‖ + (L : ℝ) * ‖xs k - xbar - ws k‖ + (2 * (L : ℝ) + ε / 2) * ρ := by
        intro ρ hρ_pos hρ_lt
        have hBρ_δ₁ : Metric.ball (xs k) ρ ⊆ Metric.ball xbar δ₁ := fun y hy => by
          rw [Metric.mem_ball] at hy ⊢
          linarith [dist_triangle y (xs k) xbar]
        have hBρ_B₀ : Metric.ball (xs k) ρ ⊆ Metric.ball xbar r₀ :=
          hBρ_δ₁.trans (Metric.ball_subset_ball hδ₁_lt.le)
        have hreg_k' : (vs k, -ws k) ∈ regNormal (gph (sv F)) (xs k, F (xs k)) := by
          rw [← has_eq k, ← hzs_eq k]; exact hreg_k k
        have hmem_cl := mem_closure_convexHull_of_regNormal hdiff hlip hρ_pos hBρ_B₀ hreg_k'
        set M : ℝ := (ε / 2) * ‖xs k - xbar‖ + (L : ℝ) * ‖xs k - xbar - ws k‖ +
          (2 * (L : ℝ) + ε / 2) * ρ
        have hsub : {u | ∃ y ∈ Metric.ball (xs k) ρ, DifferentiableAt ℝ F y ∧
            u = fderiv ℝ F y (ws k)} ⊆ Metric.closedBall (F (xs k) - F xbar) M := by
          rintro u ⟨y, hy_ball, hy_diff, rfl⟩
          rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev]
          have hy_δ₁ : y ∈ Metric.closedBall xbar δ₁ :=
            Metric.ball_subset_closedBall (hBρ_δ₁ hy_ball)
          have hy_B₀ : y ∈ Metric.ball xbar r₀ := hBρ_B₀ hy_ball
          have hx_B₀ : xs k ∈ Metric.ball xbar r₀ :=
            Metric.ball_subset_ball hδ₁_lt.le hk
          have h1 : ‖F (xs k) - F y‖ ≤ (L : ℝ) * ρ := by
            have := hlip.dist_le_mul (xs k) hx_B₀ y hy_B₀
            rw [dist_eq_norm] at this
            exact this.trans (mul_le_mul_of_nonneg_left (by rw [dist_comm]; exact (Metric.mem_ball.mp hy_ball).le) L.coe_nonneg)
          have h2 : ‖F y - F xbar - fderiv ℝ F y (y - xbar)‖ ≤ (ε / 2) * (‖xs k - xbar‖ + ρ) := by
            have h2a := hdiff_est y hy_δ₁ hy_diff
            have h2b : ‖y - xbar‖ ≤ ‖xs k - xbar‖ + ρ := by
              have htri := dist_triangle y (xs k) xbar
              have hy_dist : ‖y - xs k‖ < ρ := by simpa [dist_eq_norm] using Metric.mem_ball.mp hy_ball
              rw [dist_eq_norm, dist_eq_norm, dist_eq_norm] at htri
              linarith
            exact h2a.trans (mul_le_mul_of_nonneg_left h2b (half_pos hε).le)
          have hDf_le : ‖fderiv ℝ F y‖ ≤ (L : ℝ) :=
            norm_fderiv_le_of_lipschitzOn ℝ (Metric.isOpen_ball.mem_nhds hy_B₀) hlip
          have h3 : ‖fderiv ℝ F y (y - xs k)‖ ≤ (L : ℝ) * ρ :=
            (ContinuousLinearMap.le_opNorm _ _).trans
              (mul_le_mul hDf_le (by simpa [dist_eq_norm] using (Metric.mem_ball.mp hy_ball).le)
                (norm_nonneg _) L.coe_nonneg)
          have h4 : ‖fderiv ℝ F y (xs k - xbar - ws k)‖ ≤ (L : ℝ) * ‖xs k - xbar - ws k‖ :=
            (ContinuousLinearMap.le_opNorm _ _).trans
              (mul_le_mul_of_nonneg_right hDf_le (norm_nonneg _))
          have hsplit : F (xs k) - F xbar - fderiv ℝ F y (ws k) =
              (F (xs k) - F y) + (F y - F xbar - fderiv ℝ F y (y - xbar)) +
              fderiv ℝ F y (y - xs k) + fderiv ℝ F y (xs k - xbar - ws k) := by
            have hlin : fderiv ℝ F y (y - xbar) - fderiv ℝ F y (y - xs k) -
                fderiv ℝ F y (xs k - xbar - ws k) = fderiv ℝ F y (ws k) := by
              rw [← map_sub, ← map_sub]
              congr 1
              abel
            rw [← hlin]
            abel
          rw [hsplit]
          have htri := norm_add_le ((F (xs k) - F y) + (F y - F xbar - fderiv ℝ F y (y - xbar)) +
            fderiv ℝ F y (y - xs k)) (fderiv ℝ F y (xs k - xbar - ws k))
          have htri2 := norm_add_le ((F (xs k) - F y) + (F y - F xbar - fderiv ℝ F y (y - xbar)))
            (fderiv ℝ F y (y - xs k))
          have htri3 := norm_add_le (F (xs k) - F y) (F y - F xbar - fderiv ℝ F y (y - xbar))
          dsimp only [M]
          linarith
        have hball_mem : vs k ∈ Metric.closedBall (F (xs k) - F xbar) M :=
          closure_minimal (convexHull_min hsub (convex_closedBall _ _)) Metric.isClosed_closedBall hmem_cl
        simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hball_mem
      -- Send ρ → 0⁺
      by_contra hgt
      push Not at hgt
      set gap := ‖F (xs k) - F xbar - vs k‖ -
        ((ε / 2) * ‖xs k - xbar‖ + (L : ℝ) * ‖xs k - xbar - ws k‖)
      have hgap : 0 < gap := sub_pos.mpr hgt
      set ρ := min (ρ_max / 2) (gap / (2 * (2 * (L : ℝ) + ε / 2 + 1)))
      have hρ_pos : 0 < ρ := lt_min (half_pos hρ_max_pos) (div_pos hgap (by positivity))
      have hρ_lt : ρ < ρ_max := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hρ_max_pos)
      have hle := hfor_ρ ρ hρ_pos hρ_lt
      have hρ_gap : (2 * (L : ℝ) + ε / 2) * ρ ≤ gap / 2 := by
        have h1 : ρ ≤ gap / (2 * (2 * (L : ℝ) + ε / 2 + 1)) := min_le_right _ _
        have h2 : (2 * (L : ℝ) + ε / 2) * (gap / (2 * (2 * (L : ℝ) + ε / 2 + 1))) ≤ gap / 2 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith [L.coe_nonneg]
        exact (mul_le_mul_of_nonneg_left h1 (by positivity)).trans h2
      dsimp only [gap] at hρ_gap
      linarith
    have hx_B₀ : x ∈ Metric.ball xbar r₀ := Metric.ball_subset_ball hδ₁_lt.le hx_ball
    have hF_contAt : ContinuousAt F x :=
      hlip.continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds hx_B₀)
    have hlhs_tend : Tendsto (fun k => ‖F (xs k) - F xbar - vs k‖) atTop
        (𝓝 ‖F x - F xbar - v‖) :=
      ((hF_contAt.tendsto.comp hxs_tend).sub tendsto_const_nhds |>.sub hvs_tend).norm
    have hrhs_tend : Tendsto (fun k => (ε / 2) * ‖xs k - xbar‖ + (L : ℝ) * ‖xs k - xbar - ws k‖)
        atTop (𝓝 ((ε / 2) * ‖x - xbar‖ + (L : ℝ) * ‖x - xbar - (x - xbar)‖)) :=
      (tendsto_const_nhds.mul (hxs_tend.sub tendsto_const_nhds).norm).add
        (tendsto_const_nhds.mul ((hxs_tend.sub tendsto_const_nhds).sub hws_tend).norm)
    have hlim := le_of_tendsto_of_tendsto hlhs_tend hrhs_tend hbound_k
    simp only [sub_self, norm_zero, mul_zero, add_zero] at hlim
    nlinarith [norm_nonneg (x - xbar)]
  · -- Backward direction: o(‖x - xbar‖) bound → IsSemismoothStar
    intro hrhs
    refine ⟨rfl, fun u v w u' hu' => ?_⟩
    obtain ⟨_, ts, ds, as, hts_pos, hts_tend, hds_tend, has_tend, hreg_k⟩ := hu'
    let us : ℕ → EuclideanSpace ℝ (Fin n) := fun k => (ds k).1
    let vs : ℕ → EuclideanSpace ℝ (Fin n) := fun k => (ds k).2
    let u's : ℕ → EuclideanSpace ℝ (Fin n) := fun k => (as k).1
    let ws : ℕ → EuclideanSpace ℝ (Fin n) := fun k => -(as k).2
    let xs : ℕ → EuclideanSpace ℝ (Fin n) := fun k => xbar + ts k • us k
    have hus_tend : Tendsto us atTop (𝓝 u) := (continuous_fst.tendsto _).comp hds_tend
    have hvs_tend : Tendsto vs atTop (𝓝 v) := (continuous_snd.tendsto _).comp hds_tend
    have hu's_tend : Tendsto u's atTop (𝓝 u') := (continuous_fst.tendsto _).comp has_tend
    have hws_tend : Tendsto ws atTop (𝓝 w) := by
      have h1 : Tendsto (fun k => (as k).2) atTop (𝓝 (-w)) := (continuous_snd.tendsto _).comp has_tend
      simpa [ws] using h1.neg
    have hxs_gph : ∀ k, F (xs k) = F xbar + ts k • vs k := fun k =>
      (hreg_k k).1.symm
    have hxs_tend : Tendsto xs atTop (𝓝 xbar) := by
      have : Tendsto (fun k => xbar + ts k • us k) atTop (𝓝 (xbar + (0 : ℝ) • u)) :=
        tendsto_const_nhds.add (hts_tend.smul hus_tend)
      simpa [xs] using this
    have hall : ∀ ε : ℝ, 0 < ε → |⟪u', u⟫_ℝ - ⟪w, v⟫_ℝ| ≤ ε * (‖w‖ * ‖u‖) := by
      intro ε hε
      obtain ⟨δ, hδ_pos, hδ_est⟩ := hrhs ε hε
      set r₁ : ℝ := min δ r₀
      have hr₁_pos : 0 < r₁ := lt_min hδ_pos hr₀
      have hxs_ev : ∀ᶠ k in atTop, xs k ∈ Metric.ball xbar r₁ :=
        hxs_tend.eventually (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr₁_pos))
      have hbound_k : ∀ᶠ k in atTop, |⟪u's k, us k⟫_ℝ - ⟪ws k, vs k⟫_ℝ| ≤ ε * (‖ws k‖ * ‖us k‖) := by
        filter_upwards [hxs_ev] with k hk
        set ρ_max : ℝ := r₁ - dist (xs k) xbar
        have hρ_max_pos : 0 < ρ_max := sub_pos.mpr (Metric.mem_ball.mp hk)
        have hfor_ρ : ∀ ρ : ℝ, 0 < ρ → ρ < ρ_max →
            |⟪u's k, xs k - xbar⟫_ℝ - ⟪ws k, F (xs k) - F xbar⟫_ℝ| ≤
              ‖ws k‖ * (ε * ‖xs k - xbar‖ + (2 * (L : ℝ) + ε) * ρ) := by
          intro ρ hρ_pos hρ_lt
          have hBρ_r₁ : Metric.ball (xs k) ρ ⊆ Metric.ball xbar r₁ := fun y hy => by
            rw [Metric.mem_ball] at hy ⊢
            linarith [dist_triangle y (xs k) xbar]
          have hBρ_B₀ : Metric.ball (xs k) ρ ⊆ Metric.ball xbar r₀ :=
            hBρ_r₁.trans (Metric.ball_subset_ball (min_le_right _ _))
          have hreg_k' : (u's k, -ws k) ∈ regNormal (gph (sv F)) (xs k, F (xs k)) := by
            have h1 : (xbar, F xbar) + ts k • ds k = (xs k, F (xs k)) :=
              Prod.ext rfl (hxs_gph k).symm
            have h2 : as k = (u's k, -ws k) := Prod.ext rfl (by simp [ws])
            rw [← h2, ← h1]
            exact hreg_k k
          have hmem_cl := mem_closure_convexHull_of_regNormal hdiff hlip hρ_pos hBρ_B₀ hreg_k'
          set M : ℝ := ‖ws k‖ * (ε * ‖xs k - xbar‖ + (2 * (L : ℝ) + ε) * ρ)
          set T : Set (EuclideanSpace ℝ (Fin n)) :=
            {z | |⟪z, xs k - xbar⟫_ℝ - ⟪ws k, F (xs k) - F xbar⟫_ℝ| ≤ M}
          have hT_closed : IsClosed T := by
            have hcont : Continuous (fun z : EuclideanSpace ℝ (Fin n) =>
                |⟪z, xs k - xbar⟫_ℝ - ⟪ws k, F (xs k) - F xbar⟫_ℝ|) :=
              ((continuous_id.inner continuous_const).sub continuous_const).abs
            exact isClosed_Iic.preimage hcont
          have hT_conv : Convex ℝ T := by
            intro z₁ hz₁ z₂ hz₂ a b ha hb hab
            simp only [T, Set.mem_ofPred_eq] at hz₁ hz₂ ⊢
            have hlin : ⟪a • z₁ + b • z₂, xs k - xbar⟫_ℝ - ⟪ws k, F (xs k) - F xbar⟫_ℝ =
                a * (⟪z₁, xs k - xbar⟫_ℝ - ⟪ws k, F (xs k) - F xbar⟫_ℝ) +
                b * (⟪z₂, xs k - xbar⟫_ℝ - ⟪ws k, F (xs k) - F xbar⟫_ℝ) := by
              rw [inner_add_left, inner_smul_left, inner_smul_left]
              simp only [conj_trivial]
              have : ⟪ws k, F (xs k) - F xbar⟫_ℝ = (a + b) * ⟪ws k, F (xs k) - F xbar⟫_ℝ := by
                rw [hab, one_mul]
              linarith
            rw [hlin]
            calc |a * (⟪z₁, xs k - xbar⟫_ℝ - ⟪ws k, F (xs k) - F xbar⟫_ℝ) +
                  b * (⟪z₂, xs k - xbar⟫_ℝ - ⟪ws k, F (xs k) - F xbar⟫_ℝ)|
                ≤ |a * (⟪z₁, xs k - xbar⟫_ℝ - ⟪ws k, F (xs k) - F xbar⟫_ℝ)| +
                  |b * (⟪z₂, xs k - xbar⟫_ℝ - ⟪ws k, F (xs k) - F xbar⟫_ℝ)| := abs_add_le _ _
              _ = a * |⟪z₁, xs k - xbar⟫_ℝ - ⟪ws k, F (xs k) - F xbar⟫_ℝ| +
                  b * |⟪z₂, xs k - xbar⟫_ℝ - ⟪ws k, F (xs k) - F xbar⟫_ℝ| := by
                  rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
              _ ≤ a * M + b * M := by gcongr
              _ = M := by rw [← add_mul, hab, one_mul]
          have hsub : {z | ∃ y ∈ Metric.ball (xs k) ρ, DifferentiableAt ℝ F y ∧
              z = fderiv ℝ F y (ws k)} ⊆ T := by
            rintro z ⟨y, hy_ball, hy_diff, rfl⟩
            simp only [T, Set.mem_ofPred_eq]
            have hy_r₁ : y ∈ Metric.ball xbar r₁ := hBρ_r₁ hy_ball
            have hy_δ : y ∈ Metric.closedBall xbar δ :=
              Metric.ball_subset_closedBall (Metric.ball_subset_ball (min_le_left _ _) hy_r₁)
            have hy_B₀ : y ∈ Metric.ball xbar r₀ := hBρ_B₀ hy_ball
            have hx_B₀ : xs k ∈ Metric.ball xbar r₀ :=
              Metric.ball_subset_ball (min_le_right _ _) hk
            have hsymm := fderiv_gradient_symm Metric.isOpen_ball hdiff hy_B₀ hy_diff
            have hcod : fderiv ℝ F y (y - xbar) ∈ coderiv (sv F) y (F y) (y - xbar) :=
              hasFDerivAt_coderiv_gph hy_diff.hasFDerivAt hsymm (y - xbar)
            have hest := hδ_est y hy_δ _ hcod
            have hDf_le : ‖fderiv ℝ F y‖ ≤ (L : ℝ) :=
              norm_fderiv_le_of_lipschitzOn ℝ (Metric.isOpen_ball.mem_nhds hy_B₀) hlip
            have h1 : ‖fderiv ℝ F y (xs k - y)‖ ≤ (L : ℝ) * ρ :=
              (ContinuousLinearMap.le_opNorm _ _).trans
                (mul_le_mul hDf_le (by rw [norm_sub_rev]; simpa [dist_eq_norm] using (Metric.mem_ball.mp hy_ball).le)
                  (norm_nonneg _) L.coe_nonneg)
            have h2 : ‖F y - F (xs k)‖ ≤ (L : ℝ) * ρ := by
              have := hlip.dist_le_mul y hy_B₀ (xs k) hx_B₀
              rw [dist_eq_norm] at this
              exact this.trans (mul_le_mul_of_nonneg_left (Metric.mem_ball.mp hy_ball).le L.coe_nonneg)
            have h3 : ‖fderiv ℝ F y (y - xbar) - (F y - F xbar)‖ ≤ ε * (‖xs k - xbar‖ + ρ) := by
              rw [norm_sub_rev]
              have htri := dist_triangle y (xs k) xbar
              have hy_dist : ‖y - xs k‖ < ρ := by simpa [dist_eq_norm] using Metric.mem_ball.mp hy_ball
              rw [dist_eq_norm, dist_eq_norm, dist_eq_norm] at htri
              have hle : ‖y - xbar‖ ≤ ‖xs k - xbar‖ + ρ := by linarith
              exact hest.trans (mul_le_mul_of_nonneg_left hle hε.le)
            have hrew : ⟪fderiv ℝ F y (ws k), xs k - xbar⟫_ℝ - ⟪ws k, F (xs k) - F xbar⟫_ℝ =
                ⟪ws k, fderiv ℝ F y (xs k - y) + (fderiv ℝ F y (y - xbar) - (F y - F xbar)) +
                  (F y - F (xs k))⟫_ℝ := by
              rw [hsymm (ws k) (xs k - xbar), ← inner_sub_right]
              congr 1
              have hlin : fderiv ℝ F y (xs k - y) + fderiv ℝ F y (y - xbar) =
                  fderiv ℝ F y (xs k - xbar) := by
                rw [← map_add]; congr 1; abel
              rw [← hlin]
              abel
            rw [hrew]
            have hcs := abs_real_inner_le_norm (ws k)
              (fderiv ℝ F y (xs k - y) + (fderiv ℝ F y (y - xbar) - (F y - F xbar)) +
                (F y - F (xs k)))
            have htri1 := norm_add_le (fderiv ℝ F y (xs k - y) +
              (fderiv ℝ F y (y - xbar) - (F y - F xbar))) (F y - F (xs k))
            have htri2 := norm_add_le (fderiv ℝ F y (xs k - y))
              (fderiv ℝ F y (y - xbar) - (F y - F xbar))
            have hnorm_sum : ‖fderiv ℝ F y (xs k - y) +
                (fderiv ℝ F y (y - xbar) - (F y - F xbar)) + (F y - F (xs k))‖ ≤
                ε * ‖xs k - xbar‖ + (2 * (L : ℝ) + ε) * ρ := by linarith
            exact hcs.trans (mul_le_mul_of_nonneg_left hnorm_sum (norm_nonneg _))
          exact closure_minimal (convexHull_min hsub hT_conv) hT_closed hmem_cl
        -- Send ρ → 0⁺
        have hscaled : |⟪u's k, xs k - xbar⟫_ℝ - ⟪ws k, F (xs k) - F xbar⟫_ℝ| ≤
            ε * (‖ws k‖ * ‖xs k - xbar‖) := by
          by_contra hgt
          push Not at hgt
          set gap := |⟪u's k, xs k - xbar⟫_ℝ - ⟪ws k, F (xs k) - F xbar⟫_ℝ| -
            ε * (‖ws k‖ * ‖xs k - xbar‖)
          have hgap : 0 < gap := sub_pos.mpr hgt
          set C := ‖ws k‖ * (2 * (L : ℝ) + ε)
          set ρ := min (ρ_max / 2) (gap / (2 * (C + 1)))
          have hρ_pos : 0 < ρ := lt_min (half_pos hρ_max_pos) (div_pos hgap (by positivity))
          have hρ_lt : ρ < ρ_max := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hρ_max_pos)
          have hle := hfor_ρ ρ hρ_pos hρ_lt
          have hCρ : C * ρ ≤ gap / 2 := by
            have h1 : ρ ≤ gap / (2 * (C + 1)) := min_le_right _ _
            have h2 : C * (gap / (2 * (C + 1))) ≤ gap / 2 := by
              rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
              nlinarith [show 0 ≤ C by positivity]
            exact (mul_le_mul_of_nonneg_left h1 (by positivity)).trans h2
          have hle' : |⟪u's k, xs k - xbar⟫_ℝ - ⟪ws k, F (xs k) - F xbar⟫_ℝ| ≤
              ε * (‖ws k‖ * ‖xs k - xbar‖) + C * ρ := by
            calc |⟪u's k, xs k - xbar⟫_ℝ - ⟪ws k, F (xs k) - F xbar⟫_ℝ|
                ≤ ‖ws k‖ * (ε * ‖xs k - xbar‖ + (2 * (L : ℝ) + ε) * ρ) := hle
              _ = ε * (‖ws k‖ * ‖xs k - xbar‖) + C * ρ := by dsimp only [C]; ring
          dsimp only [gap] at hCρ
          linarith
        -- Divide by ts k > 0
        have htk := hts_pos k
        have h1 : xs k - xbar = ts k • us k := by simp [xs]
        have h2 : F (xs k) - F xbar = ts k • vs k := by rw [hxs_gph k, add_sub_cancel_left]
        rw [h1, h2, inner_smul_right, inner_smul_right, ← mul_sub, abs_mul, abs_of_pos htk,
          norm_smul, Real.norm_eq_abs, abs_of_pos htk] at hscaled
        nlinarith
      have hlhs_tend : Tendsto (fun k => |⟪u's k, us k⟫_ℝ - ⟪ws k, vs k⟫_ℝ|) atTop
          (𝓝 |⟪u', u⟫_ℝ - ⟪w, v⟫_ℝ|) :=
        ((hu's_tend.inner hus_tend).sub (hws_tend.inner hvs_tend)).abs
      have hrhs_tend : Tendsto (fun k => ε * (‖ws k‖ * ‖us k‖)) atTop
          (𝓝 (ε * (‖w‖ * ‖u‖))) :=
        tendsto_const_nhds.mul (hws_tend.norm.mul hus_tend.norm)
      exact le_of_tendsto_of_tendsto hlhs_tend hrhs_tend hbound_k
    have hle0 : |⟪u', u⟫_ℝ - ⟪w, v⟫_ℝ| ≤ 0 := by
      by_contra hpos
      push Not at hpos
      have hε : 0 < |⟪u', u⟫_ℝ - ⟪w, v⟫_ℝ| / (2 * (‖w‖ * ‖u‖ + 1)) :=
        div_pos hpos (by positivity)
      have h1 := hall _ hε
      have h2 : |⟪u', u⟫_ℝ - ⟪w, v⟫_ℝ| / (2 * (‖w‖ * ‖u‖ + 1)) * (‖w‖ * ‖u‖) ≤
          |⟪u', u⟫_ℝ - ⟪w, v⟫_ℝ| / 2 := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [mul_nonneg (norm_nonneg w) (norm_nonneg u)]
      linarith
    exact sub_eq_zero.mp (abs_nonpos_iff.mp hle0)
