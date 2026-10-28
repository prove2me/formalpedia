-- Prove2me | solution 1 for FiniteEnergyPlane.exists_plane_of_gradNorm_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-25T18:19:57.511253+00:00
-- url     : https://prove2.me/submissions/97d8a383-ae14-4dc1-9dff-bae51607ff52

import Definitions.Def_FiniteEnergyPlane_Setting
import Theorems.Thm_FiniteEnergyPlane_exists_subseq_tendstoCInftyLocOn_univ
import Theorems.Thm_FiniteEnergyPlane_lintegral_energyDensity_le_liminf
import Theorems.Thm_FiniteEnergyPlane_isCompact_aCoord_slab
import Theorems.Thm_FiniteEnergyPlane_norm_fderiv_le_mul_gradNorm
import Theorems.Thm_FiniteEnergyPlane_jtilde_isAlmostComplexOn
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- A bubble plane from curves with normalized gradients on growing discs. -/
theorem exists_plane_of_gradNorm_le_aux {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (v : ℕ → ℂ → V n) (ρ : ℕ → ℝ)
    (hρ : Tendsto ρ atTop atTop) (hv : ∀ k, IsFiniteEnergyCurve H J (ball 0 (ρ k)) (v k))
    (C : ℝ) (hC : ∀ k, energy H (ball 0 (ρ k)) (v k) ≤ ENNReal.ofReal C)
    (hgrad : ∀ k, ∀ z ∈ ball (0 : ℂ) (ρ k), gradNorm H (v k) z ≤ 2)
    (ha0 : ∀ k, aCoord H (v k 0) = 0) (hg0 : ∀ k, gradNorm H (v k) 0 = 1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ w : ℂ → V n, IsFiniteEnergyCurve H J Set.univ w ∧
      (∃ z₁ z₂, w z₁ ≠ w z₂) ∧ energy H Set.univ w ≤ ENNReal.ofReal C ∧
      ∀ R : ℝ, dlambdaEnergy H (ball 0 R) w ≤
        liminf (fun j => dlambdaEnergy H (ball 0 R) (v (φ j))) atTop := by
  obtain ⟨hJt, hprojs, haCs, -, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  set O : Set (V n) := {y | y ≠ 0} with hO
  have hOo : IsOpen O := isOpen_ne
  -- differentiability of the coordinates
  have hdiff : ∀ k, ∀ z ∈ ball (0 : ℂ) (ρ k), DifferentiableAt ℝ (v k) z := fun k z hz =>
    ((hv k).1.differentiableOn (by simp) z hz).differentiableAt (isOpen_ball.mem_nhds hz)
  have haCd : ∀ y : V n, y ≠ 0 → DifferentiableAt ℝ (aCoord H) y := fun y hy =>
    (haCs.differentiableOn (by simp) y hy).differentiableAt (hOo.mem_nhds hy)
  have hprd : ∀ y : V n, y ≠ 0 → DifferentiableAt ℝ (proj H) y := fun y hy =>
    (hprojs.differentiableOn (by simp) y hy).differentiableAt (hOo.mem_nhds hy)
  have habd : ∀ k, ∀ z ∈ ball (0 : ℂ) (ρ k), |aCoord H (v k z)| ≤ 2 * ‖z‖ := by
    intro k z hz
    have h0 : (0 : ℂ) ∈ ball (0 : ℂ) (ρ k) :=
      mem_ball_self (lt_of_le_of_lt (norm_nonneg z) (mem_ball_zero_iff.1 hz))
    have hd : ∀ x ∈ ball (0 : ℂ) (ρ k), DifferentiableAt ℝ (fun z => aCoord H (v k z)) x :=
      fun x hx => (haCd _ ((hv k).2.1 x hx)).comp x (hdiff k x hx)
    have hb : ∀ x ∈ ball (0 : ℂ) (ρ k), ‖fderiv ℝ (fun z => aCoord H (v k z)) x‖ ≤ 2 :=
      fun x hx => le_trans (le_add_of_nonneg_right (norm_nonneg _)) (hgrad k x hx)
    have := (convex_ball (0 : ℂ) (ρ k)).norm_image_sub_le_of_norm_fderiv_le hd hb h0 hz
    rw [ha0 k, sub_zero, sub_zero, Real.norm_eq_abs] at this
    exact this
  -- uniform bounds on balls
  have hbd : ∀ R : ℝ, ∃ K : Set (V n), IsCompact K ∧ K ⊆ O ∧ ∃ M : ℝ, ∀ k, R < ρ k →
      ∀ z ∈ ball (0 : ℂ) R, v k z ∈ K ∧ ‖fderiv ℝ (v k) z‖ ≤ M := by
    intro R
    obtain ⟨M, hM⟩ := norm_fderiv_le_mul_gradNorm H hH J hJ (2 * R)
    refine ⟨_, isCompact_aCoord_slab H hH J hJ (2 * R), fun y hy => hy.1, max M 0 * 2,
      fun k hk z hz => ?_⟩
    have hzk : z ∈ ball (0 : ℂ) (ρ k) := ball_subset_ball hk.le hz
    have hne := (hv k).2.1 z hzk
    have ha : |aCoord H (v k z)| ≤ 2 * R := by
      have := habd k z hzk
      have := mem_ball_zero_iff.1 hz
      linarith
    refine ⟨⟨hne, ha⟩, ?_⟩
    have hg := hgrad k z hzk
    have hgn : 0 ≤ gradNorm H (v k) z := add_nonneg (norm_nonneg _) (norm_nonneg _)
    calc ‖fderiv ℝ (v k) z‖ ≤ M * gradNorm H (v k) z := hM _ _ (hdiff k z hzk) hne ha
      _ ≤ max M 0 * gradNorm H (v k) z := mul_le_mul_of_nonneg_right (le_max_left _ _) hgn
      _ ≤ max M 0 * 2 := mul_le_mul_of_nonneg_left hg (le_max_right _ _)
  obtain ⟨φ, hφ, w, hwsm, hwhol, hwO, hconv⟩ :=
    exists_subseq_tendstoCInftyLocOn_univ (Jtilde H J) O hJt v ρ hρ
      (fun k => (hv k).1.of_le (by simp)) (fun k => (hv k).2.2.1) hbd
  have hφt := hφ.tendsto_atTop
  -- pointwise `C¹` convergence
  have hpt : ∀ z, Tendsto (fun j => v (φ j) z) atTop (𝓝 (w z)) ∧
      Tendsto (fun j => fderiv ℝ (v (φ j)) z) atTop (𝓝 (fderiv ℝ w z)) := by
    intro z
    have hz : z ∈ ({z} : Set ℂ) := rfl
    have h0 := (hconv {z} (Set.subset_univ _) isCompact_singleton 0).tendsto_at hz
    have h1 := (hconv {z} (Set.subset_univ _) isCompact_singleton 1).tendsto_at hz
    constructor
    · have := ((continuous_eval_const (Fin.elim0 : Fin 0 → ℂ)).tendsto _).comp h0
      simpa [Function.comp_def, iteratedFDeriv_zero_apply] using this
    · have hfd : ∀ f : ℂ → V n, fderiv ℝ f z =
          continuousMultilinearCurryFin1 ℝ ℂ (V n) (iteratedFDeriv ℝ 1 f z) := by
        intro f
        ext x
        rw [continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]
        rfl
      have := ((continuousMultilinearCurryFin1 ℝ ℂ (V n)).continuous.tendsto _).comp h1
      simpa only [Function.comp_def, ← hfd] using this
  have hwd : ∀ z, DifferentiableAt ℝ w z := fun z => hwsm.differentiable (by simp) z
  -- the gradient norm at `0` passes to the limit
  have hgN : ∀ u : ℂ → V n, ∀ z, DifferentiableAt ℝ u z → u z ≠ 0 →
      gradNorm H u z = ‖(fderiv ℝ (aCoord H) (u z)).comp (fderiv ℝ u z)‖ +
        ‖(fderiv ℝ (proj H) (u z)).comp (fderiv ℝ u z)‖ := by
    intro u z hu hne
    unfold gradNorm
    rw [show (fun z => aCoord H (u z)) = aCoord H ∘ u from rfl,
      show (fun z => proj H (u z)) = proj H ∘ u from rfl,
      fderiv_comp z (haCd _ hne) hu, fderiv_comp z (hprd _ hne) hu]
  have hcompc : ∀ {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X],
      Continuous fun p : (V n →L[ℝ] X) × (ℂ →L[ℝ] V n) => p.1.comp p.2 :=
    fun {X} _ _ => isBoundedBilinearMap_comp.continuous
  have hcA : ContinuousAt (fderiv ℝ (aCoord H)) (w 0) :=
    (haCs.continuousOn_fderiv_of_isOpen hOo (by simp)).continuousAt (hOo.mem_nhds (hwO 0))
  have hcP : ContinuousAt (fderiv ℝ (proj H)) (w 0) :=
    (hprojs.continuousOn_fderiv_of_isOpen hOo (by simp)).continuousAt (hOo.mem_nhds (hwO 0))
  have hev0 : ∀ᶠ j in atTop, 0 < ρ (φ j) := (hρ.comp hφt).eventually (eventually_gt_atTop 0)
  have hgw : gradNorm H w 0 = 1 := by
    have hlim : Tendsto (fun j => gradNorm H (v (φ j)) 0) atTop (𝓝 (gradNorm H w 0)) := by
      rw [hgN w 0 (hwd 0) (hwO 0)]
      have tA := ((hcompc.tendsto _).comp ((hcA.tendsto.comp (hpt 0).1).prodMk_nhds
        (hpt 0).2)).norm
      have tP := ((hcompc.tendsto _).comp ((hcP.tendsto.comp (hpt 0).1).prodMk_nhds
        (hpt 0).2)).norm
      refine (tA.add tP).congr' ?_
      filter_upwards [hev0] with j hj
      have h0 : (0 : ℂ) ∈ ball (0 : ℂ) (ρ (φ j)) := mem_ball_self hj
      rw [hgN _ 0 (hdiff _ 0 h0) ((hv _).2.1 0 h0)]
      rfl
    have : Tendsto (fun j => gradNorm H (v (φ j)) 0) atTop (𝓝 1) := by simp [hg0]
    exact tendsto_nhds_unique hlim this
  have hnc : ∃ z₁ z₂, w z₁ ≠ w z₂ := by
    by_contra hcon
    push_neg at hcon
    have hconst : (fun z => w z) = fun _ => w 0 := funext fun z => hcon z 0
    have : gradNorm H w 0 = 0 := by
      unfold gradNorm
      rw [show (fun z => aCoord H (w z)) = fun _ => aCoord H (w 0) by
          funext z; rw [hcon z 0],
        show (fun z => proj H (w z)) = fun _ => proj H (w 0) by funext z; rw [hcon z 0]]
      simp
    rw [hgw] at this
    exact one_ne_zero this
  -- Fatou on balls
  have hball : ∀ (ψ : ℝ → ℝ), ContDiff ℝ 1 ψ → ∀ R : ℝ,
      ∫⁻ z in ball 0 R, ENNReal.ofReal (energyDensity H ψ w z) ≤
        liminf (fun j => ∫⁻ z in ball 0 R, ENNReal.ofReal (energyDensity H ψ (v (φ j)) z))
          atTop := by
    intro ψ hψ R
    refine lintegral_energyDensity_le_liminf H hH J hJ (ball 0 R) isOpen_ball (fun j => v (φ j)) w
      ?_ (hwsm.of_le (by simp)).contDiffOn (fun z _ => hwO z) (fun z _ => hpt z) ψ hψ
    filter_upwards [(hρ.comp hφt).eventually (eventually_gt_atTop R)] with j hj
    exact ⟨((hv _).1.of_le (by simp)).mono (ball_subset_ball hj.le),
      fun z hz => (hv _).2.1 z (ball_subset_ball hj.le hz)⟩
  -- exhaustion
  have hexh : ∀ f : ℂ → ℝ≥0∞, Tendsto (fun N : ℕ => ∫⁻ z in ball 0 N, f z) atTop
      (𝓝 (∫⁻ z in Set.univ, f z)) := by
    intro f
    set μ := volume.withDensity f with hμ
    have hmono : Monotone (fun N : ℕ => ball (0 : ℂ) N) :=
      fun i j hij => ball_subset_ball (by exact_mod_cast hij)
    have hU : (⋃ N : ℕ, ball (0 : ℂ) N) = Set.univ := by
      refine Set.eq_univ_of_forall fun x => ?_
      obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
      exact Set.mem_iUnion.2 ⟨N, mem_ball_zero_iff.2 hN⟩
    have h := tendsto_measure_iUnion_atTop (μ := μ) hmono
    rw [hU, hμ, withDensity_apply _ MeasurableSet.univ] at h
    refine h.congr fun N => ?_
    simp only [Function.comp_apply, withDensity_apply _ measurableSet_ball]
  have hEw : energy H Set.univ w ≤ ENNReal.ofReal C := by
    refine iSup₂_le fun ψ hψ => ?_
    refine le_of_tendsto' (hexh _) fun N => ?_
    refine (hball ψ (hψ.1.of_le (by simp)) N).trans (liminf_le_of_frequently_le ?_)
    refine Eventually.frequently ?_
    filter_upwards [(hρ.comp hφt).eventually (eventually_gt_atTop (N : ℝ))] with j hj
    calc ∫⁻ z in ball 0 N, ENNReal.ofReal (energyDensity H ψ (v (φ j)) z)
        ≤ ∫⁻ z in ball 0 (ρ (φ j)), ENNReal.ofReal (energyDensity H ψ (v (φ j)) z) :=
          lintegral_mono_set (ball_subset_ball hj.le)
      _ ≤ energy H (ball 0 (ρ (φ j))) (v (φ j)) :=
          le_iSup₂ (f := fun (ψ : ℝ → ℝ) (_ : Admissible ψ) =>
            ∫⁻ z in ball 0 (ρ (φ j)), ENNReal.ofReal (energyDensity H ψ (v (φ j)) z)) ψ hψ
      _ ≤ ENNReal.ofReal C := hC _
  have hd1 : ∀ (u : ℂ → V n) z, energyDensity H (fun _ => (1 : ℝ)) u z = dlambdaDensity H u z := by
    intro u z
    simp [energyDensity, dlambdaDensity]
  refine ⟨φ, hφ, w, ⟨hwsm.contDiffOn, fun z _ => hwO z, hwhol,
    lt_of_le_of_lt hEw ENNReal.ofReal_lt_top⟩, hnc, hEw, fun R => ?_⟩
  have := hball (fun _ => 1) contDiff_const R
  simp only [hd1] at this
  exact this

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (v : ℕ → ℂ → V n)
    (ρ : ℕ → ℝ) (hρ : Tendsto ρ atTop atTop) (hv : ∀ k, IsFiniteEnergyCurve H J (ball 0 (ρ k)) (v k))
    (C : ℝ) (hC : ∀ k, energy H (ball 0 (ρ k)) (v k) ≤ ENNReal.ofReal C)
    (hgrad : ∀ k, ∀ z ∈ ball (0 : ℂ) (ρ k), gradNorm H (v k) z ≤ 2)
    (ha0 : ∀ k, aCoord H (v k 0) = 0) (hg0 : ∀ k, gradNorm H (v k) 0 = 1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ w : ℂ → V n, IsFiniteEnergyCurve H J Set.univ w ∧
      (∃ z₁ z₂, w z₁ ≠ w z₂) ∧ energy H Set.univ w ≤ ENNReal.ofReal C ∧
      ∀ R : ℝ, dlambdaEnergy H (ball 0 R) w ≤
        liminf (fun j => dlambdaEnergy H (ball 0 R) (v (φ j))) atTop :=
  exists_plane_of_gradNorm_le_aux H hH J hJ v ρ hρ hv C hC hgrad ha0 hg0
