-- Prove2me | solution 1 for FiniteEnergyPlane.exists_subseq_tendstoCInftyLocOn_of_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-26T16:19:21.237305+00:00
-- url     : https://prove2.me/submissions/8b70036d-d62b-446b-ae66-352f45ca9ede

import Definitions.Def_FiniteEnergyPlane_Setting
import Theorems.Thm_JHolomorphic_bounded_iteratedFDeriv_of_sobolevNorm_le
import Theorems.Thm_JHolomorphic_exists_subseq_tendstoLocallyUniformlyOn_iteratedFDeriv
import Theorems.Thm_JHolomorphic_contDiffOn_of_tendstoLocallyUniformlyOn_iteratedFDeriv
import Theorems.Thm_FiniteEnergyPlane_isJHolomorphicOn_comp_add_smul
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology DbarRegularity Set
open scoped ContDiff ENNReal NNReal Real

set_option maxHeartbeats 1000000 in
theorem exists_subseq_tendstoCInftyLocOn_of_isOpen_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (J : E → E →L[ℝ] E) (O : Set E)
    (hJ : JHolomorphic.IsAlmostComplexOn J O) (U : Set ℂ) (hU : IsOpen U) (v : ℕ → ℂ → E)
    (hv : ∀ k, ContDiffOn ℝ ∞ (v k) U) (hhol : ∀ k, JHolomorphic.IsJHolomorphicOn J U (v k))
    (hbd : ∀ K ⊆ U, IsCompact K → ∃ K' : Set E, IsCompact K' ∧ K' ⊆ O ∧ ∃ M : ℝ,
      ∀ k, ∀ z ∈ K, v k z ∈ K' ∧ ‖fderiv ℝ (v k) z‖ ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ w : ℂ → E, ContDiffOn ℝ ∞ w U ∧
      JHolomorphic.IsJHolomorphicOn J U w ∧ Set.MapsTo w U O ∧
      JHolomorphic.TendstoCInftyLocOn (fun j => v (φ j)) w U := by
  -- local bounds on all derivatives near a point
  have hloc : ∀ c : ℂ, ∀ s : ℝ, 0 < s → closedBall c s ⊆ U → ∀ m : ℕ, ∃ M : ℝ, ∀ k,
      ∀ y ∈ ball c (s / 2), ‖iteratedFDeriv ℝ m (v k) y‖ ≤ M := by
    intro c s hs hcs m
    obtain ⟨K', hK'c, hK'O, M, hM⟩ := hbd (closedBall c s) hcs (isCompact_closedBall c s)
    set u : ℕ → ℂ → E := fun k x => v k (c + s • x) with hu
    have hmem : ∀ x ∈ ball (0 : ℂ) 1, c + s • x ∈ closedBall c s := by
      intro x hx
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_of_nonneg hs.le]
      rw [mem_ball_zero_iff] at hx
      nlinarith
    have hA := fun k => isJHolomorphicOn_comp_add_smul J U (v k) (hhol k) c s
    have husm : ∀ k, ContDiffOn ℝ ∞ (u k) (ball 0 1) := fun k =>
      (hv k).comp (by fun_prop : ContDiff ℝ ∞ fun x : ℂ => c + s • x).contDiffOn
        (fun x hx => hcs (hmem x hx))
    have huhol : ∀ k, JHolomorphic.IsJHolomorphicOn J (ball 0 1) (u k) := fun k x hx =>
      (hA k).1 x (hcs (hmem x hx))
    have humaps : ∀ k, Set.MapsTo (u k) (ball 0 1) K' := fun k x hx => (hM k _ (hmem x hx)).1
    have huC : ∀ k, ∀ x ∈ ball (0 : ℂ) 1, ‖fderiv ℝ (u k) x‖ ≤ s * M := by
      intro k x hx
      rw [show u k = fun w => v k (c + s • w) from rfl, (hA k).2 x (hcs (hmem x hx)), norm_smul,
        Real.norm_of_nonneg hs.le]
      exact mul_le_mul_of_nonneg_left (hM k _ (hmem x hx)).2 hs.le
    obtain ⟨R, hR⟩ := hK'c.isBounded.exists_norm_le
    have hμ : (volume.restrict (ball (0 : ℂ) 1)) univ ≠ ⊤ := by
      rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top.ne
    set A : ℝ≥0∞ := (volume.restrict (ball (0 : ℂ) 1)) univ ^ (ENNReal.ofReal 3).toReal⁻¹ *
      (ENNReal.ofReal R + ENNReal.ofReal (s * M)) with hA_def
    have hAt : A ≠ ⊤ := by
      refine ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity) hμ) ?_
      exact ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
    have hsob : ∀ k, sobolevNorm 1 (ENNReal.ofReal 3) (ball 0 1) (u k) ≤ A.toNNReal := by
      intro k
      rw [ENNReal.coe_toNNReal hAt, hA_def, mul_add]
      simp only [sobolevNorm, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
      refine add_le_add ?_ ?_
      · refine eLpNorm_le_of_ae_bound (ae_restrict_of_forall_mem measurableSet_ball fun z hz => ?_)
        rw [norm_iteratedFDeriv_zero]; exact hR _ (humaps k hz)
      · refine eLpNorm_le_of_ae_bound (ae_restrict_of_forall_mem measurableSet_ball fun z hz => ?_)
        rw [norm_iteratedFDeriv_one]; exact huC k z hz
    have hsub : closedBall (0 : ℂ) (1 / 2) ⊆ ball 0 1 := closedBall_subset_ball (by norm_num)
    obtain ⟨Mu, hMu⟩ := JHolomorphic.bounded_iteratedFDeriv_of_sobolevNorm_le 3 (by norm_num) J
      (fun _ => J) O K' hJ (fun _ => hJ)
      (fun K'' _ _ m => Metric.tendstoUniformlyOn_iff.2 fun e he =>
        Eventually.of_forall fun _ _ _ => by simpa using he) hK'c hK'O u husm huhol humaps
      A.toNNReal hsob (closedBall 0 (1 / 2)) hsub (isCompact_closedBall _ _) m
    -- transfer back by the affine change of variables
    set L : ℂ ≃L[ℝ] ℂ :=
      (LinearEquiv.smulOfNeZero ℝ ℂ s⁻¹ (inv_ne_zero hs.ne')).toContinuousLinearEquiv with hLdef
    have hLx : ∀ y, L y = s⁻¹ • y := fun y => rfl
    have hLn : ‖(L : ℂ →L[ℝ] ℂ)‖ ≤ s⁻¹ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
      rw [ContinuousLinearEquiv.coe_coe, hLx, norm_smul, norm_inv, Real.norm_of_nonneg hs.le]
    refine ⟨Mu * s⁻¹ ^ m, fun k y hy => ?_⟩
    have hfun : v k = fun y => (u k ∘ L) (y - c) := by
      funext y
      simp only [Function.comp_apply, hLx, hu, smul_smul, mul_inv_cancel₀ hs.ne', one_smul,
        add_sub_cancel]
    have hcomp := L.iteratedFDerivWithin_comp_right (u k) uniqueDiffOn_univ
      (Set.mem_univ (L (y - c))) m
    simp only [iteratedFDerivWithin_univ, Set.preimage_univ] at hcomp
    rw [hfun, iteratedFDeriv_comp_sub, hcomp]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hyL : L (y - c) ∈ closedBall (0 : ℂ) (1 / 2) := by
      rw [mem_closedBall_zero_iff, hLx, norm_smul, norm_inv, Real.norm_of_nonneg hs.le,
        inv_mul_le_iff₀ hs]
      rw [mem_ball, dist_eq_norm] at hy
      linarith
    have h1 := hMu k _ hyL
    exact mul_le_mul h1 (pow_le_pow_left₀ (norm_nonneg _) hLn m) (by positivity)
      ((norm_nonneg _).trans h1)
  -- bounds on compact subsets
  have hball : ∀ z ∈ U, ∃ s : ℝ, 0 < s ∧ closedBall z s ⊆ U := by
    intro z hz
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU z hz
    exact ⟨ε / 2, by positivity, (closedBall_subset_ball (half_lt_self hε)).trans hεU⟩
  choose! sr hsr0 hsrU using hball
  have hcpt : ∀ K ⊆ U, IsCompact K → ∀ m : ℕ, ∃ M : ℝ, ∀ k, ∀ z ∈ K,
      ‖iteratedFDeriv ℝ m (v k) z‖ ≤ M := by
    intro K hK hKc m
    obtain ⟨t, htK, htcov⟩ := hKc.elim_nhds_subcover (fun z => ball z (sr z / 2))
      (fun z hz => ball_mem_nhds z (by have := hsr0 z (hK hz); positivity))
    have hb : ∀ z ∈ t, ∃ M : ℝ, ∀ k, ∀ y ∈ ball z (sr z / 2), ‖iteratedFDeriv ℝ m (v k) y‖ ≤ M :=
      fun z hz => hloc z (sr z) (hsr0 z (hK (htK z hz))) (hsrU z (hK (htK z hz))) m
    choose! Mb hMb using hb
    refine ⟨∑ z ∈ t, max (Mb z) 0, fun k y hy => ?_⟩
    obtain ⟨z, hzt, hyz⟩ := Set.mem_iUnion₂.1 (htcov hy)
    refine (hMb z hzt k y hyz).trans ((le_max_left (Mb z) 0).trans ?_)
    exact Finset.single_le_sum (f := fun z => max (Mb z) 0) (fun _ _ => le_max_right _ _) hzt
  -- extraction and identification of the limit
  obtain ⟨φ, hφ, g, hg⟩ :=
    JHolomorphic.exists_subseq_tendstoLocallyUniformlyOn_iteratedFDeriv hU v hv hcpt
  set w : ℂ → E := fun z => continuousMultilinearCurryFin0 ℝ ℂ E (g 0 z) with hw_def
  have hw : ∀ z ∈ U, Tendsto (fun ν => v (φ ν) z) atTop (𝓝 (w z)) := by
    intro z hz
    have := ((continuousMultilinearCurryFin0 ℝ ℂ E).continuous.tendsto _).comp
      ((hg 0).tendsto_at hz)
    simpa [Function.comp_def, w, continuousMultilinearCurryFin0_apply,
      iteratedFDeriv_zero_apply] using this
  obtain ⟨hws, hwg⟩ := JHolomorphic.contDiffOn_of_tendstoLocallyUniformlyOn_iteratedFDeriv hU
    (fun ν => v (φ ν)) (fun ν => hv (φ ν)) w hw g hg
  have hwO : Set.MapsTo w U O := by
    intro z hz
    obtain ⟨K', hK'c, hK'O, M, hM⟩ := hbd {z} (by simpa using hz) isCompact_singleton
    exact hK'O (hK'c.isClosed.mem_of_tendsto (hw z hz)
      (Eventually.of_forall fun ν => (hM (φ ν) z rfl).1))
  refine ⟨φ, hφ, w, hws, ?_, hwO, ?_⟩
  · intro z hz
    have hdw : DifferentiableAt ℝ w z :=
      (hws.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hz)
    refine ⟨hdw, ?_⟩
    have hD1 : Tendsto (fun ν => iteratedFDeriv ℝ 1 (v (φ ν)) z) atTop
        (𝓝 (iteratedFDeriv ℝ 1 w z)) := by
      rw [hwg 1 hz]; exact (hg 1).tendsto_at hz
    have hd : ∀ y : ℂ, Tendsto (fun ν => fderiv ℝ (v (φ ν)) z y) atTop
        (𝓝 (fderiv ℝ w z y)) := by
      intro y
      have := ((continuous_eval_const (fun _ : Fin 1 => y)).tendsto _).comp hD1
      simpa [Function.comp_def, iteratedFDeriv_one_apply] using this
    have hcont : ContinuousAt J (w z) :=
      (hJ.2.1.continuousOn).continuousAt (hJ.1.mem_nhds (hwO hz))
    have hJt : Tendsto (fun ν => J (v (φ ν) z)) atTop (𝓝 (J (w z))) :=
      hcont.tendsto.comp (hw z hz)
    have hlim : Tendsto (fun ν => JHolomorphic.dbarJ J (v (φ ν)) z) atTop
        (𝓝 (JHolomorphic.dbarJ J w z)) :=
      (hd 1).add ((isBoundedBilinearMap_apply.continuous.tendsto _).comp
        (hJt.prodMk_nhds (hd Complex.I)))
    have hzero : ∀ ν, JHolomorphic.dbarJ J (v (φ ν)) z = 0 := fun ν => (hhol (φ ν) z hz).2
    simp only [hzero] at hlim
    exact (tendsto_nhds_unique tendsto_const_nhds hlim).symm
  · intro K hK hKc m
    exact (((tendstoLocallyUniformlyOn_iff_forall_isCompact hU).1 (hg m)) K hK
      hKc).congr_right (fun z hz => (hwg m (hK hz)).symm)

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (J : E → E →L[ℝ] E) (O : Set E)
    (hJ : JHolomorphic.IsAlmostComplexOn J O) (U : Set ℂ) (hU : IsOpen U) (v : ℕ → ℂ → E)
    (hv : ∀ k, ContDiffOn ℝ ∞ (v k) U) (hhol : ∀ k, JHolomorphic.IsJHolomorphicOn J U (v k))
    (hbd : ∀ K ⊆ U, IsCompact K → ∃ K' : Set E, IsCompact K' ∧ K' ⊆ O ∧ ∃ M : ℝ,
      ∀ k, ∀ z ∈ K, v k z ∈ K' ∧ ‖fderiv ℝ (v k) z‖ ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ w : ℂ → E, ContDiffOn ℝ ∞ w U ∧
      JHolomorphic.IsJHolomorphicOn J U w ∧ Set.MapsTo w U O ∧
      JHolomorphic.TendstoCInftyLocOn (fun j => v (φ j)) w U :=
  FiniteEnergyPlane.exists_subseq_tendstoCInftyLocOn_of_isOpen_aux J O hJ U hU v hv hhol hbd
