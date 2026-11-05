-- Prove2me | solution 1 for FiniteEnergyPlane.tendsto_loopAction_of_tendstoCInftyLocOn
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-04T19:52:13.495897+00:00
-- url     : https://prove2.me/submissions/09cb8cf1-9093-4879-9b82-79d42fbb0486

import Definitions.Def_FiniteEnergyPlane_Setting
import Theorems.Thm_FiniteEnergyPlane_contDiffOn_proj_aCoord
import Theorems.Thm_FiniteEnergyPlane_tendstoCInftyLocOn_comp



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Let `S = H⁻¹(1)` be strictly star-shaped, `U ⊆ ℂ` open, and `u k → u₀` in `C^∞_loc(U)`, where
all maps are `C^∞` on `U` and avoid `0` there. Then for every smooth loop `γ : ℝ → ℂ` with image
in `U`, the loop actions `loopAction H (u k) γ` converge to `loopAction H u₀ γ`. -/
theorem tendsto_loopAction_of_tendstoCInftyLocOn_aux {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (U : Set ℂ) (hU : IsOpen U) (u : ℕ → ℂ → V n)
    (u₀ : ℂ → V n) (hu : ∀ k, ContDiffOn ℝ ∞ (u k) U) (hu₀ : ContDiffOn ℝ ∞ u₀ U)
    (hne : ∀ k, ∀ z ∈ U, u k z ≠ 0) (hne₀ : ∀ z ∈ U, u₀ z ≠ 0)
    (hconv : JHolomorphic.TendstoCInftyLocOn u u₀ U) (γ : ℝ → ℂ) (hγ : ContDiff ℝ ∞ γ)
    (hγU : ∀ t, γ t ∈ U) :
    Tendsto (fun k => loopAction H (u k) γ) atTop (𝓝 (loopAction H u₀ γ)) := by
  -- post-composition with a continuous map, on a compact set, to a continuous limit
  have hcomp : ∀ {K : Set ℝ}, IsCompact K → ∀ (F : ℕ → ℝ → V n × V n) (f : ℝ → V n × V n),
      ContinuousOn f K → TendstoUniformlyOn F f atTop K → ∀ g : V n × V n → ℝ, Continuous g →
      TendstoUniformlyOn (fun k t => g (F k t)) (fun t => g (f t)) atTop K := by
    intro K hK F f hf hF g hg
    have hS : IsCompact (f '' K) := hK.image_of_continuousOn hf
    have hT : IsCompact (cthickening 1 (f '' K)) := hS.cthickening
    have huc := hT.uniformContinuousOn_of_continuous hg.continuousOn
    rw [Metric.uniformContinuousOn_iff] at huc
    rw [Metric.tendstoUniformlyOn_iff] at hF ⊢
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := huc ε hε
    filter_upwards [hF (min δ 1) (lt_min hδ one_pos)] with k hk t ht
    have h1 : dist (f t) (F k t) < min δ 1 := hk t ht
    have hft : f t ∈ cthickening 1 (f '' K) :=
      self_subset_cthickening _ (Set.mem_image_of_mem f ht)
    have hFt : F k t ∈ cthickening 1 (f '' K) :=
      mem_cthickening_of_dist_le (F k t) (f t) 1 _ (Set.mem_image_of_mem f ht)
        (by rw [dist_comm]; exact (h1.trans_le (min_le_right _ _)).le)
    exact hδ' _ hft _ hFt (h1.trans_le (min_le_left _ _))
  have hprod : ∀ {K : Set ℝ} (F : ℕ → ℝ → V n) (f : ℝ → V n) (G : ℕ → ℝ → V n) (g : ℝ → V n),
      TendstoUniformlyOn F f atTop K → TendstoUniformlyOn G g atTop K →
      TendstoUniformlyOn (fun k t => (F k t, G k t)) (fun t => (f t, g t)) atTop K := by
    intro K F f G g hF hG
    rw [Metric.tendstoUniformlyOn_iff] at hF hG ⊢
    intro ε hε
    filter_upwards [hF ε hε, hG ε hε] with k h1 h2 t ht
    rw [Prod.dist_eq]
    exact max_lt (h1 t ht) (h2 t ht)
  have hintegral : ∀ (F : ℕ → ℝ → ℝ) (f : ℝ → ℝ), (∀ k, ContinuousOn (F k) (Set.Icc 0 1)) →
      ContinuousOn f (Set.Icc 0 1) → TendstoUniformlyOn F f atTop (Set.Icc 0 1) →
      Tendsto (fun k => ∫ t in (0 : ℝ)..1, F k t) atTop (𝓝 (∫ t in (0 : ℝ)..1, f t)) := by
    intro F f hF hf hu
    rw [Metric.tendsto_atTop]
    rw [Metric.tendstoUniformlyOn_iff] at hu
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hu (ε / 2) (half_pos hε))
    refine ⟨N, fun k hk => ?_⟩
    have hi : IntervalIntegrable (F k) volume 0 1 :=
      (hF k).intervalIntegrable_of_Icc zero_le_one
    have hi' : IntervalIntegrable f volume 0 1 := hf.intervalIntegrable_of_Icc zero_le_one
    rw [Real.dist_eq, ← intervalIntegral.integral_sub hi hi']
    have hb : ∀ t ∈ Set.uIoc (0 : ℝ) 1, ‖F k t - f t‖ ≤ ε / 2 := by
      intro t ht
      rw [Set.uIoc_of_le zero_le_one] at ht
      have := hN k hk t (Set.Ioc_subset_Icc_self ht)
      rw [dist_comm, Real.dist_eq] at this
      exact this.le
    have := intervalIntegral.norm_integral_le_of_norm_le_const hb
    simp only [sub_zero, abs_one, mul_one] at this
    exact this.trans_lt (half_lt_self hε)
  have hliou : Continuous fun p : V n × V n => liouville p.1 p.2 := by
    unfold liouville omega0 dot
    refine Continuous.div_const (continuous_finset_sum _ fun k _ => ?_) _
    refine Continuous.mul ?_ ((continuous_apply k).comp continuous_snd)
    unfold j0
    split_ifs
    · exact ((continuous_apply _).comp continuous_fst).neg
    · exact (continuous_apply _).comp continuous_fst
  have hP : ContDiffOn ℝ ∞ (proj H) {0}ᶜ := (contDiffOn_proj_aCoord H hH).1
  have hconstP : JHolomorphic.TendstoCInftyLocOn (fun _ : ℕ => proj H) (proj H) {0}ᶜ :=
    fun K _ _ m s hs => Filter.Eventually.of_forall fun _ x _ => refl_mem_uniformity hs
  have hconstγ : JHolomorphic.TendstoCInftyLocOn (fun _ : ℕ => γ) γ Set.univ :=
    fun K _ _ m s hs => Filter.Eventually.of_forall fun _ x _ => refl_mem_uniformity hs
  have h1 := tendstoCInftyLocOn_comp hU isOpen_compl_singleton u u₀ (fun _ => proj H) (proj H)
    hu hu₀ (fun _ => hP) hP (fun k z hz => hne k z hz) (fun z hz => hne₀ z hz) hconv hconstP
  have hPu : ∀ k, ContDiffOn ℝ ∞ (proj H ∘ u k) U :=
    fun k => hP.comp (hu k) (fun z hz => hne k z hz)
  have hPu₀ : ContDiffOn ℝ ∞ (proj H ∘ u₀) U := hP.comp hu₀ (fun z hz => hne₀ z hz)
  have h2 := tendstoCInftyLocOn_comp isOpen_univ hU (fun _ => γ) γ (fun k => proj H ∘ u k)
    (proj H ∘ u₀) (fun _ => hγ.contDiffOn) hγ.contDiffOn hPu hPu₀ (fun _ t _ => hγU t)
    (fun t _ => hγU t) hconstγ h1
  set ℓ : ℕ → ℝ → V n := fun k => loopInS H (u k) γ with hℓ
  set ℓ₀ : ℝ → V n := loopInS H u₀ γ with hℓ₀
  have hℓeq : (fun k => (proj H ∘ u k) ∘ γ) = ℓ := rfl
  have hℓ₀eq : (proj H ∘ u₀) ∘ γ = ℓ₀ := rfl
  rw [hℓeq, hℓ₀eq] at h2
  have hℓs : ∀ k, ContDiff ℝ ∞ (ℓ k) := fun k =>
    contDiffOn_univ.1 ((hPu k).comp hγ.contDiffOn (fun t _ => hγU t))
  have hℓ₀s : ContDiff ℝ ∞ ℓ₀ := contDiffOn_univ.1 (hPu₀.comp hγ.contDiffOn (fun t _ => hγU t))
  have hK : IsCompact (Set.Icc (0 : ℝ) 1) := isCompact_Icc
  have hc0 : TendstoUniformlyOn ℓ ℓ₀ atTop (Set.Icc 0 1) := by
    have h := h2 _ (Set.subset_univ _) hK 0
    have hev : UniformContinuous fun L : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => ℝ) (V n) =>
        L Fin.elim0 :=
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => ℝ) (V n) Fin.elim0).uniformContinuous
    have := hev.comp_tendstoUniformlyOn h
    simpa [Function.comp_def, iteratedFDeriv_zero_apply] using this
  have hc1 : TendstoUniformlyOn (fun k => deriv (ℓ k)) (deriv ℓ₀) atTop (Set.Icc 0 1) := by
    have h := h2 _ (Set.subset_univ _) hK 1
    have hev : UniformContinuous fun L : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => ℝ) (V n) =>
        L (fun _ => 1) :=
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => ℝ) (V n) (fun _ => 1)).uniformContinuous
    have := hev.comp_tendstoUniformlyOn h
    simpa [Function.comp_def, iteratedFDeriv_one_apply, fderiv_apply_one_eq_deriv] using this
  have hd1 : (1 : WithTop ℕ∞) ≤ (⊤ : ℕ∞) := by exact_mod_cast le_top
  have hcont : ∀ f : ℝ → V n, ContDiff ℝ ∞ f →
      Continuous fun t => liouville (f t) (deriv f t) := fun f hf =>
    hliou.comp (hf.continuous.prodMk (hf.continuous_deriv hd1))
  have hpair := hprod _ _ _ _ hc0 hc1
  have hint := hcomp hK _ _
    ((hℓ₀s.continuous.prodMk (hℓ₀s.continuous_deriv hd1)).continuousOn) hpair
    (fun p : V n × V n => liouville p.1 p.2) hliou
  exact hintegral _ _ (fun k => (hcont _ (hℓs k)).continuousOn) (hcont _ hℓ₀s).continuousOn hint

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (U : Set ℂ) (hU : IsOpen U) (u : ℕ → ℂ → V n)
    (u₀ : ℂ → V n) (hu : ∀ k, ContDiffOn ℝ ∞ (u k) U) (hu₀ : ContDiffOn ℝ ∞ u₀ U)
    (hne : ∀ k, ∀ z ∈ U, u k z ≠ 0) (hne₀ : ∀ z ∈ U, u₀ z ≠ 0)
    (hconv : JHolomorphic.TendstoCInftyLocOn u u₀ U) (γ : ℝ → ℂ) (hγ : ContDiff ℝ ∞ γ)
    (hγU : ∀ t, γ t ∈ U) :
    Tendsto (fun k => loopAction H (u k) γ) atTop (𝓝 (loopAction H u₀ γ)) :=
  tendsto_loopAction_of_tendstoCInftyLocOn_aux H hH U hU u u₀ hu hu₀ hne hne₀ hconv γ hγ hγU
