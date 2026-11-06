-- Prove2me | solution 1 for FiniteEnergyPlane.exists_intersection_of_tendstoCInftyLocOn
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-05T20:39:58.003159+00:00
-- url     : https://prove2.me/submissions/5505fbf4-1406-43da-a3e0-4755ca8af9cf

import Definitions.Def_FiniteEnergyPlane_Fredholm
import Theorems.Thm_FiniteEnergyPlane_jtilde_isAlmostComplexOn
import Theorems.Thm_FiniteEnergyPlane_exists_normal_chart_hasLoopWind
import Theorems.Thm_FiniteEnergyPlane_exists_uniform_rightInverse_of_fderiv_small
import Theorems.Thm_FiniteEnergyPlane_exists_eq_zero_of_hasLoopWind_of_norm_sub_lt
import Theorems.Thm_FiniteEnergyPlane_exists_tendsto_of_forall_eventually_exists

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

namespace FiniteEnergyPlane

section Conv

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y]

lemma pi_norm_sub_lt_of_tendsto {f : ℕ → X → Y} {g : X → Y} {O K : Set X}
    (hc : JHolomorphic.TendstoCInftyLocOn f g O) (hK : K ⊆ O) (hKc : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ k in atTop, ∀ x ∈ K, ‖f k x - g x‖ < ε := by
  have h := (Metric.tendstoUniformlyOn_iff.1 (hc K hK hKc 0)) ε hε
  filter_upwards [h] with k hk x hx
  have h1 := hk x hx
  rw [dist_comm, dist_eq_norm] at h1
  have h2 := (iteratedFDeriv ℝ 0 (f k) x - iteratedFDeriv ℝ 0 g x).le_opNorm Fin.elim0
  simp only [ContinuousMultilinearMap.sub_apply, iteratedFDeriv_zero_apply, Finset.univ_eq_empty,
    Finset.prod_empty, mul_one] at h2
  exact lt_of_le_of_lt h2 h1

lemma pi_norm_fderiv_sub_lt_of_tendsto {f : ℕ → X → Y} {g : X → Y} {O K : Set X}
    (hc : JHolomorphic.TendstoCInftyLocOn f g O) (hK : K ⊆ O) (hKc : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ k in atTop, ∀ x ∈ K, ‖fderiv ℝ (f k) x - fderiv ℝ g x‖ ≤ ε := by
  have h := (Metric.tendstoUniformlyOn_iff.1 (hc K hK hKc 1)) ε hε
  filter_upwards [h] with k hk x hx
  have h1 := hk x hx
  rw [dist_comm, dist_eq_norm] at h1
  refine ContinuousLinearMap.opNorm_le_bound _ hε.le fun a => ?_
  have h2 := (iteratedFDeriv ℝ 1 (f k) x - iteratedFDeriv ℝ 1 g x).le_opNorm (fun _ : Fin 1 => a)
  simp only [ContinuousMultilinearMap.sub_apply, iteratedFDeriv_one_apply, Fin.prod_univ_one]
    at h2
  rw [ContinuousLinearMap.sub_apply]
  exact h2.trans (mul_le_mul_of_nonneg_right h1.le (norm_nonneg _))

end Conv

theorem exists_intersection_of_tendstoCInftyLocOn_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (U W : Set ℂ) (hU : IsOpen U) (hW : IsOpen W) (u v : ℂ → V 1) (uk vk : ℕ → ℂ → V 1)
    (hu : IsFiniteEnergyCurve H J U u) (hv : IsFiniteEnergyCurve H J W v)
    (hvi : ∀ w ∈ W, Function.Injective (fderiv ℝ v w))
    (huk : ∀ k, IsFiniteEnergyCurve H J U (uk k)) (hvk : ∀ k, IsFiniteEnergyCurve H J W (vk k))
    (hcu : JHolomorphic.TendstoCInftyLocOn uk u U) (hcv : JHolomorphic.TendstoCInftyLocOn vk v W)
    (z₀ w₀ : ℂ) (hz₀ : z₀ ∈ U) (hw₀ : w₀ ∈ W) (h₀ : u z₀ = v w₀)
    (hiso : ∃ ε > 0, ∀ z ∈ ball z₀ ε, ∀ w ∈ ball w₀ ε, u z = v w → z = z₀ ∧ w = w₀) :
    ∃ z w : ℕ → ℂ, Tendsto z atTop (𝓝 z₀) ∧ Tendsto w atTop (𝓝 w₀) ∧
      ∀ᶠ k in atTop, uk k (z k) = vk k (w k) := by
  refine exists_tendsto_of_forall_eventually_exists (fun k z w => uk k z = vk k w) z₀ w₀ ?_
  have hE : Module.finrank ℝ (V 1) = 4 := by simp
  obtain ⟨hJt, -, -, -, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  obtain ⟨Ψ, Ξ, e, hΨ1, hΨe, hΨax, hΞc, hΞ0, hRI, m, hm, r, hr, hwind⟩ :=
    exists_normal_chart_hasLoopWind hE (Jtilde H J) {y | y ≠ 0} hJt U W hU hW u v hu.1 hv.1
      hu.2.1 hv.2.1 hu.2.2.1 hv.2.2.1 z₀ w₀ hz₀ hw₀ h₀ (hvi w₀ hw₀) hiso
  have hΨ0 : Ψ (0, 0) = u z₀ := by
    rw [hΨax 0, add_zero, h₀]
  -- the perturbation terms
  obtain ⟨R₁, hR₁, hR₁s⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hW.mem_nhds hw₀)
  have hcompW : IsCompact (closedBall w₀ R₁) := isCompact_closedBall _ _
  set d : ℕ → ℂ × ℂ → V 1 := fun k p => vk k (w₀ + p.1) - v (w₀ + p.1) with hddef
  have hfst : ∀ (p : ℂ × ℂ) (η : ℝ), p ∈ ball ((0 : ℂ), (0 : ℂ)) η → ‖p.1‖ < η := by
    intro p η hp
    have : ‖p‖ < η := mem_ball_zero_iff.1 hp
    exact lt_of_le_of_lt (norm_fst_le _) this
  have hmemW : ∀ p ∈ ball ((0 : ℂ), (0 : ℂ)) R₁, w₀ + p.1 ∈ closedBall w₀ R₁ := by
    intro p hp
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
    exact (hfst p R₁ hp).le
  have hin : ∀ p : ℂ × ℂ, HasFDerivAt (fun p : ℂ × ℂ => w₀ + p.1)
      (ContinuousLinearMap.fst ℝ ℂ ℂ) p := fun p => hasFDerivAt_fst.const_add w₀
  have hdiffat : ∀ (f : ℂ → V 1), ContDiffOn ℝ ∞ f W → ∀ w ∈ W, DifferentiableAt ℝ f w :=
    fun f hf w hw => (hf.contDiffAt (hW.mem_nhds hw)).differentiableAt (by simp)
  have hdd : ∀ k, ∀ p ∈ ball ((0 : ℂ), (0 : ℂ)) R₁, HasFDerivAt (d k)
      ((fderiv ℝ (vk k) (w₀ + p.1) - fderiv ℝ v (w₀ + p.1)).comp
        (ContinuousLinearMap.fst ℝ ℂ ℂ)) p := by
    intro k p hp
    have hpW := hR₁s (hmemW p hp)
    have h1 : HasFDerivAt (fun p : ℂ × ℂ => vk k (w₀ + p.1))
        ((fderiv ℝ (vk k) (w₀ + p.1)).comp (ContinuousLinearMap.fst ℝ ℂ ℂ)) p :=
      (hdiffat _ (hvk k).1 _ hpW).hasFDerivAt.comp p (hin p)
    have h2 : HasFDerivAt (fun p : ℂ × ℂ => v (w₀ + p.1))
        ((fderiv ℝ v (w₀ + p.1)).comp (ContinuousLinearMap.fst ℝ ℂ ℂ)) p :=
      (hdiffat _ hv.1 _ hpW).hasFDerivAt.comp p (hin p)
    exact (h1.sub h2).congr_fderiv (by ext <;> simp)
  have hdu : ∀ ε > (0 : ℝ), ∀ᶠ k in atTop, ∀ p ∈ ball ((0 : ℂ), (0 : ℂ)) R₁,
      ‖fderiv ℝ (d k) p‖ ≤ ε := by
    intro ε hε
    filter_upwards [pi_norm_fderiv_sub_lt_of_tendsto hcv hR₁s hcompW hε] with k hk p hp
    rw [(hdd k p hp).fderiv]
    refine ContinuousLinearMap.opNorm_le_bound _ hε.le fun q => ?_
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst']
    refine ((fderiv ℝ (vk k) (w₀ + p.1) - fderiv ℝ v (w₀ + p.1)).le_opNorm q.1).trans ?_
    exact mul_le_mul (hk _ (hmemW p hp)) (norm_fst_le q) (norm_nonneg _) hε.le
  have hd0 : Tendsto (fun k => d k ((0 : ℂ), (0 : ℂ))) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [pi_norm_sub_lt_of_tendsto hcv hR₁s hcompW hε] with k hk
    have := hk (w₀ + 0) (by simpa using hR₁.le)
    simpa [hddef, dist_eq_norm] using this
  obtain ⟨K, hK, R₀, hR₀, hinv⟩ := exists_uniform_rightInverse_of_fderiv_small Ψ d e (0, 0) R₁ hR₁ hΨ1
    hΨe (fun k p hp => (hdd k p hp).differentiableAt) hdu hd0
  intro δ hδ
  set η := min δ (min R₀ R₁) with hηdef
  have hη : 0 < η := lt_min hδ (lt_min hR₀ hR₁)
  have hηδ : η ≤ δ := min_le_left _ _
  have hηR₀ : η ≤ R₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hηR₁ : η ≤ R₁ := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨δ', hδ', hevΨ⟩ := hinv η ⟨hη, hηR₀⟩
  rw [hΨ0] at hevΨ
  -- the small circle
  have huc : ContinuousAt u z₀ := (hu.1.contDiffAt (hU.mem_nhds hz₀)).continuousAt
  have hE1 : ∀ᶠ z in 𝓝 z₀, z ∈ U := hU.mem_nhds hz₀
  have hE2 : ∀ᶠ z in 𝓝 z₀, u z ∈ ball (u z₀) (δ' / 2) :=
    huc.preimage_mem_nhds (ball_mem_nhds _ (half_pos hδ'))
  have hE3 : ∀ᶠ z in 𝓝 z₀, Ξ (u z) ∈ ball ((0 : ℂ), (0 : ℂ)) η := by
    have hc : ContinuousAt (fun z => Ξ (u z)) z₀ := ContinuousAt.comp (g := Ξ) hΞc huc
    refine hc.preimage_mem_nhds ?_
    rw [hΞ0]
    exact ball_mem_nhds _ hη
  have hE4 : ∀ᶠ z in 𝓝 z₀, Ψ (Ξ (u z)) = u z := huc.eventually hRI
  obtain ⟨r₂, hr₂, hr₂s⟩ := Metric.eventually_nhds_iff_ball.1 (hE1.and (hE2.and (hE3.and hE4)))
  set ρ := min r₂ (min r δ) / 2 with hρdef
  have hmin : 0 < min r₂ (min r δ) := lt_min hr₂ (lt_min hr hδ)
  have hρ : 0 < ρ := half_pos hmin
  have hρlt : ρ < min r₂ (min r δ) := half_lt_self hmin
  have hρr₂ : ρ < r₂ := hρlt.trans_le (min_le_left _ _)
  have hρr : ρ < r := hρlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hρδ : ρ < δ := hρlt.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hcl : ∀ z ∈ closedBall z₀ ρ, z ∈ ball z₀ r₂ := fun z hz =>
    closedBall_subset_ball hρr₂ hz
  have hclU : closedBall z₀ ρ ⊆ U := fun z hz => (hr₂s z (hcl z hz)).1
  have hloop : HasLoopWind (fun t => (Ξ (u (z₀ + ccwLoop ρ t))).2) (m : ℤ) :=
    hwind ρ ⟨hρ, hρr⟩
  obtain ⟨hLc, hLp, hL0, -⟩ := id hloop
  -- a lower bound on the circle
  obtain ⟨t₀, -, ht₀⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.2 (zero_le_one' ℝ))
    (hLc.norm.continuousOn (s := Set.Icc 0 1))
  set a := ‖(Ξ (u (z₀ + ccwLoop ρ t₀))).2‖ with hadef
  have ha : 0 < a := norm_pos_iff.2 (hL0 t₀)
  have hamin : ∀ t, a ≤ ‖(Ξ (u (z₀ + ccwLoop ρ t))).2‖ := by
    intro t
    obtain ⟨y, hy, hty⟩ := hLp.exists_mem_Ico₀ one_pos t
    rw [hty]
    exact ht₀ (Set.Ico_subset_Icc_self hy)
  have hε : 0 < min (δ' / 2) (a / (2 * K)) := lt_min (half_pos hδ') (by positivity)
  have hε2 : 0 < a / (2 * K) := by positivity
  filter_upwards [hevΨ, pi_norm_sub_lt_of_tendsto hcu hclU (isCompact_closedBall _ _) hε,
    pi_norm_sub_lt_of_tendsto hcv hR₁s hcompW hε2] with k hk hku hkv
  obtain ⟨Ψk, hΨkc, hΨkv, hΨkK⟩ := hk
  have hukball : ∀ z ∈ closedBall z₀ ρ, uk k z ∈ ball (u z₀) δ' := by
    intro z hz
    have h1 : ‖uk k z - u z‖ < δ' / 2 := (hku z hz).trans_le (min_le_left _ _)
    have h2 : dist (u z) (u z₀) < δ' / 2 := (hr₂s z (hcl z hz)).2.1
    rw [mem_ball]
    calc dist (uk k z) (u z₀) ≤ dist (uk k z) (u z) + dist (u z) (u z₀) := dist_triangle _ _ _
      _ < δ' := by rw [dist_eq_norm (uk k z)]; linarith
  have hukc : ContinuousOn (uk k) (closedBall z₀ ρ) :=
    ((huk k).1.continuousOn).mono hclU
  have hgc : ContinuousOn (fun z => (Ψk (uk k z)).2) (closedBall z₀ ρ) :=
    continuous_snd.comp_continuousOn (hΨkc.comp hukc hukball)
  have hcirc : ∀ t : ℝ, z₀ + ccwLoop ρ t ∈ closedBall z₀ ρ := by
    intro t
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
    unfold ccwLoop
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hρ]
  have hclose : ∀ t : ℝ, ‖(Ψk (uk k (z₀ + ccwLoop ρ t))).2 - (Ξ (u (z₀ + ccwLoop ρ t))).2‖ <
      ‖(Ξ (u (z₀ + ccwLoop ρ t))).2‖ := by
    intro t
    set z := z₀ + ccwLoop ρ t with hz
    have hzc : z ∈ closedBall z₀ ρ := hcirc t
    obtain ⟨-, -, hp, hval⟩ := hr₂s z (hcl z hzc)
    have hest := hΨkK _ hp _ (hukball z hzc)
    rw [hval] at hest
    have hp1 : ‖(Ξ (u z)).1‖ < η := hfst _ _ hp
    have hw : w₀ + (Ξ (u z)).1 ∈ closedBall w₀ R₁ := by
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
      exact (hp1.trans_le hηR₁).le
    have hdk : ‖d k (Ξ (u z))‖ < a / (2 * K) := hkv _ hw
    have huk' : ‖uk k z - u z‖ < a / (2 * K) := (hku z hzc).trans_le (min_le_right _ _)
    have hsum : ‖uk k z - (u z + d k (Ξ (u z)))‖ < a / K := by
      have : uk k z - (u z + d k (Ξ (u z))) = (uk k z - u z) - d k (Ξ (u z)) := by abel
      rw [this]
      have h1 := norm_sub_le (uk k z - u z) (d k (Ξ (u z)))
      have h2 : a / (2 * K) + a / (2 * K) = a / K := by
        field_simp
        ring
      linarith
    have hfin : ‖Ξ (u z) - Ψk (uk k z)‖ < a := by
      have := mul_lt_mul_of_pos_left hsum hK
      rw [mul_div_cancel₀ _ hK.ne'] at this
      exact hest.trans_lt this
    have hsnd : ‖(Ψk (uk k z)).2 - (Ξ (u z)).2‖ ≤ ‖Ξ (u z) - Ψk (uk k z)‖ := by
      rw [norm_sub_rev (Ξ (u z))]
      exact norm_snd_le (Ψk (uk k z) - Ξ (u z))
    exact (hsnd.trans_lt hfin).trans_le (hamin t)
  obtain ⟨z, hz, hgz⟩ := exists_eq_zero_of_hasLoopWind_of_norm_sub_lt
    (fun z => (Ψk (uk k z)).2) (fun z => (Ξ (u z)).2) z₀ ρ hρ hgc (m : ℤ)
    (by exact_mod_cast (by omega : m ≠ 0)) hloop hclose
  obtain ⟨hqη, hqeq⟩ := hΨkv _ (hukball z hz)
  set q := Ψk (uk k z) with hq
  have hq2 : q = (q.1, 0) := by
    ext1
    · rfl
    · exact hgz
  refine ⟨z, closedBall_subset_ball hρδ hz, w₀ + q.1, ?_, ?_⟩
  · rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact (hfst _ _ hqη).trans_le hηδ
  · rw [← hqeq, hq2]
    simp only [hddef]
    rw [hΨax]
    simp

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (U W : Set ℂ) (hU : IsOpen U) (hW : IsOpen W) (u v : ℂ → V 1) (uk vk : ℕ → ℂ → V 1)
    (hu : IsFiniteEnergyCurve H J U u) (hv : IsFiniteEnergyCurve H J W v)
    (hui : ∀ z ∈ U, Function.Injective (fderiv ℝ u z))
    (hvi : ∀ w ∈ W, Function.Injective (fderiv ℝ v w))
    (huk : ∀ k, IsFiniteEnergyCurve H J U (uk k)) (hvk : ∀ k, IsFiniteEnergyCurve H J W (vk k))
    (hcu : JHolomorphic.TendstoCInftyLocOn uk u U) (hcv : JHolomorphic.TendstoCInftyLocOn vk v W)
    (z₀ w₀ : ℂ) (hz₀ : z₀ ∈ U) (hw₀ : w₀ ∈ W) (h₀ : u z₀ = v w₀)
    (hiso : ∃ ε > 0, ∀ z ∈ ball z₀ ε, ∀ w ∈ ball w₀ ε, u z = v w → z = z₀ ∧ w = w₀) :
    ∃ z w : ℕ → ℂ, Tendsto z atTop (𝓝 z₀) ∧ Tendsto w atTop (𝓝 w₀) ∧
      ∀ᶠ k in atTop, uk k (z k) = vk k (w k) :=
  FiniteEnergyPlane.exists_intersection_of_tendstoCInftyLocOn_aux H hH J hJ U W hU hW u v uk vk hu hv hvi huk hvk hcu hcv z₀ w₀ hz₀ hw₀ h₀ hiso
