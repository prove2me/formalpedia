-- Prove2me | solution 1 for FiniteEnergyPlane.injOn_pageMap_of_isPageFamilyOn
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-22T19:52:35.712461+00:00
-- url     : https://prove2.me/submissions/b1c659f5-a424-4eaa-9685-322a7b65969d

import Definitions.Def_FiniteEnergyPlane_OpenBook
import Theorems.Thm_FiniteEnergyPlane_exists_affine_slice_relation_of_pageMap_eq
import Theorems.Thm_FiniteEnergyPlane_contDiffOn_pageMap
import Theorems.Thm_FiniteEnergyPlane_continuousOn_fderiv_slice
import Theorems.Thm_FiniteEnergyPlane_tendstoUniformlyOn_slice_of_continuousOn
import Theorems.Thm_FiniteEnergyPlane_tendstoUniformlyOn_fderiv_exp_smul_sub_of_tendstoUniformlyOn
import Theorems.Thm_FiniteEnergyPlane_eventually_lt_dlambdaEnergy_slice
import Theorems.Thm_FiniteEnergyPlane_exists_radius_lt_dlambdaEnergy_ball
import Theorems.Thm_FiniteEnergyPlane_norm_lt_of_affine_of_dlambdaEnergy_lt
import Theorems.Thm_FiniteEnergyPlane_exists_equiv_hasStrictFDerivAt_exp_smul_sub
import Theorems.Thm_FiniteEnergyPlane_exists_tendsto_zero_of_tendsto_fderiv
import Theorems.Thm_FiniteEnergyPlane_isFastPlane_immersion_transverse
import Theorems.Thm_FiniteEnergyPlane_injective_proj_of_isEmbeddedPlane
import Theorems.Thm_FiniteEnergyPlane_dlambdaEnergy_univ_eq_of_isNondegenerateEnd
import Theorems.Thm_FiniteEnergyPlane_contDiffAt_aCoord_proj
import Theorems.Thm_FiniteEnergyPlane_proj_aCoord_exp_smul



/-!
# (I): `pageMap` of a page family is injective near each time (Hryniewicz 2012, Lemma 7.2)

Glue over published children only.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem injOn_pageMap_of_isPageFamilyOn_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (γ : ℝ) (y : ℝ → V 1) (hy : IsReebTrajectory H y)
    (l : ℕ) (hl : 1 ≤ l) (I : Set ℝ) (hI : IsOpen I) (U : ℝ × ℂ → V 1)
    (hU : IsPageFamilyOn H J P γ y l I U) (t₀ : ℝ) (ht₀ : t₀ ∈ I) :
    ∃ ε > 0, ball t₀ ε ⊆ I ∧ Set.InjOn (pageMap H U) (ball t₀ ε ×ˢ Set.univ) := by
  obtain ⟨δ, hδ, hδI⟩ := Metric.isOpen_iff.1 hI t₀ ht₀
  have hU1 : ContDiffOn ℝ 1 U (I ×ˢ Set.univ) := hU.1.of_le (by exact_mod_cast hl)
  have hne : ∀ p ∈ I ×ˢ (Set.univ : Set ℂ), U p ≠ 0 := fun p hp =>
    (hU.2 p.1 hp.1).1.1.1.2.1 p.2 (Set.mem_univ _)
  have hinjs : ∀ t ∈ I, Function.Injective (fun z => proj H (U (t, z))) := fun t ht =>
    injective_proj_of_isEmbeddedPlane H hH J hJ P _ (hU.2 t ht).1.1 (hU.2 t ht).1.2.1
      (hU.2 t ht).2
  have hU0 : ∀ t ∈ I, U (t, 0) = y t := fun t ht => (hU.2 t ht).1.2.2.1
  by_contra hcon
  push_neg at hcon
  -- radii `δ / (n + 1)`
  set εn : ℕ → ℝ := fun n => δ / ((n : ℝ) + 1) with hεn
  have hεpos : ∀ n, 0 < εn n := fun n => by positivity
  have hεle : ∀ n, εn n ≤ δ := fun n =>
    div_le_self hδ.le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have hε0 : Tendsto εn atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul δ
    rw [mul_zero] at this
    refine this.congr fun n => ?_
    simp only [hεn]; ring
  have hballI : ∀ n, ball t₀ (εn n) ⊆ I := fun n => (ball_subset_ball (hεle n)).trans hδI
  have hseq : ∀ n : ℕ, ∃ p : ℝ × ℂ, ∃ q : ℝ × ℂ, p.1 ∈ ball t₀ (εn n) ∧ q.1 ∈ ball t₀ (εn n) ∧
      pageMap H U p = pageMap H U q ∧ p ≠ q := by
    intro n
    have h := hcon _ (hεpos n) (hballI n)
    simp only [Set.InjOn, not_forall] at h
    obtain ⟨p, hp, q, hq, he, hpq⟩ := h
    exact ⟨p, q, hp.1, hq.1, he, hpq⟩
  choose p q hp hq hpq hpq' using hseq
  have htne : ∀ n, (p n).1 ≠ (q n).1 := by
    intro n hn
    apply hpq' n
    have h2 : (p n).2 = (q n).2 := by
      apply hinjs _ (hballI n (hp n))
      calc pageMap H U ((p n).1, (p n).2) = pageMap H U (q n) := hpq n
        _ = pageMap H U ((p n).1, (q n).2) := by rw [hn]
    exact Prod.ext hn h2
  have hpair : ∀ n, ∃ (σ σ' c : ℝ) (A B : ℂ),
      ((σ = (p n).1 ∧ σ' = (q n).1) ∨ (σ = (q n).1 ∧ σ' = (p n).1)) ∧ A ≠ 0 ∧ ‖A‖ ≤ 1 ∧
      ∀ w, U (σ, A * w + B) = Real.exp (2 * c) • U (σ', w) := fun n =>
    exists_affine_slice_relation_of_pageMap_eq H hH J hJ P hcz γ y l I U hU (p n).1 (q n).1
      (hballI n (hp n)) (hballI n (hq n)) (p n).2 (q n).2 (hpq n)
  choose σ σ' c A B hor hA hA1 hrel using hpair
  have hσb : ∀ n, σ n ∈ ball t₀ (εn n) ∧ σ' n ∈ ball t₀ (εn n) := fun n => by
    rcases hor n with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact ⟨hp n, hq n⟩
    · rw [h1, h2]; exact ⟨hq n, hp n⟩
  have hσne : ∀ n, σ n ≠ σ' n := fun n => by
    rcases hor n with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact htne n
    · rw [h1, h2]; exact (htne n).symm
  have hσI : ∀ n, σ n ∈ I := fun n => hballI n (hσb n).1
  have hσI' : ∀ n, σ' n ∈ I := fun n => hballI n (hσb n).2
  have htend : ∀ τ : ℕ → ℝ, (∀ n, τ n ∈ ball t₀ (εn n)) → Tendsto τ atTop (𝓝 t₀) := by
    intro τ hτ
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun n => dist_nonneg) (fun n => (mem_ball.1 (hτ n)).le) hε0
  have hσt : Tendsto σ atTop (𝓝 t₀) := htend σ fun n => (hσb n).1
  have hσt' : Tendsto σ' atTop (𝓝 t₀) := htend σ' fun n => (hσb n).2
  -- the base plane
  set u₀ : ℂ → V 1 := fun z => U (t₀, z) with hu₀def
  have hm₀ := hU.2 t₀ ht₀
  have hu₀0 : u₀ 0 = y t₀ := hU0 t₀ ht₀
  have hsc : ∀ t ∈ I, ContDiff ℝ 1 (fun z => U (t, z)) := fun t ht =>
    (contDiffOn_univ.1 (hU.2 t ht).1.1.1.1).of_le (by exact_mod_cast le_top)
  have hu₀c : ContDiff ℝ 1 u₀ := hsc t₀ ht₀
  -- energy: `‖B n‖` is eventually bounded
  have htot : ∀ t ∈ I, dlambdaEnergy H Set.univ (fun z => U (t, z)) = ENNReal.ofReal P.T :=
    fun t ht => dlambdaEnergy_univ_eq_of_isNondegenerateEnd H hH J hJ _ (hU.2 t ht).1.1.1 P
      (hU.2 t ht).1.2.1
  have hhalf : ENNReal.ofReal (P.T / 2) + ENNReal.ofReal (P.T / 2) = ENNReal.ofReal P.T := by
    rw [← ENNReal.ofReal_add (by linarith [P.T_pos]) (by linarith [P.T_pos]), add_halves]
  obtain ⟨ρ, hρ0, hρ⟩ := exists_radius_lt_dlambdaEnergy_ball H u₀ (ENNReal.ofReal (P.T / 2))
    (by rw [htot t₀ ht₀]; exact (ENNReal.ofReal_lt_ofReal_iff P.T_pos).2 (half_lt_self P.T_pos))
  have hEσ := eventually_lt_dlambdaEnergy_slice H hH U I hI hU1 hne t₀ ht₀ σ hσI hσt
    (ball 0 ρ) _ hρ
  have hEσ' := eventually_lt_dlambdaEnergy_slice H hH U I hI hU1 hne t₀ ht₀ σ' hσI' hσt'
    (ball 0 ρ) _ hρ
  have hBb : ∀ᶠ n in atTop, B n ∈ closedBall (0 : ℂ) (2 * ρ) := by
    filter_upwards [hEσ, hEσ'] with n h1 h2
    have hw : Differentiable ℝ (fun w => proj H (U (σ n, w))) := fun w =>
      ((contDiffOn_pageMap H hH U I hI hU1 hne).contDiffAt
        ((hI.prod isOpen_univ).mem_nhds ⟨hσI n, Set.mem_univ w⟩)).differentiableAt
        (by norm_num) |>.comp w ((differentiableAt_const _).prodMk differentiableAt_id)
    have hlt := norm_lt_of_affine_of_dlambdaEnergy_lt H hH (fun w => U (σ n, w))
      (fun w => U (σ' n, w)) (c n) (A n) (B n) (hA n) hw
      (fun w => hne _ ⟨hσI' n, Set.mem_univ w⟩) (hrel n) ρ
      (by rw [htot _ (hσI n), ← hhalf]; exact ENNReal.add_lt_add h1 h2)
    rw [mem_closedBall, dist_zero_right]
    have : ‖A n‖ * ρ ≤ ρ := mul_le_of_le_one_left hρ0 (hA1 n)
    linarith
  -- the relation at `0`
  have hrel0 : ∀ n, U (σ n, B n) = Real.exp (2 * c n) • y (σ' n) := fun n => by
    have h := hrel n 0
    rwa [mul_zero, zero_add, hU0 _ (hσI' n)] at h
  have hpmc : ContinuousOn (pageMap H U) (I ×ˢ Set.univ) :=
    (contDiffOn_pageMap H hH U I hI hU1 hne).continuousOn
  have hyc : Continuous y := continuous_iff_continuousAt.2 fun t => (hy.2 t).continuousAt
  have hy0 : y t₀ ≠ 0 := hU0 t₀ ht₀ ▸ hne _ ⟨ht₀, Set.mem_univ 0⟩
  have hpc : ContinuousAt (proj H) (y t₀) := (contDiffAt_aCoord_proj H hH _ hy0).2.continuousAt
  -- `B n → 0`
  have hB0 : Tendsto B atTop (𝓝 0) := by
    apply tendsto_of_subseq_tendsto
    intro ns hns
    have hfreq : ∃ᶠ k in atTop, B (ns k) ∈ closedBall (0 : ℂ) (2 * ρ) :=
      (hns.eventually hBb).frequently
    obtain ⟨b, -, φ, hφ, hb⟩ := tendsto_subseq_of_frequently_bounded isBounded_closedBall hfreq
    have hm : Tendsto (fun k => ns (φ k)) atTop atTop := hns.comp hφ.tendsto_atTop
    have h1 : Tendsto (fun k => pageMap H U (σ (ns (φ k)), B (ns (φ k)))) atTop
        (𝓝 (pageMap H U (t₀, b))) :=
      (hpmc.continuousAt ((hI.prod isOpen_univ).mem_nhds ⟨ht₀, Set.mem_univ b⟩)).tendsto.comp
        ((hσt.comp hm).prodMk_nhds hb)
    have h2 : Tendsto (fun k => pageMap H U (σ (ns (φ k)), B (ns (φ k)))) atTop
        (𝓝 (proj H (y t₀))) := by
      have : (fun k => pageMap H U (σ (ns (φ k)), B (ns (φ k)))) =
          fun k => proj H (y (σ' (ns (φ k)))) := by
        funext k
        show proj H (U _) = _
        rw [hrel0, (proj_aCoord_exp_smul H hH _ _ (hU0 (σ' _) (hσI' _) ▸
          hne _ ⟨hσI' _, Set.mem_univ 0⟩)).1]
      rw [this]
      exact hpc.tendsto.comp ((hyc.tendsto t₀).comp (hσt'.comp hm))
    have hb0 : b = 0 := by
      apply hinjs t₀ ht₀
      show pageMap H U (t₀, b) = proj H (U (t₀, 0))
      rw [tendsto_nhds_unique h1 h2, hU0 t₀ ht₀]
    subst hb0
    exact ⟨φ, hb⟩
  -- `c n → 0`
  have hc0 : Tendsto c atTop (𝓝 0) := by
    have hcn : ∀ n, c n = aCoord H (U (σ n, B n)) - aCoord H (y (σ' n)) := fun n => by
      have hy0 : y (σ' n) ≠ 0 := hU0 _ (hσI' n) ▸ hne _ ⟨hσI' n, Set.mem_univ 0⟩
      rw [hrel0, (proj_aCoord_exp_smul H hH _ _ hy0).2]; ring
    have hac : ContinuousAt (aCoord H) (y t₀) :=
      (contDiffAt_aCoord_proj H hH _ hy0).1.continuousAt
    have hUc : ContinuousAt U (t₀, 0) :=
      hU1.continuousOn.continuousAt ((hI.prod isOpen_univ).mem_nhds ⟨ht₀, Set.mem_univ 0⟩)
    have h1 : Tendsto (fun n => aCoord H (U (σ n, B n))) atTop (𝓝 (aCoord H (y t₀))) := by
      have := hUc.tendsto.comp (hσt.prodMk_nhds hB0)
      rw [show U (t₀, 0) = y t₀ from hU0 t₀ ht₀] at this
      exact (hac.tendsto).comp this
    have h2 : Tendsto (fun n => aCoord H (y (σ' n))) atTop (𝓝 (aCoord H (y t₀))) :=
      hac.tendsto.comp ((hyc.tendsto t₀).comp hσt')
    have := h1.sub h2
    rw [sub_self] at this
    exact this.congr fun n => (hcn n).symm
  -- (G) near `(0, 0, t₀)`
  have htr := isFastPlane_immersion_transverse H hH J hJ u₀ hm₀.1.1 0
  obtain ⟨L, -, hfs⟩ := exists_equiv_hasStrictFDerivAt_exp_smul_sub H hH u₀ hu₀c y hy t₀ hu₀0 htr
  have h0u : TendstoUniformlyOn (fun k z => U (σ k, z)) u₀ atTop (closedBall 0 1) :=
    tendstoUniformlyOn_slice_of_continuousOn U I hI hU1.continuousOn t₀ ht₀ 1 σ hσt
  have h1u : TendstoUniformlyOn (fun k => fderiv ℝ (fun z => U (σ k, z))) (fderiv ℝ u₀) atTop
      (closedBall 0 1) :=
    tendstoUniformlyOn_slice_of_continuousOn (fun p : ℝ × ℂ => fderiv ℝ (fun z => U (p.1, z)) p.2)
      I hI (continuousOn_fderiv_slice U I hI hU1) t₀ ht₀ 1 σ hσt
  obtain ⟨hpd, hp0, hpD⟩ := tendstoUniformlyOn_fderiv_exp_smul_sub_of_tendstoUniformlyOn u₀ hu₀c (fun k z => U (σ k, z))
    (fun k => hsc _ (hσI k)) h0u h1u t₀
  have hp : Real.exp (2 * ((0 : ℝ), (0 : ℂ), t₀).1) • u₀ ((0 : ℝ), (0 : ℂ), t₀).2.1 -
      y ((0 : ℝ), (0 : ℂ), t₀).2.2 = 0 := by
    simp [hu₀0]
  obtain ⟨δ', hδ', hinj, -⟩ := exists_tendsto_zero_of_tendsto_fderiv hfs hp one_pos
    (fun k q _ => hpd k q) hp0 hpD
  have hsum : ∀ n (q : ℝ × ℂ × ℝ),
      (Real.exp (2 * q.1) • u₀ q.2.1 - y q.2.2) +
        Real.exp (2 * q.1) • (U (σ n, q.2.1) - u₀ q.2.1) =
      Real.exp (2 * q.1) • U (σ n, q.2.1) - y q.2.2 := fun n q => by
    rw [smul_sub]; abel
  have hx : Tendsto (fun n => ((0 : ℝ), (0 : ℂ), σ n)) atTop (𝓝 ((0 : ℝ), (0 : ℂ), t₀)) :=
    tendsto_const_nhds.prodMk_nhds (tendsto_const_nhds.prodMk_nhds hσt)
  have hx' : Tendsto (fun n => (-c n, B n, σ' n)) atTop (𝓝 ((0 : ℝ), (0 : ℂ), t₀)) := by
    have := hc0.neg.prodMk_nhds (hB0.prodMk_nhds hσt')
    rwa [neg_zero] at this
  obtain ⟨n, hn, hxn, hxn'⟩ := (hinj.and ((hx.eventually (ball_mem_nhds _ hδ')).and
    (hx'.eventually (ball_mem_nhds _ hδ')))).exists
  have hz1 : Real.exp (2 * (0 : ℝ)) • u₀ (0 : ℂ) - y (σ n) +
      Real.exp (2 * (0 : ℝ)) • (U (σ n, (0 : ℂ)) - u₀ 0) = 0 := by
    rw [hsum n ((0 : ℝ), (0 : ℂ), σ n)]
    simp [hU0 _ (hσI n)]
  have hz2 : Real.exp (2 * -c n) • u₀ (B n) - y (σ' n) +
      Real.exp (2 * -c n) • (U (σ n, B n) - u₀ (B n)) = 0 := by
    rw [hsum n (-c n, B n, σ' n)]
    simp only
    rw [hrel0, smul_smul, ← Real.exp_add]
    norm_num
  have heq := hn hxn hxn' (by simp only; rw [hz1, hz2])
  exact hσne n (congrArg (fun q : ℝ × ℂ × ℝ => q.2.2) heq)

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (γ : ℝ) (y : ℝ → V 1) (hy : IsReebTrajectory H y)
    (l : ℕ) (hl : 1 ≤ l) (I : Set ℝ) (hI : IsOpen I) (U : ℝ × ℂ → V 1)
    (hU : IsPageFamilyOn H J P γ y l I U) (t₀ : ℝ) (ht₀ : t₀ ∈ I) :
    ∃ ε > 0, ball t₀ ε ⊆ I ∧ Set.InjOn (pageMap H U) (ball t₀ ε ×ˢ Set.univ) :=
  injOn_pageMap_of_isPageFamilyOn_aux H hH J hJ P hcz γ y hy l hl I hI U hU t₀ ht₀
