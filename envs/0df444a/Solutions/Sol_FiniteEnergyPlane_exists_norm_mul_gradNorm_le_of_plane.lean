-- Prove2me | solution 1 for FiniteEnergyPlane.exists_norm_mul_gradNorm_le_of_plane
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-25T21:42:27.167978+00:00
-- url     : https://prove2.me/submissions/8d8226e4-1151-4af9-a33c-f89d88b8df3e

import Definitions.Def_FiniteEnergyPlane_Setting
import Theorems.Thm_FiniteEnergyPlane_exists_blowup_points
import Theorems.Thm_FiniteEnergyPlane_rescale_isFiniteEnergyCurve
import Theorems.Thm_FiniteEnergyPlane_exists_plane_of_gradNorm_le
import Theorems.Thm_FiniteEnergyPlane_dlambdaEnergy_pos_of_plane
import Theorems.Thm_FiniteEnergyPlane_jtilde_isAlmostComplexOn



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- `dλ`-energy as a measure. -/
theorem dlambdaEnergy_eq_withDensity {n : ℕ} (H : V n → ℝ) (u : ℂ → V n) (s : Set ℂ)
    (hs : MeasurableSet s) :
    dlambdaEnergy H s u =
      (volume.withDensity (fun z => ENNReal.ofReal (dlambdaDensity H u z))) s :=
  (withDensity_apply _ hs).symm

/-- The `dλ`-energy outside large discs tends to `0`. -/
theorem tendsto_dlambdaEnergy_norm_gt {n : ℕ} (H : V n → ℝ) (u : ℂ → V n)
    (hD : dlambdaEnergy H Set.univ u ≠ ⊤) :
    Tendsto (fun r : ℝ => dlambdaEnergy H {z | r < ‖z‖} u) atTop (𝓝 0) := by
  set μ := volume.withDensity (fun z => ENNReal.ofReal (dlambdaDensity H u z)) with hμ
  have hmeas : ∀ r : ℝ, MeasurableSet {z : ℂ | r < ‖z‖} :=
    fun r => measurableSet_lt measurable_const measurable_norm
  have hanti : Antitone (fun r : ℝ => {z : ℂ | r < ‖z‖}) :=
    fun a b hab z hz => lt_of_le_of_lt hab hz
  have hfin : ∃ r : ℝ, μ {z : ℂ | r < ‖z‖} ≠ ⊤ := ⟨0, by
    rw [← dlambdaEnergy_eq_withDensity H u _ (hmeas 0)]
    exact ne_top_of_le_ne_top hD (lintegral_mono_set (Set.subset_univ _))⟩
  have h := tendsto_measure_iInter_atTop (μ := μ) (fun r => (hmeas r).nullMeasurableSet) hanti hfin
  have hI : (⋂ r : ℝ, {z : ℂ | r < ‖z‖}) = ∅ := by
    ext z
    simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_forall,
      not_lt]
    exact ⟨‖z‖, le_rfl⟩
  rw [hI, measure_empty] at h
  refine h.congr fun r => ?_
  exact (dlambdaEnergy_eq_withDensity H u _ (hmeas r)).symm

/-- A plane whose `dλ`-energy vanishes on every disc has zero `dλ`-energy. -/
theorem dlambdaEnergy_univ_eq_zero {n : ℕ} (H : V n → ℝ) (w : ℂ → V n)
    (h0 : ∀ R : ℝ, dlambdaEnergy H (ball 0 R) w = 0) : dlambdaEnergy H Set.univ w = 0 := by
  set μ := volume.withDensity (fun z => ENNReal.ofReal (dlambdaDensity H w z)) with hμ
  have hmono : Monotone (fun N : ℕ => ball (0 : ℂ) N) :=
    fun i j hij => ball_subset_ball (by exact_mod_cast hij)
  have hU : (⋃ N : ℕ, ball (0 : ℂ) N) = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
    exact Set.mem_iUnion.2 ⟨N, mem_ball_zero_iff.2 hN⟩
  have h := tendsto_measure_iUnion_atTop (μ := μ) hmono
  rw [hU, ← dlambdaEnergy_eq_withDensity H w _ MeasurableSet.univ] at h
  have hc : (μ ∘ fun N : ℕ => ball (0 : ℂ) N) = fun _ => 0 := by
    funext N
    simp only [Function.comp_apply]
    rw [← dlambdaEnergy_eq_withDensity H w _ measurableSet_ball, h0]
  rw [hc] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

/-- Gradient bound of a finite-energy plane in cylindrical coordinates. -/
theorem exists_norm_mul_gradNorm_le_of_plane_aux {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n) (hu : IsFiniteEnergyCurve H J Set.univ u) :
    ∃ C : ℝ, ∀ z : ℂ, ‖z‖ * gradNorm H u z ≤ C := by
  classical
  obtain ⟨-, hprojs, haCs, -, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  -- continuity of `gradNorm`
  have hgc : Continuous (gradNorm H u) := by
    obtain ⟨hsm, hne, -, -⟩ := hu
    have ha : ContDiffOn ℝ ∞ (fun z => aCoord H (u z)) Set.univ :=
      haCs.comp hsm (fun z hz => hne z hz)
    have hp : ContDiffOn ℝ ∞ (fun z => proj H (u z)) Set.univ :=
      hprojs.comp hsm (fun z hz => hne z hz)
    exact continuousOn_univ.1
      ((ha.continuousOn_fderiv_of_isOpen isOpen_univ (by simp)).norm.add
        (hp.continuousOn_fderiv_of_isOpen isOpen_univ (by simp)).norm)
  have hg0 : ∀ z, 0 ≤ gradNorm H u z := fun z => add_nonneg (norm_nonneg _) (norm_nonneg _)
  by_contra hcon
  push_neg at hcon
  choose z hz using fun k : ℕ => hcon k
  set s : ℕ → ℝ := fun k => ‖z k‖ with hsdef
  have hspos : ∀ k, 0 < s k := by
    intro k
    show 0 < ‖z k‖
    have := hz k
    by_contra hle
    push_neg at hle
    have h0 : ‖z k‖ = 0 := le_antisymm hle (norm_nonneg _)
    rw [h0, zero_mul] at this
    exact absurd this (not_lt.2 (Nat.cast_nonneg k))
  -- `‖z k‖ → ∞`
  have hsinf : Tendsto s atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro r
    obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) r).exists_bound_of_continuousOn
      (continuous_norm.mul hgc).continuousOn
    obtain ⟨K, hK⟩ := exists_nat_gt B
    refine ⟨K, fun k hk => ?_⟩
    by_contra hlt
    push_neg at hlt
    have hmem : z k ∈ closedBall (0 : ℂ) r := mem_closedBall_zero_iff.2 hlt.le
    have h1 : ‖z k‖ * gradNorm H u (z k) ≤ B :=
      (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hB _ hmem)
    have h2 : (K : ℝ) ≤ k := by exact_mod_cast hk
    linarith [hz k]
  -- blow-up functions on the unit-scale discs around `z k`
  obtain ⟨g, hgdef⟩ : ∃ g : ℕ → ℂ → ℝ, g = fun k w => s k * gradNorm H u (z k + s k • w) :=
    ⟨_, rfl⟩
  obtain ⟨U, hUdef⟩ : ∃ U : ℕ → Set ℂ, U = fun _ => ball (0 : ℂ) (1 / 2) := ⟨_, rfl⟩
  have hgcont : ∀ k, ContinuousOn (g k) (U k) := fun k => by
    have hlin : Continuous (fun w : ℂ => z k + s k • w) := by fun_prop
    have h := (continuous_const (y := s k)).mul (hgc.comp hlin)
    rw [hgdef]
    exact h.continuousOn
  have hgnn : ∀ k w, 0 ≤ g k w := fun k w => by
    rw [hgdef]; exact mul_nonneg (hspos k).le (hg0 _)
  have hg00 : ∀ k, g k 0 = ‖z k‖ * gradNorm H u (z k) := by
    intro k; simp [hgdef, hsdef]
  have hgpos : ∀ k, 0 < g k ((fun _ => (0 : ℂ)) k) := fun k => by
    simp only [hg00]; exact lt_of_le_of_lt (Nat.cast_nonneg k) (hz k)
  have hgblow : Tendsto (fun k => g k ((fun _ => (0 : ℂ)) k)) atTop atTop := by
    simp only [hg00]
    exact tendsto_atTop_mono (fun k => (hz k).le) tendsto_natCast_atTop_atTop
  have hball : ∀ k, closedBall ((fun _ => (0 : ℂ)) k) (1 / 4) ⊆ U k := fun k => by
    rw [hUdef]; exact closedBall_subset_ball (by norm_num)
  obtain ⟨ζ, ε, hε, hε0, hεR, -, hRpos, hsub, hdbl⟩ :=
    exists_blowup_points g U (fun _ => 0) (1 / 4) (by norm_num) hball hgcont hgnn hgpos hgblow
  set R : ℕ → ℝ := fun k => g k (ζ k) with hR
  set z₀ : ℕ → ℂ := fun k => z k + s k • ζ k with hz₀
  set t : ℕ → ℝ := fun k => s k / R k with htdef
  have htpos : ∀ k, 0 < t k := fun k => div_pos (hspos k) (hRpos k)
  set a : ℕ → ℝ := fun k => aCoord H (u (z₀ k)) with ha
  set c : ℕ → ℝ := fun k => Real.exp (-2 * a k) with hc
  have hcpos : ∀ k, 0 < c k := fun k => Real.exp_pos _
  set v : ℕ → ℂ → V n := fun k w => c k • u (z₀ k + t k • w) with hv
  set ρ : ℕ → ℝ := fun k => ε k * R k with hρ
  have hD := fun k => rescale_isFiniteEnergyCurve H hH J hJ Set.univ isOpen_univ u hu (z₀ k) (t k)
    (htpos k) (c k) (hcpos k)
  have hpre : ∀ k, {w : ℂ | z₀ k + t k • w ∈ (Set.univ : Set ℂ)} = Set.univ := fun k => by
    ext; simp
  -- the point of the original plane hit by `v k` at `w`
  have hpt : ∀ k w, z₀ k + t k • w = z k + s k • (ζ k + (R k)⁻¹ • w) := by
    intro k w
    simp only [hz₀, htdef, smul_add, smul_smul, div_eq_mul_inv]
    abel
  have hmem : ∀ k, ∀ w ∈ ball (0 : ℂ) (ρ k), ζ k + (R k)⁻¹ • w ∈ ball (ζ k) (ε k) := by
    intro k w hw
    rw [mem_ball_zero_iff] at hw
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 (hRpos k)), inv_mul_lt_iff₀ (hRpos k)]
    simpa [hρ, mul_comm] using hw
  have hvfe : ∀ k, IsFiniteEnergyCurve H J (ball 0 (ρ k)) (v k) := by
    intro k
    obtain ⟨h0, -, -, -⟩ := hD k
    rw [hpre k] at h0
    obtain ⟨h1, h2, h3, h4⟩ := h0
    refine ⟨h1.mono (Set.subset_univ _), fun w hw => h2 w (Set.mem_univ _),
      fun w hw => h3 w (Set.mem_univ _), lt_of_le_of_lt ?_ h4⟩
    exact iSup₂_mono fun φ _ => lintegral_mono_set (Set.subset_univ _)
  set C : ℝ := (energy H Set.univ u).toReal with hCdef
  have hvC : ∀ k, energy H (ball 0 (ρ k)) (v k) ≤ ENNReal.ofReal C := by
    intro k
    obtain ⟨-, -, -, hE⟩ := hD k
    have he := (hE Set.univ subset_rfl MeasurableSet.univ).1
    rw [hpre k] at he
    calc energy H (ball 0 (ρ k)) (v k) ≤ energy H Set.univ (v k) :=
          iSup₂_mono fun φ _ => lintegral_mono_set (Set.subset_univ _)
      _ = energy H Set.univ u := he
      _ = ENNReal.ofReal C := by rw [hCdef, ENNReal.ofReal_toReal hu.2.2.2.ne]
  have hvgrad : ∀ k, ∀ w ∈ ball (0 : ℂ) (ρ k), gradNorm H (v k) w ≤ 2 := by
    intro k w hw
    obtain ⟨-, -, hG, -⟩ := hD k
    rw [hG w (Set.mem_univ _), hpt k w]
    have h := hdbl k _ (ball_subset_closedBall (hmem k w hw))
    have hRk := hRpos k
    have e : t k * gradNorm H u (z k + s k • (ζ k + (R k)⁻¹ • w)) =
        (R k)⁻¹ * g k (ζ k + (R k)⁻¹ • w) := by
      simp only [htdef, hgdef]; field_simp
    rw [e]
    calc (R k)⁻¹ * g k (ζ k + (R k)⁻¹ • w) ≤ (R k)⁻¹ * (2 * R k) :=
          mul_le_mul_of_nonneg_left h (inv_pos.2 hRk).le
      _ = 2 := by rw [mul_left_comm, inv_mul_cancel₀ hRk.ne', mul_one]
  have hva0 : ∀ k, aCoord H (v k 0) = 0 := by
    intro k
    obtain ⟨-, hA, -, -⟩ := hD k
    show aCoord H (c k • u (z₀ k + t k • (0 : ℂ))) = 0
    rw [hA 0 (Set.mem_univ _)]
    simp only [smul_zero, add_zero, hc, Real.log_exp, ha]
    ring
  have hvg0 : ∀ k, gradNorm H (v k) 0 = 1 := by
    intro k
    obtain ⟨-, -, hG, -⟩ := hD k
    rw [hG 0 (Set.mem_univ _), smul_zero, add_zero]
    have e : gradNorm H u (z₀ k) = R k / s k := by
      simp only [hR, hgdef, hz₀]
      field_simp [(hspos k).ne']
    rw [e, htdef]
    show s k / R k * (R k / s k) = 1
    rw [div_mul_div_comm, mul_comm (s k), div_self (mul_pos (hRpos k) (hspos k)).ne']
  obtain ⟨φ, hφ, w, hw, hnc, -, hlim⟩ :=
    exists_plane_of_gradNorm_le H hH J hJ v ρ hεR hvfe C hvC hvgrad hva0 hvg0
  -- the bubble carries no `dλ`-energy
  have hDu : dlambdaEnergy H Set.univ u ≠ ⊤ := by
    have hadm : Admissible (fun _ : ℝ => (1 : ℝ)) :=
      ⟨contDiff_const, monotone_const, fun _ => ⟨zero_le_one, le_rfl⟩⟩
    refine ne_top_of_le_ne_top hu.2.2.2.ne (le_trans (le_of_eq ?_)
      (le_iSup₂ (f := fun (φ : ℝ → ℝ) (_ : Admissible φ) =>
        ∫⁻ z in Set.univ, ENNReal.ofReal (energyDensity H φ u z)) _ hadm))
    simp [dlambdaEnergy, energyDensity, dlambdaDensity]
  have htail := (tendsto_dlambdaEnergy_norm_gt H u hDu).comp
    ((hsinf.atTop_div_const (by norm_num : (0 : ℝ) < 2)).comp hφ.tendsto_atTop)
  have hzero : ∀ R' : ℝ, dlambdaEnergy H (ball 0 R') w = 0 := by
    intro R'
    refine le_antisymm ((hlim R').trans ?_) bot_le
    have hev : ∀ᶠ j in atTop, dlambdaEnergy H (ball 0 R') (v (φ j)) ≤
        dlambdaEnergy H {x | s (φ j) / 2 < ‖x‖} u := by
      have hρφ : Tendsto (fun j => ρ (φ j)) atTop atTop := hεR.comp hφ.tendsto_atTop
      filter_upwards [hρφ.eventually (eventually_ge_atTop R')] with j hj
      obtain ⟨-, -, -, hE⟩ := hD (φ j)
      have he := (hE {x | s (φ j) / 2 < ‖x‖} (Set.subset_univ _)
        (measurableSet_lt measurable_const measurable_norm)).2
      rw [← he]
      refine lintegral_mono_set fun y hy => ?_
      have hy' : y ∈ ball (0 : ℂ) (ρ (φ j)) := ball_subset_ball hj hy
      have h1 := hsub (φ j) (ball_subset_closedBall (hmem (φ j) y hy'))
      simp only [hUdef, mem_ball_zero_iff] at h1
      show s (φ j) / 2 < ‖z₀ (φ j) + t (φ j) • y‖
      rw [hpt]
      have hsk := hspos (φ j)
      have h2 : ‖s (φ j) • (ζ (φ j) + (R (φ j))⁻¹ • y)‖ < s (φ j) / 2 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hsk]; nlinarith
      have h3 := norm_sub_norm_le (z (φ j)) (-(s (φ j) • (ζ (φ j) + (R (φ j))⁻¹ • y)))
      rw [sub_neg_eq_add, norm_neg] at h3
      have : ‖z (φ j)‖ = s (φ j) := rfl
      linarith
    calc liminf (fun j => dlambdaEnergy H (ball 0 R') (v (φ j))) atTop
        ≤ liminf (fun j => dlambdaEnergy H {x | s (φ j) / 2 < ‖x‖} u) atTop :=
          liminf_le_liminf hev
      _ = 0 := htail.liminf_eq
  exact (dlambdaEnergy_pos_of_plane H hH J hJ w hw hnc).ne'
    (dlambdaEnergy_univ_eq_zero H w hzero)

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n) (hu : IsFiniteEnergyCurve H J Set.univ u) :
    ∃ C : ℝ, ∀ z : ℂ, ‖z‖ * gradNorm H u z ≤ C :=
  exists_norm_mul_gradNorm_le_of_plane_aux H hH J hJ u hu
