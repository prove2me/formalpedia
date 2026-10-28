-- Prove2me | solution 1 for FiniteEnergyPlane.exists_norm_mul_gradNorm_le_near_puncture
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-26T16:35:49.425095+00:00
-- url     : https://prove2.me/submissions/0cc73363-9c91-474a-9524-f7a1996b5f0b

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
theorem dlambdaEnergy_eq_withDensity' {n : ℕ} (H : V n → ℝ) (u : ℂ → V n) (s : Set ℂ)
    (hs : MeasurableSet s) :
    dlambdaEnergy H s u =
      (volume.withDensity (fun z => ENNReal.ofReal (dlambdaDensity H u z))) s :=
  (withDensity_apply _ hs).symm

/-- A plane whose `dλ`-energy vanishes on every disc has zero `dλ`-energy. -/
theorem dlambdaEnergy_univ_eq_zero' {n : ℕ} (H : V n → ℝ) (w : ℂ → V n)
    (h0 : ∀ R : ℝ, dlambdaEnergy H (ball 0 R) w = 0) : dlambdaEnergy H Set.univ w = 0 := by
  set μ := volume.withDensity (fun z => ENNReal.ofReal (dlambdaDensity H w z)) with hμ
  have hmono : Monotone (fun N : ℕ => ball (0 : ℂ) N) :=
    fun i j hij => ball_subset_ball (by exact_mod_cast hij)
  have hU : (⋃ N : ℕ, ball (0 : ℂ) N) = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
    exact Set.mem_iUnion.2 ⟨N, mem_ball_zero_iff.2 hN⟩
  have h := tendsto_measure_iUnion_atTop (μ := μ) hmono
  rw [hU, ← dlambdaEnergy_eq_withDensity' H w _ MeasurableSet.univ] at h
  have hc : (μ ∘ fun N : ℕ => ball (0 : ℂ) N) = fun _ => 0 := by
    funext N
    simp only [Function.comp_apply]
    rw [← dlambdaEnergy_eq_withDensity' H w _ measurableSet_ball, h0]
  rw [hc] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

/-- The `dλ`-energy of small punctured discs tends to `0`. -/
theorem tendsto_dlambdaEnergy_punctured {n : ℕ} (H : V n → ℝ) (u : ℂ → V n)
    (hD : dlambdaEnergy H {x : ℂ | x ≠ 0 ∧ ‖x‖ < 1} u ≠ ⊤) :
    Tendsto (fun r : ℝ => dlambdaEnergy H {x : ℂ | x ≠ 0 ∧ ‖x‖ < r} u) (𝓝[>] 0) (𝓝 0) := by
  set μ := volume.withDensity (fun z => ENNReal.ofReal (dlambdaDensity H u z)) with hμ
  have hmeas : ∀ r : ℝ, MeasurableSet {x : ℂ | x ≠ 0 ∧ ‖x‖ < r} := fun r =>
    (measurableSet_singleton (0 : ℂ)).compl.inter (measurableSet_lt measurable_norm measurable_const)
  have h := tendsto_measure_biInter_gt (μ := μ) (s := fun r : ℝ => {x : ℂ | x ≠ 0 ∧ ‖x‖ < r})
    (a := 0) (fun r _ => (hmeas r).nullMeasurableSet)
    (fun i j _ hij x hx => ⟨hx.1, lt_of_lt_of_le hx.2 hij⟩)
    ⟨1, one_pos, by rw [← dlambdaEnergy_eq_withDensity' H u _ (hmeas 1)]; exact hD⟩
  have hI : (⋂ r > (0 : ℝ), {x : ℂ | x ≠ 0 ∧ ‖x‖ < r}) = ∅ := by
    ext x
    simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro hx
    by_cases h0 : x = 0
    · exact (hx 1 one_pos).1 h0
    · exact lt_irrefl _ (hx ‖x‖ (norm_pos_iff.2 h0)).2
  rw [hI, measure_empty] at h
  refine h.congr fun r => ?_
  exact (dlambdaEnergy_eq_withDensity' H u _ (hmeas r)).symm

/-- Gradient bound near a puncture. -/
theorem exists_norm_mul_gradNorm_le_near_puncture_aux {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, ∀ z : ℂ, z ≠ 0 → ‖z‖ < r → ‖z‖ * gradNorm H u z ≤ C := by
  classical
  set Ω : Set ℂ := ball 0 1 \ {0} with hΩ
  have hΩo : IsOpen Ω := isOpen_ball.sdiff isClosed_singleton
  have hmemΩ : ∀ x : ℂ, x ∈ Ω ↔ x ≠ 0 ∧ ‖x‖ < 1 := fun x => by
    simp [hΩ, mem_ball_zero_iff, and_comm]
  obtain ⟨-, hprojs, haCs, -, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  -- continuity of `gradNorm` on `Ω`
  have hgc : ContinuousOn (gradNorm H u) Ω := by
    obtain ⟨hsm, hne, -, -⟩ := hu
    have ha : ContDiffOn ℝ ∞ (fun z => aCoord H (u z)) Ω :=
      haCs.comp hsm (fun z hz => hne z hz)
    have hp : ContDiffOn ℝ ∞ (fun z => proj H (u z)) Ω :=
      hprojs.comp hsm (fun z hz => hne z hz)
    exact (ha.continuousOn_fderiv_of_isOpen hΩo (by simp)).norm.add
      (hp.continuousOn_fderiv_of_isOpen hΩo (by simp)).norm
  have hg0 : ∀ z, 0 ≤ gradNorm H u z := fun z => add_nonneg (norm_nonneg _) (norm_nonneg _)
  by_contra hcon
  push_neg at hcon
  choose z hz0 hzr hz using fun k : ℕ =>
    hcon (1 / ((k : ℝ) + 1) / 2) (by positivity) k
  set s : ℕ → ℝ := fun k => ‖z k‖ with hsdef
  have hspos : ∀ k, 0 < s k := fun k => norm_pos_iff.2 (hz0 k)
  have hshalf : ∀ k, s k < 1 / 2 := fun k => by
    have h1 : 1 / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have := hzr k
    show ‖z k‖ < 1 / 2
    linarith
  -- `‖z k‖ → 0`
  have hs0 : Tendsto s atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k => hspos k⟩
    have hb : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1) / 2) atTop (𝓝 0) := by
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat.div_const (2 : ℝ)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
      (fun k => (hspos k).le) (fun k => (hzr k).le)
  -- the half-discs around `z k` stay in an annulus inside `Ω`
  have hann : ∀ k (ξ : ℂ), ‖ξ‖ < 1 / 2 →
      s k / 2 < ‖z k + s k • ξ‖ ∧ ‖z k + s k • ξ‖ < 3 * s k / 2 := by
    intro k ξ hξ
    have hsk := hspos k
    have h2 : ‖s k • ξ‖ < s k / 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hsk]; nlinarith
    have h3 := norm_sub_norm_le (z k) (-(s k • ξ))
    rw [sub_neg_eq_add, norm_neg] at h3
    have h4 := norm_add_le (z k) (s k • ξ)
    have : ‖z k‖ = s k := rfl
    constructor <;> linarith
  have hannΩ : ∀ k (ξ : ℂ), ‖ξ‖ < 1 / 2 → z k + s k • ξ ∈ Ω := by
    intro k ξ hξ
    obtain ⟨h1, h2⟩ := hann k ξ hξ
    rw [hmemΩ]
    refine ⟨fun h => ?_, by linarith [hshalf k]⟩
    rw [h, norm_zero] at h1
    linarith [hspos k]
  -- blow-up functions on the unit-scale discs around `z k`
  obtain ⟨g, hgdef⟩ : ∃ g : ℕ → ℂ → ℝ, g = fun k w => s k * gradNorm H u (z k + s k • w) :=
    ⟨_, rfl⟩
  obtain ⟨U, hUdef⟩ : ∃ U : ℕ → Set ℂ, U = fun _ => ball (0 : ℂ) (1 / 2) := ⟨_, rfl⟩
  have hgcont : ∀ k, ContinuousOn (g k) (U k) := fun k => by
    have hlin : Continuous (fun w : ℂ => z k + s k • w) := by fun_prop
    have hmaps : Set.MapsTo (fun w : ℂ => z k + s k • w) (ball (0 : ℂ) (1 / 2)) Ω :=
      fun w hw => hannΩ k w (mem_ball_zero_iff.1 hw)
    have h := (continuous_const (y := s k)).continuousOn.mul
      (hgc.comp hlin.continuousOn hmaps)
    rw [hgdef, hUdef]
    exact h
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
  have hsubU : ∀ k, ∀ y ∈ closedBall (ζ k) (ε k), ‖y‖ < 1 / 2 := fun k y hy => by
    have h1 := hsub k hy
    simpa [hUdef, mem_ball_zero_iff] using h1
  set R : ℕ → ℝ := fun k => g k (ζ k) with hR
  set z₀ : ℕ → ℂ := fun k => z k + s k • ζ k with hz₀
  set t : ℕ → ℝ := fun k => s k / R k with htdef
  have htpos : ∀ k, 0 < t k := fun k => div_pos (hspos k) (hRpos k)
  set a : ℕ → ℝ := fun k => aCoord H (u (z₀ k)) with ha
  set c : ℕ → ℝ := fun k => Real.exp (-2 * a k) with hc
  have hcpos : ∀ k, 0 < c k := fun k => Real.exp_pos _
  set v : ℕ → ℂ → V n := fun k w => c k • u (z₀ k + t k • w) with hv
  set ρ : ℕ → ℝ := fun k => ε k * R k with hρ
  have hD := fun k => rescale_isFiniteEnergyCurve H hH J hJ Ω hΩo u hu (z₀ k) (t k)
    (htpos k) (c k) (hcpos k)
  -- the point of the original curve hit by `v k` at `w`
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
  have hptΩ : ∀ k, ∀ w ∈ ball (0 : ℂ) (ρ k), z₀ k + t k • w ∈ Ω := by
    intro k w hw
    rw [hpt]
    exact hannΩ k _ (hsubU k _ (ball_subset_closedBall (hmem k w hw)))
  have hpre : ∀ k, ball (0 : ℂ) (ρ k) ⊆ {w : ℂ | z₀ k + t k • w ∈ Ω} := hptΩ
  have h0pre : ∀ k, z₀ k + t k • (0 : ℂ) ∈ Ω := fun k =>
    hptΩ k 0 (mem_ball_self (mul_pos (hε k) (hRpos k)))
  have hvfe : ∀ k, IsFiniteEnergyCurve H J (ball 0 (ρ k)) (v k) := by
    intro k
    obtain ⟨h0, -, -, -⟩ := hD k
    obtain ⟨h1, h2, h3, h4⟩ := h0
    refine ⟨h1.mono (hpre k), fun w hw => h2 w (hpre k hw),
      fun w hw => h3 w (hpre k hw), lt_of_le_of_lt ?_ h4⟩
    exact iSup₂_mono fun φ _ => lintegral_mono_set (hpre k)
  set C : ℝ := (energy H Ω u).toReal with hCdef
  have hvC : ∀ k, energy H (ball 0 (ρ k)) (v k) ≤ ENNReal.ofReal C := by
    intro k
    obtain ⟨-, -, -, hE⟩ := hD k
    have he := (hE Ω subset_rfl hΩo.measurableSet).1
    calc energy H (ball 0 (ρ k)) (v k) ≤ energy H {w : ℂ | z₀ k + t k • w ∈ Ω} (v k) :=
          iSup₂_mono fun φ _ => lintegral_mono_set (hpre k)
      _ = energy H Ω u := he
      _ = ENNReal.ofReal C := by rw [hCdef, ENNReal.ofReal_toReal hu.2.2.2.ne]
  have hvgrad : ∀ k, ∀ w ∈ ball (0 : ℂ) (ρ k), gradNorm H (v k) w ≤ 2 := by
    intro k w hw
    obtain ⟨-, -, hG, -⟩ := hD k
    rw [hG w (hpre k hw), hpt k w]
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
    rw [hA 0 (h0pre k)]
    simp only [smul_zero, add_zero, hc, Real.log_exp, ha]
    ring
  have hvg0 : ∀ k, gradNorm H (v k) 0 = 1 := by
    intro k
    obtain ⟨-, -, hG, -⟩ := hD k
    rw [hG 0 (h0pre k), smul_zero, add_zero]
    have e : gradNorm H u (z₀ k) = R k / s k := by
      simp only [hR, hgdef, hz₀]
      field_simp [(hspos k).ne']
    rw [e, htdef]
    show s k / R k * (R k / s k) = 1
    rw [div_mul_div_comm, mul_comm (s k), div_self (mul_pos (hRpos k) (hspos k)).ne']
  obtain ⟨φ, hφ, w, hw, hnc, -, hlim⟩ :=
    exists_plane_of_gradNorm_le H hH J hJ v ρ hεR hvfe C hvC hvgrad hva0 hvg0
  -- the bubble carries no `dλ`-energy
  have hDu : dlambdaEnergy H {x : ℂ | x ≠ 0 ∧ ‖x‖ < 1} u ≠ ⊤ := by
    have hadm : Admissible (fun _ : ℝ => (1 : ℝ)) :=
      ⟨contDiff_const, monotone_const, fun _ => ⟨zero_le_one, le_rfl⟩⟩
    have hset : {x : ℂ | x ≠ 0 ∧ ‖x‖ < 1} = Ω := by ext x; rw [hmemΩ]; rfl
    rw [hset]
    refine ne_top_of_le_ne_top hu.2.2.2.ne (le_trans (le_of_eq ?_)
      (le_iSup₂ (f := fun (φ : ℝ → ℝ) (_ : Admissible φ) =>
        ∫⁻ z in Ω, ENNReal.ofReal (energyDensity H φ u z)) _ hadm))
    simp [dlambdaEnergy, energyDensity, dlambdaDensity]
  have h3s : Tendsto (fun j => 3 * s (φ j) / 2) atTop (𝓝[>] 0) := by
    have h1 : Tendsto (fun j => s (φ j)) atTop (𝓝[>] 0) := hs0.comp hφ.tendsto_atTop
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun j => by
      have := hspos (φ j); show (0 : ℝ) < 3 * s (φ j) / 2; positivity⟩
    have h2 := (tendsto_nhdsWithin_iff.1 h1).1
    simpa using (h2.const_mul 3).div_const 2
  have htail := (tendsto_dlambdaEnergy_punctured H u hDu).comp h3s
  have hzero : ∀ R' : ℝ, dlambdaEnergy H (ball 0 R') w = 0 := by
    intro R'
    refine le_antisymm ((hlim R').trans ?_) bot_le
    have hev : ∀ᶠ j in atTop, dlambdaEnergy H (ball 0 R') (v (φ j)) ≤
        dlambdaEnergy H {x : ℂ | x ≠ 0 ∧ ‖x‖ < 3 * s (φ j) / 2} u := by
      have hρφ : Tendsto (fun j => ρ (φ j)) atTop atTop := hεR.comp hφ.tendsto_atTop
      filter_upwards [hρφ.eventually (eventually_ge_atTop R')] with j hj
      obtain ⟨-, -, -, hE⟩ := hD (φ j)
      have hAΩ : {x : ℂ | x ≠ 0 ∧ ‖x‖ < 3 * s (φ j) / 2} ⊆ Ω := fun x hx => by
        rw [hmemΩ]; exact ⟨hx.1, by linarith [hx.2, hshalf (φ j)]⟩
      have hAm : MeasurableSet {x : ℂ | x ≠ 0 ∧ ‖x‖ < 3 * s (φ j) / 2} :=
        (measurableSet_singleton (0 : ℂ)).compl.inter
          (measurableSet_lt measurable_norm measurable_const)
      have he := (hE _ hAΩ hAm).2
      rw [← he]
      refine lintegral_mono_set fun y hy => ?_
      have hy' : y ∈ ball (0 : ℂ) (ρ (φ j)) := ball_subset_ball hj hy
      have hyΩ := hptΩ (φ j) y hy'
      rw [hmemΩ] at hyΩ
      refine ⟨hyΩ.1, ?_⟩
      rw [hpt]
      exact (hann (φ j) _ (hsubU (φ j) _ (ball_subset_closedBall (hmem (φ j) y hy')))).2
    calc liminf (fun j => dlambdaEnergy H (ball 0 R') (v (φ j))) atTop
        ≤ liminf (fun j => dlambdaEnergy H {x : ℂ | x ≠ 0 ∧ ‖x‖ < 3 * s (φ j) / 2} u) atTop :=
          liminf_le_liminf hev
      _ = 0 := htail.liminf_eq
  exact (dlambdaEnergy_pos_of_plane H hH J hJ w hw hnc).ne'
    (dlambdaEnergy_univ_eq_zero' H w hzero)

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, ∀ z : ℂ, z ≠ 0 → ‖z‖ < r → ‖z‖ * gradNorm H u z ≤ C :=
  exists_norm_mul_gradNorm_le_near_puncture_aux H hH J hJ u hu
