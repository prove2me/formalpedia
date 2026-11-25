-- Prove2me | solution 1 for FiniteEnergyPlane.exists_mem_embeddedFastPlaneSet_of_isEmbeddedPlane
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-25T10:20:16.419804+00:00
-- url     : https://prove2.me/submissions/67dd59e7-3ace-4cd3-b63e-886c511a4053

import Definitions.Def_FiniteEnergyPlane_OpenBook
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_contDiffOn_dlambdaEnergy_ball_family
import Theorems.Thm_FiniteEnergyPlane_isFastPlane_comp_add_smul
import Theorems.Thm_FiniteEnergyPlane_isFastPlane_shiftA
import Theorems.Thm_FiniteEnergyPlane_isNondegenerateEnd_shiftA
import Theorems.Thm_FiniteEnergyPlane_rescale_isFiniteEnergyCurve
import Theorems.Thm_FiniteEnergyPlane_proj_aCoord_exp_smul
import Theorems.Thm_FiniteEnergyPlane_dlambdaEnergy_univ_eq_of_isNondegenerateEnd
import Theorems.Thm_FiniteEnergyPlane_dlambdaEnergy_ne_top_of_univ_eq_ofReal
import Theorems.Thm_FiniteEnergyPlane_dlambdaEnergy_norm_sub_gt_eq_sub
import Theorems.Thm_FiniteEnergyPlane_exists_radius_lt_dlambdaEnergy_ball



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem exists_mem_embeddedFastPlaneSet_of_isEmbeddedPlane_aux (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (γ : ℝ) (hγ : 0 < γ) (hγT : γ < P.T) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1) (hue : IsEmbeddedPlane u)
    (ζ : ℂ) :
    ∃ v ∈ embeddedFastPlaneSet H J P {proj H (u ζ)} γ,
      Set.range (fun z => proj H (v z)) = Set.range (fun z => proj H (u z)) := by
  have hu0 : ∀ z, u z ≠ 0 := fun z => hu.1.2.1 z trivial
  have htot := dlambdaEnergy_univ_eq_of_isNondegenerateEnd H hH J hJ u hu.1 P huP
  have hfin := dlambdaEnergy_ne_top_of_univ_eq_ofReal H u P.T htot
  let Φ : ℝ → ℝ := fun ρ => (dlambdaEnergy H (ball ζ ρ) u).toReal
  have hcont : ContinuousOn Φ (Set.Ioi 0) := by
    have h := (contDiffOn_dlambdaEnergy_ball_family H hH J hJ 0 Set.univ isOpen_univ
      (fun p => u p.1) (((hu.1.1.of_le (by exact_mod_cast le_top)).comp contDiffOn_fst
        fun _ _ => trivial)) (fun _ _ => hu.1)).continuousOn
    exact h.comp (f := fun ρ : ℝ => (ζ, (0 : ℂ), ρ)) (by fun_prop) fun ρ hρ => ⟨trivial, trivial, hρ⟩
  -- small discs
  have hsmall : ∃ a > 0, Φ a < P.T - γ := by
    have hvol : Tendsto (fun r : ℝ => volume (ball ζ r)) (𝓝[>] 0) (𝓝 0) := by
      have h : Tendsto (fun r : ℝ => ENNReal.ofReal r ^ 2 * (NNReal.pi : ℝ≥0∞)) (𝓝[>] 0) (𝓝 0) := by
        have h1 : Tendsto (fun r : ℝ => ENNReal.ofReal (r ^ 2 * π)) (𝓝[>] 0) (𝓝 0) := by
          have : Continuous fun r : ℝ => ENNReal.ofReal (r ^ 2 * π) :=
            ENNReal.continuous_ofReal.comp (by fun_prop)
          have h2 := this.tendsto 0
          simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
            ENNReal.ofReal_zero] at h2
          exact h2.mono_left nhdsWithin_le_nhds
        refine h1.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with r hr
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (le_of_lt hr)]
        congr 1
        rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
      simpa only [Complex.volume_ball] using h
    have h := tendsto_setLIntegral_zero (f := fun z => ENNReal.ofReal (dlambdaDensity H u z))
      (μ := volume) (by simpa [dlambdaEnergy] using hfin Set.univ) hvol
    have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (P.T - γ) := ENNReal.ofReal_pos.2 (by linarith)
    obtain ⟨a, ha1, ha⟩ := ((h.eventually (gt_mem_nhds hpos)).and self_mem_nhdsWithin).exists
    refine ⟨a, ha, ?_⟩
    have := (ENNReal.toReal_lt_toReal (hfin _) ENNReal.ofReal_ne_top).2 ha1
    rwa [ENNReal.toReal_ofReal (by linarith)] at this
  -- large discs
  have hlarge : ∃ b, ∀ r ≥ b, P.T - γ < Φ r := by
    obtain ⟨b, -, hb⟩ := exists_radius_lt_dlambdaEnergy_ball H u (ENNReal.ofReal (P.T - γ))
      (by rw [htot]; exact (ENNReal.ofReal_lt_ofReal_iff P.T_pos).2 (by linarith))
    refine ⟨b + ‖ζ‖, fun r hr => ?_⟩
    have hsub : ball (0 : ℂ) b ⊆ ball ζ r := fun z hz => by
      rw [mem_ball_zero_iff] at hz
      rw [mem_ball, dist_eq_norm]
      linarith [norm_sub_le z ζ]
    have h2 : ENNReal.ofReal (P.T - γ) < dlambdaEnergy H (ball ζ r) u :=
      hb.trans_le (lintegral_mono_set hsub)
    have := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top (hfin _)).2 h2
    rwa [ENNReal.toReal_ofReal (by linarith)] at this
  obtain ⟨a, ha, hΦa⟩ := hsmall
  obtain ⟨b, hb⟩ := hlarge
  obtain ⟨ρ, hρ, hΦρ⟩ : ∃ ρ > 0, Φ ρ = P.T - γ := by
    obtain ⟨ρ, hρ, h⟩ := intermediate_value_Icc (le_max_left a b)
      (hcont.mono fun x hx => ha.trans_le hx.1) ⟨hΦa.le, (hb _ (le_max_right a b)).le⟩
    exact ⟨ρ, ha.trans_le hρ.1, h⟩
  obtain ⟨hw, hwP, hwe⟩ := isFastPlane_comp_add_smul H hH J hJ P u hu huP hue ζ ρ hρ
  set c : ℝ := -aCoord H (u ζ) with hc
  have hexp : ∀ z, proj H (Real.exp (2 * c) • u z) = proj H (u z) := fun z =>
    (proj_aCoord_exp_smul H hH c _ (hu0 z)).1
  refine ⟨shiftA c fun z => u (ζ + ρ • z), ⟨⟨isFastPlane_shiftA H hH J hJ _ hw c,
    isNondegenerateEnd_shiftA H hH _ (fun z => hu0 _) _ P 1 hwP c, ?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · have hsc : 0 < scaleToS H (u ζ) := by
      unfold scaleToS
      rw [dif_pos (hH.2.1 _ (hu0 ζ)).exists]
      exact (Classical.choose_spec (hH.2.1 _ (hu0 ζ)).exists).1
    have : Real.exp (2 * c) = scaleToS H (u ζ) := by
      rw [hc]; unfold aCoord
      rw [show 2 * -(-Real.log (scaleToS H (u ζ)) / 2) = Real.log (scaleToS H (u ζ)) by ring,
        Real.exp_log hsc]
    simp only [shiftA, smul_zero, add_zero, Set.mem_singleton_iff, this, proj]
  · have hmeas : MeasurableSet {x : ℂ | ρ < ‖x - ζ‖} :=
      (isOpen_lt continuous_const (by fun_prop)).measurableSet
    have h := ((rescale_isFiniteEnergyCurve H hH J hJ Set.univ isOpen_univ u hu.1 ζ ρ hρ
      (Real.exp (2 * c)) (Real.exp_pos _)).2.2.2 _ (Set.subset_univ _) hmeas).2
    have hset : {w : ℂ | ζ + ρ • w ∈ {x : ℂ | ρ < ‖x - ζ‖}} = {z | 1 < ‖z‖} := by
      ext w
      simp only [Set.mem_setOf_eq, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
      exact lt_mul_iff_one_lt_right hρ
    rw [hset] at h
    unfold shiftA
    rw [h, dlambdaEnergy_norm_sub_gt_eq_sub H u P.T htot ζ ρ,
      ← ENNReal.ofReal_toReal (hfin (ball ζ ρ)),
      show (dlambdaEnergy H (ball ζ ρ) u).toReal = P.T - γ from hΦρ,
      ← ENNReal.ofReal_sub _ (by linarith), sub_sub_cancel]
  · exact fun x y h => hwe.1 (smul_right_injective _ (Real.exp_pos _).ne' h)
  · intro z
    have hd : DifferentiableAt ℝ (fun z => u (ζ + ρ • z)) z :=
      ((hw.1.1.contDiffAt univ_mem).differentiableAt (by simp))
    have : fderiv ℝ (shiftA c fun z => u (ζ + ρ • z)) z =
        Real.exp (2 * c) • fderiv ℝ (fun z => u (ζ + ρ • z)) z :=
      (hd.hasFDerivAt.const_smul (Real.exp (2 * c))).fderiv
    rw [this]
    exact fun x y h => hwe.2 z (smul_right_injective _ (Real.exp_pos _).ne' h)
  · ext q
    simp only [shiftA, hexp, Set.mem_range]
    constructor
    · rintro ⟨z, rfl⟩; exact ⟨_, rfl⟩
    · rintro ⟨z, rfl⟩
      refine ⟨ρ⁻¹ • (z - ζ), ?_⟩
      rw [smul_inv_smul₀ hρ.ne', add_sub_cancel]

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (γ : ℝ) (hγ : 0 < γ) (hγT : γ < P.T) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1) (hue : IsEmbeddedPlane u)
    (ζ : ℂ) :
    ∃ v ∈ embeddedFastPlaneSet H J P {proj H (u ζ)} γ,
      Set.range (fun z => proj H (v z)) = Set.range (fun z => proj H (u z)) :=
  exists_mem_embeddedFastPlaneSet_of_isEmbeddedPlane_aux H hH J hJ P γ hγ hγT u hu huP hue ζ
