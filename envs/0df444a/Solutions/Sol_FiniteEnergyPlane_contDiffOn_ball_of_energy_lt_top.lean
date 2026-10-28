-- Prove2me | solution 1 for FiniteEnergyPlane.contDiffOn_ball_of_energy_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-24T21:17:16.709036+00:00
-- url     : https://prove2.me/submissions/a52a1f70-1727-43c1-ba85-4ab8a3d9b596

import Definitions.Def_FiniteEnergyPlane_Setting
import Theorems.Thm_FiniteEnergyPlane_contDiffOn_isJHolomorphicOn_comp_mul
import Theorems.Thm_FiniteEnergyPlane_exists_lintegral_le_rpow_of_energy_lt_top
import Theorems.Thm_FiniteEnergyPlane_lintegral_rpow_lt_top_of_norm_mul_le
import Theorems.Thm_JHolomorphic_HasWeakPartialsOn_of_contDiffOn_diff_singleton
import Theorems.Thm_FiniteEnergyPlane_exists_norm_mul_fderiv_le_of_energy_lt_top
import Theorems.Thm_JHolomorphic_contDiffOn_of_isWeakJHolomorphicOn
import Theorems.Thm_JHolomorphic_memLp_of_continuousOn_compact
import Mathlib.Analysis.Calculus.FDeriv.Measurable



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Regularity at a puncture (Zinger, Proposition 4.8). -/
theorem contDiffOn_ball_of_energy_lt_top_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (J : E → E →L[ℝ] E) (O : Set E)
    (hJ : JHolomorphic.IsAlmostComplexOn J O) (v : ℂ → E) (hc : ContinuousOn v (ball 0 1))
    (hv : ContDiffOn ℝ ∞ v (ball 0 1 \ {0}))
    (hhol : JHolomorphic.IsJHolomorphicOn J (ball 0 1 \ {0}) v)
    (hmaps : Set.MapsTo v (ball 0 1) O)
    (hE : ∫⁻ z in ball 0 1 \ {0}, ENNReal.ofReal (‖fderiv ℝ v z‖ ^ 2) < ⊤) :
    ContDiffOn ℝ ∞ v (ball 0 1) ∧ JHolomorphic.IsJHolomorphicOn J (ball 0 1) v := by
  have hSo : IsOpen (ball (0 : ℂ) 1 \ {0}) := isOpen_ball.sdiff isClosed_singleton
  have h1 : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  -- gradient bound: the sibling lemma applied to `w z = v (z / 2)`
  have hGv : ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, ∀ z : ℂ, z ≠ 0 → ‖z‖ < r →
      ‖z‖ * ‖fderiv ℝ v z‖ ≤ C := by
    set ρ : ℝ := 1 / 2 with hρdef
    have hρ : (0 : ℝ) < ρ := by norm_num [hρdef]
    have hρ1 : ρ < 1 := by norm_num [hρdef]
    have hsub : ball (0 : ℂ) ρ \ {0} ⊆ ball 0 1 \ {0} :=
      Set.diff_subset_diff_left (ball_subset_ball hρ1.le)
    obtain ⟨hw, hwhol, hwD, hwE⟩ := contDiffOn_isJHolomorphicOn_comp_mul J ρ hρ v
      (hv.mono hsub) (fun z hz => hhol z (hsub hz))
    have hcb : closedBall (0 : ℂ) ρ ⊆ ball 0 1 := closedBall_subset_ball hρ1
    have hK : IsCompact (v '' closedBall 0 ρ) :=
      (isCompact_closedBall 0 ρ).image_of_continuousOn (hc.mono hcb)
    have hKO : v '' closedBall 0 ρ ⊆ O := by
      rintro _ ⟨z, hz, rfl⟩; exact hmaps (hcb hz)
    have hwmaps : Set.MapsTo (fun z => v ((ρ : ℂ) * z)) (ball 0 1 \ {0})
        (v '' closedBall 0 ρ) := by
      intro z hz
      refine ⟨(ρ : ℂ) * z, ?_, rfl⟩
      have hz1 : ‖z‖ < 1 := by simpa using hz.1
      rw [mem_closedBall, dist_zero_right, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg hρ.le]
      nlinarith [norm_nonneg z]
    have hwE' : ∫⁻ z in ball 0 1 \ {0},
        ENNReal.ofReal (‖fderiv ℝ (fun z => v ((ρ : ℂ) * z)) z‖ ^ 2) < ⊤ := by
      rw [hwE]; exact lt_of_le_of_lt (lintegral_mono_set hsub) hE
    obtain ⟨r, hr, C, hC⟩ := exists_norm_mul_fderiv_le_of_energy_lt_top J O hJ _ hK hKO _ hw
      hwhol hwmaps hwE'
    refine ⟨ρ * r, mul_pos hρ hr, C, fun y hy hyr => ?_⟩
    have hρc : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
    set z : ℂ := (ρ : ℂ)⁻¹ * y with hzdef
    have hyz : (ρ : ℂ) * z = y := by rw [hzdef, ← mul_assoc, mul_inv_cancel₀ hρc, one_mul]
    have hnz : ‖z‖ = ρ⁻¹ * ‖y‖ := by
      rw [hzdef, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hρ.le]
    have hz0 : z ≠ 0 := mul_ne_zero (inv_ne_zero hρc) hy
    have hzr : ‖z‖ < r := by rw [hnz, inv_mul_lt_iff₀ hρ]; exact hyr
    have := hC z hz0 hzr
    rw [hwD z, hyz, norm_smul, Real.norm_of_nonneg hρ.le, hnz] at this
    calc ‖y‖ * ‖fderiv ℝ v y‖ = ρ⁻¹ * ‖y‖ * (ρ * ‖fderiv ℝ v y‖) := by
          rw [mul_mul_mul_comm, inv_mul_cancel₀ hρ.ne', one_mul]
      _ ≤ C := this
  -- energy decay
  obtain ⟨μ, hμ, r1, hr1, K1, hdec⟩ :=
    exists_lintegral_le_rpow_of_energy_lt_top J O hJ v hc hv hhol hmaps hE hGv
  obtain ⟨r2, hr2, C2, hC2⟩ := hGv
  set r0 : ℝ := min r1 (min r2 1) with hr0def
  have hr0 : 0 < r0 := lt_min hr1 (lt_min hr2 one_pos)
  have hr01 : r0 ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  have hr02 : r0 ≤ r2 := (min_le_right _ _).trans (min_le_left _ _)
  have hr0r1 : r0 ≤ r1 := min_le_left _ _
  have hU1 : ball (0 : ℂ) r0 ⊆ ball 0 1 := ball_subset_ball hr01
  -- higher integrability of the derivative near the puncture
  set p : ℝ := 2 + μ with hpdef
  have hp2 : 2 < p := by rw [hpdef]; linarith
  have hint : ∫⁻ z in ball 0 r0, ENNReal.ofReal (‖fderiv ℝ v z‖ ^ p) < ⊤ :=
    lintegral_rpow_lt_top_of_norm_mul_le (fun z => ‖fderiv ℝ v z‖) hr0 hμ
      (fun z => norm_nonneg _) (measurable_fderiv ℝ v).norm.aemeasurable
      (fun z hz hzr => hC2 z hz (lt_of_lt_of_le hzr hr02))
      (fun s hs hsr => hdec s hs (hsr.trans hr0r1)) p hp2.le (by rw [hpdef]; linarith)
  -- weak partials across the puncture
  obtain ⟨hW, hWs, hWt⟩ := JHolomorphic.HasWeakPartialsOn.of_contDiffOn_diff_singleton
    isOpen_ball (mem_ball_self hr0) (hc.mono hU1)
    ((hv.mono (Set.diff_subset_diff_left hU1)).of_le h1) (by linarith) hint
  have hne : ∀ᵐ z ∂(volume : Measure ℂ), z ∈ ({0}ᶜ : Set ℂ) :=
    compl_mem_ae_iff.2 (measure_singleton 0)
  have hweak : JHolomorphic.IsWeakJHolomorphicOn p J O (ball 0 r0) v := by
    refine ⟨hc.mono hU1, fun z hz => hmaps (hU1 hz), _, _, hW, fun K hKU hK => ⟨?_, ?_, ?_⟩, ?_⟩
    · exact JHolomorphic.memLp_of_continuousOn_compact hK (hc.mono (hKU.trans hU1))
    · exact hWs.mono_measure (Measure.restrict_mono hKU le_rfl)
    · exact hWt.mono_measure (Measure.restrict_mono hKU le_rfl)
    · filter_upwards [ae_restrict_mem measurableSet_ball, ae_restrict_of_ae hne] with z hz hz0
      exact (hhol z ⟨hU1 hz, hz0⟩).2
  have hsm0 : ContDiffOn ℝ ∞ v (ball 0 r0) :=
    JHolomorphic.contDiffOn_of_isWeakJHolomorphicOn p hp2 J O hJ _ isOpen_ball v hweak
  -- smoothness on the whole disc
  have hsm : ContDiffOn ℝ ∞ v (ball 0 1) := by
    intro z hz
    by_cases h0 : z = 0
    · subst h0
      exact ((hsm0 0 (mem_ball_self hr0)).contDiffAt
        (isOpen_ball.mem_nhds (mem_ball_self hr0))).contDiffWithinAt
    · exact ((hv z ⟨hz, h0⟩).contDiffAt (hSo.mem_nhds ⟨hz, h0⟩)).contDiffWithinAt
  refine ⟨hsm, fun z hz => ?_⟩
  by_cases h0 : z = 0
  swap
  · exact hhol z ⟨hz, h0⟩
  subst h0
  have hB : ball (0 : ℂ) 1 ∈ 𝓝 (0 : ℂ) := ball_mem_nhds 0 one_pos
  refine ⟨((hsm 0 hz).contDiffAt hB).differentiableAt (by simp), ?_⟩
  have hfd : ContinuousAt (fderiv ℝ v) 0 :=
    (hsm.continuousOn_fderiv_of_isOpen isOpen_ball h1).continuousAt hB
  have hJv : ContinuousAt (fun z => J (v z)) 0 :=
    ContinuousAt.comp (g := J) (hJ.2.1.continuousOn.continuousAt (hJ.1.mem_nhds (hmaps hz)))
      (hc.continuousAt hB)
  have hcont : ContinuousAt (fun z => JHolomorphic.dbarJ J v z) 0 :=
    (hfd.clm_apply continuousAt_const).add (hJv.clm_apply (hfd.clm_apply continuousAt_const))
  have hev : ∀ᶠ z in 𝓝[≠] (0 : ℂ), JHolomorphic.dbarJ J v z = 0 := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds hB, self_mem_nhdsWithin] with z hz1 hz0
    exact (hhol z ⟨hz1, hz0⟩).2
  exact tendsto_nhds_unique (hcont.tendsto.mono_left nhdsWithin_le_nhds)
    ((tendsto_const_nhds (x := (0 : E))).congr' (hev.mono fun z hz => hz.symm))

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (J : E → E →L[ℝ] E) (O : Set E)
    (hJ : JHolomorphic.IsAlmostComplexOn J O) (v : ℂ → E) (hc : ContinuousOn v (ball 0 1))
    (hv : ContDiffOn ℝ ∞ v (ball 0 1 \ {0}))
    (hhol : JHolomorphic.IsJHolomorphicOn J (ball 0 1 \ {0}) v)
    (hmaps : Set.MapsTo v (ball 0 1) O)
    (hE : ∫⁻ z in ball 0 1 \ {0}, ENNReal.ofReal (‖fderiv ℝ v z‖ ^ 2) < ⊤) :
    ContDiffOn ℝ ∞ v (ball 0 1) ∧ JHolomorphic.IsJHolomorphicOn J (ball 0 1) v :=
  contDiffOn_ball_of_energy_lt_top_aux J O hJ v hc hv hhol hmaps hE
