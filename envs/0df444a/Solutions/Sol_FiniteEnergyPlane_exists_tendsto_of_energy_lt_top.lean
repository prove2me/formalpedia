-- Prove2me | solution 1 for FiniteEnergyPlane.exists_tendsto_of_energy_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-24T21:17:07.934979+00:00
-- url     : https://prove2.me/submissions/af9c2866-99a5-4e31-9666-52838e61aa2d

import Definitions.Def_FiniteEnergyPlane_Setting
import Theorems.Thm_FiniteEnergyPlane_tendsto_norm_mul_fderiv_of_energy_lt_top
import Theorems.Thm_FiniteEnergyPlane_norm_sub_le_of_norm_mul_fderiv_le
import Theorems.Thm_FiniteEnergyPlane_energy_ge_of_mapsTo_ball
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Limit at a puncture (Wendl, Theorem 9.2, continuity part, (9.1)). -/
theorem exists_tendsto_of_energy_lt_top_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (J : E → E →L[ℝ] E) (O : Set E)
    (hJ : JHolomorphic.IsAlmostComplexOn J O) (K : Set E) (hK : IsCompact K) (hKO : K ⊆ O)
    (u : ℂ → E) (hu : ContDiffOn ℝ ∞ u (ball 0 1 \ {0}))
    (hhol : JHolomorphic.IsJHolomorphicOn J (ball 0 1 \ {0}) u)
    (hmaps : Set.MapsTo u (ball 0 1 \ {0}) K)
    (hE : ∫⁻ z in ball 0 1 \ {0}, ENNReal.ofReal (‖fderiv ℝ u z‖ ^ 2) < ⊤)
    (hG : ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, ∀ z : ℂ, z ≠ 0 → ‖z‖ < r → ‖z‖ * ‖fderiv ℝ u z‖ ≤ C) :
    ∃ x₀ : E, Tendsto u (𝓝[≠] 0) (𝓝 x₀) := by
  set S : Set ℂ := ball 0 1 \ {0} with hS
  set g : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (‖fderiv ℝ u z‖ ^ 2) with hg
  have hcont : ContinuousOn u S := hu.continuousOn
  have hev : ∀ᶠ z in 𝓝[≠] (0 : ℂ), u z ∈ K := by
    have : ball (0 : ℂ) 1 ∈ 𝓝[≠] (0 : ℂ) :=
      mem_nhdsWithin_of_mem_nhds (ball_mem_nhds 0 one_pos)
    filter_upwards [this, self_mem_nhdsWithin] with z hz hz0
    exact hmaps ⟨hz, hz0⟩
  have hdec := tendsto_norm_mul_fderiv_of_energy_lt_top J O hJ K hK hKO u hu hhol hmaps hE hG
  obtain ⟨r₀, hr₀, c, hc, hmono⟩ := energy_ge_of_mapsTo_ball J O hJ K hK hKO
  obtain ⟨x₀, -, hx₀⟩ := hK.exists_mapClusterPt (f := 𝓝[≠] (0 : ℂ)) (u := u)
    (Filter.le_principal_iff.mpr hev)
  refine ⟨x₀, hK.tendsto_nhds_of_unique_mapClusterPt hev ?_⟩
  intro p _ hp
  by_contra hne
  set q := x₀
  set d := ‖p - q‖ with hd
  have hd0 : 0 < d := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  set r := min r₀ (d / 8) with hr
  have hr0 : 0 < r := lt_min hr₀ (by positivity)
  have hrr₀ : r ≤ r₀ := min_le_left _ _
  have hrd : 8 * r ≤ d := by have := min_le_right r₀ (d / 8); linarith
  -- small energy near the puncture
  have hsmall : ∃ s₁ : ℝ, 0 < s₁ ∧
      ∫⁻ z in ball 0 s₁ ∩ S, g z < ENNReal.ofReal (c * r ^ 2) := by
    have hfin : ∫⁻ z, g z ∂(volume.restrict S) ≠ ⊤ := hE.ne
    have hvol : Tendsto ((volume.restrict S) ∘ fun s : ℝ => ball (0 : ℂ) s) (𝓝[>] 0) (𝓝 0) := by
      have hup : Tendsto (fun s : ℝ => ENNReal.ofReal s ^ 2 * (NNReal.pi : ℝ≥0∞)) (𝓝[>] 0)
          (𝓝 0) := by
        have h1 : Tendsto (fun s : ℝ => ENNReal.ofReal s) (𝓝[>] 0) (𝓝 0) := by
          have := (ENNReal.continuous_ofReal.tendsto 0).mono_left
            (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
          simpa using this
        have h2 : Tendsto (fun s : ℝ => ENNReal.ofReal s ^ 2) (𝓝[>] 0) (𝓝 0) := by
          have := ((ENNReal.continuous_pow 2).tendsto 0).comp h1
          simpa [Function.comp_def] using this
        have h3 := ENNReal.Tendsto.mul_const h2 (Or.inr ENNReal.coe_ne_top)
          (b := (NNReal.pi : ℝ≥0∞))
        simpa using h3
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
        (fun _ => bot_le) (fun s => ?_)
      simp only [Function.comp_apply]
      rw [← Complex.volume_ball]
      exact Measure.restrict_apply_le _ _
    have h := tendsto_setLIntegral_zero hfin hvol
    have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (c * r ^ 2) := by
      rw [ENNReal.ofReal_pos]; positivity
    obtain ⟨s₁, hs₁, hs₁'⟩ := ((h.eventually (gt_mem_nhds hpos)).and
      self_mem_nhdsWithin).exists
    refine ⟨s₁, hs₁', ?_⟩
    rw [Measure.restrict_restrict measurableSet_ball] at hs₁
    exact hs₁
  obtain ⟨s₁, hs₁, hs₁E⟩ := hsmall
  -- small weighted gradient near the puncture
  obtain ⟨s₂, hs₂, hs₂d⟩ : ∃ s₂ : ℝ, 0 < s₂ ∧
      ∀ z : ℂ, z ≠ 0 → ‖z‖ < s₂ → ‖z‖ * ‖fderiv ℝ u z‖ ≤ r / 8 := by
    have h := hdec.eventually (ge_mem_nhds (show (0 : ℝ) < r / 8 by positivity))
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h
    obtain ⟨ε, hε, hε'⟩ := h
    exact ⟨ε, hε, fun z hz hzε => hε' (by simpa using hzε) hz⟩
  set ρ₁ := min s₁ (min s₂ 1) with hρ₁
  have hρ₁0 : 0 < ρ₁ := lt_min hs₁ (lt_min hs₂ one_pos)
  have hρs₁ : ρ₁ ≤ s₁ := min_le_left _ _
  have hρs₂ : ρ₁ ≤ s₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hρ1 : ρ₁ ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  have hmemS : ∀ z : ℂ, z ≠ 0 → ‖z‖ < ρ₁ → z ∈ S := fun z hz hzρ =>
    ⟨by rw [mem_ball_zero_iff]; linarith, hz⟩
  -- oscillation on circles
  have hosc : ∀ z w : ℂ, z ≠ 0 → ‖z‖ < ρ₁ → ‖w‖ = ‖z‖ → ‖u z - u w‖ ≤ r / 2 := by
    intro z w hz hzρ hw
    have h := norm_sub_le_of_norm_mul_fderiv_le u ρ₁ (r / 8)
      (fun y hy hyρ => ⟨(hhol y (hmemS y hy hyρ)).1, hs₂d y hy (lt_of_lt_of_le hyρ hρs₂)⟩)
      z w hz hzρ hw
    have : π * (r / 8) ≤ r / 2 := by nlinarith [Real.pi_le_four]
    linarith
  -- points near a cluster point
  have hnear : ∀ y : E, MapClusterPt y (𝓝[≠] (0 : ℂ)) u → ∀ ρ : ℝ, 0 < ρ →
      ∃ z : ℂ, z ≠ 0 ∧ ‖z‖ < ρ ∧ ‖u z - y‖ < r := by
    intro y hy ρ hρ
    have hf := (mapClusterPt_iff_frequently.mp hy) (ball y r) (ball_mem_nhds y hr0)
    have he : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ≠ 0 ∧ ‖z‖ < ρ := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (0 : ℂ) hρ)] with z hz hzρ
      exact ⟨hz, by simpa using hzρ⟩
    obtain ⟨z, hz, hz'⟩ := (hf.and_eventually he).exists
    exact ⟨z, hz'.1, hz'.2, by simpa [dist_eq_norm] using hz⟩
  obtain ⟨z₀, hz₀, hz₀ρ, hz₀q⟩ := hnear q hx₀ ρ₁ hρ₁0
  obtain ⟨z₁, hz₁, hz₁ρ, hz₁p⟩ := hnear p hp ‖z₀‖ (norm_pos_iff.mpr hz₀)
  obtain ⟨z₂, hz₂, hz₂ρ, hz₂q⟩ := hnear q hx₀ ‖z₁‖ (norm_pos_iff.mpr hz₁)
  set a := ‖z₂‖
  set b := ‖z₀‖
  have ha0 : 0 < a := norm_pos_iff.mpr hz₂
  have hz₁ρ₁ : ‖z₁‖ < ρ₁ := hz₁ρ.trans hz₀ρ
  set x := u z₁ with hx
  have hxK : x ∈ K := hmaps (hmemS z₁ hz₁ hz₁ρ₁)
  -- the boundary circles stay away from `x`
  have hfar : ∀ z : ℂ, (‖z‖ = a ∨ ‖z‖ = b) → r ≤ ‖u z - x‖ := by
    intro z hz
    have hzq : ‖u z - q‖ < 2 * r := by
      rcases hz with hz | hz
      · have h1 := hosc z₂ z hz₂ (hz₂ρ.trans hz₁ρ₁) hz
        calc ‖u z - q‖ ≤ ‖u z₂ - u z‖ + ‖u z₂ - q‖ := by
              rw [norm_sub_rev (u z₂) (u z)]
              exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans_eq (by rw [norm_sub_rev])
          _ < 2 * r := by linarith
      · have h1 := hosc z₀ z hz₀ hz₀ρ hz
        calc ‖u z - q‖ ≤ ‖u z₀ - u z‖ + ‖u z₀ - q‖ := by
              rw [norm_sub_rev (u z₀) (u z)]
              exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans_eq (by rw [norm_sub_rev])
          _ < 2 * r := by linarith
    have htri : d ≤ ‖u z - x‖ + ‖u z - q‖ + ‖x - p‖ := by
      have : p - q = (u z - q) - (u z - x) - (x - p) := by abel
      rw [hd, this]
      calc ‖(u z - q) - (u z - x) - (x - p)‖ ≤ ‖(u z - q) - (u z - x)‖ + ‖x - p‖ :=
            norm_sub_le _ _
        _ ≤ ‖u z - q‖ + ‖u z - x‖ + ‖x - p‖ := by gcongr; exact norm_sub_le _ _
        _ = _ := by ring
    linarith
  -- the domain
  set A : Set ℂ := {z | a < ‖z‖ ∧ ‖z‖ < b} with hA
  have hAo : IsOpen A :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hAS : A ⊆ S := fun z hz =>
    hmemS z (norm_pos_iff.mp (ha0.trans hz.1)) (hz.2.trans hz₀ρ)
  set U : Set ℂ := A ∩ u ⁻¹' ball x r with hU
  have hUo : IsOpen U := (hcont.mono hAS).isOpen_inter_preimage hAo isOpen_ball
  have hUS : U ⊆ S := fun z hz => hAS hz.1
  set Cl : Set ℂ := {z | a ≤ ‖z‖ ∧ ‖z‖ ≤ b} with hCl
  have hClS : Cl ⊆ S := fun z hz =>
    hmemS z (norm_pos_iff.mp (ha0.trans_le hz.1)) (hz.2.trans_lt hz₀ρ)
  have hClc : IsCompact Cl := by
    refine (isCompact_closedBall (0 : ℂ) b).of_isClosed_subset ?_ ?_
    · exact (isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const)
    · intro z hz; simpa using hz.2
  have hproper : ∀ L : Set E, IsCompact L → L ⊆ ball x r → IsCompact (U ∩ u ⁻¹' L) := by
    intro L hL hLb
    have heq : U ∩ u ⁻¹' L = Cl ∩ u ⁻¹' L := by
      ext z
      constructor
      · rintro ⟨⟨hzA, -⟩, hzL⟩
        exact ⟨⟨hzA.1.le, hzA.2.le⟩, hzL⟩
      · rintro ⟨hzC, hzL⟩
        have hb := hLb hzL
        rw [mem_ball, dist_eq_norm] at hb
        have h1 : a < ‖z‖ := lt_of_le_of_ne hzC.1 (fun h => by
          have := hfar z (Or.inl h.symm); linarith)
        have h2 : ‖z‖ < b := lt_of_le_of_ne hzC.2 (fun h => by
          have := hfar z (Or.inr h); linarith)
        exact ⟨⟨⟨h1, h2⟩, hLb hzL⟩, hzL⟩
    rw [heq]
    exact hClc.of_isClosed_subset
      ((hcont.mono hClS).preimage_isClosed_of_isClosed hClc.isClosed hL.isClosed)
      Set.inter_subset_left
  have hz₁U : z₁ ∈ U := ⟨⟨hz₂ρ, hz₁ρ⟩, mem_ball_self hr0⟩
  have hlow := hmono x hxK r hr0 hrr₀ U hUo u (hu.mono hUS)
    (fun z hz => hhol z (hUS hz)) (fun z hz => hz.2) hproper ⟨z₁, hz₁U, rfl⟩
  have hUsub : U ⊆ ball 0 s₁ ∩ S := fun z hz =>
    ⟨by rw [mem_ball_zero_iff]; exact hz.1.2.trans (hz₀ρ.trans_le hρs₁), hUS hz⟩
  have hup : ∫⁻ z in U, g z ≤ ∫⁻ z in ball 0 s₁ ∩ S, g z := lintegral_mono_set hUsub
  exact absurd (hlow.trans hup) (not_le.mpr hs₁E)

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (J : E → E →L[ℝ] E) (O : Set E)
    (hJ : JHolomorphic.IsAlmostComplexOn J O) (K : Set E) (hK : IsCompact K) (hKO : K ⊆ O)
    (u : ℂ → E) (hu : ContDiffOn ℝ ∞ u (ball 0 1 \ {0}))
    (hhol : JHolomorphic.IsJHolomorphicOn J (ball 0 1 \ {0}) u)
    (hmaps : Set.MapsTo u (ball 0 1 \ {0}) K)
    (hE : ∫⁻ z in ball 0 1 \ {0}, ENNReal.ofReal (‖fderiv ℝ u z‖ ^ 2) < ⊤)
    (hG : ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, ∀ z : ℂ, z ≠ 0 → ‖z‖ < r → ‖z‖ * ‖fderiv ℝ u z‖ ≤ C) :
    ∃ x₀ : E, Tendsto u (𝓝[≠] 0) (𝓝 x₀) :=
  FiniteEnergyPlane.exists_tendsto_of_energy_lt_top_aux J O hJ K hK hKO u hu hhol hmaps hE hG
