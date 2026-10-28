-- Prove2me | solution 1 for FiniteEnergyPlane.exists_extension_of_energy_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-24T18:24:39.16843+00:00
-- url     : https://prove2.me/submissions/32128ddc-72f7-470a-a321-3d1888c436a4

import Definitions.Def_FiniteEnergyPlane_Setting
import Theorems.Thm_FiniteEnergyPlane_exists_norm_mul_fderiv_le_of_energy_lt_top
import Theorems.Thm_FiniteEnergyPlane_exists_tendsto_of_energy_lt_top
import Theorems.Thm_FiniteEnergyPlane_contDiffOn_ball_of_energy_lt_top



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Removal of singularities (Wendl, Theorem 9.2; Zinger, Proposition 5.1). -/
theorem exists_extension_of_energy_lt_top_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (J : E → E →L[ℝ] E) (O : Set E)
    (hJ : JHolomorphic.IsAlmostComplexOn J O) (K : Set E) (hK : IsCompact K) (hKO : K ⊆ O)
    (u : ℂ → E) (hu : ContDiffOn ℝ ∞ u (ball 0 1 \ {0}))
    (hhol : JHolomorphic.IsJHolomorphicOn J (ball 0 1 \ {0}) u)
    (hmaps : Set.MapsTo u (ball 0 1 \ {0}) K)
    (hE : ∫⁻ z in ball 0 1 \ {0}, ENNReal.ofReal (‖fderiv ℝ u z‖ ^ 2) < ⊤) :
    ∃ v : ℂ → E, ContDiffOn ℝ ∞ v (ball 0 1) ∧ JHolomorphic.IsJHolomorphicOn J (ball 0 1) v ∧
      Set.MapsTo v (ball 0 1) K ∧ ∀ z ∈ ball (0 : ℂ) 1, z ≠ 0 → v z = u z := by
  have hG := exists_norm_mul_fderiv_le_of_energy_lt_top J O hJ K hK hKO u hu hhol hmaps hE
  obtain ⟨x₀, hx₀⟩ := exists_tendsto_of_energy_lt_top J O hJ K hK hKO u hu hhol hmaps hE hG
  set S : Set ℂ := ball 0 1 \ {0} with hS
  have hSo : IsOpen S := isOpen_ball.sdiff isClosed_singleton
  -- the limit lies in `K`
  have hev : ∀ᶠ z in 𝓝[≠] (0 : ℂ), u z ∈ K := by
    have : ball (0 : ℂ) 1 ∈ 𝓝[≠] (0 : ℂ) :=
      mem_nhdsWithin_of_mem_nhds (ball_mem_nhds 0 one_pos)
    filter_upwards [this, self_mem_nhdsWithin] with z hz hz0
    exact hmaps ⟨hz, hz0⟩
  have hx₀K : x₀ ∈ K := hK.isClosed.mem_of_tendsto hx₀ hev
  set v : ℂ → E := Function.update u 0 x₀ with hv
  have hvS : ∀ z ∈ S, v z = u z := fun z hz => Function.update_of_ne hz.2 _ _
  have hvev : ∀ z ∈ S, v =ᶠ[𝓝 z] u := fun z hz =>
    Filter.eventually_of_mem (hSo.mem_nhds hz) hvS
  have hvsm : ContDiffOn ℝ ∞ v S := hu.congr hvS
  have hcont : ContinuousOn v (ball 0 1) := by
    intro z hz
    by_cases h0 : z = 0
    · subst h0
      exact (continuousAt_update_same.2 hx₀).continuousWithinAt
    · have hzS : z ∈ S := ⟨hz, h0⟩
      exact ((hvsm.continuousOn.continuousAt (hSo.mem_nhds hzS))).continuousWithinAt
  have hvhol : JHolomorphic.IsJHolomorphicOn J S v := by
    intro z hz
    obtain ⟨hd, hdb⟩ := hhol z hz
    refine ⟨hd.congr_of_eventuallyEq (hvev z hz), ?_⟩
    unfold JHolomorphic.dbarJ at hdb ⊢
    rw [(hvev z hz).fderiv_eq, hvS z hz]
    exact hdb
  have hvmapsK : Set.MapsTo v (ball 0 1) K := by
    intro z hz
    by_cases h0 : z = 0
    · subst h0; simpa [hv] using hx₀K
    · rw [hvS z ⟨hz, h0⟩]; exact hmaps ⟨hz, h0⟩
  have hvE : ∫⁻ z in S, ENNReal.ofReal (‖fderiv ℝ v z‖ ^ 2) < ⊤ := by
    rw [setLIntegral_congr_fun hSo.measurableSet
      (fun z hz => by rw [(hvev z hz).fderiv_eq])]
    exact hE
  obtain ⟨h1, h2⟩ := contDiffOn_ball_of_energy_lt_top J O hJ v hcont hvsm hvhol
    (hvmapsK.mono_right hKO) hvE
  exact ⟨v, h1, h2, hvmapsK, fun z hz h0 => hvS z ⟨hz, h0⟩⟩

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (J : E → E →L[ℝ] E) (O : Set E)
    (hJ : JHolomorphic.IsAlmostComplexOn J O) (K : Set E) (hK : IsCompact K) (hKO : K ⊆ O)
    (u : ℂ → E) (hu : ContDiffOn ℝ ∞ u (ball 0 1 \ {0}))
    (hhol : JHolomorphic.IsJHolomorphicOn J (ball 0 1 \ {0}) u)
    (hmaps : Set.MapsTo u (ball 0 1 \ {0}) K)
    (hE : ∫⁻ z in ball 0 1 \ {0}, ENNReal.ofReal (‖fderiv ℝ u z‖ ^ 2) < ⊤) :
    ∃ v : ℂ → E, ContDiffOn ℝ ∞ v (ball 0 1) ∧ JHolomorphic.IsJHolomorphicOn J (ball 0 1) v ∧
      Set.MapsTo v (ball 0 1) K ∧ ∀ z ∈ ball (0 : ℂ) 1, z ≠ 0 → v z = u z :=
  exists_extension_of_energy_lt_top_aux J O hJ K hK hKO u hu hhol hmaps hE
