-- Prove2me | solution 1 for FiniteEnergyPlane.isFastPlane_iff_hasWindInfAt_one
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-03T12:08:27.465203+00:00
-- url     : https://prove2.me/submissions/da852361-d272-4b12-bcf2-69e134900618

import Definitions.Def_FiniteEnergyPlane_Winding
import Theorems.Thm_FiniteEnergyPlane_windPi_eq_windInf_sub_card
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_unique
import Theorems.Thm_FiniteEnergyPlane_hasZeroIndex_unique
import Theorems.Thm_FiniteEnergyPlane_exists_ne_of_isNondegenerateEnd
import Theorems.Thm_FiniteEnergyPlane_dlambdaEnergy_pos_of_plane
import Theorems.Thm_FiniteEnergyPlane_piDs_ne_zero_iff_dlambdaDensity_pos

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

namespace FiniteEnergyPlane

/-- `wind_π` is unique when it exists. -/
lemma fp_hasWindPi_unique {H : V 1 → ℝ} {u : ℂ → V 1} {Γ : Finset ℂ} {k m : ℤ}
    (hk : HasWindPi H u Γ k) (hm : HasWindPi H u Γ m) : k = m := by
  obtain ⟨Z, hZ, idx, hidx, rfl⟩ := hk
  obtain ⟨Z', hZ', idx', hidx', rfl⟩ := hm
  have hZZ : Z = Z' := Finset.ext fun z => (hZ z).trans (hZ' z).symm
  subst hZZ
  exact Finset.sum_congr rfl fun z hz => hasZeroIndex_unique (hidx z hz) (hidx' z hz)

/-- `wind_∞` at a puncture is unique when it exists. -/
lemma fp_hasWindInfAt_unique {H : V 1 → ℝ} {u : ℂ → V 1} {e : ℝ → ℝ → ℂ} {ε : ℝ} {k m : ℤ}
    (hk : HasWindInfAt H u e ε k) (hm : HasWindInfAt H u e ε m) : k = m := by
  obtain ⟨s₀, hs₀⟩ := hk
  obtain ⟨s₁, hs₁⟩ := hm
  exact hasLoopWind_unique (hs₀ _ (le_max_left s₀ s₁)) (hs₁ _ (le_max_right s₀ s₁))

theorem isFastPlane_iff_hasWindInfAt_one_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V 1)
    (hu : IsFiniteEnergyCurve H J Set.univ u) (P : ReebOrbit H) (hP : P.IsPrime)
    (hnd : IsNondegenerateEnd H u cylInf P 1) :
    IsFastPlane H J u ↔ HasWindInfAt H u cylInf 1 1 := by
  classical
  have hu' : IsFiniteEnergyCurve H J (↑(∅ : Finset ℂ))ᶜ u := by
    simpa only [Finset.coe_empty, Set.compl_empty] using hu
  have hΓ : ∀ z ∈ (∅ : Finset ℂ), ∃ Pz : ReebOrbit H, IsNondegenerateEnd H u (cylEndAt z) Pz (-1) :=
    fun z hz => absurd hz (Finset.notMem_empty z)
  -- `π ∂ₛ u` does not vanish identically
  have hne : ∃ z ∉ (∅ : Finset ℂ), piDs H u z ≠ 0 := by
    by_contra hall
    push_neg at hall
    have hpos := dlambdaEnergy_pos_of_plane H hH J hJ u hu
      (exists_ne_of_isNondegenerateEnd H u cylInf P one_ne_zero hnd)
    obtain ⟨-, hu0, hhol, -⟩ := hu
    have hzero : ∀ z, ENNReal.ofReal (dlambdaDensity H u z) = 0 := by
      intro z
      rw [ENNReal.ofReal_eq_zero]
      by_contra hlt
      push_neg at hlt
      exact ((piDs_ne_zero_iff_dlambdaDensity_pos H hH J hJ Set.univ isOpen_univ u hu0 hhol
        (Set.mem_univ z)).2 hlt) (hall z (Finset.notMem_empty z))
    have : dlambdaEnergy H Set.univ u = 0 := by
      unfold dlambdaEnergy
      simp only [hzero, lintegral_zero]
    rw [this] at hpos
    exact lt_irrefl _ hpos
  obtain ⟨kinf, kz, kπ, hinf, -, hWP, hrel⟩ :=
    windPi_eq_windInf_sub_card H hH J hJ ∅ u hu' P hnd hΓ hne
  simp only [Finset.sum_empty, Finset.card_empty, Nat.cast_zero] at hrel
  constructor
  · rintro ⟨-, -, h0⟩
    have : kπ = 0 := fp_hasWindPi_unique hWP h0
    have hk : kinf = 1 := by omega
    exact hk ▸ hinf
  · intro h1
    have : kinf = 1 := fp_hasWindInfAt_unique hinf h1
    have hk : kπ = 0 := by omega
    exact ⟨hu, ⟨P, hP, hnd⟩, hk ▸ hWP⟩

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V 1)
    (hu : IsFiniteEnergyCurve H J Set.univ u) (P : ReebOrbit H) (hP : P.IsPrime)
    (hnd : IsNondegenerateEnd H u cylInf P 1) :
    IsFastPlane H J u ↔ HasWindInfAt H u cylInf 1 1 :=
  isFastPlane_iff_hasWindInfAt_one_aux H hH J hJ u hu P hP hnd
