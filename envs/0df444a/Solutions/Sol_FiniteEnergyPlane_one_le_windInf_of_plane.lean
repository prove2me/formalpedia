-- Prove2me | solution 1 for FiniteEnergyPlane.one_le_windInf_of_plane
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-03T11:52:54.276405+00:00
-- url     : https://prove2.me/submissions/c748c734-6bb2-444b-afcd-88e592f24d25

import Definitions.Def_FiniteEnergyPlane_Winding
import Theorems.Thm_FiniteEnergyPlane_windPi_eq_windInf_sub_card
import Theorems.Thm_FiniteEnergyPlane_exists_hasWindPi_of_nondegenerate
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_unique
import Theorems.Thm_FiniteEnergyPlane_dlambdaEnergy_pos_of_plane
import Theorems.Thm_FiniteEnergyPlane_piDs_ne_zero_iff_dlambdaDensity_pos

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

namespace FiniteEnergyPlane

/-- The local index of an isolated zero is unique. -/
lemma r320_zeroIndex_unique {f : ℂ → ℂ} {z₀ : ℂ} {k m : ℤ} (hk : HasZeroIndex f z₀ k)
    (hm : HasZeroIndex f z₀ m) : k = m := by
  obtain ⟨-, r, hr, -, hkw⟩ := hk
  obtain ⟨-, r', hr', -, hmw⟩ := hm
  have hρ : min r r' / 2 ∈ Set.Ioo 0 r :=
    ⟨by positivity, by linarith [min_le_left r r', lt_min hr hr']⟩
  have hρ' : min r r' / 2 ∈ Set.Ioo 0 r' :=
    ⟨by positivity, by linarith [min_le_right r r', lt_min hr hr']⟩
  exact hasLoopWind_unique (hkw _ hρ) (hmw _ hρ')

/-- A plane with a nondegenerate end at `∞` is nonconstant. -/
lemma r320_nonconst (H : V 1 → ℝ) (u : ℂ → V 1) (P : ReebOrbit H)
    (hnd : IsNondegenerateEnd H u cylInf P 1) : ∃ z₁ z₂, u z₁ ≠ u z₂ := by
  by_contra hc
  push_neg at hc
  obtain ⟨d, -, -, -, ha, -⟩ := hnd
  obtain ⟨s₀, hs₀⟩ := ha 1 one_pos
  set c : ℝ := aCoord H (u 0) with hcdef
  have hconst : ∀ s t : ℝ, endA H u cylInf (s, t) = c := fun s t => by
    simp only [endA, hcdef, hc (cylInf s t) 0]
  set s : ℝ := max s₀ ((|c| + |d| + 2) / P.T) with hsdef
  have hs := hs₀ s (le_max_left _ _) 0
  dsimp only at hs
  rw [hconst, Real.norm_eq_abs, one_mul] at hs
  have hT := P.T_pos
  have hsT : |c| + |d| + 2 ≤ P.T * s := by
    have : (|c| + |d| + 2) / P.T ≤ s := le_max_right _ _
    rw [div_le_iff₀ hT] at this
    linarith
  have h1 := abs_le.1 hs
  have := le_abs_self c
  have := neg_abs_le c
  have := le_abs_self d
  have := neg_abs_le d
  nlinarith [h1.1, h1.2]

theorem one_le_windInf_of_plane_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V 1)
    (hu : IsFiniteEnergyCurve H J Set.univ u) (P : ReebOrbit H)
    (hnd : IsNondegenerateEnd H u cylInf P 1) :
    ∃ k : ℤ, 1 ≤ k ∧ HasWindInfAt H u cylInf 1 k := by
  classical
  have hu' : IsFiniteEnergyCurve H J (↑(∅ : Finset ℂ))ᶜ u := by
    simpa only [Finset.coe_empty, Set.compl_empty] using hu
  have hΓ : ∀ z ∈ (∅ : Finset ℂ), ∃ Pz : ReebOrbit H, IsNondegenerateEnd H u (cylEndAt z) Pz (-1) :=
    fun z hz => absurd hz (Finset.notMem_empty z)
  -- `π ∂ₛ u` does not vanish identically
  have hne : ∃ z ∉ (∅ : Finset ℂ), piDs H u z ≠ 0 := by
    by_contra hall
    push_neg at hall
    have hpos := dlambdaEnergy_pos_of_plane H hH J hJ u hu (r320_nonconst H u P hnd)
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
  obtain ⟨hidx1, -⟩ := exists_hasWindPi_of_nondegenerate H hH J hJ ∅ u hu' P hnd hΓ hne
  obtain ⟨Z, hZ, idx, hidx, hsum⟩ := hWP
  have hpos : ∀ z ∈ Z, 0 ≤ idx z := by
    intro z hz
    obtain ⟨hzΓ, hz0⟩ := (hZ z).1 hz
    obtain ⟨m, hm1, hm⟩ := hidx1 z hzΓ hz0
    rw [r320_zeroIndex_unique (hidx z hz) hm]
    linarith
  have hkπ : 0 ≤ kπ := hsum ▸ Finset.sum_nonneg hpos
  refine ⟨kinf, ?_, hinf⟩
  simp only [Finset.sum_empty, Finset.card_empty, Nat.cast_zero] at hrel
  linarith

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V 1)
    (hu : IsFiniteEnergyCurve H J Set.univ u) (P : ReebOrbit H)
    (hnd : IsNondegenerateEnd H u cylInf P 1) :
    ∃ k : ℤ, 1 ≤ k ∧ HasWindInfAt H u cylInf 1 k :=
  one_le_windInf_of_plane_aux H hH J hJ u hu P hnd
