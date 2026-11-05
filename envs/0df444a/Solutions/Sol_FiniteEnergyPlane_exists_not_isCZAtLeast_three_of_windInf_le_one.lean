-- Prove2me | solution 1 for FiniteEnergyPlane.exists_not_isCZAtLeast_three_of_windInf_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-04T18:39:21.44287+00:00
-- url     : https://prove2.me/submissions/43df0086-4363-4240-aaca-e8c0bc075f89

import Definitions.Def_FiniteEnergyPlane_Compactness
import Theorems.Thm_FiniteEnergyPlane_two_le_windInf_of_negative_puncture
import Theorems.Thm_FiniteEnergyPlane_exists_hasWindPi_of_nondegenerate
import Theorems.Thm_FiniteEnergyPlane_windPi_eq_windInf_sub_card
import Theorems.Thm_FiniteEnergyPlane_piDs_ne_zero_iff_dlambdaDensity_pos
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_unique
import Theorems.Thm_FiniteEnergyPlane_hasZeroIndex_unique

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

open FiniteEnergyPlane in
theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (Γ : Finset ℂ) (hΓne : Γ.Nonempty) (u : ℂ → V 1) (hu : IsFiniteEnergyCurve H J (↑Γ)ᶜ u)
    (Pinf : ReebOrbit H) (hinf : IsNondegenerateEnd H u cylInf Pinf 1)
    (hΓ : ∀ z ∈ Γ, ∃ Pz : ReebOrbit H, Pz.IsNondegenerate ∧
      IsNondegenerateEnd H u (cylEndAt z) Pz (-1))
    (hpos : dlambdaEnergy H (↑Γ)ᶜ u ≠ 0) (k : ℤ) (hk : HasWindInfAt H u cylInf 1 k)
    (hk1 : k ≤ 1) :
    ∃ z ∈ Γ, ∃ Pz : ReebOrbit H, Pz.IsNondegenerate ∧
      IsNondegenerateEnd H u (cylEndAt z) Pz (-1) ∧ ¬ Pz.IsCZAtLeast 3 := by
  -- uniqueness of asymptotic windings
  have huniq : ∀ {e : ℝ → ℝ → ℂ} {ε : ℝ} {a b : ℤ}, HasWindInfAt H u e ε a →
      HasWindInfAt H u e ε b → a = b := by
    intro e ε a b ha hb
    obtain ⟨s₁, h₁⟩ := ha
    obtain ⟨s₂, h₂⟩ := hb
    exact hasLoopWind_unique (h₁ (max s₁ s₂) (le_max_left _ _))
      (h₂ (max s₁ s₂) (le_max_right _ _))
  -- `π du` does not vanish identically
  have hUo : IsOpen ((↑Γ)ᶜ : Set ℂ) := Γ.finite_toSet.isClosed.isOpen_compl
  have hne : ∃ z ∉ Γ, piDs H u z ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hpos
    unfold dlambdaEnergy
    rw [setLIntegral_congr_fun hUo.measurableSet (g := fun _ => (0 : ℝ≥0∞))]
    · simp
    · intro z hz
      have h0 : ¬ 0 < dlambdaDensity H u z := fun hlt =>
        ((piDs_ne_zero_iff_dlambdaDensity_pos H hH J hJ _ hUo u hu.2.1 hu.2.2.1 hz).2 hlt)
          (hcon z hz)
      simp only
      exact ENNReal.ofReal_eq_zero.2 (not_lt.1 h0)
  have hΓ' : ∀ z ∈ Γ, ∃ Pz : ReebOrbit H, IsNondegenerateEnd H u (cylEndAt z) Pz (-1) :=
    fun z hz => let ⟨P, _, hP⟩ := hΓ z hz; ⟨P, hP⟩
  obtain ⟨hzero, -⟩ := exists_hasWindPi_of_nondegenerate H hH J hJ Γ u hu Pinf hinf hΓ' hne
  obtain ⟨kinf, kz, kπ, hkinf, hkz, hkπ, heq⟩ :=
    windPi_eq_windInf_sub_card H hH J hJ Γ u hu Pinf hinf hΓ' hne
  have hkinf' : kinf = k := huniq hkinf hk
  -- `wind_π ≥ 0`
  have hπ0 : 0 ≤ kπ := by
    obtain ⟨Z, hZ, idx, hidx, hsum⟩ := hkπ
    rw [← hsum]
    refine Finset.sum_nonneg fun z hz => ?_
    obtain ⟨hzΓ, hz0⟩ := (hZ z).1 hz
    obtain ⟨m, hm1, hm⟩ := hzero z hzΓ hz0
    rw [hasZeroIndex_unique (hidx z hz) hm]
    omega
  by_contra hcon
  push Not at hcon
  -- every negative puncture has `wind_∞ ≥ 2`
  have h2 : ∀ z ∈ Γ, 2 ≤ kz z := by
    intro z hz
    obtain ⟨P, hPnd, hP⟩ := hΓ z hz
    obtain ⟨k', hk', h2k'⟩ := two_le_windInf_of_negative_puncture H hH J hJ Γ u hu z hz P hP
      hPnd (hcon z hz P hPnd hP) hpos
    rw [huniq (hkz z hz) hk']
    exact h2k'
  have hsum : ∑ _z ∈ Γ, (2 : ℤ) ≤ ∑ z ∈ Γ, kz z := Finset.sum_le_sum h2
  rw [Finset.sum_const, nsmul_eq_mul] at hsum
  have hc : (1 : ℤ) ≤ Γ.card := by exact_mod_cast hΓne.card_pos
  omega
