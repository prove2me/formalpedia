-- Prove2me | solution 1 for FiniteEnergyPlane.two_le_windInf_of_negative_puncture
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-04T18:19:45.371776+00:00
-- url     : https://prove2.me/submissions/c1bd4ee0-c326-497f-8e1d-8592aecd8e66

import Definitions.Def_FiniteEnergyPlane_Compactness
import Theorems.Thm_FiniteEnergyPlane_exists_hasWindInfAt_hasEigenWind
import Theorems.Thm_FiniteEnergyPlane_two_le_of_hasEigenWind_of_czIndex_ge_three
import Theorems.Thm_FiniteEnergyPlane_periodicOrbit_bridge
import Theorems.Thm_FiniteEnergyPlane_exists_ball_piDs_eq_zero_or_isolated
import Theorems.Thm_FiniteEnergyPlane_piDs_ne_zero_iff_dlambdaDensity_pos
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem two_le_windInf_of_negative_puncture_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (Γ : Finset ℂ) (u : ℂ → V 1) (hu : IsFiniteEnergyCurve H J (↑Γ)ᶜ u) (z₀ : ℂ) (hz₀ : z₀ ∈ Γ)
    (Q : ReebOrbit H) (hend : IsNondegenerateEnd H u (cylEndAt z₀) Q (-1))
    (hQ : Q.IsNondegenerate) (hcz : Q.IsCZAtLeast 3) (hpos : dlambdaEnergy H (↑Γ)ᶜ u ≠ 0) :
    ∃ k : ℤ, HasWindInfAt H u (cylEndAt z₀) (-1) k ∧ 2 ≤ k := by
  set U : Set ℂ := (↑Γ : Set ℂ)ᶜ with hUdef
  have hUo : IsOpen U := Γ.finite_toSet.isClosed.isOpen_compl
  obtain ⟨hsm, hnz, hhol, hfin⟩ := hu
  -- some point of `U` has positive `dλ`-density
  have hz₁ : ∃ z ∈ U, 0 < dlambdaDensity H u z := by
    by_contra hcon
    push_neg at hcon
    apply hpos
    unfold dlambdaEnergy
    rw [setLIntegral_congr_fun hUo.measurableSet (g := fun _ => 0)
      (fun z hz => ENNReal.ofReal_eq_zero.mpr (hcon z hz))]
    simp
  -- the set where `π ∂ₛu` vanishes on a whole disc, and the set of isolated zeros/nonzeros
  set A : Set ℂ := interior {z | piDs H u z = 0} with hA
  set B : Set ℂ := {z | ∃ ρ > (0 : ℝ), ∀ w ∈ ball z ρ, w ≠ z → piDs H u w ≠ 0} with hB
  have hAo : IsOpen A := isOpen_interior
  have hBo : IsOpen B := by
    rw [Metric.isOpen_iff]
    rintro z ⟨ρ, hρ, hz⟩
    refine ⟨ρ, hρ, fun w hw => ?_⟩
    by_cases hwz : w = z
    · subst hwz; exact ⟨ρ, hρ, hz⟩
    · have hd : 0 < dist w z := dist_pos.mpr hwz
      have hwρ : dist w z < ρ := hw
      refine ⟨min (ρ - dist w z) (dist w z), lt_min (by linarith) hd, fun w' hw' _ => ?_⟩
      have h1 : dist w' w < ρ - dist w z := lt_of_lt_of_le hw' (min_le_left _ _)
      have h2 : dist w' w < dist w z := lt_of_lt_of_le hw' (min_le_right _ _)
      apply hz w'
      · show dist w' z < ρ
        linarith [dist_triangle w' w z]
      · rintro rfl
        rw [dist_comm] at h2
        exact lt_irrefl _ h2
  have hcover : U ⊆ A ∪ B := by
    intro z hz
    obtain ⟨r, hr, -, hcase⟩ :=
      exists_ball_piDs_eq_zero_or_isolated H hH J hJ U hUo u hsm hnz hhol z hz
    rcases hcase with h0 | ⟨h1, -⟩
    · left
      rw [hA, mem_interior]
      exact ⟨ball z r, fun w hw => h0 w hw, isOpen_ball, mem_ball_self hr⟩
    · right
      exact ⟨r, hr, h1⟩
  have hUB : (U ∩ B).Nonempty := by
    obtain ⟨z, hzU, hzpos⟩ := hz₁
    have hne : piDs H u z ≠ 0 :=
      (piDs_ne_zero_iff_dlambdaDensity_pos H hH J hJ U hUo u hnz hhol hzU).mpr hzpos
    refine ⟨z, hzU, ?_⟩
    rcases hcover hzU with hzA | hzB
    · exfalso
      exact hne (interior_subset (s := {z | piDs H u z = 0}) hzA)
    · exact hzB
  have hUconn : IsPreconnected U := by
    have h := Set.Countable.isPathConnected_compl_of_one_lt_rank (E := ℂ)
      (by simp [Complex.rank_real_complex]) (Finset.countable_toSet Γ)
    exact h.isConnected.isPreconnected
  have hUA : ∀ z ∈ U, z ∉ A := by
    intro z hzU hzA
    obtain ⟨w, hwU, hwA, hwB⟩ :=
      hUconn A B hAo hBo hcover ⟨z, hzU, hzA⟩ hUB
    rw [hA, mem_interior] at hwA
    obtain ⟨t, ht, hto, hwt⟩ := hwA
    obtain ⟨ρ₁, hρ₁, hb₁⟩ := Metric.isOpen_iff.mp hto w hwt
    obtain ⟨ρ₂, hρ₂, hb₂⟩ := hwB
    set m := min ρ₁ ρ₂
    have hm : 0 < m := lt_min hρ₁ hρ₂
    set w' : ℂ := w + ((m / 2 : ℝ) : ℂ)
    have hd : dist w' w = m / 2 := by
      simp only [w', dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs]
      exact abs_of_pos (by linarith)
    have hw'1 : w' ∈ ball w ρ₁ := by
      show dist w' w < ρ₁; rw [hd]; linarith [min_le_left ρ₁ ρ₂]
    have hw'2 : w' ∈ ball w ρ₂ := by
      show dist w' w < ρ₂; rw [hd]; linarith [min_le_right ρ₁ ρ₂]
    have hw'ne : w' ≠ w := by
      intro h; rw [h, dist_self] at hd; linarith
    exact hb₂ w' hw'2 hw'ne (ht (hb₁ hw'1))
  -- a punctured disc around `z₀` inside `U`
  obtain ⟨r₀, hr₀, hr₀U⟩ : ∃ r₀ > (0 : ℝ), ball z₀ r₀ \ {z₀} ⊆ U := by
    have hcl : IsClosed (↑(Γ.erase z₀) : Set ℂ) := (Γ.erase z₀).finite_toSet.isClosed
    have hmem : (↑(Γ.erase z₀) : Set ℂ)ᶜ ∈ 𝓝 z₀ :=
      hcl.isOpen_compl.mem_nhds (by simp)
    obtain ⟨r₀, hr₀, hsub⟩ := Metric.mem_nhds_iff.mp hmem
    refine ⟨r₀, hr₀, fun z ⟨hz, hz'⟩ => ?_⟩
    have := hsub hz
    simp only [Set.mem_compl_iff, Finset.coe_erase, Set.mem_diff, Finset.mem_coe,
      Set.mem_singleton_iff, not_and, not_not] at this hz' ⊢
    intro hzΓ
    exact hz' (this hzΓ)
  have hne : ∀ ρ > 0, ∃ z ∈ ball z₀ ρ \ {z₀}, dlambdaDensity H u z ≠ 0 := by
    intro ρ hρ
    set m := min ρ r₀
    have hm : 0 < m := lt_min hρ hr₀
    set z : ℂ := z₀ + ((m / 2 : ℝ) : ℂ)
    have hd : dist z z₀ = m / 2 := by
      simp only [z, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs]
      exact abs_of_pos (by linarith)
    have hsub : ball z (m / 2) ⊆ ball z₀ m \ {z₀} := by
      intro w hw
      have hw' : dist w z < m / 2 := hw
      refine ⟨?_, ?_⟩
      · show dist w z₀ < m
        linarith [dist_triangle w z z₀]
      · rintro rfl
        rw [dist_comm, hd] at hw'
        exact lt_irrefl _ hw'
    have hsub' : ball z₀ m \ {z₀} ⊆ ball z₀ ρ \ {z₀} :=
      Set.diff_subset_diff_left (ball_subset_ball (min_le_left _ _))
    have hsubU : ball z₀ m \ {z₀} ⊆ U :=
      (Set.diff_subset_diff_left (ball_subset_ball (min_le_right _ _))).trans hr₀U
    have hzU : z ∈ U := hsubU (hsub (mem_ball_self (by linarith)))
    have hzA := hUA z hzU
    rw [hA, mem_interior] at hzA
    push_neg at hzA
    obtain ⟨w, hw, hwne⟩ : ∃ w ∈ ball z (m / 2), piDs H u w ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hzA (ball z (m / 2)) (fun w hw => hcon w hw) isOpen_ball
        (mem_ball_self (by linarith))
    have hwU : w ∈ U := hsubU (hsub hw)
    refine ⟨w, hsub' (hsub hw), ?_⟩
    exact ne_of_gt ((piDs_ne_zero_iff_dlambdaDensity_pos H hH J hJ U hUo u hnz hhol hwU).mp hwne)
  -- restrict the curve to the punctured disc
  have hu' : IsFiniteEnergyCurve H J (ball z₀ r₀ \ {z₀}) u := by
    refine ⟨hsm.mono hr₀U, fun z hz => hnz z (hr₀U hz), fun z hz => hhol z (hr₀U hz),
      lt_of_le_of_lt ?_ hfin⟩
    unfold energy
    exact iSup₂_mono fun φ _ => lintegral_mono_set hr₀U
  obtain ⟨k, μ, hμ, hk, hwind, -, -⟩ :=
    exists_hasWindInfAt_hasEigenWind H hH J hJ z₀ r₀ hr₀ u hu' Q (-1) (Or.inr rfl) hend hne
  refine ⟨k, hwind, ?_⟩
  have hμ0 : 0 ≤ μ := by linarith
  -- transfer to `HryniewiczCriterion`
  set H₀ : HryniewiczCriterion.R4 → ℝ := fun x => H (ofR4 x) with hH₀def
  have hbr := periodicOrbit_bridge H₀
  have hH₀ : HryniewiczCriterion.IsStrictlyStarShapedLevel H₀ := hbr.1.mp hH
  obtain ⟨P, hrange, haction⟩ := (hbr.2 hH₀).2 Q
  exact two_le_of_hasEigenWind_of_czIndex_ge_three H₀ hH₀ J hJ P Q hrange.symm haction hQ
    (fun Y hY => hcz P hrange.symm haction Y hY) μ hμ0 k hk

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (Γ : Finset ℂ) (u : ℂ → V 1) (hu : IsFiniteEnergyCurve H J (↑Γ)ᶜ u) (z₀ : ℂ) (hz₀ : z₀ ∈ Γ)
    (Q : ReebOrbit H) (hend : IsNondegenerateEnd H u (cylEndAt z₀) Q (-1))
    (hQ : Q.IsNondegenerate) (hcz : Q.IsCZAtLeast 3) (hpos : dlambdaEnergy H (↑Γ)ᶜ u ≠ 0) :
    ∃ k : ℤ, HasWindInfAt H u (cylEndAt z₀) (-1) k ∧ 2 ≤ k :=
  two_le_windInf_of_negative_puncture_aux H hH J hJ Γ u hu z₀ hz₀ Q hend hQ hcz hpos
