-- Prove2me | solution 1 for FiniteEnergyPlane.windInf_bounds_of_plane
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-03T12:50:06.716869+00:00
-- url     : https://prove2.me/submissions/bb6cb79a-a0c3-42e8-b1f4-c4b4dbb0faed

import Definitions.Def_FiniteEnergyPlane_Winding
import Theorems.Thm_FiniteEnergyPlane_windPi_eq_windInf_sub_card
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_unique
import Theorems.Thm_FiniteEnergyPlane_hasZeroIndex_unique
import Theorems.Thm_FiniteEnergyPlane_exists_ne_of_isNondegenerateEnd
import Theorems.Thm_FiniteEnergyPlane_dlambdaEnergy_pos_of_plane
import Theorems.Thm_FiniteEnergyPlane_piDs_ne_zero_iff_dlambdaDensity_pos
import Theorems.Thm_FiniteEnergyPlane_one_le_windInf_of_plane
import Theorems.Thm_FiniteEnergyPlane_exists_hasWindInfAt_hasEigenWind
import Theorems.Thm_FiniteEnergyPlane_czIndexOfPath_eq_alphaMinus_add_alphaPlus
import Theorems.Thm_FiniteEnergyPlane_isFiniteEnergyCurve_comp_inv
import Theorems.Thm_FiniteEnergyPlane_exists_dlambdaDensity_ne_zero_of_isOpen
import Theorems.Thm_FiniteEnergyPlane_periodicOrbit_bridge

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-!
# Winding bounds for finite-energy planes

Glue: `ũ(z) = u(z⁻¹)` turns the end at `∞` into a puncture at `0`; Hryniewicz (16) gives an
eigenvalue `μ < 0` of winding `k = wind_∞ ≤ α⁻`, HWZ Thm 3.10 gives `μ_CZ = α⁻ + α⁺ ≥ 2α⁻`,
Remark 3.20 gives `k ≥ 1` and Lemma 2.15 (with `Γ = ∅`) gives `wind_π = k - 1`.
-/


namespace FiniteEnergyPlane

lemma wb_hasWindPi_unique {H : V 1 → ℝ} {u : ℂ → V 1} {Γ : Finset ℂ} {k m : ℤ}
    (hk : HasWindPi H u Γ k) (hm : HasWindPi H u Γ m) : k = m := by
  obtain ⟨Z, hZ, idx, hidx, rfl⟩ := hk
  obtain ⟨Z', hZ', idx', hidx', rfl⟩ := hm
  have hZZ : Z = Z' := Finset.ext fun z => (hZ z).trans (hZ' z).symm
  subst hZZ
  exact Finset.sum_congr rfl fun z hz => hasZeroIndex_unique (hidx z hz) (hidx' z hz)

lemma wb_hasWindInfAt_unique {H : V 1 → ℝ} {u : ℂ → V 1} {e : ℝ → ℝ → ℂ} {ε : ℝ} {k m : ℤ}
    (hk : HasWindInfAt H u e ε k) (hm : HasWindInfAt H u e ε m) : k = m := by
  obtain ⟨s₀, hs₀⟩ := hk
  obtain ⟨s₁, hs₁⟩ := hm
  exact hasLoopWind_unique (hs₀ _ (le_max_left s₀ s₁)) (hs₁ _ (le_max_right s₀ s₁))

lemma wb_cylEndAt_zero_inv (s t : ℝ) : (cylEndAt 0 s t)⁻¹ = cylInf s t := by
  unfold cylEndAt cylInf cwLoop ccwLoop
  rw [zero_add, mul_inv, ← Complex.ofReal_inv, ← Real.exp_neg, neg_neg, ← Complex.exp_neg]
  congr 2
  ring

lemma wb_endA_inv {n : ℕ} (H : V n → ℝ) (u : ℂ → V n) :
    endA H (fun z => u z⁻¹) (cylEndAt 0) = endA H u cylInf := by
  funext p
  simp only [endA, wb_cylEndAt_zero_inv]

lemma wb_endW_inv {n : ℕ} (H : V n → ℝ) (u : ℂ → V n) :
    endW H (fun z => u z⁻¹) (cylEndAt 0) = endW H u cylInf := by
  funext p
  simp only [endW, wb_cylEndAt_zero_inv]

theorem windInf_bounds_of_plane_aux (H₀ : HryniewiczCriterion.R4 → ℝ)
    (hH₀ : HryniewiczCriterion.IsStrictlyStarShapedLevel H₀) :
    let toV : HryniewiczCriterion.R4 → V 1 := fun x k => x (Fin.cast (by norm_num) k)
    let H : V 1 → ℝ := fun y => H₀ (fun k => y (Fin.cast (by norm_num) k))
    ∀ J : V 1 → V 1 →L[ℝ] V 1, IsCompatibleXiStructure H J →
    ∀ (P : HryniewiczCriterion.PeriodicOrbit H₀) (Q : ReebOrbit H),
      Set.range Q.x = Set.range (fun τ => toV (P.x τ)) →
      Q.T = ∫ τ in (0 : ℝ)..P.T, liouville (toV (P.x τ)) (deriv (fun s => toV (P.x s)) τ) →
      Q.IsNondegenerate →
      ∀ u : ℂ → V 1, IsFiniteEnergyCurve H J Set.univ u → IsNondegenerateEnd H u cylInf Q 1 →
      ∃ k : ℤ, HasWindInfAt H u cylInf 1 k ∧ HasWindPi H u ∅ (k - 1) ∧ 1 ≤ k ∧
        ∀ Y : ℝ → (HryniewiczCriterion.R4 →L[ℝ] HryniewiczCriterion.R4),
          HryniewiczCriterion.IsLinearizedFlow H₀ P.x Y →
          2 * k ≤ HryniewiczCriterion.czIndexOfPath (HryniewiczCriterion.linearizedXiPath H₀ P Y) := by
  classical
  intro toV H J hJ P Q hrange hT hQnd u hu hnd
  have hH : IsStrictlyStarShapedLevel H := (periodicOrbit_bridge H₀).1.2 hH₀
  have hnc : ∃ z₁ z₂, u z₁ ≠ u z₂ := exists_ne_of_isNondegenerateEnd H u cylInf Q one_ne_zero hnd
  -- the inverted curve `ũ(z) = u(z⁻¹)` near `0`
  obtain ⟨hũ, hdens⟩ := isFiniteEnergyCurve_comp_inv H hH J hJ u hu
  have hndũ : IsNondegenerateEnd H (fun z => u z⁻¹) (cylEndAt 0) Q 1 := by
    unfold IsNondegenerateEnd
    rw [wb_endA_inv, wb_endW_inv]
    exact hnd
  have hneũ : ∀ ρ > 0, ∃ z ∈ ball (0 : ℂ) ρ \ {0}, dlambdaDensity H (fun z => u z⁻¹) z ≠ 0 := by
    intro ρ hρ
    obtain ⟨w, hw, hdw⟩ := exists_dlambdaDensity_ne_zero_of_isOpen H hH J hJ u hu hnc
      {w : ℂ | ρ⁻¹ < ‖w‖} (isOpen_lt continuous_const continuous_norm)
      ⟨((ρ⁻¹ + 1 : ℝ) : ℂ), by
        show ρ⁻¹ < ‖((ρ⁻¹ + 1 : ℝ) : ℂ)‖
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
        linarith⟩
    have hw' : ρ⁻¹ < ‖w‖ := hw
    have hwpos : 0 < ‖w‖ := lt_trans (inv_pos.2 hρ) hw'
    have hw0 : w ≠ 0 := norm_pos_iff.1 hwpos
    refine ⟨w⁻¹, ⟨?_, inv_ne_zero hw0⟩, ?_⟩
    · rw [mem_ball_zero_iff, norm_inv]
      exact (inv_lt_comm₀ hρ hwpos).1 hw'
    · rw [hdens _ (inv_ne_zero hw0), inv_inv]
      refine mul_ne_zero (inv_ne_zero (pow_ne_zero _ (norm_ne_zero_iff.2 (inv_ne_zero hw0)))) hdw
  -- Hryniewicz (16) at the puncture `0` of `ũ`
  obtain ⟨k, μ, hμ, hEW, hWIũ, hαm, -⟩ := exists_hasWindInfAt_hasEigenWind H hH J hJ 0 1
    one_pos (fun z => u z⁻¹) hũ Q 1 (Or.inl rfl) hndũ hneũ
  have hWI : HasWindInfAt H u cylInf 1 k := by
    have h := hWIũ
    unfold HasWindInfAt at h ⊢
    rwa [wb_endW_inv] at h
  -- HWZ Thm 3.10
  obtain ⟨a, b, ha, -, hab, hcz⟩ :=
    czIndexOfPath_eq_alphaMinus_add_alphaPlus H₀ hH₀ J hJ P Q hrange hT hQnd
  have hka : k ≤ a := hαm rfl a ha
  -- `k ≥ 1`
  obtain ⟨k', hk', hWI'⟩ := one_le_windInf_of_plane H hH J hJ u hu Q hnd
  have hkk' : k = k' := wb_hasWindInfAt_unique hWI hWI'
  -- Lemma 2.15 with `Γ = ∅`
  have hu' : IsFiniteEnergyCurve H J (↑(∅ : Finset ℂ))ᶜ u := by
    simpa only [Finset.coe_empty, Set.compl_empty] using hu
  have hΓ : ∀ z ∈ (∅ : Finset ℂ), ∃ Pz : ReebOrbit H, IsNondegenerateEnd H u (cylEndAt z) Pz (-1) :=
    fun z hz => absurd hz (Finset.notMem_empty z)
  have hne : ∃ z ∉ (∅ : Finset ℂ), piDs H u z ≠ 0 := by
    by_contra hall
    push_neg at hall
    have hpos := dlambdaEnergy_pos_of_plane H hH J hJ u hu hnc
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
    windPi_eq_windInf_sub_card H hH J hJ ∅ u hu' Q hnd hΓ hne
  simp only [Finset.sum_empty, Finset.card_empty, Nat.cast_zero] at hrel
  have hkinf : kinf = k := wb_hasWindInfAt_unique hinf hWI
  have hkπ : kπ = k - 1 := by omega
  refine ⟨k, hWI, hkπ ▸ hWP, hkk' ▸ hk', fun Y hY => ?_⟩
  rw [hcz Y hY]
  rcases hab with rfl | rfl <;> omega

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H₀ : HryniewiczCriterion.R4 → ℝ)
    (hH₀ : HryniewiczCriterion.IsStrictlyStarShapedLevel H₀) :
    let toV : HryniewiczCriterion.R4 → V 1 := fun x k => x (Fin.cast (by norm_num) k)
    let H : V 1 → ℝ := fun y => H₀ (fun k => y (Fin.cast (by norm_num) k))
    ∀ J : V 1 → V 1 →L[ℝ] V 1, IsCompatibleXiStructure H J →
    ∀ (P : HryniewiczCriterion.PeriodicOrbit H₀) (Q : ReebOrbit H),
      Set.range Q.x = Set.range (fun τ => toV (P.x τ)) →
      Q.T = ∫ τ in (0 : ℝ)..P.T, liouville (toV (P.x τ)) (deriv (fun s => toV (P.x s)) τ) →
      Q.IsNondegenerate →
      ∀ u : ℂ → V 1, IsFiniteEnergyCurve H J Set.univ u → IsNondegenerateEnd H u cylInf Q 1 →
      ∃ k : ℤ, HasWindInfAt H u cylInf 1 k ∧ HasWindPi H u ∅ (k - 1) ∧ 1 ≤ k ∧
        ∀ Y : ℝ → (HryniewiczCriterion.R4 →L[ℝ] HryniewiczCriterion.R4),
          HryniewiczCriterion.IsLinearizedFlow H₀ P.x Y →
          2 * k ≤ HryniewiczCriterion.czIndexOfPath (HryniewiczCriterion.linearizedXiPath H₀ P Y) :=
  windInf_bounds_of_plane_aux H₀ hH₀
