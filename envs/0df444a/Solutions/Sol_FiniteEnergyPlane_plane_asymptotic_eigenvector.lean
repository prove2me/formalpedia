-- Prove2me | solution 1 for FiniteEnergyPlane.plane_asymptotic_eigenvector
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-01T10:48:19.608733+00:00
-- url     : https://prove2.me/submissions/8e1790aa-9015-4272-bfbf-ebb409a53b9f

import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_isFiniteEnergyCurve_comp_inv
import Theorems.Thm_FiniteEnergyPlane_exists_dlambdaDensity_ne_zero_of_isOpen
import Theorems.Thm_FiniteEnergyPlane_isAsymptoticallyCylindricalEnd_of_isNondegenerate
import Theorems.Thm_FiniteEnergyPlane_hasExpAsymptoticsEnd_of_isAsymptoticallyCylindricalEnd
import Theorems.Thm_FiniteEnergyPlane_asymptotic_eigenvector



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff Real

theorem pae_inv_cylEnd (s t : ℝ) : (cylEnd s t)⁻¹ = cylInf s t := by
  unfold cylEnd cylInf cwLoop ccwLoop
  rw [zero_add, mul_inv, ← Complex.exp_neg, ← Complex.ofReal_inv, ← Real.exp_neg, neg_neg,
    neg_mul, neg_neg]

theorem pae_inv_cwLoop (R : ℝ) (hR : 0 < R) (t : ℝ) : (cwLoop 0 R⁻¹ t)⁻¹ = ccwLoop R t := by
  unfold cwLoop ccwLoop
  rw [zero_add, mul_inv, ← Complex.exp_neg, Complex.ofReal_inv, inv_inv, neg_mul, neg_neg]

theorem pae_eventually_le (C b ε : ℝ) (hb : 0 < b) (hε : 0 < ε) :
    ∃ s₀ : ℝ, ∀ s ≥ s₀, C * Real.exp (-(b * s)) ≤ ε := by
  have h : Tendsto (fun s : ℝ => C * Real.exp (-(b * s))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ => -(b * s)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hb)
    simpa using (Real.tendsto_exp_atBot.comp h1).const_mul C
  obtain ⟨s₀, hs₀⟩ := eventually_atTop.mp (h.eventually (ge_mem_nhds hε))
  exact ⟨s₀, hs₀⟩

theorem pae_isNondegenerateEnd_of_hasExp {n : ℕ} (H : V n → ℝ) (u : ℂ → V n)
    (e : ℝ → ℝ → ℂ) (P : ReebOrbit H) (ε b : ℝ) (hb : 0 < b)
    (h : HasExpAsymptoticsEnd H u e P ε b) : IsNondegenerateEnd H u e P ε := by
  obtain ⟨d, c, ⟨-, ha⟩, ⟨-, hw⟩⟩ := h
  obtain ⟨Ca, sa, hCa⟩ := ha 0
  obtain ⟨Cw, sw, hCw⟩ := hw 0
  refine ⟨d, c, b / 2, by positivity, ?_, ?_⟩
  · intro δ hδ
    obtain ⟨s₀, hs₀⟩ := pae_eventually_le Ca b δ hb hδ
    refine ⟨max s₀ sa, fun s hs t => ?_⟩
    have := hCa s (le_trans (le_max_right _ _) hs) t
    rw [norm_iteratedFDeriv_zero] at this
    exact this.trans (hs₀ s (le_trans (le_max_left _ _) hs))
  · intro δ hδ
    obtain ⟨s₀, hs₀⟩ := pae_eventually_le Cw (b / 2) δ (by positivity) hδ
    refine ⟨max s₀ sw, fun s hs t => ?_⟩
    have := hCw s (le_trans (le_max_right _ _) hs) t
    rw [norm_iteratedFDeriv_zero] at this
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (b / 2 * s) * ‖endW H u e (s, t) - P.x (ε * P.T * t + c)‖
        ≤ Real.exp (b / 2 * s) * (Cw * Real.exp (-(b * s))) :=
          mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
      _ = Cw * Real.exp (-(b / 2 * s)) := by
          rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
      _ ≤ δ := hs₀ s (le_trans (le_max_left _ _) hs)

theorem plane_asymptotic_eigenvector_aux {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J Set.univ u) (hnc : ∃ z₁ z₂, u z₁ ≠ u z₂) (P : ReebOrbit H)
    (hP : P.IsNondegenerate) (R : ℕ → ℝ) (hR : Tendsto R atTop atTop) (c : ℝ)
    (hconv : TendstoCInfty (fun k => loopInS H u (ccwLoop (R k))) (fun t => P.x (P.T * t + c))) :
    (∃ b > 0, HasExpAsymptoticsEnd H u cylInf P 1 b) ∧
      ∃ (μ : ℝ) (v : ℝ → V n), HasAsymptoticEigenvector H J u cylInf P 1 μ v := by
  obtain ⟨hũ, hden⟩ := isFiniteEnergyCurve_comp_inv H hH J hJ u hu
  have hA : endA H (fun z => u z⁻¹) cylEnd = endA H u cylInf := by
    funext p; simp only [endA, pae_inv_cylEnd]
  have hW : endW H (fun z => u z⁻¹) cylEnd = endW H u cylInf := by
    funext p; simp only [endW, pae_inv_cylEnd]
  -- the loop hypothesis at the puncture `0` of `z ↦ u z⁻¹`
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hR.eventually (eventually_ge_atTop 1))
  set ρ : ℕ → ℝ := fun k => (R (k + N))⁻¹
  have hRpos : ∀ k, 0 < R (k + N) := fun k => lt_of_lt_of_le one_pos (hN _ (by omega))
  have hρ : ∀ k, 0 < ρ k := fun k => inv_pos.mpr (hRpos k)
  have hρ0 : Tendsto ρ atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (hR.comp (tendsto_add_atTop_nat N))
  have hloop : (fun k => loopInS H (fun z => u z⁻¹) (cwLoop 0 (ρ k))) =
      fun k => loopInS H u (ccwLoop (R (k + N))) := by
    funext k t
    simp only [loopInS, ρ, pae_inv_cwLoop _ (hRpos k)]
  have hconv' : TendstoCInfty (fun k => loopInS H (fun z => u z⁻¹) (cwLoop 0 (ρ k)))
      (fun t => P.x (1 * P.T * t + c)) := by
    rw [hloop]
    simp only [one_mul]
    intro m U hU
    exact (tendsto_add_atTop_nat N).eventually (hconv m U hU)
  have hac := isAsymptoticallyCylindricalEnd_of_isNondegenerate H hH J hJ _ hũ P hP 1
    (Or.inl rfl) ρ hρ hρ0 c hconv'
  obtain ⟨b, hb, hexp⟩ := hasExpAsymptoticsEnd_of_isAsymptoticallyCylindricalEnd H hH J hJ _ hũ
    P hP 1 (Or.inl rfl) hac
  have hnd := pae_isNondegenerateEnd_of_hasExp H _ cylEnd P 1 b hb hexp
  -- the `dλ`-density of `z ↦ u z⁻¹` does not vanish identically near `0`
  have hπ : ∀ r > 0, ∃ z ∈ ball (0 : ℂ) r \ {0}, dlambdaDensity H (fun z => u z⁻¹) z ≠ 0 := by
    intro r hr
    obtain ⟨w, hw, hdw⟩ := exists_dlambdaDensity_ne_zero_of_isOpen H hH J hJ u hu hnc
      {w : ℂ | r⁻¹ < ‖w‖} (isOpen_lt continuous_const continuous_norm)
      ⟨((r⁻¹ + 1 : ℝ) : ℂ), by
        simp only [Set.mem_setOf_eq, Complex.norm_real, Real.norm_eq_abs]
        rw [abs_of_pos (by positivity)]; linarith⟩
    have hw0 : w ≠ 0 := by
      rintro rfl; simp only [Set.mem_setOf_eq, norm_zero] at hw; linarith [inv_pos.mpr hr]
    refine ⟨w⁻¹, ⟨?_, inv_ne_zero hw0⟩, ?_⟩
    · rw [mem_ball_zero_iff, norm_inv]
      have hw' : r⁻¹ < ‖w‖ := hw
      calc ‖w‖⁻¹ < (r⁻¹)⁻¹ := inv_strictAnti₀ (inv_pos.mpr hr) hw'
        _ = r := inv_inv r
    · rw [hden _ (inv_ne_zero hw0), inv_inv]
      exact mul_ne_zero (inv_ne_zero (pow_ne_zero _ (norm_ne_zero_iff.mpr (inv_ne_zero hw0))))
        hdw
  obtain ⟨μ, v, hev⟩ := (asymptotic_eigenvector H hH J hJ _ hũ P 1 (Or.inl rfl) hnd).2 hπ
  refine ⟨⟨b, hb, ?_⟩, μ, v, ?_⟩
  · unfold HasExpAsymptoticsEnd at hexp ⊢
    rwa [hA, hW] at hexp
  · unfold HasAsymptoticEigenvector at hev ⊢
    rwa [hW] at hev

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J Set.univ u) (hnc : ∃ z₁ z₂, u z₁ ≠ u z₂) (P : ReebOrbit H)
    (hP : P.IsNondegenerate) (R : ℕ → ℝ) (hR : Tendsto R atTop atTop) (c : ℝ)
    (hconv : TendstoCInfty (fun k => loopInS H u (ccwLoop (R k))) (fun t => P.x (P.T * t + c))) :
    (∃ b > 0, HasExpAsymptoticsEnd H u cylInf P 1 b) ∧
      ∃ (μ : ℝ) (v : ℝ → V n), HasAsymptoticEigenvector H J u cylInf P 1 μ v :=
  plane_asymptotic_eigenvector_aux H hH J hJ u hu hnc P hP R hR c hconv
