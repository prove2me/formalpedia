-- Prove2me | solution 1 for ConfoundRobust.Minimax.corollary_7
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T00:10:38.316455+00:00
-- url     : https://prove2.me/submissions/929a73fa-4a62-462f-94d9-8921a85f99a3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ConfoundRobust_Minimax_Setting
import Theorems.Thm_ConfoundRobust_Minimax_theorem_6

open MeasureTheory

open ConfoundRobust.Minimax in
theorem solution :
    ∀ v : ℕ, ∃ K : ℝ, ∀ (𝒳 : Type) [MeasurableSpace 𝒳] (m n : ℕ), 2 ≤ m → 0 < n →
      ∀ (μ : Measure (Obs 𝒳 m)) [IsProbabilityMeasure μ]
        (e : Fin m → 𝒳 → ℝ) (ν : ℝ), IsNominalPropensity μ e → 0 < ν →
        (∀ t x, ν ≤ e t x) → (∀ t x, e t x ≤ 1) →
      ∀ B : ℝ, 0 ≤ B → (∀ᵐ z ∂μ, |z.2.2| ≤ B) →
      ∀ Γ : ℝ, 1 ≤ Γ →
      ∀ Pol : Set (𝒳 → Fin m → ℝ), (∀ π ∈ Pol, IsPolicy π) → VCMajorLE (policyFns Pol) v →
        PointwiseSeparable (policyFns Pol) →
      ∀ π0 : 𝒳 → Fin m → ℝ, IsPolicy π0 →
      ∀ δ : ℝ, 0 < δ → δ < 1 →
      ∃ E : Set (Fin n → Obs 𝒳 m), MeasurableSet E ∧
        ENNReal.ofReal (1 - δ) ≤ Measure.pi (fun _ : Fin n => μ) E ∧
        ∀ ω ∈ E, ∀ πh ∈ Pol,
          (∀ π ∈ Pol, sWorstRegret ω πh π0 (WSetN Γ e ω) ≤ sWorstRegret ω π π0 (WSetN Γ e ω)) →
          worstRegret μ πh π0 (WSet Γ e) ≤
            sInf ((fun π => worstRegret μ π π0 (WSet Γ e)) '' Pol) + rateCor7 ν B Γ K m n δ := by
  intro v
  obtain ⟨K, hK⟩ := ConfoundRobust.Minimax.theorem_6 v
  refine ⟨K, ?_⟩
  intro 𝒳 _ m n hm hn μ _ e ν he hν hνe he1 B hB hY Γ hΓ Pol hPol hVC hsep π0 hπ0 δ hδ hδ1
  obtain ⟨E, hEm, hEμ, hE⟩ :=
    hK 𝒳 m n hm hn μ e ν he hν hνe he1 B hB hY Γ hΓ Pol hPol hVC hsep π0 hπ0 δ hδ hδ1
  refine ⟨E, hEm, hEμ, ?_⟩
  intro ω hω πh hπh hmin
  have hrate : rateCor7 ν B Γ K m n δ = 2 * rateThm6 ν B Γ K m n δ := by
    unfold rateCor7 rateThm6; ring
  rw [hrate]
  set ε := rateThm6 ν B Γ K m n δ
  have hall : ∀ π ∈ Pol, worstRegret μ πh π0 (WSet Γ e) - 2 * ε ≤ worstRegret μ π π0 (WSet Γ e) := by
    intro π hπ
    have a1 := abs_le.mp (hE ω hω πh hπh)
    have a2 := abs_le.mp (hE ω hω π hπ)
    have a3 := hmin π hπ
    linarith [a1.1, a1.2, a2.1, a2.2]
  have : worstRegret μ πh π0 (WSet Γ e) - 2 * ε ≤
      sInf ((fun π => worstRegret μ π π0 (WSet Γ e)) '' Pol) := by
    apply le_csInf (Set.Nonempty.image _ ⟨πh, hπh⟩)
    rintro _ ⟨π, hπ, rfl⟩
    exact hall π hπ
  linarith
