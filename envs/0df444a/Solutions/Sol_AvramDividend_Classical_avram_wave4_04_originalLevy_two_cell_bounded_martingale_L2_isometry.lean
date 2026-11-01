-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04_originalLevy_two_cell_bounded_martingale_L2_isometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T20:42:44.777215+00:00
-- url     : https://prove2.me/submissions/9a05cb82-fabc-4358-8bd1-3ce96e27d1b3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_originalLevy_disjointCells_adaptedProducts_L2_orthogonal
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_source_bounded_futurePayoff_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal
/-- Orthogonal same-source adapted Lévy cells satisfy the two-cell L² isometry. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t u v : ℝ≥0) (hst : s ≤ t) (htu : t ≤ u) (huv : u ≤ v)
    (H K : Ω → ℝ)
    (hH : StronglyMeasurable[𝓕 s] H)
    (hK : StronglyMeasurable[𝓕 u] K)
    (A B R S : ℝ) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hR0 : 0 ≤ R) (hS0 : 0 ≤ S)
    (hHb : ∀ ω, ‖H ω‖ ≤ A) (hKb : ∀ ω, ‖K ω‖ ≤ B)
    (φ ψ : ℝ → ℝ) (hφ : Measurable φ) (hψ : Measurable ψ)
    (hφb : ∀ z, ‖φ z‖ ≤ R)
    (hψb : ∀ z, ‖ψ z‖ ≤ S)
    (hψMean : (∫ ω, ψ (X.X (v - u) ω) ∂P) = 0) :
    (∫ ω, (H ω * φ (X.X t ω - X.X s ω) +
      K ω * ψ (X.X v ω - X.X u ω)) ^ 2 ∂P) =
    (∫ ω, (H ω * φ (X.X t ω - X.X s ω)) ^ 2 ∂P) +
    (∫ ω, (K ω * ψ (X.X v ω - X.X u ω)) ^ 2 ∂P) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let f : Ω → ℝ := fun ω => H ω * φ (X.X t ω - X.X s ω)
  let g : Ω → ℝ := fun ω => K ω * ψ (X.X v ω - X.X u ω)
  have hX (r : ℝ≥0) : Measurable (X.X r) := (X.adapted r).mono (𝓕.le r) le_rfl
  have hfM : StronglyMeasurable f :=
    (hH.mono (𝓕.le s)).mul ((hφ.comp ((hX t).sub (hX s))).stronglyMeasurable)
  have hgM : StronglyMeasurable g :=
    (hK.mono (𝓕.le u)).mul ((hψ.comp ((hX v).sub (hX u))).stronglyMeasurable)
  have hfB (ω : Ω) : ‖f ω‖ ≤ A * R := by
    dsimp [f]
    rw [abs_mul]
    gcongr
    exact hHb ω
    exact hφb _
  have hgB (ω : Ω) : ‖g ω‖ ≤ B * S := by
    dsimp [g]
    rw [abs_mul]
    gcongr
    exact hKb ω
    exact hψb _
  have hbounded (F : Ω → ℝ) (b : ℝ) (hFm : StronglyMeasurable F)
      (hFb : ∀ ω, ‖F ω‖ ≤ b) : Integrable F P :=
    Integrable.of_bound hFm.aestronglyMeasurable b (Filter.Eventually.of_forall hFb)
  have hfsq : Integrable (fun ω => f ω ^ 2) P :=
    hbounded _ ((A * R)^2) (hfM.fun_pow 2) (fun ω => by
      rw [norm_pow]; gcongr; exact hfB ω)
  have hgsq : Integrable (fun ω => g ω ^ 2) P :=
    hbounded _ ((B * S)^2) (hgM.fun_pow 2) (fun ω => by
      rw [norm_pow]; gcongr; exact hgB ω)
  have hcross : Integrable (fun ω => f ω * g ω) P :=
    hbounded _ ((A * R) * (B * S)) (hfM.mul hgM) (fun ω => by
      rw [norm_mul]; gcongr; exact hfB ω; exact hgB ω)
  have hψInt : Integrable (fun ω => ψ (X.X (v - u) ω)) P :=
    avram_wave3_04_source_bounded_futurePayoff_integrable X (v - u) ψ hψ S hψb
  have hz := avram_wave3_04_originalLevy_disjointCells_adaptedProducts_L2_orthogonal
    X s t u v hst htu huv H K hH hK
    A B R hA0 hB0 hR0 hHb hKb φ ψ hφ hψ hφb hψInt hψMean
  change (∫ ω, (f ω + g ω)^2 ∂P) =
    (∫ ω, (f ω)^2 ∂P) + (∫ ω, (g ω)^2 ∂P)
  calc
    _ = ∫ ω, (f ω)^2 + (g ω)^2 + 2 * (f ω * g ω) ∂P := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun ω => by ring)
    _ = (∫ ω, (f ω)^2 + (g ω)^2 ∂P) +
        (∫ ω, 2 * (f ω * g ω) ∂P) :=
          integral_add (hfsq.add hgsq) (hcross.const_mul 2)
    _ = (∫ ω, (f ω)^2 ∂P) + (∫ ω, (g ω)^2 ∂P) +
        2 * (∫ ω, f ω * g ω ∂P) := by
      rw [integral_add hfsq hgsq, integral_const_mul]
    _ = _ := by
      have hz' : (∫ ω, f ω * g ω ∂P) = 0 := by
        simpa only [f, g] using hz
      simp [hz']
