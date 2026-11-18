-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_original_finitecap_fullcell_Hessian_cross_signed_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T16:25:36.327141+00:00
-- url     : https://prove2.me/submissions/60f4e0b2-ad9f-4d50-bf61-90b4735d266a

import Theorems.Thm_AvramDividend_Classical_avram_ga_original_finitecap_true_fullcell_Hessian_coeff_measurable_bounded
import Theorems.Thm_AvramDividend_Classical_avram_ga_original_true_fullcell_raw_centered_square_diff_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ga_original_finitecap_fullcell_Hessian_cross_integrable
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hν : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hFiniteCap : C ≠ ⊤)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (δ : ℝ) (hδ : 0 < δ)
    (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω →
      δ ≤ riskProcess X x D t ω) (j : ℕ) :
    let B : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      (Finset.range m).sum (fun i =>
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        let R : ℝ := X.X (s + Δ) ω - X.X s ω
        let Z : ℝ := R - (Δ : ℝ) * X.c
        let b : ℝ := C.toReal *
          (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
        if s < ρ ω ∧ s + Δ ≤ ρ ω then
          Real.exp (-(q * (s : ℝ))) *
            (if x + X.X s ω - rightLimit D s ω ≤ b
             then iteratedDeriv 2 w
                (x + X.X s ω - rightLimit D s ω) else 0) / 2 *
                  (R ^ 2 - Z ^ 2)
        else 0)
    ∀ m, Integrable (B m) P := by
  classical
  intro B m
  let H : ℕ → ℕ → Ω → ℝ := fun m i ω =>
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℝ≥0 := (i : ℝ≥0) * Δ
    let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
    let Y : ℝ := x + X.X s ω - rightLimit D s ω
    if s < ρ ω ∧ s + Δ ≤ ρ ω then
      Real.exp (-(q * (s : ℝ))) *
        (if Y ≤ b then iteratedDeriv 2 w Y else 0)
    else 0
  let R : ℕ → ℕ → Ω → ℝ := fun m i ω =>
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℝ≥0 := (i : ℝ≥0) * Δ
    let V : ℝ := X.X (s + Δ) ω - X.X s ω
    let Z : ℝ := V - (Δ : ℝ) * X.c
    if s < ρ ω ∧ s + Δ ≤ ρ ω then V ^ 2 - Z ^ 2 else 0
  obtain ⟨K, hK, hCoeff⟩ :=
    avram_ga_original_finitecap_true_fullcell_Hessian_coeff_measurable_bounded
      X hX q hq w C hC hFiniteCap hw x D hD n hn ρ hρstop δ hδ hFloor j
  have hRmeas (i : ℕ) : AEStronglyMeasurable (R m i) P :=
    (avram_ga_original_true_fullcell_raw_centered_square_diff_measurable
      X n ρ hρstop m i).aestronglyMeasurable
  have hSum (S : Finset ℕ) :
      AEStronglyMeasurable (fun ω => ∑ i ∈ S, H m i ω / 2 * R m i ω) P := by
    induction S using Finset.induction_on with
    | empty => simpa using (aestronglyMeasurable_const :
        AEStronglyMeasurable (fun _ : Ω => (0 : ℝ)) P)
    | @insert i S hi ih =>
        have hTerm : AEStronglyMeasurable (fun ω => H m i ω / 2 * R m i ω) P :=
          (((hCoeff m i).1.div_const 2).aestronglyMeasurable).mul (hRmeas i)
        have hEqSum : (fun ω => ∑ x ∈ insert i S, H m x ω / 2 * R m x ω) =
            (fun ω => H m i ω / 2 * R m i ω + ∑ x ∈ S, H m x ω / 2 * R m x ω) := by
          funext ω
          simp only [Finset.sum_insert hi]
        rw [hEqSum]
        exact hTerm.add ih
  have hEq (ω : Ω) : B m ω = ∑ i ∈ Finset.range m, H m i ω / 2 * R m i ω := by
    simp only [B, H, R]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> ring
  have hMeas : AEStronglyMeasurable (B m) P := by
    have hFun : B m =
        (fun ω => ∑ i ∈ Finset.range m, H m i ω / 2 * R m i ω) :=
      funext hEq
    rw [hFun]
    exact hSum (Finset.range m)
  apply (integrable_norm_iff hMeas).mp
  simpa only [Real.norm_eq_abs] using
    (avram_ga_original_finitecap_fullcell_Hessian_cross_integrable
      X hX hν q hq w C hC hFiniteCap hw x D hD n hn
      ρ hρstop δ hδ hFloor j m)
