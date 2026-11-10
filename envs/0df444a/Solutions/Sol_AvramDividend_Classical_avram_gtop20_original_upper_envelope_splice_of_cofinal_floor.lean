-- Prove2me | solution 1 for AvramDividend.Classical.avram_gtop20_original_upper_envelope_splice_of_cofinal_floor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T02:42:10.755467+00:00
-- url     : https://prove2.me/submissions/a0e6be4b-3024-4049-ba15-d603358313ea

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_truncated_clock_nnreal_bounds
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_original_uniform_prefix_upcross_reserve_envelope
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_path_nonneg
import Theorems.Thm_AvramDividend_Classical_avram_gtop21_nnreal_min_max_stopping
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hSigmaNonzero : X.σ ≠ 0)
    (hNuZero : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont (fun ω => (σ ω : WithTop ℝ≥0)))
    (hσle : ∀ ω, σ ω ≤ τ ω)
    (L : ℕ → Ω → ℝ≥0)
    (hLstop : ∀ j, IsStoppingTime 𝓕.rightCont (fun ω => (L j ω : WithTop ℝ≥0)))
    (hLle : ∀ j ω, L j ω ≤ σ ω)
    (hLmono : ∀ ω, Monotone (fun j : ℕ => L j ω))
    (hLlim : ∀ᵐ ω ∂P, Tendsto (fun j => L j ω) atTop (nhds (σ ω)))
    (hLfloor : ∀ j, ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < L j ω → (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω) :
    ∃ ρ : ℕ → Ω → ℝ≥0,
      (∀ j, IsStoppingTime 𝓕.rightCont (fun ω => (ρ j ω : WithTop ℝ≥0))) ∧
      (∀ j ω, ρ j ω ≤ σ ω) ∧
      (∀ ω, Monotone (fun j : ℕ => ρ j ω)) ∧
      (∀ᵐ ω ∂P, Tendsto (fun j => ρ j ω) atTop (nhds (σ ω))) ∧
      (∀ j, ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ j ω →
        (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
        riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) := by
  classical
  have hDstrat : IsDividendStrategy 𝓕 D := hD.1.1
  have hτbound : ∀ ω, τ ω ≤ (n : ℝ≥0) := fun ω => by
    rw [hτeq ω]; exact (avram_wave7_08_source_truncated_clock_nnreal_bounds X x D n).2.1 ω
  have hσbound : ∀ ω, σ ω ≤ (n : ℝ≥0) := fun ω => (hσle ω).trans (hτbound ω)
  obtain ⟨η, hηstop, hηle, hηbounds, hηevent⟩ :=
    avram_ubv_top9_original_uniform_prefix_upcross_reserve_envelope
      X x D hDstrat (n : ℝ≥0) σ hσstop hσbound
  let ρ : ℕ → Ω → ℝ≥0 := fun j =>
    Nat.rec (fun ω => min (L 0 ω) (η 0 ω)) (fun k prev ω => max (prev ω) (min (L (k + 1) ω) (η (k + 1) ω))) j
  have h0 (ω : Ω) : ρ 0 ω = min (L 0 ω) (η 0 ω) := rfl
  have hs (j : ℕ) (ω : Ω) : ρ (j + 1) ω = max (ρ j ω) (min (L (j + 1) ω) (η (j + 1) ω)) := rfl
  have hMinCast (a b : ℝ≥0) : (some (min a b) : WithTop ℝ≥0) = min (some a) (some b) := by rfl
  have hMaxCast (a b : ℝ≥0) : (some (max a b) : WithTop ℝ≥0) = max (some a) (some b) := by rfl
  have hStop : ∀ j, IsStoppingTime 𝓕.rightCont (fun ω => (some (ρ j ω) : WithTop ℝ≥0)) := by
    intro j
    induction j with
    | zero =>
        have heq : (fun ω => (some (ρ 0 ω) : WithTop ℝ≥0)) = (fun ω => min (some (L 0 ω)) (some (η 0 ω))) := by
          funext ω; rw [h0, hMinCast]
        rw [heq]
        exact (avram_gtop21_nnreal_min_max_stopping 𝓕 (L 0) (η 0) (hLstop 0) (hηstop 0)).1
    | succ j ih =>
        have heq : (fun ω => (some (ρ (j + 1) ω) : WithTop ℝ≥0)) = (fun ω => max (some (ρ j ω)) (some (min (L (j + 1) ω) (η (j + 1) ω)))) := by
          funext ω; rw [hs, hMaxCast]
        rw [heq]
        exact (avram_gtop21_nnreal_min_max_stopping 𝓕 (ρ j)
          (fun ω => min (L (j + 1) ω) (η (j + 1) ω)) ih
          (avram_gtop21_nnreal_min_max_stopping 𝓕 (L (j + 1)) (η (j + 1))
            (hLstop (j + 1)) (hηstop (j + 1))).1).2
  have hLe : ∀ j ω, ρ j ω ≤ σ ω := by
    intro j
    induction j with
    | zero =>
        intro ω; rw [h0]; exact (min_le_left _ _).trans (hLle 0 ω)
    | succ j ih =>
        intro ω; rw [hs]; exact max_le (ih ω) ((min_le_left _ _).trans (hLle (j + 1) ω))
  have hMon : ∀ ω, Monotone (fun j : ℕ => ρ j ω) := by
    intro ω; apply monotone_nat_of_le_succ
    intro j; rw [hs]; exact le_max_left _ _
  have hMinLe : ∀ j ω, min (L j ω) (η j ω) ≤ ρ j ω := by
    intro j ω; cases j with
    | zero => rw [h0]
    | succ j => rw [hs]; exact le_max_right _ _
  have hLimit : ∀ᵐ ω ∂P, Tendsto (fun j => ρ j ω) atTop (nhds (σ ω)) := by
    filter_upwards [hLlim] with ω hlim
    have heq : (fun j => min (L j ω) (η j ω)) =ᶠ[atTop] (fun j => L j ω) := by
      filter_upwards [hηevent ω] with j hj; simp only [hj, min_eq_left (hLle j ω)]
    have hmin : Tendsto (fun j => min (L j ω) (η j ω)) atTop (nhds (σ ω)) := hlim.congr' heq.symm
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hmin
      tendsto_const_nhds (fun j => hMinLe j ω) (fun j => hLe j ω)
  have hBand : ∀ j, ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ j ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧ riskProcess X x D t ω ≤ x + ((j : ℝ) + 1) := by
    intro j
    induction j with
    | zero =>
        filter_upwards [hLfloor 0] with ω hl t ht0 ht
        rw [h0] at ht
        have htL : t < L 0 ω := lt_of_lt_of_le ht (min_le_left _ _)
        have htU : t < η 0 ω := lt_of_lt_of_le ht (min_le_right _ _)
        have hX := (hηbounds 0 ω t (le_of_lt htU)).1
        have hDiv := dividendStrategy_path_nonneg D hDstrat ω t
        constructor
        · simpa using hl t ht0 htL
        · unfold riskProcess; linarith
    | succ j ih =>
        filter_upwards [ih, hLfloor (j + 1)] with ω hprev hl t ht0 ht
        rw [hs] at ht
        have hδ : (1 : ℝ) / (((j + 1 : ℕ) : ℝ) + 1) ≤ (1 : ℝ) / ((j : ℝ) + 1) := by
          apply one_div_le_one_div_of_le (by positivity) <;> (push_cast; linarith)
        rcases lt_max_iff.mp ht with hOld | hNew
        · obtain ⟨hlo, hhi⟩ := hprev t ht0 hOld
          constructor
          · exact hδ.trans hlo
          · push_cast
            linarith
        · have htL : t < L (j + 1) ω := lt_of_lt_of_le hNew (min_le_left _ _)
          have htU : t < η (j + 1) ω := lt_of_lt_of_le hNew (min_le_right _ _)
          have hX := (hηbounds (j + 1) ω t (le_of_lt htU)).1
          have hDiv := dividendStrategy_path_nonneg D hDstrat ω t
          constructor
          · exact hl t ht0 htL
          · unfold riskProcess
            linarith
  exact ⟨ρ, hStop, hLe, hMon, hLimit, hBand⟩
