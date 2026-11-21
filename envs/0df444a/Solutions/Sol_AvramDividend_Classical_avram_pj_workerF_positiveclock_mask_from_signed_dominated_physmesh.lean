-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerF_positiveclock_mask_from_signed_dominated_physmesh
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T21:49:13.000722+00:00
-- url     : https://prove2.me/submissions/85ee0f07-12a5-46c6-a218-ea86be1e6710

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_signed_spatial_K_mask_preserves_L1
import Theorems.Thm_AvramDividend_Classical_avram_pj_true_physical_positive_ito_excess_dominated_ae_vanish_implies_L1
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (ρ : Ω → ℝ≥0) (hρz : MeasurableSet {ω : Ω | ρ ω = 0})
    (V U : Ω → ℝ) (Q : ℕ → Ω → ℝ) (ε : ℝ)
    (K : Ω → ℝ) (hKI : Integrable K P)
    (hKsmall : (∫ ω, |K ω| ∂P) ≤ ε / 4)
    (hEI : ∀ k, Integrable
      (fun ω => V ω - U ω - K ω - Q k ω) P)
    (F : Ω → ℝ) (hFI : Integrable F P)
    (hDom : ∀ k, ∀ᵐ ω ∂P,
      |V ω - U ω - K ω - Q k ω| ≤ F ω)
    (hAE : ∀ᵐ ω ∂P, Tendsto
      (fun k => V ω - U ω - K ω - Q k ω)
      Filter.atTop (nhds (0 : ℝ))) :
    ∃ K' : Ω → ℝ,
      Integrable K' P ∧ (∫ ω, |K' ω| ∂P) ≤ ε / 4 ∧
      (∀ ω, ρ ω = 0 → K' ω = 0) ∧
      (∀ k, Integrable (fun ω =>
        if ρ ω = 0 then (0 : ℝ)
        else max (0 : ℝ) (V ω - U ω - K' ω - Q k ω)) P) ∧
      Tendsto (fun k =>
        ∫ ω, |if ρ ω = 0 then (0 : ℝ)
          else max (0 : ℝ) (V ω - U ω - K' ω - Q k ω)| ∂P)
        Filter.atTop (nhds (0 : ℝ)) := by
  have hs : MeasurableSet {ω : Ω | ρ ω ≠ 0} := by
    change MeasurableSet ({ω : Ω | ρ ω = 0}ᶜ)
    exact hρz.compl
  obtain ⟨K', hKI', hKsmall', hKzero, hKsame⟩ :=
    avram_pj_workerC_signed_spatial_K_mask_preserves_L1
      {ω : Ω | ρ ω ≠ 0} hs K hKI (ε / 4) hKsmall
  let Pos : ℕ → Ω → ℝ := fun k =>
    ({ω : Ω | ρ ω ≠ 0}).indicator
      (fun ω => max (0 : ℝ) (V ω - U ω - K ω - Q k ω))
  have hPI : ∀ k, Integrable (Pos k) P := by
    intro k
    exact ((integrable_zero Ω ℝ P).sup (hEI k)).indicator hs
  have hAbs : ∀ k ω, |Pos k ω| ≤
      |V ω - U ω - K ω - Q k ω| := by
    intro k ω
    by_cases hz : ρ ω = 0
    · simp [Pos, Set.indicator, hz]
    · rw [show Pos k ω = max (0 : ℝ)
        (V ω - U ω - K ω - Q k ω) from by
          simp [Pos, Set.indicator, hz],
        abs_of_nonneg (le_max_left (0 : ℝ) _)]
      exact max_le (abs_nonneg _) (le_abs_self _)
  have hPdom : ∀ k, ∀ᵐ ω ∂P, |Pos k ω| ≤ F ω := by
    intro k
    filter_upwards [hDom k] with ω hw
    exact (hAbs k ω).trans hw
  have hPAE : ∀ᵐ ω ∂P,
      Tendsto (fun k => Pos k ω) atTop (nhds (0 : ℝ)) := by
    filter_upwards [hAE] with ω hlim
    by_cases hz : ρ ω = 0
    · simpa [Pos, Set.indicator, hz] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ))
          atTop (nhds (0 : ℝ)))
    · have hconst : Tendsto (fun _ : ℕ => (0 : ℝ))
          atTop (nhds (0 : ℝ)) := tendsto_const_nhds
      have hm := hconst.max hlim
      simpa [Pos, Set.indicator, hz] using hm
  have hPL1 :=
    avram_pj_true_physical_positive_ito_excess_dominated_ae_vanish_implies_L1
      P Pos hPI F hFI hPdom hPAE
  have hEq (k : ℕ) :
      (fun ω => if ρ ω = 0 then (0 : ℝ)
        else max (0 : ℝ) (V ω - U ω - K' ω - Q k ω)) = Pos k := by
    funext ω
    by_cases hz : ρ ω = 0
    · simp [Pos, Set.indicator, hz]
    · simp [Pos, Set.indicator, hz, hKsame ω hz]
  refine ⟨K', hKI', hKsmall', ?_, ?_, ?_⟩
  · intro ω hz
    exact hKzero ω (by simpa using hz)
  · intro k
    rw [hEq k]
    exact hPI k
  · have hFun : (fun k => ∫ ω, |if ρ ω = 0 then (0 : ℝ)
          else max (0 : ℝ) (V ω - U ω - K' ω - Q k ω)| ∂P) =
        (fun k => ∫ ω, |Pos k ω| ∂P) := by
        funext k
        exact integral_congr_ae (Filter.Eventually.of_forall
          (fun ω => congrArg abs (congrFun (hEq k) ω)))
    rw [hFun]
    exact hPL1
