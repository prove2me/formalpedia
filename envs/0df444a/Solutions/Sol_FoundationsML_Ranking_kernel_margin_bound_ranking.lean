-- Prove2me | solution 1 for FoundationsML.Ranking.kernel_margin_bound_ranking
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T18:35:06.909503+00:00
-- url     : https://prove2.me/submissions/fb785714-5f30-47c1-a1c5-b2430b339125

import Mathlib
import Definitions.Def_FoundationsML_Ranking_GeneralizationError
import Definitions.Def_FoundationsML_Ranking_EmpiricalMarginLoss
import Definitions.Def_FoundationsML_Ranking_IsPDS
import Definitions.Def_FoundationsML_Ranking_LinearKernelHypothesisClass

open MeasureTheory FoundationsML.Ranking in
theorem cex_set_empty_8bbe :
    {S : Fin 0 → Unit × Unit | ∀ h ∈ LinearKernelHypothesisClass (fun _ : Unit => (0:ℝ)) 0,
        GeneralizationError (Measure.dirac ((),())) (fun _ => (1:ℝ)) h ≤
          EmpiricalMarginLoss 1 (fun i => (S i).1) (fun i => (S i).2)
            (fun i => (fun _ => (1:ℝ)) (S i)) h +
            4 * Real.sqrt ((0:ℝ) ^ 2 * (0:ℝ) ^ 2 / (1:ℝ) ^ 2 / ((0:ℕ):ℝ)) +
            Real.sqrt (Real.log (1 / (1/2:ℝ)) / (2 * ((0:ℕ):ℝ)))} = ∅ := by
  ext S
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_forall]
  refine ⟨fun _ => 0, ⟨0, by simp, by funext x; simp⟩, ?_⟩
  simp [GeneralizationError, EmpiricalMarginLoss]

open MeasureTheory FoundationsML.Ranking in
theorem solution : ¬ (∀ {X Hb : Type} [MeasurableSpace X] (D : Measure (X × X)) [IsProbabilityMeasure D]
    [NormedAddCommGroup Hb] [InnerProductSpace ℝ Hb]
    (K : X → X → ℝ) (Φ : X → Hb) (hK : IsPDS K) (hΦ : ∀ x y, K x y = (inner (𝕜 := ℝ) (Φ x) (Φ y) : ℝ))
    (r : ℝ) (hr : 0 ≤ r) (hrK : ∀ x, K x x ≤ r)
    (Λ : ℝ) (hΛ : 0 ≤ Λ) (f : X × X → ℝ) (hf : ∀ p, f p = 1 ∨ f p = -1)
    (ρ : ℝ) (hρ : 0 < ρ) (m : ℕ) (δ : ℝ) (hδ : 0 < δ),
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X × X | ∀ h ∈ LinearKernelHypothesisClass Φ Λ,
        GeneralizationError D f h ≤
          EmpiricalMarginLoss ρ (fun i => (S i).1) (fun i => (S i).2) (fun i => f (S i)) h +
            4 * Real.sqrt (r ^ 2 * Λ ^ 2 / ρ ^ 2 / m) +
            Real.sqrt (Real.log (1 / δ) / (2 * m))}).toReal) := by
  intro H
  have h := @H Unit ℝ _ (Measure.dirac ((),())) _ _ _ (fun _ _ => 0) (fun _ => 0)
    ⟨fun _ _ => rfl, fun n x c => by simp⟩ (fun x y => by simp)
    0 le_rfl (fun _ => le_rfl) 0 le_rfl (fun _ => 1) (fun _ => Or.inl rfl)
    1 one_pos 0 (1/2) (by norm_num)
  rw [cex_set_empty_8bbe] at h
  simp at h
  norm_num at h
