-- Prove2me | solution 1 for FoundationsML.MultiClass.margin_bound_kernel_multiclass
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:24:09.413488+00:00
-- url     : https://prove2.me/submissions/fa0c41ee-a307-456c-aea7-aef5bc930440

import Mathlib
import Definitions.Def_FoundationsML_MultiClass_GeneralizationError
import Definitions.Def_FoundationsML_MultiClass_EmpiricalMarginLoss
import Definitions.Def_FoundationsML_MultiClass_IsPDS
import Definitions.Def_FoundationsML_MultiClass_KernelHypothesisClass

open MeasureTheory

namespace FoundationsML.MultiClass

/-- The zero scoring function has margin `0` everywhere. -/
theorem aux_mbk_margin_zero (x : Unit) (y : Fin 2) :
    MarginFunction (fun _ : Unit × Fin 2 => (0 : ℝ)) x y = 0 := by
  simp [MarginFunction, Real.iSup_const_zero]

/-- The zero scoring function misclassifies everything under `D = δ_()`. -/
theorem aux_mbk_generr :
    GeneralizationError (Measure.dirac ()) (fun _ : Unit => (0 : Fin 2))
      (fun _ : Unit × Fin 2 => (0 : ℝ)) = 1 := by
  unfold GeneralizationError
  simp [aux_mbk_margin_zero]

/-- With `m = 0` the empirical margin loss is `0`. -/
theorem aux_mbk_eml (S : Fin 0 → Unit) :
    EmpiricalMarginLoss 1 S (fun _ : Unit => (0 : Fin 2))
      (fun _ : Unit × Fin 2 => (0 : ℝ)) = 0 := by
  simp [EmpiricalMarginLoss]

/-- The zero kernel is PDS. -/
theorem aux_mbk_pds : IsPDS (fun _ _ : Unit => (0 : ℝ)) := by
  refine ⟨fun _ _ => rfl, fun n x c => by simp⟩

/-- The zero scoring function lies in the kernel hypothesis class (take `W = 0`). -/
theorem aux_mbk_mem :
    (fun _ : Unit × Fin 2 => (0 : ℝ)) ∈
      KernelHypothesisClass (fun _ : Unit => (0 : ℝ)) 2 1 1 := by
  refine ⟨fun _ => 0, ?_, ?_⟩
  · simp [GroupNormLp]
  · funext xy
    simp

end FoundationsML.MultiClass

open FoundationsML.MultiClass

theorem solution : ¬ (∀ {X Hb : Type} [MeasurableSpace X] (D : Measure X) [IsProbabilityMeasure D]
    [NormedAddCommGroup Hb] [InnerProductSpace ℝ Hb]
    (K : X → X → ℝ) (Φ : X → Hb) (hK : IsPDS K) (hΦ : ∀ x y, K x y = (inner (𝕜 := ℝ) (Φ x) (Φ y) : ℝ))
    (r : ℝ) (hr : 0 < r) (hrK : ∀ x, K x x ≤ r ^ 2)
    (k : ℕ) (hk2 : 2 ≤ k) (p Λ : ℝ) (hp : 1 ≤ p) (hΛ : 0 < Λ)
    (f : X → Fin k) (m : ℕ) (ρ : ℝ) (hρ : 0 < ρ) (δ : ℝ) (hδ : 0 < δ),
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X | ∀ h ∈ KernelHypothesisClass Φ k p Λ, GeneralizationError D f h ≤
        EmpiricalMarginLoss ρ S f h + 4 * (k : ℝ) * Real.sqrt (r ^ 2 * Λ ^ 2 / ρ ^ 2 / m) +
          Real.sqrt (Real.log (1 / δ) / (2 * m))}).toReal) := by
  intro Hall
  have h := Hall (X := Unit) (Hb := ℝ) (Measure.dirac ()) (fun _ _ => 0) (fun _ => 0)
    aux_mbk_pds (fun _ _ => by simp) 1 one_pos (fun _ => by norm_num) 2 le_rfl 1 1 le_rfl
    one_pos (fun _ => 0) 0 1 one_pos (1 / 2) (by norm_num)
  have hset : {S : Fin 0 → Unit | ∀ h ∈ KernelHypothesisClass (fun _ : Unit => (0 : ℝ)) 2 1 1,
      GeneralizationError (Measure.dirac ()) (fun _ : Unit => (0 : Fin 2)) h ≤
        EmpiricalMarginLoss 1 S (fun _ : Unit => (0 : Fin 2)) h +
          4 * ((2 : ℕ) : ℝ) * Real.sqrt (1 ^ 2 * 1 ^ 2 / 1 ^ 2 / ((0 : ℕ) : ℝ)) +
          Real.sqrt (Real.log (1 / (1 / 2 : ℝ)) / (2 * ((0 : ℕ) : ℝ)))} = ∅ := by
    ext S
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro hS
    have := hS _ aux_mbk_mem
    rw [aux_mbk_generr, aux_mbk_eml] at this
    norm_num at this
  rw [hset] at h
  simp at h
  norm_num at h
