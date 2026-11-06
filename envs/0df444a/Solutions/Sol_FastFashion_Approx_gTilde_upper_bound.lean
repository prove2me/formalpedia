-- Prove2me | solution 1 for FastFashion.Approx.gTilde_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T23:20:18.039444+00:00
-- url     : https://prove2.me/submissions/cb4b7470-588f-455e-a7fa-483e357a6db3

import Mathlib
import Definitions.Def_FastFashion_Structure_Model
import Definitions.Def_FastFashion_Approx_Tangents
import Theorems.Thm_FastFashion_Approx_eq_2_optional_sampling
import Theorems.Thm_FastFashion_Approx_eq_3_min_bound
import Theorems.Thm_FastFashion_Approx_eq_6_tangent_envelope

open MeasureTheory ProbabilityTheory FastFashion.Approx

theorem solution {S Ω : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (lam : S → ℝ) (N : S → ℝ → Ω → ℕ)
    (hN : FastFashion.Structure.IsPoissonFamily lam N P) (hlam : ∀ s, 0 < lam s) (T : ℝ) (hT : 0 < T)
    (Sp : Finset S) (hSp : Sp.Nonempty)
    (Nset : S → Finset (WithTop ℕ)) (hNset : ∀ s, (Nset s).Nonempty) (q : S → ℕ) :
    FastFashion.Structure.expectedSales N P Sp T q ≤ gTilde lam T Sp hSp Nset hNset q := by
  -- each `h^D(q)` is bounded by `sizeMin D`
  have key : ∀ (D : Finset S) (hD : D.Nonempty),
      FastFashion.Structure.hA N P T D q ≤ sizeMin lam T Nset hNset D hD q := by
    intro D hD
    unfold sizeMin
    refine Finset.le_inf' _ _ (fun s hs => ?_)
    have h3 := eq_3_min_bound P lam N hN hlam T hT D hD q
    have h3' : FastFashion.Structure.hA N P T D q ≤ FastFashion.Structure.hA N P T {s} q :=
      h3.trans (Finset.inf'_le _ hs)
    have h6 := (eq_6_tangent_envelope P lam N hN hlam T hT s q).2
    unfold envelope
    refine Finset.le_inf' _ _ (fun i _ => ?_)
    exact h3'.trans (h6 ⟨i, rfl⟩)
  rw [eq_2_optional_sampling P lam N hN hlam T hT Sp q]
  unfold gTilde
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (key Sp hSp)
      (Finset.sum_nonneg (fun s _ => (hlam s).le))
  · exact Finset.sum_le_sum (fun s _ =>
      mul_le_mul_of_nonneg_left (key _ _) (hlam s).le)
