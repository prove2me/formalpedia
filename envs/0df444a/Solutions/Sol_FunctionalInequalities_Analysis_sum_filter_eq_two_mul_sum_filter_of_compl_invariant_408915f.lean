-- Prove2me | solution 1 for FunctionalInequalities.Analysis.sum_filter_eq_two_mul_sum_filter_of_compl_invariant_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:47:48.346079+00:00
-- url     : https://prove2.me/submissions/a7930c36-ef8f-4f6d-8e6e-65e61a860e89

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_IteratedDerivative_Bilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_IteratedDerivative_Symmetry
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Data.List.FinRange

noncomputable section
open scoped ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- Complement pairing of Boolean masks: if a predicate and a real summand are invariant under complementing the mask, the
filtered sum is twice the sum over the masks selecting a fixed slot `i₀` (BKL (74): pairs `J`, `Jᶜ`, representative containing
slot `i₀`). -/
theorem solution {m : ℕ} (P : (Fin m → Bool) → Prop)
    [DecidablePred P] (hP : ∀ q, P (fun i => !(q i)) ↔ P q) (f : (Fin m → Bool) → ℝ)
    (hf : ∀ q, f (fun i => !(q i)) = f q) (i₀ : Fin m) :
    ∑ q ∈ Finset.univ.filter P, f q = 2 * ∑ q ∈ Finset.univ.filter (fun q => q i₀ = true ∧ P q), f q := by
    let c : (Fin m → Bool) → (Fin m → Bool) := fun q i => !(q i)
    have hcc (q : Fin m → Bool) : c (c q) = q := by
      funext i
      simp [c]
    have hsum :
        (∑ q ∈ Finset.univ.filter (fun q => q i₀ = false ∧ P q), f q) =
          ∑ q ∈ Finset.univ.filter (fun q => q i₀ = true ∧ P q), f q := by
      refine Finset.sum_bij (fun q _ => c q) ?_ ?_ ?_ ?_
      · intro q hq
        have hq' := Finset.mem_filter.mp hq
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        refine ⟨?_, ?_⟩
        · simpa [c] using hq'.2.1
        · simpa [c] using (hP q).mpr hq'.2.2
      · intro q₁ hq₁ q₂ hq₂ h
        calc
          q₁ = c (c q₁) := (hcc q₁).symm
          _ = c (c q₂) := congrArg c h
          _ = q₂ := hcc q₂
      · intro q hq
        have hq' := Finset.mem_filter.mp hq
        refine ⟨c q, ?_, hcc q⟩
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        refine ⟨?_, ?_⟩
        · simpa [c] using hq'.2.1
        · simpa [c] using (hP q).mpr hq'.2.2
      · intro q hq
        simpa [c] using (hf q).symm
    have hsplit :
        (∑ q ∈ Finset.univ.filter P, f q) =
          (∑ q ∈ Finset.univ.filter (fun q => q i₀ = true ∧ P q), f q) +
            ∑ q ∈ Finset.univ.filter (fun q => q i₀ = false ∧ P q), f q := by
      simpa [Finset.filter_filter, and_comm, and_left_comm, and_assoc] using
        (Finset.sum_filter_add_sum_filter_not
          (s := Finset.univ.filter P) (p := fun q => q i₀ = true) (f := f)).symm
    calc
      (∑ q ∈ Finset.univ.filter P, f q) =
          (∑ q ∈ Finset.univ.filter (fun q => q i₀ = true ∧ P q), f q) +
            ∑ q ∈ Finset.univ.filter (fun q => q i₀ = false ∧ P q), f q := hsplit
      _ = 2 * ∑ q ∈ Finset.univ.filter (fun q => q i₀ = true ∧ P q), f q := by
        rw [hsum]
        ring
