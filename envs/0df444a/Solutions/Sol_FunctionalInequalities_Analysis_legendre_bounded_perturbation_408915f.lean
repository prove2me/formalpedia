-- Prove2me | solution 1 for FunctionalInequalities.Analysis.legendre_bounded_perturbation_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:23:36.005308+00:00
-- url     : https://prove2.me/submissions/b6a786e6-a8e8-4b3d-8464-250fcb9d550c

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section BoundedPerturbation
section InnerProduct
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
private theorem FunctionalInequalities.Analysis.legendre_bounded_perturbation_terms
    (φ : E → EReal) (hφ : ProperPotential φ) (b : E → ℝ)
    (t c : ℝ) (z q : E) (hc : |t * b z| ≤ c) :
    (inner ℝ z q : EReal) - (φ z + ((t * b z : ℝ) : EReal)) ≤
        (inner ℝ z q : EReal) - φ z + (c : EReal) ∧
      (inner ℝ z q : EReal) - φ z ≤
        (inner ℝ z q : EReal) - (φ z + ((t * b z : ℝ) : EReal)) +
          (c : EReal) := by
  have hupper : t * b z ≤ c := (abs_le.mp hc).2
  have hlower : -c ≤ t * b z := (abs_le.mp hc).1
  by_cases ht : φ z = ⊤
  · simp only [ht, EReal.top_add_coe, EReal.sub_top, EReal.bot_add, le_refl, and_self]
  · have hbot : φ z ≠ ⊥ := hφ.1 z
    let r : ℝ := (φ z).toReal
    have hr : (r : EReal) = φ z := EReal.coe_toReal ht hbot
    constructor
    · calc
        (inner ℝ z q : EReal) - (φ z + ((t * b z : ℝ) : EReal)) =
            ((inner ℝ z q - (r + t * b z) : ℝ) : EReal) := by
              rw [← hr, ← EReal.coe_add, ← EReal.coe_sub]

        _ ≤ ((inner ℝ z q - r + c : ℝ) : EReal) := by
              exact EReal.coe_le_coe_iff.mpr (by linarith)
        _ = (inner ℝ z q : EReal) - φ z + (c : EReal) := by
              rw [← hr, ← EReal.coe_sub, ← EReal.coe_add]

    · calc
        (inner ℝ z q : EReal) - φ z =
            ((inner ℝ z q - r : ℝ) : EReal) := by
              rw [← hr, ← EReal.coe_sub]
        _ ≤ ((inner ℝ z q - (r + t * b z) + c : ℝ) : EReal) := by
              exact EReal.coe_le_coe_iff.mpr (by linarith)
        _ = (inner ℝ z q : EReal) -
              (φ z + ((t * b z : ℝ) : EReal)) + (c : EReal) := by
              rw [← hr, ← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_add]
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- An actual uniformly bounded real perturbation shifts the actual entire
Legendre sup by at most |t|M, without primal convexity or global finiteness. -/
theorem solution
    (φ : E → EReal) (hφ : FunctionalInequalities.Analysis.ProperPotential φ)
    (b : E → ℝ) (M : ℝ) (hM : 0 ≤ M) (hb : ∀ z : E, |b z| ≤ M) :
    ∀ (t : ℝ) (q : E),
      FunctionalInequalities.Analysis.legendre φ q - ((|t| * M : ℝ) : EReal) ≤
          FunctionalInequalities.Analysis.legendre (fun z : E => φ z + ((t * b z : ℝ) : EReal)) q ∧
        FunctionalInequalities.Analysis.legendre (fun z : E => φ z + ((t * b z : ℝ) : EReal)) q ≤
          FunctionalInequalities.Analysis.legendre φ q + ((|t| * M : ℝ) : EReal) := by
    intro t q
    let c : ℝ := |t| * M
    have hc : 0 ≤ c := by
      dsimp [c]
      positivity
    have hterm :
        ∀ z : E,
          (inner ℝ z q : EReal) -
                (φ z + ((t * b z : ℝ) : EReal)) ≤
              (inner ℝ z q : EReal) - φ z + (c : EReal) ∧
            (inner ℝ z q : EReal) - φ z ≤
              (inner ℝ z q : EReal) -
                  (φ z + ((t * b z : ℝ) : EReal)) + (c : EReal) := by
      intro z
      apply legendre_bounded_perturbation_terms φ hφ b t c z q ?_
      dsimp [c]
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hb z) (abs_nonneg t)
    constructor
    · apply
        (EReal.sub_le_iff_le_add
          (Or.inl (EReal.coe_ne_bot c))
          (Or.inl (EReal.coe_ne_top c))).2
      apply iSup_le
      intro z
      change (inner ℝ z q : EReal) - φ z ≤
        FunctionalInequalities.Analysis.legendre (fun z : E => φ z + ((t * b z : ℝ) : EReal)) q + (c : EReal)
      exact (hterm z).2 |>.trans <|
        add_le_add (le_iSup (fun w : E =>
          (inner ℝ w q : EReal) -
            (φ w + ((t * b w : ℝ) : EReal))) z) le_rfl
    · change
        FunctionalInequalities.Analysis.legendre (fun z : E => φ z + ((t * b z : ℝ) : EReal)) q ≤
          FunctionalInequalities.Analysis.legendre φ q + (c : EReal)
      apply iSup_le
      intro z
      change (inner ℝ z q : EReal) -
          (φ z + ((t * b z : ℝ) : EReal)) ≤
        FunctionalInequalities.Analysis.legendre φ q + (c : EReal)
      exact (hterm z).1 |>.trans <|
        add_le_add (le_iSup (fun w : E =>
          (inner ℝ w q : EReal) - φ w) z) le_rfl
