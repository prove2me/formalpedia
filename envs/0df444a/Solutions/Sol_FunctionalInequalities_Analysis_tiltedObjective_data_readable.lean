-- Prove2me | solution 1 for FunctionalInequalities.Analysis.tiltedObjective_data_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:33:56.130337+00:00
-- url     : https://prove2.me/submissions/ef3648da-716e-4bf1-a62c-6766caea9f18

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_LegendreVariation_Attainment
import Theorems.Thm_FunctionalInequalities_Analysis_exists_coercive_tilt_of_mem_interior_legendre_domain_readable

noncomputable section
section Attainment
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
/-- The actual tilted objective has the regularity, nondegeneracy, and linear
upper decay data needed by a separate generic upper-semicontinuous attainment
theorem. No maximizer or desired decay is assumed. -/
theorem solution
    (φ : E → EReal) (hφ : FunctionalInequalities.Analysis.ProperPotential φ)
    (hlsc : LowerSemicontinuous φ) (y : E)
    (hy : y ∈ interior {q : E | FunctionalInequalities.Analysis.legendre φ q ≠ ⊤}) :
    let G : E → EReal := fun z => (inner ℝ z y : EReal) - φ z
    UpperSemicontinuous G ∧
      (∀ z, G z ≠ ⊤) ∧
      (∃ z, G z ≠ ⊥) ∧
      ∃ (a b : ℝ), 0 < a ∧ ∀ z,
        G z ≤ ((b - a * ‖z‖ : ℝ) : EReal) := by
    dsimp
    have hc : Continuous (fun z : E => (inner ℝ z y : EReal)) :=
      continuous_coe_real_ereal.comp (continuous_id.inner continuous_const)
    have hneg : UpperSemicontinuous (fun z : E => -φ z) :=
      Continuous.comp_lowerSemicontinuous_antitone
        continuous_neg hlsc EReal.neg_strictAnti.antitone
    have hadd :
        UpperSemicontinuous
          (fun z : E => (inner ℝ z y : EReal) + -φ z) :=
      hc.upperSemicontinuous.add' hneg (by
        intro z
        apply EReal.continuousAt_add
        · left
          exact EReal.coe_ne_top _
        · left
          exact EReal.coe_ne_bot _)
    have hupper : UpperSemicontinuous (fun z : E => (inner ℝ z y : EReal) - φ z) := by
      simpa [sub_eq_add_neg, Function.comp_def] using hadd
    refine ⟨hupper, ?_, ?_, ?_⟩
    · intro z
      change (inner ℝ z y : EReal) + -φ z ≠ ⊤
      apply EReal.add_ne_top (EReal.coe_ne_top _)
      exact fun h => hφ.1 z (EReal.neg_eq_top_iff.mp h)
    · rcases hφ.2 with ⟨z, hz⟩
      refine ⟨z, ?_⟩
      change (inner ℝ z y : EReal) + -φ z ≠ ⊥
      apply EReal.add_ne_bot_iff.mpr
      exact ⟨EReal.coe_ne_bot _, by intro h; exact hz (EReal.neg_eq_bot_iff.mp h)⟩
    · rcases
        FunctionalInequalities.Analysis.exists_coercive_tilt_of_mem_interior_legendre_domain_readable φ hφ y hy with
        ⟨a, b, ha, hab⟩
      refine ⟨a, b, ha, fun z => ?_⟩
      have hn := EReal.neg_le_neg_iff.mpr (hab z)
      calc
        (inner ℝ z y : EReal) - φ z =
            -(φ z - (inner ℝ z y : EReal)) := by
              rw [EReal.neg_sub (Or.inr (EReal.coe_ne_bot _))
                (Or.inr (EReal.coe_ne_top _)), sub_eq_add_neg, add_comm]
        _ ≤ -((a * ‖z‖ - b : ℝ) : EReal) := hn
        _ = ((b - a * ‖z‖ : ℝ) : EReal) := by
          rw [← EReal.coe_neg]
          congr 1
          ring
