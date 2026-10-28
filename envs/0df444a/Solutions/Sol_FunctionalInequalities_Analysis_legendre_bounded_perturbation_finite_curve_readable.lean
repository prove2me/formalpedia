-- Prove2me | solution 1 for FunctionalInequalities.Analysis.legendre_bounded_perturbation_finite_curve_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:38:15.538023+00:00
-- url     : https://prove2.me/submissions/2cb0ba5f-497e-465f-935a-90b489babae1

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_LegendreVariation_Perturbation
import Theorems.Thm_FunctionalInequalities_Analysis_legendre_bounded_perturbation_readable

section
noncomputable section
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- One finite value excludes `-∞` for the entire Legendre transform. -/
theorem FunctionalInequalities.Analysis.legendre_ne_bot (φ : E → EReal) (hφ : ProperPotential φ) (y : E) :
    legendre φ y ≠ ⊥ := by
  obtain ⟨x, hx⟩ := hφ.2
  have hb := hφ.1 x
  lift φ x to ℝ using ⟨hx, hb⟩ with r hr
  have hle : ((inner ℝ x y - r : ℝ) : EReal) ≤ legendre φ y := by
    change ((inner ℝ x y - r : ℝ) : EReal) ≤
      ⨆ z : E, (inner ℝ z y : EReal) - φ z
    simpa only [← hr, EReal.coe_sub] using
      (le_iSup (fun z : E => (inner ℝ z y : EReal) - φ z) x)
  exact ne_of_gt ((EReal.bot_lt_coe _).trans_le hle)
end
end
end

noncomputable section
section FiniteCurve
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set
/-- A bounded real perturbation produces a finite real Legendre curve and its
real values remain within the actual uniform shift bound. -/
theorem solution
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (φ : E → EReal) (hφ : FunctionalInequalities.Analysis.ProperPotential φ) (y : E)
    (hy : FunctionalInequalities.Analysis.legendre φ y ≠ ⊤)
    (b : E → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ z : E, |b z| ≤ M) :
    ∀ t : ℝ,
      let ψ := FunctionalInequalities.Analysis.legendre (fun z : E => φ z + ((t * b z : ℝ) : EReal)) y
      ψ ≠ ⊤ ∧ ψ ≠ ⊥ ∧
        |ψ.toReal - (FunctionalInequalities.Analysis.legendre φ y).toReal| ≤ |t| * M := by
    intro t
    let c : ℝ := |t| * M
    let A : EReal := FunctionalInequalities.Analysis.legendre φ y
    let P : EReal :=
      FunctionalInequalities.Analysis.legendre (fun z : E => φ z + ((t * b z : ℝ) : EReal)) y
    change P ≠ ⊤ ∧ P ≠ ⊥ ∧ |P.toReal - A.toReal| ≤ c
    have hAbot : A ≠ ⊥ := FunctionalInequalities.Analysis.legendre_ne_bot φ hφ y
    have hAcoe : (A.toReal : EReal) = A :=
      EReal.coe_toReal hy hAbot
    have hsandwich :=
      FunctionalInequalities.Analysis.legendre_bounded_perturbation_readable φ hφ b M hM hb t y
    have hlower : A - (c : EReal) ≤ P := by
      simpa [A, P, c] using hsandwich.1
    have hupper : P ≤ A + (c : EReal) := by
      simpa [A, P, c] using hsandwich.2
    have hlower' : ((A.toReal - c : ℝ) : EReal) ≤ P := by
      calc
        ((A.toReal - c : ℝ) : EReal) = A - (c : EReal) := by
          rw [EReal.coe_sub, hAcoe]
        _ ≤ P := hlower
    have hupper' : P ≤ ((A.toReal + c : ℝ) : EReal) := by
      calc
        P ≤ A + (c : EReal) := hupper
        _ = ((A.toReal + c : ℝ) : EReal) := by
          exact (congrArg (fun q : EReal => q + (c : EReal)) hAcoe).symm.trans
            (EReal.coe_add _ _).symm
    have hPtop : P ≠ ⊤ := by
      intro hP
      rw [hP] at hupper'
      exact (not_le_of_gt (EReal.coe_lt_top _)) hupper'
    have hPbot : P ≠ ⊥ := by
      intro hP
      rw [hP] at hlower'
      exact (not_le_of_gt (EReal.bot_lt_coe _)) hlower'
    have hlowerReal :
        A.toReal - c ≤ P.toReal := by
      have h :=
        EReal.toReal_le_toReal hlower'
          (EReal.coe_ne_bot _) hPtop
      simpa only [EReal.toReal_coe] using h
    have hupperReal :
        P.toReal ≤ A.toReal + c := by
      have h :=
        EReal.toReal_le_toReal hupper'
          hPbot (EReal.coe_ne_top _)
      simpa only [EReal.toReal_coe] using h
    refine ⟨hPtop, hPbot, ?_⟩
    rw [abs_le]
    constructor <;> linarith
