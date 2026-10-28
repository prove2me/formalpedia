-- Prove2me | solution 1 for FunctionalInequalities.Poincare.SmoothTest.constant_eq_lipschitz_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:42:05.486603+00:00
-- url     : https://prove2.me/submissions/c97cb32e-f831-45d4-b996-ce76c969a992

import Definitions.Def_KLSModular_FunctionalInequalities_Poincare_SmoothTest_Optimal
import Definitions.Def_KLSModular_FunctionalInequalities_Poincare_L2_Energy
import Definitions.Def_KLSModular_FunctionalInequalities_Poincare_SmoothTest_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Poincare_LipschitzGradient_Comparison
import Theorems.Thm_FunctionalInequalities_Energy_LipschitzGradient_holds_ofPreEnergy_of_localSlope_readable
import Theorems.Thm_FunctionalInequalities_Energy_LipschitzGradient_localSlope_holds_of_relaxation_readable
import Theorems.Thm_FunctionalInequalities_Poincare_SmoothTest_holds_iff_localSlope_readable
import Theorems.Thm_FunctionalInequalities_Poincare_TestFamily_holds_ofPreEnergy_iff_readable

section
noncomputable section
section
universe u
section
/-- The extended Rayleigh quotient is bounded by a finite `C` exactly when the defining
inequality holds. This includes zero-energy tests, whose quotient may be infinite. -/
theorem FunctionalInequalities.Poincare.TestFamily.rayleigh_le_iff (F : TestFamily) (f : F.Test) (C : NNReal) :
    rayleigh F f ≤ (C : ENNReal) ↔ F.variance f ≤ C * F.energy f := by
  rw [rayleigh, ENNReal.div_le_iff_le_mul
    (Or.inr ENNReal.coe_ne_top) (Or.inl ENNReal.coe_ne_top), ← ENNReal.coe_mul,
    ENNReal.coe_le_coe]
/-- A finite constant is valid exactly when it bounds the optimal extended constant. -/
theorem FunctionalInequalities.Poincare.TestFamily.holds_iff_constant_le (F : TestFamily) (C : NNReal) :
    Holds F C ↔ constant F ≤ (C : ENNReal) := by
  rw [constant, iSup_le_iff]
  exact forall_congr' fun f ↦ (rayleigh_le_iff F f C).symm
end
end
end
end

section
noncomputable section
open MeasureTheory
section
universe u
variable {α : Type u} [MeasurableSpace α]
section
/-- A finite `L²` Poincaré constant is valid exactly when it bounds the optimal one. -/
theorem FunctionalInequalities.Poincare.L2Energy.holds_iff_constant_le (μ : ProbabilityMeasure α)
    (energy : Energy.Functional (Lp ℝ 2 (μ : Measure α))) (C : NNReal) :
    Holds μ energy C ↔ constant μ energy ≤ (C : ENNReal) := by
  simpa [Holds, constant] using
    TestFamily.holds_iff_constant_le (TestFamily.ofL2Energy μ energy) C
end
end
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ContDiff
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]
  [MeasurableSpace E]
/-- Source: local order consequence of `constant` and Mathlib's `iInf_le_of_le`.
Every finite valid constant bounds the optimal constant from above. -/
theorem FunctionalInequalities.Poincare.SmoothTest.constant_le {μ : Measure E} {C : NNReal}
    (hC : Holds μ (C : ℝ)) :
    constant μ ≤ (C : ENNReal) := by
  exact iInf_le_of_le ⟨C, hC⟩ le_rfl
/-- Source: local order consequence of `constant` and Mathlib's `le_iInf`.
A lower bound for every finite valid constant bounds the optimal constant from below. -/
theorem FunctionalInequalities.Poincare.SmoothTest.le_constant {μ : Measure E} {L : ENNReal}
    (hL : ∀ C : NNReal, Holds μ (C : ℝ) → L ≤ (C : ENNReal)) :
    L ≤ constant μ := by
  refine le_iInf fun C ↦ ?_
  exact hL C.1 C.2
end
end
end

noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff
open FunctionalInequalities.Energy.Euclidean
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
variable (ν : MeasureTheory.ProbabilityMeasure V) (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure]
section Bridge
section
/-- A finite constant is valid for the Lipschitz gradient relaxation exactly when it is a literature
constant. -/
theorem FunctionalInequalities.Poincare.LipschitzGradient.holds_iff_localSlope
    (hac : (ν : Measure V) ≪ m) (hfr : (ν : Measure V) (frontier (ν : Measure V).support) = 0)
    (C : NNReal) :
    Poincare.L2Energy.Holds ν (Energy.LipschitzGradient.relaxation ν m hac) C ↔ Poincare.LocalSlope.Holds ν C :=
  ⟨Energy.LipschitzGradient.localSlope_holds_of_relaxation_readable ν m hac hfr, fun h ↦
    (Poincare.TestFamily.holds_ofPreEnergy_iff_readable ν _ C).mp
      (Energy.LipschitzGradient.holds_ofPreEnergy_of_localSlope_readable ν m hac hfr h)⟩
end
/-- The smooth-test constant equals the optimal constant of the Lipschitz gradient
relaxation. -/
theorem solution
    (hac : (ν : Measure V) ≪ m) (hfr : (ν : Measure V) (frontier (ν : Measure V).support) = 0) :
    FunctionalInequalities.Poincare.SmoothTest.constant (ν : Measure V) =
      FunctionalInequalities.Poincare.L2Energy.constant ν (FunctionalInequalities.Energy.LipschitzGradient.relaxation ν m hac) := by
  apply le_antisymm
  · by_cases htop : FunctionalInequalities.Poincare.L2Energy.constant ν (FunctionalInequalities.Energy.LipschitzGradient.relaxation ν m hac) = ⊤
    · rw [htop]
      exact le_top
    · set C := (FunctionalInequalities.Poincare.L2Energy.constant ν (FunctionalInequalities.Energy.LipschitzGradient.relaxation ν m hac)).toNNReal
      have hC : FunctionalInequalities.Poincare.L2Energy.Holds ν (FunctionalInequalities.Energy.LipschitzGradient.relaxation ν m hac) C :=
        (FunctionalInequalities.Poincare.L2Energy.holds_iff_constant_le _ _ _).mpr (by rw [ENNReal.coe_toNNReal htop])
      have hlit := (FunctionalInequalities.Poincare.LipschitzGradient.holds_iff_localSlope
        ν m hac hfr C).mp hC
      have hlegacy := (FunctionalInequalities.Poincare.SmoothTest.holds_iff_localSlope_readable ν m hac C).mpr hlit
      rw [← ENNReal.coe_toNNReal htop]
      exact FunctionalInequalities.Poincare.SmoothTest.constant_le hlegacy
  · apply FunctionalInequalities.Poincare.SmoothTest.le_constant
    intro C hC
    have hlit := (FunctionalInequalities.Poincare.SmoothTest.holds_iff_localSlope_readable ν m hac C).mp hC
    exact (FunctionalInequalities.Poincare.L2Energy.holds_iff_constant_le _ _ _).mp
      ((FunctionalInequalities.Poincare.LipschitzGradient.holds_iff_localSlope ν m hac hfr C).mpr hlit)
