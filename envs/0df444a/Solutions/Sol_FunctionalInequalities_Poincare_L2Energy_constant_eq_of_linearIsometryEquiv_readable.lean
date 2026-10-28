-- Prove2me | solution 1 for FunctionalInequalities.Poincare.L2Energy.constant_eq_of_linearIsometryEquiv_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:39:56.819001+00:00
-- url     : https://prove2.me/submissions/f058dc94-e36a-44f1-8320-9779dd06bce0

import Definitions.Def_KLSModular_FunctionalInequalities_Poincare_SmoothTest_Optimal
import Definitions.Def_KLSModular_FunctionalInequalities_Poincare_L2_Energy

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

noncomputable section
open MeasureTheory
universe u
variable {α : Type u} [MeasurableSpace α]
/-- Unfolding validity gives the Poincaré inequality on the finite-energy domain. -/
theorem FunctionalInequalities.Poincare.L2Energy.holds_iff (μ : ProbabilityMeasure α)
    (energy : Energy.Functional (Lp ℝ 2 (μ : Measure α))) (C : NNReal) :
    Holds μ energy C ↔
      ∀ f : energy.domain, L2.variance μ f.1 ≤ C * energy.finiteValue f :=
  Iff.rfl
/-- A finite `L²` Poincaré constant is valid exactly when it bounds the optimal one. -/
theorem FunctionalInequalities.Poincare.L2Energy.holds_iff_constant_le (μ : ProbabilityMeasure α)
    (energy : Energy.Functional (Lp ℝ 2 (μ : Measure α))) (C : NNReal) :
    Holds μ energy C ↔ constant μ energy ≤ (C : ENNReal) := by
  simpa [Holds, constant] using
    TestFamily.holds_iff_constant_le (TestFamily.ofL2Energy μ energy) C
/-- Optimal constants agree along a linear isometric equivalence of `L²` spaces that preserves
variance and intertwines the two energies. -/
theorem solution {β : Type*} [MeasurableSpace β]
    (μ : ProbabilityMeasure α) (μ' : ProbabilityMeasure β)
    (energy : FunctionalInequalities.Energy.Functional (Lp ℝ 2 (μ : Measure α)))
    (energy' : FunctionalInequalities.Energy.Functional (Lp ℝ 2 (μ' : Measure β)))
    (e : Lp ℝ 2 (μ' : Measure β) ≃ₗᵢ[ℝ] Lp ℝ 2 (μ : Measure α))
    (hvar : ∀ f, FunctionalInequalities.L2.variance μ (e f) = FunctionalInequalities.L2.variance μ' f)
    (henergy : ∀ f, energy' f = energy (e f)) :
    FunctionalInequalities.Poincare.L2Energy.constant μ' energy' = FunctionalInequalities.Poincare.L2Energy.constant μ energy := by
  have hholds : ∀ C : NNReal, FunctionalInequalities.Poincare.L2Energy.Holds μ' energy' C ↔ FunctionalInequalities.Poincare.L2Energy.Holds μ energy C := by
    intro C
    rw [FunctionalInequalities.Poincare.L2Energy.holds_iff, FunctionalInequalities.Poincare.L2Energy.holds_iff]
    constructor
    · intro h f
      have hmem : e.symm f.1 ∈ energy'.domain := by
        change energy' (e.symm f.1) ≠ ⊤
        rw [henergy, e.apply_symm_apply]
        exact f.2
      have := h ⟨e.symm f.1, hmem⟩
      rw [← hvar, e.apply_symm_apply] at this
      refine this.trans (le_of_eq ?_)
      congr 1
      apply NNReal.eq
      simp only [FunctionalInequalities.Energy.Functional.finiteValue, henergy, e.apply_symm_apply]
    · intro h f
      have hmem : e f.1 ∈ energy.domain := by
        change energy (e f.1) ≠ ⊤
        rw [← henergy]
        exact f.2
      have := h ⟨e f.1, hmem⟩
      rw [hvar] at this
      refine this.trans (le_of_eq ?_)
      congr 1
      apply NNReal.eq
      simp only [FunctionalInequalities.Energy.Functional.finiteValue, henergy]
  refine le_antisymm ?_ ?_
  · by_cases htop : FunctionalInequalities.Poincare.L2Energy.constant μ energy = ⊤
    · rw [htop]; exact le_top
    · have h1 : FunctionalInequalities.Poincare.L2Energy.Holds μ energy (FunctionalInequalities.Poincare.L2Energy.constant μ energy).toNNReal :=
        (FunctionalInequalities.Poincare.L2Energy.holds_iff_constant_le _ _ _).mpr (by rw [ENNReal.coe_toNNReal htop])
      have h2 := (FunctionalInequalities.Poincare.L2Energy.holds_iff_constant_le _ _ _).mp ((hholds _).mpr h1)
      rwa [ENNReal.coe_toNNReal htop] at h2
  · by_cases htop : FunctionalInequalities.Poincare.L2Energy.constant μ' energy' = ⊤
    · rw [htop]; exact le_top
    · have h1 : FunctionalInequalities.Poincare.L2Energy.Holds μ' energy' (FunctionalInequalities.Poincare.L2Energy.constant μ' energy').toNNReal :=
        (FunctionalInequalities.Poincare.L2Energy.holds_iff_constant_le _ _ _).mpr (by rw [ENNReal.coe_toNNReal htop])
      have h2 := (FunctionalInequalities.Poincare.L2Energy.holds_iff_constant_le _ _ _).mp ((hholds _).mp h1)
      rwa [ENNReal.coe_toNNReal htop] at h2
