-- Prove2me | solution 1 for FunctionalInequalities.Poincare.L2Energy.Holds.of_energy_le_mul_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:40:29.633992+00:00
-- url     : https://prove2.me/submissions/87ef210e-2b1e-4d9b-ac4d-054a0b98acea

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLSModular_FunctionalInequalities_Poincare_L2_Comparison

section
section
variable {X : Type*}
/-- Coercing a finite energy back to `ENNReal` recovers the original value. -/
@[simp]
theorem FunctionalInequalities.Energy.Functional.coe_finiteValue (energy : Functional X) (x : energy.domain) :
    (energy.finiteValue x : ENNReal) = energy x.1 :=
  ENNReal.coe_toNNReal x.2
end
end

noncomputable section
open MeasureTheory
universe u
variable {α : Type u} [MeasurableSpace α]
/-- A finite comparison factor transfers a form-gap bound to another energy. The comparison
is required only on the target's finite domain and itself guarantees finite source energy.
This includes `κ = 0` and `C = 0`; no multiplication by an infinite target energy is used. -/
theorem solution {μ : ProbabilityMeasure α}
    {source target : FunctionalInequalities.Energy.Functional (Lp ℝ 2 (μ : Measure α))} {C κ : NNReal}
    (hC : FunctionalInequalities.Poincare.L2Energy.Holds μ source C)
    (henergy : ∀ f : target.domain,
      source f.1 ≤ (κ : ENNReal) * target f.1) :
    FunctionalInequalities.Poincare.L2Energy.Holds μ target (κ * C) := by
  intro f
  have hfinite : source.FiniteAt f.1 :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top f.2) (henergy f)
  let g : source.domain := ⟨f.1, hfinite⟩
  have hbound : source.finiteValue g ≤ κ * target.finiteValue f := by
    apply (ENNReal.coe_le_coe (r := source.finiteValue g)
      (q := κ * target.finiteValue f)).mp
    rw [ENNReal.coe_mul, source.coe_finiteValue g, target.coe_finiteValue f]
    exact henergy f
  change FunctionalInequalities.L2.variance μ f.1 ≤ (κ * C) * target.finiteValue f
  calc
    FunctionalInequalities.L2.variance μ f.1 ≤ C * source.finiteValue g := hC g
    _ ≤ C * (κ * target.finiteValue f) := mul_le_mul_of_nonneg_left hbound C.2
    _ = (κ * C) * target.finiteValue f := by rw [← mul_assoc, mul_comm C κ]
