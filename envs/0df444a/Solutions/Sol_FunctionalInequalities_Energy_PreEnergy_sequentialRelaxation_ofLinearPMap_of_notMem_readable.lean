-- Prove2me | solution 1 for FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_ofLinearPMap_of_notMem_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:04:18.367935+00:00
-- url     : https://prove2.me/submissions/5b4cca31-475a-446a-b10c-b195ad860fa0

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Relaxation_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Relaxation_LinearPMap
import Theorems.Thm_FunctionalInequalities_Energy_PreEnergy_mem_closure_domain_of_frequently_readable

section
noncomputable section
open Filter Topology
section
universe u v
section
variable {X : Type u} [TopologicalSpace X] (P : FunctionalInequalities.Energy.PreEnergy X)
/-- The relaxed energy is the infimum of the `liminf` energies of all approximating sequences. -/
theorem FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_apply (x : X) :
    P.sequentialRelaxation x = ⨅ f : P.ApproximatingSequence x, P.sequenceEnergy f :=
  rfl
end
end
end
end

noncomputable section
open Filter Topology Set
section PreEnergy
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (T : X →ₗ.[ℝ] H)
/-- Outside the domain of the closure the relaxed energy is infinite. -/
theorem solution (hT : T.IsClosable) {x : X}
    (hx : x ∉ T.closure.domain) : (FunctionalInequalities.Energy.PreEnergy.ofLinearPMap T).sequentialRelaxation x = ⊤ := by
  rw [FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_apply]
  refine le_antisymm le_top (le_iInf fun f ↦ ?_)
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨r, hr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hlt
  have hfreq : ∃ᶠ n in atTop, ‖T (f.1 n)‖₊ ≤ NNReal.sqrt r := by
    have := frequently_lt_of_liminf_lt (by isBoundedDefault) hr.1
    refine this.mono fun n hn ↦ ?_
    have hn' : (‖T (f.1 n)‖₊ ^ 2 : NNReal) < r := by
      have := hn
      change ((‖T (f.1 n)‖₊ ^ 2 : NNReal) : ENNReal) < (r : ENNReal) at this
      exact_mod_cast this
    have := NNReal.sqrt_le_sqrt.mpr hn'.le
    rwa [NNReal.sqrt_sq] at this
  obtain ⟨hxdom, -⟩ := FunctionalInequalities.Energy.PreEnergy.mem_closure_domain_of_frequently_readable T hT f hfreq
  exact hx hxdom
