-- Prove2me | solution 1 for FunctionalInequalities.Energy.PreEnergy.exists_test_near_of_relaxation_lt_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:53:02.145692+00:00
-- url     : https://prove2.me/submissions/890ecd4d-8fe9-49af-bbc8-5129e1e19ce1

import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Sequences

section
noncomputable section
open Filter Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Energy
end FunctionalInequalities.Energy
open FunctionalInequalities FunctionalInequalities.Energy
universe u v
section
namespace FunctionalInequalities.Energy.PreEnergy
end FunctionalInequalities.Energy.PreEnergy
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.PreEnergy
variable {X : Type u} [TopologicalSpace X] (P : PreEnergy X)
/-- The relaxed energy is the infimum of the `liminf` energies of all approximating sequences. -/
theorem FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_apply (x : X) :
    P.sequentialRelaxation x = ⨅ f : P.ApproximatingSequence x, P.sequenceEnergy f :=
  rfl
end
end
end
end
end

noncomputable section
open Filter Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Energy
end FunctionalInequalities.Energy
open FunctionalInequalities FunctionalInequalities.Energy
section
namespace FunctionalInequalities.Energy.PreEnergy
end FunctionalInequalities.Energy.PreEnergy
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.PreEnergy
universe u
variable {X : Type u} [PseudoMetricSpace X] (P : PreEnergy X)
namespace FunctionalInequalities.Energy.PreEnergy
end FunctionalInequalities.Energy.PreEnergy
open FunctionalInequalities.Energy.PreEnergy in
/-- A strict relaxed-energy bound can be realized by a concrete test in any positive-radius
neighborhood. The strict inequality is essential: an optimal test need not exist. -/
theorem solution {x : X} {bound : ENNReal}
    (hbound : P.sequentialRelaxation x < bound) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : P.Test, dist (P.toAmbient f) x < ε ∧ (P.energy f : ENNReal) < bound := by
  rw [P.sequentialRelaxation_apply, iInf_lt_iff] at hbound
  obtain ⟨approximation, henergy⟩ := hbound
  have hnear : ∀ᶠ k : ℕ in atTop,
      dist (P.toAmbient (approximation.1 k)) x < ε := by
    have htendsto := approximation.2
    rw [Metric.tendsto_atTop] at htendsto
    obtain ⟨N, hN⟩ := htendsto ε hε
    exact eventually_atTop.2 ⟨N, hN⟩
  have hlow : ∃ᶠ k : ℕ in atTop, (P.energy (approximation.1 k) : ENNReal) < bound :=
    frequently_lt_of_liminf_lt (by isBoundedDefault) henergy
  obtain ⟨k, hk_energy, hk_near⟩ := (hlow.and_eventually hnear).exists
  exact ⟨approximation.1 k, hk_near, hk_energy⟩
