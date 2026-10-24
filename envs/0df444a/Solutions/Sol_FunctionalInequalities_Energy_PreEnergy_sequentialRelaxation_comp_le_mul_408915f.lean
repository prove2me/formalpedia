-- Prove2me | solution 1 for FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_comp_le_mul_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:50:10.540736+00:00
-- url     : https://prove2.me/submissions/00288626-1c81-474f-b32a-136cbd448210

import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.LiminfLimsup

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
/-- Every particular approximating sequence gives an upper bound for the relaxed energy. -/
theorem FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_le_sequenceEnergy {x : X} (f : P.ApproximatingSequence x) :
    P.sequentialRelaxation x ≤ P.sequenceEnergy f :=
  iInf_le _ f
namespace FunctionalInequalities.Energy.PreEnergy
end FunctionalInequalities.Energy.PreEnergy
open FunctionalInequalities.Energy.PreEnergy in
/-- Scaled comparison of relaxations along a continuous map: if every concrete test of `P` is
matched by a test of `Q` with the mapped realization and energy at most `κ` times as large, the
relaxations compare with the same finite factor at every point of finite `P`-relaxation. The
finiteness premise excludes `κ = 0` against an empty approximating class. -/
theorem solution {Y : Type*} [TopologicalSpace Y]
    (Q : FunctionalInequalities.Energy.PreEnergy Y) (T : X → Y) (hT : Continuous T) (κ : NNReal)
    (h : ∀ f : P.Test, ∃ g : Q.Test,
      Q.toAmbient g = T (P.toAmbient f) ∧ (Q.energy g : ENNReal) ≤ κ * P.energy f) (x : X)
    (hx : P.sequentialRelaxation x ≠ ⊤) :
    Q.sequentialRelaxation (T x) ≤ κ * P.sequentialRelaxation x := by
  have hne : Nonempty (P.ApproximatingSequence x) := by
    by_contra hempty
    rw [not_nonempty_iff] at hempty
    have := hempty
    apply hx
    rw [P.sequentialRelaxation_apply]
    exact iInf_of_empty (fun s : P.ApproximatingSequence x ↦ P.sequenceEnergy s)
  rw [P.sequentialRelaxation_apply,
    ENNReal.mul_iInf' (fun htop ↦ absurd htop ENNReal.coe_ne_top) (fun _ ↦ hne)]
  refine le_iInf fun s ↦ ?_
  choose g hreal henergy using fun n ↦ h (s.1 n)
  have hconv : Tendsto (fun n ↦ Q.toAmbient (g n)) atTop (𝓝 (T x)) := by
    simpa only [hreal, Function.comp_def] using (hT.tendsto x).comp s.2
  refine (Q.sequentialRelaxation_le_sequenceEnergy ⟨g, hconv⟩).trans ?_
  refine (liminf_le_liminf (Eventually.of_forall fun n ↦ henergy n)).trans_eq ?_
  have hmono : Monotone fun a : ENNReal ↦ (κ : ENNReal) * a := fun _ _ hab ↦ mul_le_mul' le_rfl hab
  exact (hmono.map_liminf_of_continuousAt (fun n ↦ (P.energy (s.1 n) : ENNReal))
    ((ENNReal.continuous_const_mul ENNReal.coe_ne_top).continuousAt)).symm
