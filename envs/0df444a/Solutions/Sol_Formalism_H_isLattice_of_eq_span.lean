-- Prove2me | solution 1 for Formalism.H.isLattice_of_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:35:52.278802+00:00
-- url     : https://prove2.me/submissions/1460588a-a31a-4fbb-9def-b0e594acfd40

import Definitions.Def_Formalism_LatticeTheta_Statement
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_DualLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.H
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [FiniteDimensional ℝ V]
namespace Formalism.H
theorem _root_.solution {ι : Type*} [Fintype ι] (e : Module.Basis ι ℝ V) (L : Submodule ℤ V)
    (h : L = Submodule.span ℤ (Set.range e)) :
    DiscreteTopology L ∧ ∀ [DiscreteTopology L], IsZLattice ℝ L := by
  subst h
  refine ⟨inferInstance, ?_⟩
  intro _
  infer_instance
end Formalism.H
