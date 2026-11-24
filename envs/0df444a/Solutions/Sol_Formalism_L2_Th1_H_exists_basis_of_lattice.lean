-- Prove2me | solution 1 for Formalism.L2.Th1.H.exists_basis_of_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:26:09.961927+00:00
-- url     : https://prove2.me/submissions/40df0458-20bd-450a-b49e-298562d98b5c

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_UnitaryConstant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_RelIndexEqAbsDetReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Module
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
namespace Formalism.L2.Th1.H
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Λ : AddSubgroup E) (hd : DiscreteTopology Λ) (hs : Submodule.span ℝ (Λ : Set E) = ⊤) :
    ∃ b : Basis (Fin (finrank ℝ E)) ℝ E, Λ = .closure (Set.range b) := by
  classical
  let L : Submodule ℤ E := AddSubgroup.toIntSubmodule Λ
  haveI : DiscreteTopology L := hd
  haveI : IsZLattice ℝ L := ⟨hs⟩
  haveI := ZLattice.module_free ℝ L
  haveI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  let b := Module.Free.chooseBasis ℤ L
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ L) = finrank ℝ E := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ L]
  let b' := b.reindex (Fintype.equivFinOfCardEq hcard)
  refine ⟨Basis.ofZLatticeBasis ℝ L b', ?_⟩
  rw [← Submodule.span_int_eq_addSubgroupClosure, Basis.ofZLatticeBasis_span]
  rfl
end Formalism.L2.Th1.H
