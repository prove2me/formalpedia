-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.dualLattice_basis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:33:18.291803+00:00
-- url     : https://prove2.me/submissions/652f0bcb-0c59-4fd4-a4ce-7139d49291d9

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution [FiniteDimensional K V] (L : Submodule R V)
    (hsp : Submodule.span K (L : Set V) = ⊤) :
    ∃ (s : Set V) (_ : Fintype s) (b : Basis s K V), (∀ i, b i = (i : V)) ∧ s ⊆ L := by
  obtain ⟨s, hsL, hspan, hli⟩ := exists_linearIndependent K (L : Set V)
  have hfin : s.Finite := hli.setFinite
  refine ⟨s, hfin.fintype, Basis.mk hli (by rw [Subtype.range_coe, hspan, hsp]), fun i => ?_, hsL⟩
  simp
end Formalism.HermitianLatticesTheory
