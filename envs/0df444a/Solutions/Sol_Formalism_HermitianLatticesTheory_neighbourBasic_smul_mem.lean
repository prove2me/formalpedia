-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.neighbourBasic_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:59.058725+00:00
-- url     : https://prove2.me/submissions/2de49c4b-2208-4ded-b8a1-6931da4fec54

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_NeighbourBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution {I : Ideal R} {L N : Submodule R V}
    (e : (L ⧸ N.comap L.subtype) ≃ₗ[R] (R ⧸ I)) {r : R} (hr : r ∈ I) {l : V} (hl : l ∈ L) :
    r • l ∈ N := by
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (e (Submodule.Quotient.mk ⟨l, hl⟩))
  have h0 : e (r • Submodule.Quotient.mk (⟨l, hl⟩ : L)) = 0 := by
    rw [map_smul, ← ha, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul]
    exact I.mul_mem_right a hr
  rw [LinearEquiv.map_eq_zero_iff, ← Submodule.Quotient.mk_smul,
    Submodule.Quotient.mk_eq_zero] at h0
  exact h0
end Formalism.HermitianLatticesTheory
