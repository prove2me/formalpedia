-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.neighbourBasic_gen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:57.649451+00:00
-- url     : https://prove2.me/submissions/5c12e800-8c82-47de-a163-162b8a49b369

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
    (e : (L ⧸ N.comap L.subtype) ≃ₗ[R] (R ⧸ I)) :
    ∃ l₀ ∈ L, ∀ l ∈ L, ∃ a : R, l - a • l₀ ∈ N := by
  obtain ⟨x₀, hx₀⟩ := Submodule.Quotient.mk_surjective _ (e.symm (Submodule.Quotient.mk 1))
  refine ⟨x₀, x₀.2, fun l hl => ?_⟩
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (e (Submodule.Quotient.mk ⟨l, hl⟩))
  refine ⟨a, ?_⟩
  have h1 : Submodule.Quotient.mk (p := N.comap L.subtype) (⟨l, hl⟩ - a • x₀) = 0 := by
    rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, hx₀, ← map_smul,
      ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one, ha, LinearEquiv.symm_apply_apply,
      sub_self]
  rw [Submodule.Quotient.mk_eq_zero] at h1
  exact h1
end Formalism.HermitianLatticesTheory
