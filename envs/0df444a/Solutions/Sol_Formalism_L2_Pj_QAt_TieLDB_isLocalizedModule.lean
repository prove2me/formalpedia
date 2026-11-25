-- Prove2me | solution 1 for Formalism.L2.Pj.QAt.TieLDB.isLocalizedModule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:08:03.14142+00:00
-- url     : https://prove2.me/submissions/48923f4e-45e3-4f96-8469-ef452c9fb093

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_TieLDB
import Theorems.Thm_Formalism_L2_Pj_QAt_TieLDB_exists_smul_mem
import Theorems.Thm_Formalism_L2_Pj_QAt_TieLDB_locMap_mk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.L2.Pj.QAt.TieLDB
open Module
variable {A : Type*} [CommRing A] (p : Ideal A) [p.IsPrime]
  {V : Type*} [AddCommGroup V] [Module A V] [Module (Localization.AtPrime p) V]
  [IsScalarTower A (Localization.AtPrime p) V]
variable (H G : Submodule A V)
namespace Formalism.L2.Pj.QAt.TieLDB
theorem _root_.solution : IsLocalizedModule p.primeCompl (locMap p H G) where
  map_units s := by
    rw [Module.End.isUnit_iff]
    have hu := IsLocalization.map_units (Localization.AtPrime p) s
    constructor
    · intro z1 z2 h
      rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply,
        ← algebraMap_smul (Localization.AtPrime p) (s : A) z1,
        ← algebraMap_smul (Localization.AtPrime p) (s : A) z2] at h
      exact hu.smul_left_cancel.1 h
    · intro z
      refine ⟨hu.unit⁻¹ • z, ?_⟩
      rw [Module.algebraMap_end_apply, ← algebraMap_smul (Localization.AtPrime p) (s : A)]
      change hu.unit • hu.unit⁻¹ • z = z
      rw [smul_inv_smul]
  surj y := by
    obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨s, hs, hsx⟩ := exists_smul_mem p H hx
    refine ⟨(Submodule.Quotient.mk ⟨s • x, hsx⟩, ⟨s, hs⟩), ?_⟩
    rw [locMap_mk]
    rfl
  exists_of_eq {x₁ x₂} h := by
    obtain ⟨h1, rfl⟩ := Submodule.Quotient.mk_surjective _ x₁
    obtain ⟨h2, rfl⟩ := Submodule.Quotient.mk_surjective _ x₂
    rw [locMap_mk, locMap_mk, Submodule.Quotient.eq] at h
    have h' : (h1 : V) - h2 ∈ Submodule.span (Localization.AtPrime p) (G : Set V) := h
    obtain ⟨s, hs, hsx⟩ := exists_smul_mem p G h'
    refine ⟨⟨s, hs⟩, ?_⟩
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
    change (s • (h1 : V)) - s • (h2 : V) ∈ G
    rw [← smul_sub]
    exact hsx
end Formalism.L2.Pj.QAt.TieLDB
