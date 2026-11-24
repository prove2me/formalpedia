-- Prove2me | solution 1 for Formalism.L2.Pj.AvAlg.adjoin_eq_top_of_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:20:08.414261+00:00
-- url     : https://prove2.me/submissions/e63ead40-55ab-4362-ba0a-f01c34069d79

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AvMono
import Theorems.Thm_Formalism_L2_Pj_AvAlg_mem_adjoin_mod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Polynomial IsLocalRing
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.AvAlg
variable {A B : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B]
  [IsDiscreteValuationRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
namespace Formalism.L2.Pj.AvAlg
theorem _root_.solution [Module.Finite A B] (hinj : Function.Injective (algebraMap A B)) (α : B)
    (hres : Algebra.adjoin (ResidueField A) {residue B α} = ⊤) (f : A[X]) (hβ : Irreducible (aeval α f)) :
    Algebra.adjoin A {α} = ⊤ := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hϖ0 : algebraMap A B ϖ ≠ 0 := by
    rw [map_ne_zero_iff _ hinj]; exact hϖ.ne_zero
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hϖ0 hβ
  have hϖm : ϖ ∈ maximalIdeal A := (IsLocalRing.mem_maximalIdeal ϖ).mpr hϖ.not_isUnit
  have key : (⊤ : Submodule A B) ≤ Subalgebra.toSubmodule (Algebra.adjoin A {α}) ⊔ (maximalIdeal A) • ⊤ := by
    intro b _
    obtain ⟨s, hs, c, hc⟩ := mem_adjoin_mod α hres f hβ e b
    have e1 : b = s + ϖ • ((↑u⁻¹ : B) * c) := by
      rw [hc, Algebra.smul_def, hu]
      congr 1
      rw [mul_comm (↑u : B), mul_assoc, ← mul_assoc (↑u : B), Units.mul_inv, one_mul]
    rw [e1]
    exact Submodule.add_mem_sup ((Subalgebra.mem_toSubmodule _).mpr hs)
      (Submodule.smul_mem_smul hϖm Submodule.mem_top)
  have hfg : (⊤ : Submodule A B).FG := Module.Finite.fg_top
  have hle := Submodule.le_of_le_smul_of_le_jacobson_bot hfg
    (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge key
  rw [eq_top_iff]
  intro x _
  exact (Subalgebra.mem_toSubmodule _).mp (hle Submodule.mem_top)
end Formalism.L2.Pj.AvAlg
