-- Prove2me | solution 1 for Formalism.UG.P.tjcosets_stab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:54:12.871067+00:00
-- url     : https://prove2.me/submissions/d5343a05-ed0c-40f3-8d9b-3a03199a7c94

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsFF
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsLoc
import Theorems.Thm_Formalism_UG_P_tjcosets_bc_apply
import Theorems.Thm_Formalism_UG_P_tjcosets_iso_coe
import Theorems.Thm_Formalism_UG_P_tjcosets_red_iso
import Theorems.Thm_Formalism_UG_P_tjcosets_conj_apply
import Theorems.Thm_Formalism_UG_P_tjcosets_mem_K_iff
import Theorems.Thm_Formalism_UG_P_tjcosets_entries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {L : Type} [Field L]
variable (O : Subring L) [IsLocalRing O]
variable {O}
namespace Formalism.UG.P
theorem _root_.solution (n j : ℕ) (ϖ : L) (hϖO : ϖ ∈ O) (hϖ : ϖ ≠ 0)
    (hmax : ∀ x : O, ϖ⁻¹ * (x : L) ∈ O ↔ IsLocalRing.residue O x = 0)
    [Finite (IsLocalRing.ResidueField O)] :
    MulAction.stabilizer (GLint (Fin n) O)
        (QuotientGroup.mk (tjcosets_dG n j ϖ hϖ) : GL (Fin n) L ⧸ GLint (Fin n) O) =
      (tjcosets_par n j).comap (tjcosets_red O n) := by
  ext g
  obtain ⟨h, rfl⟩ := (tjcosets_iso n O).surjective g
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_comap, tjcosets_red_iso]
  have e1 : (tjcosets_iso n O h) • (QuotientGroup.mk (tjcosets_dG n j ϖ hϖ) : GL (Fin n) L ⧸ GLint (Fin n) O) =
      QuotientGroup.mk (bc O.subtype h * tjcosets_dG n j ϖ hϖ) := by
    show (QuotientGroup.mk (((tjcosets_iso n O h : GLint (Fin n) O) : GL (Fin n) L) * tjcosets_dG n j ϖ hϖ) :
      GL (Fin n) L ⧸ GLint (Fin n) O) = _
    rw [tjcosets_iso_coe]
  rw [e1, QuotientGroup.eq]
  have e2 : (bc O.subtype h * tjcosets_dG n j ϖ hϖ)⁻¹ * tjcosets_dG n j ϖ hϖ =
      (tjcosets_dG n j ϖ hϖ)⁻¹ * bc O.subtype h⁻¹ * tjcosets_dG n j ϖ hϖ := by
    rw [map_inv]; group
  have e3 : ((tjcosets_dG n j ϖ hϖ)⁻¹ * bc O.subtype h⁻¹ * tjcosets_dG n j ϖ hϖ)⁻¹ =
      (tjcosets_dG n j ϖ hϖ)⁻¹ * bc O.subtype h * tjcosets_dG n j ϖ hϖ := by
    rw [map_inv]; group
  rw [e2, tjcosets_mem_K_iff, e3]
  have E1 := tjcosets_entries n j ϖ hϖ hmax h⁻¹ hϖO
  have E2 := tjcosets_entries n j ϖ hϖ hmax h hϖO
  rw [map_inv, inv_mem_iff] at E1
  constructor
  · rintro ⟨_, h2⟩
    refine E2.1 (fun a b => ?_)
    have h3 := h2 a b
    rw [tjcosets_conj_apply, tjcosets_bc_apply] at h3
    exact h3
  · intro hp
    refine ⟨fun a b => ?_, fun a b => ?_⟩
    · have h3 := E1.2 hp a b
      rw [tjcosets_conj_apply, tjcosets_bc_apply]
      exact h3
    · have h3 := E2.2 hp a b
      rw [tjcosets_conj_apply, tjcosets_bc_apply]
      exact h3
end Formalism.UG.P
