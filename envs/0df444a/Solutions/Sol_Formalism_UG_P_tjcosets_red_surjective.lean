-- Prove2me | solution 1 for Formalism.UG.P.tjcosets_red_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:40:51.412996+00:00
-- url     : https://prove2.me/submissions/cabfa3e1-18e0-4cdc-816b-945e3445f81f

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsFF
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsLoc
import Theorems.Thm_Formalism_UG_P_tjcosets_bc_apply
import Theorems.Thm_Formalism_UG_P_tjcosets_red_iso

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
namespace Formalism.UG.P
theorem _root_.solution (n : ℕ) : Function.Surjective (tjcosets_red O n) := by
  intro g
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin n) (Fin n) O,
      M.map (IsLocalRing.residue O) = g.1 := by
    refine ⟨fun a b => (IsLocalRing.residue_surjective (g.1 a b)).choose, ?_⟩
    ext a b
    exact (IsLocalRing.residue_surjective (g.1 a b)).choose_spec
  have hdet : IsUnit M.det := by
    have h1 : IsLocalRing.residue O M.det = g.1.det := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hM]
    have hu : IsUnit g.1.det := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.isUnit _
    by_contra hne
    have h0 : IsLocalRing.residue O M.det = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).2 ((IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hne))
    rw [h1] at h0
    exact hu.ne_zero h0
  refine ⟨tjcosets_iso n O (Matrix.GeneralLinearGroup.mk'' M hdet), ?_⟩
  rw [tjcosets_red_iso]
  refine Units.ext (Matrix.ext fun a b => ?_)
  rw [tjcosets_bc_apply]
  show IsLocalRing.residue O (M a b) = _
  rw [← hM]
  rfl
end Formalism.UG.P
