-- Prove2me | solution 1 for Formalism.L2.SG.NormCut.PsiNatEquivPf.IsUTm.inv_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:17:45.027657+00:00
-- url     : https://prove2.me/submissions/f054622d-2b73-4eea-b323-9b9395ccb366

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_NormCore
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_NormCorePsiNatEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open scoped ComplexConjugate
noncomputable section
open Classical
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.NormCut Formalism.L2.SG.NormCut.PsiNatEquivPf
open Formalism.L2.SG.GGMirabolic
variable {F : Type} [Field F] [Fintype F] {k : ℕ}
namespace Formalism.L2.SG.NormCut.PsiNatEquivPf
namespace IsUTm
theorem _root_.solution (u : GL (Fin k) F) (h : IsUTm (u : Matrix (Fin k) (Fin k) F)) :
    IsUTm ((u⁻¹ : GL (Fin k) F) : Matrix (Fin k) (Fin k) F) := by
  have htri : ∀ i j : Fin k, j < i → ((u⁻¹ : GL (Fin k) F) : Matrix (Fin k) (Fin k) F) i j = 0 := by
    intro i j hij
    letI : Invertible (u : Matrix (Fin k) (Fin k) F) := u.invertible
    have hb : (u : Matrix (Fin k) (Fin k) F).BlockTriangular id := by
      intro a b hab
      exact h.2 a b hab
    rw [Matrix.coe_units_inv u]
    exact Matrix.blockTriangular_inv_of_blockTriangular hb hij
  refine ⟨fun i => ?_, htri⟩

  have hmul : ((u : Matrix (Fin k) (Fin k) F) * ((u⁻¹ : GL (Fin k) F) : Matrix (Fin k) (Fin k) F)) i i = 1 := by
    rw [Units.mul_inv, Matrix.one_apply_eq]
  rw [Matrix.mul_apply, Finset.sum_eq_single i, h.1 i, one_mul] at hmul
  · exact hmul
  · intro l _ hl
    rcases lt_or_gt_of_ne hl with hl' | hl'
    · rw [h.2 i l hl', zero_mul]
    · rw [htri l i hl', mul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi
end IsUTm
end Formalism.L2.SG.NormCut.PsiNatEquivPf
