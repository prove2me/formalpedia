-- Prove2me | solution 1 for Formalism.L2.SG.NormCut.PsiNatEquivPf.psiU_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:26:05.172671+00:00
-- url     : https://prove2.me/submissions/8c0246ff-bd61-4389-83c9-004fe63b3aea

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_NormCore
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_NormCorePsiNatEquiv
import Theorems.Thm_Formalism_L2_SG_NormCut_PsiNatEquivPf_superdiag_mul

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
theorem _root_.solution (ψ₀ : AddChar F ℂ) {x y : GL (Fin k) F} (hx : IsUni k x) (hy : IsUni k y) :
    psiU ψ₀ (x * y) = psiU ψ₀ x * psiU ψ₀ y := by
  unfold psiU
  rw [Units.val_mul, superdiag_mul (A := (x : Matrix (Fin k) (Fin k) F))
    (B := (y : Matrix (Fin k) (Fin k) F)) hx hy]
  first
    | exact AddChar.map_add_eq_mul ψ₀ _ _
    | exact AddChar.map_add_mul ψ₀ _ _
end Formalism.L2.SG.NormCut.PsiNatEquivPf
