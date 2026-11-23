-- Prove2me | solution 1 for Formalism.L2.SG.NormCut.PsiNatEquivPf.isUni_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:16:39.78383+00:00
-- url     : https://prove2.me/submissions/ff646a23-e14f-420d-b021-c59442d5fd80

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_NormCore
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_NormCorePsiNatEquiv
import Theorems.Thm_Formalism_L2_SG_NormCut_PsiNatEquivPf_IsUTm_mul

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
theorem _root_.solution {x y : GL (Fin k) F} (hx : IsUni k x) (hy : IsUni k y) : IsUni k (x * y) := by
  have h := IsUTm.mul (A := (x : Matrix (Fin k) (Fin k) F)) (B := (y : Matrix (Fin k) (Fin k) F)) hx hy
  show IsUTm ((x * y : GL (Fin k) F) : Matrix (Fin k) (Fin k) F)
  rw [Units.val_mul]
  exact h
end Formalism.L2.SG.NormCut.PsiNatEquivPf
