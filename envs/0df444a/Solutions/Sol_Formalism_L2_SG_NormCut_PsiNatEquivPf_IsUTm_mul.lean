-- Prove2me | solution 1 for Formalism.L2.SG.NormCut.PsiNatEquivPf.IsUTm.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:11.049856+00:00
-- url     : https://prove2.me/submissions/72524e74-c0a3-4ff3-84ae-abad6feedec4

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
theorem _root_.solution {A B : Matrix (Fin k) (Fin k) F} (hA : IsUTm A) (hB : IsUTm B) : IsUTm (A * B) := by
  obtain ⟨hA1, hA0⟩ := hA
  obtain ⟨hB1, hB0⟩ := hB
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hA1, hB1, one_mul]
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with h | h
      · rw [hA0 i l h, zero_mul]
      · rw [hB0 l i h, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rcases lt_or_ge l i with h | h
    · rw [hA0 i l h, zero_mul]
    · rw [hB0 l j (lt_of_lt_of_le hij h), mul_zero]
end IsUTm
end Formalism.L2.SG.NormCut.PsiNatEquivPf
