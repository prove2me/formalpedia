-- Prove2me | solution 1 for Formalism.DivisionValues.idxChange_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:33:22.218327+00:00
-- url     : https://prove2.me/submissions/62eb2e0f-7054-4b58-928a-3601569cacf6

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Theorems.Thm_Formalism_DivisionValues_idxChange_sum_smul_act

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDedekindDomain Formalism.HermitianLatticesTheory
open scoped Matrix nonZeroDivisors
noncomputable section
open Formalism Formalism.DivisionValues
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] {d : ℕ}
namespace Formalism.DivisionValues
theorem _root_.solution {e : Fin d → Fin d → K} {γ : Matrix (Fin d) (Fin d) K}
    (he : LinearIndependent K (idxChangeAct e γ)) : γ.det ≠ 0 := by
  intro h0
  obtain ⟨g, hg0, hg⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  rw [Fintype.linearIndependent_iff] at he
  apply hg0
  funext i
  refine he g ?_ i
  rw [idxChange_sum_smul_act, hg]
  simp
end Formalism.DivisionValues
