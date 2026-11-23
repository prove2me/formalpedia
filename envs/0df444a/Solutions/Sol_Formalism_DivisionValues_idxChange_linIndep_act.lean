-- Prove2me | solution 1 for Formalism.DivisionValues.idxChange_linIndep_act
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:12:11.318993+00:00
-- url     : https://prove2.me/submissions/4e57b24b-99ad-4efd-99ce-56e7cbee8237

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
theorem _root_.solution {e : Fin d → Fin d → K} (he : LinearIndependent K e)
    {γ : Matrix (Fin d) (Fin d) K} (hγ : γ.det ≠ 0) : LinearIndependent K (idxChangeAct e γ) := by
  rw [Fintype.linearIndependent_iff] at he ⊢
  intro g hg
  rw [idxChange_sum_smul_act] at hg
  have h0 : γ *ᵥ g = 0 := funext (he _ hg)
  have := Matrix.eq_zero_of_mulVec_eq_zero hγ h0
  intro i
  rw [this]; rfl
end Formalism.DivisionValues
