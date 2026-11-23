-- Prove2me | solution 1 for Formalism.DivisionValues.idxChange_sum_smul_act
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:07:00.435247+00:00
-- url     : https://prove2.me/submissions/8c85882e-1c4c-46fe-a12c-5d90a6ddc64c

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange

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
theorem _root_.solution (e : Fin d → Fin d → K) (γ : Matrix (Fin d) (Fin d) K)
    (g : Fin d → K) : ∑ i, g i • idxChangeAct e γ i = ∑ k, (γ *ᵥ g) k • e k := by
  simp only [idxChangeAct, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm]
end Formalism.DivisionValues
