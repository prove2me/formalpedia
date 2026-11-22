-- Prove2me | solution 1 for Formalism.QuantumDeterminants.WeylGroupFacts.col_of_fix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:55:46.104335+00:00
-- url     : https://prove2.me/submissions/65b64143-76ab-43d6-8b02-85af32958772

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.QuantumDeterminants.WeylGroupFacts
variable {k r : ℕ}
namespace Formalism.QuantumDeterminants.WeylGroupFacts
theorem _root_.solution {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    {c : Fin (2 * r + k + 1)} (hc : h *ᵥ bvec c = bvec c) (p : Fin (2 * r + k + 1)) :
    h p c = if p = c then 1 else 0 := by
  have hb : ∀ q : Fin (2 * r + k + 1), bvec c q = if q = c then 1 else 0 :=
    fun q => Pi.single_apply c 1 q
  have h1 := congrFun hc p
  first
    | (simp only [Matrix.mulVec, dotProduct, hb, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1; exact h1)
    | simpa [Matrix.mulVec, dotProduct, hb] using h1
    | simpa [Matrix.mulVec, Matrix.dotProduct, hb] using h1
end Formalism.QuantumDeterminants.WeylGroupFacts
