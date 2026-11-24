-- Prove2me | solution 1 for Formalism.QuantumDeterminants.formal_degree_vandermonde_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:12:38.623843+00:00
-- url     : https://prove2.me/submissions/f6b8676e-7673-4916-abf4-0f2f7ee376f4

import Definitions.Def_Formalism_FormalDegreeBessel_StatementDS
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_DSFdeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.REAL
namespace Formalism.QuantumDeterminants
theorem _root_.solution : FdegVand := by
  intro n lam hl
  unfold fdegHC vand Formalism.QuantumDeterminants.rhoStd
  have h1 : ∀ a : Fin n, ∀ b ∈ univ.filter (fun b : Fin n => a < b),
      |lam a - lam b| = lam a - lam b := fun a b hb =>
    abs_of_pos (sub_pos.mpr (hl (Finset.mem_filter.mp hb).2))
  rw [Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl (h1 a)]
  push_cast
  congr 1
  refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b _ => ?_
  ring
end Formalism.QuantumDeterminants
