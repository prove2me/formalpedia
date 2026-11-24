-- Prove2me | solution 1 for Formalism.QuantumDeterminants.formal_degree_dimension_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:57:37.882801+00:00
-- url     : https://prove2.me/submissions/7b4a4cd2-22c9-4363-8a45-5c18c4818ccd

import Definitions.Def_Formalism_FormalDegreeBessel_HolDimLowK
import Definitions.Def_Formalism_FormalDegreeBessel_FinalDS
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_HolomorphicLowKDimensionHolds
import Theorems.Thm_Formalism_QuantumDeterminants_formal_degree_factorial_holds

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
theorem _root_.solution : FdegDimV := by
  intro n lam hlam
  have hnum : (∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), |lam a - lam b|) =
      ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), (lam a - lam b) := by
    refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b hb => ?_
    exact abs_of_pos (sub_pos.mpr (hlam (Finset.mem_filter.mp hb).2))
  unfold fdegHC
  rw [hnum, formal_degree_factorial_holds n]
end Formalism.QuantumDeterminants
