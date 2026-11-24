-- Prove2me | solution 1 for Formalism.UG.P.tjcosets_prod_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:40:50.571691+00:00
-- url     : https://prove2.me/submissions/4c55dd3b-1ba0-498c-9360-35f93a74cca8

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsLoc
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Tjcosets

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Matrix
open scoped WithZero
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
namespace Formalism.UG.P
theorem _root_.solution (q : ℤ) (j m : ℕ) :
    (∏ i ∈ Finset.range j, (q ^ (i + 1) - 1)) * ∏ i ∈ Finset.range m, (q ^ (j + m - i) - 1) =
      ∏ i ∈ Finset.range (j + m), (q ^ (i + 1) - 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ', ← add_assoc, Finset.prod_range_succ, ← ih, mul_assoc]
    congr 2
    refine Finset.prod_congr rfl fun i hi => ?_
    congr 2
    omega
end Formalism.UG.P
