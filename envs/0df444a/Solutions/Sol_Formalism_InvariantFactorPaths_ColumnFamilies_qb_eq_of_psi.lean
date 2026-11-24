-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qb_eq_of_psi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:03:28.680002+00:00
-- url     : https://prove2.me/submissions/78b75507-5eb0-4b91-b90a-b0e800bd4242

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_FiltrationTheoremOfClauses
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreW
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_eq_of_psum_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {nu mu : Fin n → ℤ} (h : DomLE nu mu) (h2 : qb_psi mu ≤ qb_psi nu) : nu = mu := by
  apply qb_eq_of_psum_eq
  by_contra hne
  push Not at hne
  obtain ⟨a, ha⟩ := hne
  have : qb_psi nu < qb_psi mu :=
    sum_lt_sum (fun i _ => h.1 i) ⟨a, mem_univ _, lt_of_le_of_ne (h.1 a) ha⟩
  linarith
end Formalism.InvariantFactorPaths.ColumnFamilies
