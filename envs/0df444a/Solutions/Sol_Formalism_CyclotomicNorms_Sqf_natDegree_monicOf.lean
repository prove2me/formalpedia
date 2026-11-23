-- Prove2me | solution 1 for Formalism.CyclotomicNorms.Sqf.natDegree_monicOf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:50.825729+00:00
-- url     : https://prove2.me/submissions/7befcdf5-f879-4574-bdc5-de34a7d9a12f

import Definitions.Def_Formalism_CyclotomicNorms_StatementI
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_NonsquarefreeMonicBoundHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
open Formalism Formalism.CyclotomicNorms
open Formalism.CyclotomicNorms.Sqf
variable {K : Type} [Field K]
namespace Formalism.CyclotomicNorms.Sqf
theorem _root_.solution {N : ℕ} (a : Fin N → K) : (monicOf a).natDegree = N := by
  unfold monicOf
  rw [natDegree_add_eq_left_of_degree_lt (by rw [degree_X_pow]; exact degree_sum_fin_lt a), natDegree_X_pow]
end Formalism.CyclotomicNorms.Sqf
