-- Prove2me | solution 1 for Formalism.CyclotomicNorms.Sqf.monic_monicOf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:50.774941+00:00
-- url     : https://prove2.me/submissions/f7a36176-0856-4c9e-b464-5f05d5397491

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
theorem _root_.solution {N : ℕ} (a : Fin N → K) : (monicOf a).Monic := by
  unfold monicOf
  exact monic_X_pow_add (degree_sum_fin_lt a)
end Formalism.CyclotomicNorms.Sqf
