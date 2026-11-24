-- Prove2me | solution 1 for Formalism.L2.DIV.CSD.basis_rat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:10:22.504849+00:00
-- url     : https://prove2.me/submissions/fc62721e-d539-4723-b869-9bc2bc775bfd

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSum
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Theorems.Thm_Formalism_L2_DIV_CSD_basis_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV Formalism.L2.DIV.CSD
open Formalism.DivisionValues
variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)
namespace Formalism.L2.DIV.CSD
theorem _root_.solution (h : S.HasRatBasis) (i : Fin S.dim) : S.IsRat (S.basis i : S.Cl → S.V) := by
  rw [S.basis_eq h]
  exact h.choose_spec i
end Formalism.L2.DIV.CSD
