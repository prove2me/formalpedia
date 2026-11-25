-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.same_place_constant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:02:13.752882+00:00
-- url     : https://prove2.me/submissions/cb106e61-8303-426b-81a6-ad2740dedfe7

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_LatticeDeterminantIndexSq
import Definitions.Def_Formalism_FlagUnipotentLattices_SignaturePreservingEntryNorms
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegerGroupLocalParametrization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField nonZeroDivisors Finset
noncomputable section
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.LocalIntegralStructure Formalism.HermitianLatticeCounting.P.IntegralityLocalGlobal
set_option linter.all false
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : SamePlaceConst := by
  intro ι k x dimpi dimpi' deg VV Vd Tc K Pn Pk A B T' hPn hPk hA hB hT' hdeg hd' hx hVV hVd hT v
  have h := hT v
  rw [hVV, hVd] at h
  have hTk : Tc v ^ k = B * (deg v * Pn / (dimpi' v * Pk)) / A := by
    field_simp; field_simp at h; linarith
  rw [hx, inv_pow, div_pow, hTk]
  have := hdeg v; have := hd' v
  field_simp
end Formalism.HermitianLatticeCounting.P
