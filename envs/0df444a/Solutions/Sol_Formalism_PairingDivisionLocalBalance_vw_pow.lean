-- Prove2me | solution 1 for Formalism.PairingDivisionLocalBalance.vw_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:57.414608+00:00
-- url     : https://prove2.me/submissions/57d7ca45-9e5b-417d-bfd4-7e348a87fd4b

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_PairingDivisorProofs_SumValuationNat
import Definitions.Def_Formalism_PairingDivisors_PairingDivisorProofs_Height
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_mul
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw lw conjPl)
open Formalism Formalism.PairingDivisionLocalBalance
namespace Formalism.PairingDivisionLocalBalance
theorem _root_.solution {K : Type} [Field K] [NumberField K] [StarRing K] (w : Pl K) (a : K) (ha : a ≠ 0) (n : ℕ) :
    vw w (a ^ n) = n * vw w a := by
  induction n with
  | zero => simp [Formalism.DivisionValues.ValuationRepresentative.vw_one]
  | succ n ih =>
    rw [pow_succ, Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ (pow_ne_zero n ha) ha, ih]; push_cast; ring
end Formalism.PairingDivisionLocalBalance
