-- Prove2me | solution 1 for Formalism.UG.P.fSatake_ord_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:27:14.179798+00:00
-- url     : https://prove2.me/submissions/48db812e-a2e9-450a-9ebe-f8680e584c1e

import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatakeA
import Theorems.Thm_Formalism_UG_P_fSatake_v_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Formalism.UG
noncomputable section
namespace Formalism.UG.P
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
private lemma ordL_eq_of_valuation_eq {x : L} (hx : x ≠ 0) {k : ℤ}
    (h : Valued.v x = ((Multiplicative.ofAdd (-k) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) :
    ordL x = k := by
  rw [fSatake_v_eq hx] at h
  have h2 := WithZero.coe_injective h
  have h3 := Multiplicative.ofAdd.injective h2
  linarith
end Formalism.UG.P
end
end

set_option autoImplicit false
open Formalism.UG
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
namespace Formalism.UG.P
theorem _root_.solution : ordL (1 : L) = 0 := by
  apply ordL_eq_of_valuation_eq one_ne_zero
  simp
end Formalism.UG.P
