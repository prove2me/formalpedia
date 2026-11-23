-- Prove2me | solution 1 for Formalism.UG.P.fSatake_ord_zpow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:52:19.114053+00:00
-- url     : https://prove2.me/submissions/e9a24b58-66cf-4553-ab3a-ef865949c753

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
theorem _root_.solution {ϖ : L}
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (k : ℤ) : ordL (ϖ ^ k) = k := by
  have h0 : ϖ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hϖ
    exact WithZero.zero_ne_coe hϖ
  apply ordL_eq_of_valuation_eq (zpow_ne_zero k h0)
  rw [map_zpow₀, hϖ, ← WithZero.coe_zpow, ← ofAdd_zsmul]
  congr 2
  simp
end Formalism.UG.P
