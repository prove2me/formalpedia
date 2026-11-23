-- Prove2me | solution 1 for Formalism.UG.P.fSatake_chiDelta_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:31:53.477925+00:00
-- url     : https://prove2.me/submissions/0c78189f-17e4-41e8-93de-7c325e5ff804

import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatakeC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeActMem
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeConvolutionMemHolds
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatake
import Theorems.Thm_Formalism_UG_P_fSatake_ord_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}
namespace Formalism.UG.P
theorem _root_.solution {q m : ℕ} (α : Fin m → ℂ) :
    chiDeltaU (σ := σ) (n := n) q α 1 = 1 := by
  unfold chiDeltaU
  refine Finset.prod_eq_one fun i _ => ?_
  split_ifs with h
  · simp [fSatake_ord_one]
  · rfl
end Formalism.UG.P
