-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RuleSS.four_inter
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:19.636272+00:00
-- url     : https://prove2.me/submissions/b9803aff-91fc-44c2-b43f-f3aeeb46aa24

import Definitions.Def_Formalism_HermitianCurvature_StatementR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleSS
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleSS_I_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleSS_I_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RuleSS
open Matrix Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData
variable {A : Type} [Ring A] [Algebra ℂ A]
variable {r : ℕ} (L : LevelData A r)
namespace Formalism.FourierDecayAlt.P.RuleSS
theorem _root_.solution (h : A) (Ya Y1 Yl Yl' Yv Yv' Ym Ym' : ℂ)
    (hA : L.Ar Ya * h = h * L.Ar Y1) (hB : L.Br Ya * h = h * L.Br Y1)
    (hl : L.l0 Yl * h = h * L.l0 Yl')
    (hAv : L.Avr Yv * h = h * L.Avr Yv') (hBv : L.Bvr Yv * h = h * L.Bvr Yv')
    (hm : L.m0 Ym * h = h * L.m0 Ym')
    (hDr : Commute L.Dr h) (hDrb : Commute L.Drb h) (hGG : Commute L.GG h) :
    L.Dr * L.Ar Ya * h = h * (L.Dr * L.Ar Y1) ∧
    L.Drb * L.GG * (L.l0 Yl * L.Ar Ya + L.Br Ya) * h = h * (L.Drb * L.GG * (L.l0 Yl' * L.Ar Y1 + L.Br Y1)) ∧
    L.Drb * L.Avr Yv * h = h * (L.Drb * L.Avr Yv') ∧
    L.Dr * L.GG * (L.m0 Ym * L.Avr Yv + L.Bvr Yv) * h = h * (L.Dr * L.GG * (L.m0 Ym' * L.Avr Yv' + L.Bvr Yv')) :=
  ⟨I_mul hDr.eq hA, I_mul (I_mul hDrb.eq hGG.eq) (I_add (I_mul hl hA) hB), I_mul hDrb.eq hAv,
    I_mul (I_mul hDr.eq hGG.eq) (I_add (I_mul hm hAv) hBv)⟩
end Formalism.FourierDecayAlt.P.RuleSS
