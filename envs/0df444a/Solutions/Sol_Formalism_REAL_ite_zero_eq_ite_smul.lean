-- Prove2me | solution 1 for Formalism.REAL.ite_zero_eq_ite_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:34:53.739828+00:00
-- url     : https://prove2.me/submissions/6a1c133e-32b5-4e7b-9d89-d30ffef187de

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution {A : Type*} [Ring A] [Algebra ℂ A] (P : Prop) [Decidable P] (X : A) :
    (if P then X else 0) = (if P then (1 : ℂ) else 0) • X := by
  split_ifs <;> simp
end Formalism.REAL
