-- Prove2me | solution 1 for Formalism.L2.DIV.majAt_congr_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:55:28.468317+00:00
-- url     : https://prove2.me/submissions/66b65f23-8b1c-40ab-9233-a48cfd797c64

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_Frames
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_FramesLemmas
import Theorems.Thm_Formalism_L2_DIV_majAt_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder MatrixOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.DivisionValues
namespace Formalism.L2.DIV
theorem _root_.solution {K : Type} [Field K] [NumberField K] {n : ℕ}
    (X X2 : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (v : InfinitePlace K) (h : X v = X2 v)
    (x y : Fin n → K) : Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v x y =
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X2 v x y := by
  rw [majAt_eq, majAt_eq, h]
end Formalism.L2.DIV
