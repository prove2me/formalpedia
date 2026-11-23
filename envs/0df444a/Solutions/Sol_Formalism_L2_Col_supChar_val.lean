-- Prove2me | solution 1 for Formalism.L2.Col.supChar_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:18:34.928693+00:00
-- url     : https://prove2.me/submissions/2515858e-30c9-4f1a-a3e4-4d987d581b4a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_Tuples
import Definitions.Def_Formalism_GL3MeanSquares_RankMulPowThreeHalvesLeFourthPower
import Definitions.Def_Formalism_LocalToGlobal_Columns_GenericUnipotentCharacter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset IsDedekindDomain NumberField
open Formalism Formalism.L2 Formalism.L2.Col
variable {n : ℕ} {κ : Type} [CommRing κ]
variable {K : Type} [Field K]
namespace Formalism.L2.Col
theorem _root_.solution (ψ : AddChar κ K) (a : ℕ) (bl : List ℕ) (S : Finset ℕ) (M : ↥(uniUT n κ a bl)) :
    ((supChar ψ n a bl S M : Kˣ) : K) = ψ (supSum a S (M.1 : Matrix (Fin n) (Fin n) κ)) := rfl
end Formalism.L2.Col
