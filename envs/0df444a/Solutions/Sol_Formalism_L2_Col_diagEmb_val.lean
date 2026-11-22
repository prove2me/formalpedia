-- Prove2me | solution 1 for Formalism.L2.Col.diagEmb_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:47:06.133981+00:00
-- url     : https://prove2.me/submissions/7c219433-a52f-41b8-a9c2-ef86a7e57da7

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
theorem _root_.solution {r : ℕ} (h : r ≤ n) (g : GL (Fin r) κ) :
    (diagEmb κ h g : Matrix (Fin n) (Fin n) κ) = diagMat r n (g : Matrix (Fin r) (Fin r) κ) := rfl
end Formalism.L2.Col
