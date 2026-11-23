-- Prove2me | solution 1 for Formalism.L2.Col.mem_btG
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:02:55.671072+00:00
-- url     : https://prove2.me/submissions/2d4c7257-85ef-4aae-8480-b3b4807926cd

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
namespace Formalism.L2.Col
theorem _root_.solution {β : ℕ → ℕ} {M : GL (Fin n) κ} :
    M ∈ btG n κ β ↔ ∀ i j : Fin n, β j.val < β i.val → (M : Matrix (Fin n) (Fin n) κ) i j = 0 :=
  ⟨fun h _ _ hij => h hij, fun h i j hij => h i j hij⟩
end Formalism.L2.Col
