-- Prove2me | solution 1 for Formalism.L2.Col.absIrrChar_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:16:57.819271+00:00
-- url     : https://prove2.me/submissions/2e26e8e3-bbc6-4b88-bead-5348ef8e0441

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Columns_GoodXgFin
import Theorems.Thm_Formalism_L2_Col_gxIrrSet_finite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Col
open Formalism.L2.DIV
variable {G : Type} [Group G] [Fintype G]
namespace Formalism.L2.Col
theorem _root_.solution {K : Type} [Field K] [CharZero K] : {χ : G → K | IsAbsIrrChar χ}.Finite := by
  haveI : CharZero (AlgebraicClosure K) :=
    charZero_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective
  apply Set.Finite.of_finite_image (f := fun χ : G → K => fun t => algebraMap K (AlgebraicClosure K) (χ t))
  · apply (gxIrrSet_finite (G := G) (k := AlgebraicClosure K)).subset
    rintro _ ⟨χ, ⟨n, ρ, hρ, hχ⟩, rfl⟩
    exact ⟨n, ρ, hρ, funext hχ⟩
  · intro a _ b _ hab
    funext t
    exact (algebraMap K (AlgebraicClosure K)).injective (congrFun hab t)
end Formalism.L2.Col
