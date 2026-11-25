-- Prove2me | solution 1 for Formalism.L2.Col.XgE_irr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:09:38.834464+00:00
-- url     : https://prove2.me/submissions/221c1121-11f0-46ea-a1ba-c21d9e1a8344

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Columns_GoodXgFin
import Definitions.Def_Formalism_LocalToGlobal_Columns_GoodXgE
import Theorems.Thm_Formalism_L2_Col_mem_XgE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Col
open Formalism.L2.DIV
variable {G : Type} [Group G] [Fintype G] {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Col
theorem _root_.solution {σ : K →+* ℂ} {e : MonoidAlgebra ℂ G} : ∀ χ ∈ XgE σ e, IsAbsIrrChar χ :=
  fun _ h => (mem_XgE.1 h).1
end Formalism.L2.Col
