-- Prove2me | solution 1 for Formalism.L2.Col.mem_XgE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:49:20.904044+00:00
-- url     : https://prove2.me/submissions/a3ab2e46-fb8f-4c70-8eb4-91ccaa545d31

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Columns_GoodXgFin
import Definitions.Def_Formalism_LocalToGlobal_Columns_GoodXgE

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
theorem _root_.solution {σ : K →+* ℂ} {e : MonoidAlgebra ℂ G} {χ : G → K} :
    χ ∈ XgE σ e ↔ IsAbsIrrChar χ ∧ ∑ g : G, e.coeff g * σ (χ g) = σ (χ 1) :=
  Set.Finite.mem_toFinset _
end Formalism.L2.Col
