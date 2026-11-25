-- Prove2me | solution 1 for Formalism.L2.DIV.CSD.mem_Forms
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:07:56.640095+00:00
-- url     : https://prove2.me/submissions/093c8d3a-3e3c-49f2-8a1d-f973ca56c84f

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSum
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV Formalism.L2.DIV.CSD
open Formalism.DivisionValues
variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)
namespace Formalism.L2.DIV.CSD
theorem _root_.solution (f : S.Cl → S.V) : f ∈ S.Forms ↔ ∀ c (γ : S.Gam c), S.ρ c γ (f c) = f c := Iff.rfl
end Formalism.L2.DIV.CSD
