-- Prove2me | solution 1 for Formalism.L2.Pj.sum_castLE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:16:41.522682+00:00
-- url     : https://prove2.me/submissions/7701fed8-cea1-4d63-9f92-a84b7c2b0dc5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnifDom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex
open scoped ComplexConjugate Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace Formalism.L2.Pj
theorem _root_.solution {R : Type} [AddCommMonoid R] {i n : ℕ} (h : i ≤ n) (f : Fin n → R)
    (hf : ∀ c : Fin n, i ≤ (c : ℕ) → f c = 0) : ∑ c, f c = ∑ c : Fin i, f (Fin.castLE h c) := by
  refine (Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h)
    (fun c => f (Fin.castLE h c)) f (fun c hc => hf c ?_) (fun _ => rfl)).symm
  by_contra hlt
  push_neg at hlt
  exact hc ⟨⟨c, hlt⟩, rfl⟩
end Formalism.L2.Pj
