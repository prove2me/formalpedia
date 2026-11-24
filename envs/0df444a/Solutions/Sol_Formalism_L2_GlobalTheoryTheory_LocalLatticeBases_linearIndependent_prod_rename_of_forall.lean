-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.linearIndependent_prod_rename_of_forall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:23:44.864071+00:00
-- url     : https://prove2.me/submissions/8fb97993-e71a-4394-ac02-566478c33e1b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL6_LinearIndependentProdRenameOfCard
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_LocalLatticeBases_linearIndependent_prod_rename_of_card

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
open MvPolynomial
variable {K : Type*} [Field K] {S₁ S₂ : Type*}
namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
theorem _root_.solution {ι σ : Type} [Fintype ι] [DecidableEq ι] (κ : ι → Type) (b : ∀ τ, κ τ → MvPolynomial σ K)
    (hb : ∀ τ, LinearIndependent K (b τ)) :
    LinearIndependent K (fun g : (∀ τ, κ τ) => ∏ τ, rename (Prod.mk τ) (b τ (g τ))) := by
  exact linearIndependent_prod_rename_of_card _ ι rfl κ b hb
end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
