-- Prove2me | solution 1 for Formalism.MainNotions.G.SymmetricFormBlocks.li_rename_mon
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:29:28.762303+00:00
-- url     : https://prove2.me/submissions/3bb3ecc4-d416-4f9c-8869-54bfca0b1501

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SSDirect
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialFactorials_LiRenameMon
import Theorems.Thm_Formalism_MainNotions_G_SymmetricFormBlocks_decode_gen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.SymmetricFormBlocks
open MvPolynomial Finset Formalism.GM.M.SSD
variable {σ τ K : Type} [Field K] [DecidableEq σ] (e : τ → σ) (he : Function.Injective e)
include he
namespace Formalism.MainNotions.G.SymmetricFormBlocks
theorem _root_.solution (M : Finset (σ →₀ ℕ)) (hM : ∀ β ∈ M, ∀ x, β (e x) = 0) {ι : Type} (b : ι → MvPolynomial τ K)
    (hb : LinearIndependent K b) :
    LinearIndependent K (fun q : (Σ _ : M, ι) => rename e (b q.2) * monomial ((q.1 : σ →₀ ℕ)) 1) := by
  apply LinearIndependent.of_comp (decode e he M)
  have h1 : (decode e he M) ∘ (fun q : (Σ _ : M, ι) => rename e (b q.2) * monomial ((q.1 : σ →₀ ℕ)) 1) =
      (Finsupp.linearEquivFunOnFinite K (MvPolynomial τ K) M) ∘
        (fun q : (Σ _ : M, ι) => Finsupp.single q.1 (b q.2)) := by
    funext q
    simp only [Function.comp_apply, Finsupp.linearEquivFunOnFinite_single]
    exact decode_gen e he M hM (b q.2) q.1
  rw [h1]
  first
  | exact (Finsupp.linearIndependent_single (fun _ : M => b) (fun _ => hb)).map' _ (LinearEquiv.ker _)
  | exact (Finsupp.linearIndependent_single (f := fun _ : M => b) (fun _ => hb)).map' _ (LinearEquiv.ker _)
  | exact (Finsupp.linearIndependent_single (v := fun _ : M => b) (fun _ => hb)).map' _ (LinearEquiv.ker _)
end Formalism.MainNotions.G.SymmetricFormBlocks
