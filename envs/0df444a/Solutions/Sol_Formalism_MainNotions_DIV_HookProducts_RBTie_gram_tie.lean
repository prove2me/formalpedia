-- Prove2me | solution 1 for Formalism.MainNotions.DIV.HookProducts.RBTie.gram_tie
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:26:43.940913+00:00
-- url     : https://prove2.me/submissions/9d79992c-82ff-4dba-b316-f31a95da5947

import Mathlib
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_SharpRestriction_Divisibility_HookProducts_RBTieFrame
import Theorems.Thm_Formalism_MainNotions_DIV_HookProducts_RBTie_sum_star_mulVec_single
import Theorems.Thm_Formalism_MainNotions_DIV_HookProducts_RBTie_fcoord_e
import Theorems.Thm_Formalism_MainNotions_DIV_HookProducts_RBTie_fcoord_std
import Theorems.Thm_Formalism_MainNotions_DIV_HookProducts_RBTie_emb_single

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField Module
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.DIV Formalism.MainNotions.DIV.HookProducts Formalism.MainNotions.DIV.HookProducts.RBTie
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ}
namespace Formalism.MainNotions.DIV.HookProducts.RBTie
theorem _root_.solution (b : Basis ι K V) (XA : InfinitePlace K → Matrix ι ι ℂ) (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (e : (Fin d → K) ≃ₗ[K] V)
    (h : ∀ v x y, Formalism.HermitianLatticesTheory.majAt b XA v (e x) (e y) = Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) X v x y)
    (v : InfinitePlace K) :
    ((XA v)⁻¹ * cP b e v)ᴴ * ((XA v)⁻¹ * cP b e v) = ((X v)⁻¹)ᴴ * (X v)⁻¹ := by
  ext k l
  have h1 := h v (Pi.single k (1 : K) : Fin d → K) (Pi.single l (1 : K) : Fin d → K)
  unfold Formalism.HermitianLatticesTheory.majAt at h1
  rw [fcoord_e, fcoord_e, fcoord_std, fcoord_std, emb_single, emb_single] at h1
  rw [← sum_star_mulVec_single, ← sum_star_mulVec_single]
  exact h1
end Formalism.MainNotions.DIV.HookProducts.RBTie
