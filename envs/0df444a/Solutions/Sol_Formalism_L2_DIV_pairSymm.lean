-- Prove2me | solution 1 for Formalism.L2.DIV.pairSymm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:16:03.564022+00:00
-- url     : https://prove2.me/submissions/a5c5101a-3edb-44e5-ab3e-9c0c5f591b14

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefModLemmas
import Theorems.Thm_Formalism_L2_DIV_fockSHerm
import Theorems.Thm_P2M_Formalism_L2_DIV_conjTranspose_transpose__09b67af54be3
import Theorems.Thm_Formalism_L2_DIV_fockL_symm
import Theorems.Thm_Formalism_L2_DIV_fockL_blockAct_adj
import Theorems.Thm_Formalism_L2_DIV_pairP_apply
import Theorems.Thm_Formalism_L2_DIV_pairK_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.BasicNotions
namespace Formalism.L2.DIV
theorem _root_.solution : PairSymm := by
  intro K _ _ ι _ n lam G hG
  have hc : star (gramTw lam G / extNorm K lam) = gramTw lam G / extNorm K lam := by
    have h1 : star (gramTw lam G) = gramTw lam G := by
      unfold gramTw
      rw [star_prod]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [star_zpow₀, ← Matrix.det_conjTranspose, hG]
    have h2 : star (extNorm K lam) = extNorm K lam := by
      unfold extNorm
      rw [star_prod]
      refine Finset.prod_congr rfl fun τ _ => ?_
      exact (fockSHerm K _ _ _).symm
    rw [star_div₀, h1, h2]
  have e : (fun τ => ((G τ)ᵀ)ᴴ) = fun τ => (G τ)ᵀ := by
    funext τ
    rw [conjTranspose_transpose', hG]
  rw [LinearMap.isSymm_def]
  intro x y
  rw [pairK_apply, pairK_apply, pairP_apply, pairP_apply, starRingEnd_apply, star_mul', hc, ← fockL_symm,
    fockL_blockAct_adj, e]
end Formalism.L2.DIV
