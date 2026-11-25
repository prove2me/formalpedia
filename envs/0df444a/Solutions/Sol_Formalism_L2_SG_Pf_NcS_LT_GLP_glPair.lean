-- Prove2me | solution 1 for Formalism.L2.SG.Pf.NcS.LT.GLP.glPair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:44:24.953935+00:00
-- url     : https://prove2.me/submissions/3788cfce-a6e4-4fb7-bf41-1266ed036247

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_NcSGLP
import Theorems.Thm_Formalism_L2_SG_Pf_NcS_LT_GLP_trans_tuple
import Theorems.Thm_Formalism_L2_SG_Pf_NcS_LT_GLP_fix_tuple

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.NcS Formalism.L2.SG.Pf.NcS.LT Formalism.L2.SG.Pf.NcS.LT.GLP
variable {K : Type*} [Field K]
namespace Formalism.L2.SG.Pf.NcS.LT.GLP
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {a : ℕ}
    (x y : Fin a → V) (ξ η : Fin a → Module.Dual K V) (hx : LinearIndependent K x)
    (hy : LinearIndependent K y) (hξ : LinearIndependent K ξ) (hη : LinearIndependent K η)
    (h : ∀ i j, ξ i (x j) = η i (y j)) :
    ∃ A : V ≃ₗ[K] V, (∀ j, A (x j) = y j) ∧ ∀ i v, η i (A v) = ξ i v := by
  obtain ⟨A0, hA0⟩ := trans_tuple x y hx hy
  have hψ' : LinearIndependent K (fun i => (η i).comp A0.toLinearMap) := by
    rw [Fintype.linearIndependent_iff] at hη ⊢
    intro g hg
    apply hη g
    refine LinearMap.ext fun v => ?_
    have hgv := LinearMap.congr_fun hg (A0.symm v)
    first
    | simpa using hgv
    | simpa [LinearMap.sum_apply] using hgv
  obtain ⟨B, hB1, hB2⟩ := fix_tuple x hx ξ
    (fun i => (η i).comp A0.toLinearMap) hξ hψ' (fun i j => by
      show ξ i (x j) = η i (A0 (x j))
      rw [hA0 j, h i j])
  refine ⟨B.trans A0, fun j => ?_, fun i v => ?_⟩
  · rw [LinearEquiv.trans_apply, hB1 j, hA0 j]
  · rw [LinearEquiv.trans_apply]
    exact hB2 i v
end Formalism.L2.SG.Pf.NcS.LT.GLP
