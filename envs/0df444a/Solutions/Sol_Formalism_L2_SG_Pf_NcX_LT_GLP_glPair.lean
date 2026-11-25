-- Prove2me | solution 1 for Formalism.L2.SG.Pf.NcX.LT.GLP.glPair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:29:14.709891+00:00
-- url     : https://prove2.me/submissions/0e54f461-aece-4b7c-b8cf-32686b11894a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_NcXGLP
import Theorems.Thm_Formalism_L2_SG_Pf_NcX_LT_GLP_trans_tuple
import Theorems.Thm_Formalism_L2_SG_Pf_NcX_LT_GLP_fix_tuple

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.NcX Formalism.L2.SG.Pf.NcX.LT Formalism.L2.SG.Pf.NcX.LT.GLP
variable {K : Type*} [Field K]
namespace Formalism.L2.SG.Pf.NcX.LT.GLP
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {a : ℕ}
    (x y : Fin a → V) (ξ η : Fin a → Module.Dual K V) (hx : LinearIndependent K x)
    (hy : LinearIndependent K y) (hξ : LinearIndependent K ξ) (hη : LinearIndependent K η)
    (h : ∀ i j, ξ i (x j) = η i (y j)) :
    ∃ A : V ≃ₗ[K] V, (∀ j, A (x j) = y j) ∧ ∀ i v, η i (A v) = ξ i v := by
  obtain ⟨A0, hA0⟩ := trans_tuple x y hx hy
  set η' : Fin a → Module.Dual K V := fun i => η i ∘ₗ A0.toLinearMap
  have hη' : LinearIndependent K η' := by
    rw [Fintype.linearIndependent_iff] at hη ⊢
    intro c hc i
    apply hη c _ i
    ext v
    have e := LinearMap.congr_fun hc (A0.symm v)
    simpa [η'] using e
  obtain ⟨B, hBx, hB⟩ := fix_tuple x hx ξ η' hξ hη' (fun i j => by simp [η', hA0, h])
  refine ⟨B.trans A0, fun j => by simp [hBx, hA0], fun i v => ?_⟩
  simpa [η'] using hB i v
end Formalism.L2.SG.Pf.NcX.LT.GLP
