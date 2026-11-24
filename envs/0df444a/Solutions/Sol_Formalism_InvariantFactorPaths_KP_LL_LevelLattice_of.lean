-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.LevelLattice_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:08:04.900298+00:00
-- url     : https://prove2.me/submissions/fbaaebcc-c4f0-4565-b818-d771774ac651

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LevelLatticeOf
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_asm_num
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_asm_chain
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_asm_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.KP Formalism.InvariantFactorPaths.KP.LL
open Formalism.GM
open MvPolynomial Finset Formalism.GM.M
namespace Formalism.InvariantFactorPaths.KP.LL
theorem _root_.solution : MidTop → MidPEq → JoinCondition → PlusCondition → Formalism.GM.M.LevelLattice := by
  intro hTop hPEq hTie hPlus p _ N r _ D a hOK hr ha hdeg hB hz hzP hYT hYU
  have hnum := asm_num p a r ha
  generalize ⌈((r : ℝ) + 1) * lgV2 p a r⌉₊ = u at hnum ⊢
  have hT : HypJoin p (r := r) D := hYT
  have hU : HypU p (r := r) D := hYU
  obtain ⟨c1, c2⟩ := asm_chain p (fun k => Mid p (r := r) D k) u D.T.t
    (hTie p N r D a u hOK hr hdeg hz hT hnum) D.T.t le_rfl
  obtain ⟨q1, q2⟩ := hPlus p N r D a u hOK hr hdeg hB hzP hU hnum
  rw [← hTop p N r D, ← hPEq p N r D]
  have k1 : ∀ x ∈ Mid p (r := r) D D.T.t, (p : ℚ_[p]) ^ ((D.T.t + 1) * u) • x ∈ MidP p (r := r) D := by
    intro x hx
    have := q1 _ (c1 x hx)
    rwa [smul_smul, ← pow_add, add_comm u, ← Nat.succ_mul] at this
  have k2 : ∀ x ∈ MidP p (r := r) D, (p : ℚ_[p]) ^ ((D.T.t + 1) * u) • x ∈ Mid p (r := r) D D.T.t := by
    intro x hx
    have := c2 _ (q2 x hx)
    rwa [smul_smul, ← pow_add, ← Nat.succ_mul] at this
  exact ⟨le_antisymm (asm_span p _ _ _ k1) (asm_span p _ _ _ k2), k1, k2⟩
end Formalism.InvariantFactorPaths.KP.LL
