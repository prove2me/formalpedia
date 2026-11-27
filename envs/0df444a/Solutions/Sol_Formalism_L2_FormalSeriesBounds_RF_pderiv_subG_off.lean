-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.pderiv_subG_off
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T06:05:33.909031+00:00
-- url     : https://prove2.me/submissions/5887f6db-5d59-4640-8899-3a2328a81fc4

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipSelfConjCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieMemCDeg
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_FinTwoNeOneSub
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_PderivSubGOff
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_chain_aeval
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt



set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial
variable {C : Type} [Field C] {T Orb : Type} [Fintype Orb] {r : T → ℕ} {tau : Orb → ZMod 2 → T}
  {gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C} {N n : ℕ} (plc : Fin N × Fin 2 ↪ Fin n)
namespace Formalism.L2.FormalSeriesBounds.RF
theorem _root_.solution {p : MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C} {ℓ : Letter T r n}
    (h : ∀ z, ℓ ≠ lam r tau plc z) : pderiv ℓ (subG r tau gm plc p) = 0 := by
  rw [chain_aeval]
  refine Finset.sum_eq_zero fun y _ => ?_
  have hX : pderiv ℓ (subG r tau gm plc (X y)) = 0 := by
    unfold subG
    rw [MvPolynomial.aeval_X, map_sum]
    refine Finset.sum_eq_zero fun col _ => ?_
    rw [Derivation.leibniz, MvPolynomial.pderiv_C, smul_zero, add_zero, MvPolynomial.pderiv_X]
    have hne : (⟨tau y.2.1 y.2.2.2.1, y.2.2.2.2, plc (y.1, col)⟩ : Letter T r n) ≠ ℓ := by
      intro heq
      apply h (((eW r tau N) y).1, col)
      rw [← heq]
      rfl
    simp [Pi.single_apply, hne]
  rw [hX, mul_zero]
end Formalism.L2.FormalSeriesBounds.RF
