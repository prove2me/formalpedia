-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.mem_vars_blkProdG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T06:05:24.205849+00:00
-- url     : https://prove2.me/submissions/a80555ce-4621-4584-a9b0-9dfd8d3f6492

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_PderivSubGOff
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieMemCHarm
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h3
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
namespace Formalism.L2.FormalSeriesBounds.RF
theorem _root_.solution {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {Orb : Type} [Fintype Orb]
    {I J : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)]
    {X : ∀ o, RowData C V d (I o) (J o)} {F : ∀ o, Flag (X o)} {n : ℕ} {L : Orb → List (GlobalTheory d × ℝ)}
    {pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin n} {b : Fin n} {o : Orb} {w : WV (I o)}
    (hx : ((b, ⟨o, w⟩) : Fin n × WVO I) ∈ (blkProd X F n L pl).vars) :
    (b, w) ∈ (prodAll (plAt n pl o) fun i => (blkAt L o i).poly (X o) (F o)).vars := by
  first
  | unfold blkProd at hx
  | simp only [blkProd] at hx
  first
  | unfold toAll at hx
  | simp only [toAll] at hx
  have h1 := MvPolynomial.vars_prod _ hx
  rw [Finset.mem_biUnion] at h1
  obtain ⟨o', -, h2⟩ := h1
  have h3 := MvPolynomial.vars_rename _ _ h2
  rw [Finset.mem_image] at h3
  obtain ⟨x, hx1, hx2⟩ := h3
  simp only [Prod.mk.injEq, Sigma.mk.inj_iff] at hx2
  obtain ⟨hb, ho, hw⟩ := hx2
  subst ho
  obtain rfl := eq_of_heq hw
  subst hb
  exact hx1
end Formalism.L2.FormalSeriesBounds.RF
