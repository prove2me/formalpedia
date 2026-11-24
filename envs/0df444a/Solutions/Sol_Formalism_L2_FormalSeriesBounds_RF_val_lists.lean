-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.val_lists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:06:51.98102+00:00
-- url     : https://prove2.me/submissions/02a049c5-99e3-40be-a794-44de990bfd5b

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_MemVarsProdAll
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ContentZeroAt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipSelfConjugate
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_sum_get
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_val_pieces
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds
variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I J : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)]
  (X : ∀ o, RowData C V d (I o) (J o)) (n : ℕ)
variable {X n}
namespace Formalism.L2.FormalSeriesBounds.RF
theorem _root_.solution {FFimg : Set (∀ o, MvPolynomial (Fin n × WV (I o)) C)} {ν : ℝ} (hV : ValO X n FFimg ν) (hJ : JetProdSt)
    (F : ∀ o, Flag (X o)) (L : Orb → List (GlobalTheory d × ℝ))
    (hOK : ∀ o, ∀ q ∈ L o, q.1.AttainsOK (X o) (F o) q.2)
    (hrows : (∑ o, ((L o).map fun q => q.1.what₂ (X o).n).sum) ≤ n) (hmem : ProdMem X n F FFimg L) :
    ν ≤ ∑ o, ((L o).map Prod.snd).sum := by
  have hOK' : ∀ o (i : Fin (L o).length), (blkAt L o i).AttainsOK (X o) (F o) ((L o).get i).2 :=
    fun o i => hOK o _ (List.get_mem _ _)
  have hcard : Fintype.card (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) ≤ Fintype.card (Fin n) := by
    rw [Fintype.card_sigma, Fintype.card_fin]
    refine le_trans (le_of_eq ?_) hrows
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    exact sum_get (L o) fun q => q.1.what₂ (X o).n
  obtain ⟨pl⟩ := Function.Embedding.nonempty_of_card_le hcard
  choose kind hrow hatt' using hOK'
  have key := val_pieces hV hJ (fun o => (L o).length) (fun o i => rowsAt X L o i) pl pl.injective
    (fun o i => (blkAt L o i).poly (X o) (F o)) kind (fun o i => ((L o).get i).2) hrow hatt' (hmem pl pl.injective)
  refine key.trans (le_of_eq ?_)
  exact Finset.sum_congr rfl fun o _ => sum_get (L o) Prod.snd
end Formalism.L2.FormalSeriesBounds.RF
