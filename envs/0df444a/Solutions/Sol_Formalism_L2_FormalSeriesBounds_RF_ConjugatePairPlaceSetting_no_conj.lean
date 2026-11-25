-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.ConjugatePairPlaceSetting.no_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:07:14.63794+00:00
-- url     : https://prove2.me/submissions/672b24e8-c96f-404d-9799-2b26df82de6e

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipNormOne
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_FinTwoNeOneSub
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_no_conj_of_rowsOK
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_ConjugatePairPlaceSetting_rowsOK
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_mem_vars_blkProd
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_fin_two_ne_one_sub
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X


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
open Formalism.IncomingBounds Formalism.L2.Pj
variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {T : Type} {r : T → ℕ} {cc : T → T} {a : T → ℕ → ℕ}
  {Orb : Type} [Fintype Orb] {tau : Orb → Fin 2 → ZMod d → T} {J : Orb → Fin 2 → Type} [∀ o g, Fintype (J o g)]
  {X : ∀ o, RowData C V d (IIof r tau o) (J o)} {F : ∀ o, Flag (X o)} {Z : Finset Orb}
  {ga : Orb → Fin 2 → ZMod d → ℕ → ℕ} {n : ℕ} {L : Orb → List (GlobalTheory d × ℝ)}
  {pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin n}
namespace Formalism.L2.FormalSeriesBounds.RF
namespace ConjugatePairPlaceSetting
theorem _root_.solution (H : ConjugatePairPlaceSetting r cc a tau X F Z ga n L pl) (b : Fin n) (o : Orb) (g : Fin 2) (t : ZMod d)
    (i : Fin (r (tau o g t))) (i' : Fin (r (tau o (1 - g) t)))
    (hx : ((b, ⟨o, ⟨g, ⟨t, i⟩⟩⟩) : Fin n × WVO (IIof r tau)) ∈ (blkProd X F n L pl).vars)
    (hx' : ((b, ⟨o, ⟨1 - g, ⟨t, i'⟩⟩⟩) : Fin n × WVO (IIof r tau)) ∈ (blkProd X F n L pl).vars) : False := by
  obtain ⟨kind, hk⟩ := H.rowsOK o
  refine no_conj_of_rowsOK hk (mem_vars_blkProd hx) (mem_vars_blkProd hx') (fin_two_ne_one_sub g) ?_
  show ((X o).G g).ty (Sum.inl ⟨t, i⟩) = ((X o).G (1 - g)).ty (Sum.inl ⟨t, i'⟩)
  rw [H.hty o g, H.hty o (1 - g)]
end ConjugatePairPlaceSetting
end Formalism.L2.FormalSeriesBounds.RF
