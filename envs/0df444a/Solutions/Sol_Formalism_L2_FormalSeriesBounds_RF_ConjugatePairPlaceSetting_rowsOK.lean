-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.ConjugatePairPlaceSetting.rowsOK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:59:31.877737+00:00
-- url     : https://prove2.me/submissions/f20382fa-7c22-43ac-92ab-b080684a6c64

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipNormOne
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_FinTwoNeOneSub
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_exists_rowsOK
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_le_sum_map
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_plAt_inj
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_rowsOK_prodAll


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
theorem _root_.solution (H : ConjugatePairPlaceSetting r cc a tau X F Z ga n L pl) (o : Orb) :
    ∃ kind : Fin n → Knd d, RowsOK (X o).G (X o).Alt
      (prodAll (plAt n pl o) fun i => (blkAt L o i).poly (X o) (F o)) kind := by
  have h : ∀ i : Fin (L o).length, ∃ kind : Fin (rowsAt X L o i) → Knd d,
      RowsOK (X o).G (X o).Alt ((blkAt L o i).poly (X o) (F o)) kind := by
    intro i
    by_cases ho : o ∈ Z
    · refine exists_rowsOK (X o) (F o) (H.dich o ho) (H.hj o ho) _ fun g t k hk => (H.supp o ho g t k ?_).2
      rw [← H.wt o ho g t k]
      have h : (blkAt L o i).wt (X o) g t k ≤ ((L o).map fun q => q.1.wt (X o) g t k).sum :=
        le_sum_map (L o) (fun q => q.1.wt (X o) g t k) (List.get_mem (L o) i)
      omega
    · have h0 : (L o).length = 0 := by rw [H.off o ho]; rfl
      exact absurd i.2 (by omega)
  choose kind hk using h
  exact ⟨_, rowsOK_prodAll _ _ (plAt_inj n H.plinj o) _ kind hk⟩
end ConjugatePairPlaceSetting
end Formalism.L2.FormalSeriesBounds.RF
