-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.blkAdmC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:45:32.451557+00:00
-- url     : https://prove2.me/submissions/8b47924b-9f46-499a-8223-fd39350cb728

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipSelfConjugate
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAdm
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_big_one_iff
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_attainsOK_of
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_le_sum_map
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_rkF_eq_of_big_iff
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_zmod_two_add_one_add_one
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_zmod_two_even_succ_iff
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
open Formalism.IncomingBounds
variable {C : Type} [Field C] {V : VF C}
  {Orb : Type} [Fintype Orb] {I J : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)]
  (X : ∀ o, RowData C V 2 (I o) (J o)) (F : ∀ o, Flag (X o)) (gaC : Orb → ZMod 2 → ℕ → ℕ)
namespace Formalism.L2.FormalSeriesBounds.RF
theorem _root_.solution (hA : ∀ o, (X o).Alt) (hj : ∀ o, (X o).j' < (X o).n)
    (hga : ∀ o s k, gaC o s k ≠ 0 → k ≤ (X o).rkF 0 s) : BlockAdmissibleSelfConjugate X F gaC := by
  intro L hwt o q hq hatt
  refine attainsOK_of _ _ (Or.inl (hA o)) (hj o) q.1 q.2 (fun g a k hk => ?_) hatt
  have hg : g = 0 ∨ g = 1 := by fin_cases g <;> simp
  rcases hg with rfl | rfl
  · apply hga o a k
    rw [← hwt o a k]
    have h : q.1.wt (X o) 0 a k + q.1.wt (X o) 1 (a + 1) k ≤ _ :=
      le_sum_map (L o) (fun q => q.1.wt (X o) 0 a k + q.1.wt (X o) 1 (a + 1) k) hq
    omega
  · have hk' : q.1.wt (X o) 1 (a + 1 + 1) k ≠ 0 := by rwa [zmod_two_add_one_add_one]
    have h1 : k ≤ (X o).rkF 0 (a + 1) := by
      apply hga o (a + 1) k
      rw [← hwt o (a + 1) k]
      have h : q.1.wt (X o) 0 (a + 1) k + q.1.wt (X o) 1 (a + 1 + 1) k ≤ _ :=
        le_sum_map (L o) (fun q => q.1.wt (X o) 0 (a + 1) k + q.1.wt (X o) 1 (a + 1 + 1) k) hq
      omega
    have h2 : (X o).big 0 (a + 1) ↔ (X o).big 1 a := by
      rw [big_one_iff, (hA o).2 (a + 1), (hA o).2 a]
      exact zmod_two_even_succ_iff a
    rwa [rkF_eq_of_big_iff h2] at h1
end Formalism.L2.FormalSeriesBounds.RF
