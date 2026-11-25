-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.hStabSelf_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:17:26.76075+00:00
-- url     : https://prove2.me/submissions/90094683-baba-4490-807f-808b19364484

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHStab
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePCartSelfSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHStabSelf
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FBChart_self_raw_first_pairing_eq
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_add
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_neg
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FBChart_bil_ad
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_InL_add
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_InL_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_add
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul_int
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_neg
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_bil_int
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_bil_smul_left
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_bil_smul_right
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_fin_two_eq_zero_or_eq_one


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
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries
variable {C : Type} [Field C]
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution : HStabSelfSt := by
  intro C _ _ V O _ _ dd Y d _ I0 _ p g c q hty
  have hne : p.ty0 c ≠ p.ty0 q + p.hd := by
    rcases fin_two_eq_zero_or_eq_one g with rfl | rfl
    · exact hty
    · intro e
      apply hty
      show p.ty0 c + p.hd = p.ty0 q
      rw [e, add_assoc, p.hd_two, add_zero]
  obtain ⟨a, ha⟩ := p.em_sep _ _ hne
  have hb := Y.bil_ad a (p.e c) (p.e q)
  rw [p.e_eig c a, p.e_eig q (star a), p.em_conj, bil_smul_left, bil_smul_right, ← sub_mul] at hb
  have hint : V.Ge 0 (bil (Y.B.ad a) (p.e c) (p.e q)) := bil_int (Y.intAd a) (p.e_int c) (p.e_int q)
  rw [hb] at hint
  have hβ : V.Ge 0 (bil Y.h (p.e c) (p.e q)) := by
    unfold VF.Ge at hint ⊢
    rwa [V.v.map_mul, ha, zero_add] at hint
  have hgm : ∀ a r s, V.Ge 0 (p.gm a r s) := by
    obtain ⟨M, hM⟩ := p.gm_lim 0
    intro a r s
    have h1 : V.Ge 0 (p.gm a r s - p.em a (M r s)) := by simpa using hM a r s
    have h2 := h1.add (p.em_int a (M r s))
    simpa using h2
  show V.Ge 0 ((Y.rawSelf p).sg1 (fun x => p.gm (p.ty0 c) x.1 g * p.e c x.2)
    (fun x => p.gm (p.ty0 q) x.1 (1 - g) * p.e q x.2))
  rw [Y.self_raw_first_pairing_eq]
  apply VF.Ge.neg
  apply VF.Ge.sum
  intro col _
  show V.Ge 0 (bil Y.h (p.gm (p.ty0 c) col g • p.e c) (p.gm (p.ty0 q) col (1 - g) • p.e q))
  rw [bil_smul_left, bil_smul_right]
  exact (hgm _ _ _).mul_int ((hgm _ _ _).mul_int hβ)
end Formalism.L2.FormalSeriesBounds
