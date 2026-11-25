-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.Ffull_pol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:57:16.375153+00:00
-- url     : https://prove2.me/submissions/aa2d9e6f-8202-4fed-9c09-5370ca9d81b6

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_isWH_rename
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_pol_iff
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_isWH_hom
import Theorems.Thm_P2M_Formalism_GM_DimensionMonotonicity__F_val_6b0203f3e58f
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_inclusion_prodMap_injective
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_Ffull_eq
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_setTies_deg_eta
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_snoc_deg_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_snoc_deg_last
import Theorems.Thm_Formalism_GM_M_FB_evVal_castSucc
import Theorems.Thm_Formalism_GM_M_FB_evVal_last
import Theorems.Thm_Formalism_GM_M_FB_ext_castSucc
import Theorems.Thm_Formalism_GM_M_FB_ext_last
import Theorems.Thm_Formalism_GM_M_FB_res_apply
import Theorems.Thm_Formalism_GM_M_FB_res_ext
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_last
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_last
import Theorems.Thm_Formalism_GM_extendMapsTo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_castSucc
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_last
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_comb
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_comb
attribute [local simp] Formalism.GM.M.FB.evVal_castSucc
attribute [local simp] Formalism.GM.M.FB.evVal_last
attribute [local simp] Formalism.GM.M.FB.ext_castSucc
attribute [local simp] Formalism.GM.M.FB.ext_last
attribute [local simp] Formalism.GM.M.FB.res_apply
attribute [local simp] Formalism.GM.M.FB.res_ext
attribute [local simp] Formalism.GM.M.FB.snoc_deg_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_deg_last
attribute [local simp] Formalism.GM.M.FB.snoc_vec_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_vec_last



set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
variable [NeZero N] (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t)
include hadm
namespace Formalism.GM.DimensionMonotonicity
theorem _root_.solution (ρ : Fin r) (n : Fin T.t → ℕ) (f : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p])
    (hfP : f ∈ Pol p r ((LL.setTies T n).takeD (T.pos i + 1)))
    (hS : ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ n i) :
    T.Ffull p (LL.setTies T n) i ρ (n i) f ∈ Pol p r (Lz (LL.setTies T n) (T.pos i + 1 + 1)) := by
  classical
  have hK := hK_of_adm LL T hadm i
  set LLK := (LL.setTies T n).takeD (T.pos i + 1) with hLLK
  have h1 := (Formalism.GM.extendMapsTo p (T.pos i + 1) r LLK ρ (n i) hS f hfP).1
  rw [pol_iff] at h1 ⊢
  let E : (Fin (T.pos i + 1 + 1) → ℤ) →+ (Fin N → ℤ) :=
    { toFun := fun g b => if h : (b : ℕ) < T.pos i + 1 + 1 then g ⟨b, h⟩ else 0
      map_zero' := by funext b; simp
      map_add' := by intro g g'; funext b; simp only [Pi.add_apply]; split_ifs <;> simp }
  have h2 := isWH_hom E _ h1
  have hw : E ∘ wL (T.pos i + 1 + 1) r = wL N r ∘ (fun x : Fin (T.pos i + 1 + 1) × Fin r => (ιF N (T.pos i + 1) x.1, x.2)) := by
    funext x b
    simp only [Function.comp, E, AddMonoidHom.coe_mk, ZeroHom.coe_mk, wL]
    by_cases h : b = ιF N (T.pos i + 1) x.1
    · subst h
      have hlt : ((ιF N (T.pos i + 1) x.1 : Fin N) : ℕ) < T.pos i + 1 + 1 := by rw [ιF_val hK]; exact x.1.isLt
      rw [dif_pos hlt, Pi.single_eq_same]
      have : (⟨_, hlt⟩ : Fin (T.pos i + 1 + 1)) = x.1 := Fin.ext (ιF_val hK _)
      rw [this, Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne h]
      split_ifs with hb
      · rw [Pi.single_eq_of_ne]
        intro h'; apply h; apply Fin.ext; rw [ιF_val hK, ← h']
      · rfl
  rw [hw] at h2
  have h3 := isWH_rename (K := ℚ_[p]) (wL N r) _ (inclusion_prodMap_injective (r := r) hK) h2
  rw [Ffull_eq]
  convert h3 using 1
  funext b
  simp only [E, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Lz]
  by_cases hb : (b : ℕ) < T.pos i + 1 + 1
  · rw [dif_pos hb, if_pos hb]
    by_cases hb2 : (b : ℕ) < T.pos i + 1
    · have : (⟨b, hb⟩ : Fin (T.pos i + 1 + 1)) = Fin.castSucc ⟨b, hb2⟩ := rfl
      rw [this, Formalism.GM.M.FB.snoc_deg_castSucc]
      simp [hLLK, Letters.takeD, b.isLt]
    · have : (⟨b, hb⟩ : Fin (T.pos i + 1 + 1)) = Fin.last _ := by apply Fin.ext; simp; omega
      rw [this, Formalism.GM.M.FB.snoc_deg_last]
      have hb3 : b = ⟨T.pos i + 1, by omega⟩ := by apply Fin.ext; simp; omega
      rw [hb3, setTies_deg_eta LL T hadm i n]
  · rw [dif_neg hb, if_neg hb]; simp
end Formalism.GM.DimensionMonotonicity
