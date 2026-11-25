-- Prove2me | solution 1 for Formalism.CountingSumsFrames.pol_comap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:57:10.841404+00:00
-- url     : https://prove2.me/submissions/4d1c1f33-c0d2-483a-9918-86119a2a045d

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
import Theorems.Thm_Formalism_CountingSumsFrames_deg_compat
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_inclusion_prodMap_injective
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
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
import Theorems.Thm_P2M_Formalism_GM_DimensionMonotonicity__F_val_6b0203f3e58f
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
open Formalism Formalism.CountingSumsFrames
open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
variable [NeZero N] (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t)
include hadm
namespace Formalism.CountingSumsFrames
theorem _root_.solution (n : Fin T.t → ℕ) {v' : MvPolynomial (Fin (T.pos i + 1 + 1) × Fin r) ℚ_[p]}
    (hv : rename (fun x : Fin (T.pos i + 1 + 1) × Fin r => (ιF N (T.pos i + 1) x.1, x.2)) v' ∈
      Pol p r (Lz (LL.setTies T n) (T.pos i + 1 + 1))) :
    v' ∈ Pol p r (((LL.setTies T n).takeD (T.pos i + 1)).snoc (n i)) := by
  classical
  have hK := hK_of_adm LL T hadm i
  rw [Pol, mem_restrictSupport_iff]
  intro m' hm' a
  have h1 : Finsupp.mapDomain (fun x : Fin (T.pos i + 1 + 1) × Fin r => (ιF N (T.pos i + 1) x.1, x.2)) m' ∈
      (rename (fun x : Fin (T.pos i + 1 + 1) × Fin r => (ιF N (T.pos i + 1) x.1, x.2)) v').support := by
    rw [support_rename_of_injective (inclusion_prodMap_injective (r := r) hK)]; exact Finset.mem_image_of_mem _ hm'
  have h2 : MultiDeg _ _ := ((mem_restrictSupport_iff ℚ_[p]).mp hv) h1
  have h3 := h2 (ιF N (T.pos i + 1) a)
  have e : ∀ c, Finsupp.mapDomain (fun x : Fin (T.pos i + 1 + 1) × Fin r => (ιF N (T.pos i + 1) x.1, x.2)) m'
      (ιF N (T.pos i + 1) a, c) = m' (a, c) := fun c =>
    Finsupp.mapDomain_apply (inclusion_prodMap_injective (r := r) hK) m' (a, c)
  simp only [e] at h3
  rw [h3, deg_compat LL T hadm i n a]
  have : ((ιF N (T.pos i + 1) a : Fin N) : ℕ) < T.pos i + 1 + 1 := by rw [ιF_val hK]; exact a.isLt
  show (if ((ιF N (T.pos i + 1) a : Fin N) : ℕ) < T.pos i + 1 + 1 then
    (LL.setTies T n).deg (ιF N (T.pos i + 1) a) else 0) = _
  rw [if_pos this]
end Formalism.CountingSumsFrames
