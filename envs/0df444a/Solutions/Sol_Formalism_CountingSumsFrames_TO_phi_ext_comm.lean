-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.phi_ext_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:54:28.726268+00:00
-- url     : https://prove2.me/submissions/e30c864a-af2e-46be-ad15-28ea06a3efc1

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_CountingSumsFrames_TO_ext_ops_comm
import Theorems.Thm_P2M_Formalism_CountingSumsFrames_TO_phi_mem__0ab8febbb6ce
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
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
variable (L : Letters N) (T : TieData) (hadm : T.Admissible L) (i : Fin T.t)
include hadm
namespace Formalism.CountingSumsFrames.TO
theorem _root_.solution (j : Fin T.t) (hij : i < j)
    (φ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hφ : ∀ x, IsF (fsj N r (T.pos i + 1 + 1)) (φ x)) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    ext (fsj N r (T.pos i + 1 + 1)) φ (T.phi p L j x) = T.phi p L j (ext (fsj N r (T.pos i + 1 + 1)) φ x) := by
  have hK := hK_of_adm L T hadm j
  have hlt : T.pos i < T.pos j := hadm.1 hij
  have hne : T.pos j ≠ T.pos i + 1 := by
    intro he
    obtain ⟨h1, -, hb⟩ := hadm.2.1 i
    obtain ⟨h2, ha, -⟩ := hadm.2.1 j
    have : (⟨T.pos j, by omega⟩ : Fin N) = ⟨T.pos i + 1, h1⟩ := Fin.ext he
    rw [this, hb] at ha
    exact Bool.false_ne_true ha
  refine ext_ops_comm (fsj N r (T.pos i + 1 + 1)) _ (fun v hv => ?_) (phi_mem' L T j (by omega)) φ hφ x
  simp only [fsj]
  rcases hv with hv | hv <;> omega
end Formalism.CountingSumsFrames.TO
