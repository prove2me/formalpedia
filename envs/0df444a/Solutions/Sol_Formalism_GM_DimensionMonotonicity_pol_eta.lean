-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.pol_eta
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:49:01.952842+00:00
-- url     : https://prove2.me/submissions/70619499-e191-4856-9579-1703d6391822

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_pol_iff
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_eta_wL
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
open Formalism Formalism.GM Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.GM.DimensionMonotonicity
theorem _root_.solution (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t) (n : Fin T.t → ℕ)
    (n' : ℕ) (hn : n i ≤ n') (ρ : Fin r)
    {z : MvPolynomial (Fin N × Fin r) ℚ_[p]} (L0 L1 : Letters N)
    (h0 : ∀ b : Fin N, (b : ℕ) ≠ T.pos i + 1 → L1.deg b = L0.deg b)
    (h1 : ∀ b : Fin N, (b : ℕ) = T.pos i + 1 → L0.deg b = n i ∧ L1.deg b = n')
    (hz : z ∈ Pol p r L0) :
    X (⟨T.pos i + 1, by have := hK_of_adm LL T hadm i; omega⟩, ρ) ^ (n' - n i) * z ∈ Pol p r L1 := by
  rw [pol_iff] at hz ⊢
  have := (eta_wL (p := p) (r := r) ⟨T.pos i + 1, by have := hK_of_adm LL T hadm i; omega⟩ ρ (n' - n i)).mul hz
  convert this using 1
  funext b
  simp only [Pi.add_apply, Pi.single_apply]
  by_cases hb : (b : ℕ) = T.pos i + 1
  · have hb' : b = ⟨T.pos i + 1, by have := hK_of_adm LL T hadm i; omega⟩ := Fin.ext hb
    rw [if_pos hb', (h1 b hb).1, (h1 b hb).2]; push_cast [Nat.cast_sub hn]; ring
  · have hb' : b ≠ ⟨T.pos i + 1, by have := hK_of_adm LL T hadm i; omega⟩ := fun h => hb (by rw [h])
    rw [if_neg hb', h0 b hb, zero_add]
end Formalism.GM.DimensionMonotonicity
