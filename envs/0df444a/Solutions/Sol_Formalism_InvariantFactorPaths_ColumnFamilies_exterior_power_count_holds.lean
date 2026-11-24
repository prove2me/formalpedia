-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.exterior_power_count_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:13:33.143368+00:00
-- url     : https://prove2.me/submissions/d34d508b-5ab5-480e-bd41-92e70628ffd5

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_CntSym
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QkDetExpand
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_Branch
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_WeylGT
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_CntLam
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qk_W_ne
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qk_D_dom
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qk_v_add
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qk_D_nondom
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qk_mem_strVert
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qk_add_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qk_add_sel
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qk_sel_add
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qk_D_shift
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qk_dMu_eq_dGT


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.InvariantFactorPaths.GelfandTsetlinBases (dGT)
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution : CntLam := by
  classical
  intro n _ mu b hmu
  have hcard : Fintype.card (LamIdx n b) = n.choose b := by
    rw [Fintype.card_finset_len, Fintype.card_fin]
  rw [hcard]
  have hW := qk_W_ne n
  have key : ((dMu mu * n.choose b : ℕ) : ℝ) * vandermondeDenominator n = ((∑ nu ∈ strVert mu b, dMu nu : ℕ) : ℝ) * vandermondeDenominator n := by
    push_cast
    rw [sum_mul]
    have e1 : ∑ nu ∈ strVert mu b, (dMu nu : ℝ) * vandermondeDenominator n = ∑ nu ∈ strVert mu b, qk_D (qk_v nu) := by
      refine sum_congr rfl fun nu hnu => ?_
      have hd := (qk_mem_strVert.1 hnu).2.1
      rw [qk_D_dom hd, qk_dMu_eq_dGT n nu hd]
    have e2 : ∑ s ∈ (powersetCard b (univ : Finset (Fin n))).filter (fun s => Dominant (qk_add mu s)),
        qk_D (qk_v (qk_add mu s)) = ∑ nu ∈ strVert mu b, qk_D (qk_v nu) := by
      refine sum_nbij' (qk_add mu) (fun nu => univ.filter fun a => nu a = mu a + 1) ?_ ?_ ?_ ?_ ?_
      · intro s hs
        rw [mem_filter, mem_powersetCard] at hs
        refine qk_mem_strVert.2 ⟨fun a => ?_, hs.2, ?_⟩
        · unfold qk_add
          split_ifs <;> omega
        · rw [qk_add_sum, hs.1.2]
      · intro nu hnu
        have h := qk_mem_strVert.1 hnu
        rw [mem_filter, mem_powersetCard, qk_add_sel h.1]
        refine ⟨⟨subset_univ _, ?_⟩, h.2.1⟩
        have h3 := qk_add_sum mu (univ.filter fun a => nu a = mu a + 1)
        rw [qk_add_sel h.1, h.2.2] at h3
        exact_mod_cast h3.symm
      · intro s _
        exact qk_sel_add mu s
      · intro nu hnu
        exact qk_add_sel (qk_mem_strVert.1 hnu).1
      · intro s _
        rfl
    have e3 : ∑ s ∈ (powersetCard b (univ : Finset (Fin n))).filter (fun s => Dominant (qk_add mu s)),
        qk_D (qk_v (qk_add mu s)) = ∑ s ∈ powersetCard b (univ : Finset (Fin n)), qk_D (qk_v (qk_add mu s)) := by
      refine sum_filter_of_ne fun s _ hne => ?_
      by_contra hc
      exact hne (qk_D_nondom hmu s hc)
    rw [e1, ← e2, e3]
    simp only [qk_v_add]
    rw [qk_D_shift, qk_D_dom hmu, qk_dMu_eq_dGT n mu hmu]
    ring
  exact_mod_cast mul_right_cancel₀ hW key
end Formalism.InvariantFactorPaths.ColumnFamilies
