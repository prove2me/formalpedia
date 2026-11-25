-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.transferMuMax_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:08:00.015332+00:00
-- url     : https://prove2.me/submissions/af346cd6-7ba6-42f3-8a49-39c78c7ddd6f

import Mathlib
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementL
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_TransferMean
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_GoodBadCut
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Transfer
import Theorems.Thm_Formalism_BranchingDeterminantCap_PrismTransfer_natCast_smul_eq
import Theorems.Thm_Formalism_BranchingDeterminantCap_PrismTransfer_blockDiag_det
import Theorems.Thm_Formalism_BranchingDeterminantCap_PrismTransfer_opNormAt_colMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_PrismTransfer_htMap_le
import Theorems.Thm_Formalism_BranchingDeterminantCap_PrismTransfer_log_bound
import Theorems.Thm_Formalism_BranchingDeterminantCap_PrismTransfer_pow_smul_eq
import Theorems.Thm_P2M_Formalism_BranchingDeterminantCap_PrismTransfer_pow_ne_zero__012ddc03cd71
import Theorems.Thm_Formalism_BranchingDeterminantCap_PrismTransfer_colMap_injOn
import Theorems.Thm_Formalism_BranchingDeterminantCap_PrismTransfer_colMap_map_le
import Theorems.Thm_Formalism_HN_slope_inequality_mean


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
open scoped Matrix
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
open Formalism.HN
open PrismTransfer
open PrismTransfer
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution (hSc : ScaleSandwich) (hOrth : OrthSum) (hPow : PowMu) : TransferMuMax := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X hX S _ A B A0 C G n xs hA0 hC hA0ne hG hnG horth hBle hGmem hAC
    hxs hxs1 hinj
  have hG0 : (G : K) ≠ 0 := by exact_mod_cast hG.ne'
  have hBfg : ∀ s, (B s).FG := fun s => Submodule.FG.of_le hA0 (hBle s)
  have hsup0 : (⨆ s, B s) ≠ ⊥ := by
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hA0ne
    intro h
    have h1 := hGmem a ha
    rw [h, Submodule.mem_bot, natCast_smul_eq] at h1
    exact ha0 ((smul_eq_zero.1 h1).resolve_left hG0)
  have s1 := (hSc K V ι b X hX A0 (⨆ s, B s) G hA0 hA0ne hG (iSup_le hBle) hGmem).2.2.2.2
  have hlG : 0 ≤ Real.log G := Real.log_natCast_nonneg G
  have s2 := (hOrth K V ι b X hX S B hBfg horth).2.2 (muMaxDef b X C + 13 / 2 * Real.log G)
    (fun s hs => by
      have hn : 0 < n s := by
        rcases Nat.eq_zero_or_pos (n s) with h0 | h0
        · exfalso
          apply hs
          rw [Submodule.eq_bot_iff]
          intro c hc
          refine hinj s c hc fun i => ?_
          exact absurd i.2 (by omega)
        · exact h0
      have hC0 : C ≠ ⊥ := by
        intro h
        apply hs
        rw [Submodule.eq_bot_iff]
        intro c hc
        refine hinj s c hc fun i => ?_
        have h1 := hAC s (hxs s i c hc)
        rw [h, Submodule.mem_bot, pow_smul_eq] at h1
        exact (smul_eq_zero.1 h1).resolve_left (pow_ne_zero' G hG)
      obtain ⟨_, _, p3⟩ := hPow K V ι b X hX C (n s) hC hC0 hn
      have hXn : ∀ v, IsUnit (Matrix.blockDiagonal' fun _ : Fin (n s) => X v).det :=
        fun v => blockDiag_det (X v) (hX v)
      have hCn : (Submodule.pi Set.univ fun _ : Fin (n s) => C).FG := Submodule.fg_pi fun _ => hC
      have hio := colMap_injOn G hG (xs s) (B s) (hinj s)
      have hne : (B s).map ((colMap ((G : K) ^ 3) (xs s)).restrictScalars (𝓞 K)) ≠ ⊥ := by
        obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hs
        intro h
        have h1 : colMap ((G : K) ^ 3) (xs s) c ∈
            (B s).map ((colMap ((G : K) ^ 3) (xs s)).restrictScalars (𝓞 K)) := ⟨c, hc, rfl⟩
        rw [h, Submodule.mem_bot] at h1
        exact hc0 (hio hc (B s).zero_mem (by rw [h1, map_zero]))
      have d := ((slope_inequality_mean K V ι (Fin (n s) → V) (Σ _ : Fin (n s), ι) b X
        (Pi.basis fun _ : Fin (n s) => b) (fun v => Matrix.blockDiagonal' fun _ : Fin (n s) => X v)
        hX hXn (colMap ((G : K) ^ 3) (xs s)) (B s) (hBfg s) hne).2
        (Submodule.pi Set.univ fun _ : Fin (n s) => C) hCn
        (colMap_map_le G (xs s) C (B s) fun i c hc => hAC s (hxs s i c hc))).2 hio
      obtain ⟨hb1, hb2⟩ := log_bound G (n s) hG hn
      have e := htMap_le b X (Pi.basis fun _ : Fin (n s) => b)
        (fun v => Matrix.blockDiagonal' fun _ : Fin (n s) => X v) (colMap ((G : K) ^ 3) (xs s)) _ hb1
        (fun v => opNormAt_colMap b X hX G (xs s) v fun i => hxs1 s i v)
      rw [hb2] at e
      rw [p3] at d
      have hl : 2 * Real.log (n s) ≤ Real.log G := by
        have h1 : Real.log (((n s : ℕ) : ℝ) ^ 2) ≤ Real.log G :=
          Real.log_le_log (by positivity) (by exact_mod_cast hnG s)
        rw [Real.log_pow] at h1
        exact_mod_cast h1
      linarith) hsup0
  linarith
end Formalism.BranchingDeterminantCap
