-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.centralRenyi_startup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:11:41.4627+00:00
-- url     : https://prove2.me/submissions/cca7bc67-054c-4639-abb6-34bc86f4d4c7

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalNonlinearShell
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiAlpha_lt_log_ratio
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiGap_pos
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_mem_centralSourceSet_inl
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_mem_centralSourceSet_inr
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_mem_sourceLateFirstOdd_inl
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_mem_sourceLateFirstOdd_inr
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_normalizedReverseLift_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseLiftNumerator_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseLiftNumerator_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseMomentMajorant_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseMomentMajorant_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumerator_prependOne
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_wordCorrectionFrom_nil
import Theorems.Thm_CollatzEndpointTransport_OptimizedLinearPullback_psi_zero
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_card_positivePrefix
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_mem_basePullback
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_mem_collatzPullback
import Theorems.Thm_CollatzEndpointTransport_Terras_integerCorrection_zero
attribute [local simp] CollatzEndpointTransport.FixedTotal.encodeBlocks_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.encodeBlocks_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.mem_centralSourceSet_inl
attribute [local simp] CollatzEndpointTransport.FixedTotal.mem_centralSourceSet_inr
attribute [local simp] CollatzEndpointTransport.FixedTotal.mem_sourceLateFirstOdd_inl
attribute [local simp] CollatzEndpointTransport.FixedTotal.mem_sourceLateFirstOdd_inr
attribute [local simp] CollatzEndpointTransport.FixedTotal.normalizedReverseLift_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.reverseLiftNumerator_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.reverseLiftNumerator_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.reverseMomentMajorant_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.reverseMomentMajorant_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumerator_prependOne
attribute [local simp] CollatzEndpointTransport.FixedTotal.wordCorrectionFrom_nil
attribute [local simp] CollatzEndpointTransport.OptimizedLinearPullback.psi_zero
attribute [local simp] CollatzEndpointTransport.QuantitativeDensity.card_positivePrefix
attribute [local simp] CollatzEndpointTransport.QuantitativeDensity.mem_basePullback
attribute [local simp] CollatzEndpointTransport.QuantitativeDensity.mem_collatzPullback
attribute [local simp] CollatzEndpointTransport.Terras.integerCorrection_zero



set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real Topology
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.centralPullbackSourceCodeDecidableEq
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {theta eta : ℝ}
    (htheta0 : 0 < theta)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2)
    {M : ℕ} (hM : centralRenyiStartupScale theta eta ≤ M) :
    let K := centralRenyiDiscardDepth eta M
    K ≤ M ∧
    (K : ℝ) ≤ eta * M / 8 ∧
    4 ≤ eta * M ∧
    ∀ N : ℕ, M - K ≤ N → N ≤ M →
      1 < N ∧
      (1 / 2 - eta) * N > 1 / 2 ∧
      2 * eta ≤ centralRenyiGap theta eta * ((N : ℝ) - 1) ∧
      (1 / 2 : ℝ) ≤
        (Real.log 2 / Real.log 3 - (1 / 2 + eta)) * N := by
  dsimp only
  have hetaHalf : eta < 1 / 2 := by
    have ha := centralRenyiAlpha_lt_log_ratio htheta0
    have hlog : Real.log 2 / Real.log 3 < 1 := by
      rw [div_lt_one (Real.log_pos (by norm_num))]
      exact Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
    linarith
  let gap := centralRenyiGap theta eta
  have hgap : 0 < gap := centralRenyiGap_pos heta1
  let drift := Real.log 2 / Real.log 3 - (1 / 2 + eta)
  have hdrift : 0 < drift := by
    dsimp [drift]
    linarith [centralRenyiAlpha_lt_log_ratio htheta0]
  unfold centralRenyiStartupScale at hM
  rcases max_le_iff.mp hM with ⟨hM4, hM⟩
  rcases max_le_iff.mp hM with ⟨hetaScale, hM⟩
  rcases max_le_iff.mp hM with ⟨hhalfScale, hM⟩
  rcases max_le_iff.mp hM with ⟨hgapScale, hdriftScale⟩
  let K := centralRenyiDiscardDepth eta M
  have harg0 : 0 ≤ eta * (M : ℝ) / 8 := by positivity
  have hKcast : (K : ℝ) ≤ eta * M / 8 := by
    dsimp [K, centralRenyiDiscardDepth]
    exact Nat.floor_le harg0
  have hKhalfR : (K : ℝ) ≤ (M : ℝ) / 2 := by
    have hMr : 0 ≤ (M : ℝ) := by positivity
    nlinarith
  have h2K : 2 * K ≤ M := by
    exact_mod_cast (show 2 * (K : ℝ) ≤ M by linarith)
  have hKM : K ≤ M := by omega
  refine ⟨hKM, hKcast, ?_, ?_⟩
  · have hmul := mul_le_mul_of_nonneg_left hetaScale heta0.le
    field_simp [heta0.ne'] at hmul
    simpa [mul_comm] using hmul
  · intro N hNlower hNupper
    have hMNnat : M ≤ 2 * N := by omega
    have hMN : (M : ℝ) / 2 ≤ N := by
      have hcast : (M : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hMNnat
      linarith
    have hM4nat : 4 ≤ M := by exact_mod_cast hM4
    have hN2 : 2 ≤ N := by omega
    refine ⟨by omega, ?_, ?_, ?_⟩
    · have hhalf0 : 0 < 1 / 2 - eta := by linarith
      have hs := mul_le_mul_of_nonneg_left hhalfScale hhalf0.le
      have hbase : 2 ≤ (1 / 2 - eta) * M := by
        calc
          2 = (1 / 2 - eta) * (2 / (1 / 2 - eta)) := by
            rw [show
              (1 / 2 - eta) * (2 / (1 / 2 - eta)) =
                2 * ((1 / 2 - eta) / (1 / 2 - eta)) by ring]
            rw [div_self hhalf0.ne']
            norm_num
          _ ≤ (1 / 2 - eta) * M := hs
      nlinarith [mul_le_mul_of_nonneg_left hMN hhalf0.le]
    · change 2 * eta ≤ gap * ((N : ℝ) - 1)
      change 4 + 4 * eta / gap ≤ (M : ℝ) at hgapScale
      have hs := mul_le_mul_of_nonneg_left hgapScale hgap.le
      have hbase :
          gap * (4 + 4 * eta / gap) ≤ gap * M := hs
      have hNminus : (M : ℝ) / 2 - 1 ≤ N - 1 := by linarith
      have hmono := mul_le_mul_of_nonneg_left hNminus hgap.le
      have hid : gap * (4 + 4 * eta / gap) = 4 * gap + 4 * eta := by
        field_simp [hgap.ne']
      rw [hid] at hbase
      nlinarith
    · change (1 / 2 : ℝ) ≤ drift * N
      change 1 / drift ≤ (M : ℝ) at hdriftScale
      have hs := mul_le_mul_of_nonneg_left hdriftScale hdrift.le
      have hbase : 1 ≤ drift * M := by
        calc
          1 = drift * (1 / drift) := by
            rw [one_div, mul_inv_cancel₀ hdrift.ne']
          _ ≤ _ := hs
      have hhalf : (1 / 2 : ℝ) ≤ drift * ((M : ℝ) / 2) := by
        calc
          (1 : ℝ) / 2 ≤ (drift * M) / 2 :=
            div_le_div_of_nonneg_right hbase (by norm_num)
          _ = drift * ((M : ℝ) / 2) := by ring
      exact hhalf.trans (mul_le_mul_of_nonneg_left hMN hdrift.le)
end CollatzEndpointTransport.FixedTotal
