-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.exists_centralRenyi_full_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:44:13.168887+00:00
-- url     : https://prove2.me/submissions/17dc597a-3805-4c2f-828a-61b8740923ef

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalNonlinearShell
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_tendsto_centralRenyiShellRate_zero_right
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_exists_centralRenyi_linear_cutoff
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
    {theta transport eta : ℝ}
    (htheta : 0 < theta) (heta : 0 < eta)
    (htransport0 : 0 < transport)
    (htransport : transport < centralRenyiAsymptoticRate theta) :
    ∃ Dcut : ℝ, 0 < Dcut ∧ Dcut ≤ 1 ∧
      ∀ D : ℝ, 0 < D → D ≤ Dcut →
        transport * D ≤
            centralRenyiShellRate theta transport D / Real.log 2 ∧
        centralRenyiShellRate theta transport D ≤
            eta * Real.log 2 / 16 ∧
        centralRenyiShellRate theta transport D ≤ eta ^ 2 / 8 := by
  obtain ⟨Dlinear, hDlinear0, hDlinear1, hlinear⟩ :=
    exists_centralRenyi_linear_cutoff htheta htransport0 htransport
  let cap := min (eta * Real.log 2 / 16) (eta ^ 2 / 8)
  have hcap : 0 < cap := by
    dsimp [cap]
    exact lt_min
      (div_pos (mul_pos heta (Real.log_pos (by norm_num))) (by norm_num))
      (div_pos (sq_pos_of_pos heta) (by norm_num))
  have htend := tendsto_centralRenyiShellRate_zero_right theta transport
  have hopen : Set.Iio cap ∈ nhds (0 : ℝ) := Iio_mem_nhds hcap
  have hevent := htend.eventually hopen
  rw [eventually_nhdsWithin_iff] at hevent
  rcases Metric.eventually_nhds_iff.mp hevent with ⟨eps, heps, hball⟩
  let Dcut := min Dlinear (eps / 2)
  refine ⟨Dcut, ?_, ?_, ?_⟩
  · dsimp [Dcut]
    exact lt_min hDlinear0 (half_pos heps)
  · exact (min_le_left _ _).trans hDlinear1
  · intro D hD hDcut
    have hlin := hlinear D hD (hDcut.trans (min_le_left _ _))
    have hDeps : D < eps := by
      have hle := hDcut.trans (min_le_right _ _)
      linarith
    have hdist : dist D 0 < eps := by
      rw [Real.dist_eq]
      simpa [abs_of_pos hD] using hDeps
    have hrateLt : centralRenyiShellRate theta transport D < cap :=
      hball hdist hD
    exact ⟨hlin,
      hrateLt.le.trans (min_le_left _ _),
      hrateLt.le.trans (min_le_right _ _)⟩
end CollatzEndpointTransport.FixedTotal
