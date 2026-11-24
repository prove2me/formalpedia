-- Prove2me | solution 1 for Formalism.SLP.GlobalBoundRefinements.P.unipotent_upper_entries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:49:02.496913+00:00
-- url     : https://prove2.me/submissions/48261a17-eb10-4884-8648-2155feb51f26

import Definitions.Def_Formalism_HyperbolicPlaceProducts_DetIndexProductHyperbolicInequality
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_ArithmeticLatticeHypothesis
import Theorems.Thm_Formalism_SLP_GlobalBoundRefinements_P_matrix_entries_integral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.SLP Formalism.SLP.GlobalBoundRefinements Formalism.SLP.GlobalBoundRefinements.P
open Formalism.SLP.GlobalBoundRefinements
namespace Formalism.SLP.GlobalBoundRefinements.P
theorem _root_.solution : EntriesOfSignaturePreserving := by
  intro M hM
  obtain ⟨h1, h2, h3⟩ := matrix_entries_integral M hM
  have hsq : ‖M 0 0‖ ^ 2 * ‖M 0 1‖ ^ 2 = ‖M 1 0‖ ^ 2 * ‖M 1 1‖ ^ 2 := by
    rw [← mul_pow, ← mul_pow, h3]
  have hbc : ‖M 0 1‖ ^ 2 = ‖M 1 0‖ ^ 2 := by nlinarith
  have had : ‖M 0 0‖ ^ 2 = ‖M 1 1‖ ^ 2 := by linarith
  have hbc' : ‖M 0 1‖ = ‖M 1 0‖ := (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hbc
  have had' : ‖M 0 0‖ = ‖M 1 1‖ := (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 had
  refine ⟨had', hbc', h1, ?_⟩
  intro sh ch hsh hch hchsh hc
  have hsh0 : sh ≠ 0 := hsh.ne'
  have key : ‖M 0 0‖ ^ 2 = (ch / sh) ^ 2 := by
    have : ‖M 0 0‖ ^ 2 = 1 + (1 / sh) ^ 2 := by rw [← hc]; linarith
    rw [this, div_pow, div_pow, hchsh]
    field_simp
  exact (pow_left_inj₀ (norm_nonneg _) (div_nonneg hch hsh.le) two_ne_zero).1 key
end Formalism.SLP.GlobalBoundRefinements.P
