-- Prove2me | solution 1 for Freiman.gap_symbolic_exact
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:44:08.297722+00:00
-- url     : https://prove2.me/submissions/72e05499-e496-43a1-b506-a8c5efa0c57c

import Definitions.Def_Freiman_gapModel
import Theorems.Thm_Freiman_gap_endpoint_A_membership
import Theorems.Thm_Freiman_gap_endpoint_B_membership
import Theorems.Thm_Freiman_gap_threshold_enclosures
import Theorems.Thm_Freiman_markov_centered_representative
import Theorems.Thm_Freiman_gap_finite_reduction
import Theorems.Thm_Freiman_gap_maximum_reflected
import Theorems.Thm_Freiman_gap_minimum_reflected

open Freiman

theorem solution : gapLeft ∈ symbolicMarkovSpectrum ∧ cF ∈ symbolicMarkovSpectrum ∧ (symbolicMarkovSpectrum ∩ Set.Ioo gapLeft cF) = ∅ := by
  refine ⟨gap_endpoint_A_membership,gap_endpoint_B_membership,?_⟩
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro t ht
  obtain ⟨⟨a,hmax,happrox⟩,htlo,hthi⟩ := ht
  obtain ⟨b,hb0,hbmax⟩ := markov_centered_representative a t hmax happrox
  have ho := gap_threshold_enclosures
  have hc : gapCapped b := fun i => le_trans (hbmax i) (le_of_lt (lt_trans hthi ho.2.2.2.1))
  have hw : gapWindow < localValue b 0 := by rw [hb0]; exact lt_trans ho.2.1 htlo
  rcases gap_finite_reduction b hc hw with hA | hAr | hB | hBr
  · have h := gap_maximum_reflected b hc (Or.inl hA); rw [hb0] at h; exact (not_lt_of_ge h) htlo
  · have h := gap_maximum_reflected b hc (Or.inr hAr); rw [hb0] at h; exact (not_lt_of_ge h) htlo
  · have h := gap_minimum_reflected b hc (Or.inl hB); rw [hb0] at h; exact (not_lt_of_ge h) hthi
  · have h := gap_minimum_reflected b hc (Or.inr hBr); rw [hb0] at h; exact (not_lt_of_ge h) hthi
