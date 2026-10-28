-- Prove2me | solution 1 for ChannelRandomization.PostProc.lemma_2_pair_replacer
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T07:46:21.794185+00:00
-- url     : https://prove2.me/submissions/6e5bcd57-e609-4809-804b-934916db286b

import Mathlib
import Definitions.Def_ChannelRandomization_PostProc_Setting

open ChannelRandomization.PostProc in
theorem solution {h k : ℕ} (φ : Map h k) (σ : Mat h) :
    pair φ (replacer σ) = (φ σ).trace.re := by
  have e : ∀ x : Mat k, (φ ∘ₗ replacer σ) x = x.trace • φ σ := by
    intro x
    rw [LinearMap.comp_apply, replacer, LinearMap.smulRight_apply, map_smul]
    rfl
  unfold pair s
  simp only [e, Matrix.smul_apply, smul_eq_mul]
  congr 1
  conv_rhs => rw [Matrix.trace]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · rw [Matrix.trace_single_eq_same, one_mul, Matrix.diag_apply]
  · intro j _ hj
    rw [Matrix.trace_single_eq_of_ne i j (1 : ℂ) (Ne.symm hj), zero_mul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi
