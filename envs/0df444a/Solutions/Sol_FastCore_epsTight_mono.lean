-- Prove2me | solution 1 for FastCore.epsTight_mono
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:41:21.472694+00:00
-- url     : https://prove2.me/submissions/22a6b15d-3432-4206-a495-827e84743d00

import Mathlib
import Definitions.Def_FastCore_IsBidProfile
import Definitions.Def_FastCore_InCore
import Definitions.Def_FastCore_IsEpsTight

open FastCore in
theorem solution {n m : ℕ} {b : FastCore.Bids n m} (hb : FastCore.IsBidProfile b) {π π' : Fin n → ℝ}
    {ε : ℝ} {T : Finset (Fin n)} (hcore : FastCore.InCore b π') (hle : ∀ i, π i ≤ π' i)
    (hT : FastCore.IsEpsTight b π ε T) : FastCore.IsEpsTight b π' ε T := by
  unfold FastCore.InCore at hcore
  unfold FastCore.IsEpsTight at hT ⊢
  refine ⟨hcore.2 T, ?_⟩
  have h2 := hT.2
  have hsub : ∑ i ∈ T, (π' i - π i) ≤ ∑ i, (π' i - π i) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
      (fun i _ _ => sub_nonneg.2 (hle i))
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib] at hsub
  linarith
