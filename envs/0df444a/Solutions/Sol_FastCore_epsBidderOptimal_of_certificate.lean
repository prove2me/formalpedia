-- Prove2me | solution 1 for FastCore.epsBidderOptimal_of_certificate
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:16:52.142052+00:00
-- url     : https://prove2.me/submissions/877ce439-7d4d-4cf9-a16f-fa1a08f2f761

import Mathlib
import Definitions.Def_FastCore_IsBidProfile
import Definitions.Def_FastCore_InCore
import Definitions.Def_FastCore_IsEpsBidderOptimal
import Definitions.Def_FastCore_IsEpsTight

open FastCore in
theorem solution {n m : ℕ} {b : Bids n m} (hb : IsBidProfile b)
    {π : Fin n → ℝ} {ε : ℝ} {Ts : List (Finset (Fin n))} (hcore : InCore b π)
    (htight : ∀ T ∈ Ts, IsEpsTight b π ε T) (hempty : ∀ j, ∃ T ∈ Ts, j ∉ T) :
    IsEpsBidderOptimal b ε π := by
  refine ⟨hcore, ?_⟩
  rintro ⟨π', hcore', hle, j, hj⟩
  obtain ⟨T, hT, hjT⟩ := hempty j
  have h1 := (htight T hT).2
  have h2 := hcore'.2 T
  have hs : ∀ f : Fin n → ℝ, ∑ i, f i = ∑ i ∈ Finset.univ \ T, f i + ∑ i ∈ T, f i :=
    fun f => (Finset.sum_sdiff (Finset.subset_univ T)).symm
  rw [hs π] at h1
  rw [hs π'] at h2
  have hjmem : j ∈ Finset.univ \ T := by simp [hjT]
  have hdiff : π' j - π j ≤ ∑ i ∈ Finset.univ \ T, (π' i - π i) :=
    Finset.single_le_sum (f := fun i => π' i - π i) (fun i _ => sub_nonneg.mpr (hle i)) hjmem
  rw [Finset.sum_sub_distrib] at hdiff
  linarith
