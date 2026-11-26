-- Prove2me | solution 1 for Eden.supremumExponentSum_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:44:17.255281+00:00
-- url     : https://prove2.me/submissions/39f9cae3-86fb-402a-8f92-3010a618f748

import Definitions.Def_Eden_DimensionTable
import Definitions.Def_Eden_ExponentSums
import Theorems.Thm_Eden_exponentSum_on_torus
import Theorems.Thm_Eden_exponentSum_image_bddAbove
import Theorems.Thm_Eden_torus_nonempty
import Theorems.Thm_Eden_torus_subset_attractor


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c) {k : ℕ} (hk : k ≤ 4) :
    0 ≤ supremumExponentSum c k := by
  obtain ⟨p, hp⟩ := torus_nonempty
  have hle := le_csSup (exponentSum_image_bddAbove hc k)
    (Set.mem_image_of_mem (fun p => spectrumPartialSum (lyapunovExponent c p) k)
      (torus_subset_attractor hp))
  apply le_trans (b := spectrumPartialSum (lyapunovExponent c p) k) _ hle
  rw [exponentSum_on_torus hc hp]
  interval_cases k <;> norm_num [spectrumPartialSum, spectrumEntry, Finset.sum_range_succ]
end Eden
