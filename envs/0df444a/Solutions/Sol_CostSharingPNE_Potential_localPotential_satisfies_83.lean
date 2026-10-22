-- Prove2me | solution 1 for CostSharingPNE.Potential.localPotential_satisfies_83
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:01:50.631873+00:00
-- url     : https://prove2.me/submissions/e96ddd98-6025-4840-ad3b-0b1e5adaf65c

import Mathlib
import Definitions.Def_CostSharingPNE_Potential_Setting

set_option autoImplicit false
open CostSharingPNE.Potential CostSharingPNE.Char

theorem solution {n : ℕ} (ω : CostSharingPNE.Char.WeightSystem n) (W'' : CostSharingPNE.Char.Welfare n) :
    ∀ S : Finset (Fin n), ∀ i ∈ S,
      (∀ c, c < (ω.block i).rev →
        localPotential ω W'' S c = localPotential ω W'' (S.erase i) c) ∧
      CostSharingPNE.Char.gwmc ω W'' i S = ω.lam i *
        (localPotential ω W'' S (ω.block i).rev -
          localPotential ω W'' (S.erase i) (ω.block i).rev) := by
  intro S i hi
  have herase : ∀ b : Fin ω.K, sbar ω (S.erase i) b = (sbar ω S b).erase i := by
    intro b
    ext j
    simp only [sbar, Finset.mem_filter, Finset.mem_erase]
    tauto
  constructor
  · intro c hc
    have hlt : ω.block i < c.rev := by
      have := Fin.rev_lt_rev.mpr hc
      simpa using this
    unfold localPotential
    rw [herase]
    congr 1
    symm
    apply Finset.erase_eq_of_notMem
    simp only [sbar, Finset.mem_filter, not_and, not_le]
    intro _
    exact hlt
  · unfold gwmc localPotential
    rw [if_pos hi]
    simp only [Fin.rev_rev, herase]
