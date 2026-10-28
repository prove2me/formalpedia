-- Prove2me | solution 2 for CostSharingPNE.Potential.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T14:24:20.367345+00:00
-- url     : https://prove2.me/submissions/54e0b105-cc28-49e6-806c-8fee69c8472d

import Mathlib
import Definitions.Def_CostSharingPNE_Potential_Setting
import Theorems.Thm_CostSharingPNE_Potential_localPotential_satisfies_83
import Theorems.Thm_CostSharingPNE_Potential_separable_potential_of_local

-- carved verbatim out of submission 3f43ee7a-f2a2-4130-8d28-6b3d425c16ec, lines 120-138

section
set_option autoImplicit false
open CostSharingPNE.Potential

theorem solution
    (n m : ℕ) (hn : 1 < n) (hm : 1 < m)
    (ω : CostSharingPNE.Char.WeightSystem n)
    (A : Fin n → Finset (Finset (Fin m)))
    (F : Fin m → CostSharingPNE.Char.Rule n) (W' W'' : Fin m → CostSharingPNE.Char.Welfare n)
    (h12 : ∀ r, ∀ T : Finset (Fin n), T.Nonempty →
      CostSharingPNE.Char.mobius (W' r) T =
        (∑ j ∈ CostSharingPNE.Char.tbar ω T, ω.lam j) * CostSharingPNE.Char.mobius (W'' r) T)
    (hF : ∀ r S, ∀ i ∈ S,
      F r i S = CostSharingPNE.Char.gwsv ω (W' r) i S ∧
      F r i S = CostSharingPNE.Char.gwmc ω (W'' r) i S) :
    IsGenWeightedPotential A (fun i a => utility F a i)
      (fun a => ∑ r, localPotential ω (W'' r) (CostSharingPNE.Char.players a r)) ω.lam := by
  refine CostSharingPNE.Potential.separable_potential_of_local n m hn hm A F (fun r S => localPotential ω (W'' r) S) ω.lam ω.lam_pos
    (fun i => (ω.block i).rev) ?_
  intro r i S hi
  obtain ⟨h1, h2⟩ := CostSharingPNE.Potential.localPotential_satisfies_83 ω (W'' r) S i hi
  exact ⟨h1, (hF r S i hi).2.trans h2⟩

end
