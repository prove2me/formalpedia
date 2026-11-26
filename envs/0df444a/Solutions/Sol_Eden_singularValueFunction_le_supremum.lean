-- Prove2me | solution 1 for Eden.singularValueFunction_le_supremum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:56:29.041743+00:00
-- url     : https://prove2.me/submissions/bb5369e9-dcee-4d4a-ab5d-e36a2e01b4a3

import Definitions.Def_Eden_IntegerGrowthBounds
import Definitions.Def_Eden_GlobalGrowth
import Theorems.Thm_Eden_integerGrowthValues_bddAbove

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {k : ℕ} (hk : k ≤ 5) {c t : ℝ}
    (hc : 4 ≤ c) (ht : 0 ≤ t) {p : PhaseSpace} (hp : p ∈ attractor) :
    singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap k ≤ supremumSingularProduct c k t :=
  le_csSup (integerGrowthValues_bddAbove hk hc ht) ⟨p, hp, rfl⟩
end Eden
