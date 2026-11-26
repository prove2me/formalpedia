-- Prove2me | solution 1 for EdenVerified.p05_exists_complete_solution_in_attractor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:10:03.793992+00:00
-- url     : https://prove2.me/submissions/a698ccd2-06f9-4e63-a599-9b451a7c1252

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_exists_complete_solution_in_attractor


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (c : ℝ) {p : PhaseSpace} (hp : p ∈ attractor),
    ∃ f : ℝ → PhaseSpace, f 0 = p ∧ ∀ t : ℝ,
      f t ∈ attractor ∧ HasDerivAt f (vectorField c (f t)) t :=
  @Eden.exists_complete_solution_in_attractor
end EdenVerified
