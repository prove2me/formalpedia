-- Prove2me | solution 1 for EdenVerified.s04_exterior_operator_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:57:00.779503+00:00
-- url     : https://prove2.me/submissions/ac5851b9-79c8-4011-ba7b-231874e1adca

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_norm_exteriorOperator_eq_singularValueFunction


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution (k : ℕ) (hk : k ≤ 5)
    (M : PhaseSpace →ₗ[ℝ] PhaseSpace) :
    ‖exteriorOperator k M‖ = singularValueFunction M k :=
  norm_exteriorOperator_eq_singularValueFunction hk M
end EdenVerified
