-- Prove2me | solution 1 for EdenVerified.s04_exteriorOperator_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:37:51.654332+00:00
-- url     : https://prove2.me/submissions/6c47c8a3-4119-4b2f-bf71-fe24782feb58

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_exteriorOperator_comp


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (k : ℕ) (A B : PhaseSpace →ₗ[ℝ] PhaseSpace),
    exteriorOperator k (A ∘ₗ B) = (exteriorOperator k A).comp (exteriorOperator k B) :=
  @Eden.exteriorOperator_comp
end EdenVerified
