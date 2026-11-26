-- Prove2me | solution 1 for EdenVerified.s04_singularValueFunction_integer_comp_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:38:13.539641+00:00
-- url     : https://prove2.me/submissions/9ffd441e-e860-41d5-a944-7bd905b7c7b5

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_singularValueFunction_integer_comp_le


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {k : ℕ} (hk : k ≤ 5)
    (A B : PhaseSpace →ₗ[ℝ] PhaseSpace),
    singularValueFunction (A ∘ₗ B) k ≤ singularValueFunction A k * singularValueFunction B k :=
  @Eden.singularValueFunction_integer_comp_le
end EdenVerified
