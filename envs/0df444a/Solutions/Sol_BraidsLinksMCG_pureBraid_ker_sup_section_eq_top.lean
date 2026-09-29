-- Prove2me | solution 1 for BraidsLinksMCG.pureBraid_ker_sup_section_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T21:13:38.647728+00:00
-- url     : https://prove2.me/submissions/22a0cfa9-eab5-4408-87b8-aa23bb5f6e84

import Theorems.Thm_BraidsLinksMCG_pureBraid_forget_section
import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.all false

open BraidsLinksMCG

namespace SemiSol

/-- A split surjection expresses the source as the kernel together with the image
of the section. -/
theorem pureBraid_ker_sup_section (n : ℕ)
    (s : PureBraidGroup n →* PureBraidGroup (n + 1))
    (hs : (FundamentalGroup.mapOfEq (configForget n) (configForget_base n)).comp s =
        MonoidHom.id (PureBraidGroup n)) :
    (FundamentalGroup.mapOfEq (configForget n) (configForget_base n)).ker ⊔ s.range = ⊤ := by
  rw [eq_top_iff]
  intro x _
  set p := FundamentalGroup.mapOfEq (configForget n) (configForget_base n) with hp
  have hps : ∀ w : PureBraidGroup n, p (s w) = w := fun w => DFunLike.congr_fun hs w
  have h1 : x * (s (p x))⁻¹ ∈ p.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hps, mul_inv_cancel]
  have h2 : s (p x) ∈ s.range := ⟨p x, rfl⟩
  have h3 : x = (x * (s (p x))⁻¹) * s (p x) := by group
  rw [h3]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right h2)

end SemiSol

theorem _root_.solution (n : ℕ) :
    ∃ s : PureBraidGroup n →* PureBraidGroup (n + 1),
      (FundamentalGroup.mapOfEq (configForget n) (configForget_base n)).comp s =
          MonoidHom.id (PureBraidGroup n) ∧
        (FundamentalGroup.mapOfEq (configForget n) (configForget_base n)).ker ⊔ s.range = ⊤ := by
  obtain ⟨s, hs⟩ := BraidsLinksMCG.pureBraid_forget_section n
  exact ⟨s, hs, SemiSol.pureBraid_ker_sup_section n s hs⟩

#print axioms solution
