-- Prove2me | solution 1 for CannonFloydParry.exists_mulEquiv_V1_V
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-26T11:52:52.334987+00:00
-- url     : https://prove2.me/submissions/2aa60250-a296-4d8e-b7c8-2ea2ecd590af

import Definitions.Def_CannonFloydParry
import Definitions.Def_CannonFloydParry_T
import Definitions.Def_CannonFloydParry_V
import Theorems.Thm_CannonFloydParry_exists_surjective_V1_V
import Theorems.Thm_CannonFloydParry_isSimpleGroup_V1
import Mathlib

/-! `V₁ ≅ V` (CFP p. 243): the surjection `V₁ → V` has normal kernel, which by the simplicity
of `V₁` (Theorem 6.9) is trivial, since `A` does not act trivially. -/

namespace CannonFloydParry.MulEquivV1V

open Equiv

/-- `A` moves `1/4` to `1/8`, so it is not the identity of the circle. -/
lemma symV_A_ne_one : symV FormalV.A ≠ 1 := by
  intro h
  have hq : ((1 / 4 : ℝ)) ∈ Set.Ico (0 : ℝ) (0 + 1) := ⟨by norm_num, by norm_num⟩
  have e := congrArg
    (fun g : Perm UnitAddCircle =>
      ((AddCircle.equivIco (1 : ℝ) 0 (g ((AddCircle.equivIco (1 : ℝ) 0).symm ⟨1 / 4, hq⟩)) : ℝ))) h
  simp only [symV, toCircle, Perm.coe_one, id, Equiv.trans_apply, Equiv.apply_symm_apply] at e
  change ((mapA ⟨1 / 4, by norm_num, by norm_num⟩ : UI) : ℝ) = 1 / 4 at e
  rw [mapA, restrict_coe, lineA_apply, aFun_of_mem1 (by norm_num) (by norm_num)] at e
  norm_num at e

end CannonFloydParry.MulEquivV1V

open CannonFloydParry in
theorem solution :
    ∃ e : V1 ≃* V, ∀ s, (e (PresentedGroup.of s) : Equiv.Perm UnitAddCircle) = symV s := by
  obtain ⟨φ, hsurj, hgen⟩ := exists_surjective_V1_V
  have := isSimpleGroup_V1
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker inferInstance with h | h
    · exact h
    · exfalso
      apply MulEquivV1V.symV_A_ne_one
      have : PresentedGroup.of FormalV.A ∈ φ.ker := h ▸ Subgroup.mem_top _
      rw [MonoidHom.mem_ker] at this
      rw [← hgen, this]; rfl
  exact ⟨MulEquiv.ofBijective φ ⟨hinj, hsurj⟩, hgen⟩
