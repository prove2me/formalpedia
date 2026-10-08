-- Prove2me | solution 1 for ErschlerZheng.germEq_mul_and_germ_mul
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-05T23:25:12.442175+00:00
-- url     : https://prove2.me/submissions/a7ca4622-ea96-44e3-b178-79d65bcac4e0

import Mathlib
import Definitions.Def_ErschlerZheng_Germs

section
/-!
# B1: the germ cocycle (pp. 17, 52)
-/

open scoped RightActions

namespace ErschlerZheng

end ErschlerZheng
end

section
open scoped RightActions
open ErschlerZheng
theorem solution {H : Type*} [Group H] {X : Type*} [TopologicalSpace X]
    [MulAction Hᵐᵒᵖ X] [ContinuousConstSMul Hᵐᵒᵖ X] (x : X) :
    (∀ g₁ g₂ h₁ h₂ : H, GermEq x g₁ g₂ → GermEq (x <• g₁) h₁ h₂ →
        GermEq x (g₁ * h₁) (g₂ * h₂)) ∧
      ∀ g h : H, x <• g = x → x <• h = x → germ x (g * h) = germ x g * germ x h := by
  constructor
  · intro g₁ g₂ h₁ h₂ hg hh
    have hcont : Filter.Tendsto (fun y : X => y <• g₁) (nhds x) (nhds (x <• g₁)) :=
      (continuous_const_smul (MulOpposite.op g₁)).tendsto x
    filter_upwards [hg, hcont.eventually hh] with y hy1 hy2
    simp only [MulOpposite.op_mul, mul_smul]
    rw [hy2, hy1]
  · intro g h hg hh
    have hgh : x <• (g * h) = x := by rw [MulOpposite.op_mul, mul_smul, hg, hh]
    unfold germ
    rw [dif_pos hg, dif_pos hh, dif_pos hgh, ← QuotientGroup.mk_mul]
    rfl
end
