-- Prove2me | solution 1 for CategoryTheory.Functor.isMittagLeffler_nat_iff
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-11-26T19:42:06.748984+00:00
-- url     : https://prove2.me/submissions/2f917a5c-f35a-4d92-b034-2159ebbc68ae

import Mathlib.CategoryTheory.CofilteredSystem

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false

/-!
# The Mittag-Leffler condition for `ℕᵒᵖ`-indexed systems

We specialize `CategoryTheory.Functor.IsMittagLeffler` to inverse systems indexed by
`ℕᵒᵖ`, where it takes the familiar form: for every level `n` there is an `m ≥ n` such
that the image of every level `k` in level `n` contains the image of level `m`
(`CategoryTheory.Functor.isMittagLeffler_nat_iff`).

We also record that a functor with finite values satisfies the Mittag-Leffler
condition (`CategoryTheory.Functor.isMittagLeffler_of_finite`) and that the
Mittag-Leffler condition descends along a levelwise bijective natural transformation
(`CategoryTheory.Functor.IsMittagLeffler.of_natTrans_bijective`).
-/

universe w v u

open Set

namespace CategoryTheory
namespace Functor


variable (F : ℕᵒᵖ ⥤ Type v)

open Opposite in
/-- Over `ℕᵒᵖ`, the Mittag-Leffler condition states that for every level `n` there is
an `m ≥ n` such that the range of the transition map from any level `k ≥ n` into level
`n` contains the range of the transition map from level `m`. -/
theorem isMittagLeffler_nat_iff :
    F.IsMittagLeffler ↔ ∀ n : ℕ, ∃ (m : ℕ) (hm : n ≤ m), ∀ (k : ℕ) (hk : n ≤ k),
      range (F.map (homOfLE hm).op) ⊆ range (F.map (homOfLE hk).op) := by
  constructor
  · intro h n
    obtain ⟨i, f, hf⟩ := h (op n)
    have hfeq : f = (homOfLE (leOfHom f.unop)).op :=
      f.op_unop.symm.trans (congrArg Quiver.Hom.op (Subsingleton.elim _ _))
    refine ⟨i.unop, leOfHom f.unop, fun k hk ↦ ?_⟩
    rw [← hfeq]
    exact hf ((homOfLE hk).op)
  · intro h j
    obtain ⟨m, hm, hsub⟩ := h j.unop
    refine ⟨op m, (homOfLE hm).op, fun k g ↦ ?_⟩
    have hgeq : g = (homOfLE (leOfHom g.unop)).op :=
      g.op_unop.symm.trans (congrArg Quiver.Hom.op (Subsingleton.elim _ _))
    rw [hgeq]
    exact hsub k.unop (leOfHom g.unop)

end Functor
end CategoryTheory


theorem solution.{sol_u1} : type_of% @CategoryTheory.Functor.isMittagLeffler_nat_iff.{sol_u1} := @CategoryTheory.Functor.isMittagLeffler_nat_iff.{sol_u1}
