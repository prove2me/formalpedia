-- Prove2me | solution 1 for DeletionCode.WitnessAlgebra.scalar_eq_one_or_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:15:48.7017+00:00
-- url     : https://prove2.me/submissions/75ce4fb8-151b-4953-9efc-cb65dead225e

import Definitions.Def_DeletionCode_GeneratingBlocks
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Span.Basic
import Definitions.Def_DeletionCode_WitnessAlgebra

set_option autoImplicit true
open DeletionCode DeletionCode.WitnessAlgebra
open scoped BigOperators
namespace DeletionCode.WitnessAlgebra
theorem _root_.solution {H : Type*} (g w : H → ℚ) (a : ℚ)
    (hg : SignedUnitVector g) (hw : SignedUnitVector w)
    (hg0 : g ≠ 0) (ha : a ≠ 0) (hrel : w = a • g) : a = 1 ∨ a = -1 := by
  classical
  have hex : ∃ h, g h ≠ 0 := by
    by_contra hnone
    push Not at hnone
    apply hg0
    funext h
    exact hnone h
  obtain ⟨h, hh⟩ := hex
  have heq : w h = a * g h := congrFun hrel h
  rcases hg h with hgn | hgz | hgp
  · rcases hw h with hwn | hwz | hwp
    · left; nlinarith
    · exfalso; apply ha; nlinarith
    · right; nlinarith
  · exact False.elim (hh hgz)
  · rcases hw h with hwn | hwz | hwp
    · right; nlinarith
    · exfalso; apply ha; nlinarith
    · left; nlinarith
end DeletionCode.WitnessAlgebra
