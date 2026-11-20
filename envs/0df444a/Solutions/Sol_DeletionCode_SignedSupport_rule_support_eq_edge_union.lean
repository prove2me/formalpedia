-- Prove2me | solution 1 for DeletionCode.SignedSupport.rule_support_eq_edge_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:51.380174+00:00
-- url     : https://prove2.me/submissions/e162e2c3-9735-4eb1-8de4-bf102622e5e1

import Definitions.Def_DeletionCode_SupportComponents
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Definitions.Def_DeletionCode_SignedSupport
import Theorems.Thm_DeletionCode_SignedSupport_rule_support_iff

set_option autoImplicit true
open DeletionCode DeletionCode.SignedSupport
open Windows RootSelection
open scoped BigOperators
namespace DeletionCode.SignedSupport
theorem _root_.solution {B : Type*} (F : Family B) (L : ℕ)
    (H : BubbleGeometry F L) (S : Finset B) (hdis : VertexDisjointOn F L S) :
    {g | ruleSpectrum F L S g ≠ 0} = {g | ∃ b ∈ S, HasGram F L b g} := by
  ext g
  exact rule_support_iff F L H S hdis g
end DeletionCode.SignedSupport
