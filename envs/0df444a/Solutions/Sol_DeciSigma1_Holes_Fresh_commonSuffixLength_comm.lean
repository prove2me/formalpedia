-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.commonSuffixLength_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:18:46.457255+00:00
-- url     : https://prove2.me/submissions/2c2fe61c-3e25-4813-8c5f-144eb11dd919

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Mathlib.Order.Nat
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
public import Theorems.Thm_DeciSigma1_Holes_Fresh_commonPrefixLength_comm

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open Finset
variable {β : Type} [DecidableEq β]
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution (Z Y : List β) :
    commonSuffixLength Z Y = commonSuffixLength Y Z := commonPrefixLength_comm _ _
end DeciSigma1.Holes.Fresh
