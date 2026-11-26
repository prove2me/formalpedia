-- Prove2me | solution 1 for EconomicsNextProof.upperSum_upperMobius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:14:31.476801+00:00
-- url     : https://prove2.me/submissions/3eb23b84-f984-4dd3-98e3-af51e36fc267

module
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Finset.Interval
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Tactic
public import Definitions.Def_EconomicsNextProof_Mobius
public import Theorems.Thm_EconomicsNextProof_upperMobius_upperSum

set_option autoImplicit true
@[expose] public section
public section
open EconomicsNextProof
open Finset
variable {X : Type*} [Fintype X] [DecidableEq X]
namespace EconomicsNextProof
theorem _root_.solution (f : Finset X → ℝ) : upperSum (upperMobius f) = f := by
  have hinj : Function.Injective (upperSumLinear (X := X)) := by
    intro f g hfg
    have h := congrArg upperMobius hfg
    simpa only [upperSumLinear, LinearMap.coe_mk, AddHom.coe_mk,
      upperMobius_upperSum] using h
  have hsurj := (LinearMap.injective_iff_surjective.mp hinj)
  obtain ⟨g, hg⟩ := hsurj f
  change upperSum g = f at hg
  rw [← hg, upperMobius_upperSum]
end EconomicsNextProof
