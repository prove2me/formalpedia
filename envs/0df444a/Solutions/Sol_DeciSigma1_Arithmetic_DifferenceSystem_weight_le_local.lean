-- Prove2me | solution 1 for DeciSigma1.Arithmetic.DifferenceSystem.weight_le_local
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:11:09.832969+00:00
-- url     : https://prove2.me/submissions/fb270ac9-e7cd-4560-b97b-367042b62167

module
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Basic
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_DifferenceConstraints
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_isWalk_cons_cons
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc


attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_nil
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_singleton
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_cons_cons

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Arithmetic
open DeciSigma1.Arithmetic.DifferenceSystem
variable {ι : Type} (D : DifferenceSystem ι)
variable {D}
namespace DeciSigma1.Arithmetic.DifferenceSystem
theorem _root_.solution {ι : Type}
    {D : DifferenceSystem ι} {x : ι → ℤ} (P : ι → Prop)
    (hP : ∀ u v c, P u → P v → D.edgeWeight u v = some c → x u + c ≤ x v) :
    ∀ (i : ι) (q : List ι), D.IsWalk (i :: q) → (∀ z ∈ i :: q, P z) →
      x i + D.weight (i :: q) ≤ x ((i :: q).getLast (List.cons_ne_nil _ _))
  | i, [], _, _ => by simp
  | i, j :: q, hw, hall => by
    rw [DifferenceSystem.isWalk_cons_cons] at hw
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hw.1
    have h1 := hP i j c (hall i List.mem_cons_self)
      (hall j (List.mem_cons_of_mem _ List.mem_cons_self)) hc
    have h2 :=
        solution P hP j q hw.2
            (fun z hz => hall z (List.mem_cons_of_mem _ hz))
    rw [DifferenceSystem.weight_cons_cons, hc, Option.getD_some, List.getLast_cons_cons]
    linarith
end DeciSigma1.Arithmetic.DifferenceSystem
