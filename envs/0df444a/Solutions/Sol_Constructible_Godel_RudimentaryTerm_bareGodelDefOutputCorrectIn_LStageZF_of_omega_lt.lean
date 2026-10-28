-- Prove2me | solution 1 for Constructible.Godel.RudimentaryTerm.bareGodelDefOutputCorrectIn_LStageZF_of_omega_lt
-- status  : ACCEPTED   (prove)
-- author  : @Victorized
-- created : 2026-10-25T23:40:25.294995+00:00
-- url     : https://prove2.me/submissions/95e276bb-1b20-4122-be27-25fd55d0033f

import Definitions.Def_CH_ConstructibleGCH_Library03

/-
Prove2Me adaptation of the constructible-universe formalization by Zike Liu,
Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53.
Original copyright notices are preserved below.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-/

set_option Elab.async false
set_option maxHeartbeats 2000000

/- Source module: Solutions.Work_CUGCH_BareStageHistoryBounds -/
section GCHSource_Work_CUGCH_BareStageHistoryBounds
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/



/-!
# Local bounds for bounded constructible-stage histories

This file records the elementary closure facts needed before constructing a
stage-only ("bare") history inside a prescribed limit level.  The hypotheses
and conclusions are deliberately local: membership in the proper class `L`
is not used as a substitute for membership in `LStageZF theta`.

The results below do not yet internalize the Replacement family occurring at
a limit step.  In particular, they do not claim that `stageHistoryData alpha`
belongs to every later limit level.
-/

section

universe u v

namespace Constructible

section ZFC

open Set

/-! ## Explicit finite successor bounds -/

/-- Pairing raises an explicit stage bound by one successor. -/
private theorem pair_mem_LStageZF_succ {alpha : Ordinal.{u}}
    {x y : ZFSet.{u}} (hx : x ∈ LStageZF alpha)
    (hy : y ∈ LStageZF alpha) :
    ({x, y} : ZFSet.{u}) ∈ LStageZF (Order.succ alpha) := by
  rw [LStageZF_succ]
  exact pair_mem_DefZF hx hy



/-- A Kuratowski ordered pair raises an explicit stage bound by two
successors. -/
private theorem orderedPair_mem_LStageZF_succ_succ {alpha : Ordinal.{u}}
    {x y : ZFSet.{u}} (hx : x ∈ LStageZF alpha)
    (hy : y ∈ LStageZF alpha) :
    ZFSet.pair x y ∈
      LStageZF (Order.succ (Order.succ alpha)) := by
  change ({{x}, {x, y}} : ZFSet.{u}) ∈
    LStageZF (Order.succ (Order.succ alpha))
  apply pair_mem_LStageZF_succ
  · simpa using pair_mem_LStageZF_succ hx hx
  · exact pair_mem_LStageZF_succ hx hy

/-- A right-associated Kuratowski triple raises an explicit stage bound by
four successors. -/
private theorem triple_mem_LStageZF_four_succ {alpha : Ordinal.{u}}
    {x y z : ZFSet.{u}} (hx : x ∈ LStageZF alpha)
    (hy : y ∈ LStageZF alpha) (hz : z ∈ LStageZF alpha) :
    Godel.triple x y z ∈
      LStageZF
        (Order.succ (Order.succ (Order.succ (Order.succ alpha)))) := by
  change ZFSet.pair x (ZFSet.pair y z) ∈
    LStageZF
      (Order.succ (Order.succ (Order.succ (Order.succ alpha))))
  apply orderedPair_mem_LStageZF_succ_succ
  · exact LStageZF_mono
      ((Order.le_succ alpha).trans (Order.le_succ (Order.succ alpha))) hx
  · exact orderedPair_mem_LStageZF_succ_succ hy hz

/-- If a Kuratowski pair belongs to a transitive level, both coordinates
belong to that level. -/
private theorem orderedPair_components_mem_LStageZF {alpha : Ordinal.{u}}
    {x y : ZFSet.{u}} (hpair : ZFSet.pair x y ∈ LStageZF alpha) :
    x ∈ LStageZF alpha ∧ y ∈ LStageZF alpha := by
  have htrans := LStageZF_isTransitive alpha
  have hxSingleton : ({x} : ZFSet.{u}) ∈ LStageZF alpha :=
    htrans.mem_trans (by simp [ZFSet.pair]) hpair
  have hxyPair : ({x, y} : ZFSet.{u}) ∈ LStageZF alpha :=
    htrans.mem_trans (by simp [ZFSet.pair]) hpair
  exact
    ⟨htrans.mem_trans (by simp) hxSingleton,
      htrans.mem_trans (by simp) hxyPair⟩

/-- A fiber of a relation whose relation and selected coordinate lie in one
level belongs to the next level. -/
private theorem Godel.fiber_mem_LStageZF_succ {alpha : Ordinal.{u}}
    {relation index : ZFSet.{u}}
    (hrelation : relation ∈ LStageZF alpha)
    (hindex : index ∈ LStageZF alpha) :
    Godel.fiber relation index ∈ LStageZF (Order.succ alpha) := by
  rw [LStageZF_succ]
  apply (Godel.fiberDelta0Section hrelation hindex).mem_DefZF
    (LStageZF_isTransitive alpha)
  intro value hvalue
  exact (orderedPair_components_mem_LStageZF
    ((LStageZF_isTransitive alpha).mem_trans
      (Godel.mem_fiber_iff.mp hvalue) hrelation)).1

/-! ## Local closure under the rudimentary basis -/

/-- Every Jensen--Devlin primitive operation preserves an arbitrary nonzero
limit level.  The proof keeps an explicit common input stage and uses at most
five further successor stages; no appeal to closure of the proper class `L`
occurs. -/
private theorem Godel.op_mem_LStageZF_of_isSuccLimit
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    (i : Fin 9) {x y : ZFSet.{u}}
    (hx : x ∈ LStageZF theta) (hy : y ∈ LStageZF theta) :
    Godel.op i x y ∈ LStageZF theta := by
  rcases (mem_LStageZF_limit_iff htheta).mp hx with
    ⟨alpha, halpha, hxAlpha⟩
  rcases (mem_LStageZF_limit_iff htheta).mp hy with
    ⟨beta, hbeta, hyBeta⟩
  let gamma0 := max alpha beta
  let gamma1 := Order.succ gamma0
  let gamma2 := Order.succ gamma1
  let gamma3 := Order.succ gamma2
  let gamma4 := Order.succ gamma3
  let gamma5 := Order.succ gamma4
  have hgamma0 : gamma0 < theta := max_lt halpha hbeta
  have hgamma1 : gamma1 < theta := htheta.succ_lt hgamma0
  have hgamma2 : gamma2 < theta := htheta.succ_lt hgamma1
  have hgamma3 : gamma3 < theta := htheta.succ_lt hgamma2
  have hgamma4 : gamma4 < theta := htheta.succ_lt hgamma3
  have hgamma5 : gamma5 < theta := htheta.succ_lt hgamma4
  have hx0 : x ∈ LStageZF gamma0 :=
    LStageZF_mono (le_max_left alpha beta) hxAlpha
  have hy0 : y ∈ LStageZF gamma0 :=
    LStageZF_mono (le_max_right alpha beta) hyBeta
  have lift0 : ∀ {z : ZFSet.{u}}, z ∈ LStageZF gamma0 →
      z ∈ LStageZF gamma4 := by
    intro z hz
    exact LStageZF_subset_succ gamma3
      (LStageZF_subset_succ gamma2
        (LStageZF_subset_succ gamma1
          (LStageZF_subset_succ gamma0 hz)))
  have lift1 : ∀ {z : ZFSet.{u}}, z ∈ LStageZF gamma1 →
      z ∈ LStageZF gamma4 := by
    intro z hz
    exact LStageZF_subset_succ gamma3
      (LStageZF_subset_succ gamma2
        (LStageZF_subset_succ gamma1 hz))
  have lift2 : ∀ {z : ZFSet.{u}}, z ∈ LStageZF gamma2 →
      z ∈ LStageZF gamma4 := by
    intro z hz
    exact LStageZF_subset_succ gamma3
      (LStageZF_subset_succ gamma2 hz)
  have htrans0 := LStageZF_isTransitive gamma0
  have hsub : Godel.op i x y ⊆ LStageZF gamma4 := by
    intro q hq
    fin_cases i
    · rcases Godel.mem_F0_iff.mp hq with rfl | rfl
      · exact lift0 hx0
      · exact lift0 hy0
    · exact lift0 (htrans0.mem_trans (Godel.mem_F1_iff.mp hq).1 hx0)
    · rcases Godel.mem_F2_iff.mp hq with ⟨a, ha, b, hb, rfl⟩
      apply lift2
      exact orderedPair_mem_LStageZF_succ_succ
        (htrans0.mem_trans ha hx0) (htrans0.mem_trans hb hy0)
    · rcases Godel.mem_F3_iff.mp hq with
        ⟨a, z, b, hz, hab, rfl⟩
      have hab0 : ZFSet.pair a b ∈ LStageZF gamma0 :=
        htrans0.mem_trans hab hy0
      have hcomponents := orderedPair_components_mem_LStageZF hab0
      exact triple_mem_LStageZF_four_succ hcomponents.1
        (htrans0.mem_trans hz hx0) hcomponents.2
    · rcases Godel.mem_F4_iff.mp hq with
        ⟨a, b, z, hz, hab, rfl⟩
      have hab0 : ZFSet.pair a b ∈ LStageZF gamma0 :=
        htrans0.mem_trans hab hy0
      have hcomponents := orderedPair_components_mem_LStageZF hab0
      exact triple_mem_LStageZF_four_succ hcomponents.1
        hcomponents.2 (htrans0.mem_trans hz hx0)
    · rcases (Godel.mem_F5_iff (x := x) (y := y) (z := q)).mp hq with
        ⟨member, hmember, hqMember⟩
      exact lift0
        (htrans0.mem_trans hqMember
          (htrans0.mem_trans hmember hx0))
    · rcases (Godel.mem_F6_iff (x := x) (y := y) (z := q)).mp hq with
        ⟨left, hpair⟩
      exact lift0
        (orderedPair_components_mem_LStageZF
          (htrans0.mem_trans hpair hx0)).2
    · rcases (Godel.mem_F7_iff (x := x) (y := y) (q := q)).mp hq with
        ⟨a, ha, b, hb, rfl, _hab⟩
      apply lift2
      exact orderedPair_mem_LStageZF_succ_succ
        (htrans0.mem_trans ha hx0) (htrans0.mem_trans hb hx0)
    · rcases Godel.mem_F8_iff.mp hq with ⟨z, hz, rfl⟩
      apply lift1
      exact Godel.fiber_mem_LStageZF_succ hx0
        (htrans0.mem_trans hz hy0)
  have hx4 : x ∈ LStageZF gamma4 := lift0 hx0
  have hy4 : y ∈ LStageZF gamma4 := lift0 hy0
  have hop5 : Godel.op i x y ∈ LStageZF gamma5 := by
    change Godel.op i x y ∈ LStageZF (Order.succ gamma4)
    rw [LStageZF_succ]
    exact Godel.op_mem_DefZF_of_subset
      (LStageZF_isTransitive gamma4) hx4 hy4 hsub
  exact LStageZF_mono hgamma5.le hop5























/-! ## Local bounds for finite sequence and program codes -/













namespace Godel.RudimentaryTerm













/-! ## Local bounds for successful stack executions -/

/-- One successful local machine step preserves the property that every
stack entry belongs to the prescribed nonzero limit level. -/
private theorem runStackToken_entries_mem_LStageZF_of_isSuccLimit
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    {U : ZFSet.{u}} (hU : U ∈ LStageZF theta)
    (token : StackToken (Option (Constructible.ZFCarrier U)))
    (input output : List ZFSet.{u})
    (hinput : ∀ x ∈ input, x ∈ LStageZF theta)
    (hstep : runStackToken (rudimentaryGenerator U) token input =
      some output) :
    ∀ x ∈ output, x ∈ LStageZF theta := by
  cases token with
  | inl generator =>
      simp only [runStackToken, Option.some.injEq] at hstep
      subst output
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact rudimentaryGenerator_mem_LStageZF_of_isSuccLimit
          htheta hU generator
      · exact hinput x hx
  | inr operation =>
      cases input with
      | nil => simp [runStackToken] at hstep
      | cons right tail =>
          cases tail with
          | nil => simp [runStackToken] at hstep
          | cons left rest =>
              simp only [runStackToken, Option.some.injEq] at hstep
              subst output
              intro x hx
              simp only [List.mem_cons] at hx
              rcases hx with rfl | hx
              · exact Godel.op_mem_LStageZF_of_isSuccLimit
                  htheta operation
                  (hinput left (by simp)) (hinput right (by simp))
              · exact hinput x (by simp [hx])

/-- Every state in a successful finite trace remains entrywise inside the
prescribed nonzero limit level. -/
private theorem ExecutionTrace.entries_mem_LStageZF_of_isSuccLimit
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    {U : ZFSet.{u}} (hU : U ∈ LStageZF theta)
    {program : List (StackToken (Option (Constructible.ZFCarrier U)))}
    {states : List (List ZFSet.{u})}
    (htrace : ExecutionTrace (rudimentaryGenerator U) program states)
    {input : List ZFSet.{u}} (hhead : states.head? = some input)
    (hinput : ∀ x ∈ input, x ∈ LStageZF theta) :
    ∀ stack ∈ states, ∀ x ∈ stack, x ∈ LStageZF theta := by
  induction htrace generalizing input with
  | nil stack =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst input
      simpa using hinput
  | @cons token program input next tailStates hstep htail ih =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst input
      have hnext : ∀ x ∈ next, x ∈ LStageZF theta :=
        runStackToken_entries_mem_LStageZF_of_isSuccLimit
          htheta hU token _ _ hinput hstep
      intro stack hstack
      simp only [List.mem_cons] at hstack
      rcases hstack with rfl | hstack
      · exact hinput
      · exact ih rfl hnext stack
          (by simpa only [List.mem_cons] using hstack)





end Godel.RudimentaryTerm

namespace Model











end Model

end ZFC

end Constructible

end
end GCHSource_Work_CUGCH_BareStageHistoryBounds

/- Source module: Solutions.Work_CUGCH_BareGodelDefAbsolute -/
section GCHSource_Work_CUGCH_BareGodelDefAbsolute
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# Local correctness of the Goedel-definability evaluator

This file proves that the first-order formula used at a successor step of a
bare stage history has its intended ambient meaning when interpreted in a
constructible limit level above `omega`.

The proof deliberately separates soundness from completeness.  Soundness
only projects a restricted finite evaluation certificate to the ambient
universe.  Completeness constructs the canonical program and execution-trace
codes and checks, using the local bounds from `BareStageHistoryBounds`, that
every unbounded witness belongs to the prescribed level.
-/

section

open Set

universe u

namespace Constructible.Godel.RudimentaryTerm

noncomputable section

open Constructible.IndexedSequenceZF
open Constructible.FiniteSequenceZF







private theorem carrierVal_eq {a : ZFSet.{u}} {n : Nat}
    (s : Tuple (Carrier a) n) :
    Delta0Formula.val s = (fun i => (s i).1) := by
  rfl

private theorem carrierVal_snoc4 {a : ZFSet.{u}} {n : Nat}
    (s : Tuple (Carrier a) n) (w x y z : Carrier a) :
    Delta0Formula.val (snoc (snoc (snoc (snoc s w) x) y) z) =
      snoc (snoc (snoc (snoc (fun i => (s i).1) w.1) x.1) y.1) z.1 := by
  rw [Delta0Formula.val_snoc, Delta0Formula.val_snoc,
    Delta0Formula.val_snoc, Delta0Formula.val_snoc, carrierVal_eq]

private theorem carrierVal_snoc5 {a : ZFSet.{u}} {n : Nat}
    (s : Tuple (Carrier a) n) (v w x y z : Carrier a) :
    Delta0Formula.val
        (snoc (snoc (snoc (snoc (snoc s v) w) x) y) z) =
      snoc (snoc (snoc (snoc (snoc (fun i => (s i).1) v.1)
        w.1) x.1) y.1) z.1 := by
  rw [Delta0Formula.val_snoc, Delta0Formula.val_snoc,
    Delta0Formula.val_snoc, Delta0Formula.val_snoc,
    Delta0Formula.val_snoc, carrierVal_eq]











private theorem sequenceValidity_carrier_to_ambient
    {a : ZFSet.{u}} (ha : a.IsTransitive)
    (omega sequence : Carrier a)
    (hvalid : FOFormula.Satisfies (zfCarrierMem a)
      sequenceValidityFormula ![omega, sequence]) :
    FOFormula.Satisfies Delta0Formula.ZFMem sequenceValidityFormula
      ![omega.1, sequence.1] := by
  rw [satisfies_sequenceValidityFormula_carrier ha] at hvalid
  rw [satisfies_sequenceValidityFormula]
  rcases hvalid with
    ⟨length, graph, hsequence, hlength, hfunctional⟩
  refine ⟨length.1, graph.1, hsequence, hlength, ?_⟩
  intro index hindex
  let indexA : Carrier a :=
    ⟨index, ha.mem_trans hindex length.2⟩
  rcases hfunctional indexA hindex with
    ⟨value, hvalue, hunique⟩
  refine ⟨value.1, hvalue, ?_⟩
  intro other hother
  have hpairA : ZFSet.pair other index ∈ a :=
    ha.mem_trans hother graph.2
  have hsingletonA : ({other} : ZFSet.{u}) ∈ a :=
    ha.mem_trans (by simp [ZFSet.pair]) hpairA
  have hotherA : other ∈ a :=
    ha.mem_trans (by simp) hsingletonA
  let otherA : Carrier a := ⟨other, hotherA⟩
  exact hunique otherA hother

private theorem sequenceValidityAssignment_carrier_to_ambient
    {a : ZFSet.{u}} (ha : a.IsTransitive)
    (s : Tuple (Carrier a) 2)
    (hvalid : FOFormula.Satisfies (zfCarrierMem a)
      sequenceValidityFormula s) :
    FOFormula.Satisfies Delta0Formula.ZFMem sequenceValidityFormula
      (fun i => (s i).1) := by
  have hstandard : FOFormula.Satisfies (zfCarrierMem a)
      sequenceValidityFormula ![s 0, s 1] := by
    apply (satisfies_congr_assignment (zfCarrierMem a)
      sequenceValidityFormula s ![s 0, s 1] ?_).mp hvalid
    intro i
    fin_cases i <;> rfl
  have hambient := sequenceValidity_carrier_to_ambient ha
    (s 0) (s 1) hstandard
  apply (satisfies_congr_assignment Delta0Formula.ZFMem
    sequenceValidityFormula ![(s 0).1, (s 1).1]
      (fun i => (s i).1) ?_).mp hambient
  intro i
  fin_cases i <;> rfl

private theorem hasLength_carrier_to_ambient
    {a : ZFSet.{u}} (ha : a.IsTransitive)
    (s : Tuple (Carrier a) 2)
    (hlength : FOFormula.Satisfies (zfCarrierMem a)
      hasLengthFormula s) :
    FOFormula.Satisfies Delta0Formula.ZFMem hasLengthFormula
      (fun i => (s i).1) := by
  simp only [hasLengthFormula, FOFormula.Satisfies] at hlength ⊢
  rcases hlength with ⟨graph, hgraph⟩
  refine ⟨graph.1, ?_⟩
  have hraw := (Delta0Formula.satisfies_toFO_absolute ha
    _ (snoc s graph)).mp hgraph
  change FOFormula.Satisfies (fun x y : ZFSet.{u} => x ∈ y)
    (Delta0Formula.kuratowskiPairEqAt 0 1 2).toFO
    (Delta0Formula.val (snoc s graph)) at hraw
  change FOFormula.Satisfies (fun x y : ZFSet.{u} => x ∈ y)
    (Delta0Formula.kuratowskiPairEqAt 0 1 2).toFO
    (snoc (fun i => (s i).1) graph.1)
  rw [Delta0Formula.val_snoc] at hraw
  have hval : Delta0Formula.val s = (fun i => (s i).1) := rfl
  rw [hval] at hraw
  exact hraw

private theorem variableStackStep_carrier_to_ambient
    {a : ZFSet.{u}} (ha : a.IsTransitive)
    (s : Tuple (Carrier a) 16)
    (hstep : FOFormula.Satisfies (zfCarrierMem a)
      variableStackStepFormula s) :
    FOFormula.Satisfies Delta0Formula.ZFMem variableStackStepFormula
      (fun i => (s i).1) := by
  simp only [variableStackStepFormula, FOFormula.Satisfies,
    FOFormula.satisfies_disj] at hstep ⊢
  rcases hstep with ⟨generator, htoken, hgenerator, houtput⟩
  refine ⟨generator.1, ?_, ?_, ?_⟩
  · have hraw := (Delta0Formula.satisfies_toFO_absolute ha
      _ (snoc s generator)).mp htoken
    rw [Delta0Formula.val_snoc] at hraw
    exact hraw
  · rcases hgenerator with hgenerator | hgenerator
    · exact Or.inl (congrArg Subtype.val hgenerator)
    · exact Or.inr hgenerator
  · have hraw := (Delta0Formula.satisfies_toFO_absolute ha
      _ (snoc s generator)).mp houtput
    rw [Delta0Formula.val_snoc] at hraw
    exact hraw

set_option maxHeartbeats 1200000 in
private theorem operationStackStep_carrier_to_ambient
    {a : ZFSet.{u}} (ha : a.IsTransitive) (operation : Fin 9)
    (s : Tuple (Carrier a) 16)
    (hstep : FOFormula.Satisfies (zfCarrierMem a)
      (operationStackStepFormula operation) s) :
    FOFormula.Satisfies Delta0Formula.ZFMem
      (operationStackStepFormula operation) (fun i => (s i).1) := by
  simp only [operationStackStepFormula, operationStackStepBody,
    FOFormula.Satisfies, FOFormula.satisfies_rename] at hstep ⊢
  rcases hstep with
    ⟨right, left, rest, result, inner,
      htoken, hinput, hinner, houtput, hop⟩
  refine ⟨right.1, left.1, rest.1, result.1, inner.1,
    ?_, ?_, ?_, ?_, ?_⟩
  · have hraw := (Delta0Formula.satisfies_toFO_absolute ha _
      (snoc (snoc (snoc (snoc (snoc s right) left) rest)
        result) inner)).mp htoken
    rw [carrierVal_snoc5] at hraw
    exact hraw
  · have hraw := (Delta0Formula.satisfies_toFO_absolute ha _
      (snoc (snoc (snoc (snoc (snoc s right) left) rest)
        result) inner)).mp hinput
    rw [carrierVal_snoc5] at hraw
    exact hraw
  · have hraw := (Delta0Formula.satisfies_toFO_absolute ha _
      (snoc (snoc (snoc (snoc (snoc s right) left) rest)
        result) inner)).mp hinner
    rw [carrierVal_snoc5] at hraw
    exact hraw
  · have hraw := (Delta0Formula.satisfies_toFO_absolute ha _
      (snoc (snoc (snoc (snoc (snoc s right) left) rest)
        result) inner)).mp houtput
    rw [carrierVal_snoc5] at hraw
    exact hraw
  · have hraw := (Delta0Formula.satisfies_toFO_absolute ha _ _).mp hop
    apply (satisfies_congr_assignment Delta0Formula.ZFMem
      (opGraphFormula operation).toFO _ _ ?_).mp hraw
    intro j
    exact congrFun (carrierVal_snoc5 s right left rest result inner)
      (stackStepOpGraphRename j)

private theorem stackStep_carrier_to_ambient
    {a : ZFSet.{u}} (ha : a.IsTransitive)
    (s : Tuple (Carrier a) 16)
    (hstep : FOFormula.Satisfies (zfCarrierMem a)
      stackStepFormula s) :
    FOFormula.Satisfies Delta0Formula.ZFMem stackStepFormula
      (fun i => (s i).1) := by
  simp only [stackStepFormula, anyOperationStackStepFormula,
    FOFormula.satisfies_disj] at hstep ⊢
  rcases hstep with hvariable | hoperation
  · exact Or.inl (variableStackStep_carrier_to_ambient ha s hvariable)
  · right
    rcases hoperation with h | h | h | h | h | h | h | h | h
    · exact Or.inl (operationStackStep_carrier_to_ambient ha 0 s h)
    · exact Or.inr (Or.inl
        (operationStackStep_carrier_to_ambient ha 1 s h))
    · exact Or.inr (Or.inr (Or.inl
        (operationStackStep_carrier_to_ambient ha 2 s h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        (operationStackStep_carrier_to_ambient ha 3 s h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (operationStackStep_carrier_to_ambient ha 4 s h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (operationStackStep_carrier_to_ambient ha 5 s h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl (operationStackStep_carrier_to_ambient ha 6 s h)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl
          (operationStackStep_carrier_to_ambient ha 7 s h))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr
          (operationStackStep_carrier_to_ambient ha 8 s h))))))))

set_option maxHeartbeats 1200000 in
private theorem traceStep_carrier_to_ambient
    {a : ZFSet.{u}} (ha : a.IsTransitive)
    (s : Tuple (Carrier a) 16)
    (hstep : FOFormula.Satisfies (zfCarrierMem a)
      traceStepFormula s) :
    FOFormula.Satisfies Delta0Formula.ZFMem traceStepFormula
      (fun i => (s i).1) := by
  simp only [traceStepFormula, traceStepBody, FOFormula.Satisfies,
    FOFormula.satisfies_rename] at hstep ⊢
  rcases hstep with
    ⟨token, input, succ, output,
      htoken, hinput, hsucc, houtput, hstack⟩
  refine ⟨token.1, input.1, succ.1, output.1,
    ?_, ?_, ?_, ?_, ?_⟩
  · have hraw := (Delta0Formula.satisfies_toFO_absolute ha _ _).mp htoken
    change FOFormula.Satisfies Delta0Formula.ZFMem valueAtFormula _ at hraw
    apply (satisfies_congr_assignment Delta0Formula.ZFMem
      valueAtFormula _ _ ?_).mp hraw
    intro i
    exact congrFun (carrierVal_snoc4 s token input succ output)
      (traceStepProgramValueRename i)
  · have hraw := (Delta0Formula.satisfies_toFO_absolute ha _ _).mp hinput
    change FOFormula.Satisfies Delta0Formula.ZFMem valueAtFormula _ at hraw
    apply (satisfies_congr_assignment Delta0Formula.ZFMem
      valueAtFormula _ _ ?_).mp hraw
    intro i
    exact congrFun (carrierVal_snoc4 s token input succ output)
      (traceStepInputValueRename i)
  · have hraw := (Delta0Formula.satisfies_toFO_absolute ha _ _).mp hsucc
    change FOFormula.Satisfies Delta0Formula.ZFMem
      (Delta0Formula.successorFOAt (18 : Fin 20) (15 : Fin 20)) _ at hraw
    rw [carrierVal_snoc4] at hraw
    exact hraw
  · have hraw := (Delta0Formula.satisfies_toFO_absolute ha _ _).mp houtput
    change FOFormula.Satisfies Delta0Formula.ZFMem valueAtFormula _ at hraw
    apply (satisfies_congr_assignment Delta0Formula.ZFMem
      valueAtFormula _ _ ?_).mp hraw
    intro i
    exact congrFun (carrierVal_snoc4 s token input succ output)
      (traceStepOutputValueRename i)
  · have hraw := stackStep_carrier_to_ambient ha _ hstack
    apply (satisfies_congr_assignment Delta0Formula.ZFMem
      stackStepFormula _ _ ?_).mp hraw
    intro i
    exact congrFun (carrierVal_snoc4 s token input succ output)
      (traceStepStackStepRename i)

private theorem stackProgramEvalCore_carrier_to_ambient
    {a : ZFSet.{u}} (ha : a.IsTransitive)
    (s : Tuple (Carrier a) 20)
    (hcore : FOFormula.Satisfies (zfCarrierMem a)
      stackProgramEvalCore s) :
    FOFormula.Satisfies Delta0Formula.ZFMem stackProgramEvalCore
      (fun i => (s i).1) := by
  rw [stackProgramEvalCore] at hcore ⊢
  rcases hcore with
    ⟨hprogramLength, htraceLength, hsuccessor,
      hinitial, hfinal, hfinalStack, hsteps⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [FOFormula.satisfies_rename] at hprogramLength ⊢
    exact hasLength_carrier_to_ambient ha _ hprogramLength
  · rw [FOFormula.satisfies_rename] at htraceLength ⊢
    exact hasLength_carrier_to_ambient ha _ htraceLength
  · exact (Delta0Formula.satisfies_toFO_absolute ha _ s).mp hsuccessor
  · rw [FOFormula.satisfies_rename] at hinitial ⊢
    exact (Delta0Formula.satisfies_toFO_absolute ha _ _).mp hinitial
  · rw [FOFormula.satisfies_rename] at hfinal ⊢
    exact (Delta0Formula.satisfies_toFO_absolute ha _ _).mp hfinal
  · exact (Delta0Formula.satisfies_toFO_absolute ha _ s).mp hfinalStack
  · rw [FOFormula.satisfies_boundedAll] at hsteps ⊢
    intro index hindex
    let indexA : Carrier a :=
      ⟨index, ha.mem_trans hindex (s 17).2⟩
    have hrestricted := hsteps indexA hindex
    rw [FOFormula.satisfies_rename] at hrestricted ⊢
    have hambient := traceStep_carrier_to_ambient ha _ hrestricted
    apply (satisfies_congr_assignment Delta0Formula.ZFMem
      traceStepFormula _ _ ?_).mp hambient
    intro i
    simp only [carrierVal_snoc_apply, indexA]

private theorem stackProgramEval_carrier_to_ambient
    {a : ZFSet.{u}} (ha : a.IsTransitive)
    (s : Tuple (Carrier a) 16)
    (heval : FOFormula.Satisfies (zfCarrierMem a)
      stackProgramEvalFormula s) :
    FOFormula.Satisfies Delta0Formula.ZFMem stackProgramEvalFormula
      (fun i => (s i).1) := by
  rw [stackProgramEvalFormula] at heval ⊢
  rcases heval with
    ⟨hprogramValid, trace, htraceValid,
      programLength, traceLength, finalStack, hcore⟩
  refine ⟨?_, trace.1, ?_, programLength.1, traceLength.1,
    finalStack.1, ?_⟩
  · rw [FOFormula.satisfies_rename] at hprogramValid ⊢
    exact sequenceValidityAssignment_carrier_to_ambient
      ha _ hprogramValid
  · rw [FOFormula.satisfies_rename] at htraceValid ⊢
    let traceValidityAssignment : Tuple (Carrier a) 2 :=
      fun i => snoc s trace (evalTraceValidityRename i)
    have htraceRestricted :
        FOFormula.Satisfies (zfCarrierMem a) sequenceValidityFormula
          traceValidityAssignment := htraceValid
    have htraceAmbient := sequenceValidityAssignment_carrier_to_ambient
      ha traceValidityAssignment htraceRestricted
    apply (satisfies_congr_assignment Delta0Formula.ZFMem
      sequenceValidityFormula _ _ ?_).mp htraceAmbient
    intro i
    simp only [traceValidityAssignment, carrierVal_snoc_apply]
  · let coreAssignment : Tuple (Carrier a) 20 :=
      snoc (snoc (snoc (snoc s trace) programLength)
        traceLength) finalStack
    have hcoreRestricted :
        FOFormula.Satisfies (zfCarrierMem a) stackProgramEvalCore
          coreAssignment := hcore
    have hambient := stackProgramEvalCore_carrier_to_ambient
      ha coreAssignment hcoreRestricted
    apply (satisfies_congr_assignment Delta0Formula.ZFMem
      stackProgramEvalCore _ _ ?_).mp hambient
    intro i
    simp only [coreAssignment, carrierVal_snoc_apply]

/-! ## Canonical witnesses inside a limit stage -/







private theorem satisfies_variableStackStepFormula_stageCarrier
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (token : StackToken (Option (Constructible.ZFCarrier U)))
    (input output : List ZFSet.{u})
    (hinput : ∀ x ∈ input, x ∈ LStageZF delta)
    (houtput : ∀ x ∈ output, x ∈ LStageZF delta) :
    FOFormula.Satisfies (zfCarrierMem A)
        variableStackStepFormula
        (stackStepStageAssignment hdelta hsub U hU token input output
          hinput houtput) ↔
      ∃ generator : Carrier A,
        stackTokenZFCode U token = triple varTag generator.1 ∅ ∧
          (generator.1 = U ∨ generator.1 ∈ U) ∧
          listCode output = ZFSet.pair generator.1 (listCode input) := by
  simp only [variableStackStepFormula, FOFormula.Satisfies,
    Delta0Formula.satisfies_toFO,
    Delta0Formula.satisfies_absolute hA,
    Delta0Formula.satisfies_tripleEqAt,
    Delta0Formula.satisfies_kuratowskiPairEqAt,
    FOFormula.satisfies_disj, snoc_last, snoc_castSucc,
    Delta0Formula.val_snoc, Delta0Formula.val_apply,
    stackStepStageAssignment_val_apply, stackStepLiftOne,
    stackStepTokenIndex, stackStepVarTagIndex,
    stackStepEmptyIndex, stackStepUniverseIndex,
    stackStepOutputIndex, stackStepInputIndex,
    Subtype.ext_iff]
  rfl

private theorem comp_stackStepOpGraphRename_carrier
    {A : ZFSet.{u}}
    (s : Tuple (Carrier A) 16)
    (right left rest result inner : Carrier A) :
    (fun i =>
      (snoc (snoc (snoc (snoc (snoc s right) left) rest)
        result) inner (stackStepOpGraphRename i)).1) =
      ![result.1, left.1, right.1] := by
  funext i
  fin_cases i <;> rfl

private theorem satisfies_operationStackStepFormula_stageCarrier
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (operation : Fin 9)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (token : StackToken (Option (Constructible.ZFCarrier U)))
    (input output : List ZFSet.{u})
    (hinput : ∀ x ∈ input, x ∈ LStageZF delta)
    (houtput : ∀ x ∈ output, x ∈ LStageZF delta) :
    FOFormula.Satisfies (zfCarrierMem A)
        (operationStackStepFormula operation)
        (stackStepStageAssignment hdelta hsub U hU token input output
          hinput houtput) ↔
      ∃ right left rest result : Carrier A,
        stackTokenZFCode U token =
            triple appTag (operationCode operation) ∅ ∧
          listCode input = ZFSet.pair right.1 (ZFSet.pair left.1 rest.1) ∧
          listCode output = ZFSet.pair result.1 rest.1 ∧
          ZFSet.pair left.1 rest.1 ∈ A ∧
          result.1 = op operation left.1 right.1 := by
  simp only [operationStackStepFormula, operationStackStepBody,
    FOFormula.Satisfies, Delta0Formula.satisfies_toFO,
    Delta0Formula.satisfies_absolute hA,
    Delta0Formula.satisfies_tripleEqAt,
    Delta0Formula.satisfies_kuratowskiPairEqAt,
    FOFormula.satisfies_rename, snoc_castSucc,
    Delta0Formula.val_snoc, Delta0Formula.val_apply,
    stackStepStageAssignment_val_apply,
    stackStepLiftFive, stackStepAssignment_operation,
    stackStepAssignment_appTag, stackStepAssignment_empty,
    stackStepAssignment_token, stackStepAssignment_input,
    stackStepAssignment_output, stackStepWitness_right,
    stackStepWitness_left, stackStepWitness_rest,
    stackStepWitness_result, stackStepWitness_inner]
  constructor
  · rintro ⟨right, left, rest, result, inner,
      htoken, hinputCode, hinner, houtputCode, hop⟩
    have hcomp :
        Delta0Formula.val (fun i =>
          snoc (snoc (snoc (snoc (snoc
            (stackStepStageAssignment hdelta hsub U hU token input output
              hinput houtput) right) left) rest) result) inner
            (stackStepOpGraphRename i)) =
          ![result.1, left.1, right.1] := by
      funext j
      exact congrFun (comp_stackStepOpGraphRename_carrier
        (stackStepStageAssignment hdelta hsub U hU token input output
          hinput houtput) right left rest result inner) j
    have hopRaw :
        Delta0Formula.Satisfies Delta0Formula.ZFMem
          (opGraphFormula operation) ![result.1, left.1, right.1] := by
      rw [hcomp] at hop
      exact hop
    have hop' : result.1 = op operation left.1 right.1 :=
      (satisfies_opGraphFormula operation result.1 left.1 right.1).mp hopRaw
    have hinnerMem : ZFSet.pair left.1 rest.1 ∈ A := by
      rw [← hinner]
      exact inner.2
    exact ⟨right, left, rest, result, htoken,
      hinputCode.trans (congrArg (ZFSet.pair right.1) hinner),
      houtputCode, hinnerMem, hop'⟩
  · rintro ⟨right, left, rest, result,
      htoken, hinputCode, houtputCode, hinnerMem, hop⟩
    have hopRaw :
        Delta0Formula.Satisfies Delta0Formula.ZFMem
          (opGraphFormula operation) ![result.1, left.1, right.1] :=
      (satisfies_opGraphFormula operation result.1 left.1 right.1).mpr hop
    let inner : Carrier A :=
      ⟨ZFSet.pair left.1 rest.1, hinnerMem⟩
    have hcomp :
        Delta0Formula.val (fun i =>
          snoc (snoc (snoc (snoc (snoc
            (stackStepStageAssignment hdelta hsub U hU token input output
              hinput houtput) right) left) rest) result) inner
            (stackStepOpGraphRename i)) =
          ![result.1, left.1, right.1] := by
      funext j
      exact congrFun (comp_stackStepOpGraphRename_carrier
        (stackStepStageAssignment hdelta hsub U hU token input output
          hinput houtput) right left rest result inner) j
    refine ⟨right, left, rest, result, inner,
      htoken, hinputCode, rfl, houtputCode, ?_⟩
    rw [hcomp]
    exact hopRaw

private theorem satisfies_stackStepFormula_stageCarrier_of_run
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (token : StackToken (Option (Constructible.ZFCarrier U)))
    (input output : List ZFSet.{u})
    (hinput : ∀ x ∈ input, x ∈ LStageZF delta)
    (houtput : ∀ x ∈ output, x ∈ LStageZF delta)
    (hrun : runStackToken (rudimentaryGenerator U) token input =
      some output) :
    FOFormula.Satisfies (zfCarrierMem A)
      stackStepFormula
      (stackStepStageAssignment hdelta hsub U hU token input output
        hinput houtput) := by
  simp only [stackStepFormula, FOFormula.satisfies_disj]
  cases token with
  | inl generator =>
      left
      rw [satisfies_variableStackStepFormula_stageCarrier
        hA hdelta hsub]
      cases generator with
      | none =>
          have houtputEq : output = U :: input :=
            (Option.some.inj hrun).symm
          refine ⟨⟨U, hsub hU⟩, rfl, Or.inl rfl, ?_⟩
          simp only [houtputEq, listCode_cons]
      | some generator =>
          have hgenerator : generator.1 ∈ LStageZF delta :=
            (LStageZF_isTransitive delta).mem_trans generator.2 hU
          have houtputEq : output = generator.1 :: input :=
            (Option.some.inj hrun).symm
          refine ⟨⟨generator.1, hsub hgenerator⟩, rfl,
            Or.inr generator.2, ?_⟩
          simp only [houtputEq, listCode_cons]
  | inr operation =>
      right
      simp only [anyOperationStackStepFormula,
        FOFormula.satisfies_disj]
      have hop : FOFormula.Satisfies (zfCarrierMem A)
          (operationStackStepFormula operation)
          (stackStepStageAssignment hdelta hsub U hU (Sum.inr operation)
            input output hinput houtput) := by
        rw [satisfies_operationStackStepFormula_stageCarrier
          hA hdelta hsub]
        cases input with
        | nil => cases hrun
        | cons right tail =>
            cases tail with
            | nil => cases hrun
            | cons left rest =>
                have hright := hinput right (by simp)
                have hleft := hinput left (by simp)
                have hrestEntries : ∀ x ∈ rest, x ∈ LStageZF delta := by
                  intro x hx
                  exact hinput x (by simp [hx])
                have hrest :=
                  listCode_mem_LStageZF_of_isSuccLimit hdelta hrestEntries
                have hresult := op_mem_LStageZF_of_isSuccLimit
                  hdelta operation hleft hright
                have hinner := orderedPair_mem_LStageZF_of_isSuccLimit
                  hdelta hleft hrest
                have houtputEq :
                    output = op operation left right :: rest :=
                  (Option.some.inj hrun).symm
                refine ⟨⟨right, hsub hright⟩, ⟨left, hsub hleft⟩,
                  ⟨listCode rest, hsub hrest⟩,
                  ⟨op operation left right, hsub hresult⟩,
                  rfl, rfl, ?_, hsub hinner, rfl⟩
                simp only [houtputEq, listCode_cons]
      fin_cases operation
      · exact Or.inl hop
      · exact Or.inr (Or.inl hop)
      · exact Or.inr (Or.inr (Or.inl hop))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hop)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hop))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hop)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inl hop))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inl hop)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr hop)))))))

private theorem satisfies_valueAtFormula_stageCarrier_iff
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (xs : List ZFSet.{u})
    (hxs : ∀ x ∈ xs, x ∈ LStageZF delta)
    (k : Nat) (value : Carrier A) :
    FOFormula.Satisfies (zfCarrierMem A) valueAtFormula
        ![⟨IndexedSequenceZF.sequenceCode xs,
            hsub (sequenceCode_mem_LStageZF_of_isSuccLimit hdelta hxs)⟩,
          ⟨natCode k, hsub (natCode_mem_LStageZF_of_isSuccLimit hdelta k)⟩,
          value] ↔
      ∃ hk : k < xs.length, value.1 = xs.get ⟨k, hk⟩ := by
  rw [valueAtFormula,
    Delta0Formula.satisfies_toFO_absolute hA]
  have hval :
      Delta0Formula.val
        ![⟨IndexedSequenceZF.sequenceCode xs,
            hsub (sequenceCode_mem_LStageZF_of_isSuccLimit hdelta hxs)⟩,
          ⟨natCode k, hsub (natCode_mem_LStageZF_of_isSuccLimit hdelta k)⟩,
          value] = ![IndexedSequenceZF.sequenceCode xs,
            natCode k, value.1] := by
    funext i
    fin_cases i <;> rfl
  rw [hval]
  exact satisfies_valueAt_sequenceCode_iff xs k value.1

private theorem satisfies_hasLengthFormula_stageCarrier_iff
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (xs : List ZFSet.{u})
    (hxs : ∀ x ∈ xs, x ∈ LStageZF delta)
    (length : Carrier A) :
    FOFormula.Satisfies (zfCarrierMem A) hasLengthFormula
        ![⟨IndexedSequenceZF.sequenceCode xs,
            hsub (sequenceCode_mem_LStageZF_of_isSuccLimit hdelta hxs)⟩,
          length] ↔
      length.1 = natCode xs.length := by
  simp only [hasLengthFormula, FOFormula.Satisfies]
  constructor
  · rintro ⟨graph, hpair⟩
    have hpairRaw := (satisfies_kuratowskiPairEqAt_carrier
      hA
      (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) _).mp hpair
    exact (ZFSet.pair_inj.mp hpairRaw).1.symm
  · intro hlength
    let graph : Carrier A :=
      ⟨IndexedSequenceZF.graph xs,
        hsub (graphFrom_mem_LStageZF_of_isSuccLimit hdelta hxs 0)⟩
    refine ⟨graph, ?_⟩
    apply (satisfies_kuratowskiPairEqAt_carrier
      hA
      (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) _).mpr
    change IndexedSequenceZF.sequenceCode xs =
      ZFSet.pair length.1 (IndexedSequenceZF.graph xs)
    rw [hlength]
    rfl

private theorem satisfies_sequenceValidity_sequenceCode_stageCarrier
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (xs : List ZFSet.{u})
    (hxs : ∀ x ∈ xs, x ∈ LStageZF delta) :
    FOFormula.Satisfies (zfCarrierMem A)
      sequenceValidityFormula
      ![⟨Ordinal.omega0.toZFSet, homegaA⟩,
        ⟨IndexedSequenceZF.sequenceCode xs,
          hsub (sequenceCode_mem_LStageZF_of_isSuccLimit hdelta hxs)⟩] := by
  rw [satisfies_sequenceValidityFormula_carrier
    hA]
  let length : Carrier A :=
    ⟨natCode xs.length,
      hsub (natCode_mem_LStageZF_of_isSuccLimit hdelta xs.length)⟩
  let graph : Carrier A :=
    ⟨IndexedSequenceZF.graph xs,
      hsub (graphFrom_mem_LStageZF_of_isSuccLimit hdelta hxs 0)⟩
  refine ⟨length, graph, rfl, ?_, ?_⟩
  · exact Ordinal.toZFSet_mem_toZFSet_iff.mpr
      (Ordinal.natCast_lt_omega0 xs.length)
  · intro index hindex
    rcases (mem_natCode_iff index.1 xs.length).mp hindex with
      ⟨k, hk, hindexEq⟩
    have hvalue : xs.get ⟨k, hk⟩ ∈ LStageZF delta :=
      hxs _ (List.get_mem xs ⟨k, hk⟩)
    let value : Carrier A :=
      ⟨xs.get ⟨k, hk⟩, hsub hvalue⟩
    refine ⟨value, ?_, ?_⟩
    · apply (mem_graph_iff xs _).mpr
      exact ⟨⟨k, hk⟩, by simp only [hindexEq, value]⟩
    · intro other hother
      rcases (mem_graph_iff xs _).mp hother with ⟨j, hpair⟩
      have hparts := ZFSet.pair_inj.mp hpair
      have hkj : k = j.1 := natCode_injective
        (hindexEq.symm.trans hparts.2)
      simpa only [value, hkj] using hparts.1

private theorem satisfies_successorFOAt_carrier
    {a : ZFSet.{u}} (ha : a.IsTransitive) {n : Nat}
    (successor predecessor : Fin n) (s : Tuple (Carrier a) n) :
    FOFormula.Satisfies (zfCarrierMem a)
        (Delta0Formula.successorFOAt successor predecessor) s ↔
      (s successor).1 = insert (s predecessor).1 (s predecessor).1 := by
  rw [Delta0Formula.successorFOAt,
    Delta0Formula.satisfies_toFO_absolute ha,
    Delta0Formula.satisfies_toFO,
    Delta0Formula.satisfies_successorAt]
  simp only [Delta0Formula.val_apply]





private theorem stackStepPrefixStageAssignment_val
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta) :
    (fun i => (stackStepPrefixStageAssignment hdelta hsub U hU i).1) =
      stackStepPrefixAssignment U := by
  funext i
  fin_cases i <;> rfl



private theorem traceStepExecutionStageAssignment_val
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta) (k : Nat) :
    (fun i => (traceStepExecutionStageAssignment hdelta hsub U hU program
      states hstateCodes k i).1) =
      traceStepAssignment U (stackProgramZFCode U program)
        (IndexedSequenceZF.sequenceCode (encodedStackStates states))
        (natCode k) := by
  funext i
  refine Fin.lastCases ?_ (fun i14 => ?_) i
  · rfl
  · refine Fin.lastCases ?_ (fun i13 => ?_) i14
    · rfl
    · refine Fin.lastCases ?_ (fun i12 => ?_) i13
      · rfl
      · simpa only [traceStepExecutionStageAssignment,
          traceStepAssignment, stackStepAssignment, snoc_castSucc] using
          congrFun (stackStepPrefixStageAssignment_val hdelta hsub U hU) i12

private theorem comp_traceStepProgramValueRename_execution_stage
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta) (k : Nat)
    (token input succ output : Carrier A) :
    (fun i => snoc (snoc (snoc (snoc
      (traceStepExecutionStageAssignment hdelta hsub U hU program states
        hstateCodes k) token) input) succ) output
        (traceStepProgramValueRename i)) =
      ![⟨stackProgramZFCode U program,
          hsub (stackProgramZFCode_mem_LStageZF_of_isSuccLimit
            hdelta hU program)⟩,
        ⟨natCode k,
          hsub (natCode_mem_LStageZF_of_isSuccLimit hdelta k)⟩, token] := by
  funext i
  fin_cases i <;> rfl

private theorem comp_traceStepInputValueRename_execution_stage
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta) (k : Nat)
    (token input succ output : Carrier A) :
    (fun i => snoc (snoc (snoc (snoc
      (traceStepExecutionStageAssignment hdelta hsub U hU program states
        hstateCodes k) token) input) succ) output
        (traceStepInputValueRename i)) =
      ![⟨IndexedSequenceZF.sequenceCode (encodedStackStates states),
          hsub (sequenceCode_mem_LStageZF_of_isSuccLimit hdelta hstateCodes)⟩,
        ⟨natCode k,
          hsub (natCode_mem_LStageZF_of_isSuccLimit hdelta k)⟩, input] := by
  funext i
  fin_cases i <;> rfl

private theorem comp_traceStepOutputValueRename_execution_stage
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta) (k : Nat)
    (token input succ output : Carrier A) :
    (fun i => snoc (snoc (snoc (snoc
      (traceStepExecutionStageAssignment hdelta hsub U hU program states
        hstateCodes k) token) input) succ) output
        (traceStepOutputValueRename i)) =
      ![⟨IndexedSequenceZF.sequenceCode (encodedStackStates states),
          hsub (sequenceCode_mem_LStageZF_of_isSuccLimit hdelta hstateCodes)⟩,
        succ, output] := by
  funext i
  fin_cases i <;> rfl

private theorem comp_traceStepStackStepRename_execution_stage
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta) (k : Nat)
    (token : StackToken (Option (Constructible.ZFCarrier U)))
    (input output : List ZFSet.{u})
    (hinput : ∀ x ∈ input, x ∈ LStageZF delta)
    (houtput : ∀ x ∈ output, x ∈ LStageZF delta)
    (succ : Carrier A) :
    (fun i => snoc (snoc (snoc (snoc
      (traceStepExecutionStageAssignment hdelta hsub U hU program states
        hstateCodes k)
      ⟨stackTokenZFCode U token,
        hsub (stackTokenZFCode_mem_LStageZF_of_isSuccLimit hdelta hU token)⟩)
      ⟨listCode input,
        hsub (listCode_mem_LStageZF_of_isSuccLimit hdelta hinput)⟩) succ)
      ⟨listCode output,
        hsub (listCode_mem_LStageZF_of_isSuccLimit hdelta houtput)⟩
      (traceStepStackStepRename i)) =
      stackStepStageAssignment hdelta hsub U hU token input output
        hinput houtput := by
  funext i
  apply Subtype.ext
  have hextendedVal :
      (fun j => (snoc (snoc (snoc (snoc
        (traceStepExecutionStageAssignment hdelta hsub U hU program states
          hstateCodes k)
        ⟨stackTokenZFCode U token,
          hsub (stackTokenZFCode_mem_LStageZF_of_isSuccLimit hdelta hU token)⟩)
        ⟨listCode input,
          hsub (listCode_mem_LStageZF_of_isSuccLimit hdelta hinput)⟩) succ)
        ⟨listCode output,
          hsub (listCode_mem_LStageZF_of_isSuccLimit hdelta houtput)⟩ j).1) =
        snoc (snoc (snoc (snoc
          (traceStepAssignment U (stackProgramZFCode U program)
            (IndexedSequenceZF.sequenceCode (encodedStackStates states))
            (natCode k))
          (stackTokenZFCode U token)) (listCode input)) succ.1)
          (listCode output) := by
    rw [Model.subtypeVal_snoc, Model.subtypeVal_snoc,
      Model.subtypeVal_snoc, Model.subtypeVal_snoc,
      traceStepExecutionStageAssignment_val]
  have hraw := congrFun
    (comp_traceStepStackStepRename U (stackProgramZFCode U program)
      (IndexedSequenceZF.sequenceCode (encodedStackStates states))
      (natCode k) (stackTokenZFCode U token) (listCode input)
      succ.1 (listCode output)) i
  rw [congrFun hextendedVal (traceStepStackStepRename i),
    congrFun (stackStepStageAssignment_val hdelta hsub U hU token input
      output hinput houtput) i]
  exact hraw

private theorem satisfies_traceStepFormula_execution_stageCarrier
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (states : List (List ZFSet.{u}))
    (htrace : ExecutionTrace (rudimentaryGenerator U) program states)
    (hstates : ∀ stack ∈ states,
      ∀ x ∈ stack, x ∈ LStageZF delta)
    (k : Nat) (hk : k < program.length) :
    FOFormula.Satisfies (zfCarrierMem A) traceStepFormula
      (traceStepExecutionStageAssignment hdelta hsub U hU program states
        (encodedStackStates_entries_mem_LStageZF hdelta hstates) k) := by
  have hlength := htrace.length
  have hi : k < states.length := by omega
  have ho : k + 1 < states.length := by omega
  let token := program.get ⟨k, hk⟩
  let input := states.get ⟨k, hi⟩
  let output := states.get ⟨k + 1, ho⟩
  have hinput : ∀ x ∈ input, x ∈ LStageZF delta :=
    hstates input (List.get_mem states ⟨k, hi⟩)
  have houtput : ∀ x ∈ output, x ∈ LStageZF delta :=
    hstates output (List.get_mem states ⟨k + 1, ho⟩)
  let tokenStage : Carrier A :=
    ⟨stackTokenZFCode U token,
      hsub (stackTokenZFCode_mem_LStageZF_of_isSuccLimit hdelta hU token)⟩
  let inputStage : Carrier A :=
    ⟨listCode input,
      hsub (listCode_mem_LStageZF_of_isSuccLimit hdelta hinput)⟩
  let succStage : Carrier A :=
    ⟨natCode (k + 1),
      hsub (natCode_mem_LStageZF_of_isSuccLimit hdelta (k + 1))⟩
  let outputStage : Carrier A :=
    ⟨listCode output,
      hsub (listCode_mem_LStageZF_of_isSuccLimit hdelta houtput)⟩
  rw [traceStepFormula]
  refine ⟨tokenStage, inputStage, succStage, outputStage, ?_⟩
  rw [traceStepBody]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [FOFormula.satisfies_rename,
      comp_traceStepProgramValueRename_execution_stage]
    apply (satisfies_valueAtFormula_stageCarrier_iff hA hdelta hsub
      (encodedStackProgram U program) (by
        intro code hcode
        rcases List.mem_map.mp hcode with ⟨item, _hitem, rfl⟩
        exact stackTokenZFCode_mem_LStageZF_of_isSuccLimit
          hdelta hU item) k tokenStage).mpr
    refine ⟨by simpa only [encodedStackProgram, List.length_map] using hk, ?_⟩
    simp only [encodedStackProgram, tokenStage, token,
      List.get_eq_getElem, List.getElem_map]
  · rw [FOFormula.satisfies_rename,
      comp_traceStepInputValueRename_execution_stage]
    apply (satisfies_valueAtFormula_stageCarrier_iff hA hdelta hsub
      (encodedStackStates states)
      (encodedStackStates_entries_mem_LStageZF hdelta hstates)
      k inputStage).mpr
    refine ⟨by simpa only [encodedStackStates, List.length_map] using hi, ?_⟩
    simp only [encodedStackStates, inputStage, input,
      List.get_eq_getElem, List.getElem_map]
  · apply (satisfies_successorFOAt_carrier
      hA (18 : Fin 20) (15 : Fin 20) _).mpr
    exact natCode_succ_eq_insert k
  · rw [FOFormula.satisfies_rename,
      comp_traceStepOutputValueRename_execution_stage]
    apply (satisfies_valueAtFormula_stageCarrier_iff hA hdelta hsub
      (encodedStackStates states)
      (encodedStackStates_entries_mem_LStageZF hdelta hstates)
      (k + 1) outputStage).mpr
    refine ⟨by simpa only [encodedStackStates, List.length_map] using ho, ?_⟩
    simp only [encodedStackStates, outputStage, output,
      List.get_eq_getElem, List.getElem_map]
  · rw [FOFormula.satisfies_rename,
      comp_traceStepStackStepRename_execution_stage
        (hinput := hinput) (houtput := houtput)]
    apply satisfies_stackStepFormula_stageCarrier_of_run
      hA hdelta hsub U hU token input output hinput houtput
    rcases htrace.indexed with ⟨_hlength, hsteps⟩
    simpa only [token, input, output] using hsteps ⟨k, hk⟩



private theorem stackProgramEvalCoreExecutionStageAssignment_val
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ LStageZF delta)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta) :
    (fun i => (stackProgramEvalCoreExecutionStageAssignment hdelta hsub homegaA
      U hU program result hresult states hstateCodes i).1) =
      snoc (snoc (snoc (snoc
        (stackProgramEvalAssignment U (stackProgramZFCode U program)
          result)
        (IndexedSequenceZF.sequenceCode (encodedStackStates states)))
        (natCode program.length)) (natCode states.length))
        (listCode [result]) := by
  funext i
  refine Fin.lastCases ?_ (fun i19 => ?_) i
  · rfl
  · refine Fin.lastCases ?_ (fun i18 => ?_) i19
    · rfl
    · refine Fin.lastCases ?_ (fun i17 => ?_) i18
      · rfl
      · refine Fin.lastCases ?_ (fun i16 => ?_) i17
        · rfl
        · refine Fin.lastCases ?_ (fun i15 => ?_) i16
          · rfl
          · refine Fin.lastCases ?_ (fun i14 => ?_) i15
            · rfl
            · refine Fin.lastCases ?_ (fun i13 => ?_) i14
              · rfl
              · simpa only [stackProgramEvalCoreExecutionStageAssignment,
                  stackProgramEvalAssignment, stackStepAssignment,
                  snoc_castSucc] using congrFun
                    (stackStepPrefixStageAssignment_val hdelta hsub U hU) i13













private theorem satisfies_evalTraceSteps_execution_stageCarrier
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ LStageZF delta)
    (states : List (List ZFSet.{u}))
    (htrace : ExecutionTrace (rudimentaryGenerator U) program states)
    (hstates : ∀ stack ∈ states,
      ∀ x ∈ stack, x ∈ LStageZF delta)
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta) :
    FOFormula.Satisfies (zfCarrierMem A)
      (FOFormula.boundedAll (17 : Fin 20)
        (FOFormula.rename evalTraceStepRename traceStepFormula))
      (stackProgramEvalCoreExecutionStageAssignment hdelta hsub homegaA U hU program
        result hresult states hstateCodes) := by
  rw [FOFormula.satisfies_boundedAll]
  intro index hindex
  change index.1 ∈ natCode program.length at hindex
  rcases (mem_natCode_iff index.1 program.length).mp hindex with
    ⟨k, hk, hindexValue⟩
  have hindexEq : index =
      (⟨natCode k,
        hsub (natCode_mem_LStageZF_of_isSuccLimit hdelta k)⟩ :
        Carrier A) := Subtype.ext hindexValue
  subst index
  rw [FOFormula.satisfies_rename]
  have hlocal := satisfies_traceStepFormula_execution_stageCarrier
    hA hdelta hsub U hU program states htrace hstates k hk
  apply (satisfies_congr_assignment (zfCarrierMem A)
    traceStepFormula _ _ ?_).mpr hlocal
  intro i
  apply Subtype.ext
  have hextendedVal :
      (fun j => (snoc
        (stackProgramEvalCoreExecutionStageAssignment hdelta hsub homegaA U hU program
          result hresult states hstateCodes)
        (⟨natCode k,
          hsub (natCode_mem_LStageZF_of_isSuccLimit hdelta k)⟩ :
          Carrier A) j).1) =
        snoc (snoc (snoc (snoc (snoc
          (stackProgramEvalAssignment U (stackProgramZFCode U program)
            result)
          (IndexedSequenceZF.sequenceCode (encodedStackStates states)))
          (natCode program.length)) (natCode states.length))
          (listCode [result])) (natCode k) := by
    rw [Model.subtypeVal_snoc,
      stackProgramEvalCoreExecutionStageAssignment_val]
  have hraw := congrFun
    (comp_evalTraceStepRename U (stackProgramZFCode U program)
      result (IndexedSequenceZF.sequenceCode (encodedStackStates states))
      (natCode program.length) (natCode states.length)
      (listCode [result]) (natCode k)) i
  rw [congrFun hextendedVal (evalTraceStepRename i),
    congrFun (traceStepExecutionStageAssignment_val hdelta hsub U hU program
      states (encodedStackStates_entries_mem_LStageZF hdelta hstates) k) i]
  exact hraw

private theorem satisfies_evalProgramLength_execution_stageCarrier
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ LStageZF delta)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta) :
    FOFormula.Satisfies (zfCarrierMem A)
      (FOFormula.rename evalProgramLengthRename hasLengthFormula)
      (stackProgramEvalCoreExecutionStageAssignment hdelta hsub homegaA U hU program
        result hresult states hstateCodes) := by
  have hprogramCodes : ∀ code ∈ encodedStackProgram U program,
      code ∈ LStageZF delta := by
    intro code hcode
    rcases List.mem_map.mp hcode with ⟨token, _htoken, rfl⟩
    exact stackTokenZFCode_mem_LStageZF_of_isSuccLimit hdelta hU token
  let programLength : Carrier A :=
    ⟨natCode program.length,
      hsub (natCode_mem_LStageZF_of_isSuccLimit hdelta program.length)⟩
  rw [FOFormula.satisfies_rename]
  have hcomp :
      (fun i => stackProgramEvalCoreExecutionStageAssignment hdelta hsub homegaA U hU
        program result hresult states hstateCodes
          (evalProgramLengthRename i)) =
        ![⟨stackProgramZFCode U program,
            hsub (stackProgramZFCode_mem_LStageZF_of_isSuccLimit
              hdelta hU program)⟩, programLength] := by
    funext i
    fin_cases i <;> rfl
  rw [hcomp]
  apply (satisfies_hasLengthFormula_stageCarrier_iff hA hdelta hsub
    (encodedStackProgram U program) hprogramCodes programLength).mpr
  simp only [programLength, encodedStackProgram, List.length_map]

private theorem satisfies_evalTraceLength_execution_stageCarrier
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ LStageZF delta)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta) :
    FOFormula.Satisfies (zfCarrierMem A)
      (FOFormula.rename evalTraceLengthRename hasLengthFormula)
      (stackProgramEvalCoreExecutionStageAssignment hdelta hsub homegaA U hU program
        result hresult states hstateCodes) := by
  let traceLength : Carrier A :=
    ⟨natCode states.length,
      hsub (natCode_mem_LStageZF_of_isSuccLimit hdelta states.length)⟩
  rw [FOFormula.satisfies_rename]
  have hcomp :
      (fun i => stackProgramEvalCoreExecutionStageAssignment hdelta hsub homegaA U hU
        program result hresult states hstateCodes
          (evalTraceLengthRename i)) =
        ![⟨IndexedSequenceZF.sequenceCode (encodedStackStates states),
            hsub (sequenceCode_mem_LStageZF_of_isSuccLimit hdelta hstateCodes)⟩,
          traceLength] := by
    funext i
    fin_cases i <;> rfl
  rw [hcomp]
  apply (satisfies_hasLengthFormula_stageCarrier_iff hA hdelta hsub
    (encodedStackStates states) hstateCodes traceLength).mpr
  simp only [traceLength, encodedStackStates, List.length_map]

private theorem satisfies_evalSuccessor_execution_stageCarrier
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ LStageZF delta)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta)
    (hlength : states.length = program.length + 1) :
    FOFormula.Satisfies (zfCarrierMem A)
      (Delta0Formula.successorFOAt (18 : Fin 20) (17 : Fin 20))
      (stackProgramEvalCoreExecutionStageAssignment hdelta hsub homegaA U hU
        program result hresult states hstateCodes) := by
  apply (satisfies_successorFOAt_carrier
    hA (18 : Fin 20) (17 : Fin 20) _).mpr
  change natCode states.length =
    insert (natCode program.length) (natCode program.length)
  rw [hlength]
  exact natCode_succ_eq_insert program.length



private theorem comp_evalInitialValueRename_execution_stageCarrier
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ LStageZF delta)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta) :
    (fun i => stackProgramEvalCoreExecutionStageAssignment hdelta hsub homegaA
      U hU program result hresult states hstateCodes
        (evalInitialValueRename i)) =
      ![⟨IndexedSequenceZF.sequenceCode (encodedStackStates states),
          hsub (sequenceCode_mem_LStageZF_of_isSuccLimit hdelta hstateCodes)⟩,
        (⟨∅, hsub (empty_mem_LStageZF_of_isSuccLimit hdelta)⟩ :
          Carrier A),
        (⟨∅, hsub (empty_mem_LStageZF_of_isSuccLimit hdelta)⟩ :
          Carrier A)] := by
  funext i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun x => ?_) j) i
  · exact stackProgramEvalCoreExecutionStageAssignment_trace
      hdelta hsub homegaA U hU program result hresult states hstateCodes
  · exact stackProgramEvalCoreExecutionStageAssignment_empty
      hdelta hsub homegaA U hU program result hresult states hstateCodes
  · fin_cases x
    exact stackProgramEvalCoreExecutionStageAssignment_empty
      hdelta hsub homegaA U hU program result hresult states hstateCodes

private theorem satisfies_valueAt_zero_encodedStackStates_stageCarrier
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta)
    (hstatesNonempty : 0 < states.length)
    (hhead : states.head? = some []) :
    FOFormula.Satisfies (zfCarrierMem A) valueAtFormula
      ![⟨IndexedSequenceZF.sequenceCode (encodedStackStates states),
          hsub (sequenceCode_mem_LStageZF_of_isSuccLimit hdelta hstateCodes)⟩,
        (⟨∅, hsub (empty_mem_LStageZF_of_isSuccLimit hdelta)⟩ :
          Carrier A),
        (⟨∅, hsub (empty_mem_LStageZF_of_isSuccLimit hdelta)⟩ :
          Carrier A)] := by
  rcases exists_encodedStackStates_zero_eq states hstatesNonempty hhead with
    ⟨hzero, hrawHead⟩
  let emptyStage : Carrier A :=
    ⟨∅, hsub (empty_mem_LStageZF_of_isSuccLimit hdelta)⟩
  let zeroStage : Carrier A :=
    ⟨natCode 0, hsub (natCode_mem_LStageZF_of_isSuccLimit hdelta 0)⟩
  have hvalue :
      FOFormula.Satisfies (zfCarrierMem A) valueAtFormula
        ![⟨IndexedSequenceZF.sequenceCode (encodedStackStates states),
            hsub (sequenceCode_mem_LStageZF_of_isSuccLimit hdelta hstateCodes)⟩,
          zeroStage, emptyStage] := by
    exact (satisfies_valueAtFormula_stageCarrier_iff hA hdelta hsub
      (encodedStackStates states) hstateCodes 0 emptyStage).mpr
        ⟨hzero, hrawHead⟩
  apply (satisfies_congr_assignment (zfCarrierMem A)
    valueAtFormula _ _ ?_).mpr hvalue
  intro i
  fin_cases i
  · rfl
  · apply Subtype.ext
    change (∅ : ZFSet.{u}) = natCode 0
    simp [natCode]
  · rfl

private theorem satisfies_evalInitial_execution_stageCarrier
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ LStageZF delta)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta)
    (hlength : states.length = program.length + 1)
    (hhead : states.head? = some []) :
    FOFormula.Satisfies (zfCarrierMem A)
      (FOFormula.rename evalInitialValueRename valueAtFormula)
      (stackProgramEvalCoreExecutionStageAssignment hdelta hsub homegaA U hU
        program result hresult states hstateCodes) := by
  have hvalue := satisfies_valueAt_zero_encodedStackStates_stageCarrier
    hA hdelta hsub states hstateCodes (by omega) hhead
  rw [FOFormula.satisfies_rename]
  apply (satisfies_congr_assignment (zfCarrierMem A)
    valueAtFormula _ _ ?_).mpr hvalue
  intro i
  exact congrFun
    (comp_evalInitialValueRename_execution_stageCarrier hdelta hsub homegaA
      U hU program result hresult states hstateCodes) i

private theorem satisfies_evalFinal_execution_stageCarrier
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ LStageZF delta)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta)
    (hlength : states.length = program.length + 1)
    (hlast : states.getLast? = some [result]) :
    FOFormula.Satisfies (zfCarrierMem A)
      (FOFormula.rename evalFinalValueRename valueAtFormula)
      (stackProgramEvalCoreExecutionStageAssignment hdelta hsub homegaA U hU
        program result hresult states hstateCodes) := by
  have hrawLast :
      (encodedStackStates states).getLast? = some (listCode [result]) := by
    simp only [encodedStackStates, List.getLast?_map, hlast,
      Option.map_some]
  have hrawLength :
      (encodedStackStates states).length = program.length + 1 := by
    simpa only [encodedStackStates, List.length_map] using hlength
  have hprogramLength : program.length < (encodedStackStates states).length :=
    by omega
  have hrawLastGet :
      listCode [result] = (encodedStackStates states).get
        ⟨program.length, hprogramLength⟩ := by
    have hgetLast :
        (encodedStackStates states).getLast? =
          some ((encodedStackStates states).get
            ⟨program.length, hprogramLength⟩) := by
      rw [List.getLast?_eq_getElem?]
      have hindex :
          (encodedStackStates states).length - 1 = program.length := by
        omega
      rw [hindex, List.getElem?_eq_getElem hprogramLength]
      rfl
    rw [hgetLast] at hrawLast
    exact (Option.some.inj hrawLast).symm
  let finalStack : Carrier A :=
    ⟨listCode [result],
      hsub (listCode_mem_LStageZF_of_isSuccLimit hdelta (by
        intro x hx
        simp only [List.mem_singleton] at hx
        subst x
        exact hresult))⟩
  rw [FOFormula.satisfies_rename]
  have hcomp :
      (fun i => stackProgramEvalCoreExecutionStageAssignment hdelta hsub homegaA
        U hU program result hresult states hstateCodes
          (evalFinalValueRename i)) =
        ![⟨IndexedSequenceZF.sequenceCode (encodedStackStates states),
            hsub (sequenceCode_mem_LStageZF_of_isSuccLimit hdelta hstateCodes)⟩,
          ⟨natCode program.length,
            hsub (natCode_mem_LStageZF_of_isSuccLimit hdelta program.length)⟩,
          finalStack] := by
    funext i
    fin_cases i
    · exact stackProgramEvalCoreExecutionStageAssignment_trace
        hdelta hsub homegaA U hU program result hresult states hstateCodes
    · exact stackProgramEvalCoreExecutionStageAssignment_programLength
        hdelta hsub homegaA U hU program result hresult states hstateCodes
    · apply Subtype.ext
      exact stackProgramEvalCoreExecutionStageAssignment_finalStack
        hdelta hsub homegaA U hU program result hresult states hstateCodes
  rw [hcomp]
  apply (satisfies_valueAtFormula_stageCarrier_iff hA hdelta hsub
    (encodedStackStates states) hstateCodes program.length finalStack).mpr
  exact ⟨hprogramLength, hrawLastGet⟩

private theorem satisfies_evalFinalStack_execution_stageCarrier
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ LStageZF delta)
    (states : List (List ZFSet.{u}))
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta) :
    FOFormula.Satisfies (zfCarrierMem A)
      (Delta0Formula.kuratowskiPairEqAt
        (19 : Fin 20) (15 : Fin 20) (3 : Fin 20)).toFO
      (stackProgramEvalCoreExecutionStageAssignment hdelta hsub homegaA U hU
        program result hresult states hstateCodes) := by
  apply (satisfies_kuratowskiPairEqAt_carrier
    hA
    (19 : Fin 20) (15 : Fin 20) (3 : Fin 20) _).mpr
  rw [stackProgramEvalCoreExecutionStageAssignment_finalStack,
    stackProgramEvalCoreExecutionStageAssignment_result]
  have hempty := congrArg Subtype.val
    (stackProgramEvalCoreExecutionStageAssignment_empty hdelta hsub homegaA
      U hU program result hresult states hstateCodes)
  rw [hempty]
  rfl

private theorem satisfies_stackProgramEvalCore_execution_stageCarrier
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ LStageZF delta)
    (states : List (List ZFSet.{u}))
    (htrace : ExecutionTrace (rudimentaryGenerator U) program states)
    (hhead : states.head? = some [])
    (hlast : states.getLast? = some [result])
    (hstates : ∀ stack ∈ states,
      ∀ x ∈ stack, x ∈ LStageZF delta)
    (hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta) :
    FOFormula.Satisfies (zfCarrierMem A)
      stackProgramEvalCore
      (stackProgramEvalCoreExecutionStageAssignment hdelta hsub homegaA U hU
        program result hresult states hstateCodes) := by
  rw [stackProgramEvalCore]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact satisfies_evalProgramLength_execution_stageCarrier
      hA hdelta hsub homegaA U hU program result hresult states hstateCodes
  · exact satisfies_evalTraceLength_execution_stageCarrier
      hA hdelta hsub homegaA U hU program result hresult states hstateCodes
  · exact satisfies_evalSuccessor_execution_stageCarrier
      hA hdelta hsub homegaA U hU program result hresult states hstateCodes
        htrace.length
  · exact satisfies_evalInitial_execution_stageCarrier
      hA hdelta hsub homegaA U hU program result hresult states hstateCodes
        htrace.length hhead
  · exact satisfies_evalFinal_execution_stageCarrier
      hA hdelta hsub homegaA U hU program result hresult states hstateCodes
        htrace.length hlast
  · exact satisfies_evalFinalStack_execution_stageCarrier
      hA hdelta hsub homegaA U hU program result hresult states hstateCodes
  · exact satisfies_evalTraceSteps_execution_stageCarrier
      hA hdelta hsub homegaA U hU program result hresult states htrace hstates
        hstateCodes







private theorem satisfies_stackProgramEvalFormula_stageCarrier_of_run
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U : ZFSet.{u}) (hU : U ∈ LStageZF delta)
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) (hresult : result ∈ LStageZF delta)
    (hrun : runStackProgram (rudimentaryGenerator U) program [] =
      some [result]) :
    FOFormula.Satisfies (zfCarrierMem A)
      stackProgramEvalFormula
      (stackProgramEvalStageAssignment hdelta hsub homegaA U hU program
        result (hsub hresult)) := by
  rcases exists_executionTrace_of_run
      (rudimentaryGenerator U) program [] [result] hrun with
    ⟨states, htrace, hhead, hlast⟩
  have hstates : ∀ stack ∈ states,
      ∀ x ∈ stack, x ∈ LStageZF delta :=
    htrace.entries_mem_LStageZF_of_isSuccLimit hdelta hU hhead (by simp)
  have hstateCodes : ∀ code ∈ encodedStackStates states,
      code ∈ LStageZF delta :=
    encodedStackStates_entries_mem_LStageZF hdelta hstates
  have hprogramCodes : ∀ code ∈ encodedStackProgram U program,
      code ∈ LStageZF delta := by
    intro code hcode
    rcases List.mem_map.mp hcode with ⟨token, _htoken, rfl⟩
    exact stackTokenZFCode_mem_LStageZF_of_isSuccLimit hdelta hU token
  let omegaStage : Carrier A :=
    ⟨Ordinal.omega0.toZFSet, homegaA⟩
  let programStage : Carrier A :=
    ⟨stackProgramZFCode U program,
      hsub (stackProgramZFCode_mem_LStageZF_of_isSuccLimit hdelta hU program)⟩
  let traceStage : Carrier A :=
    ⟨IndexedSequenceZF.sequenceCode (encodedStackStates states),
      hsub (sequenceCode_mem_LStageZF_of_isSuccLimit hdelta hstateCodes)⟩
  let programLengthStage : Carrier A :=
    ⟨natCode program.length,
      hsub (natCode_mem_LStageZF_of_isSuccLimit hdelta program.length)⟩
  let traceLengthStage : Carrier A :=
    ⟨natCode states.length,
      hsub (natCode_mem_LStageZF_of_isSuccLimit hdelta states.length)⟩
  let finalStackStage : Carrier A :=
    ⟨listCode [result],
      hsub (listCode_mem_LStageZF_of_isSuccLimit hdelta (by
        intro x hx
        simp only [List.mem_singleton] at hx
        subst x
        exact hresult))⟩
  let baseAssignment :=
    stackProgramEvalStageAssignment hdelta hsub homegaA U hU program
      result (hsub hresult)
  let traceContext : Tuple (Carrier A) 17 :=
    snoc baseAssignment traceStage
  rw [stackProgramEvalFormula]
  refine ⟨?_, traceStage, ?_, programLengthStage,
    traceLengthStage, finalStackStage, ?_⟩
  · rw [FOFormula.satisfies_rename]
    have hcomp :
        (fun i => baseAssignment (evalProgramValidityRename i)) =
          ![omegaStage, programStage] := by
      funext i
      fin_cases i <;> rfl
    rw [hcomp]
    simpa only [programStage, stackProgramZFCode,
      encodedStackProgram] using
      (satisfies_sequenceValidity_sequenceCode_stageCarrier
        hA hdelta hsub homegaA
          (encodedStackProgram U program) hprogramCodes)
  · rw [FOFormula.satisfies_rename]
    have hcomp :
        (fun i => traceContext (evalTraceValidityRename i)) =
          ![omegaStage, traceStage] := by
      funext i
      fin_cases i <;> rfl
    rw [hcomp]
    exact satisfies_sequenceValidity_sequenceCode_stageCarrier
      hA hdelta hsub homegaA (encodedStackStates states) hstateCodes
  · exact satisfies_stackProgramEvalCore_execution_stageCarrier
      hA hdelta hsub homegaA U hU program result hresult states htrace hhead hlast
        hstates hstateCodes





/-! ## The output formula over a limit stage -/



private theorem godelDefOutputStageAssignment_val
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U nextU : ZFSet.{u})
    (hU : U ∈ LStageZF delta) (hnextU : nextU ∈ A) :
    (fun i => (godelDefOutputStageAssignment hdelta hsub homegaA
      U nextU hU hnextU i).1) =
      Model.bareGodelDefOutputRawAssignment
        Model.stageHistoryFixedParametersRaw U nextU := by
  funext i
  refine Fin.lastCases ?_ (fun i14 => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun i13 => ?_) i14
    · rfl
    · fin_cases i13 <;> rfl



private theorem stackProgramEvalCodeStageAssignment_val
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U code result : ZFSet.{u})
    (hU : U ∈ LStageZF delta) (hcode : code ∈ A)
    (hresult : result ∈ A) :
    (fun i => (stackProgramEvalCodeStageAssignment hdelta hsub homegaA U code
      result hU hcode hresult i).1) =
      stackProgramEvalAssignment U code result := by
  funext i
  refine Fin.lastCases ?_ (fun i14 => ?_) i
  · rfl
  · refine Fin.lastCases ?_ (fun i13 => ?_) i14
    · rfl
    · refine Fin.lastCases ?_ (fun i12 => ?_) i13
      · rfl
      · simpa only [stackProgramEvalCodeStageAssignment,
          stackProgramEvalAssignment, snoc_castSucc] using
          congrFun (stackStepPrefixStageAssignment_val hdelta hsub U hU) i12

private theorem comp_godelDefEvalRename_stage
    {A : ZFSet.{u}} {delta : Ordinal.{u}}
    (hdelta : Order.IsSuccLimit delta) (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U nextU result code : ZFSet.{u})
    (hU : U ∈ LStageZF delta) (hnextU : nextU ∈ A)
    (hresult : result ∈ A) (hcode : code ∈ A) :
    (fun i => snoc (snoc
      (godelDefOutputStageAssignment hdelta hsub homegaA U nextU hU hnextU)
      ⟨result, hresult⟩) ⟨code, hcode⟩ (godelDefEvalRename i)) =
      stackProgramEvalCodeStageAssignment hdelta hsub homegaA U code result
        hU hcode hresult := by
  funext i
  refine Fin.lastCases ?_ (fun i14 => ?_) i
  · rfl
  · refine Fin.lastCases ?_ (fun i13 => ?_) i14
    · rfl
    · simp only [godelDefEvalRename, Fin.lastCases_castSucc,
        godelDefOutputStageAssignment,
        stackProgramEvalCodeStageAssignment, snoc_castSucc]

private theorem satisfies_godelDefSubset_stageCarrier
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U nextU result : ZFSet.{u})
    (hU : U ∈ LStageZF delta) (hnextU : nextU ∈ A)
    (hresult : result ∈ A) :
    FOFormula.Satisfies (zfCarrierMem A)
      (Delta0Formula.subsetAt (15 : Fin 16) (0 : Fin 16)).toFO
      (snoc (godelDefOutputStageAssignment hdelta hsub homegaA
        U nextU hU hnextU) ⟨result, hresult⟩) ↔ result ⊆ U := by
  rw [Delta0Formula.satisfies_toFO_absolute
      hA,
    Delta0Formula.satisfies_toFO,
    Delta0Formula.satisfies_subsetAt]
  change result ⊆ U ↔ result ⊆ U
  rfl

private theorem satisfies_godelDefOutputFormula_components_stageCarrier
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U nextU : ZFSet.{u})
    (hU : U ∈ LStageZF delta) (hnextU : nextU ∈ A) :
    FOFormula.Satisfies (zfCarrierMem A)
      godelDefOutputFormula
      (godelDefOutputStageAssignment hdelta hsub homegaA
        U nextU hU hnextU) ↔
      ∀ result : Carrier A,
        result.1 ∈ nextU ↔ result.1 ⊆ U ∧
          ∃ code : Carrier A,
            FOFormula.Satisfies (zfCarrierMem A)
              stackProgramEvalFormula
              (stackProgramEvalCodeStageAssignment hdelta hsub homegaA
                U code.1 result.1 hU code.2 result.2) := by
  simp only [godelDefOutputFormula, FOFormula.satisfies_all,
    FOFormula.satisfies_biimp]
  apply forall_congr'
  intro result
  change
    (result.1 ∈ nextU ↔
      FOFormula.Satisfies (zfCarrierMem A)
          (Delta0Formula.subsetAt (15 : Fin 16) (0 : Fin 16)).toFO
          (snoc (godelDefOutputStageAssignment hdelta hsub homegaA
            U nextU hU hnextU) result) ∧
        ∃ code : Carrier A,
          FOFormula.Satisfies (zfCarrierMem A)
            (FOFormula.rename godelDefEvalRename stackProgramEvalFormula)
            (snoc (snoc (godelDefOutputStageAssignment hdelta hsub homegaA
              U nextU hU hnextU) result) code)) ↔ _
  rw [satisfies_godelDefSubset_stageCarrier hA]
  simp only [FOFormula.satisfies_rename,
    comp_godelDefEvalRename_stage]

private theorem rudimentaryClosureTerm_eval_mem_LStageZF_of_isSuccLimit
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    {U : ZFSet.{u}} (hU : U ∈ LStageZF theta)
    (term : RudimentaryClosureTerm U) :
    term.eval ∈ LStageZF theta := by
  induction term with
  | var generator =>
      cases generator with
      | none => exact hU
      | some x =>
          exact (LStageZF_isTransitive theta).mem_trans x.2 hU
  | app i left right hleft hright =>
      exact op_mem_LStageZF_of_isSuccLimit htheta i hleft hright

private theorem godelDef_element_mem_LStageZF_of_isSuccLimit
    {theta : Ordinal.{u}} (htheta : Order.IsSuccLimit theta)
    {U result : ZFSet.{u}} (hU : U ∈ LStageZF theta)
    (hresult : result ∈ godelDef U) : result ∈ LStageZF theta := by
  rcases mem_godelDef_iff_exists_rudimentaryTerm.mp hresult with
    ⟨_hsubset, term, hterm⟩
  rw [← hterm]
  exact rudimentaryClosureTerm_eval_mem_LStageZF_of_isSuccLimit
    htheta hU term

private theorem satisfies_godelDefOutputFormula_stageCarrier_iff
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U nextU : ZFSet.{u})
    (hU : U ∈ LStageZF delta) (hnextU : nextU ∈ A) :
    FOFormula.Satisfies (zfCarrierMem A)
      godelDefOutputFormula
      (godelDefOutputStageAssignment hdelta hsub homegaA
        U nextU hU hnextU) ↔ nextU = godelDef U := by
  rw [satisfies_godelDefOutputFormula_components_stageCarrier hA]
  constructor
  · intro h
    apply ZFSet.ext
    intro result
    constructor
    · intro hnext
      have hresultA : result ∈ A := hA.mem_trans hnext hnextU
      let resultStage : Carrier A := ⟨result, hresultA⟩
      rcases (h resultStage).mp hnext with ⟨hsubset, code, heval⟩
      have hambient := stackProgramEval_carrier_to_ambient
        hA _ heval
      rw [stackProgramEvalCodeStageAssignment_val] at hambient
      rcases (satisfies_stackProgramEvalFormula_iff_exists_run
        U code.1 result).mp hambient with
        ⟨program, _hrep, hrun⟩
      exact mem_godelDef_iff.mpr
        ⟨hsubset, mem_rudimentaryClosure_of_runStackProgram
          U program result hrun⟩
    · intro hgodel
      have hresultDelta : result ∈ LStageZF delta :=
        godelDef_element_mem_LStageZF_of_isSuccLimit hdelta hU hgodel
      let resultStage : Carrier A := ⟨result, hsub hresultDelta⟩
      apply (h resultStage).mpr
      have hparts := mem_godelDef_iff.mp hgodel
      rcases mem_rudimentaryClosure_iff_exists_term.mp hparts.2 with
        ⟨term, hterm⟩
      let program := stackProgram term
      have hrun : runStackProgram (rudimentaryGenerator U) program [] =
          some [result] := by
        simp only [program, run_stackProgram, hterm]
      let code : Carrier A :=
        ⟨stackProgramZFCode U program,
          hsub (stackProgramZFCode_mem_LStageZF_of_isSuccLimit
            hdelta hU program)⟩
      refine ⟨hparts.1, code, ?_⟩
      have heval := satisfies_stackProgramEvalFormula_stageCarrier_of_run
        hA hdelta hsub homegaA U hU program result hresultDelta hrun
      change FOFormula.Satisfies (zfCarrierMem A)
        stackProgramEvalFormula
        (stackProgramEvalCodeStageAssignment hdelta hsub homegaA
          U code.1 result hU code.2 (hsub hresultDelta))
      simpa only [code, program, stackProgramEvalStageAssignment,
        stackProgramEvalCodeStageAssignment] using heval
  · intro hnext result
    rw [hnext, mem_godelDef_iff]
    constructor
    · rintro ⟨hsubset, hclosure⟩
      have hresultDelta : result.1 ∈ LStageZF delta :=
        godelDef_element_mem_LStageZF_of_isSuccLimit hdelta hU
          (mem_godelDef_iff.mpr ⟨hsubset, hclosure⟩)
      rcases mem_rudimentaryClosure_iff_exists_term.mp hclosure with
        ⟨term, hterm⟩
      let program := stackProgram term
      have hrun : runStackProgram (rudimentaryGenerator U) program [] =
          some [result.1] := by
        simp only [program, run_stackProgram, hterm]
      let code : Carrier A :=
        ⟨stackProgramZFCode U program,
          hsub (stackProgramZFCode_mem_LStageZF_of_isSuccLimit
            hdelta hU program)⟩
      refine ⟨hsubset, code, ?_⟩
      have heval := satisfies_stackProgramEvalFormula_stageCarrier_of_run
        hA hdelta hsub homegaA U hU program result.1 hresultDelta hrun
      change FOFormula.Satisfies (zfCarrierMem A)
        stackProgramEvalFormula
        (stackProgramEvalCodeStageAssignment hdelta hsub homegaA
          U code.1 result.1 hU code.2 result.2)
      simpa only [code, program, stackProgramEvalStageAssignment,
        stackProgramEvalCodeStageAssignment] using heval
    · rintro ⟨hsubset, code, heval⟩
      have hambient := stackProgramEval_carrier_to_ambient
        hA _ heval
      rw [stackProgramEvalCodeStageAssignment_val] at hambient
      rcases (satisfies_stackProgramEvalFormula_iff_exists_run
        U code.1 result.1).mp hambient with
        ⟨program, _hrep, hrun⟩
      exact ⟨hsubset,
        mem_rudimentaryClosure_of_runStackProgram
          U program result.1 hrun⟩

/-- Pointwise correctness of the internal Goedel-definability output formula
in a transitive carrier containing a nonzero limit level with all canonical
finite witnesses.  Only the predecessor `U` is required to lie in that
sublevel; the candidate output may be any element of the ambient carrier. -/
private theorem bareGodelDefOutputIn_of_isSuccLimit_substage_iff
    {A : ZFSet.{u}} (hA : A.IsTransitive)
    {delta : Ordinal.{u}} (hdelta : Order.IsSuccLimit delta)
    (hsub : LStageZF delta ⊆ A)
    (homegaA : Ordinal.omega0.toZFSet ∈ A)
    (U nextU : ZFSet.{u})
    (hU : U ∈ LStageZF delta) (hnextU : nextU ∈ A) :
    Model.BareGodelDefOutputIn (A : Set ZFSet.{u})
        Model.stageHistoryFixedParametersRaw U nextU ↔
      nextU = godelDef U := by
  let s := godelDefOutputStageAssignment
    hdelta hsub homegaA U nextU hU hnextU
  have hbridge := Model.satisfies_subtype_iff_satisfiesIn
    (A : Set ZFSet.{u}) godelDefOutputFormula s
  have hval := godelDefOutputStageAssignment_val
    hdelta hsub homegaA U nextU hU hnextU
  rw [hval] at hbridge
  exact hbridge.symm.trans
    (satisfies_godelDefOutputFormula_stageCarrier_iff
      hA hdelta hsub homegaA U nextU hU hnextU)

/-- Over a constructible nonzero limit level above `omega`, the internal
Goedel-definability output formula has exactly its ambient meaning. -/
private theorem bareGodelDefOutputCorrectIn_LStageZF_of_omega_lt_gchProof02
    {theta : Ordinal.{u}}
    (htheta : Order.IsSuccLimit theta)
    (homega : Ordinal.omega0 < theta) :
    Model.BareGodelDefOutputCorrectIn
      (LStageZF theta)
      Model.stageHistoryFixedParametersRaw := by
  intro predecessorStage stage hpredecessor hstage
  exact bareGodelDefOutputIn_of_isSuccLimit_substage_iff
    (LStageZF_isTransitive theta) htheta (fun _ hx => hx)
      (ordinal_toZFSet_mem_LStageZF_of_lt homega)
      predecessorStage stage hpredecessor hstage

end
end «RudimentaryTerm»
end «Godel»
end «Constructible»
end
end GCHSource_Work_CUGCH_BareGodelDefAbsolute

universe u

theorem solution : ∀ {theta : Ordinal.{u}},
  @Order.IsSuccLimit.{u + 1} Ordinal.{u} (@PartialOrder.toPreorder.{u + 1} Ordinal.{u} Ordinal.partialOrder.{u}) theta →
    @LT.lt.{u + 1} Ordinal.{u}
        (@Preorder.toLT.{u + 1} Ordinal.{u} (@PartialOrder.toPreorder.{u + 1} Ordinal.{u} Ordinal.partialOrder.{u}))
        Ordinal.omega0.{u} theta →
      Constructible.Model.BareGodelDefOutputCorrectIn.{u} (Constructible.LStageZF.{u} theta)
        Constructible.Model.stageHistoryFixedParametersRaw.{u} :=
  @Constructible.Godel.RudimentaryTerm.bareGodelDefOutputCorrectIn_LStageZF_of_omega_lt_gchProof02.{u}
