-- Prove2me | solution 1 for CircuitComplexity.restrictCircuit_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:14:42.040145+00:00
-- url     : https://prove2.me/submissions/5266662e-ece6-43ff-b682-4eb733c4c461

module
public import Definitions.Def_LeanPool_CircuitComplexity_Nondeterminism_Defs
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_Nondeterminism
public import Theorems.Thm_CircuitComplexity_Circuit_inputWireDepth
public import Theorems.Thm_CircuitComplexity_Circuit_wireValue_ge
public import Theorems.Thm_CircuitComplexity_Circuit_wireValue_lt
public import Theorems.Thm_CircuitComplexity_andOr2_fanIn
public import Theorems.Thm_CircuitComplexity_existQuantify_const_false
public import Theorems.Thm_CircuitComplexity_existQuantify_const_true
public import Theorems.Thm_CircuitComplexity_existQuantify_eq_true
public import Theorems.Thm_CircuitComplexity_forallQuantify_const_false
public import Theorems.Thm_CircuitComplexity_forallQuantify_const_true
public import Theorems.Thm_CircuitComplexity_forallQuantify_eq_true
attribute [local simp] CircuitComplexity.Circuit.inputWireDepth
attribute [local simp] CircuitComplexity.existQuantify_const_false
attribute [local simp] CircuitComplexity.existQuantify_const_true
attribute [local simp] CircuitComplexity.existQuantify_eq_true
attribute [local simp] CircuitComplexity.forallQuantify_const_false
attribute [local simp] CircuitComplexity.forallQuantify_const_true
attribute [local simp] CircuitComplexity.forallQuantify_eq_true


section
@[expose] public section
namespace CircuitComplexity
variable {k m : Nat}
private theorem andOr2_eval_two {W : Nat} (g : Gate Basis.andOr2 W)
    (wv : BitString W) :
    g.eval wv =
    let a0 := g.negated ⟨0,
      by rw [andOr2_fanIn]; omega⟩ ^^ wv (g.inputs ⟨0, by rw [andOr2_fanIn]; omega⟩)
    let a1 := g.negated ⟨1,
      by rw [andOr2_fanIn]; omega⟩ ^^ wv (g.inputs ⟨1, by rw [andOr2_fanIn]; omega⟩)
    match g.op with
    | .and => a0 && a1
    | .or  => a0 || a1 := by
  have hf := andOr2_fanIn g
  simp only [Gate.eval, Basis.andOr2]
  cases g.op <;> simp_all [AONOp.eval, Fin.foldl_succ_last, Fin.foldl_zero] <;>
    congr 1
private theorem mkConstGateP_eval {G : Nat} [NeZero m] (val : Bool) (bound : Nat)
    (wv : BitString (k + m + G)) :
    (mkConstGateP (k := k) (m := m) (G := G) val bound).val.eval wv = val := by
  unfold mkConstGateP
  split
  · rename_i hval; rw [andOr2_eval_two]; simp_all
  · rename_i hval; rw [andOr2_eval_two]; simp_all
private theorem mkIdentGateP_eval {G : Nat} (op : AONOp) (w : Fin (k + m + G)) (neg : Bool)
    (bound : Nat) (hw : w.val < k + m + bound)
    (wv : BitString (k + m + G)) :
    (mkIdentGateP (k := k) (m := m) (G := G) op w neg bound hw).val.eval wv = (neg ^^ wv w) := by
  unfold mkIdentGateP
  rw [andOr2_eval_two]; simp only
  cases op <;> cases (neg ^^ wv w) <;> simp
private theorem restrictGateP_eval_eq {G : Nat} [NeZero m]
    (b : Bool) (g : Gate Basis.andOr2 ((k + 1) + m + G))
    (hfanIn : g.fanIn = 2)
    (bound : Nat) (hboundG : bound ≤ G)
    (hbound : ∀ j : Fin g.fanIn, (g.inputs j).val < (k + 1) + m + bound)
    (wvOld : BitString ((k + 1) + m + G))
    (wvNew : BitString (k + m + G))
    (hwv0 : wvOld ⟨0, by omega⟩ = b)
    (hwv : ∀ (i : Nat), (hi : i < (k + 1) + m + bound) → (hip : 0 < i) →
      wvOld ⟨i, by omega⟩ = wvNew ⟨i - 1, by omega⟩) :
    g.eval wvOld =
    (restrictGateP (k := k) (m := m) b g hfanIn bound hbound).val.eval wvNew := by
  set w0 := g.inputs ⟨0, by omega⟩ with hw0_def
  set w1 := g.inputs ⟨1, by omega⟩ with hw1_def
  set n0 := g.negated ⟨0, by omega⟩ with hn0_def
  set n1 := g.negated ⟨1, by omega⟩ with hn1_def
  have hwv0' : ∀ (w : Fin ((k+1)+m+G)), w.val = 0 → wvOld w = b := by
    intro w hw; rw [show w = ⟨0, by omega⟩ from Fin.ext hw]; exact hwv0
  have hwvS : ∀ (w : Fin ((k+1)+m+G)), w.val ≠ 0 → w.val < (k+1)+m+bound →
      wvOld w = wvNew ⟨w.val - 1, by have := w.isLt; have := NeZero.ne m; omega⟩ := by
    intro w hw hlt; exact hwv w.val hlt (by omega)
  rw [andOr2_eval_two g wvOld]
  unfold restrictGateP
  simp only [← hw0_def, ← hw1_def, ← hn0_def, ← hn1_def]
  by_cases hw0 : w0.val = 0 <;> by_cases hw1 : w1.val = 0 <;>
    simp only [hw0, hw1, dite_true, dite_false]
  · rw [hwv0' w0 hw0, hwv0' w1 hw1, mkConstGateP_eval]
    cases b <;> cases n0 <;> cases n1 <;> cases g.op <;> rfl
  · rw [hwv0' w0 hw0, hwvS w1 hw1 (hbound ⟨1, by omega⟩)]
    cases b <;> cases n0 <;> cases n1 <;> cases g.op <;>
      simp (config := { decide := true }) [mkIdentGateP_eval, mkConstGateP_eval]
  · rw [hwvS w0 hw0 (hbound ⟨0, by omega⟩), hwv0' w1 hw1]
    cases b <;> cases n0 <;> cases n1 <;> cases g.op <;>
      simp (config := { decide := true }) [mkIdentGateP_eval, mkConstGateP_eval]
  · rw [hwvS w0 hw0 (hbound ⟨0, by omega⟩), hwvS w1 hw1 (hbound ⟨1, by omega⟩)]
    rw [andOr2_eval_two]
    cases g.op <;> simp (config := { decide := true })
private theorem wireValue_zero {G : Nat} [NeZero m] (b : Bool)
    (c : Circuit Basis.andOr2 ((k + 1) + m) 1 G)
    (x : BitString (k + m)) :
    c.wireValue (prependInput b x) ⟨0, by omega⟩ = b := by
  rw [Circuit.wireValue_lt _ _ _ (by change 0 < (k + 1) + m; omega)]
  simp [prependInput]
private theorem wireValue_restrict {G : Nat} [NeZero m] (b : Bool)
    (c : Circuit Basis.andOr2 ((k + 1) + m) 1 G)
    (x : BitString (k + m))
    (w : Nat) (hwlt : w < (k + 1) + m + G)
    (hw : 0 < w) :
    c.wireValue (prependInput b x) ⟨w, hwlt⟩ =
      (restrictCircuit (k := k) b c).wireValue x ⟨w - 1, by omega⟩ := by
  induction w using Nat.strongRecOn with
  | _ w ih =>
    by_cases hwN : w < (k + 1) + m
    · rw [Circuit.wireValue_lt _ _ _ (show (⟨w, hwlt⟩ : Fin _).val < (k + 1) + m by simp; omega)]
      rw [Circuit.wireValue_lt _ _ _
        (show (⟨w - 1, (by omega)⟩ : Fin _).val < k + m by simp; omega)]
      simp only [prependInput, show ¬ (w = 0) from by omega, dite_false]
    · push Not at hwN
      rw [Circuit.wireValue_ge _ _ _ (show ¬ (⟨w, hwlt⟩ : Fin _).val < (k + 1) + m by simp; omega)]
      rw [Circuit.wireValue_ge _ _ _
        (show ¬ (⟨w - 1, (by omega)⟩ : Fin _).val < k + m by simp; omega)]
      simp only [restrictCircuit]
      have hidx : w - 1 - (k + m) = w - (k + 1 + m) := by omega
      have hg_eq : (⟨w - 1 - (k + m), by omega⟩ : Fin G) = ⟨w - (k + 1 + m), by omega⟩ := by
        ext; exact hidx
      simp only [hg_eq]
      apply restrictGateP_eval_eq b (c.gates ⟨w-(k+1+m), by omega⟩) (andOr2_fanIn _)
        (w-1-(k+m)) (by omega)
        (fun j => by have := c.acyclic ⟨w-(k+1+m), by omega⟩ j; simp at this; omega)
        (c.wireValue (prependInput b x)) _ (wireValue_zero b c x)
      intro i hi hip
      exact ih i (by omega) (by omega) hip
end CircuitComplexity
end
end

set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
variable {k m : Nat}
namespace CircuitComplexity
theorem _root_.solution {G : Nat} [NeZero m] (b : Bool)
    (c : Circuit Basis.andOr2 ((k + 1) + m) 1 G)
    (f : BitString ((k + 1) + m) → Bool)
    (heval : (fun x => (c.eval x) 0) = f) :
    (fun x => ((restrictCircuit (k := k) b c).eval x) 0) = restrictFirst f b := by
  funext x
  have hrhs : restrictFirst f b x = f (prependInput b x) := rfl
  rw [hrhs, ← heval]
  simp only [Circuit.eval, restrictCircuit]
  symm
  apply restrictGateP_eval_eq b (c.outputs 0) (andOr2_fanIn _) G (le_refl G)
    (fun j => by have := ((c.outputs 0).inputs j).isLt; omega)
    (c.wireValue (prependInput b x)) ((restrictCircuit b c).wireValue x)
    (wireValue_zero b c x)
  intro i hi hip
  convert wireValue_restrict b c x i (by omega) hip using 2
end CircuitComplexity
