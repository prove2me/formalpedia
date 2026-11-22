-- Prove2me | solution 1 for CircuitComplexity.wireValue_eq_wireValD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:12:10.909947+00:00
-- url     : https://prove2.me/submissions/fcec38e5-8fb5-4554-82d1-4edc555a7c6e

module
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_CircDesc
public import Definitions.Def_LeanPool_CircuitComplexity_XOR
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_Schnorr
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_Bridge
public import Theorems.Thm_CircuitComplexity_Circuit_inputWireDepth
public import Theorems.Thm_CircuitComplexity_Circuit_wireValue_ge
public import Theorems.Thm_CircuitComplexity_Circuit_wireValue_lt
public import Theorems.Thm_CircuitComplexity_andOr2_fanIn
attribute [local simp] CircuitComplexity.Circuit.inputWireDepth


section
@[expose] public section
namespace CircuitComplexity
private theorem gate_eval_eq_slot {W W' : Nat} (g : Gate Basis.andOr2 W) (hW : W ≤ W')
    (wireVal : Fin W → Bool) (wireVal' : Fin W' → Bool)
    (hwv : ∀ w : Fin W, wireVal w = wireVal' ⟨w.val, by omega⟩) :
    g.eval wireVal =
      let (isAnd, (w1, w2), (n1, n2)) := encodeGate g hW
      if isAnd then
        (n1.xor (wireVal' w1)) && (n2.xor (wireVal' w2))
      else
        (n1.xor (wireVal' w1)) || (n2.xor (wireVal' w2)) := by
  obtain ⟨op, fanIn, arityOk, inputs, negated⟩ := g
  change fanIn = 2 at arityOk
  subst arityOk
  cases op <;> simp [Gate.eval, Basis.andOr2, encodeGate, AONOp.eval,
    Fin.foldl_succ_last, Fin.foldl_zero, hwv]
end CircuitComplexity
end
end

set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
namespace CircuitComplexity
theorem _root_.solution {N G : Nat} [NeZero N]
    (c : Circuit Basis.andOr2 N 1 G)
    (input : BitString N) (w : Fin (N + G)) :
    c.wireValue input w =
      wireValD (circuitToDesc c) input ⟨w.val, by omega⟩ := by
  by_cases hwN : w.val < N
  · rw [Circuit.wireValue_lt _ _ _ hwN]
    conv_rhs => unfold wireValD
    simp [hwN]
  · push Not at hwN
    have hG : w.val - N < G := by omega
    rw [Circuit.wireValue_ge c input w (by omega)]
    have h2 : (c.gates ⟨w.val - N, hG⟩).fanIn = 2 := andOr2_fanIn _
    have hacyc0 : ((c.gates ⟨w.val - N, hG⟩).inputs ⟨0, by omega⟩).val < w.val := by
      have h := c.acyclic ⟨w.val - N, hG⟩ ⟨0, by omega⟩
      simp only [] at h; omega
    have hacyc1 : ((c.gates ⟨w.val - N, hG⟩).inputs ⟨1, by omega⟩).val < w.val := by
      have h := c.acyclic ⟨w.val - N, hG⟩ ⟨1, by omega⟩
      simp only [] at h; omega
    set gate := c.gates ⟨w.val - N, hG⟩ with gate_def
    have ih0 := solution c input
      ⟨(gate.inputs ⟨0, by omega⟩).val, by omega⟩
    have ih1 := solution c input
      ⟨(gate.inputs ⟨1, by omega⟩).val, by omega⟩
    conv_rhs => unfold wireValD
    simp only [show ¬((⟨w.val, (by omega : w.val < N + (G + 1))⟩ : Fin (N + (G + 1))).val < N)
      from by simp; omega, dite_false]
    simp only [circuitToDesc, show (⟨w.val - N, (by omega : w.val - N < G + 1)⟩ :
      Fin (G + 1)).val < G from hG, dite_true, encodeGate, Fin.val_mk]
    have hgate : ∀ h : w.val - N < G, c.gates ⟨w.val - N, h⟩ = gate :=
      fun h => (congrArg c.gates (Fin.ext rfl)).trans gate_def.symm
    simp_rw [hgate]
    simp only [hacyc0, hacyc1, ↓reduceIte]
    rw [← ih0, ← ih1]
    suffices h : ∀ (h' : ↑w - N < G) (j : Fin (c.gates ⟨↑w - N, h'⟩).fanIn),
        (c.gates ⟨↑w - N, h'⟩).negated j =
          gate.negated (j.cast (show (c.gates ⟨↑w - N, h'⟩).fanIn = gate.fanIn by
            rw [hgate h'])) by
      simp only [h, Fin.cast_mk]
      have := gate_eval_eq_slot gate (show N + G ≤ N + G by omega)
        (c.wireValue input) (c.wireValue input) (fun _ => rfl)
      rw [this]; clear this
      simp [encodeGate]
      rfl
    intro h' j
    exact (show ∀ (g : Gate Basis.andOr2 (N + G)) (heq : g = c.gates ⟨↑w - N, h'⟩)
        (hfanIn : (c.gates ⟨↑w - N, h'⟩).fanIn = g.fanIn)
        (j : Fin (c.gates ⟨↑w - N, h'⟩).fanIn),
        (c.gates ⟨↑w - N, h'⟩).negated j = g.negated (j.cast hfanIn)
      from fun g heq _ j => by subst heq; rfl)
      _ (hgate h').symm (by simp [hgate h']) j
  termination_by w.val
end CircuitComplexity
