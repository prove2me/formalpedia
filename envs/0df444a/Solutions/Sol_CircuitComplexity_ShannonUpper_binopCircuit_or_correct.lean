-- Prove2me | solution 1 for CircuitComplexity.ShannonUpper.binopCircuit_or_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:12:13.597923+00:00
-- url     : https://prove2.me/submissions/4244b126-670e-4d6b-a473-1851722abe3c

module
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
public import Mathlib.Data.Nat.Log
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_ShannonUpper
public import Theorems.Thm_CircuitComplexity_Circuit_inputWireDepth
public import Theorems.Thm_CircuitComplexity_Circuit_wireValue_ge
public import Theorems.Thm_CircuitComplexity_Circuit_wireValue_lt
public import Theorems.Thm_CircuitComplexity_andOr2_fanIn
attribute [local simp] CircuitComplexity.Circuit.inputWireDepth


section
@[expose] public section
namespace CircuitComplexity
namespace ShannonUpper
private theorem mkGate2'_eval (o : AONOp) {W : Nat} (w₀ w₁ : Fin W) (n₀ n₁ : Bool)
    (b : Nat) (h₀ : w₀.val < b) (h₁ : w₁.val < b)
    (wv : BitString W) :
    (mkGate2' o w₀ w₁ n₀ n₁ b h₀ h₁).val.eval wv =
    match o with
    | .and => (n₀ ^^ wv w₀) && (n₁ ^^ wv w₁)
    | .or => (n₀ ^^ wv w₀) || (n₁ ^^ wv w₁) := by
  simp only [mkGate2', Gate.eval, Basis.andOr2]
  cases o <;> simp [AONOp.eval, Fin.foldl_succ_last, Fin.foldl_zero]
private theorem andOr2_gate_eval_two_inputs {W : Nat}
    (g : Gate Basis.andOr2 W) (wv : BitString W) :
    g.eval wv =
    match g.op with
    | .and => (gn 0 g ^^ wv (gw 0 g)) && (gn 1 g ^^ wv (gw 1 g))
    | .or => (gn 0 g ^^ wv (gw 0 g)) || (gn 1 g ^^ wv (gw 1 g)) := by
  have hf := andOr2_fanIn g
  simp only [Gate.eval, Basis.andOr2, gw, gn]
  cases g.op <;> simp_all [AONOp.eval, Fin.foldl_succ_last, Fin.foldl_zero, Fin.cast]
private theorem binop_wireValue_c₁ {N G₁ G₂ : Nat} [NeZero N]
    (op : AONOp)
    (c₁ : Circuit Basis.andOr2 N 1 G₁) (c₂ : Circuit Basis.andOr2 N 1 G₂)
    (x : BitString N) (w : Fin (N + G₁))
    (hw : w.val < N + G₁) :
    (binopCircuit op c₁ c₂).wireValue x ⟨w.val, by omega⟩ = c₁.wireValue x w := by
  have key : ∀ n : Nat, ∀ (hn₁ : n < N + (G₁ + G₂ + 2)) (hn₂ : n < N + G₁),
      (binopCircuit op c₁ c₂).wireValue x ⟨n, hn₁⟩ = c₁.wireValue x ⟨n, hn₂⟩ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn₁ hn₂
      by_cases hlt : n < N
      · rw [Circuit.wireValue_lt _ _ ⟨n, hn₁⟩ (show (⟨n, hn₁⟩ : Fin _).val < N from hlt),
             Circuit.wireValue_lt _ _ ⟨n, hn₂⟩ (show (⟨n, hn₂⟩ : Fin _).val < N from hlt)]
      · rw [Circuit.wireValue_ge _ _ _ hlt, Circuit.wireValue_ge _ _ _ hlt]
        have hg : n - N < G₁ := by omega
        -- binopGWP takes first branch since n - N < G₁
        -- Change goal to use binopGWP
        change (binopGWP c₁ c₂ ⟨n - N, _⟩).val.eval _ = _
        -- Unfold binopGWP for the first branch
        simp only [binopGWP, dif_pos hg]
        rw [mkGate2'_eval (c₁.gates ⟨n - N, hg⟩).op, andOr2_gate_eval_two_inputs]
        have hacyc0 : (gw 0 (c₁.gates ⟨n - N, hg⟩)).val < n := by
          have := c₁.acyclic ⟨_, hg⟩ ⟨0, by rw [andOr2_fanIn]; omega⟩; simp [gw] at this ⊢; omega
        have hacyc1 : (gw 1 (c₁.gates ⟨n - N, hg⟩)).val < n := by
          have := c₁.acyclic ⟨_, hg⟩ ⟨1, by rw [andOr2_fanIn]; omega⟩; simp [gw] at this ⊢; omega
        cases (c₁.gates ⟨n - N, hg⟩).op <;> simp only <;> congr 1 <;> congr 1
        · exact ih _ hacyc0 (by omega) (by omega)
        · exact ih _ hacyc1 (by omega) (by omega)
        · exact ih _ hacyc0 (by omega) (by omega)
        · exact ih _ hacyc1 (by omega) (by omega)
  simp_all
private theorem binop_wireValue_c₂ {N G₁ G₂ : Nat} [NeZero N]
    (op : AONOp)
    (c₁ : Circuit Basis.andOr2 N 1 G₁) (c₂ : Circuit Basis.andOr2 N 1 G₂)
    (x : BitString N) (w : Fin (N + G₂)) :
    (binopCircuit op c₁ c₂).wireValue x (remap₂ N G₁ G₂ w) = c₂.wireValue x w := by
  have key : ∀ n : Nat, ∀ (hn : n < N + G₂),
      (binopCircuit op c₁ c₂).wireValue x (remap₂ N G₁ G₂ ⟨n, hn⟩) =
        c₂.wireValue x ⟨n, hn⟩ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      by_cases hlt : n < N
      · -- Input wire: remap₂ preserves it
        simp only [remap₂, dif_pos hlt]
        rw [Circuit.wireValue_lt _ _ _ hlt, Circuit.wireValue_lt _ _ _ hlt]
      · -- Gate wire: remap₂ shifts by G₁ + 1
        simp only [remap₂, dif_neg hlt]
        have hge : ¬(n + G₁ + 1 < N) := by omega
        rw [Circuit.wireValue_ge _ _ _ hge, Circuit.wireValue_ge _ _ _ hlt]
        have hg₂ : n - N < G₂ := by omega
        have hidx : n + G₁ + 1 - N = n - N + G₁ + 1 := by omega
        -- Change to binopGWP form
        change (binopGWP c₁ c₂ ⟨n + G₁ + 1 - N, _⟩).val.eval _ = _
        -- Unfold binopGWP for the third branch
        have hb1 : ¬(n + G₁ + 1 - N < G₁) := by omega
        have hb2 : ¬(n + G₁ + 1 - N = G₁) := by omega
        have hb3 : n + G₁ + 1 - N < G₁ + 1 + G₂ := by omega
        simp only [binopGWP, dif_neg hb1, dif_neg hb2, dif_pos hb3]
        rw [mkGate2'_eval (c₂.gates ⟨n + G₁ + 1 - N - G₁ - 1, by omega⟩).op,
          andOr2_gate_eval_two_inputs]
        -- Simplify gate index
        have : (⟨n + G₁ + 1 - N - G₁ - 1, by omega⟩ : Fin G₂) = ⟨n - N, hg₂⟩ := by
          ext; simp; omega
        simp only [this]
        have hacyc0 : (gw 0 (c₂.gates ⟨n - N, hg₂⟩)).val < n := by
          have := c₂.acyclic ⟨_, hg₂⟩ ⟨0, by rw [andOr2_fanIn]; omega⟩; simp [gw] at this ⊢; omega
        have hacyc1 : (gw 1 (c₂.gates ⟨n - N, hg₂⟩)).val < n := by
          have := c₂.acyclic ⟨_, hg₂⟩ ⟨1, by rw [andOr2_fanIn]; omega⟩; simp [gw] at this ⊢; omega
        cases (c₂.gates ⟨n - N, hg₂⟩).op <;> simp only <;> congr 1 <;> congr 1
        · exact ih _ hacyc0 (by omega)
        · exact ih _ hacyc1 (by omega)
        · exact ih _ hacyc0 (by omega)
        · exact ih _ hacyc1 (by omega)
  exact key w.val w.isLt
end ShannonUpper
end CircuitComplexity
end
end

set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
open CircuitComplexity.ShannonUpper
namespace CircuitComplexity.ShannonUpper
theorem _root_.solution {N G₁ G₂ : Nat} [NeZero N]
    (c₁ : Circuit Basis.andOr2 N 1 G₁) (c₂ : Circuit Basis.andOr2 N 1 G₂)
    (f₁ f₂ : BitString N → Bool)
    (hf₁ : (fun x => (c₁.eval x) 0) = f₁)
    (hf₂ : (fun x => (c₂.eval x) 0) = f₂) :
    (fun x => ((binopCircuit AONOp.or c₁ c₂).eval x) 0) =
    fun x => f₁ x || f₂ x := by
  funext x
  simp only [← hf₁, ← hf₂, Circuit.eval]
  set cb := binopCircuit AONOp.or c₁ c₂
  -- Wire N + G₁ corresponds to c₁'s output gate (gate G₁ in combined circuit)
  have hw1 : cb.wireValue x ⟨N + G₁, by omega⟩ =
      (c₁.outputs 0).eval (c₁.wireValue x) := by
    rw [Circuit.wireValue_ge _ _ _ (show ¬(N + G₁ < N) by omega)]
    change (binopGWP c₁ c₂ ⟨_, _⟩).val.eval _ = _
    have hfin : (⟨N + G₁ - N, (by omega : N + G₁ - N < G₁ + G₂ + 2)⟩ : Fin (G₁ + G₂ + 2)) =
        ⟨G₁, by omega⟩ := Fin.ext (show N + G₁ - N = G₁ by omega)
    rw [hfin]
    simp only [binopGWP, show ¬(G₁ < G₁) from Nat.lt_irrefl G₁, dite_false, dite_true]
    rw [mkGate2'_eval (c₁.outputs 0).op, andOr2_gate_eval_two_inputs]
    cases (c₁.outputs 0).op <;> simp only <;> congr 1 <;> congr 1
    all_goals (apply binop_wireValue_c₁; exact (gw _ (c₁.outputs 0)).isLt)
  -- Wire N + G₁ + G₂ + 1 corresponds to c₂'s output gate
  have hw2 : cb.wireValue x ⟨N + G₁ + G₂ + 1, by omega⟩ =
      (c₂.outputs 0).eval (c₂.wireValue x) := by
    rw [Circuit.wireValue_ge _ _ _ (show ¬(N + G₁ + G₂ + 1 < N) by omega)]
    change (binopGWP c₁ c₂ ⟨_, _⟩).val.eval _ = _
    have hfin :
      (⟨N + G₁ + G₂ + 1 - N, (by omega : N + G₁ + G₂ + 1 - N < G₁ + G₂ + 2)⟩ : Fin (G₁ + G₂ + 2)) =
        ⟨G₁ + G₂ + 1, by omega⟩ := Fin.ext (show N + G₁ + G₂ + 1 - N = G₁ + G₂ + 1 by omega)
    rw [hfin]
    simp only [binopGWP,
      show ¬(G₁ + G₂ + 1 < G₁) by omega,
      show ¬(G₁ + G₂ + 1 = G₁) by omega,
      show ¬(G₁ + G₂ + 1 < G₁ + 1 + G₂) by omega,
      dite_false]
    rw [mkGate2'_eval (c₂.outputs 0).op, andOr2_gate_eval_two_inputs]
    cases (c₂.outputs 0).op <;> simp only <;> congr 1 <;> congr 1
    all_goals (apply binop_wireValue_c₂)
  -- The output gate of cb applies OR to these two wires
  change (cb.outputs 0).eval (cb.wireValue x) = _
  rw [andOr2_gate_eval_two_inputs (g := cb.outputs 0)]
  -- The output gate has op = .or, negated = false, inputs 0 = N+G₁, inputs 1 = N+G₁+G₂+1
  have hcb_op : (cb.outputs 0).op = AONOp.or := rfl
  have hcb_gn0 : gn 0 (cb.outputs 0) = false := rfl
  have hcb_gn1 : gn 1 (cb.outputs 0) = false := rfl
  have hcb_gw0 : gw 0 (cb.outputs 0) = ⟨N + G₁, by omega⟩ := by
    simp [gw, cb, binopCircuit]
  have hcb_gw1 : gw 1 (cb.outputs 0) = ⟨N + G₁ + G₂ + 1, by omega⟩ := by
    simp [gw, cb, binopCircuit]
  simp_all
end CircuitComplexity.ShannonUpper
