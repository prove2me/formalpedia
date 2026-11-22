-- Prove2me | solution 1 for CircuitComplexity.Schnorr.evalD_restrictD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:12:08.526586+00:00
-- url     : https://prove2.me/submissions/c8748277-0335-43f9-bae5-242664c82330

module
public import Definitions.Def_LeanPool_CircuitComplexity_XOR
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_CircDesc
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_Schnorr
public import Theorems.Thm_CircuitComplexity_Circuit_inputWireDepth
attribute [local simp] CircuitComplexity.Circuit.inputWireDepth


section
@[expose] public section
namespace CircuitComplexity
namespace Schnorr
private theorem remapWireR_effective {N s : Nat} (d : CircDesc (N + 1) s)
    (a : Fin (N + 1)) (b : Bool) (x : BitString N)
    (w : Fin (N + s)) (hw : ¬w.val < N)
    (wi : Fin (N + 1 + s)) (ni : Bool)
    (ih : ∀ w' : Fin (N + s), w'.val < w.val →
      wireValD (restrictD d a b) x w' =
      wireValD d (insertAt x a b)
        (if w'.val < a.val then ⟨w'.val, by omega⟩ else ⟨w'.val + 1, by omega⟩)) :
    let p := remapWireR a b ⟨w.val - N, by omega⟩ wi ni
    p.2.xor (if p.1.val < w.val then
        wireValD (restrictD d a b) x ⟨p.1.val, p.1.isLt⟩ else false) =
    ni.xor (if wi.val < w.val + 1 then
        wireValD d (insertAt x a b) ⟨wi.val, wi.isLt⟩ else false) := by
  simp only [remapWireR]
  split
  · -- wi.val = a.val: self-reference, effective input = ni.xor b
    rename_i heq
    have : ¬(N + (w.val - N) < w.val) := by omega
    simp only [this, ite_false, Bool.xor_false]
    have : wi.val < w.val + 1 := by have := a.isLt; omega
    simp only [this, ite_true]
    rw [wireValD]; simp only [show wi.val < N + 1 from by have := a.isLt; omega, dite_true]
    congr 1
    simp only [insertAt, heq]
    simp_all
  · split
    · -- wi.val < a.val: same index, shifted
      rename_i hne hlt
      have hwi : wi.val < w.val := by omega
      have hwi' : wi.val < w.val + 1 := by omega
      simp only [hwi, ite_true, hwi', ite_true]
      rw [ih ⟨wi.val, by omega⟩ hwi]
      simp_all
    · -- wi.val > a.val: index - 1
      rename_i hne hge
      by_cases hwi : wi.val - 1 < w.val
      · have : wi.val < w.val + 1 := by omega
        simp only [hwi, ite_true, this, ite_true]
        rw [ih ⟨wi.val - 1, by have := wi.isLt; omega⟩ hwi]
        congr 1
        have : ¬(wi.val - 1 < a.val) := by omega
        simp only [this, ite_false]
        congr 1; ext; simp; omega
      · have : ¬(wi.val < w.val + 1) := by omega
        simp only [hwi, ite_false, this, ite_false]
private theorem wireValD_restrictD {N s : Nat} (d : CircDesc (N + 1) s)
    (a : Fin (N + 1)) (b : Bool) (x : BitString N) (w : Fin (N + s)) :
    wireValD (restrictD d a b) x w =
    wireValD d (insertAt x a b)
      (if w.val < a.val then ⟨w.val, by omega⟩ else ⟨w.val + 1, by omega⟩) := by
  by_cases hw : w.val < N
  · -- Primary input: LHS = x w, RHS = insertAt x a b (lifted w)
    conv_lhs => rw [wireValD]; simp only [hw, dite_true]
    split <;> rename_i hlt
    · -- w < a: lifted wire is w, also a primary input
      rw [wireValD]; simp only [show w.val < N + 1 from by omega, dite_true]
      simp only [insertAt, hlt, dite_true]
    · -- w ≥ a: lifted wire is w+1, also a primary input (w+1 ≤ N < N+1)
      conv_rhs => rw [wireValD]; simp only [show w.val + 1 < N + 1 from by omega, dite_true]
      simp only [insertAt]
      have : ¬(w.val + 1 < a.val) := by omega
      have : ¬(w.val + 1 = a.val) := by omega
      simp only [*, dite_false]; congr 1
  · -- Gate wire: w.val ≥ N ≥ a.val, so lifted wire is w+1
    have ha := a.isLt
    have : ¬(w.val < a.val) := by omega
    simp only [this, ite_false]
    -- Unfold both wireValD calls one step
    conv_lhs => rw [wireValD]; simp only [hw, dite_false]
    conv_rhs => rw [wireValD]; simp only [show ¬(w.val + 1 < N + 1) from by omega, dite_false]
    have hgi : w.val + 1 - (N + 1) = w.val - N := by omega
    simp only [restrictD, hgi]
    -- Both sides branch on isAnd; congr reduces to per-wire-input goals
    split <;> rename_i hd <;>
      simp only [hd, Bool.false_eq_true, ite_false, ite_true] <;> congr 1 <;>
      exact remapWireR_effective d a b x w hw _ _
        (fun w' hw' => wireValD_restrictD d a b x w')
termination_by w.val
end Schnorr
end CircuitComplexity
end
end

set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
open CircuitComplexity.Schnorr
namespace CircuitComplexity.Schnorr
theorem _root_.solution {N s : Nat} (d : CircDesc (N + 1) s)
    (hs : 0 < s) (a : Fin (N + 1)) (b : Bool) (x : BitString N) :
    evalD hs (restrictD d a b) x = evalD hs d (insertAt x a b) := by
  simp only [evalD]
  rw [wireValD_restrictD]
  have ha := a.isLt
  have : ¬(N + s - 1 < a.val) := by omega
  simp only [this, ite_false]
  congr 1; ext; simp; omega
end CircuitComplexity.Schnorr
