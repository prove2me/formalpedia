-- Prove2me | solution 1 for CircuitComplexity.Schnorr.evalD_elimGateD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:12:09.62256+00:00
-- url     : https://prove2.me/submissions/3312795e-2081-41dc-9794-8a54224fa13b

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
private theorem liftWireE_val_lt {N s : Nat} {g : Fin (s + 1)} {w : Fin (N + s)}
    (h : w.val < N + g.val) : (liftWireE g w).val = w.val := by
  simp [liftWireE, h]
private theorem liftWireE_val_ge {N s : Nat} {g : Fin (s + 1)} {w : Fin (N + s)}
    (h : ¬(w.val < N + g.val)) : (liftWireE g w).val = w.val + 1 := by
  simp [liftWireE, h]
private theorem remapWireE_effective {N s : Nat} (d : CircDesc N (s + 1))
    (g : Fin (s + 1)) (rd : GateRedirect (N + s))
    (hrd : ∀ x : BitString N,
      wireValD d x ⟨N + g.val, by omega⟩ = match rd with
        | .const c => c
        | .wire w' flip => flip.xor (wireValD d x ⟨w'.val, by omega⟩))
    (hrd_wire : ∀ w' flip, rd = .wire w' flip → w'.val < N + g.val)
    (x : BitString N) (w : Fin (N + s)) (hw : ¬w.val < N)
    (wi : Fin (N + (s + 1))) (ni : Bool)
    (ih : ∀ w' : Fin (N + s), w'.val < w.val →
      wireValD (elimGateD d g rd) x w' = wireValD d x (liftWireE g w')) :
    let p := remapWireE g rd ⟨w.val - N, by omega⟩ wi ni
    p.2.xor (if p.1.val < w.val then
        wireValD (elimGateD d g rd) x ⟨p.1.val, p.1.isLt⟩ else false) =
    ni.xor (if wi.val < (liftWireE g w).val then
        wireValD d x ⟨wi.val, wi.isLt⟩ else false) := by
  -- Get liftWireE value info
  have hlift_val : (liftWireE g w).val =
      if w.val < N + g.val then w.val else w.val + 1 := by
    simp [liftWireE]; split <;> simp
  simp only [remapWireE]
  -- Case 1: wi < N (primary input)
  split
  · rename_i hwi
    have hwi_w : wi.val < w.val := by omega
    have hwi_lift : wi.val < (liftWireE g w).val := by rw [hlift_val]; split <;> omega
    simp only [hwi_w, ite_true, hwi_lift, ite_true]
    congr 1; rw [ih ⟨wi.val, by omega⟩ hwi_w]; congr 1
    show liftWireE g ⟨wi.val, _⟩ = ⟨wi.val, _⟩
    simp [liftWireE, show wi.val < N + g.val from by omega]
  · split
    · -- Case 2: wi = N + g.val
      rename_i hne hwi_eq
      split
      · -- Case 2a: i < g (forward reference, was false)
        rename_i hi_lt
        have hw_lt_g : w.val < N + g.val := by omega
        simp only [show ¬(N + (w.val - N) < w.val) from by omega, ite_false, Bool.xor_false]
        simp only
          [show ¬(wi.val < (liftWireE g w).val) from by rw [hlift_val]; simp [hw_lt_g]; omega,
          ite_false, Bool.xor_false]
      · -- Case 2b: i ≥ g (back reference)
        rename_i hi_ge
        have hw_ge : ¬(w.val < N + g.val) := by omega
        cases rd with
        | const c =>
          simp only [show ¬(N + (w.val - N) < w.val) from by omega, ite_false, Bool.xor_false]
          simp only
            [show wi.val < (liftWireE g w).val from by rw [hlift_val]; simp [hw_ge]; omega,
            ite_true]
          simp_all
        | wire w' flip =>
          have hwr := hrd_wire w' flip rfl
          have hw'_lt : w'.val < w.val := by omega
          simp only [hw'_lt, ite_true,
            show wi.val < (liftWireE g w).val from by rw [hlift_val]; simp [hw_ge]; omega, ite_true]
          rw [ih ⟨w'.val, w'.isLt⟩ hw'_lt]
          have hrd_spec := hrd x; simp only at hrd_spec
          have hfin : (⟨wi.val, wi.isLt⟩ : Fin (N + (s + 1))) = ⟨N + g.val, by omega⟩ :=
            Fin.ext hwi_eq
          rw [hfin, hrd_spec]
          have hlift' : liftWireE g (⟨w'.val, w'.isLt⟩ : Fin (N + s)) = ⟨w'.val, by omega⟩ := by
            simp [liftWireE, show w'.val < N + g.val from hwr]
          rw [hlift', Bool.xor_assoc]
    · split
      · -- Case 3: N ≤ wi < N + g.val, wi ≠ N + g.val
        rename_i hne hwi_ne hwi_lt
        by_cases hwi_w : wi.val < w.val
        · -- Back reference
          have hwi_lift : wi.val < (liftWireE g w).val := by rw [hlift_val]; split <;> omega
          simp only [hwi_w, ite_true, hwi_lift, ite_true]
          congr 1; rw [ih ⟨wi.val, by omega⟩ hwi_w]; congr 1
          show liftWireE g ⟨wi.val, _⟩ = ⟨wi.val, _⟩
          simp [liftWireE, hwi_lt]
        · -- Forward reference: both sides give false
          have : w.val < N + g.val := by omega
          have hwi_lift : ¬(wi.val < (liftWireE g w).val) := by rw [hlift_val]; simp [this]; omega
          simp only [hwi_w, ite_false, hwi_lift, ite_false]
      · -- Case 4: wi > N + g.val
        rename_i hne hwi_ne hwi_ge
        by_cases hwi_lt : wi.val - 1 < w.val
        · -- Back reference (shifted)
          -- wi > N + g.val and wi - 1 < w.val, so wi ≤ w.val, so wi.val ≤ w.val
          -- liftWireE: w.val ≥ N + g.val (since wi.val > N + g.val and wi.val - 1 < w.val → w.val
          -- ≥ N + g.val)
          have hw_ge : ¬(w.val < N + g.val) := by omega
          have hwi_lift : wi.val < (liftWireE g w).val := by rw [hlift_val]; simp [hw_ge]; omega
          simp only [hwi_lt, ite_true, hwi_lift, ite_true]
          congr 1; rw [ih ⟨wi.val - 1, by omega⟩ hwi_lt]; congr 1
          show liftWireE g ⟨wi.val - 1, _⟩ = ⟨wi.val, _⟩
          simp only [liftWireE, show ¬(wi.val - 1 < N + g.val) from by omega, ite_false]
          ext; simp; omega
        · have hwi_lift : ¬(wi.val < (liftWireE g w).val) := by rw [hlift_val]; split <;> omega
          simp only [hwi_lt, ite_false, hwi_lift, ite_false]
private theorem wireValD_elimGateD {N s : Nat} (d : CircDesc N (s + 1))
    (g : Fin (s + 1)) (rd : GateRedirect (N + s))
    (hrd : ∀ x : BitString N,
      wireValD d x ⟨N + g.val, by omega⟩ = match rd with
        | .const c => c
        | .wire w flip => flip.xor (wireValD d x ⟨w.val, by omega⟩))
    (hrd_wire : ∀ w' flip, rd = .wire w' flip → w'.val < N + g.val)
    (x : BitString N) (w : Fin (N + s)) :
    wireValD (elimGateD d g rd) x w = wireValD d x (liftWireE g w) := by
  by_cases hw : w.val < N
  · -- Primary input case
    conv_lhs => rw [wireValD]; simp only [hw, dite_true]
    simp only [liftWireE]
    have : w.val < N + g.val := by omega
    simp only [this, ite_true]
    rw [wireValD]; simp only [show w.val < N from hw, dite_true]
  · -- Gate case: w is a gate wire
    have hi : w.val - N < s := by omega
    -- Unfold wireValD on both sides
    conv_lhs => rw [wireValD]; simp only [hw, dite_false]
    have hlift_val : (liftWireE g w).val =
        if w.val < N + g.val then w.val else w.val + 1 := by
      unfold liftWireE; split <;> simp only []
    have hw_lift : ¬(liftWireE g w).val < N := by
      simp only [hlift_val]; split <;> omega
    conv_rhs => rw [wireValD]; simp only [hw_lift, dite_false]
    -- Case split on gate index relative to eliminated gate
    by_cases hig : w.val - N < g.val
    · -- w.val - N < g.val: liftWireE g w has val = w.val
      have hw_lt : w.val < N + g.val := by omega
      have hgi : (liftWireE g w).val - N = w.val - N := by
        rw [liftWireE_val_lt hw_lt]
      simp only [elimGateD, hig, dite_true, hgi]
      split <;> (congr 1 <;> [skip; skip]) <;>
        exact remapWireE_effective d g rd hrd hrd_wire x w hw _ _
          (fun w' hw' => wireValD_elimGateD d g rd hrd hrd_wire x w')
    · -- w.val - N ≥ g.val: liftWireE g w has val = w.val + 1
      have hw_ge : ¬(w.val < N + g.val) := by omega
      have hgi : (liftWireE g w).val - N = w.val - N + 1 := by
        rw [liftWireE_val_ge hw_ge]; omega
      simp only [elimGateD, hig, dite_false, hgi]
      split <;> (congr 1 <;> [skip; skip]) <;>
        exact remapWireE_effective d g rd hrd hrd_wire x w hw _ _
          (fun w' hw' => wireValD_elimGateD d g rd hrd hrd_wire x w')
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
theorem _root_.solution {N s : Nat} (d : CircDesc N (s + 1))
    (hs : 0 < s) (g : Fin (s + 1)) (rd : GateRedirect (N + s))
    (hrd : ∀ x : BitString N,
      wireValD d x ⟨N + g.val, by omega⟩ = match rd with
        | .const c => c
        | .wire w flip => flip.xor (wireValD d x ⟨w.val, by omega⟩))
    (hrd_wire : ∀ w' flip, rd = .wire w' flip → w'.val < N + g.val)
    (hg_not_last : g.val < s) :
    ∀ x, evalD hs (elimGateD d g rd) x = evalD (by omega : 0 < s + 1) d x := by
  intro x; simp only [evalD]
  rw [wireValD_elimGateD d g rd hrd hrd_wire x]
  congr 1; simp only [liftWireE]
  have : ¬(N + s - 1 < N + g.val) := by omega
  simp only [this, ite_false]; ext; simp; omega
end CircuitComplexity.Schnorr
