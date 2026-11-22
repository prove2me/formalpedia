-- Prove2me | solution 1 for CircuitComplexity.Schnorr.restriction_eliminates_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:13:42.128798+00:00
-- url     : https://prove2.me/submissions/472c11c0-3c50-4309-b3d2-68fbdb27c918

module
public import Definitions.Def_LeanPool_CircuitComplexity_XOR
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_CircDesc
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_Schnorr
public import Theorems.Thm_CircuitComplexity_Schnorr_xorBool_insertAt
public import Theorems.Thm_CircuitComplexity_Schnorr_evalD_essential_means_referenced
public import Theorems.Thm_CircuitComplexity_Schnorr_evalD_restrictD
public import Theorems.Thm_CircuitComplexity_Schnorr_evalD_elimGateD
public import Theorems.Thm_CircuitComplexity_Circuit_inputWireDepth
public import Theorems.Thm_CircuitComplexity_Schnorr_xorBool_flip
attribute [local simp] CircuitComplexity.Circuit.inputWireDepth


section
@[expose] public section
namespace CircuitComplexity
namespace Schnorr
private theorem xor_circuit_essential {N s : Nat} (d : CircDesc N s) (hs : 0 < s)
    (comp : Bool) (heval : ∀ x, evalD hs d x = comp.xor (xorBool N x))
    (a : Fin N) (x : BitString N) :
    evalD hs d x ≠ evalD hs d (Function.update x a (!x a)) := by
  rw [heval, heval, xorBool_flip]
  cases comp <;> cases xorBool N x <;> simp [Bool.xor]
private theorem exists_index_ne {N : Nat} (hN : 2 ≤ N) (a : Fin N) :
    ∃ b : Fin N, b ≠ a := by
  rcases Nat.lt_or_ge a.val 1 with h | h
  · exact ⟨⟨1, by omega⟩, fun he => by simp [Fin.ext_iff] at he; omega⟩
  · exact ⟨⟨0, by omega⟩, fun he => by simp [Fin.ext_iff] at he; omega⟩
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
private theorem last_gate_no_input_ref {n s : Nat} (d : CircDesc (n + 1) s)
    (hs : 0 < s) (hn : 0 < n) (comp : Bool)
    (heval : ∀ x, evalD hs d x = comp.xor (xorBool (n + 1) x))
    (g : Fin s) (hg : (d g).2.1.1.val = 0 ∨ (d g).2.1.2.val = 0) :
    g.val < s - 1 := by
  by_contra hge; push Not at hge
  have hg_last : g.val = s - 1 := by omega
  have hg_eq : (⟨s - 1, by omega⟩ : Fin s) = g := Fin.ext hg_last.symm
  have hessential := xor_circuit_essential d hs comp heval
  -- Pick x with input 0 at gate g's killing value: the last gate becomes constant,
  -- so flipping input 1 leaves the output fixed, contradicting essentiality of input 1.
  rcases hg with hg0 | hg0
  · -- First wire input of gate g reads input 0
    -- Killing value: AND → x₀ = n₁, OR → x₀ = ¬n₁
    let kv := if (d g).1 then (d g).2.2.1 else !((d g).2.2.1)
    let x₀ : BitString (n + 1) := Function.update (fun _ => false) ⟨0, by omega⟩ kv
    have hne := hessential ⟨1, by omega⟩ x₀
    apply hne; clear hne
    have hfin_ne : (⟨0, by omega⟩ : Fin (n + 1)) ≠ ⟨1, by omega⟩ := by
      simp [Fin.ext_iff]
    simp only [evalD]
    conv_lhs => rw [wireValD]
    conv_rhs => rw [wireValD]
    simp only [show ¬(n + 1 + s - 1 < n + 1) from by omega, dite_false,
               show n + 1 + s - 1 - (n + 1) = s - 1 from by omega, hg_eq]
    -- Both sides compute gate g. First wire input has val = 0.
    have hw1_lt : (d g).2.1.1.val < n + 1 + s - 1 := by omega
    simp only [hg0]
    -- Unfold wireValD at wire 0 → primary input
    conv_lhs => rw [show wireValD d x₀ ⟨0, by omega⟩ = x₀ ⟨0, by omega⟩ from by
      rw [wireValD]; simp [show (0 : Nat) < n + 1 from by omega]]
    conv_rhs => rw [show wireValD d (Function.update x₀ ⟨1, by omega⟩ (!x₀ ⟨1, by omega⟩))
      ⟨0, by omega⟩ = x₀ ⟨0, by omega⟩ from by
      rw [wireValD]; simp [show (0 : Nat) < n + 1 from by omega]]
    have hx0 : x₀ ⟨0, by omega⟩ = kv := Function.update_self ..
    simp only [hx0]
    -- Simplify the 0 < n + 1 + s - 1 condition
    simp only [show (0 : Nat) < n + 1 + s - 1 from by omega, ite_true]
    -- kv kills the gate: AND → n1 ^^ n1 = false, OR → n1 ^^ ¬n1 = true
    split <;> simp_all [kv]
  · -- Second wire input reads input 0 (symmetric)
    let kv := if (d g).1 then (d g).2.2.2 else !((d g).2.2.2)
    let x₀ : BitString (n + 1) := Function.update (fun _ => false) ⟨0, by omega⟩ kv
    have hne := hessential ⟨1, by omega⟩ x₀
    apply hne; clear hne
    have hfin_ne : (⟨0, by omega⟩ : Fin (n + 1)) ≠ ⟨1, by omega⟩ := by
      simp [Fin.ext_iff]
    simp only [evalD]
    conv_lhs => rw [wireValD]
    conv_rhs => rw [wireValD]
    simp only [show ¬(n + 1 + s - 1 < n + 1) from by omega, dite_false,
               show n + 1 + s - 1 - (n + 1) = s - 1 from by omega, hg_eq]
    have hw2_lt : (d g).2.1.2.val < n + 1 + s - 1 := by omega
    simp only [hg0]
    conv_lhs => rw [show wireValD d x₀ ⟨0, by omega⟩ = x₀ ⟨0, by omega⟩ from by
      rw [wireValD]; simp [show (0 : Nat) < n + 1 from by omega]]
    conv_rhs => rw [show wireValD d (Function.update x₀ ⟨1, by omega⟩ (!x₀ ⟨1, by omega⟩))
      ⟨0, by omega⟩ = x₀ ⟨0, by omega⟩ from by
      rw [wireValD]; simp [show (0 : Nat) < n + 1 from by omega]]
    have hx0 : x₀ ⟨0, by omega⟩ = kv := Function.update_self ..
    simp only [hx0]
    simp only [show (0 : Nat) < n + 1 + s - 1 from by omega, ite_true]
    split <;> simp_all [kv]
private theorem wireValD_eq_sole_no_back_ref {N s : Nat}
    (d : CircDesc N s) (a : Fin N) (b : Bool)
    (g : Fin s)
    (honly : ∀ g' : Fin s, g' ≠ g → (d g').2.1.1.val ≠ a.val ∧ (d g').2.1.2.val ≠ a.val)
    (hunref : ∀ g' : Fin s, g'.val > g.val →
      (d g').2.1.1.val ≠ N + g.val ∧ (d g').2.1.2.val ≠ N + g.val)
    (x : BitString N) (w : Fin (N + s))
    (hw1 : w.val ≠ a.val) (hw2 : w.val ≠ N + g.val) :
    wireValD d x w = wireValD d (Function.update x a b) w := by
  by_cases hw_lt : w.val < N
  · conv_lhs => rw [wireValD]
    conv_rhs => rw [wireValD]
    simp only [hw_lt, dite_true]
    exact (Function.update_of_ne (show (⟨w.val, hw_lt⟩ : Fin N) ≠ a from
      fun h => hw1 (congrArg Fin.val h)) b x).symm
  · have hi : w.val - N < s := by omega
    have hi_ne : (⟨w.val - N, hi⟩ : Fin s) ≠ g := by
      intro h; apply hw2; have := congrArg Fin.val h; simp at this; omega
    obtain ⟨ho1, ho2⟩ := honly ⟨w.val - N, hi⟩ hi_ne
    have hrec1 : ∀ (_ : (d ⟨w.val - N, hi⟩).2.1.1.val < w.val),
        wireValD d x ⟨(d ⟨w.val - N, hi⟩).2.1.1.val, by omega⟩ =
        wireValD d (Function.update x a b) ⟨(d ⟨w.val - N, hi⟩).2.1.1.val, by omega⟩ := by
      intro hw1_lt
      apply wireValD_eq_sole_no_back_ref d a b g honly hunref x _ ho1
      intro heq; exact absurd heq (hunref ⟨w.val - N, hi⟩ (show w.val - N > g.val by omega)).1
    have hrec2 : ∀ (_ : (d ⟨w.val - N, hi⟩).2.1.2.val < w.val),
        wireValD d x ⟨(d ⟨w.val - N, hi⟩).2.1.2.val, by omega⟩ =
        wireValD d (Function.update x a b) ⟨(d ⟨w.val - N, hi⟩).2.1.2.val, by omega⟩ := by
      intro hw2_lt
      apply wireValD_eq_sole_no_back_ref d a b g honly hunref x _ ho2
      intro heq; exact absurd heq (hunref ⟨w.val - N, hi⟩ (show w.val - N > g.val by omega)).2
    conv_lhs => rw [wireValD]
    conv_rhs => rw [wireValD]
    simp only [hw_lt, dite_false]
    simp_all
termination_by w.val
private theorem wireValD_at_gate {N s : Nat} (d : CircDesc N s) (x : BitString N)
    (g : Fin s) :
    wireValD d x ⟨N + g.val, by omega⟩ =
      (if (d g).1 then
        ((d g).2.2.1.xor (if (d g).2.1.1.val < N + g.val then
          wireValD d x ⟨(d g).2.1.1.val, (d g).2.1.1.isLt⟩ else false)) &&
        ((d g).2.2.2.xor (if (d g).2.1.2.val < N + g.val then
          wireValD d x ⟨(d g).2.1.2.val, (d g).2.1.2.isLt⟩ else false))
      else
        ((d g).2.2.1.xor (if (d g).2.1.1.val < N + g.val then
          wireValD d x ⟨(d g).2.1.1.val, (d g).2.1.1.isLt⟩ else false)) ||
        ((d g).2.2.2.xor (if (d g).2.1.2.val < N + g.val then
          wireValD d x ⟨(d g).2.1.2.val, (d g).2.1.2.isLt⟩ else false))) := by
  have h := wireValD.eq_def d x ⟨N + g.val, by omega⟩
  simp only [show ¬(N + g.val < N) from by omega, dite_false] at h
  rw [show (⟨N + g.val - N, _⟩ : Fin s) = g from by ext; simp] at h
  exact h
private theorem gateConstW1 {N s : Nat} (d : CircDesc N s) (gg : Fin s) (a : Fin N)
    (hw : (d gg).2.1.1.val = a.val) (y : BitString N)
    (hya : y a = (d gg).2.2.1.xor (!(d gg).1)) :
    wireValD d y ⟨N + gg.val, by omega⟩ = !(d gg).1 := by
  rw [wireValD_at_gate]
  have ha_lt : (d gg).2.1.1.val < N + gg.val := by have := a.isLt; omega
  have hval : wireValD d y ⟨(d gg).2.1.1.val, (d gg).2.1.1.isLt⟩ = y a := by
    rw [wireValD]; simp_all
  simp_all
private theorem gateConstW2 {N s : Nat} (d : CircDesc N s) (gg : Fin s) (a : Fin N)
    (hw : (d gg).2.1.2.val = a.val) (y : BitString N)
    (hya : y a = (d gg).2.2.2.xor (!(d gg).1)) :
    wireValD d y ⟨N + gg.val, by omega⟩ = !(d gg).1 := by
  rw [wireValD_at_gate]
  have ha_lt : (d gg).2.1.2.val < N + gg.val := by have := a.isLt; omega
  have hval : wireValD d y ⟨(d gg).2.1.2.val, (d gg).2.1.2.isLt⟩ = y a := by
    rw [wireValD]; simp_all
  simp_all
private theorem lastGateNoInput {N s : Nat} (d : CircDesc N s) (hs : 0 < s) (hN : 2 ≤ N)
    (comp : Bool) (heval : ∀ x, evalD hs d x = comp.xor (xorBool N x)) :
    N ≤ (d ⟨s - 1, by omega⟩).2.1.1.val ∧ N ≤ (d ⟨s - 1, by omega⟩).2.1.2.val := by
  set g : Fin s := ⟨s - 1, by omega⟩ with hg_def
  have hessential := xor_circuit_essential d hs comp heval
  have houtput : ∀ x, evalD hs d x = wireValD d x ⟨N + g.val, by omega⟩ := by
    intro x; simp only [evalD]; congr 1; ext; simp only [hg_def]; omega
  -- If gate g's first wire reads input a, fixing a to the killing value makes g constant.
  have killw1 : ∀ (a : Fin N), (d g).2.1.1.val = a.val →
      ∀ y : BitString N, y a = (d g).2.2.1.xor (!(d g).1) →
      wireValD d y ⟨N + g.val, by omega⟩ = !(d g).1 :=
    gateConstW1 d g
  have killw2 : ∀ (a : Fin N), (d g).2.1.2.val = a.val →
      ∀ y : BitString N, y a = (d g).2.2.2.xor (!(d g).1) →
      wireValD d y ⟨N + g.val, by omega⟩ = !(d g).1 :=
    gateConstW2 d g
  have dom : ∀ (a : Fin N),
      (d g).2.1.1.val = a.val ∨ (d g).2.1.2.val = a.val → False := by
    intro a hga
    obtain ⟨b, hba⟩ := exists_index_ne hN a
    rcases hga with hw1 | hw2
    · set kv : Bool := (d g).2.2.1.xor (!(d g).1) with hkv
      set x₀ : BitString N := Function.update (fun _ => false) a kv with hx₀
      apply hessential b x₀
      have hxa : x₀ a = kv := Function.update_self ..
      have hxa' : (Function.update x₀ b (!x₀ b)) a = kv := by
        rw [Function.update_of_ne (fun he => hba he.symm), hxa]
      rw [houtput, houtput, killw1 a hw1 x₀ hxa, killw1 a hw1 _ hxa']
    · set kv : Bool := (d g).2.2.2.xor (!(d g).1) with hkv
      set x₀ : BitString N := Function.update (fun _ => false) a kv with hx₀
      apply hessential b x₀
      have hxa : x₀ a = kv := Function.update_self ..
      have hxa' : (Function.update x₀ b (!x₀ b)) a = kv := by
        rw [Function.update_of_ne (fun he => hba he.symm), hxa]
      rw [houtput, houtput, killw2 a hw2 x₀ hxa, killw2 a hw2 _ hxa']
  refine ⟨?_, ?_⟩
  · by_contra h; push Not at h
    exact dom ⟨(d g).2.1.1.val, by omega⟩ (.inl rfl)
  · by_contra h; push Not at h
    exact dom ⟨(d g).2.1.2.val, by omega⟩ (.inr rfl)
private theorem xor_needs_three_gates {N s : Nat} (hN : 2 ≤ N) (hs : 0 < s) (hs2 : s ≤ 2) :
    ∀ (d : CircDesc N s) (comp : Bool),
    ¬(∀ x : BitString N, evalD hs d x = comp.xor (xorBool N x)) := by
  intro d comp heval
  have hessential := xor_circuit_essential d hs comp heval
  have notConst : ∀ (c : Bool), ¬(∀ x, evalD hs d x = c) := fun c hc =>
    hessential ⟨0, by omega⟩ (fun _ => false) ((hc _).trans (hc _).symm)
  by_cases hcount : 2 * s < N
  · have hess : ∀ a : Fin N, ∃ g : Fin s,
        (d g).2.1.1.val = a.val ∨ (d g).2.1.2.val = a.val := fun a =>
      evalD_essential_means_referenced d hs a ⟨fun _ => false, hessential a _⟩
    let refs : Finset Nat := Finset.univ.biUnion fun g : Fin s =>
      {(d g).2.1.1.val, (d g).2.1.2.val}
    have hcard : refs.card ≤ 2 * s := by
      calc refs.card
          ≤ ∑ g : Fin s, ({(d g).2.1.1.val, (d g).2.1.2.val} : Finset Nat).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ _ : Fin s, 2 := Finset.sum_le_sum fun g _ => by
            apply le_trans (Finset.card_insert_le _ _); simp [Finset.card_singleton]
        _ = 2 * s := by simp [Finset.sum_const, mul_comm]
    have hNle : N ≤ refs.card := by
      calc N = ((Finset.univ : Finset (Fin N)).image Fin.val).card := by
              rw [Finset.card_image_of_injective _ Fin.val_injective, Finset.card_fin]
        _ ≤ refs.card := Finset.card_le_card fun x hx => by
            simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
            obtain ⟨a, _, rfl⟩ := hx
            obtain ⟨g, hg⟩ := hess a
            exact Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ _, by
              rcases hg with h | h <;> simp [Finset.mem_insert, Finset.mem_singleton, h]⟩
    omega
  · push Not at hcount
    obtain ⟨hout1, hout2⟩ := lastGateNoInput d hs hN comp heval
    have houtput : ∀ x, evalD hs d x = wireValD d x ⟨N + (s - 1), by omega⟩ := by
      intro x; simp only [evalD]; congr 1; ext; simp; omega
    interval_cases s
    · -- s = 1: the output gate reads no input, so its value is constant.
      have hb1 : N ≤ (d ⟨0, by omega⟩).2.1.1.val := hout1
      have hb2 : N ≤ (d ⟨0, by omega⟩).2.1.2.val := hout2
      apply notConst (if (d ⟨0, by omega⟩).1 then
          ((d ⟨0, by omega⟩).2.2.1.xor false) && ((d ⟨0, by omega⟩).2.2.2.xor false)
        else ((d ⟨0, by omega⟩).2.2.1.xor false) || ((d ⟨0, by omega⟩).2.2.2.xor false))
      intro x
      rw [houtput, show (⟨N + (1 - 1), by omega⟩ : Fin (N + 1))
            = ⟨N + (⟨0, by omega⟩ : Fin 1).val, by omega⟩ from rfl,
        wireValD_at_gate d x ⟨0, by omega⟩]
      simp only [Nat.add_zero,
        show ¬((d ⟨0, by omega⟩).2.1.1.val < N) from by omega,
        show ¬((d ⟨0, by omega⟩).2.1.2.val < N) from by omega, ite_false]
    · -- s = 2: the output gate (gate 1) depends only on gate 0.
      have hout1 : N ≤ (d ⟨1, by omega⟩).2.1.1.val := hout1
      have hout2 : N ≤ (d ⟨1, by omega⟩).2.1.2.val := hout2
      have gate1dep : ∀ y₁ y₂ : BitString N,
          wireValD d y₁ ⟨N, by omega⟩ = wireValD d y₂ ⟨N, by omega⟩ →
          wireValD d y₁ ⟨N + 1, by omega⟩ = wireValD d y₂ ⟨N + 1, by omega⟩ := by
        intro y₁ y₂ hg0
        rw [show (⟨N + 1, by omega⟩ : Fin (N + 2)) = ⟨N + (⟨1, by omega⟩ : Fin 2).val, by omega⟩
          from rfl, wireValD_at_gate d y₁ ⟨1, by omega⟩, wireValD_at_gate d y₂ ⟨1, by omega⟩]
        have key : ∀ (w : Fin (N + 2)), N ≤ w.val →
            (if w.val < N + 1 then wireValD d y₁ ⟨w.val, w.isLt⟩ else false) =
            (if w.val < N + 1 then wireValD d y₂ ⟨w.val, w.isLt⟩ else false) := by
          intro w hw
          by_cases hlt : w.val < N + 1
          · have hwN : w.val = N := le_antisymm (Nat.lt_succ_iff.mp hlt) hw
            simp_all
          · simp only [hlt, ite_false]
        rw [key (d ⟨1, by omega⟩).2.1.1 hout1, key (d ⟨1, by omega⟩).2.1.2 hout2]
      -- gate 0's value, when its input-wire (if any) is fixed, is independent of inputs.
      suffices hg0const : ∃ c : Bool, ∀ x, evalD hs d x = c by
        obtain ⟨c, hc⟩ := hg0const; exact notConst c hc
      by_cases hg0in : ∃ a : Fin N,
          (d ⟨0, by omega⟩).2.1.1.val = a.val ∨ (d ⟨0, by omega⟩).2.1.2.val = a.val
      · -- gate 0 reads input a: fixing a to gate-0's killing value makes evalD
        -- constant, contradicting essentiality.
        exfalso
        obtain ⟨a, ha⟩ := hg0in
        obtain ⟨b, hba⟩ := exists_index_ne hN a
        rcases ha with ha1 | ha2
        · set kv : Bool := (d ⟨0, by omega⟩).2.2.1.xor (!(d ⟨0, by omega⟩).1) with hkv
          set x₀ : BitString N := Function.update (fun _ => false) a kv with hx₀
          apply hessential b x₀
          have hk : ∀ y : BitString N, y a = kv →
              wireValD d y ⟨N, by omega⟩ = !(d ⟨0, by omega⟩).1 := by
            intro y hya
            have := gateConstW1 d ⟨0, by omega⟩ a ha1 y (by rw [hya, hkv])
            simp_all
          rw [houtput, houtput]
          exact gate1dep _ _ ((hk x₀ (Function.update_self ..)).trans
            (hk (Function.update x₀ b (!x₀ b))
              (by rw [Function.update_of_ne (fun he => hba he.symm)];
                  exact Function.update_self ..)).symm)
        · set kv : Bool := (d ⟨0, by omega⟩).2.2.2.xor (!(d ⟨0, by omega⟩).1) with hkv
          set x₀ : BitString N := Function.update (fun _ => false) a kv with hx₀
          apply hessential b x₀
          have hk : ∀ y : BitString N, y a = kv →
              wireValD d y ⟨N, by omega⟩ = !(d ⟨0, by omega⟩).1 := by
            intro y hya
            have := gateConstW2 d ⟨0, by omega⟩ a ha2 y (by rw [hya, hkv])
            simp_all
          rw [houtput, houtput]
          exact gate1dep _ _ ((hk x₀ (Function.update_self ..)).trans
            (hk (Function.update x₀ b (!x₀ b))
              (by rw [Function.update_of_ne (fun he => hba he.symm)];
                  exact Function.update_self ..)).symm)
      · -- gate 0 reads no input → gate 0 (and hence evalD) is constant.
        push Not at hg0in
        have hge1 : N ≤ (d ⟨0, by omega⟩).2.1.1.val := by
          by_contra hlt; push Not at hlt
          exact (hg0in ⟨(d ⟨0, by omega⟩).2.1.1.val, hlt⟩).1 rfl
        have hge2 : N ≤ (d ⟨0, by omega⟩).2.1.2.val := by
          by_contra hlt; push Not at hlt
          exact (hg0in ⟨(d ⟨0, by omega⟩).2.1.2.val, hlt⟩).2 rfl
        -- gate 0 has no input wire, so its value is the same constant for any input.
        have hg0const : ∀ y : BitString N,
            wireValD d y ⟨N, by omega⟩ = wireValD d (fun _ => false) ⟨N, by omega⟩ := by
          intro y
          rw [show (⟨N, by omega⟩ : Fin (N + 2)) = ⟨N + (⟨0, by omega⟩ : Fin 2).val, by omega⟩
            from rfl, wireValD_at_gate d y ⟨0, by omega⟩,
            wireValD_at_gate d (fun _ => false) ⟨0, by omega⟩]
          simp only [Nat.add_zero,
            show ¬((d ⟨0, by omega⟩).2.1.1.val < N) from by omega,
            show ¬((d ⟨0, by omega⟩).2.1.2.val < N) from by omega, ite_false]
        refine ⟨wireValD d (fun _ => false) ⟨N + 1, by omega⟩, fun x => ?_⟩
        rw [houtput]
        exact gate1dep _ _ (hg0const x)
private theorem wireValD_restrictD_killing_w1_gen {n s : Nat} (d : CircDesc (n + 1) s)
    (g : Fin s) (b : Bool) (x : BitString n)
    (hw1 : (d g).2.1.1.val = 0) (hkill : (d g).2.2.1.xor b = !(d g).1) :
    wireValD (restrictD d ⟨0, by omega⟩ b) x ⟨n + g.val, by omega⟩ = !(d g).1 := by
  set d_r := restrictD d ⟨0, by omega⟩ b
  have h_isAnd : (d_r g).1 = (d g).1 := by dsimp [d_r, restrictD]
  have h_w1_val : (d_r g).2.1.1.val = n + g.val := by
    change (remapWireR ⟨0, _⟩ b g (d g).2.1.1 (d g).2.2.1).1.val = _; simp [remapWireR, hw1]
  have h_n1 : (d_r g).2.2.1 = (d g).2.2.1.xor b := by
    change (remapWireR ⟨0, _⟩ b g (d g).2.1.1 (d g).2.2.1).2 = _; simp [remapWireR, hw1]
  have step1 := wireValD_at_gate d_r x g
  simp_all
private theorem wireValD_restrictD_killing_w2_gen {n s : Nat} (d : CircDesc (n + 1) s)
    (g : Fin s) (b : Bool) (x : BitString n)
    (hw2 : (d g).2.1.2.val = 0) (hkill : (d g).2.2.2.xor b = !(d g).1) :
    wireValD (restrictD d ⟨0, by omega⟩ b) x ⟨n + g.val, by omega⟩ = !(d g).1 := by
  set d_r := restrictD d ⟨0, by omega⟩ b
  have h_isAnd : (d_r g).1 = (d g).1 := by dsimp [d_r, restrictD]
  have h_w2_val : (d_r g).2.1.2.val = n + g.val := by
    change (remapWireR ⟨0, _⟩ b g (d g).2.1.2 (d g).2.2.2).1.val = _; simp [remapWireR, hw2]
  have h_n2 : (d_r g).2.2.2 = (d g).2.2.2.xor b := by
    change (remapWireR ⟨0, _⟩ b g (d g).2.1.2 (d g).2.2.2).2 = _; simp [remapWireR, hw2]
  have step1 := wireValD_at_gate d_r x g
  simp_all
private theorem self_ref_gate_redirect {N s : Nat} (d : CircDesc N s) (g : Fin s)
    (hself : (d g).2.1.1.val = N + g.val ∨ (d g).2.1.2.val = N + g.val) :
    ∃ (rd : GateRedirect (N + s)),
      (∀ x, wireValD d x ⟨N + g.val, by omega⟩ = match rd with
        | .const c => c
        | .wire w flip => flip.xor (wireValD d x ⟨w.val, by omega⟩)) ∧
      (∀ w' flip, rd = .wire w' flip → w'.val < N + g.val) := by
  have us := fun x => wireValD_at_gate d x g
  rcases hself with hw1_self | hw2_self
  · have hw1_nlt : ¬((d g).2.1.1.val < N + g.val) := by omega
    by_cases hkill : (d g).2.2.1 = !(d g).1
    · exact ⟨.const (!(d g).1), fun x => by
        simp_all, fun _ _ h => by cases h⟩
    · have hn1 : (d g).2.2.1 = (d g).1 := by
        revert hkill; cases (d g).2.2.1 <;> cases (d g).1 <;> simp
      by_cases hw2_lt : (d g).2.1.2.val < N + g.val
      · exact ⟨.wire ⟨(d g).2.1.2.val, by omega⟩ (d g).2.2.2, fun x => by
          simp_all, fun w' fl h => by cases h; exact hw2_lt⟩
      · exact ⟨.const (if (d g).1 then (d g).2.2.1 && (d g).2.2.2
            else (d g).2.2.1 || (d g).2.2.2), fun x => by
          rw [us]; simp only [hw1_nlt, hw2_lt, ite_false, Bool.xor_false],
          fun _ _ h => by cases h⟩
  · have hw2_nlt : ¬((d g).2.1.2.val < N + g.val) := by omega
    by_cases hkill : (d g).2.2.2 = !(d g).1
    · exact ⟨.const (!(d g).1), fun x => by
        simp_all, fun _ _ h => by cases h⟩
    · have hn2 : (d g).2.2.2 = (d g).1 := by
        revert hkill; cases (d g).2.2.2 <;> cases (d g).1 <;> simp
      by_cases hw1_lt : (d g).2.1.1.val < N + g.val
      · exact ⟨.wire ⟨(d g).2.1.1.val, by omega⟩ (d g).2.2.1, fun x => by
          simp_all, fun w' fl h => by cases h; exact hw1_lt⟩
      · exact ⟨.const (if (d g).1 then (d g).2.2.1 && (d g).2.2.2
            else (d g).2.2.1 || (d g).2.2.2), fun x => by
          rw [us]; simp only [hw1_lt, hw2_nlt, ite_false, Bool.xor_false],
          fun _ _ h => by cases h⟩
private theorem restrictD_false_components {n s : Nat} (d : CircDesc (n + 1) s) (g : Fin s) :
    let d_r := restrictD d ⟨0, by omega⟩ false
    (d_r g).1 = (d g).1 ∧ (d_r g).2.2.1 = (d g).2.2.1 ∧ (d_r g).2.2.2 = (d g).2.2.2 ∧
    (d_r g).2.1.1.val = (if (d g).2.1.1.val = 0 then n + g.val else (d g).2.1.1.val - 1) ∧
    (d_r g).2.1.2.val = (if (d g).2.1.2.val = 0 then n + g.val else (d g).2.1.2.val - 1) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;>
    · simp only [restrictD, remapWireR]
      split_ifs <;> first | omega | simp_all
private theorem gateElimRedirect_const {n s : Nat} (d : CircDesc (n + 1) s) (g : Fin s)
    (x : BitString n)
    (hw1 : ¬((restrictD d ⟨0, by omega⟩ false g).2.1.1.val < n + g.val))
    (hw2 : ¬((restrictD d ⟨0, by omega⟩ false g).2.1.2.val < n + g.val)) :
    wireValD (restrictD d ⟨0, by omega⟩ false) x ⟨n + g.val, by omega⟩ =
      if (d g).1 then (d g).2.2.1 && (d g).2.2.2 else (d g).2.2.1 || (d g).2.2.2 := by
  obtain ⟨hop, hn1, hn2, _, _⟩ := restrictD_false_components d g
  have step1 := wireValD_at_gate (restrictD d ⟨0, by omega⟩ false) x g
  simp only [hw1, hw2, ite_false, Bool.xor_false] at step1
  simp_all
private theorem gateElimRedirect {n t : Nat} (d : CircDesc (n + 1) (t + 3))
    (g : Fin (t + 3)) (hg0 : (d g).2.1.1.val = 0 ∨ (d g).2.1.2.val = 0) :
    ∃ (rd : GateRedirect (n + (t + 2))),
      (∀ x : BitString n,
        wireValD (restrictD d ⟨0, by omega⟩ false) x ⟨n + g.val, by omega⟩ =
          match rd with
          | .const c => c
          | .wire w flip =>
            flip.xor (wireValD (restrictD d ⟨0, by omega⟩ false) x ⟨w.val, by omega⟩)) ∧
      (∀ w' flip, rd = .wire w' flip → w'.val < n + g.val) := by
  set d_r := restrictD d ⟨0, by omega⟩ false with hd_r_def
  -- After restriction with b=false, a wire reading input 0 becomes a self-reference
  -- ⟨n + g.val,...⟩ (evaluating to false), so its effective value is its negation flag.
  set isAnd := (d g).1
  set w1 := (d g).2.1.1
  set w2 := (d g).2.1.2
  set n1 := (d g).2.2.1
  set n2 := (d g).2.2.2
  rcases hg0 with h1 | h2
  · -- First wire reads input 0 (w1.val = 0)
    by_cases hkill : n1 = !isAnd
    · -- Killing: AND with n1=false or OR with n1=true → constant output
      exact ⟨.const (!isAnd), ⟨fun x =>
        wireValD_restrictD_killing_w1_gen d g false x h1 (by rw [Bool.xor_false]; exact hkill),
        fun _ _ h => by cases h⟩⟩
    · -- Non-killing: n1 ≠ !isAnd, so output = v2 (second wire value)
      by_cases hw2_zero : w2.val = 0
      · -- Both wires read input 0: v2 constant
        obtain ⟨_, _, _, hwv1, hwv2⟩ := restrictD_false_components d g
        exact ⟨.const (if isAnd then n1 && n2 else n1 || n2), ⟨fun x =>
          gateElimRedirect_const d g x (by rw [hwv1, if_pos h1]; omega)
            (by rw [hwv2, if_pos hw2_zero]; omega), fun _ _ h => by cases h⟩⟩
      · by_cases hw2_back : w2.val - 1 < n + g.val
        · -- Second wire back-ref after restriction
          exact ⟨.wire ⟨w2.val - 1, by omega⟩ n2,
            ⟨fun x => by
              dsimp only
              have hw1_fin : (d g).2.1.1 = 0 := by ext; exact h1
              have h_w1_val : (d_r g).2.1.1.val = n + g.val := by
                change (restrictD d ⟨0, _⟩ false g).2.1.1.val = _
                simp [restrictD, remapWireR, hw1_fin]
              have h_w2_val : (d_r g).2.1.2.val = w2.val - 1 := by
                change (restrictD d ⟨0, _⟩ false g).2.1.2.val = _
                simp only [restrictD, remapWireR]; split_ifs <;> (first | omega | rfl)
              have h_n1 : (d_r g).2.2.1 = (d g).2.2.1 := by
                change (restrictD d ⟨0, _⟩ false g).2.2.1 = _
                simp [restrictD, remapWireR, hw1_fin]
              have h_n2 : (d_r g).2.2.2 = (d g).2.2.2 := by
                change (restrictD d ⟨0, _⟩ false g).2.2.2 = _
                simp only [restrictD, remapWireR]; split_ifs <;> (first | omega | rfl)
              have step1 := wireValD_at_gate d_r x g
              have hw1_nlt : ¬((d_r g).2.1.1.val < n + g.val) := by rw [h_w1_val]; omega
              have hw2_lt' : (d_r g).2.1.2.val < n + g.val := by rw [h_w2_val]; exact hw2_back
              simp only [hw1_nlt, ite_false, Bool.xor_false, hw2_lt', ite_true] at step1
              rw [show (d_r g).1 = isAnd from rfl, h_n1, h_n2] at step1
              simp only [h_w2_val, show (d g).2.2.1 = n1 from rfl,
                show (d g).2.2.2 = n2 from rfl] at step1
              simp_all,
             fun w' flip h => by
              simp only [GateRedirect.wire.injEq] at h; obtain ⟨rfl, _⟩ := h
              exact hw2_back⟩⟩
        · -- Second wire forward-ref after restriction (proof 3)
          obtain ⟨_, _, _, hwv1, hwv2⟩ := restrictD_false_components d g
          exact ⟨.const (if isAnd then n1 && n2 else n1 || n2), ⟨fun x =>
            gateElimRedirect_const d g x (by rw [hwv1, if_pos h1]; omega)
              (by rw [hwv2, if_neg hw2_zero]; omega), fun _ _ h => by cases h⟩⟩
  · -- Second wire reads input 0 (symmetric)
    by_cases hkill : n2 = !isAnd
    · exact ⟨.const (!isAnd), ⟨fun x =>
        wireValD_restrictD_killing_w2_gen d g false x h2 (by rw [Bool.xor_false]; exact hkill),
        fun _ _ h => by cases h⟩⟩
    · by_cases hw1_zero : w1.val = 0
      · -- proof 4: both w1=0, w2=0
        obtain ⟨_, _, _, hwv1, hwv2⟩ := restrictD_false_components d g
        exact ⟨.const (if isAnd then n1 && n2 else n1 || n2), ⟨fun x =>
          gateElimRedirect_const d g x (by rw [hwv1, if_pos hw1_zero]; omega)
            (by rw [hwv2, if_pos h2]; omega), fun _ _ h => by cases h⟩⟩
      · by_cases hw1_back : w1.val - 1 < n + g.val
        · -- proof 5: w1≠0 back-ref, w2=0 (.wire case)
          exact ⟨.wire ⟨w1.val - 1, by omega⟩ n1,
            ⟨fun x => by
              dsimp only
              have hw2_fin : (d g).2.1.2 = 0 := by ext; exact h2
              have h_w1_val : (d_r g).2.1.1.val = w1.val - 1 := by
                change (restrictD d ⟨0, _⟩ false g).2.1.1.val = _
                simp only [restrictD, remapWireR]; split_ifs <;> (first | omega | rfl)
              have h_w2_val : (d_r g).2.1.2.val = n + g.val := by
                change (restrictD d ⟨0, _⟩ false g).2.1.2.val = _
                simp [restrictD, remapWireR, hw2_fin]
              have h_n1 : (d_r g).2.2.1 = (d g).2.2.1 := by
                change (restrictD d ⟨0, _⟩ false g).2.2.1 = _
                simp only [restrictD, remapWireR]; split_ifs <;> (first | omega | rfl)
              have h_n2 : (d_r g).2.2.2 = (d g).2.2.2 := by
                change (restrictD d ⟨0, _⟩ false g).2.2.2 = _
                simp [restrictD, remapWireR, hw2_fin]
              have step1 := wireValD_at_gate d_r x g
              have hw1_lt : (d_r g).2.1.1.val < n + g.val := by rw [h_w1_val]; exact hw1_back
              have hw2_nlt : ¬((d_r g).2.1.2.val < n + g.val) := by rw [h_w2_val]; omega
              simp only [hw1_lt, ite_true, hw2_nlt, ite_false, Bool.xor_false] at step1
              rw [show (d_r g).1 = isAnd from rfl, h_n1, h_n2] at step1
              simp only [h_w1_val, show (d g).2.2.1 = n1 from rfl,
                show (d g).2.2.2 = n2 from rfl] at step1
              simp_all,
             fun w' flip h => by
              simp only [GateRedirect.wire.injEq] at h; obtain ⟨rfl, _⟩ := h
              exact hw1_back⟩⟩
        · -- proof 6: w1≠0 forward-ref, w2=0 (const case)
          obtain ⟨_, _, _, hwv1, hwv2⟩ := restrictD_false_components d g
          exact ⟨.const (if isAnd then n1 && n2 else n1 || n2), ⟨fun x =>
            gateElimRedirect_const d g x (by rw [hwv1, if_neg hw1_zero]; omega)
              (by rw [hwv2, if_pos h2]; omega), fun _ _ h => by cases h⟩⟩
private theorem elimTwoGatesWire {n t : Nat} (d_r : CircDesc n (t + 3)) (comp : Bool)
    (hd_r_eval : ∀ x : BitString n,
      evalD (by omega : 0 < t + 3) d_r x = comp.xor (xorBool n x))
    (ga gb : Fin (t + 3)) (hlt : gb.val < ga.val) (hga_not_last : ga.val < t + 2)
    (rda : GateRedirect (n + (t + 2)))
    (hrda : ∀ x : BitString n, wireValD d_r x ⟨n + ga.val, by omega⟩ =
      match rda with
      | .const c => c
      | .wire w flip => flip.xor (wireValD d_r x ⟨w.val, by omega⟩))
    (hrda_wire : ∀ w' flip, rda = .wire w' flip → w'.val < n + ga.val)
    (rdb : GateRedirect (n + (t + 2)))
    (hrdb : ∀ x : BitString n, wireValD d_r x ⟨n + gb.val, by omega⟩ =
      match rdb with
      | .const c => c
      | .wire w flip => flip.xor (wireValD d_r x ⟨w.val, by omega⟩))
    (hrdb_wire : ∀ w' flip, rdb = .wire w' flip → w'.val < n + gb.val) :
    ∃ (s' : Nat) (d' : CircDesc n s') (hs' : 0 < s') (comp' : Bool),
      s' + 2 ≤ t + 3 ∧ (∀ x, evalD hs' d' x = comp'.xor (xorBool n x)) := by
  -- The continuation `finish` removes `gb` once `ga` has been eliminated to `rdaC`.
  -- It is supplied a `liftAt` fact specialised to the concrete `rdaC`, so all
  -- `match` motives are already reduced and the elimination lemmas apply.
  suffices finish : ∀ (rdaC : GateRedirect (n + (t + 2)))
      (_ : ∀ (k : Nat) (hk : k < n + (t + 2)), k < n + ga.val → ∀ y,
        wireValD (elimGateD d_r ga rdaC) y ⟨k, hk⟩ = wireValD d_r y ⟨k, by omega⟩)
      (_ : ∀ x, evalD (by omega : 0 < t + 2) (elimGateD d_r ga rdaC) x =
        comp.xor (xorBool n x)),
      ∃ (s' : Nat) (d' : CircDesc n s') (hs' : 0 < s') (comp' : Bool),
        s' + 2 ≤ t + 3 ∧ (∀ x, evalD hs' d' x = comp'.xor (xorBool n x)) by
    cases rda with
    | const ca =>
      refine finish (.const ca) (fun k hk hlt' y => ?_) (fun x => ?_)
      · have s := wireValD_elimGateD d_r ga (.const ca) hrda hrda_wire y ⟨k, hk⟩
        rwa [show liftWireE ga ⟨k, hk⟩ = (⟨k, by omega⟩ : Fin (n + (t + 3))) from
          Fin.ext (liftWireE_val_lt (show k < n + ga.val by omega))] at s
      · rw [evalD_elimGateD d_r (by omega) ga (.const ca) hrda hrda_wire hga_not_last x,
          hd_r_eval x]
    | wire wa fa =>
      refine finish (.wire wa fa) (fun k hk hlt' y => ?_) (fun x => ?_)
      · have s := wireValD_elimGateD d_r ga (.wire wa fa) hrda hrda_wire y ⟨k, hk⟩
        rwa [show liftWireE ga ⟨k, hk⟩ = (⟨k, by omega⟩ : Fin (n + (t + 3))) from
          Fin.ext (liftWireE_val_lt (show k < n + ga.val by omega))] at s
      · rw [evalD_elimGateD d_r (by omega) ga (.wire wa fa) hrda hrda_wire hga_not_last x,
          hd_r_eval x]
  intro rdaC liftAt hd₁
  cases rdb with
  | const c =>
    refine ⟨t + 1, elimGateD (elimGateD d_r ga rdaC) ⟨gb.val, by omega⟩ (.const c),
      by omega, comp, by omega, fun x => ?_⟩
    have key : ∀ y, wireValD (elimGateD d_r ga rdaC) y ⟨n + gb.val, by omega⟩ = c := by
      intro y; rw [liftAt (n + gb.val) (by omega) (by omega) y]; exact hrdb y
    have hd₂ := evalD_elimGateD (elimGateD d_r ga rdaC) (by omega : 0 < t + 1)
      ⟨gb.val, by omega⟩ (.const c) key (fun _ _ h => by cases h) (show gb.val < t + 1 by omega)
    rw [hd₂ x, hd₁ x]
  | wire w flip =>
    have hwlt : w.val < n + gb.val := hrdb_wire w flip rfl
    refine ⟨t + 1, elimGateD (elimGateD d_r ga rdaC) ⟨gb.val, by omega⟩
      (.wire ⟨w.val, by omega⟩ flip), by omega, comp, by omega, fun x => ?_⟩
    have key : ∀ y, wireValD (elimGateD d_r ga rdaC) y ⟨n + gb.val, by omega⟩ =
        flip.xor (wireValD (elimGateD d_r ga rdaC) y ⟨w.val, by omega⟩) := by
      intro y
      rw [liftAt (n + gb.val) (by omega) (by omega) y, liftAt w.val (by omega) (by omega) y]
      exact hrdb y
    have hd₂ := evalD_elimGateD (elimGateD d_r ga rdaC) (by omega : 0 < t + 1)
      ⟨gb.val, by omega⟩ (.wire ⟨w.val, by omega⟩ flip) key
      (fun w' fl h => by cases h; omega) (show gb.val < t + 1 by omega)
    rw [hd₂ x, hd₁ x]
private theorem restrictionElimTwoA {n t : Nat} (d : CircDesc (n + 1) (t + 3))
    (hn : 0 < n) (comp : Bool)
    (heval : ∀ x, evalD (by omega : 0 < t + 3) d x = comp.xor (xorBool (n + 1) x))
    (g₁ : Fin (t + 3)) (hg₁ : (d g₁).2.1.1.val = 0 ∨ (d g₁).2.1.2.val = 0)
    (hg₁_not_last : g₁.val < t + 2)
    (hd_r_eval : ∀ x : BitString n,
      evalD (by omega : 0 < t + 3) (restrictD d ⟨0, by omega⟩ false) x =
        comp.xor (xorBool n x))
    (h_two : ∃ g₂ : Fin (t + 3),
      ((d g₂).2.1.1.val = 0 ∨ (d g₂).2.1.2.val = 0) ∧ g₂ ≠ g₁) :
    ∃ (s' : Nat) (d' : CircDesc n s') (hs' : 0 < s') (comp' : Bool),
      s' + 2 ≤ t + 3 ∧ (∀ x, evalD hs' d' x = comp'.xor (xorBool n x)) := by
  set d_r := restrictD d ⟨0, by omega⟩ false with hd_r_def
  have gate_elim_rd : ∀ (g : Fin (t + 3)),
      (d g).2.1.1.val = 0 ∨ (d g).2.1.2.val = 0 →
      ∃ (rd : GateRedirect (n + (t + 2))),
        (∀ x : BitString n, wireValD d_r x ⟨n + g.val, by omega⟩ =
          match rd with
          | .const c => c
          | .wire w flip => flip.xor (wireValD d_r x ⟨w.val, by omega⟩)) ∧
        (∀ w' flip, rd = .wire w' flip → w'.val < n + g.val) :=
    fun g hg0 => gateElimRedirect d g hg0
  obtain ⟨g₂, hg₂, hg₂_ne⟩ := h_two
  have hg₂_not_last : g₂.val < t + 2 :=
    last_gate_no_input_ref d (by omega) hn comp heval g₂ hg₂
  obtain ⟨rd₁, hrd₁, hrd₁_wire⟩ := gate_elim_rd g₁ hg₁
  obtain ⟨rd₂, hrd₂, hrd₂_wire⟩ := gate_elim_rd g₂ hg₂
  have hne : g₁.val ≠ g₂.val := fun h => hg₂_ne (Fin.ext h.symm)
  by_cases hlt : g₁.val < g₂.val
  · exact elimTwoGatesWire d_r comp hd_r_eval g₂ g₁ hlt hg₂_not_last
      rd₂ hrd₂ hrd₂_wire rd₁ hrd₁ hrd₁_wire
  · exact elimTwoGatesWire d_r comp hd_r_eval g₁ g₂ (by omega) hg₁_not_last
      rd₁ hrd₁ hrd₁_wire rd₂ hrd₂ hrd₂_wire
private theorem truncateAtGate {n t j : Nat} (d₁ : CircDesc n (t + 2))
    (hj_lt : j < t + 1) (K : Bool)
    (hxor : ∀ x, wireValD d₁ x ⟨n + j, by omega⟩ = K.xor (xorBool n x)) :
    ∃ (s' : Nat) (d' : CircDesc n s') (hs' : 0 < s') (comp' : Bool),
      s' + 2 ≤ t + 3 ∧ (∀ x, evalD hs' d' x = comp'.xor (xorBool n x)) := by
  let clampW (i : Fin (j + 1)) (w : Fin (n + (t + 2))) : Fin (n + (j + 1)) :=
    if h : w.val < n + (j + 1) then ⟨w.val, h⟩ else ⟨n + i.val, by omega⟩
  let d₂ : CircDesc n (j + 1) := fun i =>
    ((d₁ ⟨i.val, by omega⟩).1,
     (clampW i (d₁ ⟨i.val, by omega⟩).2.1.1,
      clampW i (d₁ ⟨i.val, by omega⟩).2.1.2),
     (d₁ ⟨i.val, by omega⟩).2.2)
  -- wireValD agrees on the truncated circuit (by strong induction on the wire index)
  have htrunc : ∀ x (w : Fin (n + (j + 1))),
      wireValD d₂ x w = wireValD d₁ x ⟨w.val, by omega⟩ := by
    intro x
    -- Use strong induction on w.val
    suffices h : ∀ (k : Nat) (hk : k < n + (j + 1)),
        wireValD d₂ x ⟨k, hk⟩ = wireValD d₁ x ⟨k, by omega⟩ from
      fun w => h w.val w.isLt
    intro k
    induction k using Nat.strongRecOn with
    | _ k ih =>
      intro hk
      by_cases hkn : k < n
      · rw [wireValD, wireValD]; simp only [hkn, dite_true]
      · conv_lhs => rw [wireValD]; simp only [hkn, dite_false]
        conv_rhs => rw [wireValD]; simp only [hkn, dite_false]
        -- Suffices to show each wire input gives the same xor'd value
        suffices hwire : ∀ (ni : Bool) (wi_d1 : Fin (n + (t + 2))),
            ni.xor (if (clampW ⟨k - n, by omega⟩ wi_d1).val < k then
              wireValD d₂ x ⟨(clampW ⟨k - n, by omega⟩ wi_d1).val,
                (clampW ⟨k - n, by omega⟩ wi_d1).isLt⟩ else false) =
            ni.xor
              (if wi_d1.val < k then wireValD d₁ x ⟨wi_d1.val, wi_d1.isLt⟩ else false) by
          split <;> (congr 1 <;> [skip; skip]) <;> exact hwire _ _
        intro ni wi_d1
        simp only [clampW]
        split
        · -- Wire in bounds
          simp_all
        · -- Wire out of bounds: clamped to n + (k - n) = k
          rename_i h_out
          simp only [show ¬(n + (k - n) < k) from by omega, ite_false,
            show ¬(wi_d1.val < k) from by omega]
  refine ⟨j + 1, d₂, by omega, K, by omega, fun x => ?_⟩
  simp only [evalD]
  simp_all
private theorem restrictionElimTwoB {n t : Nat} (d : CircDesc (n + 1) (t + 3))
    (hn : 0 < n) (comp : Bool)
    (hessential : ∀ (a : Fin (n + 1)) (x : BitString (n + 1)),
      evalD (by omega : 0 < t + 3) d x ≠
        evalD (by omega : 0 < t + 3) d (Function.update x a (!x a)))
    (hrestrict : ∀ b : Bool, ∀ x : BitString n,
      evalD (by omega : 0 < t + 3) (restrictD d ⟨0, by omega⟩ b) x =
        (comp.xor b).xor (xorBool n x))
    (g₁ : Fin (t + 3)) (hg₁ : (d g₁).2.1.1.val = 0 ∨ (d g₁).2.1.2.val = 0)
    (hg₁_not_last : g₁.val < t + 2)
    (h_two : ¬∃ g₂ : Fin (t + 3),
      ((d g₂).2.1.1.val = 0 ∨ (d g₂).2.1.2.val = 0) ∧ g₂ ≠ g₁) :
    ∃ (s' : Nat) (d' : CircDesc n s') (hs' : 0 < s') (comp' : Bool),
      s' + 2 ≤ t + 3 ∧ (∀ x, evalD hs' d' x = comp'.xor (xorBool n x)) := by
  push Not at h_two
  -- g₁ is the sole gate reading input 0
  have honly : ∀ g' : Fin (t + 3), g' ≠ g₁ →
      (d g').2.1.1.val ≠ (⟨0, by omega⟩ : Fin (n + 1)).val ∧
      (d g').2.1.2.val ≠ (⟨0, by omega⟩ : Fin (n + 1)).val := by
    intro g' hne
    exact ⟨fun h1 => absurd (h_two g' (.inl h1)) hne, fun h2 => absurd (h_two g' (.inr h2)) hne⟩
  -- g₁ must be referenced by a strictly later gate (else input 0 is inessential).
  have hg₁_back_ref : ∃ g' : Fin (t + 3), g₁.val < g'.val ∧
      ((d g').2.1.1.val = (n + 1) + g₁.val ∨ (d g').2.1.2.val = (n + 1) + g₁.val) := by
    by_contra h; push Not at h
    exact hessential ⟨0, by omega⟩ (fun _ => false)
      (by simp only [evalD]
          exact wireValD_eq_sole_no_back_ref d ⟨0, by omega⟩ true g₁ honly
            (fun g' hgt => h g' hgt) (fun _ => false)
            ⟨(n + 1) + (t + 3) - 1, by omega⟩
            (by dsimp only []; omega)
            (by dsimp only []; omega))
  obtain ⟨g', hg'_gt, hg'_ref⟩ := hg₁_back_ref
  -- Choose killing value: ensures g₁ has constant output !(d g₁).1
  obtain ⟨b_kill, hg₁_const⟩ : ∃ b : Bool, ∀ x : BitString n,
      wireValD (restrictD d ⟨0, by omega⟩ b) x ⟨n + g₁.val, by omega⟩ = !(d g₁).1 := by
    rcases hg₁ with h1 | h2
    · refine ⟨(d g₁).2.2.1.xor (!(d g₁).1), fun x =>
        wireValD_restrictD_killing_w1_gen d g₁ _ x h1 ?_⟩
      cases (d g₁).2.2.1 <;> cases (d g₁).1 <;> rfl
    · refine ⟨(d g₁).2.2.2.xor (!(d g₁).1), fun x =>
        wireValD_restrictD_killing_w2_gen d g₁ _ x h2 ?_⟩
      cases (d g₁).2.2.2 <;> cases (d g₁).1 <;> rfl
  set c₁ := !(d g₁).1
  set d_rb := restrictD d ⟨0, by omega⟩ b_kill
  -- First elimination: g₁ from d_rb
  set d₁ := elimGateD d_rb g₁ (.const c₁)
  have hd₁ : ∀ x, evalD (by omega : 0 < t + 2) d₁ x =
      (comp.xor b_kill).xor (xorBool n x) := by
    intro x
    rw [show evalD (by omega : 0 < t + 2) d₁ x = evalD (by omega : 0 < t + 3) d_rb x from
      evalD_elimGateD d_rb (by omega) g₁ (.const c₁) hg₁_const
        (fun _ _ h => by cases h) hg₁_not_last x]
    exact hrestrict b_kill x
  -- In d₁, gate g' (index g'.val-1) has a self-ref wire → constant input
  -- Use wireValD_elimGateD to relate d₁ back to d_rb
  have hg'_pos : g'.val ≥ 1 := by omega
  have hg'_val : ∀ x, wireValD d₁ x ⟨n + (g'.val - 1), by omega⟩ =
      wireValD d_rb x ⟨n + g'.val, by omega⟩ := by
    intro x
    have h := wireValD_elimGateD d_rb g₁ (.const c₁) hg₁_const
      (fun _ _ h => by cases h) x ⟨n + (g'.val - 1), by omega⟩
    have hlift : liftWireE g₁ ⟨n + (g'.val - 1), by omega⟩ =
        (⟨n + g'.val, by omega⟩ : Fin (n + (t + 3))) := by
      simp only [liftWireE, show ¬(n + (g'.val - 1) < n + g₁.val) from by omega, ite_false]
      ext; simp; omega
    rw [hlift] at h; exact h
  -- Second elimination: gate g' in d_rb has one input = c₁, making it eliminable in d₁
  have hg'_ne : g' ≠ g₁ := by intro h; exact absurd (h ▸ le_refl g₁.val) (not_le.mpr hg'_gt)
  have hg'_no_zero := honly g' hg'_ne
  -- Gate g'.val-1 in d₁ has a self-referencing wire
  -- First establish what d_rb g' wires look like after restriction
  have hg'_rb_w1 : (d_rb g').2.1.1.val = (d g').2.1.1.val - 1 := by
    simp only [d_rb, restrictD, remapWireR]
    simp_all
  have hg'_rb_w2 : (d_rb g').2.1.2.val = (d g').2.1.2.val - 1 := by
    simp only [d_rb, restrictD, remapWireR]
    simp_all
  -- Now show the self-reference in d₁
  have hg'_self : (d₁ ⟨g'.val - 1, by omega⟩).2.1.1.val = n + (g'.val - 1) ∨
      (d₁ ⟨g'.val - 1, by omega⟩).2.1.2.val = n + (g'.val - 1) := by
    -- Unfold elimGateD at index g'.val - 1
    -- Since g'.val - 1 ≥ g₁.val, oldIdx = ⟨g'.val, _⟩
    have hig : ¬(g'.val - 1 < g₁.val) := by omega
    have hg'_bound2 : g'.val - 1 < t + 2 := by omega
    have hg'_bound3 : g'.val - 1 + 1 < t + 3 := by omega
    change (elimGateD d_rb g₁ (.const c₁) ⟨g'.val - 1, hg'_bound2⟩).2.1.1.val = n + (g'.val - 1) ∨
        (elimGateD d_rb g₁ (.const c₁) ⟨g'.val - 1, hg'_bound2⟩).2.1.2.val = n + (g'.val - 1)
    simp only [elimGateD, hig, dite_false]
    have hgi : (⟨g'.val - 1 + 1, hg'_bound3⟩ : Fin (t + 3)) = g' := by
      ext; dsimp only []; omega
    rw [hgi]
    -- Now need to show remapWireE maps one of the wires to self-ref
    -- Case split on which wire of d g' references g₁
    rcases hg'_ref with hw1_ref | hw2_ref
    · -- Wire 1 references g₁: (d g').2.1.1.val = (n+1) + g₁.val
      -- After restriction: (d_rb g').2.1.1.val = n + g₁.val
      left
      have hw1_rb : (d_rb g').2.1.1.val = n + g₁.val := by
        rw [hg'_rb_w1, hw1_ref]; omega
      simp only [remapWireE]
      -- (d_rb g').2.1.1.val = n + g₁.val ≥ n, so not < n
      simp only [dite_false,
        show ((d_rb g').2.1.1.val = n + g₁.val) from hw1_rb, dite_true,
        show ¬(g'.val - 1 < g₁.val) from hig, ite_false, Fin.val_mk,
        show ¬(n + g₁.val < n) from by omega]
    · -- Wire 2 references g₁
      right
      have hw2_rb : (d_rb g').2.1.2.val = n + g₁.val := by rw [hg'_rb_w2]; omega
      simp only [remapWireE]
      have h_not_lt_n : ¬((d_rb g').2.1.2.val < n) := by omega
      simp only [h_not_lt_n, dite_false]
      simp only [show (d_rb g').2.1.2.val = n + g₁.val from hw2_rb, dite_true,
        show ¬(g'.val - 1 < g₁.val) from hig, ite_false, Fin.val_mk]
  -- Apply self_ref_gate_redirect to get a redirect for gate g'.val-1
  obtain ⟨rd₂, hrd₂, hrd₂_wire⟩ := self_ref_gate_redirect d₁ ⟨g'.val - 1, by omega⟩ hg'_self
  -- Case split on whether g'.val - 1 is the last gate
  by_cases hg'_not_last2 : g'.val - 1 < t + 1
  · -- Non-last gate: eliminate it
    rcases rd₂ with ⟨c₂⟩ | ⟨⟨w₂, hw₂⟩, f₂⟩
    · -- const redirect
      refine ⟨t + 1, elimGateD d₁ ⟨g'.val - 1, by omega⟩ (.const c₂), by omega,
        comp.xor b_kill, by omega, fun x => ?_⟩
      rw [evalD_elimGateD d₁ (by omega : 0 < t + 1) ⟨g'.val - 1, by omega⟩ (.const c₂)
        hrd₂ (fun _ _ h => by cases h) hg'_not_last2 x]
      exact hd₁ x
    · -- wire redirect
      have hw₂_lt : w₂ < n + (g'.val - 1) := hrd₂_wire ⟨w₂, hw₂⟩ f₂ rfl
      refine ⟨t + 1, elimGateD d₁ ⟨g'.val - 1, by omega⟩ (.wire ⟨w₂, by omega⟩ f₂), by omega,
        comp.xor b_kill, by omega, fun x => ?_⟩
      have hrd₂' : ∀ x, wireValD d₁ x ⟨n + (g'.val - 1), by omega⟩ =
          f₂.xor (wireValD d₁ x ⟨w₂, by omega⟩) := by
        intro x; have h := hrd₂ x; simp only at h; exact h
      rw [evalD_elimGateD d₁ (by omega : 0 < t + 1) ⟨g'.val - 1, by omega⟩
        (.wire ⟨w₂, by omega⟩ f₂)
        hrd₂' (fun w' fl h => by cases h; omega) hg'_not_last2 x]
      exact hd₁ x
  · -- Last gate case: g'.val - 1 = t + 1, so g'.val = t + 2
    have hg'_last : g'.val = t + 2 := by omega
    -- The last gate (index t+1) of d₁ has a self-ref → redirect
    -- evalD reads the last wire: n + (t+2) - 1 = n + (t+1) = n + (g'.val - 1)
    have heval_wire : ∀ x, evalD (by omega : 0 < t + 2) d₁ x =
        wireValD d₁ x ⟨n + (t + 1), by omega⟩ := by
      intro x; rfl
    have heval_last : ∀ x, wireValD d₁ x ⟨n + (t + 1), by omega⟩ =
        wireValD d₁ x ⟨n + (g'.val - 1), by omega⟩ := by
      intro x; congr 1; ext; dsimp only []; omega
    rcases rd₂ with ⟨c₂⟩ | ⟨⟨w₂, hw₂⟩, f₂⟩
    · -- Constant redirect: evalD d₁ is constant, contradicting XOR non-constancy
      exfalso
      have hconst : ∀ x, (comp.xor b_kill).xor (xorBool n x) = c₂ := by
        intro x; rw [← hd₁ x, heval_wire x, heval_last x, hrd₂ x]
      have h0 := hconst (fun _ => false)
      have h1 := hconst (Function.update (fun _ => false) ⟨0, hn⟩ true)
      rw [show Function.update (fun _ : Fin n => false) ⟨0, hn⟩ true =
        Function.update (fun _ : Fin n => false) ⟨0, hn⟩ (!(fun _ : Fin n => false) ⟨0, hn⟩) from
        by simp] at h1
      rw [xorBool_flip] at h1
      -- h0 : comp ^^ b_kill ^^ xorBool n (fun _ => false) = c₂
      -- h1 : comp ^^ b_kill ^^ !xorBool n (fun _ => false) = c₂
      simp_all
    · -- Wire redirect: evalD d₁ x = f₂ ⊕ wireValD d₁ x w₂
      have hw₂_lt : w₂ < n + (g'.val - 1) := hrd₂_wire ⟨w₂, hw₂⟩ f₂ rfl
      -- evalD d₁ x = f₂ ⊕ wireValD d₁ x w₂ = (comp ⊕ b_kill) ⊕ xorBool n x
      -- So wireValD d₁ x ⟨w₂, _⟩ computes XOR (up to flip)
      have hxor_at_w₂ : ∀ x, wireValD d₁ x ⟨w₂, by omega⟩ =
          (f₂.xor (comp.xor b_kill)).xor (xorBool n x) := by
        intro x
        have h1 := hd₁ x
        have h2 : evalD (by omega : 0 < t + 2) d₁ x =
            f₂.xor (wireValD d₁ x ⟨w₂, by omega⟩) := by
          rw [heval_wire x, heval_last x, hrd₂ x]
        rw [h1] at h2
        -- h2 : (comp ^^ b_kill ^^ xorBool n x) = f₂ ^^ wireValD d₁ x ⟨w₂, _⟩
        -- Need: wireValD d₁ x ⟨w₂, _⟩ = (f₂ ^^ comp ^^ b_kill) ^^ xorBool n x
        simp_all
      by_cases hw₂n : w₂ < n
      · -- Wire w₂ is an input: build a 1-gate AND-self circuit reading w₂
        -- (gate 0 computes AND(x w₂, x w₂) = x w₂).
        refine ⟨1, fun _ => (true, (⟨w₂, by omega⟩, ⟨w₂, by omega⟩), (false, false)),
          by omega, f₂.xor (comp.xor b_kill), by omega, fun x => ?_⟩
        change wireValD (fun _ => (true, (⟨w₂, by omega⟩, ⟨w₂, by omega⟩), (false, false)))
          x ⟨n, by omega⟩ = _
        rw [wireValD]
        simp only [show ¬(n < n) from by omega, dite_false, hw₂n,
          ite_true, Bool.and_self]
        rw [wireValD]; simp only [hw₂n, dite_true]
        have hw₂_input : wireValD d₁ x ⟨w₂, by omega⟩ = x ⟨w₂, hw₂n⟩ := by
          rw [wireValD]; simp only [hw₂n, dite_true]
        rw [← hw₂_input, hxor_at_w₂ x, Bool.false_xor]
      · -- Wire w₂ is a gate output: truncate circuit
        push Not at hw₂n
        have hj_lt : w₂ - n < t + 1 := by omega
        have hxw : ∀ x, wireValD d₁ x ⟨n + (w₂ - n), by omega⟩ =
            (f₂.xor (comp.xor b_kill)).xor (xorBool n x) := by
          simp_all
        exact truncateAtGate d₁ hj_lt (f₂.xor (comp.xor b_kill)) hxw
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
theorem _root_.solution {n s : Nat} (d : CircDesc (n + 1) s)
    (hs : 0 < s) (hn : 0 < n) (comp : Bool)
    (heval : ∀ x, evalD hs d x = comp.xor (xorBool (n + 1) x))
    (hessential : ∀ (a : Fin (n + 1)) (x : BitString (n + 1)),
      evalD hs d x ≠ evalD hs d (Function.update x a (!x a))) :
    ∃ (s' : Nat) (d' : CircDesc n s') (hs' : 0 < s') (comp' : Bool),
      s' + 2 ≤ s ∧ (∀ x, evalD hs' d' x = comp'.xor (xorBool n x)) := by
  -- s ≥ 3
  have hs3 : 3 ≤ s := by
    by_contra h; push Not at h
    exact xor_needs_three_gates (by omega) hs (by omega) d comp heval
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 3 := ⟨s - 3, by omega⟩
  -- Some gate reads input 0
  obtain ⟨g₁, hg₁⟩ := evalD_essential_means_referenced d (by omega) ⟨0, by omega⟩
    ⟨fun _ => false, hessential ⟨0, by omega⟩ (fun _ => false)⟩
  have hg₁_not_last : g₁.val < t + 2 :=
    last_gate_no_input_ref d (by omega) hn comp heval g₁ hg₁
  simp only [] at hg₁
  -- Restricted circuit computes XOR_n for any restriction value b
  have hrestrict : ∀ b : Bool, ∀ x : BitString n,
      evalD (by omega : 0 < t + 3) (restrictD d ⟨0, by omega⟩ b) x =
      (comp.xor b).xor (xorBool n x) := by
    intro b x; rw [evalD_restrictD, heval, xorBool_insertAt, Bool.xor_assoc]
  -- Restrict input 0 to false
  let d_r := restrictD d ⟨0, by omega⟩ false
  have hd_r_eval : ∀ x : BitString n, evalD (by omega : 0 < t + 3) d_r x =
      comp.xor (xorBool n x) := by
    intro x; change evalD _ (restrictD d ⟨0, by omega⟩ false) x = _
    rw [hrestrict]; simp
  -- After restriction, any gate reading input 0 has a self-referencing wire
  -- and can be eliminated via a GateRedirect
  have gate_elim_rd : ∀ (g : Fin (t + 3)),
      (d g).2.1.1.val = 0 ∨ (d g).2.1.2.val = 0 →
      ∃ (rd : GateRedirect (n + (t + 2))),
        (∀ x : BitString n, wireValD d_r x ⟨n + g.val, by omega⟩ =
          match rd with
          | .const c => c
          | .wire w flip => flip.xor (wireValD d_r x ⟨w.val, by omega⟩)) ∧
        (∀ w' flip, rd = .wire w' flip → w'.val < n + g.val) :=
    fun g hg0 => gateElimRedirect d g hg0
  -- Case A: ∃ second gate reading input 0, or Case B: sole reader → cascade
  by_cases h_two : ∃ g₂ : Fin (t + 3),
      ((d g₂).2.1.1.val = 0 ∨ (d g₂).2.1.2.val = 0) ∧ g₂ ≠ g₁
  · -- Case A: Two gates read input 0 → eliminate both from d_r
    exact restrictionElimTwoA d hn comp heval g₁ hg₁ hg₁_not_last hd_r_eval h_two
  · -- Case B: Only g₁ reads input 0 → g₁ is referenced → cascade
    exact restrictionElimTwoB d hn comp hessential hrestrict g₁ hg₁ hg₁_not_last h_two
end CircuitComplexity.Schnorr
