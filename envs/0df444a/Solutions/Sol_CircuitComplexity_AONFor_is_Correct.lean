-- Prove2me | solution 1 for CircuitComplexity.AONFor_is_Correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:13:26.249903+00:00
-- url     : https://prove2.me/submissions/5bd294de-df5d-457e-a05b-46224c2ae097

module
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_AON
public import Theorems.Thm_CircuitComplexity_Circuit_inputWireDepth
public import Theorems.Thm_CircuitComplexity_Circuit_wireValue_ge
public import Theorems.Thm_CircuitComplexity_Circuit_wireValue_lt
attribute [local simp] CircuitComplexity.Circuit.inputWireDepth


section
@[expose] public section
namespace CircuitComplexity
private lemma AONFor_wireValue_gate {N : Nat} [NeZero N] (f : BitString N → Bool)
    (x : BitString N) (i : Fin (2 ^ N)) :
    (AONFor f).wireValue x (Fin.natAdd N i) =
      (AONFor.mkGate f i).eval ((AONFor f).wireValue x) := by
  have hge : ¬ ((Fin.natAdd N i).val < N) := by simp [Fin.natAdd]
  rw [Circuit.wireValue_ge _ _ _ hge]
  congr 1; simp only [AONFor]; congr 1
  exact Fin.ext (by simp [Fin.natAdd])
private lemma AONFor_wireValue_input {N : Nat} [NeZero N] (f : BitString N → Bool)
    (x : BitString N) (j : Fin N) :
    (AONFor f).wireValue x (j.castAdd (2 ^ N)) = x j := by
  have h : (j.castAdd (2 ^ N)).val < N := by simp [Fin.val_castAdd]
  rw [Circuit.wireValue_lt _ _ _ h]
  congr 1
private lemma mkGate_true {N : Nat} (f : BitString N → Bool) (i : Fin (2 ^ N))
    (hfi : f (fun j => i.val.testBit j.val) = true) :
    AONFor.mkGate f i =
      { op := .and, fanIn := N, arityOk := trivial,
        inputs := fun j => (j.castAdd (2 ^ N)),
        negated := fun j => !(i.val.testBit j.val) } := by
  unfold AONFor.mkGate; simp [hfi]
private lemma mkGate_eval_false {N : Nat} (f : BitString N → Bool) (i : Fin (2 ^ N))
    (wv : BitString (N + 2 ^ N))
    (hfi : f (fun j => i.val.testBit j.val) = false) :
    (AONFor.mkGate f i).eval wv = false := by
  unfold AONFor.mkGate Gate.eval
  simp [hfi, Basis.unboundedAON, AONOp.eval, Fin.foldl_zero]
private lemma mkGate_eval_true_iff {N : Nat} (f : BitString N → Bool) (i : Fin (2 ^ N))
    (wv : BitString (N + 2 ^ N))
    (hfi : f (fun j => i.val.testBit j.val) = true) :
    (AONFor.mkGate f i).eval wv = true ↔
      ∀ j : Fin N, wv (j.castAdd (2 ^ N)) = (i.val.testBit j.val) := by
  rw [mkGate_true f i hfi]
  simp only [Gate.eval, Basis.unboundedAON, AONOp.eval]
  rw [foldl_band_eq_true]
  exact ⟨fun h j => (xor_not_eq_true_iff _ _).mp (h j),
         fun h j => (xor_not_eq_true_iff _ _).mpr (h j)⟩
end CircuitComplexity
end
end

set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
namespace CircuitComplexity
theorem _root_.solution {N : Nat} [NeZero N] (f : BitString N → Bool) :
    (fun (x : BitString 1) => x 0) ∘ (AONFor f).eval = f := by
  funext x
  simp only [Function.comp, Circuit.eval, AONFor_outputs, Gate.eval,
    Basis.unboundedAON, Bool.false_xor, AONOp.eval]
  have key : ∀ i : Fin (2^N), (AONFor f).wireValue x (Fin.natAdd N i) =
      (AONFor.mkGate f i).eval ((AONFor f).wireValue x) := AONFor_wireValue_gate f x
  conv_lhs => arg 2; ext acc i; erw [key i]
  -- Goal: Fin.foldl (2^N) (fun acc i => acc || (mkGate f i).eval (wireValue x)) false = f x
  have h_iff : (Fin.foldl (2 ^ N)
      (fun acc i => acc || (AONFor.mkGate f i).eval ((AONFor f).wireValue x))
      false = true) ↔ (f x = true) := by
    rw [foldl_bor_eq_true]
    constructor
    · -- Some gate fires → f x = true
      rintro ⟨i, hi⟩
      by_cases hfi : f (fun j => i.val.testBit j.val) = true
      · rw [mkGate_eval_true_iff f i _ hfi] at hi
        have hxeq : ∀ j : Fin N, x j = i.val.testBit j.val := by
          intro j; rw [← AONFor_wireValue_input f x j]; exact hi j
        have : f x = f (fun j => i.val.testBit j.val) := congr_arg f (funext hxeq)
        rw [this]; exact hfi
      · have hfi' : f (fun j => i.val.testBit j.val) = false := Bool.not_eq_true _ |>.mp hfi
        exact absurd (mkGate_eval_false f i _ hfi' ▸ hi) Bool.false_ne_true
    · -- f x = true → some gate fires
      intro hfx
      obtain ⟨m, hm⟩ := exists_testBit_encode N x
      refine ⟨m, ?_⟩
      have hfm : f (fun j => m.val.testBit j.val) = true := by
        convert hfx using 1; congr 1; funext j; exact hm j
      rw [mkGate_eval_true_iff f m _ hfm]
      intro j; rw [AONFor_wireValue_input f x j]; exact (hm j).symm
  -- Close by Bool case analysis using the ↔
  cases hfx : f x <;>
    cases hfold : Fin.foldl (2 ^ N) (fun acc i =>
      acc || (AONFor.mkGate f i).eval ((AONFor f).wireValue x)) false <;>
    simp_all
end CircuitComplexity
