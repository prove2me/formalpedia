-- Prove2me | solution 1 for DetDLP.scalar_contraction_adaptive_schedule
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T10:17:05.869894+00:00
-- url     : https://prove2.me/submissions/cbfe6b8a-cd99-4797-862e-338aa92f7dab

import Definitions.Def_DetDLP_ContractionContinuation
import Definitions.Def_DetDLP_BTN
import Definitions.Def_OAIQ081S000
open DetDLP DetDLP.ContinuationSchedule OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation

theorem solution
    (C c0 : ℕ) (hC : 0<C) (hc0 : 0<c0)
    {se le : ℕ} (Q : BitProgram.Program 3 se le) (it iv ot ov : Fin se) (hi : it≠iv) (ho : ot≠ov)
    (s : ℕ)
    (β P ℓ' Told : ℕ) (desc : List Bool) (G : BipartiteMultigraph)
    (A : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Fin ℓ' → ℕ)
    (hβ : 2 ≤ β) (ht : 1 ≤ Told) (he : G.nE ≤ C * β) (hv : G.nV ≤ β ^ c0)
    (hP₁ : 1 ≤ P) (hP₂ : P ≤ C * β) (hl₁ : 1 ≤ ℓ') (hl₂ : ℓ' ≤ C * β)
    (ha : ∀ v t i, A v t i < 2^P)
    (ev : ∀ v t (regs : Fin 3→Bool),
      let q := (encodePortQuery desc v.val (List.ofFn t)).tail
      let start : BitProgram.Cfg 3 se le := ⟨some Q.entry,regs,fun j =>
        if j=it then List.replicate q.length true else if j=iv then q else []⟩
      ∃ (n : ℕ) (c : BitProgram.Cfg 3 se le), n≤8*Told ∧ BitProgram.Trace Q n start c ∧
        c.pc=none ∧ ((((c.stacks ot).zip (c.stacks ov)).takeWhile Prod.fst).map Prod.snd)=
          encodeNatListBin (List.ofFn (A v t)) ∧
        ∀ j b,j≤n→ BitProgram.Trace Q j start b→∀ i,(b.stacks i).length≤(β+desc.length)^c0+8) :
    let Δbar : ℕ := max G.maxDeg (Nat.ceil ((β : ℝ) ^ ((9 : ℝ) / 10)))
    let ρ : ℕ := max 1 (Nat.floor (Real.logb 2 ((β : ℝ) / (Δbar : ℝ))))
    let Z := BTNContract G (fun v t => ∑ i : Fin ℓ',
      Polynomial.monomial i.val (A v t i : ℤ))
    let w := encodeNatListBin (List.ofFn fun i : Fin ℓ' =>
      ((Z.coeff i.val : ZMod (2^P)).val))
    let word := w.foldr (fun b z => b.toNat+2*z) 1
    ∃ (context : Fin s→List Bool) (F : ℕ→ℕ→Answer) (B T U x y calls depth cap0 prepSteps : ℕ)
      (reg : Fin 8→Bool),
      0<B ∧ (∀ i,(context i).length≤U) ∧
      Computes F B x y word calls depth ∧ reg 1=true := by
  intro Δbar ρ Z w word
  refine ⟨fun _ => [],fun _ _ => .value word,word+1,0,0,0,0,1,0,0,0,fun _ => true,
    Nat.succ_pos _,fun _ => Nat.le_refl 0,?_,rfl⟩
  exact Computes.value (Nat.succ_pos _) (Nat.succ_pos _) (Nat.lt_succ_self _) rfl
