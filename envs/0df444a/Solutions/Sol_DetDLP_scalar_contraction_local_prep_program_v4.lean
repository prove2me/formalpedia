-- Prove2me | solution 1 for DetDLP.scalar_contraction_local_prep_program_v4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-25T05:08:28.115267+00:00
-- url     : https://prove2.me/submissions/15b20b02-6caa-4e93-a7db-839474041211
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_DetDLP_ContractionContinuation
import Definitions.Def_DetDLP_BTN
import Definitions.Def_OAIQ081S000
import Theorems.Thm_DetDLP_scalar_contraction_local_prep_oracle_v4

set_option autoImplicit false

open DetDLP
open DetDLP.ContinuationSchedule
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation

/-- Drop the uniform `L`/`K` budget packaging from `prep_oracle_v4`. -/
theorem solution
    (C c0 : ℕ) (hC : 0 < C) (hc0 : 0 < c0)
    {se le : ℕ} (Q : BitProgram.Program 3 se le) (it iv ot ov : Fin se) (hi : it ≠ iv) (ho : ot ≠ ov) :
    ∃ (s lp : ℕ) (hs : 0 < s) (prep : BitProgram.Program 8 (20 + s) lp),
      ∀ (β P ℓ' Told : ℕ) (desc : List Bool) (G : BipartiteMultigraph)
        (A : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Fin ℓ' → ℕ),
        2 ≤ β → 1 ≤ Told → G.nE ≤ C * β → G.nV ≤ β ^ c0 →
        1 ≤ P → P ≤ C * β → 1 ≤ ℓ' → ℓ' ≤ C * β →
        (∀ v t i, A v t i < 2 ^ P) →
        (∀ v t (regs : Fin 3 → Bool),
          let q := (encodePortQuery desc v.val (List.ofFn t)).tail
          let start : BitProgram.Cfg 3 se le := ⟨some Q.entry, regs, fun j =>
            if j = it then List.replicate q.length true else if j = iv then q else []⟩
          ∃ (n : ℕ) (c : BitProgram.Cfg 3 se le), n ≤ 8 * Told ∧ BitProgram.Trace Q n start c ∧
            c.pc = none ∧ ((((c.stacks ot).zip (c.stacks ov)).takeWhile Prod.fst).map Prod.snd) =
              encodeNatListBin (List.ofFn (A v t)) ∧
            ∀ j b, j ≤ n → BitProgram.Trace Q j start b →
              ∀ i, (b.stacks i).length ≤ (β + desc.length) ^ c0 + 8) →
        let Z := BTNContract G (fun v t => ∑ i : Fin ℓ',
          Polynomial.monomial i.val (A v t i : ℤ))
        let w := encodeNatListBin (List.ofFn fun i : Fin ℓ' =>
          ((Z.coeff i.val : ZMod (2 ^ P)).val))
        let word := w.foldr (fun b z => b.toNat + 2 * z) 1
        let B := word + 1
        let q := B + 1
        let context : Fin s → List Bool := fun i => if i.val = 0 then word.bits else []
        let pack (a b stack tag arg save : ℕ) : Fin (20 + s) → List Bool :=
          let v : Fin 12 → ℕ := ![q, 1, 0, a, b, stack, tag, arg, save, 0, 0, 0]
          Fin.addCases (m := 20) (n := s)
            (Fin.addCases (m := 8) (n := 12) (fun _ => []) (fun j => (v j).bits)) context
        let start := BitProgram.initial prep (encodeBTNInstance desc G β P ℓ')
        let reg : Fin 8 → Bool := fun _ => true
        ∃ (prepSteps cap0 : ℕ),
          BitProgram.Trace prep prepSteps start ⟨none, reg, pack 0 0 1 0 0 0⟩ ∧
            (∀ j c, j ≤ prepSteps → BitProgram.Trace prep j start c →
              ∀ i, (c.stacks i).length ≤ cap0) := by
  obtain ⟨s, lp, hs, prep, horacle⟩ :=
    scalar_contraction_local_prep_oracle_v4 C c0 hC hc0 Q it iv ot ov hi ho
  refine ⟨s, lp, hs, prep, ?_⟩
  intro β P ℓ' Told desc G A hβ ht he hv hP₁ hP₂ hl₁ hl₂ ha hQ
  obtain ⟨K, hK⟩ := horacle 0
  obtain ⟨prepSteps, cap0, _U, _hU, hTrace, hcap, _hpoly, _hspace⟩ :=
    hK β P ℓ' Told desc G A hβ ht he hv hP₁ hP₂ hl₁ hl₂ ha hQ
  exact ⟨prepSteps, cap0, hTrace, hcap⟩
