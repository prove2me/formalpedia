-- Prove2me | solution 1 for FriedbergMuchnik.finite_oracle_evaln_primrec
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-09T21:23:24.372201+00:00
-- url     : https://prove2.me/submissions/caeb7d00-3814-4c33-9b10-07b6eba85c2e

import Definitions.Def_FriedbergMuchnik_Priority

set_option autoImplicit false
attribute [local irreducible] Primrec

open Encodable Denumerable Primrec

namespace FriedbergMuchnik

-- Mathlib's codes are used only to number and inspect syntax. Their ordinary
-- evaluator is not used for the oracle interpreter.
private abbrev Code := Nat.Partrec.Code
private abbrev Call := ℕ × (Code × ℕ)

private theorem program_toCode_primrec : Primrec Program.toCode := by
  apply Primrec.encode_iff.mp
  exact Primrec.encode

/-- A right fold preserves the sequential search's stop-on-undefined behavior. -/
private theorem boundedMu_eq_fold (f : ℕ → Option ℕ) (k n : ℕ) :
    boundedMu f k n = (List.range k).foldr
      (fun i rest => (f (n + i)).bind (fun v => if v = 0 then some (n + i) else rest))
      none := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    simp [boundedMu, List.range_succ_eq_map, List.foldr_map, ih,
      Nat.add_comm, Nat.add_left_comm]

private theorem boundedMu_primrec {α : Type} [Primcodable α]
    {f : α → ℕ → Option ℕ} {k n : α → ℕ}
    (hf : Primrec₂ f) (hk : Primrec k) (hn : Primrec n) :
    Primrec (fun a => boundedMu (f a) (k a) (n a)) := by
  have hs : Primrec (fun p : α × (ℕ × Option ℕ) =>
      (f p.1 (n p.1 + p.2.1)).bind
        (fun v => if v = 0 then some (n p.1 + p.2.1) else p.2.2)) := by
    have hi : Primrec (fun p : α × (ℕ × Option ℕ) => n p.1 + p.2.1) :=
      Primrec.nat_add.comp (hn.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)
    apply Primrec.option_bind (hf.comp Primrec.fst hi)
    exact (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0))
      (Primrec.option_some.comp (hi.comp Primrec.fst))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).to₂
  exact (Primrec.list_foldr (Primrec.list_range.comp hk) (Primrec.const none) hs.to₂).of_eq
    (fun a => (boundedMu_eq_fold (f a) (k a) (n a)).symm)

private def tableLookup (V : List (Option ℕ)) (k : ℕ) (c : Code) (n : ℕ) : Option ℕ :=
  if n < k then (V[Nat.pair (encode c) n]?).getD none else none

private theorem tableLookup_primrec :
    Primrec (fun p : List (Option ℕ) × (ℕ × (Code × ℕ)) =>
      tableLookup p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  unfold tableLookup
  exact Primrec.ite
    (Primrec.nat_lt.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.fst.comp Primrec.snd))
    (Primrec.option_getD.comp
      (Primrec.list_getElem?.comp Primrec.fst
        (Primrec₂.natPair.comp
          (Primrec.encode.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
          (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
      (Primrec.const none))
    (Primrec.const none)

/-- A finite list covering every subprogram/input call needed at the previous fuel. -/
private def dependencies (b : Call) : List Call :=
  match b.1 with
  | 0 => []
  | k + 1 => (List.range (Nat.pair (encode b.2.1) k + 1)).map
      (fun j => (k, ofNat Code j.unpair.1, j.unpair.2))

private theorem dependencies_primrec : Primrec dependencies := by
  have hpos : Primrec (fun p : Call × ℕ =>
      (List.range (Nat.pair (encode p.1.2.1) p.2 + 1)).map
        (fun j => (p.2, ofNat Code j.unpair.1, j.unpair.2))) := by
    apply Primrec.list_map
      (Primrec.list_range.comp (Primrec.succ.comp
        (Primrec₂.natPair.comp
          (Primrec.encode.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
          Primrec.snd)))
    exact ((Primrec.snd.comp Primrec.fst).pair
      (((Primrec.ofNat Code).comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))).pair
        (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))).to₂
  exact (Primrec.nat_casesOn Primrec.fst (Primrec.const []) hpos.to₂).of_eq
    (fun b => by unfold dependencies; cases b.1 <;> rfl)

private theorem dependencies_decrease (b b' : Call) (h : b' ∈ dependencies b) :
    b'.1 < b.1 := by
  rcases b with ⟨r, c, n⟩
  cases r with
  | zero => simp [dependencies] at h
  | succ k =>
    simp only [dependencies, List.mem_map] at h
    obtain ⟨j, _, rfl⟩ := h
    exact Nat.lt_succ_self k

private def evalCode (L : List ℕ) (b : Call) : Option ℕ :=
  oracleEvaln (fun n => if n ∈ L then 1 else 0) b.1 (Program.ofCode b.2.1) b.2.2

private theorem oracleEvaln_outside (O : ℕ → ℕ) (k : ℕ) (c : Program) (n : ℕ)
    (h : k ≤ n) : oracleEvaln O k c n = none := by
  cases k with
  | zero => rfl
  | succ k => simp [oracleEvaln, Nat.not_lt.mpr h]

/-- Inputs outside the table's bound are already undefined in the interpreter. -/
private theorem tableLookup_correct (L : List ℕ) (k n : ℕ) (c d : Code)
    (hd : encode d < encode c) :
    tableLookup ((dependencies (k + 1, c, n)).map (evalCode L)) k d =
      (fun x => evalCode L (k, d, x)) := by
  funext x
  by_cases hx : x < k
  · have hi : Nat.pair (encode d) x < Nat.pair (encode c) k + 1 :=
      Nat.lt_succ_of_lt ((Nat.pair_lt_pair_left x hd).trans
        (Nat.pair_lt_pair_right (encode c) hx))
    simp [tableLookup, dependencies, hx, hi, evalCode, List.map_map]
  · simp [tableLookup, hx, evalCode, oracleEvaln_outside _ _ _ _ (Nat.le_of_not_gt hx)]

private abbrev StepContext := List ℕ × (ℕ × (List (Option ℕ) × ℕ))

private def contextLookup (a : StepContext) (c : Code) (n : ℕ) : Option ℕ :=
  tableLookup a.2.2.1 a.2.1 c n

private theorem contextLookup_primrec :
    Primrec (fun p : StepContext × (Code × ℕ) => contextLookup p.1 p.2.1 p.2.2) :=
  tableLookup_primrec.comp
    ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).pair
      ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
        ((Primrec.fst.comp Primrec.snd).pair (Primrec.snd.comp Primrec.snd))))

/-- Reconstruct one constructor using table lookups for its recursive calls. -/
private def oneStep (a : StepContext) : Code → Option ℕ
  | .zero => some (if a.2.2.2 ∈ a.1 then 1 else 0)
  | .succ => some (a.2.2.2 + 1)
  | .left => some a.2.2.2.unpair.1
  | .right => some a.2.2.2.unpair.2
  | .pair f g => do
      let x ← contextLookup a f a.2.2.2
      let y ← contextLookup a g a.2.2.2
      pure (Nat.pair x y)
  | .comp f g => do
      let x ← contextLookup a g a.2.2.2
      contextLookup a f x
  | .prec f g =>
      a.2.2.2.unpair.2.rec (contextLookup a f a.2.2.2.unpair.1) fun y ih => do
        let z ← ih
        contextLookup a g (Nat.pair a.2.2.2.unpair.1 (Nat.pair y z))
  | .rfind' f =>
      boundedMu (fun m => contextLookup a f (Nat.pair a.2.2.2 m)) (a.2.1 + 1) 0

private theorem pairStep_primrec :
    Primrec (fun p : StepContext × (Code × Code) => oneStep p.1 (.pair p.2.1 p.2.2)) := by
  have hn : Primrec (fun p : StepContext × (Code × Code) => p.1.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hf := contextLookup_primrec.comp
    (Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair hn))
  have hg := contextLookup_primrec.comp
    (Primrec.fst.pair ((Primrec.snd.comp Primrec.snd).pair hn))
  exact Primrec.option_bind hf
    (Primrec.option_bind (hg.comp Primrec.fst)
      (Primrec.option_some.comp
        (Primrec₂.natPair.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)).to₂).to₂

private theorem compStep_primrec :
    Primrec (fun p : StepContext × (Code × Code) => oneStep p.1 (.comp p.2.1 p.2.2)) := by
  have hn : Primrec (fun p : StepContext × (Code × Code) => p.1.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  apply Primrec.option_bind (contextLookup_primrec.comp
    (Primrec.fst.pair ((Primrec.snd.comp Primrec.snd).pair hn)))
  exact (contextLookup_primrec.comp
    ((Primrec.fst.comp Primrec.fst).pair
      ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair Primrec.snd))).to₂

private theorem precStep_primrec :
    Primrec (fun p : StepContext × (Code × Code) => oneStep p.1 (.prec p.2.1 p.2.2)) := by
  have hn : Primrec (fun p : StepContext × (Code × Code) => p.1.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have ha := Primrec.fst.comp (Primrec.unpair.comp hn)
  have hm := Primrec.snd.comp (Primrec.unpair.comp hn)
  have hbase := contextLookup_primrec.comp
    (Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair ha))
  have hstep : Primrec (fun p : (StepContext × (Code × Code)) × (ℕ × Option ℕ) =>
      p.2.2.bind (fun z => contextLookup p.1.1 p.1.2.2
        (Nat.pair p.1.1.2.2.2.unpair.1 (Nat.pair p.2.1 z)))) := by
    apply Primrec.option_bind (Primrec.snd.comp Primrec.snd)
    exact (contextLookup_primrec.comp
      ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
        ((Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair
          (Primrec₂.natPair.comp (ha.comp (Primrec.fst.comp Primrec.fst))
            (Primrec₂.natPair.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
              Primrec.snd))))).to₂
  exact Primrec.nat_rec' hm hbase hstep.to₂

private theorem muStep_primrec :
    Primrec (fun p : StepContext × Code => oneStep p.1 (.rfind' p.2)) := by
  have hn : Primrec (fun p : StepContext × Code => p.1.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  apply boundedMu_primrec
  · exact (contextLookup_primrec.comp
      ((Primrec.fst.comp Primrec.fst).pair
        ((Primrec.snd.comp Primrec.fst).pair
          (Primrec₂.natPair.comp (hn.comp Primrec.fst) Primrec.snd)))).to₂
  · exact Primrec.succ.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
  · exact Primrec.const 0

private theorem oneStep_primrec : Primrec₂ oneStep := by
  have hn : Primrec (fun p : StepContext × Code => p.1.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hmem : PrimrecRel (fun (L : List ℕ) (n : ℕ) => n ∈ L) :=
    (Primrec.eq.exists_mem_list).of_eq (by simp)
  have hzero := Primrec.option_some.comp
    (Primrec.ite (hmem.comp (Primrec.fst.comp Primrec.fst) hn)
      (Primrec.const 1) (Primrec.const 0))
  have hsucc := Primrec.option_some.comp (Primrec.succ.comp hn)
  have hleft := Primrec.option_some.comp (Primrec.fst.comp (Primrec.unpair.comp hn))
  have hright := Primrec.option_some.comp (Primrec.snd.comp (Primrec.unpair.comp hn))
  have hbinary : Primrec (fun p : (StepContext × Code) × (Code × (Code × (Option ℕ × Option ℕ))) =>
      (p.1.1, p.2.1, p.2.2.1)) :=
    (Primrec.fst.comp Primrec.fst).pair
      ((Primrec.fst.comp Primrec.snd).pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
  have hunary : Primrec (fun p : (StepContext × Code) × (Code × Option ℕ) =>
      (p.1.1, p.2.1)) :=
    (Primrec.fst.comp Primrec.fst).pair (Primrec.fst.comp Primrec.snd)
  have hrec := Nat.Partrec.Code.primrec_recOn Primrec.snd hzero hsucc hleft hright
    (pr := fun a f g _ _ => oneStep a.1 (.pair f g)) (pairStep_primrec.comp hbinary)
    (co := fun a f g _ _ => oneStep a.1 (.comp f g)) (compStep_primrec.comp hbinary)
    (pc := fun a f g _ _ => oneStep a.1 (.prec f g)) (precStep_primrec.comp hbinary)
    (rf := fun a f _ => oneStep a.1 (.rfind' f)) (muStep_primrec.comp hunary)
  exact hrec.of_eq (fun p => by rcases p with ⟨a, c⟩; cases c <;> rfl)

private def rebuild (L : List ℕ) (b : Call) (V : List (Option ℕ)) : Option ℕ :=
  match b.1 with
  | 0 => none
  | k + 1 => if b.2.2 < k + 1 then oneStep (L, k, V, b.2.2) b.2.1 else none

private theorem rebuild_primrec :
    Primrec (fun p : List ℕ × (Call × List (Option ℕ)) => rebuild p.1 p.2.1 p.2.2) := by
  have hpos : Primrec (fun p : (List ℕ × (Call × List (Option ℕ))) × ℕ =>
      if p.1.2.1.2.2 < p.2 + 1 then
        oneStep (p.1.1, p.2, p.1.2.2, p.1.2.1.2.2) p.1.2.1.2.1
      else none) := by
    have hn : Primrec (fun p : (List ℕ × (Call × List (Option ℕ))) × ℕ => p.1.2.1.2.2) :=
      Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
    have hc : Primrec (fun p : (List ℕ × (Call × List (Option ℕ))) × ℕ => p.1.2.1.2.1) :=
      Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
    exact Primrec.ite (Primrec.nat_lt.comp hn (Primrec.succ.comp Primrec.snd))
      (oneStep_primrec.comp
        ((Primrec.fst.comp Primrec.fst).pair (Primrec.snd.pair
          ((Primrec.snd.comp (Primrec.snd.comp Primrec.fst)).pair hn))) hc)
      (Primrec.const none)
  exact (Primrec.nat_casesOn (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
    (Primrec.const none) hpos.to₂).of_eq
    (fun p => by unfold rebuild; cases p.2.1.1 <;> rfl)

private theorem rebuild_correct (L : List ℕ) (b : Call) :
    rebuild L b ((dependencies b).map (evalCode L)) = evalCode L b := by
  rcases b with ⟨r, c, n⟩
  cases r with
  | zero => rfl
  | succ k =>
    by_cases hn : n < k + 1
    · have look (d : Code) (hd : encode d < encode c) :
          contextLookup (L, k, (dependencies (k + 1, c, n)).map (evalCode L), n) d =
            (fun x => evalCode L (k, d, x)) :=
        tableLookup_correct L k n c d hd
      simp only [rebuild, if_pos hn]
      cases c with
      | zero => simp [oneStep, evalCode, Program.ofCode, oracleEvaln, hn]
      | succ => simp [oneStep, evalCode, Program.ofCode, oracleEvaln, hn]
      | left => simp [oneStep, evalCode, Program.ofCode, oracleEvaln, hn]
      | right => simp [oneStep, evalCode, Program.ofCode, oracleEvaln, hn]
      | pair f g =>
        simp only [oneStep]
        rw [look f (Nat.Partrec.Code.encode_lt_pair f g).1,
          look g (Nat.Partrec.Code.encode_lt_pair f g).2]
        simp [evalCode, Program.ofCode, oracleEvaln, hn]
      | comp f g =>
        simp only [oneStep]
        rw [look f (Nat.Partrec.Code.encode_lt_comp f g).1,
          look g (Nat.Partrec.Code.encode_lt_comp f g).2]
        simp [evalCode, Program.ofCode, oracleEvaln, hn]
      | prec f g =>
        simp only [oneStep]
        rw [look f (Nat.Partrec.Code.encode_lt_prec f g).1,
          look g (Nat.Partrec.Code.encode_lt_prec f g).2]
        simp [evalCode, Program.ofCode, oracleEvaln, hn]
      | rfind' f =>
        simp only [oneStep]
        rw [look f (Nat.Partrec.Code.encode_lt_rfind' f)]
        simp [evalCode, Program.ofCode, oracleEvaln, hn]
    · simp [rebuild, evalCode, oracleEvaln, hn]

/-- The finite dependency list decreases in fuel, so bounded-table recursion applies. -/
private theorem evalCode_primrec : Primrec₂ evalCode := by
  apply Primrec.nat_omega_rec evalCode
    (m := fun (_ : List ℕ) (b : Call) => b.1)
    (l := fun (_ : List ℕ) (b : Call) => dependencies b)
    (g := fun (L : List ℕ) (p : Call × List (Option ℕ)) => some (rebuild L p.1 p.2))
    (Primrec.fst.comp Primrec.snd).to₂
    (dependencies_primrec.comp Primrec.snd).to₂
    (Primrec.option_some.comp rebuild_primrec).to₂
  · intro _ b b' hb
    exact dependencies_decrease b b' hb
  · intro L b
    exact congrArg some (rebuild_correct L b)

end FriedbergMuchnik

theorem solution :
    Primrec (fun p : List ℕ × (ℕ × (FriedbergMuchnik.Program × ℕ)) =>
      FriedbergMuchnik.oracleEvaln (fun n => if n ∈ p.1 then 1 else 0)
        p.2.1 p.2.2.1 p.2.2.2) := by
  have h := FriedbergMuchnik.evalCode_primrec.comp Primrec.fst
    ((Primrec.fst.comp Primrec.snd).pair
      ((FriedbergMuchnik.program_toCode_primrec.comp
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))).pair
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  apply h.of_eq
  intro p
  simp only [FriedbergMuchnik.evalCode]
  rw [show FriedbergMuchnik.Program.ofCode (FriedbergMuchnik.Program.toCode p.2.2.1) =
      p.2.2.1 from FriedbergMuchnik.Program.codeEquiv.left_inv p.2.2.1]
