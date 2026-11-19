-- Prove2me | solution 1 for DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T11:22:23.229282+00:00
-- url     : https://prove2.me/submissions/5fefbedb-4a9a-4d77-812f-0bb5342d7c19

import Definitions.Def_DecrAlmostLinearSSSP_RAMFoundation
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_1
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_2
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_3
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_4
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_5
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_6
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_7
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_8
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_normal_laws_1
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
open scoped ENNReal NNReal
attribute [local instance] Classical.propDecidable
theorem DecrAlmostLinearSSSP.Decremental.step_eq_effect : ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine)
  (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
  @Eq.{1} Bool c.halted Bool.false →
    @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
          DecrAlmostLinearSSSP.Decremental.Instruction
          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code c.pc)
        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins) →
      @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine (DecrAlmostLinearSSSP.Decremental.step p c)
        (DecrAlmostLinearSSSP.Decremental.instructionEffect ins
          {
            pc :=
              @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))),
            realReg := c.realReg, natReg := c.natReg, realMem := c.realMem, natMem := c.natMem, halted := c.halted,
            fault := c.fault,
            work :=
              @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) }) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_1.1.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.execute_add : ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (a b : Nat),
  @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
    (DecrAlmostLinearSSSP.Decremental.execute p c (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a b))
    (DecrAlmostLinearSSSP.Decremental.execute p (DecrAlmostLinearSSSP.Decremental.execute p c a) b) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_1.2.1.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.embedded_header_exact : ∀ (host : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (pc : Nat),
  @Eq.{1} Bool c.halted Bool.false →
    @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
            DecrAlmostLinearSSSP.Decremental.Instruction
            (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
            (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code c.pc)
          (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
            (DecrAlmostLinearSSSP.Decremental.Instruction.natural
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pc
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
        @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
            (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
              DecrAlmostLinearSSSP.Decremental.Instruction
              (fun as i =>
                @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
              (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
              (DecrAlmostLinearSSSP.Decremental.Instruction.nadd
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
          @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
            (DecrAlmostLinearSSSP.Decremental.execute host c
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (DecrAlmostLinearSSSP.Decremental.headerState c pc) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_1.2.1.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.execute_halted : ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine),
  @Eq.{1} Bool c.halted Bool.true →
    ∀ (t : Nat), @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine (DecrAlmostLinearSSSP.Decremental.execute p c t) c := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_1.2.2.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.execute_succ_front : ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (t : Nat),
  @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
    (DecrAlmostLinearSSSP.Decremental.execute p c
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (DecrAlmostLinearSSSP.Decremental.execute p (DecrAlmostLinearSSSP.Decremental.step p c) t) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_1.2.2.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.execution_valid_code : ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (t : Nat),
  @Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.execute p c t).fault Bool.false →
    ∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j t →
        @Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.execute p c j).halted Bool.false →
          ∃ ins,
            @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
              (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                DecrAlmostLinearSSSP.Decremental.Instruction
                (fun as i =>
                  @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code
                (DecrAlmostLinearSSSP.Decremental.execute p c j).pc)
              (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_1.2.2.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.terminating_prefix : ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (t : Nat),
  @Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.execute p c t).halted Bool.true →
    ∃ r,
      And (@LE.le.{0} Nat instLENat r t)
        (And
          (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine (DecrAlmostLinearSSSP.Decremental.execute p c r)
            (DecrAlmostLinearSSSP.Decremental.execute p c t))
          (@Eq.{1} Nat r
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (DecrAlmostLinearSSSP.Decremental.execute p c t).work c.work))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.1.1.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Structured.CodeAt.head : ∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {start : Nat} {ins : DecrAlmostLinearSSSP.Decremental.Instruction}
  {rest : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction},
  DecrAlmostLinearSSSP.Decremental.Structured.CodeAt p start
      (@List.cons.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins rest) →
    @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
      (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
        DecrAlmostLinearSSSP.Decremental.Instruction
        (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
        (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code start)
      (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.1.2.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.Structured.CodeAt.tail : ∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {start : Nat} {ins : DecrAlmostLinearSSSP.Decremental.Instruction}
  {rest : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction},
  DecrAlmostLinearSSSP.Decremental.Structured.CodeAt p start
      (@List.cons.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins rest) →
    DecrAlmostLinearSSSP.Decremental.Structured.CodeAt p
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      rest := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.1.2.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Structured.eval_natural : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (d q : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.natural d q) s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    { realReg := s.realReg, natReg := @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natReg d q,
      realMem := s.realMem, natMem := s.natMem } := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.1.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Structured.eval_cast : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (d a : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.cast d a) s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    {
      realReg :=
        @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realReg d
          (@Nat.cast.{0} Real Real.instNatCast (s.natReg a)),
      natReg := s.natReg, realMem := s.realMem, natMem := s.natMem } := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.1.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Structured.eval_nadd : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (d a b : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.nadd d a b) s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    { realReg := s.realReg,
      natReg :=
        @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natReg d
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (s.natReg a) (s.natReg b)),
      realMem := s.realMem, natMem := s.natMem } := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.1.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Structured.eval_load : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (d a : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.load d a) s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    { realReg := @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realReg d (s.realMem (s.natReg a)),
      natReg := s.natReg, realMem := s.realMem, natMem := s.natMem } := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.2.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.Structured.eval_store : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (a d : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.store a d) s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    { realReg := s.realReg, natReg := s.natReg,
      realMem := @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realMem (s.natReg a) (s.realReg d),
      natMem := s.natMem } := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.2.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Structured.eval_loadN : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (d a : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.loadN d a) s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    { realReg := s.realReg,
      natReg := @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natReg d (s.natMem (s.natReg a)),
      realMem := s.realMem, natMem := s.natMem } := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.2.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.Structured.eval_storeN : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (a d : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.storeN a d) s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    { realReg := s.realReg, natReg := s.natReg, realMem := s.realMem,
      natMem := @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natMem (s.natReg a) (s.natReg d) } := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.2.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.Structured.eval_sequence_atoms : ∀ (atoms : List.{0} DecrAlmostLinearSSSP.Decremental.Structured.Atom)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval
    (DecrAlmostLinearSSSP.Decremental.Structured.sequence
      (@List.map.{0, 0} DecrAlmostLinearSSSP.Decremental.Structured.Atom DecrAlmostLinearSSSP.Decremental.Structured.Cmd
        DecrAlmostLinearSSSP.Decremental.Structured.Cmd.atom atoms))
    s (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Structured.Atom atoms)
    (@List.foldl.{0, 0} DecrAlmostLinearSSSP.Decremental.Structured.Data
      DecrAlmostLinearSSSP.Decremental.Structured.Atom (fun t a => a.effect t) s atoms) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.2.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.Structured.atom_nat_frame : ∀ (a : DecrAlmostLinearSSSP.Decremental.Structured.Atom) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data)
  (k : Nat),
  Not (DecrAlmostLinearSSSP.Decremental.writesNat a.instruction k) → @Eq.{1} Nat ((a.effect s).natReg k) (s.natReg k) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.2.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.Structured.Eval.nat_frame : ∀ {cmd : DecrAlmostLinearSSSP.Decremental.Structured.Cmd} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {cost k : Nat},
  DecrAlmostLinearSSSP.Decremental.Structured.Eval cmd s cost t →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame cmd k → @Eq.{1} Nat (t.natReg k) (s.natReg k) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.2.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.Structured.Eval.real_frame : ∀ {cmd : DecrAlmostLinearSSSP.Decremental.Structured.Cmd} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {cost k : Nat},
  DecrAlmostLinearSSSP.Decremental.Structured.Eval cmd s cost t →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame cmd k → @Eq.{1} Real (t.realReg k) (s.realReg k) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.2.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Structured.Eval.deterministic : ∀ {cmd : DecrAlmostLinearSSSP.Decremental.Structured.Cmd} {s t u : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {a b : Nat},
  DecrAlmostLinearSSSP.Decremental.Structured.Eval cmd s a t →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval cmd s b u →
      And (@Eq.{1} Nat a b) (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Structured.Data t u) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_3.1.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Structured.Eval.no_memory : ∀ {cmd : DecrAlmostLinearSSSP.Decremental.Structured.Cmd} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {cost : Nat},
  DecrAlmostLinearSSSP.Decremental.Structured.Eval cmd s cost t →
    DecrAlmostLinearSSSP.Decremental.Structured.NoMemory cmd →
      And (@Eq.{1} (Nat → Real) t.realMem s.realMem) (@Eq.{1} (Nat → Nat) t.natMem s.natMem) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_3.1.2.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.TriePush.Result.nat_frame : ∀ {h : Nat} {tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h} {low : Nat}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  (r : @DecrAlmostLinearSSSP.Decremental.Exact.TriePush.Result h tree low s),
  ∀ k ∉ DecrAlmostLinearSSSP.Decremental.Exact.TriePush.registers,
    @Eq.{1} Nat ((@DecrAlmostLinearSSSP.Decremental.Exact.TriePush.Result.final h tree low s r).natReg k) (s.natReg k) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_3.2.1.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.TriePop.Result.nat_frame : ∀ {h : Nat} {tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  (r : @DecrAlmostLinearSSSP.Decremental.Exact.TriePop.Result h tree s),
  ∀ k ∉ DecrAlmostLinearSSSP.Decremental.Exact.TriePop.registers,
    @Eq.{1} Nat ((@DecrAlmostLinearSSSP.Decremental.Exact.TriePop.Result.final h tree s r).natReg k) (s.natReg k) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.1.1.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.input_vertex_positive : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) i.n := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.1.1.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.logarithm2_nonneg : ∀ {x : Real},
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) x →
    @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (DecrAlmostLinearSSSP.Decremental.logarithm2 x) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.1.2.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.Powers.Prefix.step : ∀ {bound base d : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Powers.Prefix bound base d s →
    DecrAlmostLinearSSSP.Decremental.Exact.Powers.Prefix bound base
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (DecrAlmostLinearSSSP.Decremental.Exact.Powers.advanced s) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.1.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.bankFactor_positive : ∀ (j : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
    (DecrAlmostLinearSSSP.Decremental.bankFactor j) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.1.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.guest_bank_ne_host : ∀ (base j a b : Nat),
  @Ne.{1} Nat (DecrAlmostLinearSSSP.Decremental.bankAddress base j a)
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.1.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.shadowReg_ne_meta : ∀ (j k : Nat),
  @LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) →
    @Ne.{1} Nat (DecrAlmostLinearSSSP.Decremental.shadowReg j) k := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.shadow_scalar : ∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    ∀ (ins tr : DecrAlmostLinearSSSP.Decremental.Instruction),
      @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (DecrAlmostLinearSSSP.Decremental.shadowScalarTranslation ins)
          (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction tr) →
        DecrAlmostLinearSSSP.Decremental.ShadowRep base F (DecrAlmostLinearSSSP.Decremental.instructionEffect tr c)
          (DecrAlmostLinearSSSP.Decremental.instructionEffect ins g) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.2.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.shadow_load : ∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    ∀ (d a : Nat),
      @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (g.natReg a))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
        DecrAlmostLinearSSSP.Decremental.ShadowRep base F
          (DecrAlmostLinearSSSP.Decremental.instructionEffect
            (DecrAlmostLinearSSSP.Decremental.Instruction.load (DecrAlmostLinearSSSP.Decremental.shadowReg d)
              (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
            c)
          (DecrAlmostLinearSSSP.Decremental.instructionEffect (DecrAlmostLinearSSSP.Decremental.Instruction.load d a) g) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.shadow_loadN : ∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    ∀ (d a : Nat),
      @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (g.natReg a))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
        DecrAlmostLinearSSSP.Decremental.ShadowRep base F
          (DecrAlmostLinearSSSP.Decremental.instructionEffect
            (DecrAlmostLinearSSSP.Decremental.Instruction.loadN (DecrAlmostLinearSSSP.Decremental.shadowReg d)
              (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
            c)
          (DecrAlmostLinearSSSP.Decremental.instructionEffect (DecrAlmostLinearSSSP.Decremental.Instruction.loadN d a)
            g) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.2.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.shadow_store : ∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) F →
      ∀ (a d : Nat),
        @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (g.natReg a))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
          DecrAlmostLinearSSSP.Decremental.ShadowRep base F
            (DecrAlmostLinearSSSP.Decremental.instructionEffect
              (DecrAlmostLinearSSSP.Decremental.Instruction.store
                (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                (DecrAlmostLinearSSSP.Decremental.shadowReg d))
              c)
            (DecrAlmostLinearSSSP.Decremental.instructionEffect (DecrAlmostLinearSSSP.Decremental.Instruction.store a d)
              g) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.1.1.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.shadow_storeN : ∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) F →
      ∀ (a d : Nat),
        @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (g.natReg a))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
          DecrAlmostLinearSSSP.Decremental.ShadowRep base F
            (DecrAlmostLinearSSSP.Decremental.instructionEffect
              (DecrAlmostLinearSSSP.Decremental.Instruction.storeN
                (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                (DecrAlmostLinearSSSP.Decremental.shadowReg d))
              c)
            (DecrAlmostLinearSSSP.Decremental.instructionEffect
              (DecrAlmostLinearSSSP.Decremental.Instruction.storeN a d) g) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.1.1.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.ShadowRep.pc_update : ∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    ∀ (pc : Nat),
      DecrAlmostLinearSSSP.Decremental.ShadowRep base F
        { pc := c.pc, realReg := c.realReg,
          natReg :=
            @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat c.natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) pc,
          realMem := c.realMem, natMem := c.natMem, halted := c.halted, fault := c.fault, work := c.work }
        { pc := pc, realReg := g.realReg, natReg := g.natReg, realMem := g.realMem, natMem := g.natMem,
          halted := g.halted, fault := g.fault, work := g.work } := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.1.1.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.ShadowRep.halt_update : ∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    DecrAlmostLinearSSSP.Decremental.ShadowRep base F
      { pc := c.pc, realReg := c.realReg,
        natReg :=
          @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat c.natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))),
        realMem := c.realMem, natMem := c.natMem, halted := c.halted, fault := c.fault, work := c.work }
      { pc := g.pc, realReg := g.realReg, natReg := g.natReg, realMem := g.realMem, natMem := g.natMem,
        halted := Bool.true, fault := g.fault, work := g.work } := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.1.1.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.shadow_nat_comparison : ∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) F →
      ∀ (a b : Nat),
        Iff
          (@LT.lt.{0} Nat instLTNat (c.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg a))
            (c.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg b)))
          (@LT.lt.{0} Nat instLTNat (g.natReg a) (g.natReg b)) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.1.1.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.shadow_real_comparison : ∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    ∀ (a b : Nat),
      Iff
        (@LT.lt.{0} Real Real.instLT (c.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg a))
          (c.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg b)))
        (@LT.lt.{0} Real Real.instLT (g.realReg a) (g.realReg b)) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.1.1.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.ShadowRep.data_machine : ∀ {B F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep B F c g →
    DecrAlmostLinearSSSP.Decremental.ShadowRep B F (DecrAlmostLinearSSSP.Decremental.Structured.data c).machine g := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.1.1.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.ShadowDataRep.effect : ∀ {B F : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine}
  (a : DecrAlmostLinearSSSP.Decremental.Structured.Atom),
  DecrAlmostLinearSSSP.Decremental.ShadowRep B F
      (DecrAlmostLinearSSSP.Decremental.instructionEffect a.instruction s.machine) g →
    DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F (a.effect s) g := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.1.1.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.ShadowDataRep.header : ∀ {B F : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F s g →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F
        { realReg := s.realReg,
          natReg :=
            @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
              (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natReg
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.pc
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))),
          realMem := s.realMem, natMem := s.natMem }
        {
          pc :=
            @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.pc
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))),
          realReg := g.realReg, natReg := g.natReg, realMem := g.realMem, natMem := g.natMem, halted := g.halted,
          fault := g.fault,
          work :=
            @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.work
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) } := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.1.1.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.eval_shadow_header : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (pc : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval
    ((DecrAlmostLinearSSSP.Decremental.Structured.natural (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pc
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))).seq
      (DecrAlmostLinearSSSP.Decremental.Structured.nadd (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    s (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    { realReg := s.realReg,
      natReg :=
        @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
          (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pc
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
      realMem := s.realMem, natMem := s.natMem } := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.1.1.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.eval_shadow_cast : ∀ {B F : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F s g →
    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) F →
      ∀ (d a : Nat),
        @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
            (@Nat.cast.{0} Real Real.instNatCast F) →
          ∃ t,
            And
              (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                ((DecrAlmostLinearSSSP.Decremental.Structured.cast (DecrAlmostLinearSSSP.Decremental.shadowReg d)
                      (DecrAlmostLinearSSSP.Decremental.shadowReg a)).seq
                  (DecrAlmostLinearSSSP.Decremental.Structured.div (DecrAlmostLinearSSSP.Decremental.shadowReg d)
                    (DecrAlmostLinearSSSP.Decremental.shadowReg d)
                    (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                s (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) t)
              (DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F t
                (DecrAlmostLinearSSSP.Decremental.instructionEffect
                  (DecrAlmostLinearSSSP.Decremental.Instruction.cast d a) g)) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.1.1.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.eval_shadow_address : ∀ {B F : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F s g →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) B →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) F →
        ∀ (a : Nat),
          ∃ t,
            And
              (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                (DecrAlmostLinearSSSP.Decremental.Structured.sequence
                  (@List.cons.{0} DecrAlmostLinearSSSP.Decremental.Structured.Cmd
                    (DecrAlmostLinearSSSP.Decremental.Structured.nadd
                      (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                      (DecrAlmostLinearSSSP.Decremental.shadowReg a) (DecrAlmostLinearSSSP.Decremental.shadowReg a))
                    (@List.cons.{0} DecrAlmostLinearSSSP.Decremental.Structured.Cmd
                      (DecrAlmostLinearSSSP.Decremental.Structured.nadd
                        (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                      (@List.cons.{0} DecrAlmostLinearSSSP.Decremental.Structured.Cmd
                        (DecrAlmostLinearSSSP.Decremental.Structured.nadd
                          (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                          (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                          (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                        (@List.nil.{0} DecrAlmostLinearSSSP.Decremental.Structured.Cmd)))))
                s (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) t)
              (And (DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F t g)
                (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (g.natReg a))
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.1.1.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.structuredConstant_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (d factor q : Nat),
  @Ne.{1} Nat factor d →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.structuredConstant d factor q) s
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) q
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      { realReg := s.realReg,
        natReg :=
          @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natReg d
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) q (s.natReg factor)),
        realMem := s.realMem, natMem := s.natMem } := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.1.1.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.eval_shadow_constant : ∀ {B F : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F s g →
    ∀ (d q : Nat),
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) F →
        ∃ t,
          And
            (DecrAlmostLinearSSSP.Decremental.Structured.Eval
              (DecrAlmostLinearSSSP.Decremental.structuredConstant (DecrAlmostLinearSSSP.Decremental.shadowReg d)
                (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))) q)
              s
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) q
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              t)
            (DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F t
              (DecrAlmostLinearSSSP.Decremental.instructionEffect
                (DecrAlmostLinearSSSP.Decremental.Instruction.natural d q) g)) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.1.1.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.repeatedAdd_nat_frame : ∀ (d factor q k : Nat),
  @Ne.{1} Nat d k →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.repeatedAdd d factor q) k := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.1.2.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.repeatedAdd_real_frame : ∀ (d factor q k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.repeatedAdd d factor q) k := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.1.2.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.append_report_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
      DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.appendStoreReport s
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
        (DecrAlmostLinearSSSP.Decremental.appendedReport s) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.1.2.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.append_report_rep : ∀ {B F : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F s g →
    (∀ (a : Nat),
        @Ne.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) →
      DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F (DecrAlmostLinearSSSP.Decremental.appendedReport s) g := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.1.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.append_report_log : ∀ (start : Nat) (reports : List.{0} Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.ReportLog start reports s →
    DecrAlmostLinearSSSP.Decremental.ReportLog start
      (@HAppend.hAppend.{0, 0, 0} (List.{0} Nat) (List.{0} Nat) (List.{0} Nat)
        (@instHAppendOfAppend.{0} (List.{0} Nat) (@List.instAppend.{0} Nat)) reports
        (@List.cons.{0} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
          (@List.nil.{0} Nat)))
      (DecrAlmostLinearSSSP.Decremental.appendedReport s) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.1.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.report_log_outside : ∀ (B bank start : Nat) (reports : List.{0} Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  (∃ r,
      @Eq.{1} Nat start
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
    DecrAlmostLinearSSSP.Decremental.ReportLog start reports s →
      ∀ (a : Nat),
        @Ne.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.1.2.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.InputCapture.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.InputCapture.code s
    (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19)))
    (DecrAlmostLinearSSSP.Decremental.InputCapture.result s) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.1.2.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.InputCapture.no_memory : DecrAlmostLinearSSSP.Decremental.Structured.NoMemory DecrAlmostLinearSSSP.Decremental.InputCapture.code := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.1.2.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.Powers.eval_code : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (base : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i s →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 234) (instOfNatNat (nat_lit 234)))) base →
      ∃ t,
        And
          (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.Powers.code s
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                (DecrAlmostLinearSSSP.Decremental.Exact.height
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) i.n i.W)))
              (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11))))
            t)
          (And
            (DecrAlmostLinearSSSP.Decremental.Exact.Powers.Prefix
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) i.n i.W) base
              (DecrAlmostLinearSSSP.Decremental.Exact.height
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) i.n i.W))
              t)
            (And (@Eq.{1} (Nat → Real) t.realMem s.realMem)
              (∀ (address : Nat),
                Or (@LT.lt.{0} Nat instLTNat address base)
                    (@LE.le.{0} Nat instLENat
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                        (DecrAlmostLinearSSSP.Decremental.Exact.height
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) i.n i.W)))
                      address) →
                  @Eq.{1} Nat (t.natMem address) (s.natMem address)))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.1.2.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.Powers.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 248) (instOfNatNat (nat_lit 248))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 250) (instOfNatNat (nat_lit 250))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 252) (instOfNatNat (nat_lit 252))) →
        DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.Powers.code k := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.2.1.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.Layout.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.Layout.code s
    (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
    (DecrAlmostLinearSSSP.Decremental.Exact.Layout.result s) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.2.1.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.Layout.no_memory : DecrAlmostLinearSSSP.Decremental.Structured.NoMemory DecrAlmostLinearSSSP.Decremental.Exact.Layout.code := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.2.1.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.Layout.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 224) (instOfNatNat (nat_lit 224))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 226) (instOfNatNat (nat_lit 226))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 228) (instOfNatNat (nat_lit 228))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 230) (instOfNatNat (nat_lit 230))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 232) (instOfNatNat (nat_lit 232))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 234) (instOfNatNat (nat_lit 234))) →
              DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.Layout.code k := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.2.1.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.Layout.real_frame : ∀ (k : Nat), DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Exact.Layout.code k := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.2.1.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.Clear.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 290) (instOfNatNat (nat_lit 290))) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.Clear.code k := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.2.1.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.Clear.real_frame : ∀ (k : Nat), DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Exact.Clear.code k := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.2.1.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.Clear.eval_code : ∀ (base length : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 290) (instOfNatNat (nat_lit 290)))) base →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 292) (instOfNatNat (nat_lit 292))))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base length) →
          ∃ t,
            And
              (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.Clear.code s
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) length)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                t)
              (And
                (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 290) (instOfNatNat (nat_lit 290))))
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base length))
                (And
                  (∀ (a : Nat),
                    @LE.le.{0} Nat instLENat base a →
                      @LT.lt.{0} Nat instLTNat a
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base length) →
                        @Eq.{1} Nat (t.natMem a) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (And (@Eq.{1} (Nat → Real) t.realMem s.realMem)
                    (∀ (a : Nat),
                      Or (@LT.lt.{0} Nat instLTNat a base)
                          (@LE.le.{0} Nat instLENat
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base length) a) →
                        @Eq.{1} Nat (t.natMem a) (s.natMem a))))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.2.1.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.Reachable.trans : ∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {u v w : Fin n},
  @DecrAlmostLinearSSSP.Decremental.Reachable n k g active u v →
    @DecrAlmostLinearSSSP.Decremental.Reachable n k g active v w →
      @DecrAlmostLinearSSSP.Decremental.Reachable n k g active u w := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.setup_nat_frame : ∀
  j ∉
    @Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 290) (instOfNatNat (nat_lit 290)))
      (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 292) (instOfNatNat (nat_lit 292)))
        (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 294) (instOfNatNat (nat_lit 294)))
          (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 296) (instOfNatNat (nat_lit 296)))
            (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 298) (instOfNatNat (nat_lit 298)))
              (@Singleton.singleton.{0, 0} Nat (Finset.{0} Nat) (@Finset.instSingleton.{0} Nat)
                (@OfNat.ofNat.{0} Nat (nat_lit 300) (instOfNatNat (nat_lit 300)))))))),
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.setup j := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_6.2.1.2.1.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.setup_eval : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 66) (instOfNatNat (nat_lit 66)))) i.n →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68)))) i.k →
          DecrAlmostLinearSSSP.Decremental.Exact.Layout.Image
              (DecrAlmostLinearSSSP.Decremental.Exact.Layout.addresses
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                i.n i.k)
              s →
            DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.Tape i s →
              ∃ t,
                And
                  (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                    DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.setup s
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) i.n)
                      (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                    t)
                  (And
                    (DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.Prefix i
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) t)
                    (And (@Eq.{1} (Nat → Real) t.realMem s.realMem)
                      (∀ (a : Nat),
                        Or
                            (@LT.lt.{0} Nat instLTNat a
                              (DecrAlmostLinearSSSP.Decremental.Exact.Layout.addresses
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  i.n i.k).heads)
                            (@LE.le.{0} Nat instLENat
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (DecrAlmostLinearSSSP.Decremental.Exact.Layout.addresses
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    i.n i.k).heads
                                i.n)
                              a) →
                          @Eq.{1} Nat (t.natMem a) (s.natMem a)))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_6.2.1.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.TentativeImage.update : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {l : DecrAlmostLinearSSSP.Decremental.Exact.Layout.Addresses}
  {tentative : Fin i.n → Option.{0} Nat} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.TentativeImage i l tentative s →
    ∀ (target : Fin i.n) (candidate : Nat),
      (∀ (v u : Fin i.n),
          @Ne.{1} Nat (@Fin.val i.n v)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) l.distances (@Fin.val i.n u))) →
        @Eq.{1} (Nat → Nat) t.natMem
            (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
              (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natMem (@Fin.val i.n target)
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) l.distances (@Fin.val i.n target))
              candidate) →
          @Eq.{1} (Nat → Real) t.realMem
              (@Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realMem (@Fin.val i.n target)
                (@Nat.cast.{0} Real Real.instNatCast candidate)) →
            DecrAlmostLinearSSSP.Decremental.Exact.TentativeImage i l
              (@Function.update.{1, 1} (Fin i.n) (fun a => Option.{0} Nat) (instDecidableEqFin i.n) tentative target
                (@Option.some.{0} Nat candidate))
              t := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_7.1.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State.step : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)},
  i.Valid →
    ∀ (q : DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State i deleted)
      (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
      @DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State.memory i deleted q s →
        (DecrAlmostLinearSSSP.Decremental.Structured.Test.natLess
                (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56)))
                (@OfNat.ofNat.{0} Nat (nat_lit 348) (instOfNatNat (nat_lit 348)))).holds
            s →
          ∃ next t cost,
            And
              (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.body s
                cost t)
              (And (@DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State.memory i deleted next t)
                (And
                  (@LT.lt.{0} Nat instLTNat
                    (@DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State.potential i deleted next)
                    (@DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State.potential i deleted q))
                  (@LE.le.{0} Nat instLENat
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cost
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 200) (instOfNatNat (nat_lit 200)))
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                        (@DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State.potential i deleted q)
                        (@DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State.potential i deleted next)))))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_8.1.1.2.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Ready.execute : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  i.Valid →
    DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Ready i deleted s →
      ∃ cost t q,
        And
          (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.code s cost
            t)
          (And
            (@LE.le.{0} Nat instLENat cost
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 600) (instOfNatNat (nat_lit 600)))
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n i.k)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
            (And (@DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State.memory i deleted q t)
              (And
                (@Eq.{1} (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n)))
                  (@DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State.queue i deleted q)
                  (@OfNat.ofNat.{0} (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))) (nat_lit 0)
                    (@Zero.toOfNat0.{0} (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n)))
                      (@Multiset.instZero.{0} (Prod.{0, 0} Nat (Fin i.n))))))
                (And (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Ready i deleted t)
                  (And
                    (@Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.stored t.machine (@Fin.val i.n i.source))
                      (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero)))
                    (And
                      (∀ (v : Fin i.n),
                        And
                          (@LE.le.{0} Nat instLENat (t.natMem (@Fin.val i.n v))
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          (@Eq.{1} Nat (t.natMem (@Fin.val i.n v))
                              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                            @LE.le.{0} Real Real.instLE
                              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                              (t.realMem (@Fin.val i.n v))))
                      (∀ (v : Fin i.n),
                        And
                          (@Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.stored t.machine (@Fin.val i.n v))
                            (i.dist deleted v))
                          (Iff
                            (@Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.stored t.machine (@Fin.val i.n v))
                              (@Top.top.{0} ENNReal ENNReal.instTop))
                            (Not
                              (@DecrAlmostLinearSSSP.Decremental.Reachable i.n i.k i.graph
                                (@DecrAlmostLinearSSSP.Decremental.live i.k deleted) i.source v)))))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_8.2.1.1.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Ends.deterministic : ∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {c d e : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.Ends p c d →
    DecrAlmostLinearSSSP.Decremental.Ends p c e → @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine d e := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_8.2.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.ScaledCeiling.routine_ends : ∀ (c : DecrAlmostLinearSSSP.Decremental.Machine) (N : Nat),
  @Eq.{1} Nat c.pc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Bool c.halted Bool.false →
      @Eq.{1} Bool c.fault Bool.false →
        @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (c.realReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
          @LE.le.{0} Real Real.instLE (c.realReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                N) →
            ∃ d,
              And
                (DecrAlmostLinearSSSP.Decremental.Ends
                  (DecrAlmostLinearSSSP.Decremental.Structured.program
                    DecrAlmostLinearSSSP.Decremental.ScaledCeiling.routine
                    DecrAlmostLinearSSSP.Decremental.Structured.Cmd.skip)
                  c d)
                (And
                  (@Eq.{1} Nat (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                      (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
                        (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing)
                        (c.realReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                  (@LE.le.{0} Nat instLENat d.work
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16))) N))
                      (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_1.1.2.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.source_constant_bound : ∀ (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
  @Membership.mem.{0, 0} DecrAlmostLinearSSSP.Decremental.Instruction
      (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
      (@List.instMembership.{0} DecrAlmostLinearSSSP.Decremental.Instruction) code ins →
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (DecrAlmostLinearSSSP.Decremental.naturalConstant ins)
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
      (DecrAlmostLinearSSSP.Decremental.shadowWidth code) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_1.1.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.shadowWidth_positive : ∀ (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
    (DecrAlmostLinearSSSP.Decremental.shadowWidth code) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_1.1.2.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.ShadowRep.header : ∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    ∀ (host : DecrAlmostLinearSSSP.Decremental.Program),
      @Eq.{1} Bool c.halted Bool.false →
        @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
          @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
              (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                DecrAlmostLinearSSSP.Decremental.Instruction
                (fun as i =>
                  @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code c.pc)
              (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                (DecrAlmostLinearSSSP.Decremental.Instruction.natural
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.pc
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
            @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                  DecrAlmostLinearSSSP.Decremental.Instruction
                  (fun as i =>
                    @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                  (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                  (DecrAlmostLinearSSSP.Decremental.Instruction.nadd
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
              DecrAlmostLinearSSSP.Decremental.ShadowRep base F
                (DecrAlmostLinearSSSP.Decremental.execute host c
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                {
                  pc :=
                    @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.pc
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))),
                  realReg := g.realReg, natReg := g.natReg, realMem := g.realMem, natMem := g.natMem,
                  halted := g.halted, fault := g.fault,
                  work :=
                    @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.work
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) } := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_1.1.2.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.shadow_address_run : ∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    ∀ (host : DecrAlmostLinearSSSP.Decremental.Program) (a : Nat),
      @Eq.{1} Bool c.halted Bool.false →
        @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) base →
          @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) F →
            @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                  DecrAlmostLinearSSSP.Decremental.Instruction
                  (fun as i =>
                    @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                  (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code c.pc)
                (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                  (DecrAlmostLinearSSSP.Decremental.Instruction.nadd
                    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                    (DecrAlmostLinearSSSP.Decremental.shadowReg a) (DecrAlmostLinearSSSP.Decremental.shadowReg a))) →
              @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                  (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                    DecrAlmostLinearSSSP.Decremental.Instruction
                    (fun as i =>
                      @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                    (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                    (DecrAlmostLinearSSSP.Decremental.Instruction.nadd
                      (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                      (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) →
                @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                    (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                      DecrAlmostLinearSSSP.Decremental.Instruction
                      (fun as i =>
                        @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                      (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                      (DecrAlmostLinearSSSP.Decremental.Instruction.nadd
                        (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))) →
                  ∃ d,
                    And
                      (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                        (DecrAlmostLinearSSSP.Decremental.execute host c
                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                        d)
                      (And (DecrAlmostLinearSSSP.Decremental.ShadowRep base F d g)
                        (And
                          (@Eq.{1} Nat (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (g.natReg a))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                          (And
                            (@Eq.{1} Nat d.pc
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                            (And
                              (@Eq.{1} Nat d.work
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                              (And (@Eq.{1} Bool d.halted Bool.false)
                                (And
                                  (@Eq.{1} Nat (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                    (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                                  (And
                                    (@Eq.{1} Nat
                                      (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                      (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                    (And
                                      (@Eq.{1} Nat
                                        (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                                        (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                                      (@Eq.{1} Real
                                        (d.realReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                                        (c.realReg
                                          (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))))))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_1.2.1.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.shadow_macro : ∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    ∀ (host : DecrAlmostLinearSSSP.Decremental.Program) (width offset returnPC : Nat),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) width →
        @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) F →
          ∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
            @LE.le.{0} Nat instLENat
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (DecrAlmostLinearSSSP.Decremental.naturalConstant ins)
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                width →
              @Eq.{1} Bool c.halted Bool.false →
                @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                  @Eq.{1} Bool g.halted Bool.false →
                    @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) base →
                      @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) F →
                        @Eq.{1} Real (c.realReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                            (@Nat.cast.{0} Real Real.instNatCast F) →
                          @Eq.{1} Nat c.pc
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) width g.pc)) →
                            (∀ (slot : Nat),
                                @LT.lt.{0} Nat instLTNat slot width →
                                  @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                                    (@GetElem?.getElem?.{0, 0, 0}
                                      (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                                      DecrAlmostLinearSSSP.Decremental.Instruction
                                      (fun as i =>
                                        @LT.lt.{0} Nat instLTNat i
                                          (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                                      (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                                      host.code
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc slot))
                                    (@GetElem?.getElem?.{0, 0, 0}
                                      (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                                      DecrAlmostLinearSSSP.Decremental.Instruction
                                      (fun as i =>
                                        @LT.lt.{0} Nat instLTNat i
                                          (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                                      (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                                      (DecrAlmostLinearSSSP.Decremental.shadowBlock width offset returnPC g.pc ins)
                                      slot)) →
                              ∃ steps d,
                                And (@LE.le.{0} Nat instLENat steps width)
                                  (And
                                    (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                                      (DecrAlmostLinearSSSP.Decremental.execute host c steps) d)
                                    (And
                                      (DecrAlmostLinearSSSP.Decremental.ShadowRep base F d
                                        (DecrAlmostLinearSSSP.Decremental.instructionEffect ins
                                          {
                                            pc :=
                                              @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.pc
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))),
                                            realReg := g.realReg, natReg := g.natReg, realMem := g.realMem,
                                            natMem := g.natMem, halted := g.halted, fault := g.fault,
                                            work :=
                                              @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.work
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) }))
                                      (And
                                        (@Eq.{1} Nat d.pc
                                          (DecrAlmostLinearSSSP.Decremental.shadowDestination width offset returnPC
                                            (DecrAlmostLinearSSSP.Decremental.instructionEffect ins
                                              {
                                                pc :=
                                                  @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.pc
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))),
                                                realReg := g.realReg, natReg := g.natReg, realMem := g.realMem,
                                                natMem := g.natMem, halted := g.halted, fault := g.fault,
                                                work :=
                                                  @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.work
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) })))
                                        (And
                                          (@Eq.{1} Nat d.work
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                                              steps))
                                          (And (@Eq.{1} Bool d.halted Bool.false)
                                            (And
                                              (@Eq.{1} Nat
                                                (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                (c.natReg
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                                              (And
                                                (@Eq.{1} Nat
                                                  (d.natReg
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                                  (c.natReg
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                (And
                                                  (@Eq.{1} Nat
                                                    (d.natReg
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                                                    (c.natReg
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                                                  (And
                                                    (@Eq.{1} Real
                                                      (d.realReg
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                                                      (c.realReg
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                                                    (@Eq.{1} Nat steps
                                                      (DecrAlmostLinearSSSP.Decremental.shadowSteps ins g))))))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_1.2.2.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.shadowSteps_bound : ∀ (width : Nat) (ins : DecrAlmostLinearSSSP.Decremental.Instruction) (g : DecrAlmostLinearSSSP.Decremental.Machine),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) width →
    @LE.le.{0} Nat instLENat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (DecrAlmostLinearSSSP.Decremental.naturalConstant ins)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        width →
      @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.shadowSteps ins g) width := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_1.2.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.shadow_nonbranch_prefix : ∀ (host : DecrAlmostLinearSSSP.Decremental.Program) (c g : DecrAlmostLinearSSSP.Decremental.Machine)
  (width offset returnPC : Nat) (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) width →
    @LE.le.{0} Nat instLENat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (DecrAlmostLinearSSSP.Decremental.naturalConstant ins)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        width →
      Not (DecrAlmostLinearSSSP.Decremental.IsBranch ins) →
        @Eq.{1} Bool c.halted Bool.false →
          (∀ (slot : Nat),
              @LT.lt.{0} Nat instLTNat slot width →
                @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                  (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                    DecrAlmostLinearSSSP.Decremental.Instruction
                    (fun as i =>
                      @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                    (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc slot))
                  (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                    DecrAlmostLinearSSSP.Decremental.Instruction
                    (fun as i =>
                      @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                    (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                    (DecrAlmostLinearSSSP.Decremental.shadowBlock width offset returnPC g.pc ins) slot)) →
            ∀ (j : Nat),
              @LT.lt.{0} Nat instLTNat j (DecrAlmostLinearSSSP.Decremental.shadowSteps ins g) →
                And
                  (@Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.execute host c j).pc
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc j))
                  (And (@Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.execute host c j).halted Bool.false)
                    (@Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.execute host c j).work
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work j))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_1.2.2.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.shadow_residence : ∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    ∀ (host : DecrAlmostLinearSSSP.Decremental.Program) (width offset returnPC : Nat),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) width →
        @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) F →
          ∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
            @LE.le.{0} Nat instLENat
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (DecrAlmostLinearSSSP.Decremental.naturalConstant ins)
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                width →
              @Eq.{1} Bool c.halted Bool.false →
                @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                  @Eq.{1} Nat c.pc
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) width g.pc)) →
                    (∀ (slot : Nat),
                        @LT.lt.{0} Nat instLTNat slot width →
                          @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                            (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                              DecrAlmostLinearSSSP.Decremental.Instruction
                              (fun as i =>
                                @LT.lt.{0} Nat instLTNat i
                                  (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                              (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc slot))
                            (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                              DecrAlmostLinearSSSP.Decremental.Instruction
                              (fun as i =>
                                @LT.lt.{0} Nat instLTNat i
                                  (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                              (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                              (DecrAlmostLinearSSSP.Decremental.shadowBlock width offset returnPC g.pc ins) slot)) →
                      ∀ (j : Nat),
                        @LT.lt.{0} Nat instLTNat j (DecrAlmostLinearSSSP.Decremental.shadowSteps ins g) →
                          ∃ slot,
                            And (@LT.lt.{0} Nat instLTNat slot width)
                              (@Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.execute host c j).pc
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc slot)) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_1.2.2.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.shadowBlock_memory_origin : ∀ (width offset returnPC pc : Nat) (ins tr : DecrAlmostLinearSSSP.Decremental.Instruction),
  @Membership.mem.{0, 0} DecrAlmostLinearSSSP.Decremental.Instruction
      (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
      (@List.instMembership.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
      (DecrAlmostLinearSSSP.Decremental.shadowBlock width offset returnPC pc ins) tr →
    DecrAlmostLinearSSSP.Decremental.ModifiesMemory tr → DecrAlmostLinearSSSP.Decremental.ModifiesMemory ins := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_1.2.2.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.shadowBlock_store_slot : ∀ (width offset returnPC pc a d slot : Nat),
  @LT.lt.{0} Nat instLTNat slot (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))) →
    ∀ (tr : DecrAlmostLinearSSSP.Decremental.Instruction),
      @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
            DecrAlmostLinearSSSP.Decremental.Instruction
            (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
            (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
            (DecrAlmostLinearSSSP.Decremental.shadowBlock width offset returnPC pc
              (DecrAlmostLinearSSSP.Decremental.Instruction.store a d))
            slot)
          (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction tr) →
        DecrAlmostLinearSSSP.Decremental.ModifiesMemory tr →
          And (@Eq.{1} Nat slot (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
            (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Instruction tr
              (DecrAlmostLinearSSSP.Decremental.Instruction.store
                (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                (DecrAlmostLinearSSSP.Decremental.shadowReg d))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_1.2.2.2.1.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.shadowBlock_storeN_slot : ∀ (width offset returnPC pc a d slot : Nat),
  @LT.lt.{0} Nat instLTNat slot (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))) →
    ∀ (tr : DecrAlmostLinearSSSP.Decremental.Instruction),
      @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
            DecrAlmostLinearSSSP.Decremental.Instruction
            (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
            (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
            (DecrAlmostLinearSSSP.Decremental.shadowBlock width offset returnPC pc
              (DecrAlmostLinearSSSP.Decremental.Instruction.storeN a d))
            slot)
          (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction tr) →
        DecrAlmostLinearSSSP.Decremental.ModifiesMemory tr →
          And (@Eq.{1} Nat slot (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
            (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Instruction tr
              (DecrAlmostLinearSSSP.Decremental.Instruction.storeN
                (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                (DecrAlmostLinearSSSP.Decremental.shadowReg d))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_1.2.2.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.no_address_write_of_no_memory : ∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction) (c : DecrAlmostLinearSSSP.Decremental.Machine) (address : Nat),
  Not (DecrAlmostLinearSSSP.Decremental.ModifiesMemory ins) →
    Not (DecrAlmostLinearSSSP.Decremental.WritesAddress ins c address) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_1.2.2.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.execute_address_frame : ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (t address : Nat),
  (∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j t →
        ∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
          @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
              (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                DecrAlmostLinearSSSP.Decremental.Instruction
                (fun as i =>
                  @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code
                (DecrAlmostLinearSSSP.Decremental.execute p c j).pc)
              (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins) →
            Not
              (DecrAlmostLinearSSSP.Decremental.WritesAddress ins (DecrAlmostLinearSSSP.Decremental.execute p c j)
                address)) →
    And (@Eq.{1} Real ((DecrAlmostLinearSSSP.Decremental.execute p c t).realMem address) (c.realMem address))
      (@Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.execute p c t).natMem address) (c.natMem address)) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_1.2.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.memory_of_write : ∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction) (c : DecrAlmostLinearSSSP.Decremental.Machine) (address : Nat),
  DecrAlmostLinearSSSP.Decremental.WritesAddress ins c address → DecrAlmostLinearSSSP.Decremental.ModifiesMemory ins := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_1.2.2.2.2.2.2.2
section s0
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s0
section s1
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s1
section s2
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s2
section s3
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s3
section s4
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s4
section s5
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s5
section s6
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s6
section s7
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s7
section s8
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s8
section s9
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental
end s9
section s10
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s10
section s11
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s11
section s12
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s12
section s13
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s13
section s14
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s14
section s15
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental.Structured
end s15
section s16
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end s16
section s17
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end s17
section s18
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end s18
section s19
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s19
section s20
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s20
section s21
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end s21
section s22
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end s22
section s23
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end s23
section s24
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end s24
section s25
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s25
section s26
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end s26
section s27
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s27
section s28
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s28
section s29
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s29
section s30
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s30
section s31
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s31
section s32
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end s32
section s33
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end s33
section s34
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end s34
section s35
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.InputCapture
open Structured
end DecrAlmostLinearSSSP.Decremental.InputCapture
end s35
section s36
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.InputCapture
open Structured
end DecrAlmostLinearSSSP.Decremental.InputCapture
end s36
section s37
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end s37
section s38
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.ScaledCeiling
open Structured
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental.ScaledCeiling
end s38
section s39
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.ScaledCeiling
open Structured
end DecrAlmostLinearSSSP.Decremental.ScaledCeiling
end s39
section s40
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.ScaledCeiling
open Structured
end DecrAlmostLinearSSSP.Decremental.ScaledCeiling
end s40
section s41
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.ScaledCeiling
open Structured
end DecrAlmostLinearSSSP.Decremental.ScaledCeiling
end s41
section s42
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s42
section s43
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s43
section s44
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s44
section s45
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s45
section s46
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s46
section s47
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s47
section s48
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental
end s48
section s49
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s49
section s50
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s50
section s51
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s51
section s52
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s52
section s53
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s53
section s54
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental
end s54
section s55
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s55
section s56
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s56
section s57
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental
end s57
section s58
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental
end s58
section s59
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s59
section s60
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s60
section s61
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s61
section s62
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma shadow_prefix_address {base F : ℕ} {c g : Machine} (hr : ShadowRep base F c g)
    (host : Program) (a : ℕ) (hh : c.halted = false) (hone : c.natReg 1 = 1)
    (hbase : c.natReg 0 = base) (hfactor : c.natReg 7 = F)
    (h0 : host.code[c.pc]? = some (.natural 2 (g.pc+1)))
    (h1 : host.code[c.pc+1]? = some (.nadd 3 3 1))
    (h2 : host.code[c.pc+2]? = some (.nadd 6 (shadowReg a) (shadowReg a)))
    (h3 : host.code[c.pc+3]? = some (.nadd 6 6 0))
    (h4 : host.code[c.pc+4]? = some (.nadd 6 6 7)) :
    (execute host c 5).natReg 6 = base + F*(2*g.natReg a+1) := by
  let b := headerState c g.pc
  have hb : execute host c 2 = b := embedded_header_exact host c g.pc hh hone h0 h1
  have hbrep : ShadowRep base F b {g with pc := g.pc+1,work := g.work+1} := by rw [← hb];exact hr.header host hh hone h0 h1
  obtain ⟨t,ht,_,ha,_,_,_,_,_,_,_⟩ := shadow_address_run hbrep host a hh hbase hfactor h2
    (by simpa [b,headerState,Nat.add_assoc] using h3)
    (by simpa [b,headerState,Nat.add_assoc] using h4)
  rw [show 5 = 2+3 by omega,execute_add,hb,ht]
  exact ha
lemma shadow_outside_memory {base F : ℕ} {c g : Machine} (hr : ShadowRep base F c g)
    (host : Program) (width offset returnPC : ℕ) (hw : 8 ≤ width)
    (hF : 0 < F) (ins : Instruction) (hc : naturalConstant ins+4 ≤ width)
    (hh : c.halted = false) (hone : c.natReg 1 = 1)
    (hbase : c.natReg 0 = base) (hfactor : c.natReg 7 = F)
    (hpos : c.pc = offset+width*g.pc)
    (hcode : ∀ slot < width,host.code[c.pc+slot]? = (shadowBlock width offset returnPC g.pc ins)[slot]?)
    (address : ℕ) (ha : OutsideBank base F address) :
    (execute host c (shadowSteps ins g)).realMem address = c.realMem address ∧
      (execute host c (shadowSteps ins g)).natMem address = c.natMem address := by
  classical
  apply execute_address_frame
  intro j hj tr htr
  by_cases hstore : ModifiesMemory ins
  · cases ins with
    | store a d =>
      have hpc := (shadow_nonbranch_prefix host c g width offset returnPC (.store a d) hw hc (by simp [IsBranch]) hh hcode j hj).1
      have hlookup : (shadowBlock width offset returnPC g.pc (.store a d))[j]? = some tr := by
        rw [hpc] at htr
        exact (hcode j (lt_of_lt_of_le hj (shadowSteps_bound width (.store a d) g hw hc))).symm.trans htr
      intro hwrite
      obtain ⟨hj5,htr5⟩ := shadowBlock_store_slot width offset returnPC g.pc a d j hj tr hlookup (memory_of_write tr _ address hwrite)
      subst j
      subst tr
      have h0 : host.code[c.pc]? = some (.natural 2 (g.pc+1)) := by simpa [shadowBlock] using hcode 0 (by omega)
      have h1 : host.code[c.pc+1]? = some (.nadd 3 3 1) := by simpa [shadowBlock] using hcode 1 (by omega)
      have h2 : host.code[c.pc+2]? = some (.nadd 6 (shadowReg a) (shadowReg a)) := by simpa [shadowBlock] using hcode 2 (by omega)
      have h3 : host.code[c.pc+3]? = some (.nadd 6 6 0) := by simpa [shadowBlock] using hcode 3 (by omega)
      have h4 : host.code[c.pc+4]? = some (.nadd 6 6 7) := by simpa [shadowBlock] using hcode 4 (by omega)
      have haddr := shadow_prefix_address hr host a hh hone hbase hfactor h0 h1 h2 h3 h4
      exact ha (g.natReg a) ((show (execute host c 5).natReg 6 = address from hwrite).symm.trans haddr)
    | storeN a d =>
      have hpc := (shadow_nonbranch_prefix host c g width offset returnPC (.storeN a d) hw hc (by simp [IsBranch]) hh hcode j hj).1
      have hlookup : (shadowBlock width offset returnPC g.pc (.storeN a d))[j]? = some tr := by
        rw [hpc] at htr
        exact (hcode j (lt_of_lt_of_le hj (shadowSteps_bound width (.storeN a d) g hw hc))).symm.trans htr
      intro hwrite
      obtain ⟨hj5,htr5⟩ := shadowBlock_storeN_slot width offset returnPC g.pc a d j hj tr hlookup (memory_of_write tr _ address hwrite)
      subst j
      subst tr
      have h0 : host.code[c.pc]? = some (.natural 2 (g.pc+1)) := by simpa [shadowBlock] using hcode 0 (by omega)
      have h1 : host.code[c.pc+1]? = some (.nadd 3 3 1) := by simpa [shadowBlock] using hcode 1 (by omega)
      have h2 : host.code[c.pc+2]? = some (.nadd 6 (shadowReg a) (shadowReg a)) := by simpa [shadowBlock] using hcode 2 (by omega)
      have h3 : host.code[c.pc+3]? = some (.nadd 6 6 0) := by simpa [shadowBlock] using hcode 3 (by omega)
      have h4 : host.code[c.pc+4]? = some (.nadd 6 6 7) := by simpa [shadowBlock] using hcode 4 (by omega)
      have haddr := shadow_prefix_address hr host a hh hone hbase hfactor h0 h1 h2 h3 h4
      exact ha (g.natReg a) ((show (execute host c 5).natReg 6 = address from hwrite).symm.trans haddr)
    | _ => simp [ModifiesMemory] at hstore
  · obtain ⟨slot,hslot,hpc⟩ := shadow_residence hr host width offset returnPC hw hF ins hc hh hone hpos hcode j hj
    have hlookup : (shadowBlock width offset returnPC g.pc ins)[slot]? = some tr := by
      rw [hpc] at htr
      exact (hcode slot hslot).symm.trans htr
    exact no_address_write_of_no_memory tr _ address (fun hm => hstore (shadowBlock_memory_origin width offset returnPC g.pc ins tr (List.mem_of_getElem? hlookup) hm))
end DecrAlmostLinearSSSP.Decremental
end s62
section s63
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma PreservesOutside.refl (base F : ℕ) (c : Machine) : PreservesOutside base F c c := fun _ _ => ⟨rfl,rfl⟩
lemma PreservesOutside.trans {base F : ℕ} {c d e : Machine}
    (hcd : PreservesOutside base F c d) (hde : PreservesOutside base F d e) : PreservesOutside base F c e := by
  intro address ha
  exact ⟨(hde address ha).1.trans (hcd address ha).1,(hde address ha).2.trans (hcd address ha).2⟩
lemma shadow_single_step_framed {base F : ℕ} {c g : Machine} (hr : ShadowRep base F c g)
    (host guest : Program) (width offset returnPC : ℕ) (hw : 8 ≤ width)
    (hc : ∀ ins ∈ guest.code, naturalConstant ins + 4 ≤ width)
    (hcode : ShadowEmbedsCode host guest width offset returnPC) (hF : 0 < F)
    (hh : c.halted = false) (hone : c.natReg 1 = 1) (hgh : g.halted = false)
    (hbase : c.natReg 0 = base) (hfactor : c.natReg 7 = F) (hrealFactor : c.realReg 7 = (F : ℝ))
    (hpos : c.pc = shadowDestination width offset returnPC g)
    (ins : Instruction) (hins : guest.code[g.pc]? = some ins) :
    ∃ (steps : ℕ) (d : Machine), steps ≤ width ∧ execute host c steps = d ∧
      ShadowRep base F d (step guest g) ∧ d.pc = shadowDestination width offset returnPC (step guest g) ∧
      d.work = c.work + steps ∧ d.halted = false ∧
      d.natReg 0 = c.natReg 0 ∧ d.natReg 1 = c.natReg 1 ∧
      d.natReg 7 = c.natReg 7 ∧ d.realReg 7 = c.realReg 7 ∧ PreservesOutside base F c d := by
  have hp : c.pc = offset+width*g.pc := by simpa [shadowDestination,hgh] using hpos
  have hconst := hc ins (List.mem_of_getElem? hins)
  have hslots : ∀ slot < width, host.code[c.pc+slot]? = (shadowBlock width offset returnPC g.pc ins)[slot]? :=
    fun slot hslot => by rw [hp];exact hcode _ _ hins slot hslot
  obtain ⟨steps,d,hs,hd,hrep,hdpc,hdw,hdh,hd0,hd1,hd7,hdr7,hsteps⟩ :=
    shadow_macro hr host width offset returnPC hw hF ins hconst hh hone hgh hbase hfactor hrealFactor hp hslots
  have hmem : PreservesOutside base F c d := by
    intro address ha
    have hm := shadow_outside_memory hr host width offset returnPC hw hF ins hconst hh hone hbase hfactor hp hslots address ha
    rw [← hsteps,hd] at hm
    exact hm
  rw [← step_eq_effect guest g ins hgh hins] at hrep hdpc
  exact ⟨steps,d,hs,hd,hrep,hdpc,hdw,hdh,hd0,hd1,hd7,hdr7,hmem⟩
lemma shadow_framed_execution (host guest : Program) (width offset returnPC : ℕ)
    (hw : 8 ≤ width) (hc : ∀ ins ∈ guest.code, naturalConstant ins + 4 ≤ width)
    (hcode : ShadowEmbedsCode host guest width offset returnPC)
    (base F : ℕ) (hF : 0 < F) (t : ℕ) (c g : Machine) (hr : ShadowRep base F c g)
    (hh : c.halted = false) (hone : c.natReg 1 = 1)
    (hbase : c.natReg 0 = base) (hfactor : c.natReg 7 = F) (hrealFactor : c.realReg 7 = (F : ℝ))
    (hpos : c.pc = shadowDestination width offset returnPC g)
    (hvalid : ∀ j < t, (execute guest g j).halted = false → ∃ ins, guest.code[(execute guest g j).pc]? = some ins) :
    ∃ (steps : ℕ) (d : Machine), steps ≤ width*t ∧ execute host c steps = d ∧
      ShadowRep base F d (execute guest g t) ∧ d.pc = shadowDestination width offset returnPC (execute guest g t) ∧
      d.work = c.work+steps ∧ d.halted = false ∧
      d.natReg 0 = c.natReg 0 ∧ d.natReg 1 = c.natReg 1 ∧
      d.natReg 7 = c.natReg 7 ∧ d.realReg 7 = c.realReg 7 ∧ PreservesOutside base F c d := by
  induction t generalizing c g with
  | zero => exact ⟨0,c,le_rfl,rfl,hr,hpos,rfl,hh,rfl,rfl,rfl,rfl,PreservesOutside.refl base F c⟩
  | succ t ih =>
    by_cases hgh : g.halted = true
    · refine ⟨0,c,Nat.zero_le _,rfl,?_,?_,rfl,hh,rfl,rfl,rfl,rfl,PreservesOutside.refl base F c⟩
      · rwa [execute_halted guest g hgh]
      · rwa [execute_halted guest g hgh]
    · have hghfalse := Bool.eq_false_iff.mpr hgh
      obtain ⟨ins,hins⟩ := hvalid 0 (by omega) hghfalse
      obtain ⟨s,b,hs,hb,hbrep,hbpc,hbw,hbh,hb0,hb1,hb7,hbr7,hbmem⟩ :=
        shadow_single_step_framed hr host guest width offset returnPC hw hc hcode hF hh hone hghfalse hbase hfactor hrealFactor hpos ins hins
      have hbvalid : ∀ j < t, (execute guest (step guest g) j).halted = false →
          ∃ ins,guest.code[(execute guest (step guest g) j).pc]? = some ins := by
        intro j hj hhj
        rw [← execute_succ_front] at hhj ⊢
        exact hvalid (j+1) (by omega) hhj
      obtain ⟨r,d,hrcost,hd,hdrep,hdpc,hdw,hdh,hd0,hd1,hd7,hdr7,hdmem⟩ :=
        ih b (step guest g) hbrep hbh (hb1.trans hone) (hb0.trans hbase) (hb7.trans hfactor) (hbr7.trans hrealFactor) hbpc hbvalid
      refine ⟨s+r,d,?_,?_,?_,?_,?_,hdh,hd0.trans hb0,hd1.trans hb1,hd7.trans hb7,hdr7.trans hbr7,hbmem.trans hdmem⟩
      · rw [Nat.mul_succ];omega
      · rw [execute_add,hb,hd]
      · rwa [execute_succ_front]
      · rwa [execute_succ_front]
      · omega
lemma shadow_framed_ends (host guest : Program) (offset returnPC : ℕ)
    (hcode : ShadowEmbedsCode host guest (shadowWidth guest.code) offset returnPC)
    (base F : ℕ) (hF : 0 < F) (c g final : Machine) (hr : ShadowRep base F c g)
    (hh : c.halted = false) (hone : c.natReg 1 = 1)
    (hbase : c.natReg 0 = base) (hfactor : c.natReg 7 = F) (hrealFactor : c.realReg 7 = (F : ℝ))
    (hpos : c.pc = shadowDestination (shadowWidth guest.code) offset returnPC g)
    (he : Ends guest g final) :
    ∃ (steps : ℕ) (d : Machine), execute host c steps = d ∧ ShadowRep base F d final ∧
      d.pc = returnPC ∧ d.work ≤ c.work+shadowWidth guest.code*(final.work-g.work) ∧
      d.halted = false ∧ d.natReg 0 = c.natReg 0 ∧ d.natReg 1 = c.natReg 1 ∧
      d.natReg 7 = c.natReg 7 ∧ d.realReg 7 = c.realReg 7 ∧ PreservesOutside base F c d := by
  obtain ⟨t,ht,hhalt,hfault⟩ := he
  have hhalt' : (execute guest g t).halted = true := by rwa [ht]
  obtain ⟨r,_,hrun,hrwork⟩ := terminating_prefix guest g t hhalt'
  have hrfinal : execute guest g r = final := hrun.trans ht
  have hrfault : (execute guest g r).fault = false := by rwa [hrfinal]
  obtain ⟨s,d,hs,hd,hdrep,hdpc,hdw,hdh,hd0,hd1,hd7,hdr7,hdmem⟩ :=
    shadow_framed_execution host guest (shadowWidth guest.code) offset returnPC (shadowWidth_positive guest.code)
      (source_constant_bound guest.code) hcode base F hF r c g hr hh hone hbase hfactor hrealFactor hpos
      (execution_valid_code guest g r hrfault)
  refine ⟨s,d,hd,?_,?_,?_,hdh,hd0,hd1,hd7,hdr7,hdmem⟩
  · rwa [hrfinal] at hdrep
  · rw [hdpc,hrfinal];simp [shadowDestination,hhalt]
  · rw [ht] at hrwork
    rw [hdw,← hrwork]
    omega
end DecrAlmostLinearSSSP.Decremental
end s63
section s64
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.ScaledCeiling
open Structured
lemma ceilingProgram_width : shadowWidth ceilingProgram.code = 9 := by decide
lemma shadow_ceiling_call (host : Program) (offset returnPC base N : ℕ) (c g : Machine)
    (hcode : ShadowEmbedsCode host ceilingProgram (shadowWidth ceilingProgram.code) offset returnPC)
    (hr : ShadowRep base 2 c g)
    (hh : c.halted = false) (hone : c.natReg 1 = 1)
    (hbase : c.natReg 0 = base) (hfactor : c.natReg 7 = 2) (hrealFactor : c.realReg 7 = 2)
    (hpos : c.pc = offset) (hgp : g.pc = 0) (hgh : g.halted = false) (hgf : g.fault = false)
    (hnonneg : 0 ≤ g.realReg 0) (hupper : g.realReg 0 ≤ (2 : ℝ)^N) :
    ∃ (steps : ℕ) (d : Machine), execute host c steps = d ∧ d.pc = returnPC ∧
      d.natReg (shadowReg 3) = (2*g.natReg 0)*⌈g.realReg 0⌉₊ ∧
      d.work ≤ c.work+9*(16*N+15) ∧ d.halted = false ∧ PreservesOutside base 2 c d := by
  obtain ⟨final,hends,hout,hwork⟩ := routine_ends g N hgp hgh hgf hnonneg hupper
  have hposition : c.pc = shadowDestination (shadowWidth ceilingProgram.code) offset returnPC g := by
    simpa [shadowDestination,hgh,hgp] using hpos
  obtain ⟨steps,d,hd,hdrep,hdpc,hdwork,hdh,_,_,_,_,hdframe⟩ :=
    shadow_framed_ends host ceilingProgram offset returnPC hcode base 2 (by omega) c g final hr
      hh hone hbase hfactor hrealFactor hposition hends
  have helapsed : final.work-g.work ≤ 16*N+15 := by omega
  rw [ceilingProgram_width] at hdwork
  refine ⟨steps,d,hd,hdpc,?_,by omega,hdh,hdframe⟩
  rw [hdrep.natReg,hout]
  ring
end DecrAlmostLinearSSSP.Decremental.ScaledCeiling
end s64
section s65
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
lemma eval_shadow_scalar_command {B F : ℕ} {s : Data} {g : Machine}
    (h : ShadowDataRep B F s g) (ins : Instruction) (a : Atom)
    (ht : shadowScalarTranslation ins = some a.instruction) :
    ∃ cost t, Eval (.atom a) s cost t ∧ cost ≤ 4 ∧ ShadowDataRep B F t (instructionEffect ins g) :=
  ⟨1,a.effect s,.atom _ _,by omega,(shadow_scalar h ins a.instruction ht).data_machine⟩
lemma eval_shadow_action {B F : ℕ} {s : Data} {g : Machine}
    (h : ShadowDataRep B F s g) (hF : 0 < F) (hb : s.natReg 0 = B)
    (hf : s.natReg 7 = F) (hrf : s.realReg 7 = (F : ℝ)) (ins : Instruction) :
    ∃ cost t, Eval (shadowAction ins) s cost t ∧ cost ≤ actionBound ins ∧
      ShadowDataRep B F t (instructionEffect ins g) := by
  classical
  cases ins with
  | rational d q => exact eval_shadow_scalar_command h _ ⟨.rational (shadowReg d) q,trivial⟩ rfl
  | add d a b => exact eval_shadow_scalar_command h _ ⟨.add (shadowReg d) (shadowReg a) (shadowReg b),trivial⟩ rfl
  | sub d a b => exact eval_shadow_scalar_command h _ ⟨.sub (shadowReg d) (shadowReg a) (shadowReg b),trivial⟩ rfl
  | mul d a b => exact eval_shadow_scalar_command h _ ⟨.mul (shadowReg d) (shadowReg a) (shadowReg b),trivial⟩ rfl
  | div d a b => exact eval_shadow_scalar_command h _ ⟨.div (shadowReg d) (shadowReg a) (shadowReg b),trivial⟩ rfl
  | log d a => exact eval_shadow_scalar_command h _ ⟨.log (shadowReg d) (shadowReg a),trivial⟩ rfl
  | nadd d a b => exact eval_shadow_scalar_command h _ ⟨.nadd (shadowReg d) (shadowReg a) (shadowReg b),trivial⟩ rfl
  | nsub d a b => exact eval_shadow_scalar_command h _ ⟨.nsub (shadowReg d) (shadowReg a) (shadowReg b),trivial⟩ rfl
  | natural d q =>
    obtain ⟨t,he,ht⟩ := eval_shadow_constant h d q hf
    exact ⟨q+1,t,he,by simp [actionBound],ht⟩
  | cast d a =>
    obtain ⟨t,he,ht⟩ := eval_shadow_cast h hF d a hrf
    exact ⟨2,t,he,by norm_num [actionBound],ht⟩
  | load d a =>
    obtain ⟨t,he,ht,ha⟩ := eval_shadow_address h hb hf a
    exact ⟨4,_,Eval.seq he (eval_load t (shadowReg d) 6),le_rfl,(shadow_load ht d a ha).data_machine⟩
  | loadN d a =>
    obtain ⟨t,he,ht,ha⟩ := eval_shadow_address h hb hf a
    exact ⟨4,_,Eval.seq he (eval_loadN t (shadowReg d) 6),le_rfl,(shadow_loadN ht d a ha).data_machine⟩
  | store a d =>
    obtain ⟨t,he,ht,ha⟩ := eval_shadow_address h hb hf a
    exact ⟨4,_,Eval.seq he (eval_store t 6 (shadowReg d)),le_rfl,(shadow_store ht hF a d ha).data_machine⟩
  | storeN a d =>
    obtain ⟨t,he,ht,ha⟩ := eval_shadow_address h hb hf a
    exact ⟨4,_,Eval.seq he (eval_storeN t 6 (shadowReg d)),le_rfl,(shadow_storeN ht hF a d ha).data_machine⟩
  | jump pc =>
    exact ⟨1,_,eval_natural s 2 pc,by norm_num [actionBound],(h.pc_update pc).data_machine⟩
  | halt => exact ⟨1,_,eval_natural s 4 1,by norm_num [actionBound],h.halt_update.data_machine⟩
  | less a b pc =>
    by_cases htest : g.realReg a < g.realReg b
    · have ht : (Test.realLess (shadowReg a) (shadowReg b)).holds s := (shadow_real_comparison h a b).mpr htest
      refine ⟨2,_,Eval.branchYes ht (eval_natural s 2 pc),by norm_num [actionBound],?_⟩
      simp only [instructionEffect,if_pos htest]
      change ShadowRep B F {s.machine with natReg := Function.update s.natReg 2 pc} {g with pc := pc}
      exact h.pc_update pc
    · have ht : ¬(Test.realLess (shadowReg a) (shadowReg b)).holds s := fun hh => htest ((shadow_real_comparison h a b).mp hh)
      refine ⟨2,s,Eval.branchNo ht (.skip s),by norm_num [actionBound],?_⟩
      simpa only [instructionEffect,if_neg htest] using h
  | lessN a b pc =>
    by_cases htest : g.natReg a < g.natReg b
    · have ht : (Test.natLess (shadowReg a) (shadowReg b)).holds s := (shadow_nat_comparison h hF a b).mpr htest
      refine ⟨2,_,Eval.branchYes ht (eval_natural s 2 pc),by norm_num [actionBound],?_⟩
      simp only [instructionEffect,if_pos htest]
      change ShadowRep B F {s.machine with natReg := Function.update s.natReg 2 pc} {g with pc := pc}
      exact h.pc_update pc
    · have ht : ¬(Test.natLess (shadowReg a) (shadowReg b)).holds s := fun hh => htest ((shadow_nat_comparison h hF a b).mp hh)
      refine ⟨2,s,Eval.branchNo ht (.skip s),by norm_num [actionBound],?_⟩
      simpa only [instructionEffect,if_neg htest] using h
end DecrAlmostLinearSSSP.Decremental
end s65
section s66
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
lemma repeatedAdd_no_memory (d factor q : ℕ) : NoMemory (repeatedAdd d factor q) := by
  induction q with
  | zero => trivial
  | succ q ih => exact ⟨trivial,ih⟩
lemma shadowAction_no_memory (ins : Instruction) (hins : NoStore ins) : NoMemory (shadowAction ins) := by
  cases ins with
  | natural d q => exact ⟨trivial,repeatedAdd_no_memory _ _ _⟩
  | store a d | storeN a d => exact False.elim hins
  | _ => all_goals simp [shadowAction,NoMemory,Structured.natural,rational,Structured.cast,add,sub,mul,Structured.div,
      logarithm,nadd,nsub,load,loadN,store,storeN,Structured.sequence,NoStore]
lemma shadowAction_memory_frame {B F : ℕ} {s t : Data} {g : Machine}
    (h : ShadowDataRep B F s g) (hb : s.natReg 0 = B) (hf : s.natReg 7 = F)
    (ins : Instruction) (cost : ℕ) (he : Eval (shadowAction ins) s cost t)
    (address : ℕ) (hout : ∀ a, address ≠ B+F*(2*a+1)) :
    t.realMem address = s.realMem address ∧ t.natMem address = s.natMem address := by
  classical
  by_cases hi : NoStore ins
  · obtain ⟨hr,hn⟩ := he.no_memory (shadowAction_no_memory ins hi)
    exact ⟨congrFun hr address,congrFun hn address⟩
  · cases ins with
    | store a d =>
      obtain ⟨u,hu,hrep,haddr⟩ := eval_shadow_address h hb hf a
      have he' : Eval (shadowAction (.store a d)) s 4
          {u with realMem := Function.update u.realMem (u.natReg 6) (u.realReg (shadowReg d))} :=
        Eval.seq hu (eval_store u 6 (shadowReg d))
      obtain ⟨_,rfl⟩ := he.deterministic he'
      have hmem := hu.no_memory (by simp [NoMemory,Structured.sequence,nadd,NoStore])
      have hne : address ≠ u.natReg 6 := by rw [haddr];exact hout _
      exact ⟨(Function.update_of_ne hne _ _).trans (congrFun hmem.1 address),congrFun hmem.2 address⟩
    | storeN a d =>
      obtain ⟨u,hu,hrep,haddr⟩ := eval_shadow_address h hb hf a
      have he' : Eval (shadowAction (.storeN a d)) s 4
          {u with natMem := Function.update u.natMem (u.natReg 6) (u.natReg (shadowReg d))} :=
        Eval.seq hu (eval_storeN u 6 (shadowReg d))
      obtain ⟨_,rfl⟩ := he.deterministic he'
      have hmem := hu.no_memory (by simp [NoMemory,Structured.sequence,nadd,NoStore])
      have hne : address ≠ u.natReg 6 := by rw [haddr];exact hout _
      exact ⟨congrFun hmem.1 address,(Function.update_of_ne hne _ _).trans (congrFun hmem.2 address)⟩
    | _ => all_goals exact False.elim (hi trivial)
end DecrAlmostLinearSSSP.Decremental
end s66
section s67
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
lemma NatFrame.flag {cmd : Cmd} {k : ℕ} (h : NatFrame cmd k) : FlagFrame cmd k := by
  induction cmd with
  | skip => trivial
  | atom a => exact Or.inl h
  | seq a b iha ihb | branch test a b iha ihb => exact ⟨iha h.1,ihb h.2⟩
  | loop test a ih => exact ih h
lemma Eval.flag_bound {cmd : Cmd} {s t : Data} {cost k : ℕ}
    (he : Eval cmd s cost t) (h : FlagFrame cmd k) (hs : s.natReg k ≤ 1) : t.natReg k ≤ 1 := by
  induction he with
  | skip => exact hs
  | atom a s =>
    rcases h with h | ⟨q,hq,heq⟩
    · rw [atom_nat_frame a s k h];exact hs
    · cases a with
      | mk ins hstraight =>
        dsimp only at heq
        subst ins
        simpa only [Atom.effect,instructionEffect,data,Data.machine,Function.update_self] using hq
  | seq ha hb iha ihb => exact ihb h.2 (iha h.1 hs)
  | branchYes ht he ih => exact ih h.1 hs
  | branchNo ht he ih => exact ih h.2 hs
  | loopNo => exact hs
  | loopYes ht ha hb iha ihb => exact ihb h (iha h hs)
end DecrAlmostLinearSSSP.Decremental.Structured
end s67
section s68
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
lemma shadowAction_nat_frame (ins : Instruction) (k : ℕ) (hk : k < 9)
    (h2 : 2 ≠ k) (h4 : 4 ≠ k) (h6 : 6 ≠ k) : NatFrame (shadowAction ins) k := by
  have hs : ∀ j, shadowReg j ≠ k := fun j => shadowReg_ne_meta j k hk
  cases ins with
  | natural d q => exact ⟨hs d,repeatedAdd_nat_frame _ _ _ _ (hs d)⟩
  | _ => all_goals simp [shadowAction,NatFrame,Structured.natural,rational,Structured.cast,add,sub,mul,Structured.div,
      logarithm,nadd,nsub,load,loadN,store,storeN,Structured.sequence,writesNat,hs,h2,h4,h6]
lemma shadowAction_real_frame (ins : Instruction) (k : ℕ) (hk : k < 9) : RealFrame (shadowAction ins) k := by
  have hs : ∀ j, shadowReg j ≠ k := fun j => shadowReg_ne_meta j k hk
  cases ins with
  | natural d q => exact ⟨not_false,repeatedAdd_real_frame _ _ _ _⟩
  | _ => all_goals simp [shadowAction,RealFrame,Structured.natural,rational,Structured.cast,add,sub,mul,Structured.div,
      logarithm,nadd,nsub,load,loadN,store,storeN,Structured.sequence,writesReal,hs]
lemma shadowAction_halt_frame (ins : Instruction) (hins : ins ≠ .halt) : NatFrame (shadowAction ins) 4 := by
  have hs : ∀ j, shadowReg j ≠ 4 := fun j => shadowReg_ne_meta j 4 (by omega)
  cases ins with
  | natural d q => exact ⟨hs d,repeatedAdd_nat_frame _ _ _ _ (hs d)⟩
  | halt => exact False.elim (hins rfl)
  | _ => all_goals simp [shadowAction,NatFrame,Structured.natural,rational,Structured.cast,add,sub,mul,Structured.div,
      logarithm,nadd,nsub,load,loadN,store,storeN,Structured.sequence,writesNat,hs]
lemma shadowAction_flag_frame (ins : Instruction) : FlagFrame (shadowAction ins) 4 := by
  by_cases hi : ins = .halt
  · subst ins
    exact Or.inr ⟨1,le_rfl,rfl⟩
  · exact (shadowAction_halt_frame ins hi).flag
end DecrAlmostLinearSSSP.Decremental
end s68
section s69
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
lemma ShadowDataRep.scratch8 {B F : ℕ} {s : Data} {g : Machine}
    (h : ShadowDataRep B F s g) (x : ℕ) :
    ShadowDataRep B F {s with natReg := Function.update s.natReg 8 x} g := by
  refine ⟨?_,?_,?_,?_,h.realReg,?_,h.realMem,h.natMem⟩
  all_goals try simpa only [Data.machine,Function.update_of_ne (by decide : (2 : ℕ) ≠ 8),
    Function.update_of_ne (by decide : (3 : ℕ) ≠ 8),Function.update_of_ne (by decide : (4 : ℕ) ≠ 8),
    Function.update_of_ne (by decide : (5 : ℕ) ≠ 8)] using h.pc
  · simpa only [Data.machine,Function.update_of_ne (by decide : (3 : ℕ) ≠ 8)] using h.work
  · simpa only [Data.machine,Function.update_of_ne (by decide : (4 : ℕ) ≠ 8)] using h.halted
  · simpa only [Data.machine,Function.update_of_ne (by decide : (5 : ℕ) ≠ 8)] using h.fault
  · intro j
    simpa only [Data.machine,Function.update_of_ne (shadowReg_ne_meta j 8 (by omega))] using h.natReg j
lemma eval_shadow_instruction {B F : ℕ} {s : Data} {g : Machine}
    (h : ShadowDataRep B F s g) (hF : 0 < F) (hb : s.natReg 0 = B)
    (h1 : s.natReg 1 = 1) (hf : s.natReg 7 = F) (hrf : s.realReg 7 = (F : ℝ))
    (ins : Instruction) :
    ∃ cost t, Eval (shadowInstruction g.pc ins) s cost t ∧ cost ≤ actionBound ins+2 ∧
      ShadowDataRep B F t (instructionEffect ins {g with pc := g.pc+1,work := g.work+1}) := by
  let t : Data := {s with natReg := Function.update (Function.update s.natReg 2 (g.pc+1)) 3 (s.natReg 3+1)}
  have he : Eval (.seq (natural 2 (g.pc+1)) (nadd 3 3 1)) s 2 t := by
    simpa only [h1] using eval_shadow_header s g.pc
  have ht := h.header h1
  have ht0 : t.natReg 0 = B := by simp [t,hb]
  have ht7 : t.natReg 7 = F := by simp [t,hf]
  obtain ⟨cost,u,hu,hcost,hrep⟩ := eval_shadow_action ht hF ht0 ht7 hrf ins
  exact ⟨2+cost,u,.seq he hu,by omega,hrep⟩
lemma eval_dispatch_aux {B F : ℕ} (code : List Instruction) (start : ℕ) (s : Data) (g : Machine)
    (h : ShadowDataRep B F s g) (hF : 0 < F) (hb : s.natReg 0 = B)
    (h1 : s.natReg 1 = 1) (hf : s.natReg 7 = F) (hrf : s.realReg 7 = (F : ℝ))
    (hstart : start ≤ g.pc) (ins : Instruction) (hins : code[g.pc-start]? = some ins) :
    ∃ cost t, Eval (dispatchAux start code) s cost t ∧ cost ≤ dispatchCharge code ∧
      ShadowDataRep B F t (instructionEffect ins {g with pc := g.pc+1,work := g.work+1}) := by
  induction code generalizing start s with
  | nil => simp at hins
  | cons head rest ih =>
    let t : Data := {s with natReg := Function.update s.natReg 8 (start+1)}
    have ht : ShadowDataRep B F t g := h.scratch8 (start+1)
    have ht0 : t.natReg 0 = B := by simp [t,hb]
    have ht1 : t.natReg 1 = 1 := by simp [t,h1]
    have ht7 : t.natReg 7 = F := by simp [t,hf]
    by_cases hp : g.pc = start
    · have hins' : head = ins := by simpa only [hp,Nat.sub_self,List.getElem?_cons_zero,Option.some.injEq] using hins
      subst ins
      obtain ⟨cost,u,hu,hcost,hrep⟩ := eval_shadow_instruction ht hF ht0 ht1 ht7 hrf head
      have htest : (Test.natLess 2 8).holds t := by
        change t.natReg 2 < t.natReg 8
        simp only [t,Function.update_self,Function.update_of_ne (by decide : (2 : ℕ) ≠ 8)]
        have hh : s.natReg 2 = g.pc := h.pc
        omega
      have hu' : Eval (shadowInstruction start head) t cost u := by simpa only [hp] using hu
      have he : Eval (dispatchAux start (head::rest)) s (1+(cost+1)) u :=
        Eval.seq (eval_natural s 8 (start+1)) (Eval.branchYes htest hu')
      refine ⟨1+(cost+1),u,he,?_,hrep⟩
      simp only [dispatchCharge,List.map_cons,List.sum_cons] at hcost ⊢
      omega
    · have hnext : start+1 ≤ g.pc := by omega
      have hidx : g.pc-start = (g.pc-(start+1))+1 := by omega
      have htail : rest[g.pc-(start+1)]? = some ins := by simpa only [hidx,List.getElem?_cons_succ] using hins
      obtain ⟨cost,u,hu,hcost,hrep⟩ := ih (start+1) t ht ht0 ht1 ht7 hrf hnext htail
      have htest : ¬(Test.natLess 2 8).holds t := by
        change ¬t.natReg 2 < t.natReg 8
        simp only [t,Function.update_self,Function.update_of_ne (by decide : (2 : ℕ) ≠ 8)]
        have hh : s.natReg 2 = g.pc := h.pc
        omega
      refine ⟨1+(cost+2),u,Eval.seq (eval_natural s 8 (start+1)) (Eval.branchNo htest hu),?_,hrep⟩
      simp only [dispatchCharge,List.map_cons,List.sum_cons] at hcost ⊢
      omega
end DecrAlmostLinearSSSP.Decremental
end s69
section s70
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
lemma shadowInstruction_memory_frame {B F : ℕ} {s t : Data} {g : Machine}
    (h : ShadowDataRep B F s g) (hb : s.natReg 0 = B) (hf : s.natReg 7 = F)
    (h1 : s.natReg 1 = 1)
    (ins : Instruction) (cost : ℕ) (he : Eval (shadowInstruction g.pc ins) s cost t)
    (address : ℕ) (hout : ∀ a, address ≠ B+F*(2*a+1)) :
    t.realMem address = s.realMem address ∧ t.natMem address = s.natMem address := by
  let u : Data := {s with natReg := Function.update (Function.update s.natReg 2 (g.pc+1)) 3 (s.natReg 3+1)}
  have hu : Eval (.seq (natural 2 (g.pc+1)) (nadd 3 3 1)) s 2 u := by
    simpa only [h1] using eval_shadow_header s g.pc
  cases he with
  | seq hhead haction =>
    obtain ⟨_,rfl⟩ := hhead.deterministic hu
    have hu0 : u.natReg 0 = B := by simp [u,hb]
    have hu7 : u.natReg 7 = F := by simp [u,hf]
    have hu1 : u.natReg 1 = 1 := by simp [u,h1]
    exact shadowAction_memory_frame (h.header h1) hu0 hu7 ins _ haction address hout
lemma dispatchAux_memory_frame {B F : ℕ} (code : List Instruction) (pc : ℕ)
    (s t : Data) (g : Machine) (h : ShadowDataRep B F s g)
    (hb : s.natReg 0 = B) (hf : s.natReg 7 = F) (h1 : s.natReg 1 = 1)
    (hpc : pc ≤ g.pc) (ins : Instruction) (hins : code[g.pc-pc]? = some ins)
    (cost : ℕ) (he : Eval (dispatchAux pc code) s cost t)
    (address : ℕ) (hout : ∀ a, address ≠ B+F*(2*a+1)) :
    t.realMem address = s.realMem address ∧ t.natMem address = s.natMem address := by
  induction code generalizing pc s cost with
  | nil => simp at hins
  | cons head rest ih =>
    let u : Data := {s with natReg := Function.update s.natReg 8 (pc+1)}
    have hu := eval_natural s 8 (pc+1)
    cases he with
    | seq hnat hbranch =>
      obtain ⟨_,rfl⟩ := hnat.deterministic hu
      have huRep : ShadowDataRep B F u g := h.scratch8 (pc+1)
      have hu0 : u.natReg 0 = B := by simp [u,hb]
      have hu7 : u.natReg 7 = F := by simp [u,hf]
      have hu1 : u.natReg 1 = 1 := by simp [u,h1]
      by_cases hp : g.pc = pc
      · have hins' : head = ins := by simpa only [hp,Nat.sub_self,List.getElem?_cons_zero,Option.some.injEq] using hins
        have htest : (Test.natLess 2 8).holds u := by
          change u.natReg 2 < u.natReg 8
          simp only [u,Function.update_self,Function.update_of_ne (by decide : (2 : ℕ) ≠ 8)]
          have hh : s.natReg 2 = g.pc := h.pc
          omega
        cases hbranch with
        | @branchYes _ _ _ _ _ amount ht hbody =>
          have hbody' : Eval (shadowInstruction g.pc head) u amount t := by simpa only [hp] using hbody
          exact shadowInstruction_memory_frame huRep hu0 hu7 hu1 head _ hbody' address hout
        | branchNo ht hbody => exact False.elim (ht htest)
      · have hnext : pc+1 ≤ g.pc := by omega
        have hidx : g.pc-pc = (g.pc-(pc+1))+1 := by omega
        have htail : rest[g.pc-(pc+1)]? = some ins := by simpa only [hidx,List.getElem?_cons_succ] using hins
        have htest : ¬(Test.natLess 2 8).holds u := by
          change ¬u.natReg 2 < u.natReg 8
          simp only [u,Function.update_self,Function.update_of_ne (by decide : (2 : ℕ) ≠ 8)]
          have hh : s.natReg 2 = g.pc := h.pc
          omega
        cases hbranch with
        | branchYes ht hbody => exact False.elim (htest ht)
        | branchNo ht hbody => exact ih (pc+1) u huRep hu0 hu7 hu1 hnext htail _ hbody
end DecrAlmostLinearSSSP.Decremental
end s70
section s71
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
lemma shadowInstruction_nat_frame (pc : ℕ) (ins : Instruction) (k : ℕ)
    (hk : k = 0 ∨ k = 1 ∨ k = 7) : NatFrame (shadowInstruction pc ins) k := by
  refine ⟨?_,shadowAction_nat_frame ins k (by rcases hk with rfl|rfl|rfl <;> omega)
    (by rcases hk with rfl|rfl|rfl <;> omega) (by rcases hk with rfl|rfl|rfl <;> omega)
    (by rcases hk with rfl|rfl|rfl <;> omega)⟩
  simp only [NatFrame,Structured.natural,nadd,writesNat]
  rcases hk with rfl|rfl|rfl <;> omega
lemma shadowInstruction_real_frame (pc : ℕ) (ins : Instruction) : RealFrame (shadowInstruction pc ins) 7 :=
  ⟨⟨not_false,not_false⟩,shadowAction_real_frame ins 7 (by omega)⟩
lemma shadowInstruction_flag_frame (pc : ℕ) (ins : Instruction) : FlagFrame (shadowInstruction pc ins) 4 :=
  ⟨(show NatFrame (.seq (natural 2 (pc+1)) (nadd 3 3 1)) 4 from ⟨by norm_num [NatFrame,Structured.natural,nadd,writesNat],by norm_num [NatFrame,Structured.natural,nadd,writesNat]⟩).flag,
    shadowAction_flag_frame ins⟩
lemma dispatchAux_nat_frame (code : List Instruction) (start k : ℕ)
    (hk : k = 0 ∨ k = 1 ∨ k = 7) : NatFrame (dispatchAux start code) k := by
  induction code generalizing start with
  | nil =>
    simp only [dispatchAux,NatFrame,Structured.natural,writesNat]
    rcases hk with rfl|rfl|rfl <;> omega
  | cons ins rest ih =>
    refine ⟨?_,shadowInstruction_nat_frame start ins k hk,ih (start+1)⟩
    simp only [NatFrame,Structured.natural,writesNat]
    rcases hk with rfl|rfl|rfl <;> omega
lemma dispatchAux_real_frame (code : List Instruction) (start : ℕ) : RealFrame (dispatchAux start code) 7 := by
  induction code generalizing start with
  | nil => exact ⟨not_false,not_false⟩
  | cons ins rest ih => exact ⟨not_false,shadowInstruction_real_frame start ins,ih (start+1)⟩
lemma dispatchAux_flag_frame (code : List Instruction) (start : ℕ) : FlagFrame (dispatchAux start code) 4 := by
  induction code generalizing start with
  | nil => exact ⟨Or.inl (by norm_num [NatFrame,Structured.natural,nadd,writesNat]),Or.inr ⟨1,le_rfl,rfl⟩⟩
  | cons ins rest ih => exact ⟨Or.inl (by norm_num [NatFrame,Structured.natural,nadd,writesNat]),shadowInstruction_flag_frame start ins,ih (start+1)⟩
end DecrAlmostLinearSSSP.Decremental
end s71
section s72
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
lemma ShadowDataRep.halt_flag {B F : ℕ} {s : Data} {g : Machine} (h : ShadowDataRep B F s g)
    (hb : s.natReg 4 ≤ 1) : s.natReg 4 = if g.halted then 1 else 0 := by
  have hh := h.halted
  by_cases hg : g.halted = true
  · have hs : s.natReg 4 = 1 := by simpa only [Data.machine,hg,beq_iff_eq] using hh
    simp [hg,hs]
  · have hg' : g.halted = false := Bool.eq_false_iff.mpr hg
    have hs : s.natReg 4 ≠ 1 := by
      intro hs
      simp [Data.machine,hs,hg'] at hh
    have hs0 : s.natReg 4 = 0 := by omega
    simp only [hg',Bool.false_eq_true,if_false,hs0]
lemma eval_shadow_interpreter (guest : Program) (t : ℕ) (B F : ℕ) (hF : 0 < F)
    (s : Data) (g : Machine) (h : ShadowDataRep B F s g) (hb : s.natReg 0 = B)
    (h1 : s.natReg 1 = 1) (hf : s.natReg 7 = F) (hrf : s.realReg 7 = (F : ℝ))
    (hflag : s.natReg 4 ≤ 1)
    (hvalid : ∀ j < t, (execute guest g j).halted = false → ∃ ins, guest.code[(execute guest g j).pc]? = some ins)
    (hfinal : (execute guest g t).halted = true) :
    ∃ cost u, Eval (shadowInterpreter guest.code) s cost u ∧
      cost ≤ (dispatchCharge guest.code+2)*t+2 ∧ ShadowDataRep B F u (execute guest g t) := by
  induction t generalizing s g with
  | zero =>
    have hgh : g.halted = true := hfinal
    have hs := h.halt_flag hflag
    have htest : ¬(Test.natLess 4 1).holds s := by simp [Test.holds,hs,hgh,h1]
    exact ⟨2,s,Eval.loopNo s htest,by simp,h⟩
  | succ t ih =>
    by_cases hgh : g.halted = true
    · have hs := h.halt_flag hflag
      have htest : ¬(Test.natLess 4 1).holds s := by simp [Test.holds,hs,hgh,h1]
      refine ⟨2,s,Eval.loopNo s htest,by omega,?_⟩
      rwa [execute_halted guest g hgh]
    · have hgh' : g.halted = false := Bool.eq_false_iff.mpr hgh
      obtain ⟨ins,hins⟩ := hvalid 0 (by omega) hgh'
      obtain ⟨cost,u,he,hcost,hrep⟩ := eval_dispatch_aux guest.code 0 s g h hF hb h1 hf hrf
        (Nat.zero_le _) ins (by simpa [execute] using hins)
      rw [← step_eq_effect guest g ins hgh' hins] at hrep
      have hu0 : u.natReg 0 = B := (he.nat_frame (dispatchAux_nat_frame _ _ 0 (Or.inl rfl))).trans hb
      have hu1 : u.natReg 1 = 1 := (he.nat_frame (dispatchAux_nat_frame _ _ 1 (Or.inr (Or.inl rfl)))).trans h1
      have hu7 : u.natReg 7 = F := (he.nat_frame (dispatchAux_nat_frame _ _ 7 (Or.inr (Or.inr rfl)))).trans hf
      have hur7 : u.realReg 7 = (F : ℝ) := (he.real_frame (dispatchAux_real_frame _ _)).trans hrf
      have huflag : u.natReg 4 ≤ 1 := he.flag_bound (dispatchAux_flag_frame _ _) hflag
      have hv : ∀ j < t, (execute guest (step guest g) j).halted = false → ∃ ins, guest.code[(execute guest (step guest g) j).pc]? = some ins := by
        intro j hj hh
        rw [← execute_succ_front] at hh ⊢
        exact hvalid (j+1) (by omega) hh
      have hfin : (execute guest (step guest g) t).halted = true := by rwa [← execute_succ_front]
      obtain ⟨rest,v,hrest,hrestcost,hrestrep⟩ := ih u (step guest g) hrep hu0 hu1 hu7 hur7 huflag hv hfin
      have hs := h.halt_flag hflag
      have htest : (Test.natLess 4 1).holds s := by simp [Test.holds,hs,hgh',h1]
      refine ⟨cost+rest+2,v,Eval.loopYes htest he hrest,?_,?_⟩
      · rw [Nat.mul_succ]
        omega
      · rwa [execute_succ_front]
lemma eval_shadow_interpreter_ends (guest : Program) (B F : ℕ) (hF : 0 < F)
    (s : Data) (g final : Machine) (h : ShadowDataRep B F s g) (hb : s.natReg 0 = B)
    (h1 : s.natReg 1 = 1) (hf : s.natReg 7 = F) (hrf : s.realReg 7 = (F : ℝ))
    (hflag : s.natReg 4 ≤ 1) (he : Ends guest g final) :
    ∃ cost u, Eval (shadowInterpreter guest.code) s cost u ∧
      cost ≤ (dispatchCharge guest.code+2)*(final.work-g.work)+2 ∧ ShadowDataRep B F u final := by
  obtain ⟨t,ht,hhalt,hfault⟩ := he
  have hhalt' : (execute guest g t).halted = true := by rwa [ht]
  obtain ⟨r,_,hrun,hrwork⟩ := terminating_prefix guest g t hhalt'
  have hrfinal : execute guest g r = final := hrun.trans ht
  have hrfault : (execute guest g r).fault = false := by rwa [hrfinal]
  obtain ⟨cost,u,hu,hcost,hrep⟩ := eval_shadow_interpreter guest r B F hF s g h hb h1 hf hrf hflag
    (execution_valid_code guest g r hrfault) (by rwa [hrfinal])
  rw [ht] at hrwork
  refine ⟨cost,u,hu,?_,?_⟩
  · rwa [← hrwork]
  · rwa [hrfinal] at hrep
end DecrAlmostLinearSSSP.Decremental
end s72
section s73
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
lemma shadow_interpreter_memory_frame (guest : Program) (steps B F : ℕ) (hF : 0 < F)
    (s u : Data) (g : Machine) (h : ShadowDataRep B F s g) (hb : s.natReg 0 = B)
    (h1 : s.natReg 1 = 1) (hf : s.natReg 7 = F) (hrf : s.realReg 7 = (F : ℝ))
    (hflag : s.natReg 4 ≤ 1)
    (hvalid : ∀ j < steps, (execute guest g j).halted = false → ∃ ins, guest.code[(execute guest g j).pc]? = some ins)
    (hfinal : (execute guest g steps).halted = true)
    (cost : ℕ) (he : Eval (shadowInterpreter guest.code) s cost u)
    (address : ℕ) (hout : ∀ a, address ≠ B+F*(2*a+1)) :
    u.realMem address = s.realMem address ∧ u.natMem address = s.natMem address := by
  induction steps generalizing s u g cost with
  | zero =>
    have hgh : g.halted = true := hfinal
    have hs := h.halt_flag hflag
    have htest : ¬(Test.natLess 4 1).holds s := by simp [Test.holds,hs,hgh,h1]
    obtain ⟨_,rfl⟩ := he.deterministic (show Eval (shadowInterpreter guest.code) s 2 s from Eval.loopNo s htest)
    exact ⟨rfl,rfl⟩
  | succ steps ih =>
    by_cases hgh : g.halted = true
    · have hs := h.halt_flag hflag
      have htest : ¬(Test.natLess 4 1).holds s := by simp [Test.holds,hs,hgh,h1]
      obtain ⟨_,rfl⟩ := he.deterministic (show Eval (shadowInterpreter guest.code) s 2 s from Eval.loopNo s htest)
      exact ⟨rfl,rfl⟩
    · have hgh' : g.halted = false := Bool.eq_false_iff.mpr hgh
      obtain ⟨ins,hins⟩ := hvalid 0 (by omega) hgh'
      have hins' : guest.code[g.pc]? = some ins := by simpa [execute] using hins
      obtain ⟨first,t,hbody,hfirst,hrep⟩ := eval_dispatch_aux guest.code 0 s g h hF hb h1 hf hrf
        (Nat.zero_le _) ins (by simpa only [Nat.sub_zero] using hins')
      have hbodyMem := dispatchAux_memory_frame guest.code 0 s t g h hb hf h1
        (Nat.zero_le _) ins (by simpa only [Nat.sub_zero] using hins') first hbody address hout
      rw [← step_eq_effect guest g ins hgh' hins'] at hrep
      have ht0 : t.natReg 0 = B := (hbody.nat_frame (dispatchAux_nat_frame _ _ 0 (Or.inl rfl))).trans hb
      have ht1 : t.natReg 1 = 1 := (hbody.nat_frame (dispatchAux_nat_frame _ _ 1 (Or.inr (Or.inl rfl)))).trans h1
      have ht7 : t.natReg 7 = F := (hbody.nat_frame (dispatchAux_nat_frame _ _ 7 (Or.inr (Or.inr rfl)))).trans hf
      have htr7 : t.realReg 7 = (F : ℝ) := (hbody.real_frame (dispatchAux_real_frame _ _)).trans hrf
      have htflag : t.natReg 4 ≤ 1 := hbody.flag_bound (dispatchAux_flag_frame _ _) hflag
      have hv : ∀ j < steps, (execute guest (step guest g) j).halted = false → ∃ ins, guest.code[(execute guest (step guest g) j).pc]? = some ins := by
        intro j hj hh
        rw [← execute_succ_front] at hh ⊢
        exact hvalid (j+1) (by omega) hh
      have hfin : (execute guest (step guest g) steps).halted = true := by rwa [← execute_succ_front]
      obtain ⟨rest,v,hrest,_,_⟩ := eval_shadow_interpreter guest steps B F hF t (step guest g) hrep
        ht0 ht1 ht7 htr7 htflag hv hfin
      have hrestMem := ih t v (step guest g) hrep ht0 ht1 ht7 htr7 htflag hv hfin rest hrest
      have hs := h.halt_flag hflag
      have htest : (Test.natLess 4 1).holds s := by simp [Test.holds,hs,hgh',h1]
      have hcombined : Eval (shadowInterpreter guest.code) s (first+rest+2) v := Eval.loopYes htest hbody hrest
      obtain ⟨_,rfl⟩ := he.deterministic hcombined
      exact ⟨hrestMem.1.trans hbodyMem.1,hrestMem.2.trans hbodyMem.2⟩
lemma eval_shadow_call (guest : Program) (B F : ℕ) (hF : 0 < F)
    (s : Data) (g final : Machine) (h : ShadowDataRep B F s g) (hb : s.natReg 0 = B)
    (h1 : s.natReg 1 = 1) (hf : s.natReg 7 = F) (hrf : s.realReg 7 = (F : ℝ))
    (hflag : s.natReg 4 ≤ 1) (he : Ends guest g final) :
    ∃ cost u, Eval (shadowInterpreter guest.code) s cost u ∧
      cost ≤ (dispatchCharge guest.code+2)*(final.work-g.work)+2 ∧ ShadowDataRep B F u final ∧
      ∀ address, (∀ a, address ≠ B+F*(2*a+1)) →
        u.realMem address = s.realMem address ∧ u.natMem address = s.natMem address := by
  obtain ⟨t,ht,hhalt,hfault⟩ := he
  have hhalt' : (execute guest g t).halted = true := by rwa [ht]
  obtain ⟨r,_,hrun,hrwork⟩ := terminating_prefix guest g t hhalt'
  have hrfinal : execute guest g r = final := hrun.trans ht
  have hrfault : (execute guest g r).fault = false := by rwa [hrfinal]
  obtain ⟨cost,u,hu,hcost,hrep⟩ := eval_shadow_interpreter guest r B F hF s g h hb h1 hf hrf hflag
    (execution_valid_code guest g r hrfault) (by rwa [hrfinal])
  rw [ht] at hrwork
  refine ⟨cost,u,hu,?_,?_,?_⟩
  · rwa [← hrwork]
  · rwa [hrfinal] at hrep
  · intro address hout
    exact shadow_interpreter_memory_frame guest r B F hF s u g h hb h1 hf hrf hflag
      (execution_valid_code guest g r hrfault) (by rwa [hrfinal]) cost hu address hout
end DecrAlmostLinearSSSP.Decremental
end s73
section s74
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
lemma shadowAction_even_frame (ins : Instruction) (k : ℕ) (hk : 10 ≤ k) (heven : Even k) :
    NatFrame (shadowAction ins) k := by
  have hs : ∀ j, shadowReg j ≠ k := by
    obtain ⟨r,hr⟩ := heven
    intro j
    dsimp [shadowReg]
    omega
  cases ins with
  | natural d q => exact ⟨hs d,repeatedAdd_nat_frame _ _ _ _ (hs d)⟩
  | _ => all_goals simp [shadowAction,NatFrame,Structured.natural,rational,Structured.cast,add,sub,mul,Structured.div,
      logarithm,nadd,nsub,load,loadN,store,storeN,Structured.sequence,writesNat,hs] <;> omega
lemma shadowAction_preserves_report_log {B bank start : ℕ} {s t : Data} {g : Machine}
    (h : ShadowDataRep B (bankFactor bank) s g) (hb : s.natReg 0 = B) (hf : s.natReg 7 = bankFactor bank)
    (ins : Instruction) (cost : ℕ) (he : Eval (shadowAction ins) s cost t)
    (reports : List ℕ) (hl : ReportLog start reports s) (hstart : ∃ r, start = B+2*r+1) :
    ReportLog start reports t := by
  refine ⟨(he.nat_frame (shadowAction_even_frame ins 10 (by omega) (by decide))).trans hl.1,
    (he.nat_frame (shadowAction_even_frame ins 12 (by omega) (by decide))).trans hl.2.1,?_⟩
  intro j hj
  obtain ⟨r,hr⟩ := hstart
  have hout : ∀ a, start+2*j ≠ B+bankFactor bank*(2*a+1) := by
    intro a
    rw [hr,show B+2*r+1+2*j = B+(2*(r+j)+1) by ring]
    exact Ne.symm (guest_bank_ne_host B bank a (r+j))
  exact (shadowAction_memory_frame h hb hf ins cost he (start+2*j) hout).2.trans (hl.2.2 j hj)
lemma shadowAction_store_address {B F : ℕ} {s t : Data} {g : Machine}
    (h : ShadowDataRep B F s g) (hb : s.natReg 0 = B) (hf : s.natReg 7 = F)
    (a d cost : ℕ) (he : Eval (shadowAction (.store a d)) s cost t) :
    t.natReg 6 = B+F*(2*g.natReg a+1) := by
  obtain ⟨u,hu,hrep,haddr⟩ := eval_shadow_address h hb hf a
  have he' : Eval (shadowAction (.store a d)) s 4
      {u with realMem := Function.update u.realMem (u.natReg 6) (u.realReg (shadowReg d))} :=
    Eval.seq hu (eval_store u 6 (shadowReg d))
  obtain ⟨_,rfl⟩ := he.deterministic he'
  exact haddr
lemma shadowAction_storeN_address {B F : ℕ} {s t : Data} {g : Machine}
    (h : ShadowDataRep B F s g) (hb : s.natReg 0 = B) (hf : s.natReg 7 = F)
    (a d cost : ℕ) (he : Eval (shadowAction (.storeN a d)) s cost t) :
    t.natReg 6 = B+F*(2*g.natReg a+1) := by
  obtain ⟨u,hu,hrep,haddr⟩ := eval_shadow_address h hb hf a
  have he' : Eval (shadowAction (.storeN a d)) s 4
      {u with natMem := Function.update u.natMem (u.natReg 6) (u.natReg (shadowReg d))} :=
    Eval.seq hu (eval_storeN u 6 (shadowReg d))
  obtain ⟨_,rfl⟩ := he.deterministic he'
  exact haddr
lemma eval_observed_action {B bank start : ℕ} {s : Data} {g : Machine}
    (h : ShadowDataRep B (bankFactor bank) s g) (hb : s.natReg 0 = B)
    (h1 : s.natReg 1 = 1) (hf : s.natReg 7 = bankFactor bank)
    (hrf : s.realReg 7 = (bankFactor bank : ℝ)) (h14 : s.natReg 14 = 2)
    (reports : List ℕ) (hl : ReportLog start reports s) (hstart : ∃ r, start = B+2*r+1)
    (ins : Instruction) :
    ∃ cost t, Eval (observedAction ins) s cost t ∧ cost ≤ actionBound ins+3 ∧
      ShadowDataRep B (bankFactor bank) t (instructionEffect ins g) ∧
      ReportLog start (reports++physicalWrites B bank ins g) t := by
  obtain ⟨cost,t,he,hcost,hrep⟩ := eval_shadow_action h (bankFactor_positive bank) hb hf hrf ins
  have hlog := shadowAction_preserves_report_log h hb hf ins cost he reports hl hstart
  have ht1 : t.natReg 1 = 1 := (he.nat_frame (shadowAction_nat_frame ins 1 (by omega) (by omega) (by omega) (by omega))).trans h1
  have ht14 : t.natReg 14 = 2 := (he.nat_frame (shadowAction_even_frame ins 14 (by omega) (by decide))).trans h14
  by_cases hi : NoStore ins
  · have heq : observedAction ins = shadowAction ins := by cases ins <;> first | rfl | exact False.elim hi
    have hnil : physicalWrites B bank ins g = [] := by cases ins <;> first | rfl | exact False.elim hi
    refine ⟨cost,t,?_,by omega,hrep,?_⟩
    · rwa [heq]
    · simpa only [hnil,List.append_nil] using hlog
  · have hout := report_log_outside B bank start reports t hstart hlog
    have happ := append_report_eval t ht1 ht14
    have happr := append_report_rep hrep hout
    have happLog := append_report_log start reports t hlog
    cases ins with
    | store a d =>
      have haddr := shadowAction_store_address h hb hf a d cost he
      refine ⟨cost+3,appendedReport t,Eval.seq he happ,by omega,happr,?_⟩
      simpa only [physicalWrites,sourceWrite,List.map_cons,List.map_nil,haddr] using happLog
    | storeN a d =>
      have haddr := shadowAction_storeN_address h hb hf a d cost he
      refine ⟨cost+3,appendedReport t,Eval.seq he happ,by omega,happr,?_⟩
      simpa only [physicalWrites,sourceWrite,List.map_cons,List.map_nil,haddr] using happLog
    | _ => all_goals exact False.elim (hi trivial)
end DecrAlmostLinearSSSP.Decremental
end s74
section s75
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
lemma shadowAction_real_even_frame (ins : Instruction) (k : ℕ) (heven : Even k) : RealFrame (shadowAction ins) k := by
  have hs : ∀ j, shadowReg j ≠ k := by
    obtain ⟨r,hr⟩ := heven
    intro j
    dsimp [shadowReg]
    omega
  cases ins with
  | natural d q => exact ⟨not_false,repeatedAdd_real_frame _ _ _ _⟩
  | _ => all_goals simp [shadowAction,RealFrame,Structured.natural,rational,Structured.cast,add,sub,mul,Structured.div,
      logarithm,nadd,nsub,load,loadN,store,storeN,Structured.sequence,writesReal,hs]
lemma dispatchAux_nat_even_frame (code : List Instruction) (pc k : ℕ) (hk : 10 ≤ k) (heven : Even k) :
    NatFrame (dispatchAux pc code) k := by
  induction code generalizing pc with
  | nil =>
    simp only [dispatchAux,NatFrame,Structured.natural,writesNat]
    constructor <;> omega
  | cons ins rest ih =>
    refine ⟨?_,?_,ih (pc+1)⟩
    · change 8 ≠ k
      omega
    · refine ⟨?_,shadowAction_even_frame ins k hk heven⟩
      change (2 ≠ k) ∧ (3 ≠ k)
      constructor <;> omega
lemma dispatchAux_real_even_frame (code : List Instruction) (pc k : ℕ) (heven : Even k) :
    RealFrame (dispatchAux pc code) k := by
  induction code generalizing pc with
  | nil => exact ⟨not_false,not_false⟩
  | cons ins rest ih =>
    exact ⟨not_false,⟨⟨not_false,not_false⟩,shadowAction_real_even_frame ins k heven⟩,ih (pc+1)⟩
lemma shadowInterpreter_nat_even_frame (code : List Instruction) (k : ℕ) (hk : 10 ≤ k) (heven : Even k) :
    NatFrame (shadowInterpreter code) k := dispatchAux_nat_even_frame code 0 k hk heven
lemma shadowInterpreter_real_even_frame (code : List Instruction) (k : ℕ) (heven : Even k) :
    RealFrame (shadowInterpreter code) k := dispatchAux_real_even_frame code 0 k heven
end DecrAlmostLinearSSSP.Decremental
end s75
section s76
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.ScaledCeiling
open Structured
lemma unscaledGuest_rep (base : ℕ) (s : Data) : ShadowDataRep base 1 s (unscaledGuest base s) := by
  refine ⟨rfl,rfl,rfl,rfl,fun _ => rfl,?_,?_,?_⟩
  · intro j
    simp [unscaledGuest,Data.machine]
  · intro a
    simp [unscaledGuest,Data.machine,Nat.add_assoc]
  · intro a
    simp [unscaledGuest,Data.machine,Nat.add_assoc]
lemma unscaled_ceiling_eval (base N : ℕ) (s : Data)
    (hb : s.natReg 0 = base) (h1 : s.natReg 1 = 1) (hpc : s.natReg 2 = 0)
    (hh : s.natReg 4 = 0) (hf : s.natReg 5 = 0)
    (hfactor : s.natReg 7 = 1) (hrfactor : s.realReg 7 = 1)
    (hnonneg : 0 ≤ s.realReg (shadowReg 0)) (hupper : s.realReg (shadowReg 0) ≤ (2 : ℝ)^N) :
    ∃ cost t, Eval (shadowInterpreter ceilingProgram.code) s cost t ∧
      t.natReg (shadowReg 3) = s.natReg (shadowReg 0)*⌈s.realReg (shadowReg 0)⌉₊ ∧
      cost ≤ (dispatchCharge ceilingProgram.code+2)*(16*N+15)+2 ∧
      (∀ address, (∀ a, address ≠ base+2*a+1) →
        t.realMem address = s.realMem address ∧ t.natMem address = s.natMem address) ∧
      ∀ k, 10 ≤ k → Even k → t.natReg k = s.natReg k ∧ t.realReg k = s.realReg k := by
  let g := unscaledGuest base s
  have hgp : g.pc = 0 := hpc
  have hgh : g.halted = false := by simp [g,unscaledGuest,hh]
  have hgf : g.fault = false := by simp [g,unscaledGuest,hf]
  obtain ⟨final,he,hout,hwork⟩ := routine_ends g N hgp hgh hgf hnonneg hupper
  obtain ⟨cost,t,ht,hcost,hrep,hframe⟩ := eval_shadow_call ceilingProgram base 1 (by omega) s g final
    (unscaledGuest_rep base s) hb h1 hfactor (by simpa using hrfactor) (by simp [hh]) he
  refine ⟨cost,t,ht,?_,?_,?_,?_⟩
  · have hreg : t.natReg (shadowReg 3) = final.natReg 3 := by
      simpa only [Data.machine,Nat.one_mul] using hrep.natReg 3
    exact hreg.trans hout
  · have hdelta : final.work-g.work ≤ 16*N+15 := by omega
    exact hcost.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hdelta) 2)
  · intro address ha
    apply hframe address
    simpa only [Nat.one_mul,Nat.add_assoc] using ha
  · intro k hk heven
    exact ⟨ht.nat_frame (shadowInterpreter_nat_even_frame _ k hk heven),
      ht.real_frame (shadowInterpreter_real_even_frame _ k heven)⟩
end DecrAlmostLinearSSSP.Decremental.ScaledCeiling
end s76
section s77
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.ScaledCeiling
open Structured
lemma setup_eval (s : Data) : Eval setup s 10 (setupData s) := eval_sequence_atoms setupAtoms s
lemma setup_fields (s : Data) (hn : s.natReg 56 = 0) (hr : s.realReg 56 = 0) :
    (setupData s).natReg 0 = s.natReg 48 ∧ (setupData s).natReg 1 = 1 ∧
    (setupData s).natReg 2 = 0 ∧ (setupData s).natReg 4 = 0 ∧ (setupData s).natReg 5 = 0 ∧
    (setupData s).natReg 7 = 1 ∧ (setupData s).realReg 7 = 1 ∧
    (setupData s).natReg (shadowReg 0) = s.natReg 58 ∧
    (setupData s).realReg (shadowReg 0) = s.realReg 58 := by
  simp [setupData,setupAtoms,Atom.effect,instructionEffect,data,Data.machine,shadowReg,hn,hr]
lemma setup_nat_frame (k : ℕ) (hk : 10 ≤ k) : NatFrame setup k := by
  simp only [setup,setupAtoms,List.map_cons,List.map_nil,Structured.sequence,NatFrame,writesNat,shadowReg]
  exact ⟨by omega,by omega,by omega,by omega,by omega,by omega,by omega,not_false,by omega,not_false,trivial⟩
lemma setup_real_frame (k : ℕ) (hk : 10 ≤ k) : RealFrame setup k := by
  simp only [setup,setupAtoms,List.map_cons,List.map_nil,Structured.sequence,RealFrame,writesReal,shadowReg]
  exact ⟨not_false,not_false,not_false,not_false,not_false,not_false,not_false,by omega,not_false,by omega,trivial⟩
lemma setup_memory (s : Data) : (setupData s).realMem = s.realMem ∧ (setupData s).natMem = s.natMem := by
  exact (setup_eval s).no_memory (by simp [setup,setupAtoms,Structured.sequence,NoMemory,NoStore])
lemma call_eval (s : Data) (N : ℕ) (hn : s.natReg 56 = 0) (hr : s.realReg 56 = 0)
    (hnonneg : 0 ≤ s.realReg 58) (hupper : s.realReg 58 ≤ (2 : ℝ)^N) :
    ∃ cost t, Eval call s cost t ∧ t.natReg (shadowReg 3) = s.natReg 58*⌈s.realReg 58⌉₊ ∧
      cost ≤ (dispatchCharge ceilingProgram.code+3)*(16*N+32) ∧
      (∀ address, (∀ a, address ≠ s.natReg 48+2*a+1) →
        t.realMem address = s.realMem address ∧ t.natMem address = s.natMem address) ∧
      ∀ k, 10 ≤ k → Even k → t.natReg k = s.natReg k ∧ t.realReg k = s.realReg k := by
  obtain ⟨h0,h1,h2,h4,h5,h7,hr7,hP,hx⟩ := setup_fields s hn hr
  have hnn : 0 ≤ (setupData s).realReg (shadowReg 0) := by rwa [hx]
  have hup : (setupData s).realReg (shadowReg 0) ≤ (2 : ℝ)^N := by rwa [hx]
  obtain ⟨cost,t,he,hout,hcost,hframe,hregs⟩ := unscaled_ceiling_eval (s.natReg 48) N (setupData s)
    h0 h1 h2 h4 h5 h7 hr7 hnn hup
  refine ⟨10+cost,t,Eval.seq (setup_eval s) he,?_,?_,?_,?_⟩
  · simpa only [hP,hx] using hout
  · have hmult := Nat.mul_le_mul_left (dispatchCharge ceilingProgram.code+2) (show 16*N+15 ≤ 16*N+32 by omega)
    nlinarith only [hcost,hmult]
  · intro address ha
    have hh := hframe address ha
    have hm := setup_memory s
    exact ⟨hh.1.trans (congrFun hm.1 address),hh.2.trans (congrFun hm.2 address)⟩
  · intro k hk heven
    have hh := hregs k hk heven
    exact ⟨hh.1.trans ((setup_eval s).nat_frame (setup_nat_frame k hk)),
      hh.2.trans ((setup_eval s).real_frame (setup_real_frame k hk))⟩
lemma guest_bank_outside_utility_tail (B bank tail a : ℕ) :
    ∀ u, B+bankFactor bank*(2*a+1) ≠ (B+2*tail)+2*u+1 := by
  intro u
  have heq : (B+2*tail)+2*u+1 = B+(2*(tail+u)+1) := by ring
  rw [heq]
  exact guest_bank_ne_host B bank a (tail+u)
end DecrAlmostLinearSSSP.Decremental.ScaledCeiling
end s77
section s78
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.ScaledCeiling
open Structured
lemma call_nat_even (k : ℕ) (hk : 10 ≤ k) (heven : Even k) : NatFrame call k :=
  ⟨setup_nat_frame k hk,shadowInterpreter_nat_even_frame _ k hk heven⟩
lemma call_real_even (k : ℕ) (hk : 10 ≤ k) (heven : Even k) : RealFrame call k :=
  ⟨setup_real_frame k hk,shadowInterpreter_real_even_frame _ k heven⟩
lemma cube_nat_frame (k : ℕ) (hk : 10 ≤ k) (heven : Even k) (h58 : k ≠ 58) : NatFrame cube k :=
  ⟨call_nat_even k hk heven,Ne.symm h58,call_nat_even k hk heven⟩
lemma cube_real_frame (k : ℕ) (hk : 10 ≤ k) (heven : Even k) : RealFrame cube k :=
  ⟨call_real_even k hk heven,not_false,call_real_even k hk heven⟩
lemma cube_eval (s : Data) (m N : ℕ) (hP : s.natReg 58 = m) (hx : s.realReg 58 = (m : ℝ))
    (hn : s.natReg 56 = 0) (hr : s.realReg 56 = 0) (hupper : (m : ℝ) ≤ (2 : ℝ)^N) :
    ∃ cost t, Eval cube s cost t ∧ t.natReg (shadowReg 3) = m^3 ∧
      cost ≤ 2*(dispatchCharge ceilingProgram.code+3)*(16*N+32)+1 ∧
      (∀ address, (∀ a, address ≠ s.natReg 48+2*a+1) →
        t.realMem address = s.realMem address ∧ t.natMem address = s.natMem address) := by
  have hnon : 0 ≤ s.realReg 58 := by rw [hx];exact Nat.cast_nonneg _
  have hup : s.realReg 58 ≤ (2 : ℝ)^N := by rwa [hx]
  obtain ⟨first,a,ha,haout,hacost,haframe,haregs⟩ := call_eval s N hn hr hnon hup
  have ha56 : a.natReg 56 = 0 := (haregs 56 (by omega) (by decide)).1.trans hn
  have har56 : a.realReg 56 = 0 := (haregs 56 (by omega) (by decide)).2.trans hr
  have har58 : a.realReg 58 = (m : ℝ) := (haregs 58 (by omega) (by decide)).2.trans hx
  have ha48 : a.natReg 48 = s.natReg 48 := (haregs 48 (by omega) (by decide)).1
  have haout' : a.natReg (shadowReg 3) = m*m := by simpa only [hP,hx,Nat.ceil_natCast] using haout
  let b : Data := {a with natReg := Function.update a.natReg 58 (a.natReg (shadowReg 3)+a.natReg 56)}
  have hb : Eval (nadd 58 (shadowReg 3) 56) a 1 b := eval_nadd a 58 (shadowReg 3) 56
  have hbP : b.natReg 58 = m*m := by simp [b,haout',ha56]
  have hbN : b.natReg 56 = 0 := by simp [b,ha56]
  have hbR : b.realReg 56 = 0 := har56
  have hbX : b.realReg 58 = (m : ℝ) := har58
  obtain ⟨last,t,ht,htout,htcost,htframe,htregs⟩ := call_eval b N hbN hbR
    (by rw [hbX];exact Nat.cast_nonneg _) (by rwa [hbX])
  refine ⟨first+(1+last),t,Eval.seq ha (Eval.seq hb ht),?_,by nlinarith only [hacost,htcost],?_⟩
  · simpa only [hbP,hbX,Nat.ceil_natCast,pow_succ,pow_two,pow_zero,one_mul] using htout
  · intro address haddr
    have hb48 : b.natReg 48 = s.natReg 48 := by simpa [b] using ha48
    have htail := htframe address (by simpa only [hb48] using haddr)
    have hhead := haframe address haddr
    exact ⟨htail.1.trans hhead.1,htail.2.trans hhead.2⟩
lemma polynomialReserve_eval (s : Data) (m N B : ℕ) (hP : s.natReg 58 = m)
    (hx : s.realReg 58 = (m : ℝ)) (hn : s.natReg 56 = 0) (hr : s.realReg 56 = 0)
    (h26 : s.natReg 26 = 1) (hupper : (m : ℝ) ≤ (2 : ℝ)^N) :
    ∃ cost t, Eval (polynomialReserve B) s cost t ∧ t.natReg 60 = B*m^3+1 ∧
      cost ≤ 2*(dispatchCharge ceilingProgram.code+3)*(16*N+32)+B+3 ∧
      ∀ address, (∀ a, address ≠ s.natReg 48+2*a+1) →
        t.realMem address = s.realMem address ∧ t.natMem address = s.natMem address := by
  obtain ⟨cost,a,ha,haout,hcost,hframe⟩ := cube_eval s m N hP hx hn hr hupper
  have ha26 : a.natReg 26 = 1 := (ha.nat_frame (cube_nat_frame 26 (by omega) (by decide) (by omega))).trans h26
  let b : Data := {a with natReg := Function.update a.natReg 60 (B*a.natReg (shadowReg 3))}
  have hb : Eval (structuredConstant 60 (shadowReg 3) B) a (B+1) b :=
    structuredConstant_eval a 60 (shadowReg 3) B (by decide)
  let t : Data := {b with natReg := Function.update b.natReg 60 (b.natReg 60+b.natReg 26)}
  have ht : Eval (nadd 60 60 26) b 1 t := eval_nadd b 60 60 26
  refine ⟨cost+(B+1+1),t,?_,?_,by omega,?_⟩
  · simpa only [polynomialReserve,Nat.add_assoc] using Eval.seq ha (Eval.seq hb ht)
  · simp [t,b,haout,ha26]
  · exact hframe
end DecrAlmostLinearSSSP.Decremental.ScaledCeiling
end s78
section s79
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s79
section s80
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s80
section s81
set_option autoImplicit false
open Filter
open scoped Topology
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s81
section s82
set_option autoImplicit false
open Filter
open scoped Topology
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s82
section s83
set_option autoImplicit false
open Filter
open scoped Topology
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s83
section s84
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma real_succ_le_two_pow (n : ℕ) : (n : ℝ)+1 ≤ (2 : ℝ)^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Nat.cast_add,Nat.cast_one,pow_succ]
    nlinarith only [ih,(show (0 : ℝ) ≤ n from Nat.cast_nonneg n)]
lemma scale_count_ceiling_argument (i : Input) (hi : i.Valid) :
    0 ≤ logarithm2 ((i.n : ℝ)*i.W) ∧
      logarithm2 ((i.n : ℝ)*i.W) ≤ (2 : ℝ)^scaleCount i := by
  have hn : (1 : ℝ) ≤ i.n := by exact_mod_cast input_vertex_positive i
  have hW : (1 : ℝ) ≤ i.W := by exact_mod_cast hi.2.2.1
  have hprod : (1 : ℝ) ≤ (i.n : ℝ)*i.W := by nlinarith only [hn,hW,mul_nonneg (sub_nonneg.mpr hn) (sub_nonneg.mpr hW)]
  refine ⟨logarithm2_nonneg hprod,?_⟩
  have hc := Nat.le_ceil (logarithm2 ((i.n : ℝ)*i.W))
  have hbound := real_succ_le_two_pow (scaleCount i)
  have heq : (scaleCount i : ℝ) = (⌈logarithm2 ((i.n : ℝ)*i.W)⌉₊ : ℝ)+1 := by
    simp only [scaleCount,Nat.cast_add,Nat.cast_one]
  rw [heq] at hbound
  linarith
lemma scale_count_nat_argument (i : Input) : (scaleCount i : ℝ) ≤ (2 : ℝ)^scaleCount i :=
  (le_add_of_nonneg_right zero_le_one).trans (real_succ_le_two_pow (scaleCount i))
end DecrAlmostLinearSSSP.Decremental
end s84
section s85
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.ScaledCeiling
open Structured
lemma scaleArgument_eval (s : Data) : Eval scaleArgument s 8 (scaleArgumentData s) := eval_sequence_atoms scaleArgumentAtoms s
lemma scaleArgument_fields (s : Data) (i : Input) (hn : s.natReg 66 = i.n) (hW : s.natReg 70 = i.W) :
    (scaleArgumentData s).natReg 58 = 1 ∧
      (scaleArgumentData s).realReg 58 = logarithm2 ((i.n : ℝ)*i.W) ∧
      (scaleArgumentData s).natReg 56 = s.natReg 56 ∧
      (scaleArgumentData s).realReg 56 = s.realReg 56 ∧
      (scaleArgumentData s).natReg 26 = s.natReg 26 := by
  simp [scaleArgumentData,scaleArgumentAtoms,Atom.effect,instructionEffect,data,Data.machine,hn,hW,logarithm2]
lemma countScales_eval (s : Data) (i : Input) (hi : i.Valid) (hn : s.natReg 66 = i.n)
    (hW : s.natReg 70 = i.W) (hz : s.natReg 56 = 0) (hrz : s.realReg 56 = 0) (h1 : s.natReg 26 = 1) :
    ∃ cost t, Eval countScales s cost t ∧ t.natReg 80 = scaleCount i ∧
      cost ≤ (dispatchCharge ceilingProgram.code+4)*(16*scaleCount i+32) ∧
      ∀ address, (∀ a, address ≠ s.natReg 48+2*a+1) →
        t.realMem address = s.realMem address ∧ t.natMem address = s.natMem address := by
  obtain ⟨hP,hx,hz',hrz',h1'⟩ := scaleArgument_fields s i hn hW
  obtain ⟨hnon,hupper⟩ := scale_count_ceiling_argument i hi
  obtain ⟨cost,a,ha,haout,hcost,hframe,hregs⟩ := call_eval (scaleArgumentData s) (scaleCount i)
    (hz'.trans hz) (hrz'.trans hrz) (by rwa [hx]) (by rwa [hx])
  have ha26 : a.natReg 26 = 1 := ((hregs 26 (by omega) (by decide)).1.trans h1').trans h1
  let t : Data := {a with natReg := Function.update a.natReg 80 (a.natReg (shadowReg 3)+a.natReg 26)}
  refine ⟨8+(cost+1),t,Eval.seq (scaleArgument_eval s) (Eval.seq ha (eval_nadd a 80 (shadowReg 3) 26)),?_,?_,?_⟩
  · simp only [t,Function.update_self,ha26,haout,hP,hx,Nat.one_mul,scaleCount]
  · nlinarith only [hcost]
  · intro address hout
    have hbase : (scaleArgumentData s).natReg 48 = s.natReg 48 := by
      simp [scaleArgumentData,scaleArgumentAtoms,Atom.effect,instructionEffect,data,Data.machine]
    have hh := hframe address (by simpa only [hbase] using hout)
    have hm := (scaleArgument_eval s).no_memory (by
      simp [scaleArgument,scaleArgumentAtoms,Structured.sequence,NoMemory,NoStore])
    exact ⟨hh.1.trans (congrFun hm.1 address),hh.2.trans (congrFun hm.2 address)⟩
end DecrAlmostLinearSSSP.Decremental.ScaledCeiling
end s85
section s86
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.ScaledCeiling
open Structured
lemma scaleArea_eval (s : Data) (i : Input) (hn : s.natReg 66 = i.n)
    (hS : s.natReg 80 = scaleCount i) (hz : s.natReg 56 = 0) (hrz : s.realReg 56 = 0) :
    ∃ cost t, Eval scaleArea s cost t ∧ t.natReg 82 = i.n*scaleCount i ∧
      t.natReg 80 = scaleCount i ∧ cost ≤ (dispatchCharge ceilingProgram.code+4)*(16*scaleCount i+32) ∧
      ∀ address, (∀ a, address ≠ s.natReg 48+2*a+1) →
        t.realMem address = s.realMem address ∧ t.natMem address = s.natMem address := by
  let a : Data := {s with natReg := Function.update s.natReg 58 (s.natReg 66+s.natReg 56)}
  let b : Data := {a with realReg := Function.update a.realReg 58 (a.natReg 80 : ℝ)}
  have ha : Eval (nadd 58 66 56) s 1 a := eval_nadd s 58 66 56
  have hb : Eval (cast 58 80) a 1 b := eval_cast a 58 80
  have hbP : b.natReg 58 = i.n := by simp [b,a,hn,hz]
  have hbX : b.realReg 58 = (scaleCount i : ℝ) := by simp [b,a,hS]
  have hbN : b.natReg 56 = 0 := by simp [b,a,hz]
  have hbR : b.realReg 56 = 0 := by simp [b,a,hrz]
  obtain ⟨cost,c,hc,hcout,hcost,hframe,hregs⟩ := call_eval b (scaleCount i) hbN hbR
    (by rw [hbX];exact Nat.cast_nonneg _) (by rw [hbX];exact scale_count_nat_argument i)
  have hc56 : c.natReg 56 = 0 := (hregs 56 (by omega) (by decide)).1.trans hbN
  have hc80 : c.natReg 80 = scaleCount i := by
    have hh := (hregs 80 (by omega) (by decide)).1
    simpa [b,a,hS] using hh
  let t : Data := {c with natReg := Function.update c.natReg 82 (c.natReg (shadowReg 3)+c.natReg 56)}
  have ht : Eval (nadd 82 (shadowReg 3) 56) c 1 t := eval_nadd c 82 (shadowReg 3) 56
  refine ⟨1+(1+(cost+1)),t,Eval.seq ha (Eval.seq hb (Eval.seq hc ht)),?_,?_,?_,?_⟩
  · simp only [t,Function.update_self,hcout,hbP,hbX,Nat.ceil_natCast,hc56,Nat.add_zero]
  · simpa [t] using hc80
  · nlinarith only [hcost]
  · intro address hout
    have hb48 : b.natReg 48 = s.natReg 48 := by simp [b,a]
    exact hframe address (by simpa only [hb48] using hout)
end DecrAlmostLinearSSSP.Decremental.ScaledCeiling
end s86
section s87
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Layout
open Structured
lemma pre_record (s : Data) : (preData s).natReg 84 = 6*s.natReg 66+s.natReg 74+s.natReg 26 := by
  simp [preData,preAtoms,Atom.effect,instructionEffect,data,Data.machine]
  ring
lemma pre_meta (s : Data) (k : ℕ) (h84 : k ≠ 84) (h86 : k ≠ 86) : (preData s).natReg k = s.natReg k := by
  have he := eval_sequence_atoms preAtoms s
  apply he.nat_frame
  simp [preAtoms,Structured.sequence,NatFrame,writesNat,Ne.symm h84,Ne.symm h86]
lemma post_rep (s : Data) : Represents (postData s) (postAddresses s) := by
  simp [Represents,postAddresses,postData,postAtoms,Atom.effect,instructionEffect,data,Data.machine]
lemma code_no_memory (stride : ℕ) : NoMemory (code stride) := by
  simp [code,NoMemory,preAtoms,postAtoms,Structured.sequence,NoStore,structuredConstant,repeatedAdd_no_memory,Structured.natural]
lemma eval_code (s : Data) (B n S reserve stride : ℕ)
    (hB : s.natReg 74 = B) (hn : s.natReg 66 = n) (hS : s.natReg 80 = S)
    (harea : s.natReg 82 = n*S) (hR : s.natReg 60 = reserve) (h1 : s.natReg 26 = 1) :
    ∃ t, Eval (code stride) s (stride+16) t ∧ Represents t (addresses B n S reserve stride) ∧
      t.realMem = s.realMem ∧ t.natMem = s.natMem := by
  have hp : Eval (Structured.sequence (preAtoms.map Cmd.atom)) s 5 (preData s) := eval_sequence_atoms preAtoms s
  let b : Data := {preData s with natReg := Function.update (preData s).natReg 86 (stride*(preData s).natReg 80)}
  have hb : Eval (structuredConstant 86 80 stride) (preData s) (stride+1) b :=
    structuredConstant_eval _ 86 80 stride (by decide)
  have ht : Eval (Structured.sequence (postAtoms.map Cmd.atom)) b 10 (postData b) := eval_sequence_atoms postAtoms b
  have he : Eval (code stride) s (stride+16) (postData b) := by
    simpa only [code,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Eval.seq hp (Eval.seq hb ht)
  have hm := he.no_memory (code_no_memory stride)
  refine ⟨postData b,he,?_,hm⟩
  have hrep := post_rep b
  have haddr : postAddresses b = addresses B n S reserve stride := by
    simp [postAddresses,addresses,b,pre_meta,pre_record,hB,hn,hS,harea,hR,h1]
    all_goals congr 1 <;> omega
  rwa [haddr] at hrep
end DecrAlmostLinearSSSP.Decremental.Layout
end s87
section s88
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
namespace ScaledCeiling
lemma reserve_nat_frame (B k : ℕ) (hk : 10 ≤ k) (hev : Even k) (h58 : k ≠ 58) (h60 : k ≠ 60) :
    NatFrame (polynomialReserve B) k :=
  ⟨cube_nat_frame k hk hev h58,⟨Ne.symm h60,repeatedAdd_nat_frame _ _ _ _ (Ne.symm h60)⟩,Ne.symm h60⟩
lemma reserve_real_frame (B k : ℕ) (hk : 10 ≤ k) (hev : Even k) : RealFrame (polynomialReserve B) k :=
  ⟨cube_real_frame k hk hev,⟨not_false,repeatedAdd_real_frame _ _ _ _⟩,not_false⟩
end ScaledCeiling
namespace Layout
end Layout
end DecrAlmostLinearSSSP.Decremental
end s88
section s89
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s89
section s90
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s90
section s91
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Prepass
open Structured
open ScaledCeiling
end DecrAlmostLinearSSSP.Decremental.Prepass
end s91
section s92
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Fill
open Structured
end DecrAlmostLinearSSSP.Decremental.Fill
end s92
section s93
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.SnapshotFill
open Structured
end DecrAlmostLinearSSSP.Decremental.SnapshotFill
end s93
section s94
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.ScaledCeiling
open Structured
end DecrAlmostLinearSSSP.Decremental.ScaledCeiling
end s94
section s95
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.ScaledCeiling
open Structured
end DecrAlmostLinearSSSP.Decremental.ScaledCeiling
end s95
section s96
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.ScaleParameters
open Structured
end DecrAlmostLinearSSSP.Decremental.ScaleParameters
end s96
section s97
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.ScaleParameters
open Structured
end DecrAlmostLinearSSSP.Decremental.ScaleParameters
end s97
section s98
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.ScaleParameters
open Structured
end DecrAlmostLinearSSSP.Decremental.ScaleParameters
end s98
section s99
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.ScaleParameters
open Structured
end DecrAlmostLinearSSSP.Decremental.ScaleParameters
end s99
section s100
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.ScaleParameters
open Structured
end DecrAlmostLinearSSSP.Decremental.ScaleParameters
end s100
section s101
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s101
section s102
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end s102
section s103
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end s103
section s104
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.ScaledCeiling
open Structured
end DecrAlmostLinearSSSP.Decremental.ScaledCeiling
end s104
section s105
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.TapeCopy
open Structured
end DecrAlmostLinearSSSP.Decremental.TapeCopy
end s105
section s106
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.TapeCopy
open Structured
end DecrAlmostLinearSSSP.Decremental.TapeCopy
end s106
section s107
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.TapeCopy
open Structured
end DecrAlmostLinearSSSP.Decremental.TapeCopy
end s107
section s108
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.SourceMemory
open Structured
end DecrAlmostLinearSSSP.Decremental.SourceMemory
end s108
section s109
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.TapeCopy
open Structured
end DecrAlmostLinearSSSP.Decremental.TapeCopy
end s109
section s110
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.TapeCopy
open Structured
end DecrAlmostLinearSSSP.Decremental.TapeCopy
end s110
section s111
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.TapeCopy
open Structured
end DecrAlmostLinearSSSP.Decremental.TapeCopy
end s111
section s112
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.TapeCopy
open Structured
end DecrAlmostLinearSSSP.Decremental.TapeCopy
end s112
section s113
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.RecordHeader
open Structured
end DecrAlmostLinearSSSP.Decremental.RecordHeader
end s113
section s114
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end s114
section s115
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end s115
section s116
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
namespace ScaledCeiling
end ScaledCeiling
namespace Layout
end Layout
namespace Prepass
end Prepass
end DecrAlmostLinearSSSP.Decremental
end s116
section s117
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Layout
open Structured
end DecrAlmostLinearSSSP.Decremental.Layout
end s117
section s118
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.TapeCopy
open Structured
end DecrAlmostLinearSSSP.Decremental.TapeCopy
end s118
section s119
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.RegisterSave
open Structured
end DecrAlmostLinearSSSP.Decremental.RegisterSave
end s119
section s120
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.RegisterSave
open Structured
end DecrAlmostLinearSSSP.Decremental.RegisterSave
end s120
section s121
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.RegisterSave
open Structured
end DecrAlmostLinearSSSP.Decremental.RegisterSave
end s121
section s122
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.SourceSetup
open Structured
open RegisterSave
end DecrAlmostLinearSSSP.Decremental.SourceSetup
end s122
section s123
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end s123
section s124
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end s124
section s125
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
namespace RegisterSave
end RegisterSave
namespace SourceSetup
end SourceSetup
end DecrAlmostLinearSSSP.Decremental
end s125
section s126
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.SourceSnapshot
open Structured
open RegisterSave
end DecrAlmostLinearSSSP.Decremental.SourceSnapshot
end s126
section s127
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.SourceCall
open Structured
end DecrAlmostLinearSSSP.Decremental.SourceCall
end s127
section s128
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.ExtendedMax
open Structured
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental.ExtendedMax
end s128
section s129
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.ScaledReadout
open Structured
end DecrAlmostLinearSSSP.Decremental.ScaledReadout
end s129
section s130
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CacheCopy
open Structured
end DecrAlmostLinearSSSP.Decremental.CacheCopy
end s130
section s131
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CacheCopy
open Structured
end DecrAlmostLinearSSSP.Decremental.CacheCopy
end s131
section s132
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.CacheCopy
open Structured
end DecrAlmostLinearSSSP.Decremental.CacheCopy
end s132
section s133
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CacheCopy
open Structured
end DecrAlmostLinearSSSP.Decremental.CacheCopy
end s133
section s134
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s134
section s135
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Prepass
open Structured ScaledCeiling
end DecrAlmostLinearSSSP.Decremental.Prepass
end s135
section s136
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s136
section s137
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s137
section s138
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s138
section s139
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s139
section s140
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.TapeCopy
end DecrAlmostLinearSSSP.Decremental.TapeCopy
end s140
section s141
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.TapeCopy
end DecrAlmostLinearSSSP.Decremental.TapeCopy
end s141
section s142
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.TapeCopy
open Structured
end DecrAlmostLinearSSSP.Decremental.TapeCopy
end s142
section s143
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.TapeCopy
open Structured
end DecrAlmostLinearSSSP.Decremental.TapeCopy
end s143
section s144
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end s144
section s145
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s145
section s146
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s146
section s147
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s147
section s148
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s148
section s149
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s149
section s150
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.SourceCall
open Structured
end DecrAlmostLinearSSSP.Decremental.SourceCall
end s150
section s151
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
namespace CacheCopy
end CacheCopy
namespace Native
end Native
end DecrAlmostLinearSSSP.Decremental
end s151
section s152
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Native
end DecrAlmostLinearSSSP.Decremental.Native
end s152
section s153
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s153
section s154
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s154
section s155
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s155
section s156
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s156
section s157
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Layout
end DecrAlmostLinearSSSP.Decremental.Layout
end s157
section s158
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Native
end DecrAlmostLinearSSSP.Decremental.Native
end s158
section s159
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s159
section s160
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Native
end DecrAlmostLinearSSSP.Decremental.Native
end s160
section s161
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s161
section s162
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s162
section s163
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s163
section s164
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
end DecrAlmostLinearSSSP.Decremental.Native
end s164
section s165
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s165
section s166
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s166
section s167
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s167
section s168
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s168
section s169
set_option autoImplicit false
open scoped ENNReal NNReal
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s169
section s170
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s170
section s171
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.LinkedScan
open Structured
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental.LinkedScan
end s171
section s172
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.LinkedScan
open Structured
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental.LinkedScan
end s172
section s173
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.LinkedScan
open Structured
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental.LinkedScan
end s173
section s174
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s174
section s175
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s175
section s176
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s176
section s177
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.LinkedScan
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental.LinkedScan
end s177
section s178
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental.Native
end s178
section s179
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.LinkedScan
open Structured
end DecrAlmostLinearSSSP.Decremental.LinkedScan
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s179
section s180
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.DirtyMark
open Structured
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental.DirtyMark
end s180
section s181
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s181
section s182
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s182
section s183
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s183
section s184
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s184
section s185
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Native
end DecrAlmostLinearSSSP.Decremental.Native
end s185
section s186
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s186
section s187
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s187
section s188
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s188
section s189
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s189
section s190
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s190
section s191
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.PointerRead
open Structured
end DecrAlmostLinearSSSP.Decremental.PointerRead
end s191
section s192
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.SelectedRead
open Structured
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental.SelectedRead
end s192
section s193
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.AnswerTable
open Structured
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental.AnswerTable
end s193
section s194
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental.Native
end s194
section s195
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s195
section s196
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.DirtyCommit
open Structured
end DecrAlmostLinearSSSP.Decremental.DirtyCommit
end s196
section s197
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.DirtyCommit
open Structured
end DecrAlmostLinearSSSP.Decremental.DirtyCommit
end s197
section s198
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.DirtyCommit
open Structured
end DecrAlmostLinearSSSP.Decremental.DirtyCommit
end s198
section s199
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
namespace SelectedRead
end SelectedRead
namespace DirtyCommit
end DirtyCommit
namespace Native
end Native
end DecrAlmostLinearSSSP.Decremental
end s199
section s200
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s200
section s201
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s201
section s202
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s202
section s203
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s203
section s204
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s204
section s205
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s205
section s206
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s206
section s207
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s207
section s208
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s208
section s209
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s209
section s210
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s210
section s211
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s211
section s212
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s212
section s213
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s213
section s214
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s214
section s215
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s215
section s216
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
end DecrAlmostLinearSSSP.Decremental.Native
end s216
section s217
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s217
section s218
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s218
section s219
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s219
section s220
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s220
section s221
set_option autoImplicit false
open Filter
open scoped Topology
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s221
section s222
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s222
section s223
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Native
end DecrAlmostLinearSSSP.Decremental.Native
end s223
section s224
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
namespace CacheRefresh
end CacheRefresh
end DecrAlmostLinearSSSP.Decremental.Native
end s224
section s225
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s225
section s226
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s226
section s227
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
namespace PointerRefresh
end PointerRefresh
end DecrAlmostLinearSSSP.Decremental.Native
end s227
section s228
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
open Structured
namespace Native
end Native
end DecrAlmostLinearSSSP.Decremental
end s228
section s229
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s229
section s230
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s230
section s231
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s231
section s232
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end s232
section s233
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s233
section s234
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s234
section s235
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s235
section s236
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end s236
section s237
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s237
section s238
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s238
section s239
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s239
section s240
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.ReportDecode
open Structured
end DecrAlmostLinearSSSP.Decremental.ReportDecode
end s240
section s241
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s241
section s242
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s242
section s243
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
namespace ReportConsume
end ReportConsume
end DecrAlmostLinearSSSP.Decremental.Native
end s243
section s244
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
namespace ReportConsume
end ReportConsume
end DecrAlmostLinearSSSP.Decremental.Native
end s244
section s245
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s245
section s246
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s246
section s247
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s247
section s248
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s248
section s249
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s249
section s250
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
namespace ReportConsume
end ReportConsume
end DecrAlmostLinearSSSP.Decremental.Native
end s250
section s251
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
namespace ReportConsume
end ReportConsume
end DecrAlmostLinearSSSP.Decremental.Native
end s251
section s252
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
namespace ReportConsume
end ReportConsume
end DecrAlmostLinearSSSP.Decremental.Native
end s252
section s253
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
namespace ReportConsume
end ReportConsume
end DecrAlmostLinearSSSP.Decremental.Native
end s253
section s254
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
namespace ReportConsume
end ReportConsume
end DecrAlmostLinearSSSP.Decremental.Native
end s254
section s255
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
namespace ReportConsume
end ReportConsume
end DecrAlmostLinearSSSP.Decremental.Native
end s255
section s256
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
namespace ReportConsume
end ReportConsume
end DecrAlmostLinearSSSP.Decremental.Native
end s256
section s257
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
namespace UpdateHeader
end UpdateHeader
end DecrAlmostLinearSSSP.Decremental.Native
end s257
section s258
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
namespace SavedDeletion
end SavedDeletion
end DecrAlmostLinearSSSP.Decremental.Native
end s258
section s259
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end s259
section s260
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end s260
section s261
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end s261
section s262
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end s262
section s263
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.ObservedSourceCall
open Structured
end DecrAlmostLinearSSSP.Decremental.ObservedSourceCall
end s263
section s264
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.ObservedSourceCall
open Structured
end DecrAlmostLinearSSSP.Decremental.ObservedSourceCall
end s264
section s265
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.ObservedSourceCall
open Structured
end DecrAlmostLinearSSSP.Decremental.ObservedSourceCall
end s265
section s266
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s266
section s267
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s267
section s268
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s268
section s269
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s269
section s270
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s270
section s271
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s271
section s272
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s272
section s273
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Native
end DecrAlmostLinearSSSP.Decremental.Native
end s273
section s274
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s274
section s275
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s275
section s276
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s276
section s277
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s277
section s278
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s278
section s279
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
namespace ReportConsume
end ReportConsume
end DecrAlmostLinearSSSP.Decremental.Native
end s279
section s280
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
end DecrAlmostLinearSSSP.Decremental.Native
end s280
section s281
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
namespace UpdateTraversal
end UpdateTraversal
end DecrAlmostLinearSSSP.Decremental.Native
end s281
section s282
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s282
section s283
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s283
section s284
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s284
section s285
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s285
section s286
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
end DecrAlmostLinearSSSP.Decremental.Native
end s286
section s287
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s287
section s288
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.DirtyCommit
open Structured
end DecrAlmostLinearSSSP.Decremental.DirtyCommit
end s288
section s289
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s289
section s290
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s290
section s291
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s291
section s292
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s292
section s293
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s293
section s294
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s294
section s295
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s295
section s296
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s296
section s297
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
end DecrAlmostLinearSSSP.Decremental.Native
end s297
section s298
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
end DecrAlmostLinearSSSP.Decremental.Native
end s298
section s299
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
end DecrAlmostLinearSSSP.Decremental.Native
end s299
section s300
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s300
section s301
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s301
section s302
set_option autoImplicit false
open Filter
open scoped Topology
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s302
section s303
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
end DecrAlmostLinearSSSP.Decremental.Native
end s303
section s304
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s304
section s305
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s305
section s306
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
end DecrAlmostLinearSSSP.Decremental.Native
end s306
section s307
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
end DecrAlmostLinearSSSP.Decremental.Native
end s307
section s308
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Native
end s308
open DecrAlmostLinearSSSP.Decremental
set_option autoImplicit false
theorem solution : (((((((∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    ∀ (host : DecrAlmostLinearSSSP.Decremental.Program) (a : Nat),
      @Eq.{1} Bool c.halted Bool.false →
        @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
          @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) base →
            @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) F →
              @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                  (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                    DecrAlmostLinearSSSP.Decremental.Instruction
                    (fun as i =>
                      @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                    (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code c.pc)
                  (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                    (DecrAlmostLinearSSSP.Decremental.Instruction.natural
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.pc
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
                @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                    (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                      DecrAlmostLinearSSSP.Decremental.Instruction
                      (fun as i =>
                        @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                      (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                      (DecrAlmostLinearSSSP.Decremental.Instruction.nadd
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                  @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                      (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                        DecrAlmostLinearSSSP.Decremental.Instruction
                        (fun as i =>
                          @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                        (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                        (DecrAlmostLinearSSSP.Decremental.Instruction.nadd
                          (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                          (DecrAlmostLinearSSSP.Decremental.shadowReg a)
                          (DecrAlmostLinearSSSP.Decremental.shadowReg a))) →
                    @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                          DecrAlmostLinearSSSP.Decremental.Instruction
                          (fun as i =>
                            @LT.lt.{0} Nat instLTNat i
                              (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                          (DecrAlmostLinearSSSP.Decremental.Instruction.nadd
                            (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                            (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) →
                      @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                          (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                            DecrAlmostLinearSSSP.Decremental.Instruction
                            (fun as i =>
                              @LT.lt.{0} Nat instLTNat i
                                (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                            (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
                          (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                            (DecrAlmostLinearSSSP.Decremental.Instruction.nadd
                              (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                              (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                              (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))) →
                        @Eq.{1} Nat
                          ((DecrAlmostLinearSSSP.Decremental.execute host c
                                (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))).natReg
                            (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (g.natReg a))
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) ∧ (∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    ∀ (host : DecrAlmostLinearSSSP.Decremental.Program) (width offset returnPC : Nat),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) width →
        @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) F →
          ∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
            @LE.le.{0} Nat instLENat
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (DecrAlmostLinearSSSP.Decremental.naturalConstant ins)
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                width →
              @Eq.{1} Bool c.halted Bool.false →
                @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                  @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) base →
                    @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) F →
                      @Eq.{1} Nat c.pc
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) width g.pc)) →
                        (∀ (slot : Nat),
                            @LT.lt.{0} Nat instLTNat slot width →
                              @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                                (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                                  Nat DecrAlmostLinearSSSP.Decremental.Instruction
                                  (fun as i =>
                                    @LT.lt.{0} Nat instLTNat i
                                      (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                                  (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                                  host.code (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc slot))
                                (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                                  Nat DecrAlmostLinearSSSP.Decremental.Instruction
                                  (fun as i =>
                                    @LT.lt.{0} Nat instLTNat i
                                      (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                                  (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                                  (DecrAlmostLinearSSSP.Decremental.shadowBlock width offset returnPC g.pc ins) slot)) →
                          ∀ (address : Nat),
                            DecrAlmostLinearSSSP.Decremental.OutsideBank base F address →
                              And
                                (@Eq.{1} Real
                                  ((DecrAlmostLinearSSSP.Decremental.execute host c
                                        (DecrAlmostLinearSSSP.Decremental.shadowSteps ins g)).realMem
                                    address)
                                  (c.realMem address))
                                (@Eq.{1} Nat
                                  ((DecrAlmostLinearSSSP.Decremental.execute host c
                                        (DecrAlmostLinearSSSP.Decremental.shadowSteps ins g)).natMem
                                    address)
                                  (c.natMem address)))) ∧ ((∀ (base F : Nat) (c : DecrAlmostLinearSSSP.Decremental.Machine),
  DecrAlmostLinearSSSP.Decremental.PreservesOutside base F c c) ∧ (∀ {base F : Nat} {c d e : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.PreservesOutside base F c d →
    DecrAlmostLinearSSSP.Decremental.PreservesOutside base F d e →
      DecrAlmostLinearSSSP.Decremental.PreservesOutside base F c e))) ∧ (((∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    ∀ (host guest : DecrAlmostLinearSSSP.Decremental.Program) (width offset returnPC : Nat),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) width →
        (∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
            @Membership.mem.{0, 0} DecrAlmostLinearSSSP.Decremental.Instruction
                (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                (@List.instMembership.{0} DecrAlmostLinearSSSP.Decremental.Instruction) guest.code ins →
              @LE.le.{0} Nat instLENat
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (DecrAlmostLinearSSSP.Decremental.naturalConstant ins)
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                width) →
          DecrAlmostLinearSSSP.Decremental.ShadowEmbedsCode host guest width offset returnPC →
            @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) F →
              @Eq.{1} Bool c.halted Bool.false →
                @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                  @Eq.{1} Bool g.halted Bool.false →
                    @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) base →
                      @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) F →
                        @Eq.{1} Real (c.realReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                            (@Nat.cast.{0} Real Real.instNatCast F) →
                          @Eq.{1} Nat c.pc
                              (DecrAlmostLinearSSSP.Decremental.shadowDestination width offset returnPC g) →
                            ∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
                              @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                                  (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                                    Nat DecrAlmostLinearSSSP.Decremental.Instruction
                                    (fun as i =>
                                      @LT.lt.{0} Nat instLTNat i
                                        (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                                    (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                                    guest.code g.pc)
                                  (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins) →
                                ∃ steps d,
                                  And (@LE.le.{0} Nat instLENat steps width)
                                    (And
                                      (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                                        (DecrAlmostLinearSSSP.Decremental.execute host c steps) d)
                                      (And
                                        (DecrAlmostLinearSSSP.Decremental.ShadowRep base F d
                                          (DecrAlmostLinearSSSP.Decremental.step guest g))
                                        (And
                                          (@Eq.{1} Nat d.pc
                                            (DecrAlmostLinearSSSP.Decremental.shadowDestination width offset returnPC
                                              (DecrAlmostLinearSSSP.Decremental.step guest g)))
                                          (And
                                            (@Eq.{1} Nat d.work
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                                                steps))
                                            (And (@Eq.{1} Bool d.halted Bool.false)
                                              (And
                                                (@Eq.{1} Nat
                                                  (d.natReg
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                  (c.natReg
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                                                (And
                                                  (@Eq.{1} Nat
                                                    (d.natReg
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                                    (c.natReg
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                  (And
                                                    (@Eq.{1} Nat
                                                      (d.natReg
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                                                      (c.natReg
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                                                    (And
                                                      (@Eq.{1} Real
                                                        (d.realReg
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                                                        (c.realReg
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 7)
                                                            (instOfNatNat (nat_lit 7)))))
                                                      (DecrAlmostLinearSSSP.Decremental.PreservesOutside base F c
                                                        d))))))))))) ∧ (∀ (host guest : DecrAlmostLinearSSSP.Decremental.Program) (width offset returnPC : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) width →
    (∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
        @Membership.mem.{0, 0} DecrAlmostLinearSSSP.Decremental.Instruction
            (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
            (@List.instMembership.{0} DecrAlmostLinearSSSP.Decremental.Instruction) guest.code ins →
          @LE.le.{0} Nat instLENat
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (DecrAlmostLinearSSSP.Decremental.naturalConstant ins)
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            width) →
      DecrAlmostLinearSSSP.Decremental.ShadowEmbedsCode host guest width offset returnPC →
        ∀ (base F : Nat),
          @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) F →
            ∀ (t : Nat) (c g : DecrAlmostLinearSSSP.Decremental.Machine),
              DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
                @Eq.{1} Bool c.halted Bool.false →
                  @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                    @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) base →
                      @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) F →
                        @Eq.{1} Real (c.realReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                            (@Nat.cast.{0} Real Real.instNatCast F) →
                          @Eq.{1} Nat c.pc
                              (DecrAlmostLinearSSSP.Decremental.shadowDestination width offset returnPC g) →
                            (∀ (j : Nat),
                                @LT.lt.{0} Nat instLTNat j t →
                                  @Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.execute guest g j).halted Bool.false →
                                    ∃ ins,
                                      @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                                        (@GetElem?.getElem?.{0, 0, 0}
                                          (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                                          DecrAlmostLinearSSSP.Decremental.Instruction
                                          (fun as i =>
                                            @LT.lt.{0} Nat instLTNat i
                                              (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                                          (@List.instGetElem?NatLtLength.{0}
                                            DecrAlmostLinearSSSP.Decremental.Instruction)
                                          guest.code (DecrAlmostLinearSSSP.Decremental.execute guest g j).pc)
                                        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins)) →
                              ∃ steps d,
                                And
                                  (@LE.le.{0} Nat instLENat steps
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) width t))
                                  (And
                                    (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                                      (DecrAlmostLinearSSSP.Decremental.execute host c steps) d)
                                    (And
                                      (DecrAlmostLinearSSSP.Decremental.ShadowRep base F d
                                        (DecrAlmostLinearSSSP.Decremental.execute guest g t))
                                      (And
                                        (@Eq.{1} Nat d.pc
                                          (DecrAlmostLinearSSSP.Decremental.shadowDestination width offset returnPC
                                            (DecrAlmostLinearSSSP.Decremental.execute guest g t)))
                                        (And
                                          (@Eq.{1} Nat d.work
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                                              steps))
                                          (And (@Eq.{1} Bool d.halted Bool.false)
                                            (And
                                              (@Eq.{1} Nat
                                                (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                (c.natReg
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                                              (And
                                                (@Eq.{1} Nat
                                                  (d.natReg
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                                  (c.natReg
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                (And
                                                  (@Eq.{1} Nat
                                                    (d.natReg
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                                                    (c.natReg
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                                                  (And
                                                    (@Eq.{1} Real
                                                      (d.realReg
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                                                      (c.realReg
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                                                    (DecrAlmostLinearSSSP.Decremental.PreservesOutside base F c
                                                      d)))))))))))) ∧ ((∀ (host guest : DecrAlmostLinearSSSP.Decremental.Program) (offset returnPC : Nat),
  DecrAlmostLinearSSSP.Decremental.ShadowEmbedsCode host guest (DecrAlmostLinearSSSP.Decremental.shadowWidth guest.code)
      offset returnPC →
    ∀ (base F : Nat),
      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) F →
        ∀ (c g final : DecrAlmostLinearSSSP.Decremental.Machine),
          DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
            @Eq.{1} Bool c.halted Bool.false →
              @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) base →
                  @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) F →
                    @Eq.{1} Real (c.realReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                        (@Nat.cast.{0} Real Real.instNatCast F) →
                      @Eq.{1} Nat c.pc
                          (DecrAlmostLinearSSSP.Decremental.shadowDestination
                            (DecrAlmostLinearSSSP.Decremental.shadowWidth guest.code) offset returnPC g) →
                        DecrAlmostLinearSSSP.Decremental.Ends guest g final →
                          ∃ steps d,
                            And
                              (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                                (DecrAlmostLinearSSSP.Decremental.execute host c steps) d)
                              (And (DecrAlmostLinearSSSP.Decremental.ShadowRep base F d final)
                                (And (@Eq.{1} Nat d.pc returnPC)
                                  (And
                                    (@LE.le.{0} Nat instLENat d.work
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (DecrAlmostLinearSSSP.Decremental.shadowWidth guest.code)
                                          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) final.work
                                            g.work))))
                                    (And (@Eq.{1} Bool d.halted Bool.false)
                                      (And
                                        (@Eq.{1} Nat
                                          (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                          (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                                        (And
                                          (@Eq.{1} Nat
                                            (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                            (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                          (And
                                            (@Eq.{1} Nat
                                              (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                                              (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                                            (And
                                              (@Eq.{1} Real
                                                (d.realReg
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                                                (c.realReg
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                                              (DecrAlmostLinearSSSP.Decremental.PreservesOutside base F c d)))))))))) ∧ ((@Eq.{1} Nat
  (DecrAlmostLinearSSSP.Decremental.shadowWidth DecrAlmostLinearSSSP.Decremental.ScaledCeiling.ceilingProgram.code)
  (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))) ∧ (∀ (host : DecrAlmostLinearSSSP.Decremental.Program) (offset returnPC base N : Nat)
  (c g : DecrAlmostLinearSSSP.Decremental.Machine),
  DecrAlmostLinearSSSP.Decremental.ShadowEmbedsCode host DecrAlmostLinearSSSP.Decremental.ScaledCeiling.ceilingProgram
      (DecrAlmostLinearSSSP.Decremental.shadowWidth DecrAlmostLinearSSSP.Decremental.ScaledCeiling.ceilingProgram.code)
      offset returnPC →
    DecrAlmostLinearSSSP.Decremental.ShadowRep base (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) c g →
      @Eq.{1} Bool c.halted Bool.false →
        @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
          @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) base →
            @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
              @Eq.{1} Real (c.realReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))) →
                @Eq.{1} Nat c.pc offset →
                  @Eq.{1} Nat g.pc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                    @Eq.{1} Bool g.halted Bool.false →
                      @Eq.{1} Bool g.fault Bool.false →
                        @LE.le.{0} Real Real.instLE
                            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                            (g.realReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
                          @LE.le.{0} Real Real.instLE
                              (g.realReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                              (@HPow.hPow.{0, 0, 0} Real Nat Real
                                (@instHPow.{0, 0} Real Nat
                                  (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                                (@OfNat.ofNat.{0} Real (nat_lit 2)
                                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                    (@Nat.instAtLeastTwoHAddOfNat
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                      (@Nat.instNeZeroSucc
                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                                N) →
                            ∃ steps d,
                              And
                                (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                                  (DecrAlmostLinearSSSP.Decremental.execute host c steps) d)
                                (And (@Eq.{1} Nat d.pc returnPC)
                                  (And
                                    (@Eq.{1} Nat
                                      (d.natReg
                                        (DecrAlmostLinearSSSP.Decremental.shadowReg
                                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                          (g.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                                        (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
                                          (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder
                                            Real.instFloorRing)
                                          (g.realReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                                    (And
                                      (@LE.le.{0} Nat instLENat d.work
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16))) N)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))))))
                                      (And (@Eq.{1} Bool d.halted Bool.false)
                                        (DecrAlmostLinearSSSP.Decremental.PreservesOutside base
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) c d)))))))))) ∧ ((((∀ {B F : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F s g →
    ∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction) (a : DecrAlmostLinearSSSP.Decremental.Structured.Atom),
      @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (DecrAlmostLinearSSSP.Decremental.shadowScalarTranslation ins)
          (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction a.instruction) →
        ∃ cost t,
          And
            (DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.Cmd.atom a) s
              cost t)
            (And (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F t
                (DecrAlmostLinearSSSP.Decremental.instructionEffect ins g)))) ∧ (∀ {B F : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F s g →
    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) F →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) B →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) F →
          @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
              (@Nat.cast.{0} Real Real.instNatCast F) →
            ∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
              ∃ cost t,
                And
                  (DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.shadowAction ins)
                    s cost t)
                  (And (@LE.le.{0} Nat instLENat cost (DecrAlmostLinearSSSP.Decremental.actionBound ins))
                    (DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F t
                      (DecrAlmostLinearSSSP.Decremental.instructionEffect ins g))))) ∧ ((∀ (d factor q : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.NoMemory (DecrAlmostLinearSSSP.Decremental.repeatedAdd d factor q)) ∧ (∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
  DecrAlmostLinearSSSP.Decremental.Structured.NoStore ins →
    DecrAlmostLinearSSSP.Decremental.Structured.NoMemory (DecrAlmostLinearSSSP.Decremental.shadowAction ins)))) ∧ (((∀ {B F : Nat} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F s g →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) B →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) F →
        ∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction) (cost : Nat),
          DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.shadowAction ins) s cost
              t →
            ∀ (address : Nat),
              (∀ (a : Nat),
                  @Ne.{1} Nat address
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) →
                And (@Eq.{1} Real (t.realMem address) (s.realMem address))
                  (@Eq.{1} Nat (t.natMem address) (s.natMem address))) ∧ (∀ {cmd : DecrAlmostLinearSSSP.Decremental.Structured.Cmd} {k : Nat},
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame cmd k →
    DecrAlmostLinearSSSP.Decremental.Structured.FlagFrame cmd k)) ∧ ((∀ {cmd : DecrAlmostLinearSSSP.Decremental.Structured.Cmd} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {cost k : Nat},
  DecrAlmostLinearSSSP.Decremental.Structured.Eval cmd s cost t →
    DecrAlmostLinearSSSP.Decremental.Structured.FlagFrame cmd k →
      @LE.le.{0} Nat instLENat (s.natReg k) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
        @LE.le.{0} Nat instLENat (t.natReg k) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) ∧ ((∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction) (k : Nat),
  @LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) →
    @Ne.{1} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k →
      @Ne.{1} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) k →
        @Ne.{1} Nat (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) k →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.shadowAction ins) k) ∧ (∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction) (k : Nat),
  @LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.shadowAction ins) k)))))) ∧ (((((∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
  @Ne.{1} DecrAlmostLinearSSSP.Decremental.Instruction ins DecrAlmostLinearSSSP.Decremental.Instruction.halt →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.shadowAction ins)
      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) ∧ (∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
  DecrAlmostLinearSSSP.Decremental.Structured.FlagFrame (DecrAlmostLinearSSSP.Decremental.shadowAction ins)
    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))) ∧ ((∀ {B F : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F s g →
    ∀ (x : Nat),
      DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F
        { realReg := s.realReg,
          natReg :=
            @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) x,
          realMem := s.realMem, natMem := s.natMem }
        g) ∧ (∀ {B F : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F s g →
    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) F →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) B →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) F →
            @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                (@Nat.cast.{0} Real Real.instNatCast F) →
              ∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
                ∃ cost t,
                  And
                    (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                      (DecrAlmostLinearSSSP.Decremental.shadowInstruction g.pc ins) s cost t)
                    (And
                      (@LE.le.{0} Nat instLENat cost
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (DecrAlmostLinearSSSP.Decremental.actionBound ins)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F t
                        (DecrAlmostLinearSSSP.Decremental.instructionEffect ins
                          {
                            pc :=
                              @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.pc
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))),
                            realReg := g.realReg, natReg := g.natReg, realMem := g.realMem, natMem := g.natMem,
                            halted := g.halted, fault := g.fault,
                            work :=
                              @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.work
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) })))))) ∧ (((∀ {B F : Nat} (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (start : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (g : DecrAlmostLinearSSSP.Decremental.Machine),
  DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F s g →
    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) F →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) B →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) F →
            @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                (@Nat.cast.{0} Real Real.instNatCast F) →
              @LE.le.{0} Nat instLENat start g.pc →
                ∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
                  @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                      (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                        DecrAlmostLinearSSSP.Decremental.Instruction
                        (fun as i =>
                          @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                        (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) code
                        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) g.pc start))
                      (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins) →
                    ∃ cost t,
                      And
                        (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                          (DecrAlmostLinearSSSP.Decremental.dispatchAux start code) s cost t)
                        (And (@LE.le.{0} Nat instLENat cost (DecrAlmostLinearSSSP.Decremental.dispatchCharge code))
                          (DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F t
                            (DecrAlmostLinearSSSP.Decremental.instructionEffect ins
                              {
                                pc :=
                                  @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.pc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))),
                                realReg := g.realReg, natReg := g.natReg, realMem := g.realMem, natMem := g.natMem,
                                halted := g.halted, fault := g.fault,
                                work :=
                                  @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.work
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) })))) ∧ (∀ {B F : Nat} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F s g →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) B →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) F →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
          ∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction) (cost : Nat),
            DecrAlmostLinearSSSP.Decremental.Structured.Eval
                (DecrAlmostLinearSSSP.Decremental.shadowInstruction g.pc ins) s cost t →
              ∀ (address : Nat),
                (∀ (a : Nat),
                    @Ne.{1} Nat address
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) →
                  And (@Eq.{1} Real (t.realMem address) (s.realMem address))
                    (@Eq.{1} Nat (t.natMem address) (s.natMem address)))) ∧ ((∀ {B F : Nat} (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (pc : Nat)
  (s t : DecrAlmostLinearSSSP.Decremental.Structured.Data) (g : DecrAlmostLinearSSSP.Decremental.Machine),
  DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F s g →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) B →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) F →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
          @LE.le.{0} Nat instLENat pc g.pc →
            ∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
              @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                  (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                    DecrAlmostLinearSSSP.Decremental.Instruction
                    (fun as i =>
                      @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                    (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) code
                    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) g.pc pc))
                  (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins) →
                ∀ (cost : Nat),
                  DecrAlmostLinearSSSP.Decremental.Structured.Eval
                      (DecrAlmostLinearSSSP.Decremental.dispatchAux pc code) s cost t →
                    ∀ (address : Nat),
                      (∀ (a : Nat),
                          @Ne.{1} Nat address
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) →
                        And (@Eq.{1} Real (t.realMem address) (s.realMem address))
                          (@Eq.{1} Nat (t.natMem address) (s.natMem address))) ∧ ((∀ (pc : Nat) (ins : DecrAlmostLinearSSSP.Decremental.Instruction) (k : Nat),
  Or (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (Or (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.shadowInstruction pc ins) k) ∧ (∀ (pc : Nat) (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.shadowInstruction pc ins)
    (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))))) ∧ ((((∀ (pc : Nat) (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
  DecrAlmostLinearSSSP.Decremental.Structured.FlagFrame (DecrAlmostLinearSSSP.Decremental.shadowInstruction pc ins)
    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) ∧ (∀ (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (start k : Nat),
  Or (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (Or (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.dispatchAux start code) k)) ∧ ((∀ (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (start : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.dispatchAux start code)
    (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) ∧ ((∀ (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (start : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.FlagFrame (DecrAlmostLinearSSSP.Decremental.dispatchAux start code)
    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) ∧ (∀ {B F : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F s g →
    @LE.le.{0} Nat instLENat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        (@ite.{1} Nat (@Eq.{1} Bool g.halted Bool.true) (instDecidableEqBool g.halted Bool.true)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))) ∧ (((∀ (guest : DecrAlmostLinearSSSP.Decremental.Program) (t B F : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) F →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (g : DecrAlmostLinearSSSP.Decremental.Machine),
      DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F s g →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) B →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) F →
              @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                  (@Nat.cast.{0} Real Real.instNatCast F) →
                @LE.le.{0} Nat instLENat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                  (∀ (j : Nat),
                      @LT.lt.{0} Nat instLTNat j t →
                        @Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.execute guest g j).halted Bool.false →
                          ∃ ins,
                            @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                              (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                                DecrAlmostLinearSSSP.Decremental.Instruction
                                (fun as i =>
                                  @LT.lt.{0} Nat instLTNat i
                                    (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                                (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                                guest.code (DecrAlmostLinearSSSP.Decremental.execute guest g j).pc)
                              (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins)) →
                    @Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.execute guest g t).halted Bool.true →
                      ∃ cost u,
                        And
                          (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                            (DecrAlmostLinearSSSP.Decremental.shadowInterpreter guest.code) s cost u)
                          (And
                            (@LE.le.{0} Nat instLENat cost
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (DecrAlmostLinearSSSP.Decremental.dispatchCharge guest.code)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  t)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                            (DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F u
                              (DecrAlmostLinearSSSP.Decremental.execute guest g t)))) ∧ (∀ (guest : DecrAlmostLinearSSSP.Decremental.Program) (B F : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) F →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (g final : DecrAlmostLinearSSSP.Decremental.Machine),
      DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F s g →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) B →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) F →
              @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                  (@Nat.cast.{0} Real Real.instNatCast F) →
                @LE.le.{0} Nat instLENat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                  DecrAlmostLinearSSSP.Decremental.Ends guest g final →
                    ∃ cost u,
                      And
                        (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                          (DecrAlmostLinearSSSP.Decremental.shadowInterpreter guest.code) s cost u)
                        (And
                          (@LE.le.{0} Nat instLENat cost
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (DecrAlmostLinearSSSP.Decremental.dispatchCharge guest.code)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) final.work g.work))
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                          (DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F u final)))) ∧ ((∀ (guest : DecrAlmostLinearSSSP.Decremental.Program) (steps B F : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) F →
    ∀ (s u : DecrAlmostLinearSSSP.Decremental.Structured.Data) (g : DecrAlmostLinearSSSP.Decremental.Machine),
      DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F s g →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) B →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) F →
              @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                  (@Nat.cast.{0} Real Real.instNatCast F) →
                @LE.le.{0} Nat instLENat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                  (∀ (j : Nat),
                      @LT.lt.{0} Nat instLTNat j steps →
                        @Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.execute guest g j).halted Bool.false →
                          ∃ ins,
                            @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                              (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                                DecrAlmostLinearSSSP.Decremental.Instruction
                                (fun as i =>
                                  @LT.lt.{0} Nat instLTNat i
                                    (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                                (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                                guest.code (DecrAlmostLinearSSSP.Decremental.execute guest g j).pc)
                              (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins)) →
                    @Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.execute guest g steps).halted Bool.true →
                      ∀ (cost : Nat),
                        DecrAlmostLinearSSSP.Decremental.Structured.Eval
                            (DecrAlmostLinearSSSP.Decremental.shadowInterpreter guest.code) s cost u →
                          ∀ (address : Nat),
                            (∀ (a : Nat),
                                @Ne.{1} Nat address
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) →
                              And (@Eq.{1} Real (u.realMem address) (s.realMem address))
                                (@Eq.{1} Nat (u.natMem address) (s.natMem address))) ∧ ((∀ (guest : DecrAlmostLinearSSSP.Decremental.Program) (B F : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) F →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (g final : DecrAlmostLinearSSSP.Decremental.Machine),
      DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F s g →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) B →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) F →
              @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                  (@Nat.cast.{0} Real Real.instNatCast F) →
                @LE.le.{0} Nat instLENat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                  DecrAlmostLinearSSSP.Decremental.Ends guest g final →
                    ∃ cost u,
                      And
                        (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                          (DecrAlmostLinearSSSP.Decremental.shadowInterpreter guest.code) s cost u)
                        (And
                          (@LE.le.{0} Nat instLENat cost
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (DecrAlmostLinearSSSP.Decremental.dispatchCharge guest.code)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) final.work g.work))
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                          (And (DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F u final)
                            (∀ (address : Nat),
                              (∀ (a : Nat),
                                  @Ne.{1} Nat address
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) →
                                And (@Eq.{1} Real (u.realMem address) (s.realMem address))
                                  (@Eq.{1} Nat (u.natMem address) (s.natMem address)))))) ∧ (∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction) (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.shadowAction ins) k))))))) ∧ ((((((∀ {B bank start : Nat} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowDataRep B (DecrAlmostLinearSSSP.Decremental.bankFactor bank) s g →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) B →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
          (DecrAlmostLinearSSSP.Decremental.bankFactor bank) →
        ∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction) (cost : Nat),
          DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.shadowAction ins) s cost
              t →
            ∀ (reports : List.{0} Nat),
              DecrAlmostLinearSSSP.Decremental.ReportLog start reports s →
                (∃ r,
                    @Eq.{1} Nat start
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                  DecrAlmostLinearSSSP.Decremental.ReportLog start reports t) ∧ (∀ {B F : Nat} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F s g →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) B →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) F →
        ∀ (a d cost : Nat),
          DecrAlmostLinearSSSP.Decremental.Structured.Eval
              (DecrAlmostLinearSSSP.Decremental.shadowAction (DecrAlmostLinearSSSP.Decremental.Instruction.store a d)) s
              cost t →
            @Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (g.natReg a))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))) ∧ ((∀ {B F : Nat} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F s g →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) B →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) F →
        ∀ (a d cost : Nat),
          DecrAlmostLinearSSSP.Decremental.Structured.Eval
              (DecrAlmostLinearSSSP.Decremental.shadowAction (DecrAlmostLinearSSSP.Decremental.Instruction.storeN a d))
              s cost t →
            @Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (g.natReg a))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) ∧ (∀ {B bank start : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowDataRep B (DecrAlmostLinearSSSP.Decremental.bankFactor bank) s g →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) B →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
            (DecrAlmostLinearSSSP.Decremental.bankFactor bank) →
          @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
              (@Nat.cast.{0} Real Real.instNatCast (DecrAlmostLinearSSSP.Decremental.bankFactor bank)) →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
              ∀ (reports : List.{0} Nat),
                DecrAlmostLinearSSSP.Decremental.ReportLog start reports s →
                  (∃ r,
                      @Eq.{1} Nat start
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                    ∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
                      ∃ cost t,
                        And
                          (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                            (DecrAlmostLinearSSSP.Decremental.observedAction ins) s cost t)
                          (And
                            (@LE.le.{0} Nat instLENat cost
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (DecrAlmostLinearSSSP.Decremental.actionBound ins)
                                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                            (And
                              (DecrAlmostLinearSSSP.Decremental.ShadowDataRep B
                                (DecrAlmostLinearSSSP.Decremental.bankFactor bank) t
                                (DecrAlmostLinearSSSP.Decremental.instructionEffect ins g))
                              (DecrAlmostLinearSSSP.Decremental.ReportLog start
                                (@HAppend.hAppend.{0, 0, 0} (List.{0} Nat) (List.{0} Nat) (List.{0} Nat)
                                  (@instHAppendOfAppend.{0} (List.{0} Nat) (@List.instAppend.{0} Nat)) reports
                                  (DecrAlmostLinearSSSP.Decremental.physicalWrites B bank ins g))
                                t)))))) ∧ (((∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction) (k : Nat),
  @Even.{0} Nat instAddNat k →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.shadowAction ins) k) ∧ (∀ (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (pc k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.dispatchAux pc code) k)) ∧ ((∀ (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (pc k : Nat),
  @Even.{0} Nat instAddNat k →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.dispatchAux pc code) k) ∧ ((∀ (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.shadowInterpreter code) k) ∧ (∀ (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (k : Nat),
  @Even.{0} Nat instAddNat k →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.shadowInterpreter code) k))))) ∧ ((((∀ (base : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.ShadowDataRep base (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) s
    (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.unscaledGuest base s)) ∧ (∀ (base N : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) base →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
              @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
                @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                    (s.realReg
                      (DecrAlmostLinearSSSP.Decremental.shadowReg
                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) →
                  @LE.le.{0} Real Real.instLE
                      (s.realReg
                        (DecrAlmostLinearSSSP.Decremental.shadowReg
                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                      (@HPow.hPow.{0, 0, 0} Real Nat Real
                        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                        (@OfNat.ofNat.{0} Real (nat_lit 2)
                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                        N) →
                    ∃ cost t,
                      And
                        (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                          (DecrAlmostLinearSSSP.Decremental.shadowInterpreter
                            DecrAlmostLinearSSSP.Decremental.ScaledCeiling.ceilingProgram.code)
                          s cost t)
                        (And
                          (@Eq.{1} Nat
                            (t.natReg
                              (DecrAlmostLinearSSSP.Decremental.shadowReg
                                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (s.natReg
                                (DecrAlmostLinearSSSP.Decremental.shadowReg
                                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                              (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
                                (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing)
                                (s.realReg
                                  (DecrAlmostLinearSSSP.Decremental.shadowReg
                                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
                          (And
                            (@LE.le.{0} Nat instLENat cost
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (DecrAlmostLinearSSSP.Decremental.dispatchCharge
                                      DecrAlmostLinearSSSP.Decremental.ScaledCeiling.ceilingProgram.code)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16))) N)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))))
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                            (And
                              (∀ (address : Nat),
                                (∀ (a : Nat),
                                    @Ne.{1} Nat address
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a))
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                                  And (@Eq.{1} Real (t.realMem address) (s.realMem address))
                                    (@Eq.{1} Nat (t.natMem address) (s.natMem address)))
                              (∀ (k : Nat),
                                @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))
                                    k →
                                  @Even.{0} Nat instAddNat k →
                                    And (@Eq.{1} Nat (t.natReg k) (s.natReg k))
                                      (@Eq.{1} Real (t.realReg k) (s.realReg k)))))))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.ScaledCeiling.setup s
    (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))
    (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.setupData s)) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
      And
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.ScaledCeiling.setupData s).natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 48) (instOfNatNat (nat_lit 48)))))
        (And
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.ScaledCeiling.setupData s).natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (And
            (@Eq.{1} Nat
              ((DecrAlmostLinearSSSP.Decremental.ScaledCeiling.setupData s).natReg
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
            (And
              (@Eq.{1} Nat
                ((DecrAlmostLinearSSSP.Decremental.ScaledCeiling.setupData s).natReg
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (And
                (@Eq.{1} Nat
                  ((DecrAlmostLinearSSSP.Decremental.ScaledCeiling.setupData s).natReg
                    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                (And
                  (@Eq.{1} Nat
                    ((DecrAlmostLinearSSSP.Decremental.ScaledCeiling.setupData s).natReg
                      (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (And
                    (@Eq.{1} Real
                      ((DecrAlmostLinearSSSP.Decremental.ScaledCeiling.setupData s).realReg
                        (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                    (And
                      (@Eq.{1} Nat
                        ((DecrAlmostLinearSSSP.Decremental.ScaledCeiling.setupData s).natReg
                          (DecrAlmostLinearSSSP.Decremental.shadowReg
                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58)))))
                      (@Eq.{1} Real
                        ((DecrAlmostLinearSSSP.Decremental.ScaledCeiling.setupData s).realReg
                          (DecrAlmostLinearSSSP.Decremental.shadowReg
                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                        (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))))))))))))) ∧ (∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.ScaledCeiling.setup k)))) ∧ (((∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.ScaledCeiling.setup k) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  And (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.setupData s).realMem s.realMem)
    (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.setupData s).natMem s.natMem))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (N : Nat),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58)))) →
        @LE.le.{0} Real Real.instLE (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))))
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              N) →
          ∃ cost t,
            And
              (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.ScaledCeiling.call s
                cost t)
              (And
                (@Eq.{1} Nat
                  (t.natReg
                    (DecrAlmostLinearSSSP.Decremental.shadowReg
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))))
                    (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
                      (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing)
                      (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58)))))))
                (And
                  (@LE.le.{0} Nat instLENat cost
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (DecrAlmostLinearSSSP.Decremental.dispatchCharge
                          DecrAlmostLinearSSSP.Decremental.ScaledCeiling.ceilingProgram.code)
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16))) N)
                        (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))))
                  (And
                    (∀ (address : Nat),
                      (∀ (a : Nat),
                          @Ne.{1} Nat address
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 48) (instOfNatNat (nat_lit 48))))
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a))
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                        And (@Eq.{1} Real (t.realMem address) (s.realMem address))
                          (@Eq.{1} Nat (t.natMem address) (s.natMem address)))
                    (∀ (k : Nat),
                      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
                        @Even.{0} Nat instAddNat k →
                          And (@Eq.{1} Nat (t.natReg k) (s.natReg k)) (@Eq.{1} Real (t.realReg k) (s.realReg k))))))) ∧ ((∀ (B bank tail a u : Nat),
  @Ne.{1} Nat
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) tail))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) u))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) ∧ (∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.ScaledCeiling.call k)))))) ∧ (((((∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.ScaledCeiling.call k) ∧ (∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
        DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.ScaledCeiling.cube k)) ∧ ((∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.ScaledCeiling.cube k) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (m N : Nat),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58)))) m →
    @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))))
        (@Nat.cast.{0} Real Real.instNatCast m) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
        @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
          @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast m)
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                N) →
            ∃ cost t,
              And
                (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.ScaledCeiling.cube s
                  cost t)
                (And
                  (@Eq.{1} Nat
                    (t.natReg
                      (DecrAlmostLinearSSSP.Decremental.shadowReg
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) m
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                  (And
                    (@LE.le.{0} Nat instLENat cost
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (DecrAlmostLinearSSSP.Decremental.dispatchCharge
                                DecrAlmostLinearSSSP.Decremental.ScaledCeiling.ceilingProgram.code)
                              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16))) N)
                            (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (∀ (address : Nat),
                      (∀ (a : Nat),
                          @Ne.{1} Nat address
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 48) (instOfNatNat (nat_lit 48))))
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a))
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                        And (@Eq.{1} Real (t.realMem address) (s.realMem address))
                          (@Eq.{1} Nat (t.natMem address) (s.natMem address)))))))) ∧ (((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (m N B : Nat),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58)))) m →
    @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))))
        (@Nat.cast.{0} Real Real.instNatCast m) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
        @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
            @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast m)
                (@HPow.hPow.{0, 0, 0} Real Nat Real
                  (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                  N) →
              ∃ cost t,
                And
                  (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                    (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.polynomialReserve B) s cost t)
                  (And
                    (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 60) (instOfNatNat (nat_lit 60))))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) B
                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) m
                            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (And
                      (@LE.le.{0} Nat instLENat cost
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (DecrAlmostLinearSSSP.Decremental.dispatchCharge
                                    DecrAlmostLinearSSSP.Decremental.ScaledCeiling.ceilingProgram.code)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16))) N)
                                (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))))
                            B)
                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                      (∀ (address : Nat),
                        (∀ (a : Nat),
                            @Ne.{1} Nat address
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 48) (instOfNatNat (nat_lit 48))))
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a))
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                          And (@Eq.{1} Real (t.realMem address) (s.realMem address))
                            (@Eq.{1} Nat (t.natMem address) (s.natMem address)))))) ∧ (∀ (n : Nat),
  @LE.le.{0} Real Real.instLE
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast n)
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
    (@HPow.hPow.{0, 0, 0} Real Nat Real
      (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
      (@OfNat.ofNat.{0} Real (nat_lit 2)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
      n))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    And
      (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (DecrAlmostLinearSSSP.Decremental.logarithm2
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@Nat.cast.{0} Real Real.instNatCast i.n) (@Nat.cast.{0} Real Real.instNatCast i.W))))
      (@LE.le.{0} Real Real.instLE
        (DecrAlmostLinearSSSP.Decremental.logarithm2
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@Nat.cast.{0} Real Real.instNatCast i.n) (@Nat.cast.{0} Real Real.instNatCast i.W)))
        (@HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
          (DecrAlmostLinearSSSP.Decremental.scaleCount i)))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast (DecrAlmostLinearSSSP.Decremental.scaleCount i))
    (@HPow.hPow.{0, 0, 0} Real Nat Real
      (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
      (@OfNat.ofNat.{0} Real (nat_lit 2)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
      (DecrAlmostLinearSSSP.Decremental.scaleCount i))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.ScaledCeiling.scaleArgument s
    (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
    (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.scaleArgumentData s)))))) ∧ ((((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (i : DecrAlmostLinearSSSP.Decremental.Input),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 66) (instOfNatNat (nat_lit 66)))) i.n →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 70) (instOfNatNat (nat_lit 70)))) i.W →
      And
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.ScaledCeiling.scaleArgumentData s).natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (And
          (@Eq.{1} Real
            ((DecrAlmostLinearSSSP.Decremental.ScaledCeiling.scaleArgumentData s).realReg
              (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))))
            (DecrAlmostLinearSSSP.Decremental.logarithm2
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@Nat.cast.{0} Real Real.instNatCast i.n) (@Nat.cast.{0} Real Real.instNatCast i.W))))
          (And
            (@Eq.{1} Nat
              ((DecrAlmostLinearSSSP.Decremental.ScaledCeiling.scaleArgumentData s).natReg
                (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56)))))
            (And
              (@Eq.{1} Real
                ((DecrAlmostLinearSSSP.Decremental.ScaledCeiling.scaleArgumentData s).realReg
                  (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
                (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56)))))
              (@Eq.{1} Nat
                ((DecrAlmostLinearSSSP.Decremental.ScaledCeiling.scaleArgumentData s).natReg
                  (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))))))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 66) (instOfNatNat (nat_lit 66)))) i.n →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 70) (instOfNatNat (nat_lit 70)))) i.W →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
          @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
              ∃ cost t,
                And
                  (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                    DecrAlmostLinearSSSP.Decremental.ScaledCeiling.countScales s cost t)
                  (And
                    (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
                      (DecrAlmostLinearSSSP.Decremental.scaleCount i))
                    (And
                      (@LE.le.{0} Nat instLENat cost
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (DecrAlmostLinearSSSP.Decremental.dispatchCharge
                              DecrAlmostLinearSSSP.Decremental.ScaledCeiling.ceilingProgram.code)
                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))
                              (DecrAlmostLinearSSSP.Decremental.scaleCount i))
                            (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))))
                      (∀ (address : Nat),
                        (∀ (a : Nat),
                            @Ne.{1} Nat address
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 48) (instOfNatNat (nat_lit 48))))
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a))
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                          And (@Eq.{1} Real (t.realMem address) (s.realMem address))
                            (@Eq.{1} Nat (t.natMem address) (s.natMem address))))))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (i : DecrAlmostLinearSSSP.Decremental.Input),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 66) (instOfNatNat (nat_lit 66)))) i.n →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
        (DecrAlmostLinearSSSP.Decremental.scaleCount i) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
        @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
          ∃ cost t,
            And
              (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.ScaledCeiling.scaleArea
                s cost t)
              (And
                (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))))
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) i.n
                    (DecrAlmostLinearSSSP.Decremental.scaleCount i)))
                (And
                  (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
                    (DecrAlmostLinearSSSP.Decremental.scaleCount i))
                  (And
                    (@LE.le.{0} Nat instLENat cost
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (DecrAlmostLinearSSSP.Decremental.dispatchCharge
                            DecrAlmostLinearSSSP.Decremental.ScaledCeiling.ceilingProgram.code)
                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))
                            (DecrAlmostLinearSSSP.Decremental.scaleCount i))
                          (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))))
                    (∀ (address : Nat),
                      (∀ (a : Nat),
                          @Ne.{1} Nat address
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 48) (instOfNatNat (nat_lit 48))))
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a))
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                        And (@Eq.{1} Real (t.realMem address) (s.realMem address))
                          (@Eq.{1} Nat (t.natMem address) (s.natMem address))))))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat
    ((DecrAlmostLinearSSSP.Decremental.Layout.preData s).natReg
      (@OfNat.ofNat.{0} Nat (nat_lit 84) (instOfNatNat (nat_lit 84))))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 66) (instOfNatNat (nat_lit 66)))))
        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))))
      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26)))))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 84) (instOfNatNat (nat_lit 84))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 86) (instOfNatNat (nat_lit 86))) →
      @Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.Layout.preData s).natReg k) (s.natReg k))))) ∧ (((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Layout.Represents (DecrAlmostLinearSSSP.Decremental.Layout.postData s)
    (DecrAlmostLinearSSSP.Decremental.Layout.postAddresses s)) ∧ (∀ (stride : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.NoMemory (DecrAlmostLinearSSSP.Decremental.Layout.code stride))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (B n S reserve stride : Nat),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))) B →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 66) (instOfNatNat (nat_lit 66)))) n →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80)))) S →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) n S) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 60) (instOfNatNat (nat_lit 60)))) reserve →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
              ∃ t,
                And
                  (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                    (DecrAlmostLinearSSSP.Decremental.Layout.code stride) s
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) stride
                      (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16))))
                    t)
                  (And
                    (DecrAlmostLinearSSSP.Decremental.Layout.Represents t
                      (DecrAlmostLinearSSSP.Decremental.Layout.addresses B n S reserve stride))
                    (And (@Eq.{1} (Nat → Real) t.realMem s.realMem) (@Eq.{1} (Nat → Nat) t.natMem s.natMem)))) ∧ ((∀ (B k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 60) (instOfNatNat (nat_lit 60))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
            (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.polynomialReserve B) k) ∧ (∀ (B k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
        (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.polynomialReserve B) k)))))))) := by
  exact ⟨⟨⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.shadow_prefix_address,DecrAlmostLinearSSSP.Decremental.shadow_outside_memory⟩,⟨DecrAlmostLinearSSSP.Decremental.PreservesOutside.refl,DecrAlmostLinearSSSP.Decremental.PreservesOutside.trans⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.shadow_single_step_framed,DecrAlmostLinearSSSP.Decremental.shadow_framed_execution⟩,⟨DecrAlmostLinearSSSP.Decremental.shadow_framed_ends,⟨DecrAlmostLinearSSSP.Decremental.ScaledCeiling.ceilingProgram_width,DecrAlmostLinearSSSP.Decremental.ScaledCeiling.shadow_ceiling_call⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.eval_shadow_scalar_command,DecrAlmostLinearSSSP.Decremental.eval_shadow_action⟩,⟨DecrAlmostLinearSSSP.Decremental.repeatedAdd_no_memory,DecrAlmostLinearSSSP.Decremental.shadowAction_no_memory⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.shadowAction_memory_frame,DecrAlmostLinearSSSP.Decremental.Structured.NatFrame.flag⟩,⟨DecrAlmostLinearSSSP.Decremental.Structured.Eval.flag_bound,⟨DecrAlmostLinearSSSP.Decremental.shadowAction_nat_frame,DecrAlmostLinearSSSP.Decremental.shadowAction_real_frame⟩⟩⟩⟩⟩,⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.shadowAction_halt_frame,DecrAlmostLinearSSSP.Decremental.shadowAction_flag_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.ShadowDataRep.scratch8,DecrAlmostLinearSSSP.Decremental.eval_shadow_instruction⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.eval_dispatch_aux,DecrAlmostLinearSSSP.Decremental.shadowInstruction_memory_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.dispatchAux_memory_frame,⟨DecrAlmostLinearSSSP.Decremental.shadowInstruction_nat_frame,DecrAlmostLinearSSSP.Decremental.shadowInstruction_real_frame⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.shadowInstruction_flag_frame,DecrAlmostLinearSSSP.Decremental.dispatchAux_nat_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.dispatchAux_real_frame,⟨DecrAlmostLinearSSSP.Decremental.dispatchAux_flag_frame,DecrAlmostLinearSSSP.Decremental.ShadowDataRep.halt_flag⟩⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.eval_shadow_interpreter,DecrAlmostLinearSSSP.Decremental.eval_shadow_interpreter_ends⟩,⟨DecrAlmostLinearSSSP.Decremental.shadow_interpreter_memory_frame,⟨DecrAlmostLinearSSSP.Decremental.eval_shadow_call,DecrAlmostLinearSSSP.Decremental.shadowAction_even_frame⟩⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.shadowAction_preserves_report_log,DecrAlmostLinearSSSP.Decremental.shadowAction_store_address⟩,⟨DecrAlmostLinearSSSP.Decremental.shadowAction_storeN_address,DecrAlmostLinearSSSP.Decremental.eval_observed_action⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.shadowAction_real_even_frame,DecrAlmostLinearSSSP.Decremental.dispatchAux_nat_even_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.dispatchAux_real_even_frame,⟨DecrAlmostLinearSSSP.Decremental.shadowInterpreter_nat_even_frame,DecrAlmostLinearSSSP.Decremental.shadowInterpreter_real_even_frame⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.ScaledCeiling.unscaledGuest_rep,DecrAlmostLinearSSSP.Decremental.ScaledCeiling.unscaled_ceiling_eval⟩,⟨DecrAlmostLinearSSSP.Decremental.ScaledCeiling.setup_eval,⟨DecrAlmostLinearSSSP.Decremental.ScaledCeiling.setup_fields,DecrAlmostLinearSSSP.Decremental.ScaledCeiling.setup_nat_frame⟩⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.ScaledCeiling.setup_real_frame,DecrAlmostLinearSSSP.Decremental.ScaledCeiling.setup_memory⟩,⟨DecrAlmostLinearSSSP.Decremental.ScaledCeiling.call_eval,⟨DecrAlmostLinearSSSP.Decremental.ScaledCeiling.guest_bank_outside_utility_tail,DecrAlmostLinearSSSP.Decremental.ScaledCeiling.call_nat_even⟩⟩⟩⟩⟩,⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.ScaledCeiling.call_real_even,DecrAlmostLinearSSSP.Decremental.ScaledCeiling.cube_nat_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.ScaledCeiling.cube_real_frame,DecrAlmostLinearSSSP.Decremental.ScaledCeiling.cube_eval⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.ScaledCeiling.polynomialReserve_eval,DecrAlmostLinearSSSP.Decremental.real_succ_le_two_pow⟩,⟨DecrAlmostLinearSSSP.Decremental.scale_count_ceiling_argument,⟨DecrAlmostLinearSSSP.Decremental.scale_count_nat_argument,DecrAlmostLinearSSSP.Decremental.ScaledCeiling.scaleArgument_eval⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.ScaledCeiling.scaleArgument_fields,DecrAlmostLinearSSSP.Decremental.ScaledCeiling.countScales_eval⟩,⟨DecrAlmostLinearSSSP.Decremental.ScaledCeiling.scaleArea_eval,⟨DecrAlmostLinearSSSP.Decremental.Layout.pre_record,DecrAlmostLinearSSSP.Decremental.Layout.pre_meta⟩⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Layout.post_rep,DecrAlmostLinearSSSP.Decremental.Layout.code_no_memory⟩,⟨DecrAlmostLinearSSSP.Decremental.Layout.eval_code,⟨DecrAlmostLinearSSSP.Decremental.ScaledCeiling.reserve_nat_frame,DecrAlmostLinearSSSP.Decremental.ScaledCeiling.reserve_real_frame⟩⟩⟩⟩⟩⟩⟩
