-- Prove2me | solution 1 for DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_8
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T11:14:40.280614+00:00
-- url     : https://prove2.me/submissions/7ee79d90-c8bb-4863-a93f-ba8eec86a775

import Definitions.Def_DecrAlmostLinearSSSP_RAMFoundation
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_1
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_2
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_3
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_4
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_5
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_6
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_7
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
open scoped ENNReal NNReal
attribute [local instance] Classical.propDecidable
theorem DecrAlmostLinearSSSP.Decremental.execute_add : ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (a b : Nat),
  @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
    (DecrAlmostLinearSSSP.Decremental.execute p c (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a b))
    (DecrAlmostLinearSSSP.Decremental.execute p (DecrAlmostLinearSSSP.Decremental.execute p c a) b) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_1.2.1.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.execute_halted : ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine),
  @Eq.{1} Bool c.halted Bool.true →
    ∀ (t : Nat), @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine (DecrAlmostLinearSSSP.Decremental.execute p c t) c := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_1.2.2.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.execute_work_mono : ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (t : Nat),
  @LE.le.{0} Nat instLENat c.work (DecrAlmostLinearSSSP.Decremental.execute p c t).work := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.1.1.1.1.1.1
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
theorem DecrAlmostLinearSSSP.Decremental.Exact.Payload.Image.frame : ∀ {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {items : List.{0} (Prod.{0, 0} Nat Nat)},
  DecrAlmostLinearSSSP.Decremental.Exact.Payload.Image s items →
    (∀ (address : Nat),
        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
            (DecrAlmostLinearSSSP.Decremental.Exact.Payload.footprint items) address →
          @Eq.{1} Nat (t.natMem address) (s.natMem address)) →
      DecrAlmostLinearSSSP.Decremental.Exact.Payload.Image t items := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.1.1.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image.frame : ∀ {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {height : Nat}
  {tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie height},
  @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image s height tree →
    (∀ (address : Nat),
        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
            (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint height tree) address →
          @Eq.{1} Nat (t.natMem address) (s.natMem address)) →
      @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image t height tree := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.1.1.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.Structured.program_init : ∀ (init update : DecrAlmostLinearSSSP.Decremental.Structured.Cmd),
  DecrAlmostLinearSSSP.Decremental.Structured.CodeAt (DecrAlmostLinearSSSP.Decremental.Structured.program init update)
    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
    (DecrAlmostLinearSSSP.Decremental.Structured.compile init
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.1.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.Structured.program_init_halt : ∀ (init update : DecrAlmostLinearSSSP.Decremental.Structured.Cmd),
  @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
    (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
      DecrAlmostLinearSSSP.Decremental.Instruction
      (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
      (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
      (DecrAlmostLinearSSSP.Decremental.Structured.program init update).code
      (DecrAlmostLinearSSSP.Decremental.Structured.codeSize init))
    (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction DecrAlmostLinearSSSP.Decremental.Instruction.halt) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.1.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.Structured.program_update : ∀ (init update : DecrAlmostLinearSSSP.Decremental.Structured.Cmd),
  DecrAlmostLinearSSSP.Decremental.Structured.CodeAt (DecrAlmostLinearSSSP.Decremental.Structured.program init update)
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (DecrAlmostLinearSSSP.Decremental.Structured.codeSize init)
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (DecrAlmostLinearSSSP.Decremental.Structured.compile update
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (DecrAlmostLinearSSSP.Decremental.Structured.codeSize init)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.1.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.Structured.program_update_halt : ∀ (init update : DecrAlmostLinearSSSP.Decremental.Structured.Cmd),
  @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
    (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
      DecrAlmostLinearSSSP.Decremental.Instruction
      (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
      (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
      (DecrAlmostLinearSSSP.Decremental.Structured.program init update).code
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (DecrAlmostLinearSSSP.Decremental.Structured.codeSize init)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (DecrAlmostLinearSSSP.Decremental.Structured.codeSize update)))
    (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction DecrAlmostLinearSSSP.Decremental.Instruction.halt) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.1.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Structured.program_query_nine : ∀ (init update : DecrAlmostLinearSSSP.Decremental.Structured.Cmd) (c : DecrAlmostLinearSSSP.Decremental.Machine)
  (v : Nat),
  ∃ d,
    And
      (DecrAlmostLinearSSSP.Decremental.Ends (DecrAlmostLinearSSSP.Decremental.Structured.program init update)
        (have __src :=
          DecrAlmostLinearSSSP.Decremental.resume c
            (DecrAlmostLinearSSSP.Decremental.Structured.program init update).query;
        { pc := __src.pc, realReg := __src.realReg,
          natReg :=
            @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat c.natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) v,
          realMem := __src.realMem, natMem := __src.natMem, halted := __src.halted, fault := __src.fault,
          work := __src.work })
        d)
      (And
        (@LE.le.{0} Nat instLENat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d.work
            (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
            (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))))
        (And (@Eq.{1} Nat (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))) (c.natMem v))
          (And (@Eq.{1} Real (d.realReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (c.realMem v))
            (And (@Eq.{1} (Nat → Real) d.realMem c.realMem) (@Eq.{1} (Nat → Nat) d.natMem c.natMem))))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.1.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Structured.command_ends : ∀ {cmd : DecrAlmostLinearSSSP.Decremental.Structured.Cmd} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {cost : Nat},
  DecrAlmostLinearSSSP.Decremental.Structured.Eval cmd s cost t →
    ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (start : Nat) (c : DecrAlmostLinearSSSP.Decremental.Machine),
      DecrAlmostLinearSSSP.Decremental.Structured.CodeAt p start
          (DecrAlmostLinearSSSP.Decremental.Structured.compile cmd start) →
        @Eq.{1} Nat c.pc start →
          @Eq.{1} DecrAlmostLinearSSSP.Decremental.Structured.Data (DecrAlmostLinearSSSP.Decremental.Structured.data c)
              s →
            @Eq.{1} Bool c.halted Bool.false →
              @Eq.{1} Bool c.fault Bool.false →
                @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                    (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                      DecrAlmostLinearSSSP.Decremental.Instruction
                      (fun as i =>
                        @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                      (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start
                        (DecrAlmostLinearSSSP.Decremental.Structured.codeSize cmd)))
                    (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                      DecrAlmostLinearSSSP.Decremental.Instruction.halt) →
                  ∃ d,
                    And (DecrAlmostLinearSSSP.Decremental.Ends p c d)
                      (And
                        (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Structured.Data
                          (DecrAlmostLinearSSSP.Decremental.Structured.data d) t)
                        (@Eq.{1} Nat d.work
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work cost)
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.1.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.Structured.eval_natural : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (d q : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.natural d q) s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    { realReg := s.realReg, natReg := @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natReg d q,
      realMem := s.realMem, natMem := s.natMem } := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.1.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Structured.eval_sequence_atoms : ∀ (atoms : List.{0} DecrAlmostLinearSSSP.Decremental.Structured.Atom)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval
    (DecrAlmostLinearSSSP.Decremental.Structured.sequence
      (@List.map.{0, 0} DecrAlmostLinearSSSP.Decremental.Structured.Atom DecrAlmostLinearSSSP.Decremental.Structured.Cmd
        DecrAlmostLinearSSSP.Decremental.Structured.Cmd.atom atoms))
    s (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Structured.Atom atoms)
    (@List.foldl.{0, 0} DecrAlmostLinearSSSP.Decremental.Structured.Data
      DecrAlmostLinearSSSP.Decremental.Structured.Atom (fun t a => a.effect t) s atoms) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.2.1.2.1.1
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
theorem DecrAlmostLinearSSSP.Decremental.Exact.TriePush.code_nat_frame : ∀ k ∉ DecrAlmostLinearSSSP.Decremental.Exact.TriePush.registers,
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.TriePush.code k := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_3.2.2.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.TriePush.code_real_frame : ∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Exact.TriePush.code k := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_3.2.2.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.TriePop.Result.nat_frame : ∀ {h : Nat} {tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  (r : @DecrAlmostLinearSSSP.Decremental.Exact.TriePop.Result h tree s),
  ∀ k ∉ DecrAlmostLinearSSSP.Decremental.Exact.TriePop.registers,
    @Eq.{1} Nat ((@DecrAlmostLinearSSSP.Decremental.Exact.TriePop.Result.final h tree s r).natReg k) (s.natReg k) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.1.1.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.TriePop.code_nat_frame : ∀ k ∉ DecrAlmostLinearSSSP.Decremental.Exact.TriePop.registers,
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.TriePop.code k := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.1.1.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.TriePop.code_real_frame : ∀ (k : Nat), DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Exact.TriePop.code k := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.1.1.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.input_vertex_positive : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) i.n := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.1.1.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.subpolynomial_constant : ∀ (c : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) c →
    DecrAlmostLinearSSSP.Decremental.Subpolynomial fun x => c := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.1.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.subpolynomial_add : ∀ (a b : Nat → Real),
  DecrAlmostLinearSSSP.Decremental.Subpolynomial a →
    DecrAlmostLinearSSSP.Decremental.Subpolynomial b →
      DecrAlmostLinearSSSP.Decremental.Subpolynomial fun m =>
        @HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (a m) (b m) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.1.2.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.scaleCount_saturated_bound : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast (DecrAlmostLinearSSSP.Decremental.scaleCount i))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (@OfNat.ofNat.{0} Real (nat_lit 3)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
          (DecrAlmostLinearSSSP.Decremental.logarithm2
            (@Nat.cast.{0} Real Real.instNatCast
              (@Max.max.{0} Nat Nat.instMax (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) i.size))))
        (@Max.max.{0} Real Real.instMax (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (DecrAlmostLinearSSSP.Decremental.logarithm2 (@Nat.cast.{0} Real Real.instNatCast i.W)))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.1.2.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.subpolynomial_logarithm2_size : DecrAlmostLinearSSSP.Decremental.Subpolynomial fun m =>
  DecrAlmostLinearSSSP.Decremental.logarithm2
    (@Nat.cast.{0} Real Real.instNatCast
      (@Max.max.{0} Nat Nat.instMax (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.1.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.height_spec : ∀ (bound : Nat),
  @LT.lt.{0} Nat instLTNat bound
    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
      (DecrAlmostLinearSSSP.Decremental.Exact.height bound)) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.1.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.input_height_le : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    @LE.le.{0} Nat instLENat
      (DecrAlmostLinearSSSP.Decremental.Exact.height
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) i.n i.W))
      (DecrAlmostLinearSSSP.Decremental.scaleCount i) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.1.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.Powers.body_real_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 250) (instOfNatNat (nat_lit 250))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Exact.Powers.body k := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.1.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.Powers.Prefix.step : ∀ {bound base d : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Powers.Prefix bound base d s →
    DecrAlmostLinearSSSP.Decremental.Exact.Powers.Prefix bound base
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (DecrAlmostLinearSSSP.Decremental.Exact.Powers.advanced s) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.1.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.ShadowDataRep.effect : ∀ {B F : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine}
  (a : DecrAlmostLinearSSSP.Decremental.Structured.Atom),
  DecrAlmostLinearSSSP.Decremental.ShadowRep B F
      (DecrAlmostLinearSSSP.Decremental.instructionEffect a.instruction s.machine) g →
    DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F (a.effect s) g := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.1.1.2.1.1.1
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
theorem DecrAlmostLinearSSSP.Decremental.Exact.Layout.values : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i s →
    DecrAlmostLinearSSSP.Decremental.Exact.Layout.Image
      (DecrAlmostLinearSSSP.Decremental.Exact.Layout.addresses
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        i.n i.k)
      (DecrAlmostLinearSSSP.Decremental.Exact.Layout.result s) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.2.1.1.1.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.Exact.candidate_key_bound : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (active : Finset.{0} (Fin i.k)) (u : Fin i.n) (d : Nat),
      @Eq.{1} ENNReal
          (@DecrAlmostLinearSSSP.Decremental.distance i.n i.k i.graph active
            (fun e =>
              @Nat.cast.{0} ENNReal
                (@AddMonoidWithOne.toNatCast.{0} ENNReal
                  (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                (i.weight e))
            i.source u)
          (@Nat.cast.{0} ENNReal
            (@AddMonoidWithOne.toNatCast.{0} ENNReal
              (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
            d) →
        @DecrAlmostLinearSSSP.Decremental.Reachable i.n i.k i.graph active i.source u →
          ∀ (e : Fin i.k),
            @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d (i.weight e))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) i.n i.W) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_6.1.1.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.LabelInvariant.pop_exact : ∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {w : Fin k → Nat}
  {source : Fin n} {tentative : Fin n → Option.{0} Nat} {settled : Finset.{0} (Fin n)}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin n))},
  @DecrAlmostLinearSSSP.Decremental.Exact.LabelInvariant n k g active w source tentative settled queue →
    ∀ (key : Nat) (v : Fin n),
      @Membership.mem.{0, 0} (Prod.{0, 0} Nat (Fin n)) (Multiset.{0} (Prod.{0, 0} Nat (Fin n)))
          (@Multiset.instMembership.{0} (Prod.{0, 0} Nat (Fin n))) queue (@Prod.mk.{0, 0} Nat (Fin n) key v) →
        (∀ (item : Prod.{0, 0} Nat (Fin n)),
            @Membership.mem.{0, 0} (Prod.{0, 0} Nat (Fin n)) (Multiset.{0} (Prod.{0, 0} Nat (Fin n)))
                (@Multiset.instMembership.{0} (Prod.{0, 0} Nat (Fin n))) queue item →
              @LE.le.{0} Nat instLENat key (@Prod.fst.{0, 0} Nat (Fin n) item)) →
          v ∉ settled →
            And (@Eq.{1} (Option.{0} Nat) (tentative v) (@Option.some.{0} Nat key))
              (@Eq.{1} ENNReal
                (@DecrAlmostLinearSSSP.Decremental.distance n k g active
                  (fun e =>
                    @Nat.cast.{0} ENNReal
                      (@AddMonoidWithOne.toNatCast.{0} ENNReal
                        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                      (w e))
                  source v)
                (@Nat.cast.{0} ENNReal
                  (@AddMonoidWithOne.toNatCast.{0} ENNReal
                    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                  key)) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_6.1.1.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.reachable_of_nat_bound : ∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (active : Finset.{0} (Fin k)) (w : Fin k → ENNReal)
  (s v : Fin n) (d : Nat),
  @LE.le.{0} ENNReal ENNReal.instLE (@DecrAlmostLinearSSSP.Decremental.distance n k g active w s v)
      (@Nat.cast.{0} ENNReal
        (@AddMonoidWithOne.toNatCast.{0} ENNReal
          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
        d) →
    @DecrAlmostLinearSSSP.Decremental.Reachable n k g active s v := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_6.1.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.labelInvariant_initial : ∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (active : Finset.{0} (Fin k)) (w : Fin k → Nat)
  (source : Fin n),
  @DecrAlmostLinearSSSP.Decremental.Exact.LabelInvariant n k g active w source
    (@DecrAlmostLinearSSSP.Decremental.Exact.initialTentative n source)
    (@EmptyCollection.emptyCollection.{0} (Finset.{0} (Fin n)) (@Finset.instEmptyCollection.{0} (Fin n)))
    (@Singleton.singleton.{0, 0} (Prod.{0, 0} Nat (Fin n)) (Multiset.{0} (Prod.{0, 0} Nat (Fin n)))
      (@Multiset.instSingleton.{0} (Prod.{0, 0} Nat (Fin n)))
      (@Prod.mk.{0, 0} Nat (Fin n) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) source)) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_6.1.1.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.LabelInvariant.finished : ∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {w : Fin k → Nat}
  {source : Fin n} {tentative : Fin n → Option.{0} Nat} {settled : Finset.{0} (Fin n)},
  @DecrAlmostLinearSSSP.Decremental.Exact.LabelInvariant n k g active w source tentative settled
      (@OfNat.ofNat.{0} (Multiset.{0} (Prod.{0, 0} Nat (Fin n))) (nat_lit 0)
        (@Zero.toOfNat0.{0} (Multiset.{0} (Prod.{0, 0} Nat (Fin n)))
          (@Multiset.instZero.{0} (Prod.{0, 0} Nat (Fin n))))) →
    ∀ (v : Fin n),
      And
        (@Eq.{1} ENNReal
          (@DecrAlmostLinearSSSP.Decremental.distance n k g active
            (fun e =>
              @Nat.cast.{0} ENNReal
                (@AddMonoidWithOne.toNatCast.{0} ENNReal
                  (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                (w e))
            source v)
          (DecrAlmostLinearSSSP.Decremental.Exact.tentativeValue (tentative v)))
        (Iff (@Eq.{1} (Option.{0} Nat) (tentative v) (@Option.none.{0} Nat))
          (Not (@DecrAlmostLinearSSSP.Decremental.Reachable n k g active source v))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_6.1.2.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.adjacency_total : ∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (t : Nat),
  @LE.le.{0} Nat instLENat t k →
    @Eq.{1} Nat (∑ v, @List.length.{0} (Fin k) (@DecrAlmostLinearSSSP.Decremental.Exact.adjacency n k g t v)) t := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_6.1.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.code_real_frame : ∀ (j : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.code j := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_6.1.2.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.tape_initial : ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (i : DecrAlmostLinearSSSP.Decremental.Input),
  DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.Tape i
    (DecrAlmostLinearSSSP.Decremental.Structured.data (DecrAlmostLinearSSSP.Decremental.initialMachine p i)) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_6.1.2.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.tape_frame : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (s t : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.Tape i s →
    (∀ (a : Nat),
        @LT.lt.{0} Nat instLTNat a
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k)) →
          @Eq.{1} Nat (t.natMem a) (s.natMem a)) →
      DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.Tape i t := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_6.2.1.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.code_nat_frame : ∀
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
              (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 300) (instOfNatNat (nat_lit 300)))
                (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 304) (instOfNatNat (nat_lit 304)))
                  (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 306) (instOfNatNat (nat_lit 306)))
                    (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 308) (instOfNatNat (nat_lit 308)))
                      (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 310) (instOfNatNat (nat_lit 310)))
                        (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 312) (instOfNatNat (nat_lit 312)))
                          (@Singleton.singleton.{0, 0} Nat (Finset.{0} Nat) (@Finset.instSingleton.{0} Nat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 314) (instOfNatNat (nat_lit 314)))))))))))))),
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.code j := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_6.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.code_eval : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
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
                    DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.code s
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) i.n)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) i.k))
                      (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))))
                    t)
                  (And (DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.Prefix i i.k t)
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
                              (DecrAlmostLinearSSSP.Decremental.Exact.Layout.addresses
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  i.n i.k).powers
                              a) →
                          @Eq.{1} Nat (t.natMem a) (s.natMem a)))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_6.2.1.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.Image.static : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {l : DecrAlmostLinearSSSP.Decremental.Exact.Layout.Addresses}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.Image i l i.k s →
    DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.StaticImage i l s := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_6.2.2.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.Image.active_initial : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {l : DecrAlmostLinearSSSP.Decremental.Exact.Layout.Addresses}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.Image i l i.k s →
    DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.ActiveImage i l (@List.nil.{0} (Fin i.k)) s := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_6.2.2.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.StaticImage.frame : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {l : DecrAlmostLinearSSSP.Decremental.Exact.Layout.Addresses}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.StaticImage i l s →
    (∀ (a : Nat),
        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
            (DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.staticFootprint i l) a →
          @Eq.{1} Nat (t.natMem a) (s.natMem a)) →
      DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.StaticImage i l t := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_6.2.2.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.TentativeImage.finite : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {l : DecrAlmostLinearSSSP.Decremental.Exact.Layout.Addresses}
  {tentative : Fin i.n → Option.{0} Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.TentativeImage i l tentative s →
    ∀ (v : Fin i.n) (d : Nat),
      @Eq.{1} (Option.{0} Nat) (tentative v) (@Option.some.{0} Nat d) →
        And (@Eq.{1} Nat (s.natMem (@Fin.val i.n v)) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (And
            (@Eq.{1} Nat
              (s.natMem (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) l.distances (@Fin.val i.n v)))
              d)
            (@Eq.{1} Real (s.realMem (@Fin.val i.n v)) (@Nat.cast.{0} Real Real.instNatCast d))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_6.2.2.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.TentativeImage.infinite : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {l : DecrAlmostLinearSSSP.Decremental.Exact.Layout.Addresses}
  {tentative : Fin i.n → Option.{0} Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.TentativeImage i l tentative s →
    ∀ (v : Fin i.n),
      @Eq.{1} (Option.{0} Nat) (tentative v) (@Option.none.{0} Nat) →
        @Eq.{1} Nat (s.natMem (@Fin.val i.n v)) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_6.2.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.TentativeImage.stored : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {l : DecrAlmostLinearSSSP.Decremental.Exact.Layout.Addresses}
  {tentative : Fin i.n → Option.{0} Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.TentativeImage i l tentative s →
    ∀ (v : Fin i.n),
      @Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.stored s.machine (@Fin.val i.n v))
        (DecrAlmostLinearSSSP.Decremental.Exact.tentativeValue (tentative v)) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_6.2.2.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.TentativeImage.frame : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {l : DecrAlmostLinearSSSP.Decremental.Exact.Layout.Addresses}
  {tentative : Fin i.n → Option.{0} Nat} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.TentativeImage i l tentative s →
    (∀ (v : Fin i.n), @Eq.{1} Nat (t.natMem (@Fin.val i.n v)) (s.natMem (@Fin.val i.n v))) →
      (∀ (v : Fin i.n),
          @Eq.{1} Nat
            (t.natMem (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) l.distances (@Fin.val i.n v)))
            (s.natMem (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) l.distances (@Fin.val i.n v)))) →
        (∀ (v : Fin i.n), @Eq.{1} Real (t.realMem (@Fin.val i.n v)) (s.realMem (@Fin.val i.n v))) →
          DecrAlmostLinearSSSP.Decremental.Exact.TentativeImage i l tentative t := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_6.2.2.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.Layout.vertex_bounds : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (v : Fin i.n),
  have l :=
    DecrAlmostLinearSSSP.Decremental.Exact.Layout.addresses
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      i.n i.k;
  And (@LT.lt.{0} Nat instLTNat (@Fin.val i.n v) l.heads)
    (And
      (@LT.lt.{0} Nat instLTNat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) l.heads (@Fin.val i.n v)) l.powers)
      (And
        (@LT.lt.{0} Nat instLTNat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) l.settled (@Fin.val i.n v)) l.powers)
        (@LT.lt.{0} Nat instLTNat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) l.distances (@Fin.val i.n v)) l.powers))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_6.2.2.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.Layout.edge_bounds : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (e : Fin i.k) (r : Nat),
  @LT.lt.{0} Nat instLTNat r (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
    have l :=
      DecrAlmostLinearSSSP.Decremental.Exact.Layout.addresses
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        i.n i.k;
    And
      (@LT.lt.{0} Nat instLTNat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) l.active (@Fin.val i.k e)) l.powers)
      (@LT.lt.{0} Nat instLTNat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.nodeAddress l i.k e) r)
        l.powers) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_6.2.2.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.Layout.static_bounds : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (a : Nat),
  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.staticFootprint i
        (DecrAlmostLinearSSSP.Decremental.Exact.Layout.addresses
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          i.n i.k))
      a →
    @LT.lt.{0} Nat instLTNat a
      (DecrAlmostLinearSSSP.Decremental.Exact.Layout.addresses
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          i.n i.k).powers := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_6.2.2.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.Heap.Image.push : ∀ {n h base slot : Nat} {tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin n))} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  @DecrAlmostLinearSSSP.Decremental.Exact.Heap.Image n h base slot tree queue s →
    ∀ (key : Nat) (v : Fin n),
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260)))) key →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 262) (instOfNatNat (nat_lit 262)))) (@Fin.val n v) →
          @LT.lt.{0} Nat instLTNat key
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h) →
            ∃ cost t next,
              And
                (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePush.code s
                  cost t)
                (And
                  (@LE.le.{0} Nat instLENat cost
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 43) (instOfNatNat (nat_lit 43)))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                  (And
                    (@DecrAlmostLinearSSSP.Decremental.Exact.Heap.Image n h base slot next
                      (@Multiset.cons.{0} (Prod.{0, 0} Nat (Fin n)) (@Prod.mk.{0, 0} Nat (Fin n) key v) queue) t)
                    (And (@Eq.{1} (Nat → Real) t.realMem s.realMem)
                      (∀ (a : Nat), @LT.lt.{0} Nat instLTNat a slot → @Eq.{1} Nat (t.natMem a) (s.natMem a))))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_7.1.1.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.Heap.Image.pop : ∀ {n h base slot : Nat} {tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin n))} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  @DecrAlmostLinearSSSP.Decremental.Exact.Heap.Image n h base slot tree queue s →
    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@Multiset.card.{0} (Prod.{0, 0} Nat (Fin n)) queue) →
      ∃ cost t next key v remaining,
        And
          (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePop.code s cost
            t)
          (And
            (@LE.le.{0} Nat instLENat cost
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 34) (instOfNatNat (nat_lit 34)))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
            (And (@DecrAlmostLinearSSSP.Decremental.Exact.Heap.Image n h base slot next remaining t)
              (And (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260)))) key)
                (And
                  (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 262) (instOfNatNat (nat_lit 262))))
                    (@Fin.val n v))
                  (And
                    (@Eq.{1} (Multiset.{0} (Prod.{0, 0} Nat (Fin n))) queue
                      (@Multiset.cons.{0} (Prod.{0, 0} Nat (Fin n)) (@Prod.mk.{0, 0} Nat (Fin n) key v) remaining))
                    (And
                      (∀ (item : Prod.{0, 0} Nat (Fin n)),
                        @Membership.mem.{0, 0} (Prod.{0, 0} Nat (Fin n)) (Multiset.{0} (Prod.{0, 0} Nat (Fin n)))
                            (@Multiset.instMembership.{0} (Prod.{0, 0} Nat (Fin n))) queue item →
                          @LE.le.{0} Nat instLENat key (@Prod.fst.{0, 0} Nat (Fin n) item))
                      (And (@Eq.{1} (Nat → Real) t.realMem s.realMem)
                        (∀ (a : Nat), @LT.lt.{0} Nat instLTNat a slot → @Eq.{1} Nat (t.natMem a) (s.natMem a))))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_7.1.1.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.public_below : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (v : Fin i.n),
  @LT.lt.{0} Nat instLTNat (@Fin.val i.n v) (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapSlot i) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_7.1.1.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.settled_below : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (v : Fin i.n),
  @LT.lt.{0} Nat instLTNat
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.layout i).settled (@Fin.val i.n v))
    (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapSlot i) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_7.1.1.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.Heap.Image.frame : ∀ {n h base slot : Nat} {tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin n))} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  @DecrAlmostLinearSSSP.Decremental.Exact.Heap.Image n h base slot tree queue s →
    (∀ (j : Nat),
        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
            (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56)))
              (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26)))
                (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 236) (instOfNatNat (nat_lit 236)))
                  (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 238) (instOfNatNat (nat_lit 238)))
                    (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))
                      (@Singleton.singleton.{0, 0} Nat (Finset.{0} Nat) (@Finset.instSingleton.{0} Nat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 246) (instOfNatNat (nat_lit 246)))))))))
            j →
          @Eq.{1} Nat (t.natReg j) (s.natReg j)) →
      @Eq.{1} (Nat → Nat) t.natMem s.natMem →
        @DecrAlmostLinearSSSP.Decremental.Exact.Heap.Image n h base slot tree queue t := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_7.1.1.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory.register_frame : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)} {tentative : Fin i.n → Option.{0} Nat}
  {settled : Finset.{0} (Fin i.n)}
  {tree :
    DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled tree queue s →
    (∀ (j : Nat),
        @LE.le.{0} Nat instLENat j (@OfNat.ofNat.{0} Nat (nat_lit 246) (instOfNatNat (nat_lit 246))) →
          @Eq.{1} Nat (t.natReg j) (s.natReg j)) →
      @Eq.{1} Real (t.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
          (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56)))) →
        @Eq.{1} (Nat → Nat) t.natMem s.natMem →
          @Eq.{1} (Nat → Real) t.realMem s.realMem →
            DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled tree queue t := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_7.1.1.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory.queueCount : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)} {tentative : Fin i.n → Option.{0} Nat}
  {settled : Finset.{0} (Fin i.n)}
  {tree :
    DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled tree queue s →
    ∃ c,
      And
        (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.queueCount s c
          (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.counted s))
        (And (@LE.le.{0} Nat instLENat c (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
          (And
            (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled tree queue
              (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.counted s))
            (@Eq.{1} Nat
              ((DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.counted s).natReg
                (@OfNat.ofNat.{0} Nat (nat_lit 348) (instOfNatNat (nat_lit 348))))
              (@Multiset.card.{0} (Prod.{0, 0} Nat (Fin i.n)) queue)))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_7.1.1.2.2.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory.push : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)} {tentative : Fin i.n → Option.{0} Nat}
  {settled : Finset.{0} (Fin i.n)}
  {tree :
    DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled tree queue s →
    ∀ (key : Nat) (v : Fin i.n),
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260)))) key →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 262) (instOfNatNat (nat_lit 262)))) (@Fin.val i.n v) →
          @LT.lt.{0} Nat instLTNat key
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)) →
            ∃ cost t next,
              And
                (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePush.code s
                  cost t)
                (And
                  (@LE.le.{0} Nat instLENat cost
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 43) (instOfNatNat (nat_lit 43)))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                  (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled next
                    (@Multiset.cons.{0} (Prod.{0, 0} Nat (Fin i.n)) (@Prod.mk.{0, 0} Nat (Fin i.n) key v) queue) t)) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_7.1.2.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory.pop : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)} {tentative : Fin i.n → Option.{0} Nat}
  {settled : Finset.{0} (Fin i.n)}
  {tree :
    DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled tree queue s →
    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@Multiset.card.{0} (Prod.{0, 0} Nat (Fin i.n)) queue) →
      ∃ cost t next key v remaining,
        And
          (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePop.code s cost
            t)
          (And
            (@LE.le.{0} Nat instLENat cost
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 34) (instOfNatNat (nat_lit 34)))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
            (And (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled next remaining t)
              (And (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260)))) key)
                (And
                  (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 262) (instOfNatNat (nat_lit 262))))
                    (@Fin.val i.n v))
                  (And
                    (@Eq.{1} (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))) queue
                      (@Multiset.cons.{0} (Prod.{0, 0} Nat (Fin i.n)) (@Prod.mk.{0, 0} Nat (Fin i.n) key v) remaining))
                    (∀ (item : Prod.{0, 0} Nat (Fin i.n)),
                      @Membership.mem.{0, 0} (Prod.{0, 0} Nat (Fin i.n)) (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n)))
                          (@Multiset.instMembership.{0} (Prod.{0, 0} Nat (Fin i.n))) queue item →
                        @LE.le.{0} Nat instLENat key (@Prod.fst.{0, 0} Nat (Fin i.n) item))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_7.1.2.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.LabelInvariant.skip_settled : ∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {w : Fin k → Nat}
  {source : Fin n} {tentative : Fin n → Option.{0} Nat} {settled : Finset.{0} (Fin n)}
  {remaining : Multiset.{0} (Prod.{0, 0} Nat (Fin n))} (key : Nat) (v : Fin n),
  @DecrAlmostLinearSSSP.Decremental.Exact.LabelInvariant n k g active w source tentative settled
      (@Multiset.cons.{0} (Prod.{0, 0} Nat (Fin n)) (@Prod.mk.{0, 0} Nat (Fin n) key v) remaining) →
    @Membership.mem.{0, 0} (Fin n) (Finset.{0} (Fin n))
        (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin n)) (Fin n) (@Finset.instSetLike.{0} (Fin n))) settled v →
      @DecrAlmostLinearSSSP.Decremental.Exact.LabelInvariant n k g active w source tentative settled remaining := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_7.1.2.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.ScanState.scan : ∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {w : Fin k → Nat}
  {source v : Fin n} {key : Nat} {settled : Finset.{0} (Fin n)} {scanned : List.{0} (Fin k)}
  {tentative : Fin n → Option.{0} Nat} {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin n))},
  @DecrAlmostLinearSSSP.Decremental.Exact.ScanState n k g active w source v key settled scanned tentative queue →
    ∀ (es : List.{0} (Fin k)),
      (∀ (e : Fin k),
          @Membership.mem.{0, 0} (Fin k) (List.{0} (Fin k)) (@List.instMembership.{0} (Fin k)) es e →
            @Eq.{1} (Fin n) (@DecrAlmostLinearSSSP.Decremental.Digraph.tail n k g e) v) →
        have r := @DecrAlmostLinearSSSP.Decremental.Exact.scanEdges n k g active w settled key es tentative queue;
        And
          (@DecrAlmostLinearSSSP.Decremental.Exact.ScanState n k g active w source v key settled
            (@HAppend.hAppend.{0, 0, 0} (List.{0} (Fin k)) (List.{0} (Fin k)) (List.{0} (Fin k))
              (@instHAppendOfAppend.{0} (List.{0} (Fin k)) (@List.instAppend.{0} (Fin k)))
              (@List.reverse.{0} (Fin k) es) scanned)
            (@Prod.fst.{0, 0} (Fin n → Option.{0} Nat) (Multiset.{0} (Prod.{0, 0} Nat (Fin n))) r)
            (@Prod.snd.{0, 0} (Fin n → Option.{0} Nat) (Multiset.{0} (Prod.{0, 0} Nat (Fin n))) r))
          (@LE.le.{0} Nat instLENat
            (@Multiset.card.{0} (Prod.{0, 0} Nat (Fin n))
              (@Prod.snd.{0, 0} (Fin n → Option.{0} Nat) (Multiset.{0} (Prod.{0, 0} Nat (Fin n))) r))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@Multiset.card.{0} (Prod.{0, 0} Nat (Fin n)) queue) (@List.length.{0} (Fin k) es))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_7.2.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.scan_outgoing : ∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {w : Fin k → Nat}
  {source v : Fin n} {key : Nat} {settled : Finset.{0} (Fin n)} {tentative : Fin n → Option.{0} Nat}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin n))},
  @DecrAlmostLinearSSSP.Decremental.Exact.LabelInvariant n k g active w source tentative settled
      (@Multiset.cons.{0} (Prod.{0, 0} Nat (Fin n)) (@Prod.mk.{0, 0} Nat (Fin n) key v) queue) →
    v ∉ settled →
      (∀ (item : Prod.{0, 0} Nat (Fin n)),
          @Membership.mem.{0, 0} (Prod.{0, 0} Nat (Fin n)) (Multiset.{0} (Prod.{0, 0} Nat (Fin n)))
              (@Multiset.instMembership.{0} (Prod.{0, 0} Nat (Fin n))) queue item →
            @LE.le.{0} Nat instLENat key (@Prod.fst.{0, 0} Nat (Fin n) item)) →
        have r :=
          @DecrAlmostLinearSSSP.Decremental.Exact.scanEdges n k g active w settled key
            (@DecrAlmostLinearSSSP.Decremental.Exact.adjacency n k g k v) tentative queue;
        And
          (@DecrAlmostLinearSSSP.Decremental.Exact.LabelInvariant n k g active w source
            (@Prod.fst.{0, 0} (Fin n → Option.{0} Nat) (Multiset.{0} (Prod.{0, 0} Nat (Fin n))) r)
            (@Insert.insert.{0, 0} (Fin n) (Finset.{0} (Fin n)) (@Finset.instInsert.{0} (Fin n) (instDecidableEqFin n))
              v settled)
            (@Prod.snd.{0, 0} (Fin n → Option.{0} Nat) (Multiset.{0} (Prod.{0, 0} Nat (Fin n))) r))
          (@LE.le.{0} Nat instLENat
            (@Multiset.card.{0} (Prod.{0, 0} Nat (Fin n))
              (@Prod.snd.{0, 0} (Fin n → Option.{0} Nat) (Multiset.{0} (Prod.{0, 0} Nat (Fin n))) r))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@Multiset.card.{0} (Prod.{0, 0} Nat (Fin n)) queue)
              (@List.length.{0} (Fin k) (@DecrAlmostLinearSSSP.Decremental.Exact.adjacency n k g k v)))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_7.2.2.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory.scan : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)} {tentative : Fin i.n → Option.{0} Nat}
  {settled : Finset.{0} (Fin i.n)}
  {tree :
    DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled tree queue s →
    ∀ (v : Fin i.n) (key : Nat),
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 306) (instOfNatNat (nat_lit 306)))) (@Fin.val i.n v) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 304) (instOfNatNat (nat_lit 304)))) key →
          (∀ (e : Fin i.k),
              @Membership.mem.{0, 0} (Fin i.k) (List.{0} (Fin i.k)) (@List.instMembership.{0} (Fin i.k))
                  (@DecrAlmostLinearSSSP.Decremental.Exact.adjacency i.n i.k i.graph i.k v) e →
                @LT.lt.{0} Nat instLTNat
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) key (i.weight e))
                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                    (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i))) →
            have r :=
              @DecrAlmostLinearSSSP.Decremental.Exact.scanEdges i.n i.k i.graph
                (@DecrAlmostLinearSSSP.Decremental.live i.k deleted) i.weight settled key
                (@DecrAlmostLinearSSSP.Decremental.Exact.adjacency i.n i.k i.graph i.k v) tentative queue;
            ∃ cost t next,
              And
                (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.scan s
                  cost t)
                (And
                  (@LE.le.{0} Nat instLENat cost
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82)))
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        (@List.length.{0} (Fin i.k)
                          (@DecrAlmostLinearSSSP.Decremental.Exact.adjacency i.n i.k i.graph i.k v)))
                      (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
                  (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted
                    (@Prod.fst.{0, 0} (Fin i.n → Option.{0} Nat) (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))) r)
                    (@Insert.insert.{0, 0} (Fin i.n) (Finset.{0} (Fin i.n))
                      (@Finset.instInsert.{0} (Fin i.n) (instDecidableEqFin i.n)) v settled)
                    next (@Prod.snd.{0, 0} (Fin i.n → Option.{0} Nat) (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))) r) t)) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_7.2.2.2.2.2.2.2
section s0
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.RadixQueue
end DecrAlmostLinearSSSP.Decremental.RadixQueue
end s0
section s1
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.RadixQueue
end DecrAlmostLinearSSSP.Decremental.RadixQueue
end s1
section s2
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.RadixQueue
end DecrAlmostLinearSSSP.Decremental.RadixQueue
end s2
section s3
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s3
section s4
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s4
section s5
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s5
section s6
set_option autoImplicit false
open scoped ENNReal NNReal
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
attribute [local instance] Classical.propDecidable
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
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s15
section s16
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s16
section s17
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s17
section s18
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental.Structured
end s18
section s19
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact
open Structured
namespace Payload
end Payload
end DecrAlmostLinearSSSP.Decremental.Exact
end s19
section s20
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact
namespace LocatedTrie
end LocatedTrie
end DecrAlmostLinearSSSP.Decremental.Exact
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
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s24
section s25
set_option autoImplicit false
open scoped ENNReal NNReal
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
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end s27
section s28
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s28
section s29
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end s29
section s30
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Allocate
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Allocate
end s30
section s31
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePush
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.TriePush
end s31
section s32
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact
open Structured
namespace TriePush
end TriePush
end DecrAlmostLinearSSSP.Decremental.Exact
end s32
section s33
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePush
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.TriePush
end s33
section s34
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePush
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.TriePush
end s34
section s35
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePush
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.TriePush
end s35
section s36
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePush
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.TriePush
end s36
section s37
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePush
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.TriePush
end s37
section s38
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end s38
section s39
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end s39
section s40
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end s40
section s41
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePush
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.TriePush
end s41
section s42
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePush
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.TriePush
end s42
section s43
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie
end DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie
end s43
section s44
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePush
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.TriePush
end s44
section s45
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie
end DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie
end s45
section s46
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePush
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.TriePush
end s46
section s47
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePush
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.TriePush
end s47
section s48
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePush
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.TriePush
end s48
section s49
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePush
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.TriePush
end s49
section s50
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePush
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.TriePush
end s50
section s51
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePush
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.TriePush
end s51
section s52
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePop
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.TriePop
end s52
section s53
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePop
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.TriePop
end s53
section s54
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePop
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.TriePop
end s54
section s55
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePop
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.TriePop
end s55
section s56
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePop
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.TriePop
end s56
section s57
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact
open Structured
namespace TriePop
end TriePop
end DecrAlmostLinearSSSP.Decremental.Exact
end s57
section s58
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie
end DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie
end s58
section s59
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePop
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.TriePop
end s59
section s60
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePop
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.TriePop
end s60
section s61
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s61
section s62
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s62
section s63
set_option autoImplicit false
open Filter
open scoped Topology
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s63
section s64
set_option autoImplicit false
open Filter
open scoped Topology
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s64
section s65
set_option autoImplicit false
open Filter
open scoped Topology
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s65
section s66
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact
end DecrAlmostLinearSSSP.Decremental.Exact
end s66
section s67
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Powers
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Powers
end s67
section s68
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s68
section s69
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s69
section s70
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s70
section s71
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s71
section s72
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s72
section s73
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end s73
section s74
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end s74
section s75
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end s75
section s76
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.InputCapture
open Structured
end DecrAlmostLinearSSSP.Decremental.InputCapture
end s76
section s77
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Powers
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Powers
end s77
section s78
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Layout
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Layout
end s78
section s79
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Clear
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Clear
end s79
section s80
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s80
section s81
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s81
section s82
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s82
section s83
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s83
section s84
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s84
section s85
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s85
section s86
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact
end DecrAlmostLinearSSSP.Decremental.Exact
end s86
section s87
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact
end DecrAlmostLinearSSSP.Decremental.Exact
end s87
section s88
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact
end DecrAlmostLinearSSSP.Decremental.Exact
end s88
section s89
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact
end DecrAlmostLinearSSSP.Decremental.Exact
end s89
section s90
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact
end DecrAlmostLinearSSSP.Decremental.Exact
end s90
section s91
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact
end DecrAlmostLinearSSSP.Decremental.Exact
end s91
section s92
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact
end DecrAlmostLinearSSSP.Decremental.Exact
end s92
section s93
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild
end s93
section s94
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild
end s94
section s95
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s95
section s96
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact
open Structured
namespace Adjacency
end Adjacency
end DecrAlmostLinearSSSP.Decremental.Exact
end s96
section s97
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Adjacency
end DecrAlmostLinearSSSP.Decremental.Exact.Adjacency
end s97
section s98
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Adjacency
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Adjacency
end s98
section s99
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild
end s99
section s100
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild
open Structured
attribute [local irreducible] advanced
end DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild
end s100
section s101
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
namespace DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild
end s101
section s102
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild
end s102
section s103
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s103
section s104
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact
namespace Adjacency
end Adjacency
end DecrAlmostLinearSSSP.Decremental.Exact
end s104
section s105
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Adjacency
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Adjacency
end s105
section s106
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact
end s106
section s107
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Layout
end DecrAlmostLinearSSSP.Decremental.Exact.Layout
end s107
section s108
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact
end DecrAlmostLinearSSSP.Decremental.Exact
end s108
section s109
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Heap
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Heap
end s109
section s110
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Heap
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Heap
end s110
section s111
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Heap
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Heap
end s111
section s112
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s112
section s113
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s113
section s114
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Heap
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Heap
end s114
section s115
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s115
section s116
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s116
section s117
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s117
section s118
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Heap
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Heap
end s118
section s119
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s119
section s120
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact
end s120
section s121
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s121
section s122
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s122
section s123
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s123
section s124
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact
end DecrAlmostLinearSSSP.Decremental.Exact
end s124
section s125
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact
end DecrAlmostLinearSSSP.Decremental.Exact
end s125
section s126
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact
end DecrAlmostLinearSSSP.Decremental.Exact
end s126
section s127
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental.Exact
end s127
section s128
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s128
section s129
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s129
section s130
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s130
section s131
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s131
section s132
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s132
section s133
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s133
section s134
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Adjacency
end DecrAlmostLinearSSSP.Decremental.Exact.Adjacency
end s134
section s135
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact
end DecrAlmostLinearSSSP.Decremental.Exact
end s135
section s136
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact
end DecrAlmostLinearSSSP.Decremental.Exact
end s136
section s137
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s137
section s138
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s138
section s139
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s139
section s140
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
lemma popped_eval (s : Data) : Eval (Structured.sequence (poppedAtoms.map Cmd.atom)) s 4 (poppedData s) := eval_sequence_atoms poppedAtoms s
lemma popped_nat_frame (j : ℕ) (hk : j∉({304,306,318,320} : Finset ℕ)) : NatFrame (Structured.sequence (poppedAtoms.map Cmd.atom)) j := by
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hk
  simp [poppedAtoms,Structured.sequence,NatFrame,writesNat] <;> tauto
lemma popped_real_frame (j : ℕ) : RealFrame (Structured.sequence (poppedAtoms.map Cmd.atom)) j := by
  simp [poppedAtoms,Structured.sequence,RealFrame,writesReal]
lemma Memory.popped {i : Input} {deleted : List (Fin i.k)} {tentative : Fin i.n → Option ℕ}
    {settled : Finset (Fin i.n)} {tree : LocatedTrie (heapHeight i)} {queue : Multiset (ℕ × Fin i.n)} {s : Data}
    (h : Memory i deleted tentative settled tree queue s) (key : ℕ) (v : Fin i.n)
    (h260 : s.natReg 260=key) (h262 : s.natReg 262=v.val) :
    Memory i deleted tentative settled tree queue (poppedData s) ∧
      (poppedData s).natReg 304=key ∧ (poppedData s).natReg 306=v.val ∧
      (poppedData s).natReg 320=(if v∈settled then 1 else 0) := by
  have he := popped_eval s
  refine ⟨?_,?_,?_,?_⟩
  · exact h.register_frame (fun j hj => he.nat_frame (popped_nat_frame j (by
      simp only [Finset.mem_insert,Finset.mem_singleton,not_or];omega)))
      (he.real_frame (popped_real_frame 56)) rfl rfl
  all_goals simp [poppedData,poppedAtoms,Atom.effect,instructionEffect,data,Data.machine,
    h260,h262,h.heap.zero,h.layoutRegs.settled,h.settled v]
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s140
section s141
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact
attribute [local instance] Classical.propDecidable
lemma remainingDegree_empty {n k : ℕ} (g : Digraph n k) : remainingDegree g ∅ = k := by
  simpa only [remainingDegree,Finset.sdiff_empty] using adjacency_total g k le_rfl
lemma remainingDegree_insert {n k : ℕ} (g : Digraph n k) (settled : Finset (Fin n)) (v : Fin n) (hv : v∉settled) :
    remainingDegree g (insert v settled)+(adjacency g k v).length=remainingDegree g settled := by
  unfold remainingDegree
  rw [Finset.sdiff_insert]
  exact Finset.sum_erase_add _ _ (by simp [hv])
lemma potential_skip {n k : ℕ} (g : Digraph n k) (settled : Finset (Fin n))
    (key : ℕ) (v : Fin n) (queue : Multiset (ℕ × Fin n)) :
    queuePotential g settled queue+1 = queuePotential g settled ((key,v)::ₘqueue) := by
  simp [queuePotential,Multiset.card_cons,Nat.add_assoc]
lemma potential_settle {n k : ℕ} (g : Digraph n k) (settled : Finset (Fin n))
    (key : ℕ) (v : Fin n) (queue next : Multiset (ℕ × Fin n)) (hv : v∉settled)
    (hc : next.card ≤ queue.card+(adjacency g k v).length) :
    queuePotential g (insert v settled) next+(adjacency g k v).length+1 ≤
      queuePotential g settled ((key,v)::ₘqueue) := by
  have hd := remainingDegree_insert g settled v hv
  simp only [queuePotential,Multiset.card_cons]
  omega
lemma potential_initial {n k : ℕ} (g : Digraph n k) (source : Fin n) :
    queuePotential g ∅ ({(0,source)} : Multiset (ℕ × Fin n)) = 2*k+1 := by
  simp [queuePotential,remainingDegree_empty]
end DecrAlmostLinearSSSP.Decremental.Exact
end s141
section s142
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
lemma eval_loop_amortized {G : Type} (test : Test) (body : Cmd) (invariant : G → Data → Prop)
    (potential : G → ℕ) (charge : ℕ)
    (step : ∀ g s, invariant g s → test.holds s →
      ∃ g' t cost, Eval body s cost t ∧ invariant g' t ∧ potential g'<potential g ∧
        cost+2 ≤ charge*(potential g-potential g'))
    (g : G) (s : Data) (hi : invariant g s) :
    ∃ g' t cost, Eval (.loop test body) s cost t ∧ invariant g' t ∧ ¬test.holds t ∧
      cost ≤ charge*potential g+2 := by
  classical
  have aux : ∀ bound g s, potential g=bound → invariant g s →
      ∃ g' t cost, Eval (.loop test body) s cost t ∧ invariant g' t ∧ ¬test.holds t ∧
        cost ≤ charge*potential g+2 := by
    intro bound
    induction bound using Nat.strong_induction_on with
    | h bound ih =>
      intro g s hp hi
      by_cases ht : test.holds s
      · obtain ⟨g',u,c,he,hi',hdrop,hc⟩ := step g s hi ht
        obtain ⟨g'',t,d,het,hit,hstop,hd⟩ := ih (potential g') (by omega) g' u rfl hi'
        refine ⟨g'',t,c+d+2,Eval.loopYes ht he het,hit,hstop,?_⟩
        have hsplit : charge*potential g = charge*(potential g-potential g')+charge*potential g' := by
          rw [←Nat.mul_add, Nat.sub_add_cancel (by omega)]
        omega
      · exact ⟨g,s,2,Eval.loopNo s ht,hi,ht,by omega⟩
  exact aux (potential g) g s rfl hi
end DecrAlmostLinearSSSP.Decremental.Structured
end s142
section s143
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s143
section s144
set_option autoImplicit false
open scoped ENNReal NNReal
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
lemma body_append {s u v w t : Data} {cp cs cq : ℕ} (hp : Eval TriePop.code s cp u)
    (hc : Eval (Structured.sequence (poppedAtoms.map Cmd.atom)) u 4 v)
    (hs : Eval (.branch (.natLess 320 26) scan .skip) v cs w)
    (hq : Eval queueCount w cq t) : Eval body s (cp+(4+(cs+cq))) t := Eval.seq hp (Eval.seq hc (Eval.seq hs hq))
lemma State.step {i : Input} {deleted : List (Fin i.k)} (hi : i.Valid) (q : State i deleted) (s : Data)
    (hs : q.memory s) (htest : (Test.natLess 56 348).holds s) :
    ∃ (next : State i deleted) (t : Data) (cost : ℕ), Eval body s cost t ∧ next.memory t ∧
      next.potential<q.potential ∧ cost+2 ≤ (200*(heapHeight i+1))*(q.potential-next.potential) := by
  have hpositive : 0<q.queue.card := by
    change s.natReg 56<s.natReg 348 at htest
    rw [hs.1.heap.zero,hs.2] at htest
    exact htest
  obtain ⟨cp,u,utree,key,v,remaining,hpop,hcp,hu,hkey,hvertex,hqueue,hmin⟩ := hs.1.pop hpositive
  have hlabels : LabelInvariant i.graph (live deleted) i.weight i.source q.tentative q.settled ((key,v)::ₘremaining) := by
    simpa only [hqueue] using q.labels
  have hminRemaining (item : ℕ × Fin i.n) (hitem : item∈remaining) : key ≤ item.1 := by
    apply hmin
    rw [hqueue];exact Multiset.mem_cons_of_mem hitem
  obtain ⟨hv,hvkey,hvvertex,hvsettled⟩ := hu.popped key v hkey hvertex
  let w := poppedData u
  have hwUnit : w.natReg 26=1 := hv.heap.unit
  change w.natReg 320=(if v∈q.settled then 1 else 0) at hvsettled
  by_cases hsettled : v∈q.settled
  · have hvalue : w.natReg 320=1 := by simpa only [if_pos hsettled] using hvsettled
    have ht : ¬(Test.natLess 320 26).holds w := by simp [Test.holds,hvalue,hwUnit]
    let next : State i deleted := ⟨q.tentative,q.settled,remaining,utree,hlabels.skip_settled key v hsettled⟩
    obtain ⟨cq,hcq,hcqBound,hmem,hcount⟩ := hv.queueCount
    have hp : next.potential+1=q.potential := by
      change queuePotential i.graph q.settled remaining+1=queuePotential i.graph q.settled q.queue
      rw [hqueue];exact potential_skip i.graph q.settled key v remaining
    have hdiff : q.potential-next.potential=1 := by omega
    refine ⟨next,counted w,cp+(4+(2+cq)),body_append hpop (popped_eval u) (Eval.branchNo ht (Eval.skip w)) hcq,
      ⟨hmem,hcount⟩,by omega,?_⟩
    rw [hdiff,Nat.mul_one]
    omega
  · have hvalue : w.natReg 320=0 := by simpa only [if_neg hsettled] using hvsettled
    have ht : (Test.natLess 320 26).holds w := by simp [Test.holds,hvalue,hwUnit]
    have hpopExact := hlabels.pop_exact key v (Multiset.mem_cons_self _ _) (by
      intro item himem
      rcases Multiset.mem_cons.mp himem with hh | hh
      · subst item;exact le_rfl
      · exact hminRemaining item hh) hsettled
    have hreach := reachable_of_nat_bound i.graph (live deleted) (fun e => (i.weight e : ℝ≥0∞)) i.source v key hpopExact.2.le
    have hbound (e : Fin i.k) : key+i.weight e < 2^(heapHeight i) :=
      (candidate_key_bound i hi (live deleted) v key hpopExact.2 hreach e).trans_lt (height_spec (i.n*i.W))
    obtain ⟨cs,z,ztree,hscan,hcs,hz⟩ := hv.scan v key hvvertex hvkey (fun e _ => hbound e)
    let r := scanEdges i.graph (live deleted) i.weight q.settled key (adjacency i.graph i.k v) q.tentative remaining
    have hr := scan_outgoing hlabels hsettled hminRemaining
    let next : State i deleted := ⟨r.1,insert v q.settled,r.2,ztree,hr.1⟩
    obtain ⟨cq,hcq,hcqBound,hmem,hcount⟩ := hz.queueCount
    have hdrop : next.potential+(adjacency i.graph i.k v).length+1 ≤ q.potential := by
      change queuePotential i.graph (insert v q.settled) r.2+(adjacency i.graph i.k v).length+1 ≤ queuePotential i.graph q.settled q.queue
      rw [hqueue]
      exact potential_settle i.graph q.settled key v remaining r.2 hsettled hr.2
    refine ⟨next,counted z,cp+(4+((cs+1)+cq)),body_append hpop (popped_eval u) (Eval.branchYes ht hscan) hcq,
      ⟨hmem,hcount⟩,by omega,?_⟩
    have hphi : (adjacency i.graph i.k v).length+1 ≤ q.potential-next.potential := by omega
    have hcharge := Nat.mul_le_mul_left (200*(heapHeight i+1)) hphi
    have hcost : cp+(4+((cs+1)+cq))+2 ≤ (200*(heapHeight i+1))*((adjacency i.graph i.k v).length+1) := by
      nlinarith
    exact hcost.trans hcharge
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s144
section s145
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
lemma State.run {i : Input} {deleted : List (Fin i.k)} (hi : i.Valid) (q : State i deleted) (s : Data)
    (hs : q.memory s) :
    ∃ (next : State i deleted) (t : Data) (cost : ℕ), Eval loop s cost t ∧ next.memory t ∧ next.queue=0 ∧
      cost ≤ 200*(heapHeight i+1)*q.potential+2 ∧
      (∀ v : Fin i.n, stored t.machine v.val=i.dist deleted v) := by
  obtain ⟨next,t,cost,he,ht,hstop,hcost⟩ := eval_loop_amortized (.natLess 56 348) body State.memory State.potential
    (200*(heapHeight i+1)) (fun q s hmem htest => q.step hi s hmem htest) q s hs
  have hzero : next.queue.card=0 := by
    change ¬t.natReg 56<t.natReg 348 at hstop
    rw [ht.1.heap.zero,ht.2] at hstop
    omega
  have hq : next.queue=0 := Multiset.card_eq_zero.mp hzero
  refine ⟨next,t,cost,he,ht,hq,hcost,?_⟩
  have hlabels := next.labels
  rw [hq] at hlabels
  intro v
  have hf := hlabels.finished v
  exact (ht.1.tentative.stored v).trans hf.1.symm
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s145
section s146
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
lemma State.source_normalized {i : Input} {deleted : List (Fin i.k)} (q : State i deleted) (s : Data)
    (h : Memory i deleted q.tentative q.settled q.tree q.queue s) :
    stored s.machine i.source.val=0 ∧
      (∀ v : Fin i.n, s.natMem v.val≤1 ∧ (s.natMem v.val=0 → 0 ≤ s.realMem v.val)) := by
  constructor
  · rw [h.tentative.stored i.source,q.labels.sourceZero];simp [tentativeValue]
  · intro v
    cases ht : q.tentative v with
    | none =>
      have hf := h.tentative.infinite v ht
      rw [hf];simp
    | some d =>
      have hf := h.tentative.finite v d ht
      rw [hf.1,hf.2.2]
      exact ⟨by omega,fun _ => Nat.cast_nonneg d⟩
lemma State.exact_infinity {i : Input} {deleted : List (Fin i.k)} (q : State i deleted) (s : Data)
    (h : Memory i deleted q.tentative q.settled q.tree q.queue s) (hq : q.queue=0) :
    ∀ v : Fin i.n, stored s.machine v.val=i.dist deleted v ∧
      (stored s.machine v.val=⊤ ↔ ¬Reachable i.graph (live deleted) i.source v) := by
  have hl := q.labels
  rw [hq] at hl
  intro v
  have hf := hl.finished v
  refine ⟨(h.tentative.stored v).trans hf.1.symm,?_⟩
  rw [h.tentative.stored v,← hf.2]
  cases q.tentative v <;> simp [tentativeValue]
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s146
section s147
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
lemma resetBody_eval (s : Data) : Eval resetBody s 4 (resetAdvanced s) := eval_sequence_atoms resetBodyAtoms s
lemma resetBody_fields (s : Data) (hz : s.natReg 56=0) (h1 : s.natReg 26=1) :
    (resetAdvanced s).natMem=Function.update (Function.update s.natMem (s.natReg 340) 1) (s.natReg 226+s.natReg 340) 0 ∧
      (resetAdvanced s).natReg 340=s.natReg 340+1 ∧ (resetAdvanced s).realMem=s.realMem := by
  simp [resetAdvanced,resetBodyAtoms,Atom.effect,instructionEffect,data,Data.machine,hz,h1]
lemma resetBody_nat_frame (j : ℕ) (h340 : j≠340) (h342 : j≠342) : NatFrame resetBody j := by
  simp [resetBody,resetBodyAtoms,Structured.sequence,NatFrame,writesNat,Ne.symm h340,Ne.symm h342]
lemma resetLoop_nat_frame (j : ℕ) (h340 : j≠340) (h342 : j≠342) : NatFrame resetLoop j := resetBody_nat_frame j h340 h342
lemma resetLoop_real_frame (j : ℕ) : RealFrame resetLoop j := by
  simp [resetLoop,resetBody,resetBodyAtoms,Structured.sequence,RealFrame,writesReal]
lemma resetLoop_eval (bank start remaining : ℕ) (s : Data)
    (hz : s.natReg 56=0) (h1 : s.natReg 26=1) (hb : s.natReg 226=bank)
    (hp : s.natReg 340=start) (he : s.natReg 66=start+remaining) (hsep : start+remaining ≤ bank) :
    ∃ t, Eval resetLoop s (6*remaining+2) t ∧ t.natReg 340=start+remaining ∧
      (∀ j, start≤j → j<start+remaining → t.natMem j=1 ∧ t.natMem (bank+j)=0) ∧
      t.realMem=s.realMem ∧
      (∀ a, (a<start ∨ start+remaining≤a) → (a<bank+start ∨ bank+start+remaining≤a) → t.natMem a=s.natMem a) := by
  induction remaining generalizing start s with
  | zero =>
    refine ⟨s,?_,by simpa using hp,?_,rfl,fun _ _ _ => rfl⟩
    · exact Eval.loopNo s (by simp [Test.holds,hp,he])
    · intro j hlow hhigh;omega
  | succ remaining ih =>
    let u := resetAdvanced s
    have hu := resetBody_eval s
    have huf (j : ℕ) (h340 : j≠340) (h342 : j≠342) := hu.nat_frame (resetBody_nat_frame j h340 h342)
    have huz : u.natReg 56=0 := (huf 56 (by omega) (by omega)).trans hz
    have hu1 : u.natReg 26=1 := (huf 26 (by omega) (by omega)).trans h1
    have hub : u.natReg 226=bank := (huf 226 (by omega) (by omega)).trans hb
    have hum : u.natMem=Function.update (Function.update s.natMem start 1) (bank+start) 0 := by
      simpa only [hb,hp] using (resetBody_fields s hz h1).1
    have hup : u.natReg 340=start+1 := by simpa only [hp] using (resetBody_fields s hz h1).2.1
    have hue : u.natReg 66=(start+1)+remaining := by rw [huf 66 (by omega) (by omega),he];omega
    obtain ⟨t,ht,htp,htvalues,htr,htframe⟩ := ih (start+1) u huz hu1 hub hup hue (by omega)
    have htest : (Test.natLess 340 66).holds s := by simp [Test.holds,hp,he]
    refine ⟨t,?_,by omega,?_,htr.trans (resetBody_fields s hz h1).2.2,?_⟩
    · have hh := Eval.loopYes htest hu ht
      convert hh using 1 <;> first | rfl | omega
    · intro j hlow hhigh
      by_cases hj : j=start
      · subst j
        constructor
        · rw [htframe start (Or.inl (by omega)) (Or.inl (by omega)),hum,
            Function.update_of_ne (by omega),Function.update_self]
        · rw [htframe (bank+start) (Or.inr (by omega)) (Or.inl (by omega)),hum,Function.update_self]
      · exact htvalues j (by omega) (by omega)
    · intro a hout hbankout
      rw [htframe a (by omega) (by omega),hum,Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s147
section s148
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
lemma Memory.ready {i : Input} {deleted : List (Fin i.k)} {tentative : Fin i.n → Option ℕ}
    {settled : Finset (Fin i.n)} {tree : LocatedTrie (heapHeight i)} {queue : Multiset (ℕ × Fin i.n)} {s : Data}
    (h : Memory i deleted tentative settled tree queue s) : Ready i deleted s :=
  ⟨h.heap.zero,h.heap.unit,h.vertices,h.edges,h.source,h.zeroR,h.layoutRegs,h.graph,h.active,
    h.heap.height,h.heap.powerPtr,h.heap.slotReg,h.heap.powers⟩
lemma Ready.frame {i : Input} {deleted : List (Fin i.k)} {s t : Data} (h : Ready i deleted s)
    (hn : ∀ j, j≤246 → t.natReg j=s.natReg j) (hr : t.realReg 56=s.realReg 56)
    (hgraph : Adjacency.StaticImage i (layout i) t) (hactive : Adjacency.ActiveImage i (layout i) deleted t)
    (hp : ∀ j<heapHeight i, t.natMem (heapBase i+j)=s.natMem (heapBase i+j)) : Ready i deleted t := by
  refine ⟨(hn 56 (by omega)).trans h.zero,(hn 26 (by omega)).trans h.unit,
    (hn 66 (by omega)).trans h.vertices,(hn 68 (by omega)).trans h.edges,
    (hn 72 (by omega)).trans h.source,hr.trans h.zeroR,?_,hgraph,hactive,
    (hn 236 (by omega)).trans h.height,?_,(hn 246 (by omega)).trans h.slotReg,?_⟩
  · constructor
    · exact (hn 224 (by omega)).trans h.layoutRegs.heads
    · exact (hn 226 (by omega)).trans h.layoutRegs.settled
    · exact (hn 228 (by omega)).trans h.layoutRegs.active
    · exact (hn 230 (by omega)).trans h.layoutRegs.distances
    · exact (hn 232 (by omega)).trans h.layoutRegs.nodes
    · exact (hn 234 (by omega)).trans h.layoutRegs.powers
  · intro hh;rw [hn 238 (by omega)];exact h.powerPtr hh
  · intro j hj;rw [hp j hj];exact h.powers j hj
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s148
section s149
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.InputCapture
open Structured
lemma Captured.frame {i : Input} {s t : Data} (h : Captured i s)
    (hn : ∀ j, j≤74 → t.natReg j=s.natReg j) (hr : ∀ j, j≤64 → t.realReg j=s.realReg j) : Captured i t :=
  ⟨(hn 56 (by omega)).trans h.zeroN,(hr 56 (by omega)).trans h.zeroR,
    (hn 26 (by omega)).trans h.unit,(hn 14 (by omega)).trans h.two,
    (hn 34 (by omega)).trans h.scanZero,(hn 36 (by omega)).trans h.scanUnit,
    (hn 64 (by omega)).trans h.size,(hn 66 (by omega)).trans h.vertices,
    (hn 68 (by omega)).trans h.edges,(hn 70 (by omega)).trans h.weightBound,
    (hn 72 (by omega)).trans h.source,(hr 64 (by omega)).trans h.accuracy,
    (hn 74 (by omega)).trans h.base,(hn 48 (by omega)).trans h.utilityBase,
    (hn 58 (by omega)).trans h.factor,(hr 58 (by omega)).trans h.argument⟩
end DecrAlmostLinearSSSP.Decremental.InputCapture
end s149
section s150
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
lemma install_eval (s : Data) : Eval install s 3 (installed s) := eval_sequence_atoms installAtoms s
lemma install_nat_frame (j : ℕ) (h236 : j≠236) (h238 : j≠238) (h246 : j≠246) : NatFrame install j := by
  simp [install,installAtoms,Structured.sequence,NatFrame,writesNat,Ne.symm h236,Ne.symm h238,Ne.symm h246]
lemma install_real_frame (j : ℕ) : RealFrame install j := by simp [install,installAtoms,Structured.sequence,RealFrame,writesReal]
lemma install_ready (i : Input) (s : Data) (h : InputCapture.Captured i s)
    (hl : Layout.Image (layout i) s) (hg : Adjacency.StaticImage i (layout i) s)
    (ha : Adjacency.ActiveImage i (layout i) [] s)
    (hp : Powers.Prefix (i.n*i.W) (heapBase i) (heapHeight i) s) : Ready i [] (installed s) := by
  have he := install_eval s
  have hm : (installed s).natMem=s.natMem := by rfl
  have hn (j : ℕ) (h236 : j≠236) (h238 : j≠238) (h246 : j≠246) := he.nat_frame (install_nat_frame j h236 h238 h246)
  refine ⟨(hn 56 (by omega) (by omega) (by omega)).trans h.zeroN,
    (hn 26 (by omega) (by omega) (by omega)).trans h.unit,
    (hn 66 (by omega) (by omega) (by omega)).trans h.vertices,
    (hn 68 (by omega) (by omega) (by omega)).trans h.edges,
    (hn 72 (by omega) (by omega) (by omega)).trans h.source,
    (he.real_frame (install_real_frame 56)).trans h.zeroR,?_,hg.frame (fun a _ => congrFun hm a),(by intro e;rw [hm];exact ha e),?_,?_,?_,(fun j hj => (congrFun hm _).trans (hp.entries j hj))⟩
  · constructor
    · exact (hn 224 (by omega) (by omega) (by omega)).trans hl.heads
    · exact (hn 226 (by omega) (by omega) (by omega)).trans hl.settled
    · exact (hn 228 (by omega) (by omega) (by omega)).trans hl.active
    · exact (hn 230 (by omega) (by omega) (by omega)).trans hl.distances
    · exact (hn 232 (by omega) (by omega) (by omega)).trans hl.nodes
    · exact (hn 234 (by omega) (by omega) (by omega)).trans hl.powers
  · simp [installed,installAtoms,Atom.effect,instructionEffect,data,Data.machine,h.zeroN,hp.index]
  · intro hne
    have hh : 1 ≤ heapBase i+heapHeight i := by omega
    simp [installed,installAtoms,Atom.effect,instructionEffect,data,Data.machine,h.unit,hp.pointer,Nat.sub_add_cancel hh]
  · simp [installed,installAtoms,Atom.effect,instructionEffect,data,Data.machine,h.zeroN,hp.pointer,heapSlot]
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s150
section s151
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
lemma powers_real_frame (j : ℕ) (hj : j≤64) : RealFrame Powers.code j := by
  refine ⟨?_,Powers.body_real_frame j (by omega)⟩
  simp [Powers.prepare,Powers.prepareAtoms,Structured.sequence,RealFrame,writesReal]
  omega
lemma Preparation.powers {i : Input} {s : Data} (h : Preparation i s) :
    ∃ t, Eval (.seq Powers.code install) s (7*heapHeight i+14) t ∧ Ready i [] t := by
  obtain ⟨u,he,hp,hr,hm⟩ := Powers.eval_code i (heapBase i) s h.captured h.layoutRegs.powers
  have hn (j : ℕ) (h248 : j≠248) (h250 : j≠250) (h252 : j≠252) := he.nat_frame (Powers.nat_frame j h248 h250 h252)
  have huc : InputCapture.Captured i u := h.captured.frame
    (fun j hj => hn j (by omega) (by omega) (by omega)) (fun j hj => he.real_frame (powers_real_frame j hj))
  have hul : Layout.Image (layout i) u := by
    constructor
    · exact (hn 224 (by omega) (by omega) (by omega)).trans h.layoutRegs.heads
    · exact (hn 226 (by omega) (by omega) (by omega)).trans h.layoutRegs.settled
    · exact (hn 228 (by omega) (by omega) (by omega)).trans h.layoutRegs.active
    · exact (hn 230 (by omega) (by omega) (by omega)).trans h.layoutRegs.distances
    · exact (hn 232 (by omega) (by omega) (by omega)).trans h.layoutRegs.nodes
    · exact (hn 234 (by omega) (by omega) (by omega)).trans h.layoutRegs.powers
  have hug : Adjacency.StaticImage i (layout i) u := h.graph.frame (by
    intro a ha
    apply hm a
    exact Or.inl (Layout.static_bounds i a ha))
  have hua : Adjacency.ActiveImage i (layout i) [] u := by
    intro e
    have hb : (layout i).active+e.val < heapBase i := (Layout.edge_bounds i e 0 (by omega)).1
    rw [hm ((layout i).active+e.val) (Or.inl hb)]
    exact h.active e
  refine ⟨installed u,?_,install_ready i u huc hul hug hua hp⟩
  have hh := Eval.seq he (install_eval u)
  convert hh using 1 <;> first | rfl | omega
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s151
section s152
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.InputCapture
open Structured
lemma raw_initial (p : Program) (i : Input) : RawInput i (data (initialMachine p i)) := by
  constructor <;> simp [data,initialMachine]
lemma captures_raw (i : Input) (s : Data) (h : RawInput i s) : Captured i (result s) := by
  constructor <;> simp [result,atoms,Atom.effect,instructionEffect,data,Data.machine,
    h.vertices,h.edges,h.size,h.weightBound,h.source,h.accuracy]
  all_goals omega
end DecrAlmostLinearSSSP.Decremental.InputCapture
end s152
section s153
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
lemma prepareGraph_eval (i : Input) (s : Data) (hraw : InputCapture.RawInput i s) (htape : Adjacency.Tape i s) :
    ∃ t, Eval prepareGraph s (4*i.n+22*i.k+37) t ∧ Preparation i t := by
  let u := InputCapture.result s
  have heu := InputCapture.eval_code s
  have huc := InputCapture.captures_raw i s hraw
  have huMem := heu.no_memory InputCapture.no_memory
  have huTape : Adjacency.Tape i u := Adjacency.tape_frame i s u htape (fun a _ => congrFun huMem.2 a)
  let v := Layout.result u
  have hev := Layout.eval_code u
  have hvl : Layout.Image (layout i) v := Layout.values i u huc
  have hvc : InputCapture.Captured i v := huc.frame (fun j hj => hev.nat_frame
    (Layout.nat_frame j (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)))
    (fun j _ => hev.real_frame (Layout.real_frame j))
  have hvMem := hev.no_memory Layout.no_memory
  have hvTape : Adjacency.Tape i v := Adjacency.tape_frame i u v huTape (fun a _ => congrFun hvMem.2 a)
  obtain ⟨t,het,ht,htr,htf⟩ := AdjacencyBuild.code_eval i v hvc.zeroN hvc.unit hvc.vertices hvc.edges hvl hvTape
  have htc : InputCapture.Captured i t := hvc.frame (fun j hj => het.nat_frame
    (AdjacencyBuild.code_nat_frame j (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or];omega)))
    (fun j _ => het.real_frame (AdjacencyBuild.code_real_frame j))
  refine ⟨t,?_,⟨htc,ht.layout,ht.image.static,ht.image.active_initial⟩⟩
  have he := Eval.seq heu (Eval.seq hev het)
  convert he using 1 <;> first | rfl | omega
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s153
section s154
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
lemma Ready.register_frame {i : Input} {deleted : List (Fin i.k)} {s t : Data} (h : Ready i deleted s)
    (hn : ∀ j, j≤246 → t.natReg j=s.natReg j) (hr : t.realReg 56=s.realReg 56)
    (hm : t.natMem=s.natMem) : Ready i deleted t := by
  apply h.frame hn hr (h.graph.frame (fun a _ => congrFun hm a))
  · intro e;rw [hm];exact h.active e
  · intro j _;exact congrFun hm _
lemma Ready.reset {i : Input} {deleted : List (Fin i.k)} {s : Data} (h : Ready i deleted s) :
    ∃ t, Eval (.seq resetPrepare resetLoop) s (6*i.n+3) t ∧ Ready i deleted t ∧
      (∀ v : Fin i.n, t.natMem v.val=1 ∧ t.natMem ((layout i).settled+v.val)=0) ∧ t.realMem=s.realMem := by
  let u : Data := {s with natReg := Function.update s.natReg 340 0}
  have hePrepare : Eval resetPrepare s 1 u := eval_natural s 340 0
  have hu : Ready i deleted u := h.register_frame (fun j hj => by simp [u,Function.update_of_ne (show j≠340 by omega)]) rfl rfl
  obtain ⟨t,he,htindex,htvalues,hreal,hframe⟩ := resetLoop_eval (layout i).settled 0 i.n u hu.zero hu.unit hu.layoutRegs.settled
    (by simp [u]) (by simpa using hu.vertices) (by dsimp [layout,Layout.addresses];omega)
  have htBelow (a : ℕ) (hpublic : i.n≤a) (hsettled : a<(layout i).settled ∨ (layout i).settled+i.n≤a) : t.natMem a=s.natMem a :=
    hframe a (Or.inr (by simpa using hpublic)) (by simpa only [Nat.add_zero] using hsettled)
  have hn (j : ℕ) (hj : j≤246) : t.natReg j=s.natReg j :=
    (he.nat_frame (resetLoop_nat_frame j (by omega) (by omega))).trans (by simp [u,Function.update_of_ne (show j≠340 by omega)])
  have htReady : Ready i deleted t := by
    apply h.frame hn (he.real_frame (resetLoop_real_frame 56))
    · apply h.graph.frame
      intro a ha
      simp only [Adjacency.staticFootprint,Finset.mem_union,Finset.mem_Ico] at ha
      apply htBelow a
      · dsimp [layout,Layout.addresses] at ha;rcases ha with ha | ha <;> omega
      · dsimp [layout,Layout.addresses] at ha ⊢;rcases ha with ha | ha
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)
    · intro e
      rw [htBelow _ (by dsimp [layout,Layout.addresses];omega) (Or.inr (by dsimp [layout,Layout.addresses];omega))]
      exact h.active e
    · intro j hj
      apply htBelow
      · dsimp [heapBase,layout,Layout.addresses];omega
      · exact Or.inr (by dsimp [heapBase,layout,Layout.addresses];omega)
  refine ⟨t,?_,htReady,?_,hreal⟩
  · have hh := Eval.seq hePrepare he
    convert hh using 1 <;> first | rfl | omega
  · intro v
    exact htvalues v.val (by omega) (by have hv := v.isLt;omega)
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s154
section s155
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
lemma root_eval (s : Data) : Eval rootSetup s 8 (rootData s) := eval_sequence_atoms rootAtoms s
lemma root_nat_frame (j : ℕ) (h244 : j≠244) (h260 : j≠260) (h262 : j≠262) (h342 : j≠342) : NatFrame rootSetup j := by
  simp [rootSetup,rootAtoms,Structured.sequence,NatFrame,writesNat,Ne.symm h244,Ne.symm h260,Ne.symm h262,Ne.symm h342]
lemma root_real_frame (j : ℕ) : RealFrame rootSetup j := by simp [rootSetup,rootAtoms,Structured.sequence,RealFrame,writesReal]
lemma Ready.root_fields {i : Input} {deleted : List (Fin i.k)} {s : Data} (h : Ready i deleted s) :
    (rootData s).natMem=Function.update (Function.update (Function.update s.natMem (heapSlot i) 0) i.source.val 0)
      ((layout i).distances+i.source.val) 0 ∧
    (rootData s).realMem=Function.update s.realMem i.source.val 0 ∧
    (rootData s).natReg 244=heapSlot i+1 ∧ (rootData s).natReg 260=0 ∧ (rootData s).natReg 262=i.source.val := by
  simp [rootData,rootAtoms,Atom.effect,instructionEffect,data,Data.machine,h.slotReg,h.source,
    h.layoutRegs.distances,h.zero,h.zeroR,h.unit]
lemma Ready.root_memory {i : Input} {deleted : List (Fin i.k)} {s : Data} (h : Ready i deleted s)
    (hreset : ∀ v : Fin i.n, s.natMem v.val=1 ∧ s.natMem ((layout i).settled+v.val)=0) :
    Memory i deleted (initialTentative i.source) ∅ (.empty : LocatedTrie (heapHeight i)) 0 (rootData s) := by
  classical
  let t := rootData s
  obtain ⟨hm,hr,ha,hkey,hvertex⟩ := h.root_fields
  have he := root_eval s
  have hn (j : ℕ) (h244 : j≠244) (h260 : j≠260) (h262 : j≠262) (h342 : j≠342) :=
    he.nat_frame (root_nat_frame j h244 h260 h262 h342)
  have hsource := i.source.isLt
  have hsourceBelow : i.source.val<heapBase i := by
    dsimp [heapBase,layout,Layout.addresses];omega
  have hdistBelow : (layout i).distances+i.source.val<heapBase i := (Layout.vertex_bounds i i.source).2.2.2
  have hslotAbove : heapBase i≤heapSlot i := Nat.le_add_right _ _
  have hframe (a : ℕ) (hs : a≠heapSlot i) (hp : a≠i.source.val) (hd : a≠(layout i).distances+i.source.val) : t.natMem a=s.natMem a := by
    rw [hm,Function.update_of_ne hd,Function.update_of_ne hp,Function.update_of_ne hs]
  have htGraph : Adjacency.StaticImage i (layout i) t := by
    apply h.graph.frame
    intro a hab
    have hlow := Layout.static_bounds i a hab
    change a < heapBase i at hlow
    apply hframe a (by omega)
    · simp only [Adjacency.staticFootprint,Finset.mem_union,Finset.mem_Ico] at hab
      dsimp [layout,Layout.addresses] at hab;rcases hab with hab | hab <;> omega
    · simp only [Adjacency.staticFootprint,Finset.mem_union,Finset.mem_Ico] at hab
      dsimp [layout,Layout.addresses] at hab ⊢;rcases hab with hab | hab <;> omega
  have htActive : Adjacency.ActiveImage i (layout i) deleted t := by
    intro e
    have hlow := (Layout.edge_bounds i e 0 (by omega)).1
    change (layout i).active+e.val < heapBase i at hlow
    rw [hframe _ (by omega) (by dsimp [layout,Layout.addresses];omega)
      (by have he := e.isLt;dsimp [layout,Layout.addresses];omega)]
    exact h.active e
  have htPowers (j : ℕ) (hj : j<heapHeight i) : t.natMem (heapBase i+j)=2^j := by
    rw [hframe _ (by dsimp [heapSlot];omega) (by omega) (by omega)]
    exact h.powers j hj
  refine ⟨(hn 66 (by omega) (by omega) (by omega) (by omega)).trans h.vertices,
    (hn 68 (by omega) (by omega) (by omega) (by omega)).trans h.edges,
    (hn 72 (by omega) (by omega) (by omega) (by omega)).trans h.source,
    (he.real_frame (root_real_frame 56)).trans h.zeroR,?_,htGraph,htActive,?_,?_,?_⟩
  · constructor
    · exact (hn 224 (by omega) (by omega) (by omega) (by omega)).trans h.layoutRegs.heads
    · exact (hn 226 (by omega) (by omega) (by omega) (by omega)).trans h.layoutRegs.settled
    · exact (hn 228 (by omega) (by omega) (by omega) (by omega)).trans h.layoutRegs.active
    · exact (hn 230 (by omega) (by omega) (by omega) (by omega)).trans h.layoutRegs.distances
    · exact (hn 232 (by omega) (by omega) (by omega) (by omega)).trans h.layoutRegs.nodes
    · exact (hn 234 (by omega) (by omega) (by omega) (by omega)).trans h.layoutRegs.powers
  · intro v
    by_cases hv : v=i.source
    · subst v
      simp only [initialTentative,if_pos rfl]
      refine ⟨?_,?_,?_⟩
      · rw [hm,Function.update_of_ne (by dsimp [layout,Layout.addresses];omega),Function.update_self]
      · rw [hm,Function.update_self]
      · rw [hr,Function.update_self];simp
    · simp only [initialTentative,if_neg hv]
      have hvval : v.val≠i.source.val := fun hh => hv (Fin.ext hh)
      have hvlt := v.isLt
      rw [hframe _ (by have := public_below i v;omega) hvval (by dsimp [layout,Layout.addresses];omega)]
      exact (hreset v).1
  · intro v
    have hv := v.isLt
    rw [hframe _ (by have := settled_below i v;omega) (by dsimp [layout,Layout.addresses];omega)
      (by dsimp [layout,Layout.addresses];omega)]
    simpa using (hreset v).2
  · refine ⟨(hn 56 (by omega) (by omega) (by omega) (by omega)).trans h.zero,
      (hn 26 (by omega) (by omega) (by omega) (by omega)).trans h.unit,
      (hn 236 (by omega) (by omega) (by omega) (by omega)).trans h.height,?_,
      (hn 246 (by omega) (by omega) (by omega) (by omega)).trans h.slotReg,?_,trivial,trivial,?_,?_,htPowers,le_rfl,?_⟩
    · intro hh;rw [hn 238 (by omega) (by omega) (by omega) (by omega)];exact h.powerPtr hh
    · rw [ha];omega
    · intro a hh;simp [LocatedTrie.footprint] at hh
    · change t.natMem (heapSlot i)=0
      rw [hm,Function.update_of_ne (by omega),Function.update_of_ne (by omega),Function.update_self]
    · simp [queueMap,LocatedTrie.abstract,RadixQueue.entries]
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s155
section s156
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
lemma Ready.initialState {i : Input} {deleted : List (Fin i.k)} {s : Data} (h : Ready i deleted s)
    (hreset : ∀ v : Fin i.n, s.natMem v.val=1 ∧ s.natMem ((layout i).settled+v.val)=0) :
    ∃ (cost : ℕ) (t : Data) (q : State i deleted),
      Eval (.seq rootSetup (.seq TriePush.code queueCount)) s cost t ∧
      cost ≤ 43*(heapHeight i+1)+12 ∧ q.memory t ∧ q.potential=2*i.k+1 := by
  have hm := h.root_memory hreset
  have hv := h.root_fields
  obtain ⟨cp,u,next,hpush,hcp,hu⟩ := hm.push 0 i.source hv.2.2.2.1 hv.2.2.2.2 (Nat.pow_pos (by omega))
  let q : State i deleted := ⟨initialTentative i.source,∅,{(0,i.source)},next,
    labelInvariant_initial i.graph (live deleted) i.weight i.source⟩
  obtain ⟨cq,hcount,hcq,ht,hcard⟩ := hu.queueCount
  refine ⟨8+(cp+cq),counted u,q,Eval.seq (root_eval s) (Eval.seq hpush hcount),by omega,⟨ht,hcard⟩,?_⟩
  exact potential_initial i.graph i.source
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s156
section s157
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
lemma code_append {s u v t : Data} {cr cb cl : ℕ}
    (hr : Eval (.seq resetPrepare resetLoop) s cr u)
    (hb : Eval (.seq rootSetup (.seq TriePush.code queueCount)) u cb v) (hl : Eval loop v cl t) :
    Eval code s (cr+cb+cl) t := by
  cases hr with
  | seq hp hreset =>
    cases hb with
    | seq hroot hs =>
      cases hs with
      | seq hpush hcount =>
        have he := Eval.seq hp (Eval.seq hreset (Eval.seq hroot (Eval.seq hpush (Eval.seq hcount hl))))
        convert he using 1 <;> first | rfl | omega
lemma Ready.execute {i : Input} {deleted : List (Fin i.k)} {s : Data} (hi : i.Valid) (h : Ready i deleted s) :
    ∃ (cost : ℕ) (t : Data) (q : State i deleted), Eval code s cost t ∧
      cost ≤ 600*(i.n+i.k+1)*(heapHeight i+1) ∧ q.memory t ∧ q.queue=0 ∧ Ready i deleted t ∧
      stored t.machine i.source.val=0 ∧
      (∀ v : Fin i.n, t.natMem v.val≤1 ∧ (t.natMem v.val=0 → 0 ≤ t.realMem v.val)) ∧
      (∀ v : Fin i.n, stored t.machine v.val=i.dist deleted v ∧
        (stored t.machine v.val=⊤ ↔ ¬Reachable i.graph (live deleted) i.source v)) := by
  obtain ⟨u,heReset,hu,hreset,hResetReal⟩ := h.reset
  obtain ⟨cb,v,q0,heBoot,hcb,hq0,hp0⟩ := hu.initialState hreset
  obtain ⟨q,t,cl,heLoop,hqt,hqZero,hcl,hcorrect⟩ := q0.run hi v hq0
  obtain ⟨hsource,hnormal⟩ := q.source_normalized t hqt.1
  refine ⟨(6*i.n+3)+cb+cl,t,q,code_append heReset heBoot heLoop,?_,hqt,hqZero,hqt.1.ready,hsource,hnormal,
    q.exact_infinity t hqt.1 hqZero⟩
  rw [hp0] at hcl
  nlinarith
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s157
section s158
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
lemma delete_eval (s : Data) : Eval deleteCode s 2 (deletedData s) := eval_sequence_atoms deleteAtoms s
lemma delete_nat_frame (j : ℕ) (hj : j≠350) : NatFrame deleteCode j := by
  simp [deleteCode,deleteAtoms,Structured.sequence,NatFrame,writesNat,Ne.symm hj]
lemma delete_real_frame (j : ℕ) : RealFrame deleteCode j := by simp [deleteCode,deleteAtoms,Structured.sequence,RealFrame,writesReal]
lemma Ready.delete {i : Input} {deleted : List (Fin i.k)} {s : Data} (h : Ready i deleted s)
    (e : Fin i.k) (he : s.natReg 5=e.val) : Ready i (deleted++[e]) (deletedData s) := by
  classical
  let t := deletedData s
  have heval := delete_eval s
  have hm : t.natMem=Function.update s.natMem ((layout i).active+e.val) 0 := by
    simp [t,deletedData,deleteAtoms,Atom.effect,instructionEffect,data,Data.machine,he,h.layoutRegs.active,h.zero]
  have hn (j : ℕ) (hj : j≤246) : t.natReg j=s.natReg j := heval.nat_frame (delete_nat_frame j (by omega))
  have hframe (a : ℕ) (ha : a≠(layout i).active+e.val) : t.natMem a=s.natMem a := by rw [hm,Function.update_of_ne ha]
  have heBound := e.isLt
  refine ⟨(hn 56 (by omega)).trans h.zero,(hn 26 (by omega)).trans h.unit,
    (hn 66 (by omega)).trans h.vertices,(hn 68 (by omega)).trans h.edges,(hn 72 (by omega)).trans h.source,
    (heval.real_frame (delete_real_frame 56)).trans h.zeroR,?_,?_,?_,(hn 236 (by omega)).trans h.height,?_,
    (hn 246 (by omega)).trans h.slotReg,?_⟩
  · constructor
    · exact (hn 224 (by omega)).trans h.layoutRegs.heads
    · exact (hn 226 (by omega)).trans h.layoutRegs.settled
    · exact (hn 228 (by omega)).trans h.layoutRegs.active
    · exact (hn 230 (by omega)).trans h.layoutRegs.distances
    · exact (hn 232 (by omega)).trans h.layoutRegs.nodes
    · exact (hn 234 (by omega)).trans h.layoutRegs.powers
  · apply h.graph.frame
    intro a ha
    apply hframe
    simp only [Adjacency.staticFootprint,Finset.mem_union,Finset.mem_Ico] at ha
    dsimp [layout,Layout.addresses] at ha ⊢
    rcases ha with ha | ha <;> omega
  · intro f
    by_cases hf : f=e
    · subst f
      rw [hm,Function.update_self]
      simp [live]
    · rw [hframe _ (by intro hh;apply hf;apply Fin.ext;omega),h.active f]
      simp [live,hf]
  · intro hh;rw [hn 238 (by omega)];exact h.powerPtr hh
  · intro j hj
    rw [hframe _ (by dsimp [heapBase,layout,Layout.addresses];omega)]
    exact h.powers j hj
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s158
section s159
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
lemma initialize_eval (i : Input) (hi : i.Valid) (s : Data) (hraw : InputCapture.RawInput i s) (htape : Adjacency.Tape i s) :
    ∃ (cost : ℕ) (t : Data) (q : State i []), Eval initializeCode s cost t ∧
      cost ≤ 700*(i.n+i.k+1)*(heapHeight i+1) ∧ q.memory t ∧ q.queue=0 ∧ Ready i [] t ∧
      stored t.machine i.source.val=0 ∧
      (∀ v : Fin i.n, t.natMem v.val≤1 ∧ (t.natMem v.val=0 → 0 ≤ t.realMem v.val)) ∧
      (∀ v : Fin i.n, stored t.machine v.val=i.dist [] v ∧
        (stored t.machine v.val=⊤ ↔ ¬Reachable i.graph (live []) i.source v)) := by
  obtain ⟨u,heu,hu⟩ := prepareGraph_eval i s hraw htape
  obtain ⟨v,hev,hv⟩ := hu.powers
  obtain ⟨c,t,q,het,hc,hq,hqZero,hReady,hsource,hnorm,hcorrect⟩ := hv.execute hi
  refine ⟨(4*i.n+22*i.k+37)+((7*heapHeight i+14)+c),t,q,Eval.seq heu (Eval.seq hev het),?_,
    hq,hqZero,hReady,hsource,hnorm,hcorrect⟩
  nlinarith
lemma Ready.external {i : Input} {deleted : List (Fin i.k)} {s : Data} (h : Ready i deleted s) (index : ℕ) :
    Ready i deleted {s with natReg := Function.update s.natReg 5 index} := by
  let t : Data := {s with natReg := Function.update s.natReg 5 index}
  change Ready i deleted t
  have hm : t.natMem=s.natMem := rfl
  have hn (j : ℕ) (hj : j≠5) : t.natReg j=s.natReg j := Function.update_of_ne hj _ _
  refine ⟨(hn 56 (by omega)).trans h.zero,(hn 26 (by omega)).trans h.unit,
    (hn 66 (by omega)).trans h.vertices,(hn 68 (by omega)).trans h.edges,(hn 72 (by omega)).trans h.source,
    h.zeroR,?_,h.graph.frame (fun a _ => congrFun hm a),(by intro e;rw [hm];exact h.active e),(hn 236 (by omega)).trans h.height,?_,(hn 246 (by omega)).trans h.slotReg,(fun j hj => (congrFun hm _).trans (h.powers j hj))⟩
  · constructor
    · exact (hn 224 (by omega)).trans h.layoutRegs.heads
    · exact (hn 226 (by omega)).trans h.layoutRegs.settled
    · exact (hn 228 (by omega)).trans h.layoutRegs.active
    · exact (hn 230 (by omega)).trans h.layoutRegs.distances
    · exact (hn 232 (by omega)).trans h.layoutRegs.nodes
    · exact (hn 234 (by omega)).trans h.layoutRegs.powers
  · intro hh;rw [hn 238 (by omega)];exact h.powerPtr hh
lemma update_eval {i : Input} (hi : i.Valid) {deleted : List (Fin i.k)} {s : Data} (h : Ready i deleted s)
    (e : Fin i.k) (he : s.natReg 5=e.val) :
    ∃ (cost : ℕ) (t : Data) (q : State i (deleted++[e])), Eval updateCode s cost t ∧
      cost ≤ 602*(i.n+i.k+1)*(heapHeight i+1) ∧ q.memory t ∧ q.queue=0 ∧ Ready i (deleted++[e]) t ∧
      stored t.machine i.source.val=0 ∧
      (∀ v : Fin i.n, t.natMem v.val≤1 ∧ (t.natMem v.val=0 → 0 ≤ t.realMem v.val)) ∧
      (∀ v : Fin i.n, stored t.machine v.val=i.dist (deleted++[e]) v ∧
        (stored t.machine v.val=⊤ ↔ ¬Reachable i.graph (live (deleted++[e])) i.source v)) := by
  obtain ⟨c,t,q,het,hc,hq,hqZero,hReady,hsource,hnorm,hcorrect⟩ := (h.delete e he).execute hi
  exact ⟨2+c,t,q,Eval.seq (delete_eval s) het,by nlinarith,hq,hqZero,hReady,hsource,hnorm,hcorrect⟩
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s159
section s160
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
lemma program_initialization (i : Input) (hi : i.Valid) :
    ∃ cost c, Ends hostProgram (initialMachine hostProgram i) c ∧ c.work=cost+1 ∧
      cost ≤ 700*(i.n+i.k+1)*(heapHeight i+1) ∧ Ready i [] (data c) ∧
      ∃ q : State i [], q.memory (data c) ∧ q.queue=0 := by
  obtain ⟨cost,t,q,he,hcost,hq,hzero,hr,hsource,hnorm,hcorrect⟩ := initialize_eval i hi (data (initialMachine hostProgram i))
    (InputCapture.raw_initial hostProgram i) (Adjacency.tape_initial hostProgram i)
  obtain ⟨c,hend,hdata,hwork⟩ := command_ends he hostProgram 0 (initialMachine hostProgram i)
    (program_init _ _) rfl rfl rfl rfl (by simpa only [hostProgram,Nat.zero_add] using program_init_halt initializeCode updateCode)
  refine ⟨cost,c,hend,?_,hcost,?_,q,?_,hzero⟩
  · simpa only [initialMachine,Nat.zero_add] using hwork
  · rw [hdata];exact hr
  · rw [hdata];exact hq
lemma program_update (i : Input) (hi : i.Valid) (deleted : List (Fin i.k)) (c : Machine)
    (h : Ready i deleted (data c)) (e : Fin i.k) :
    ∃ cost d, Ends hostProgram (deletionMachine hostProgram c e.val) d ∧ d.work=c.work+cost+1 ∧
      cost ≤ 602*(i.n+i.k+1)*(heapHeight i+1) ∧ Ready i (deleted++[e]) (data d) ∧
      ∃ q : State i (deleted++[e]), q.memory (data d) ∧ q.queue=0 := by
  let start := deletionMachine hostProgram c e.val
  have hs : Ready i deleted (data start) := by
    change Ready i deleted {data c with natReg := Function.update (data c).natReg 5 e.val}
    exact h.external e.val
  obtain ⟨cost,t,q,he,hcost,hq,hzero,hr,hsource,hnorm,hcorrect⟩ := update_eval hi hs e rfl
  obtain ⟨d,hend,hdata,hwork⟩ := command_ends he hostProgram hostProgram.update start (Structured.program_update _ _) rfl rfl rfl rfl (program_update_halt _ _)
  refine ⟨cost,d,hend,?_,hcost,?_,q,?_,hzero⟩
  · exact hwork
  · rw [hdata];exact hr
  · rw [hdata];exact hq
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s160
section s161
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
lemma Completed.ready {i : Input} {deleted : List (Fin i.k)} {c : Machine} (h : Completed i deleted c) : Ready i deleted (Structured.data c) := by
  obtain ⟨q,hm,hq⟩ := h
  exact hm.1.ready
lemma Completed.good {i : Input} (hi : i.Valid) {deleted : List (Fin i.k)} {c : Machine} (h : Completed i deleted c) : Good i deleted c := by
  obtain ⟨q,hm,hq⟩ := h
  obtain ⟨hs,hn⟩ := q.source_normalized (Structured.data c) hm.1
  have hv := q.exact_infinity (Structured.data c) hm.1 hq
  change stored c i.source.val=0 at hs
  refine ⟨hs,hn,?_⟩
  intro v
  have hstored : stored c v.val=i.dist deleted v := (hv v).1
  refine ⟨hstored.ge,?_,(hv v).2⟩
  rw [hstored]
  have hfactor : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (1+i.accuracy) := by
    rw [←ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by have hh := hi.2.2.2.1;linarith)
  calc
    i.dist deleted v = 1*i.dist deleted v := by simp
    _ ≤ ENNReal.ofReal (1+i.accuracy)*i.dist deleted v := by gcongr
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s161
section s162
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma ends_running_work_positive (p : Program) (c d : Machine)
    (hh : c.halted = false) (he : Ends p c d) : c.work+1 ≤ d.work := by
  obtain ⟨t,ht,hhalt,hfault⟩ := he
  have hhalt' : (execute p c t).halted = true := by rwa [ht]
  obtain ⟨r,_,hrun,hrwork⟩ := terminating_prefix p c t hhalt'
  have hr : 0 < r := by
    by_contra hn
    have hr0 : r = 0 := by omega
    have hh' : (execute p c r).halted = true := by rw [hrun,ht];exact hhalt
    simp only [hr0,execute,Function.iterate_zero,id_eq,hh,Bool.false_eq_true] at hh'
  rw [ht] at hrwork
  omega
lemma call_overhead_absorbed (D overhead before after cost : ℕ)
    (hstep : before+1 ≤ after) (hcost : cost ≤ D*(after-before)+overhead) :
    cost ≤ (D+overhead)*(after-before) := by
  have hpos : 1 ≤ after-before := by omega
  have hh := Nat.mul_le_mul_left overhead hpos
  rw [Nat.mul_one] at hh
  rw [Nat.add_mul]
  omega
lemma live_take_subset {k : ℕ} (ds : List (Fin k)) (j : ℕ) : live ds ⊆ live (ds.take j) := by
  classical
  intro e he
  simp only [live,Finset.mem_sdiff,Finset.mem_univ,true_and,List.mem_toFinset] at he ⊢
  intro hh
  exact he (List.mem_of_mem_take hh)
end DecrAlmostLinearSSSP.Decremental
end s162
section s163
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
lemma OnlineRun.initial_execution {p : Program} {i : Input} {ds : List (Fin i.k)} {cs : List Machine}
    (h : OnlineRun p i ds cs) : ∃ c, cs[0]? = some c ∧ Ends p (initialMachine p i) c := by
  induction h with
  | init he => exact ⟨_,rfl,he⟩
  | @next ds cs c d h hlast e hd ih =>
    obtain ⟨a,ha,he⟩ := ih
    cases cs with
    | nil => simp at ha
    | cons b rest =>
      have hab : b = a := by simpa using ha
      subst b
      exact ⟨a,rfl,he⟩
lemma Maintains.initialization {p : Program} {C : ℝ} {a : ℕ → ℝ} {queryBound : ℕ}
    {logWeights : Bool} {i : Input} (h : Maintains p C a queryBound logWeights i) :
    ∃ c, Ends p (initialMachine p i) c ∧ stored c i.source.val = 0 ∧
      (∀ v : Fin i.n, c.natMem v.val ≤ 1 ∧ (c.natMem v.val = 0 → 0 ≤ c.realMem v.val)) ∧
      (∀ v : Fin i.n, i.dist [] v ≤ stored c v.val ∧
        stored c v.val ≤ ENNReal.ofReal (1+i.accuracy)*i.dist [] v ∧
        (stored c v.val = ⊤ ↔ ¬Reachable i.graph (live []) i.source v)) ∧
      (c.work : ℝ) ≤ C*i.size*a i.size/i.accuracy*
        (if logWeights then max 1 (logarithm2 i.W) else 1) := by
  obtain ⟨cs,hrun,hlen,hgood,hcost,_⟩ := h [] (by simp [Legal])
  obtain ⟨c,hfirst,hend⟩ := hrun.initial_execution
  have hg := hgood 0 c hfirst
  have hcs : cs = [c] := by
    cases cs with
    | nil => simp at hfirst
    | cons d rest =>
      have hd : d = c := by simpa using hfirst
      subst d
      have hr : rest = [] := by simpa using hlen
      subst rest
      rfl
  have hc := hcost c (by simp [hcs])
  refine ⟨c,hend,hg.1,hg.2.1,?_,?_⟩
  · simpa using hg.2.2
  · simpa using hc
end DecrAlmostLinearSSSP.Decremental
end s163
section s164
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma Ends.deterministic {p : Program} {c d e : Machine} (hd : Ends p c d) (he : Ends p c e) : d = e := by
  obtain ⟨t,rfl,hhalt,_⟩ := hd
  obtain ⟨u,rfl,hhalt',_⟩ := he
  rcases le_total t u with htu | hut
  · have heq : u = t+(u-t) := by omega
    conv_rhs => rw [heq,execute_add,execute_halted p _ hhalt]
  · have heq : t = u+(t-u) := by omega
    conv_lhs => rw [heq,execute_add,execute_halted p _ hhalt']
end DecrAlmostLinearSSSP.Decremental
end s164
section s165
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma OnlineRun.length {p : Program} {i : Input} {ds : List (Fin i.k)} {cs : List Machine}
    (h : OnlineRun p i ds cs) : cs.length = ds.length+1 := by
  induction h with
  | init => rfl
  | next _ _ _ _ ih => simp only [List.length_append,List.length_singleton];omega
lemma OnlineRun.transition_at {p : Program} {i : Input} {ds : List (Fin i.k)} {cs : List Machine}
    (h : OnlineRun p i ds cs) (k : ℕ) (hk : k < ds.length) :
    ∃ c d, cs[k]? = some c ∧ cs[k+1]? = some d ∧ Ends p (deletionMachine p c (ds[k]).val) d := by
  induction h generalizing k with
  | init => simp at hk
  | @next ds cs c d h hlast e hd ih =>
    have hlen := h.length
    by_cases hlt : k < ds.length
    · obtain ⟨c',d',hc',hd',he'⟩ := ih k hlt
      refine ⟨c',d',?_,?_,?_⟩
      · simpa only [List.getElem?_append_left (show k < cs.length by omega)] using hc'
      · simpa only [List.getElem?_append_left (show k+1 < cs.length by omega)] using hd'
      · simpa only [List.getElem_append_left hlt] using he'
    · have heq : k = ds.length := by simp only [List.length_append,List.length_singleton] at hk;omega
      subst k
      have hc : cs[ds.length]? = some c := by
        rw [List.getLast?_eq_getElem?] at hlast
        simpa only [hlen,Nat.add_sub_cancel] using hlast
      refine ⟨c,d,?_,?_,?_⟩
      · simpa only [List.getElem?_append_left (show ds.length < cs.length by omega)] using hc
      · rw [show ds.length+1 = cs.length from hlen.symm,List.getElem?_append_right le_rfl,Nat.sub_self]
        rfl
      · have he : (ds++[e])[ds.length] = e := by simp
        simpa only [he] using hd
lemma Ends.work_mono {p : Program} {c d : Machine} (h : Ends p c d) : c.work ≤ d.work := by
  obtain ⟨t,ht,_,_⟩ := h
  rw [← ht]
  exact execute_work_mono p c t
lemma OnlineRun.work_le_last {p : Program} {i : Input} {ds : List (Fin i.k)} {cs : List Machine}
    (h : OnlineRun p i ds cs) (last : Machine) (hlast : cs.getLast? = some last) :
    ∀ c ∈ cs, c.work ≤ last.work := by
  induction h generalizing last with
  | @init c he =>
    have heq : c = last := by simpa using hlast
    subst last
    intro d hd
    have hd' : d = c := by simpa using hd
    subst d
    exact le_rfl
  | @next ds cs c d h hlastc e hd ih =>
    have heq : d = last := by simpa using hlast
    subst last
    intro z hz
    simp only [List.mem_append,List.mem_singleton] at hz
    rcases hz with hz | hz
    · exact (ih c hlastc z hz).trans hd.work_mono
    · subst z;exact le_rfl
end DecrAlmostLinearSSSP.Decremental
end s165
section s166
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
lemma online (i : Input) (hi : i.Valid) (ds : List (Fin i.k)) :
    ∃ (cs : List Machine) (last : Machine), OnlineRun hostProgram i ds cs ∧
      cs.length=ds.length+1 ∧ cs.getLast?=some last ∧ Completed i ds last ∧
      (∀ j c, cs[j]?=some c → Completed i (ds.take j) c) ∧
      last.work+6*ds.length ≤ 1000*(i.n+i.k+1)*(heapHeight i+1)*(ds.length+1) := by
  classical
  let R := (i.n+i.k+1)*(heapHeight i+1)
  have hR : 1≤R := by dsimp [R];nlinarith
  induction ds using List.reverseRecOn with
  | nil =>
    obtain ⟨cost,c,he,hw,hc,hr,q,hqm,hqzero⟩ := program_initialization i hi
    have hcompleted : Completed i [] c := ⟨q,hqm,hqzero⟩
    refine ⟨[c],c,OnlineRun.init he,rfl,rfl,hcompleted,?_,?_⟩
    · intro j d hd
      cases j with
      | zero =>
        have hdc : c=d := Option.some.inj hd
        subst d;exact hcompleted
      | succ j => simp at hd
    · simp only [List.length_nil,Nat.mul_zero,Nat.add_zero,Nat.zero_add,Nat.mul_one,hw]
      have hc' : cost≤700*R := by simpa only [R,Nat.mul_assoc] using hc
      have hf : cost+1 ≤ 1000*R := by omega
      simpa only [R,Nat.mul_assoc] using hf
  | append_singleton ds e ih =>
    obtain ⟨cs,c,hr,hlen,hlast,hcompleted,hprefix,hwork⟩ := ih
    obtain ⟨cost,d,he,hdwork,hcost,hdReady,q,hdmem,hdzero⟩ := program_update i hi ds c hcompleted.ready e
    have hdCompleted : Completed i (ds++[e]) d := ⟨q,hdmem,hdzero⟩
    refine ⟨cs++[d],d,OnlineRun.next hr hlast e he,?_,by simp,hdCompleted,?_,?_⟩
    · simp only [List.length_append,List.length_singleton,hlen]
    · intro j z hz
      by_cases hj : j<cs.length
      · have hget : cs[j]?=some z := by rwa [List.getElem?_append_left hj] at hz
        have hjds : j≤ds.length := by omega
        have htake : (ds++[e]).take j=ds.take j := by
          rw [List.take_append]
          simp only [Nat.sub_eq_zero_of_le hjds,List.take_zero,List.append_nil]
        rw [htake]
        exact hprefix j z hget
      · have hjlen : j<(cs++[d]).length := by
          by_contra hn
          have hnone : (cs++[d])[j]?=none := List.getElem?_eq_none_iff.mpr (by omega)
          rw [hnone] at hz;contradiction
        have hjeq : j=cs.length := by simp only [List.length_append,List.length_singleton] at hjlen;omega
        subst j
        rw [List.getElem?_append_right le_rfl,Nat.sub_self] at hz
        have hdz : d=z := Option.some.inj hz
        subst z
        have htake : (ds++[e]).take cs.length=ds++[e] := by
          apply List.take_of_length_le
          simp only [List.length_append,List.length_singleton,hlen]
          exact le_rfl
        rw [htake];exact hdCompleted
    · simp only [List.length_append,List.length_singleton,hdwork]
      have hc' : cost≤602*R := by simpa only [R,Nat.mul_assoc] using hcost
      have hw : c.work+6*ds.length ≤ 1000*R*(ds.length+1) := by simpa only [R,Nat.mul_assoc] using hwork
      have hf : c.work+cost+1+6*(ds.length+1) ≤ 1000*R*(ds.length+1+1) := by nlinarith
      simpa only [R,Nat.mul_assoc] using hf
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s166
section s167
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
lemma overhead_subpolynomial : Subpolynomial overhead :=
  subpolynomial_add (fun _ => 4) (fun m => logarithm2 (max 2 m : ℕ))
    (subpolynomial_constant 4 (by norm_num)) subpolynomial_logarithm2_size
lemma height_work_bound (i : Input) (hi : i.Valid) :
    ((heapHeight i+1 : ℕ) : ℝ) ≤ overhead i.size*max 1 (logarithm2 i.W) := by
  have hh : ((heapHeight i : ℕ) : ℝ) ≤ scaleCount i := by exact_mod_cast input_height_le i hi
  have hs := scaleCount_saturated_bound i hi
  have hw : (1 : ℝ) ≤ max 1 (logarithm2 i.W) := le_max_left _ _
  unfold overhead
  rw [Nat.cast_add,Nat.cast_one]
  nlinarith
lemma small_accuracy_work_bound (i : Input) (hi : i.Valid) (hsmall : i.accuracy ≤ 1/(i.size : ℝ)) :
    (10000 : ℝ)*(i.size : ℝ)^2*(heapHeight i+1 : ℕ) ≤
      10000*i.size*overhead i.size/i.accuracy*max 1 (logarithm2 i.W) := by
  have hmN : 1 ≤ i.size := by have hn := input_vertex_positive i;have hh := hi.1;omega
  have hm : (0 : ℝ) < i.size := by exact_mod_cast (show 0 < i.size by omega)
  have he : 0 < i.accuracy := hi.2.2.2.1
  have hprod : i.accuracy*(i.size : ℝ) ≤ 1 := (le_div_iff₀ hm).mp hsmall
  have hmsq : (i.size : ℝ)^2 ≤ (i.size : ℝ)/i.accuracy := by
    apply (le_div_iff₀ he).mpr
    nlinarith [mul_le_mul_of_nonneg_right hprod hm.le]
  have ha : 0<overhead i.size := overhead_subpolynomial.1 i.size
  have hw : (0 : ℝ) ≤ max 1 (logarithm2 i.W) := (by have hh := le_max_left (1 : ℝ) (logarithm2 i.W);linarith)
  have hh := height_work_bound i hi
  calc
    10000*(i.size : ℝ)^2*(heapHeight i+1 : ℕ) ≤ 10000*(i.size : ℝ)^2*(overhead i.size*max 1 (logarithm2 i.W)) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ ≤ 10000*((i.size : ℝ)/i.accuracy)*(overhead i.size*max 1 (logarithm2 i.W)) := by
      gcongr
    _ = _ := by ring
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s167
section s168
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
lemma stream_work_bound (i : Input) (hi : i.Valid) (ds : List (Fin i.k)) (hd : Legal ds) :
    1000*(i.n+i.k+1)*(heapHeight i+1)*(ds.length+1) ≤ 10000*i.size^2*(heapHeight i+1) := by
  have hm : 1 ≤ i.size := by have hn := input_vertex_positive i;have hh := hi.1;omega
  have hlen : ds.length ≤ i.k := by simpa only [Fintype.card_fin] using hd.length_le_card
  have hnk : i.n+i.k+1≤3*i.size := by have hn := hi.1;have hk := hi.2.1;omega
  have hds : ds.length+1≤2*i.size := by have hk := hi.2.1;omega
  calc
    1000*(i.n+i.k+1)*(heapHeight i+1)*(ds.length+1) ≤ 1000*(3*i.size)*(heapHeight i+1)*(2*i.size) := by gcongr
    _ = 6000*i.size^2*(heapHeight i+1) := by ring
    _ ≤ 10000*i.size^2*(heapHeight i+1) := by gcongr <;> omega
lemma exact_small_accuracy_maintains (i : Input) (hi : i.Valid) (hsmall : i.accuracy ≤ 1/(i.size : ℝ)) :
    Maintains hostProgram 10000 overhead 9 true i := by
  classical
  intro ds hd
  obtain ⟨cs,last,hr,hlen,hlast,hcompleted,hprefix,hwork⟩ := online i hi ds
  refine ⟨cs,hr,hlen,?_,?_,?_⟩
  · intro j c hc
    exact (hprefix j c hc).good hi
  · intro c hc
    have hclast : c=last := Option.some.inj (hc.symm.trans hlast)
    subst c
    have hnat := hwork.trans (stream_work_bound i hi ds hd)
    have hreal : (((last.work+6*ds.length : ℕ) : ℝ)) ≤ (10000 : ℝ)*(i.size : ℝ)^2*(heapHeight i+1 : ℕ) := by
      exact_mod_cast hnat
    exact hreal.trans (small_accuracy_work_bound i hi hsmall)
  · intro c hc v
    exact Structured.program_query_nine initializeCode updateCode c v.val
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s168
open DecrAlmostLinearSSSP.Decremental
set_option autoImplicit false
theorem solution : (((((((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval
    (DecrAlmostLinearSSSP.Decremental.Structured.sequence
      (@List.map.{0, 0} DecrAlmostLinearSSSP.Decremental.Structured.Atom DecrAlmostLinearSSSP.Decremental.Structured.Cmd
        DecrAlmostLinearSSSP.Decremental.Structured.Cmd.atom
        DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.poppedAtoms))
    s (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
    (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.poppedData s)) ∧ (∀
  j ∉
    @Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 304) (instOfNatNat (nat_lit 304)))
      (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 306) (instOfNatNat (nat_lit 306)))
        (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 318) (instOfNatNat (nat_lit 318)))
          (@Singleton.singleton.{0, 0} Nat (Finset.{0} Nat) (@Finset.instSingleton.{0} Nat)
            (@OfNat.ofNat.{0} Nat (nat_lit 320) (instOfNatNat (nat_lit 320)))))),
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
    (DecrAlmostLinearSSSP.Decremental.Structured.sequence
      (@List.map.{0, 0} DecrAlmostLinearSSSP.Decremental.Structured.Atom DecrAlmostLinearSSSP.Decremental.Structured.Cmd
        DecrAlmostLinearSSSP.Decremental.Structured.Cmd.atom
        DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.poppedAtoms))
    j)) ∧ ((∀ (j : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
    (DecrAlmostLinearSSSP.Decremental.Structured.sequence
      (@List.map.{0, 0} DecrAlmostLinearSSSP.Decremental.Structured.Atom DecrAlmostLinearSSSP.Decremental.Structured.Cmd
        DecrAlmostLinearSSSP.Decremental.Structured.Cmd.atom
        DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.poppedAtoms))
    j) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)} {tentative : Fin i.n → Option.{0} Nat}
  {settled : Finset.{0} (Fin i.n)}
  {tree :
    DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled tree queue s →
    ∀ (key : Nat) (v : Fin i.n),
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260)))) key →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 262) (instOfNatNat (nat_lit 262)))) (@Fin.val i.n v) →
          And
            (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled tree queue
              (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.poppedData s))
            (And
              (@Eq.{1} Nat
                ((DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.poppedData s).natReg
                  (@OfNat.ofNat.{0} Nat (nat_lit 304) (instOfNatNat (nat_lit 304))))
                key)
              (And
                (@Eq.{1} Nat
                  ((DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.poppedData s).natReg
                    (@OfNat.ofNat.{0} Nat (nat_lit 306) (instOfNatNat (nat_lit 306))))
                  (@Fin.val i.n v))
                (@Eq.{1} Nat
                  ((DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.poppedData s).natReg
                    (@OfNat.ofNat.{0} Nat (nat_lit 320) (instOfNatNat (nat_lit 320))))
                  (@ite.{1} Nat
                    (@Membership.mem.{0, 0} (Fin i.n) (Finset.{0} (Fin i.n))
                      (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin i.n)) (Fin i.n)
                        (@Finset.instSetLike.{0} (Fin i.n)))
                      settled v)
                    (@Finset.decidableMem.{0} (Fin i.n) (instDecidableEqFin i.n) v settled)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))) ∧ (((∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k),
  @Eq.{1} Nat
    (@DecrAlmostLinearSSSP.Decremental.Exact.remainingDegree n k g
      (@EmptyCollection.emptyCollection.{0} (Finset.{0} (Fin n)) (@Finset.instEmptyCollection.{0} (Fin n))))
    k) ∧ (∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (settled : Finset.{0} (Fin n)),
  ∀ v ∉ settled,
    @Eq.{1} Nat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@DecrAlmostLinearSSSP.Decremental.Exact.remainingDegree n k g
          (@Insert.insert.{0, 0} (Fin n) (Finset.{0} (Fin n)) (@Finset.instInsert.{0} (Fin n) (instDecidableEqFin n)) v
            settled))
        (@List.length.{0} (Fin k) (@DecrAlmostLinearSSSP.Decremental.Exact.adjacency n k g k v)))
      (@DecrAlmostLinearSSSP.Decremental.Exact.remainingDegree n k g settled))) ∧ ((∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (settled : Finset.{0} (Fin n)) (key : Nat) (v : Fin n)
  (queue : Multiset.{0} (Prod.{0, 0} Nat (Fin n))),
  @Eq.{1} Nat
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@DecrAlmostLinearSSSP.Decremental.Exact.queuePotential n k g settled queue)
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@DecrAlmostLinearSSSP.Decremental.Exact.queuePotential n k g settled
      (@Multiset.cons.{0} (Prod.{0, 0} Nat (Fin n)) (@Prod.mk.{0, 0} Nat (Fin n) key v) queue))) ∧ (∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (settled : Finset.{0} (Fin n)) (key : Nat) (v : Fin n)
  (queue next : Multiset.{0} (Prod.{0, 0} Nat (Fin n))),
  v ∉ settled →
    @LE.le.{0} Nat instLENat (@Multiset.card.{0} (Prod.{0, 0} Nat (Fin n)) next)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@Multiset.card.{0} (Prod.{0, 0} Nat (Fin n)) queue)
          (@List.length.{0} (Fin k) (@DecrAlmostLinearSSSP.Decremental.Exact.adjacency n k g k v))) →
      @LE.le.{0} Nat instLENat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@DecrAlmostLinearSSSP.Decremental.Exact.queuePotential n k g
              (@Insert.insert.{0, 0} (Fin n) (Finset.{0} (Fin n))
                (@Finset.instInsert.{0} (Fin n) (instDecidableEqFin n)) v settled)
              next)
            (@List.length.{0} (Fin k) (@DecrAlmostLinearSSSP.Decremental.Exact.adjacency n k g k v)))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@DecrAlmostLinearSSSP.Decremental.Exact.queuePotential n k g settled
          (@Multiset.cons.{0} (Prod.{0, 0} Nat (Fin n)) (@Prod.mk.{0, 0} Nat (Fin n) key v) queue)))))) ∧ ((((∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (source : Fin n),
  @Eq.{1} Nat
    (@DecrAlmostLinearSSSP.Decremental.Exact.queuePotential n k g
      (@EmptyCollection.emptyCollection.{0} (Finset.{0} (Fin n)) (@Finset.instEmptyCollection.{0} (Fin n)))
      (@Singleton.singleton.{0, 0} (Prod.{0, 0} Nat (Fin n)) (Multiset.{0} (Prod.{0, 0} Nat (Fin n)))
        (@Multiset.instSingleton.{0} (Prod.{0, 0} Nat (Fin n)))
        (@Prod.mk.{0, 0} Nat (Fin n) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) source)))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k)
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) ∧ (∀ {G : Type} (test : DecrAlmostLinearSSSP.Decremental.Structured.Test)
  (body : DecrAlmostLinearSSSP.Decremental.Structured.Cmd)
  (invariant : G → DecrAlmostLinearSSSP.Decremental.Structured.Data → Prop) (potential : G → Nat) (charge : Nat),
  (∀ (g : G) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
      invariant g s →
        test.holds s →
          ∃ g' t cost,
            And (DecrAlmostLinearSSSP.Decremental.Structured.Eval body s cost t)
              (And (invariant g' t)
                (And (@LT.lt.{0} Nat instLTNat (potential g') (potential g))
                  (@LE.le.{0} Nat instLENat
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cost
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) charge
                      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (potential g)
                        (potential g'))))))) →
    ∀ (g : G) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
      invariant g s →
        ∃ g' t cost,
          And
            (DecrAlmostLinearSSSP.Decremental.Structured.Eval
              (DecrAlmostLinearSSSP.Decremental.Structured.Cmd.loop test body) s cost t)
            (And (invariant g' t)
              (And (Not (test.holds t))
                (@LE.le.{0} Nat instLENat cost
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) charge (potential g))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))) ∧ ((∀ {s u v w t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {cp cs cq : Nat},
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePop.code s cp u →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval
        (DecrAlmostLinearSSSP.Decremental.Structured.sequence
          (@List.map.{0, 0} DecrAlmostLinearSSSP.Decremental.Structured.Atom
            DecrAlmostLinearSSSP.Decremental.Structured.Cmd DecrAlmostLinearSSSP.Decremental.Structured.Cmd.atom
            DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.poppedAtoms))
        u (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) v →
      DecrAlmostLinearSSSP.Decremental.Structured.Eval
          (DecrAlmostLinearSSSP.Decremental.Structured.Cmd.branch
            (DecrAlmostLinearSSSP.Decremental.Structured.Test.natLess
              (@OfNat.ofNat.{0} Nat (nat_lit 320) (instOfNatNat (nat_lit 320)))
              (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
            DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.scan DecrAlmostLinearSSSP.Decremental.Structured.Cmd.skip)
          v cs w →
        DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.queueCount w cq
            t →
          DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.body s
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cp
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cs cq)))
            t) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)},
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
                        (@DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State.potential i deleted next))))))))) ∧ (((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)},
  i.Valid →
    ∀ (q : DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State i deleted)
      (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
      @DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State.memory i deleted q s →
        ∃ next t cost,
          And
            (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.loop s
              cost t)
            (And (@DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State.memory i deleted next t)
              (And
                (@Eq.{1} (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n)))
                  (@DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State.queue i deleted next)
                  (@OfNat.ofNat.{0} (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))) (nat_lit 0)
                    (@Zero.toOfNat0.{0} (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n)))
                      (@Multiset.instZero.{0} (Prod.{0, 0} Nat (Fin i.n))))))
                (And
                  (@LE.le.{0} Nat instLENat cost
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 200) (instOfNatNat (nat_lit 200)))
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        (@DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State.potential i deleted q))
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (∀ (v : Fin i.n),
                    @Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.stored t.machine (@Fin.val i.n v))
                      (i.dist deleted v)))))) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)}
  (q : DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State i deleted)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted
      (@DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State.tentative i deleted q)
      (@DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State.settled i deleted q)
      (@DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State.tree i deleted q)
      (@DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State.queue i deleted q) s →
    And
      (@Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.stored s.machine (@Fin.val i.n i.source))
        (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero)))
      (∀ (v : Fin i.n),
        And
          (@LE.le.{0} Nat instLENat (s.natMem (@Fin.val i.n v))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@Eq.{1} Nat (s.natMem (@Fin.val i.n v)) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
            @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              (s.realMem (@Fin.val i.n v)))))) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)}
  (q : DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State i deleted)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted
      (@DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State.tentative i deleted q)
      (@DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State.settled i deleted q)
      (@DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State.tree i deleted q)
      (@DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State.queue i deleted q) s →
    @Eq.{1} (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n)))
        (@DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State.queue i deleted q)
        (@OfNat.ofNat.{0} (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))) (nat_lit 0)
          (@Zero.toOfNat0.{0} (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n)))
            (@Multiset.instZero.{0} (Prod.{0, 0} Nat (Fin i.n))))) →
      ∀ (v : Fin i.n),
        And (@Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.stored s.machine (@Fin.val i.n v)) (i.dist deleted v))
          (Iff
            (@Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.stored s.machine (@Fin.val i.n v))
              (@Top.top.{0} ENNReal ENNReal.instTop))
            (Not
              (@DecrAlmostLinearSSSP.Decremental.Reachable i.n i.k i.graph
                (@DecrAlmostLinearSSSP.Decremental.live i.k deleted) i.source v)))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.resetBody s
    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
    (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.resetAdvanced s)) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      And
        (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.resetAdvanced s).natMem
          (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
            (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natMem
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 340) (instOfNatNat (nat_lit 340))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 226) (instOfNatNat (nat_lit 226))))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 340) (instOfNatNat (nat_lit 340)))))
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (And
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.resetAdvanced s).natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 340) (instOfNatNat (nat_lit 340))))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 340) (instOfNatNat (nat_lit 340))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.resetAdvanced s).realMem s.realMem)))))))) ∧ (((((∀ (j : Nat),
  @Ne.{1} Nat j (@OfNat.ofNat.{0} Nat (nat_lit 340) (instOfNatNat (nat_lit 340))) →
    @Ne.{1} Nat j (@OfNat.ofNat.{0} Nat (nat_lit 342) (instOfNatNat (nat_lit 342))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.resetBody j) ∧ (∀ (j : Nat),
  @Ne.{1} Nat j (@OfNat.ofNat.{0} Nat (nat_lit 340) (instOfNatNat (nat_lit 340))) →
    @Ne.{1} Nat j (@OfNat.ofNat.{0} Nat (nat_lit 342) (instOfNatNat (nat_lit 342))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.resetLoop j)) ∧ ((∀ (j : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.resetLoop j) ∧ (∀ (bank start remaining : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 226) (instOfNatNat (nat_lit 226)))) bank →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 340) (instOfNatNat (nat_lit 340)))) start →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 66) (instOfNatNat (nat_lit 66))))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start remaining) →
            @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start remaining)
                bank →
              ∃ t,
                And
                  (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                    DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.resetLoop s
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) remaining)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    t)
                  (And
                    (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 340) (instOfNatNat (nat_lit 340))))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start remaining))
                    (And
                      (∀ (j : Nat),
                        @LE.le.{0} Nat instLENat start j →
                          @LT.lt.{0} Nat instLTNat j
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start remaining) →
                            And (@Eq.{1} Nat (t.natMem j) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              (@Eq.{1} Nat
                                (t.natMem (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) bank j))
                                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                      (And (@Eq.{1} (Nat → Real) t.realMem s.realMem)
                        (∀ (a : Nat),
                          Or (@LT.lt.{0} Nat instLTNat a start)
                              (@LE.le.{0} Nat instLENat
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start remaining) a) →
                            Or
                                (@LT.lt.{0} Nat instLTNat a
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) bank start))
                                (@LE.le.{0} Nat instLENat
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) bank start)
                                    remaining)
                                  a) →
                              @Eq.{1} Nat (t.natMem a) (s.natMem a)))))))) ∧ (((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)} {tentative : Fin i.n → Option.{0} Nat}
  {settled : Finset.{0} (Fin i.n)}
  {tree :
    DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled tree queue s →
    DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Ready i deleted s) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Ready i deleted s →
    (∀ (j : Nat),
        @LE.le.{0} Nat instLENat j (@OfNat.ofNat.{0} Nat (nat_lit 246) (instOfNatNat (nat_lit 246))) →
          @Eq.{1} Nat (t.natReg j) (s.natReg j)) →
      @Eq.{1} Real (t.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
          (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56)))) →
        DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.StaticImage i
            (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.layout i) t →
          DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.ActiveImage i
              (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.layout i) deleted t →
            (∀ (j : Nat),
                @LT.lt.{0} Nat instLTNat j (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i) →
                  @Eq.{1} Nat
                    (t.natMem
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapBase i) j))
                    (s.natMem
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapBase i) j))) →
              DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Ready i deleted t)) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i s →
    (∀ (j : Nat),
        @LE.le.{0} Nat instLENat j (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74))) →
          @Eq.{1} Nat (t.natReg j) (s.natReg j)) →
      (∀ (j : Nat),
          @LE.le.{0} Nat instLENat j (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64))) →
            @Eq.{1} Real (t.realReg j) (s.realReg j)) →
        DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i t) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.install s
    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
    (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.installed s)) ∧ (∀ (j : Nat),
  @Ne.{1} Nat j (@OfNat.ofNat.{0} Nat (nat_lit 236) (instOfNatNat (nat_lit 236))) →
    @Ne.{1} Nat j (@OfNat.ofNat.{0} Nat (nat_lit 238) (instOfNatNat (nat_lit 238))) →
      @Ne.{1} Nat j (@OfNat.ofNat.{0} Nat (nat_lit 246) (instOfNatNat (nat_lit 246))) →
        DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.install j))))) ∧ ((((∀ (j : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.install j) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i s →
    DecrAlmostLinearSSSP.Decremental.Exact.Layout.Image (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.layout i) s →
      DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.StaticImage i
          (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.layout i) s →
        DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.ActiveImage i
            (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.layout i) (@List.nil.{0} (Fin i.k)) s →
          DecrAlmostLinearSSSP.Decremental.Exact.Powers.Prefix
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) i.n i.W)
              (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapBase i)
              (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i) s →
            DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Ready i (@List.nil.{0} (Fin i.k))
              (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.installed s))) ∧ ((∀ (j : Nat),
  @LE.le.{0} Nat instLENat j (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Exact.Powers.code j) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Preparation i s →
    ∃ t,
      And
        (DecrAlmostLinearSSSP.Decremental.Structured.Eval
          (DecrAlmostLinearSSSP.Decremental.Exact.Powers.code.seq
            DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.install)
          s
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
              (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i))
            (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
          t)
        (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Ready i (@List.nil.{0} (Fin i.k)) t)))) ∧ (((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (i : DecrAlmostLinearSSSP.Decremental.Input),
  DecrAlmostLinearSSSP.Decremental.InputCapture.RawInput i
    (DecrAlmostLinearSSSP.Decremental.Structured.data (DecrAlmostLinearSSSP.Decremental.initialMachine p i))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.InputCapture.RawInput i s →
    DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i (DecrAlmostLinearSSSP.Decremental.InputCapture.result s))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.InputCapture.RawInput i s →
    DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.Tape i s →
      ∃ t,
        And
          (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.prepareGraph
            s
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) i.n)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) i.k))
              (@OfNat.ofNat.{0} Nat (nat_lit 37) (instOfNatNat (nat_lit 37))))
            t)
          (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Preparation i t)) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Ready i deleted s →
    (∀ (j : Nat),
        @LE.le.{0} Nat instLENat j (@OfNat.ofNat.{0} Nat (nat_lit 246) (instOfNatNat (nat_lit 246))) →
          @Eq.{1} Nat (t.natReg j) (s.natReg j)) →
      @Eq.{1} Real (t.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
          (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56)))) →
        @Eq.{1} (Nat → Nat) t.natMem s.natMem → DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Ready i deleted t) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Ready i deleted s →
    ∃ t,
      And
        (DecrAlmostLinearSSSP.Decremental.Structured.Eval
          (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.resetPrepare.seq
            DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.resetLoop)
          s
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) i.n)
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          t)
        (And (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Ready i deleted t)
          (And
            (∀ (v : Fin i.n),
              And
                (@Eq.{1} Nat (t.natMem (@Fin.val i.n v)) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (@Eq.{1} Nat
                  (t.natMem
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.layout i).settled (@Fin.val i.n v)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
            (@Eq.{1} (Nat → Real) t.realMem s.realMem)))))))))) ∧ ((((((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.rootSetup s
    (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
    (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.rootData s)) ∧ (∀ (j : Nat),
  @Ne.{1} Nat j (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))) →
    @Ne.{1} Nat j (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260))) →
      @Ne.{1} Nat j (@OfNat.ofNat.{0} Nat (nat_lit 262) (instOfNatNat (nat_lit 262))) →
        @Ne.{1} Nat j (@OfNat.ofNat.{0} Nat (nat_lit 342) (instOfNatNat (nat_lit 342))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.rootSetup
            j)) ∧ ((∀ (j : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.rootSetup j) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Ready i deleted s →
    And
      (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.rootData s).natMem
        (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
          (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
            (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natMem
              (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapSlot i)
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
            (@Fin.val i.n i.source) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.layout i).distances (@Fin.val i.n i.source))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (And
        (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.rootData s).realMem
          (@Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realMem (@Fin.val i.n i.source)
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
        (And
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.rootData s).natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapSlot i)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (And
            (@Eq.{1} Nat
              ((DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.rootData s).natReg
                (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260))))
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
            (@Eq.{1} Nat
              ((DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.rootData s).natReg
                (@OfNat.ofNat.{0} Nat (nat_lit 262) (instOfNatNat (nat_lit 262))))
              (@Fin.val i.n i.source)))))))) ∧ (((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Ready i deleted s →
    (∀ (v : Fin i.n),
        And (@Eq.{1} Nat (s.natMem (@Fin.val i.n v)) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@Eq.{1} Nat
            (s.natMem
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.layout i).settled (@Fin.val i.n v)))
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) →
      DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted
        (@DecrAlmostLinearSSSP.Decremental.Exact.initialTentative i.n i.source)
        (@EmptyCollection.emptyCollection.{0} (Finset.{0} (Fin i.n)) (@Finset.instEmptyCollection.{0} (Fin i.n)))
        (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.empty
          (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i))
        (@OfNat.ofNat.{0} (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))) (nat_lit 0)
          (@Zero.toOfNat0.{0} (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n)))
            (@Multiset.instZero.{0} (Prod.{0, 0} Nat (Fin i.n)))))
        (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.rootData s)) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Ready i deleted s →
    (∀ (v : Fin i.n),
        And (@Eq.{1} Nat (s.natMem (@Fin.val i.n v)) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@Eq.{1} Nat
            (s.natMem
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.layout i).settled (@Fin.val i.n v)))
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) →
      ∃ cost t q,
        And
          (DecrAlmostLinearSSSP.Decremental.Structured.Eval
            (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.rootSetup.seq
              (DecrAlmostLinearSSSP.Decremental.Exact.TriePush.code.seq
                DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.queueCount))
            s cost t)
          (And
            (@LE.le.{0} Nat instLENat cost
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 43) (instOfNatNat (nat_lit 43)))
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))))
            (And (@DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State.memory i deleted q t)
              (@Eq.{1} Nat (@DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State.potential i deleted q)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) i.k)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))) ∧ ((∀ {s u v t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {cr cb cl : Nat},
  DecrAlmostLinearSSSP.Decremental.Structured.Eval
      (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.resetPrepare.seq
        DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.resetLoop)
      s cr u →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval
        (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.rootSetup.seq
          (DecrAlmostLinearSSSP.Decremental.Exact.TriePush.code.seq
            DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.queueCount))
        u cb v →
      DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.loop v cl t →
        DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.code s
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cr cb) cl)
          t) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)}
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
                                (@DecrAlmostLinearSSSP.Decremental.live i.k deleted) i.source v)))))))))))))) ∧ ((((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.deleteCode s
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.deletedData s)) ∧ (∀ (j : Nat),
  @Ne.{1} Nat j (@OfNat.ofNat.{0} Nat (nat_lit 350) (instOfNatNat (nat_lit 350))) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.deleteCode j)) ∧ ((∀ (j : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.deleteCode j) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Ready i deleted s →
    ∀ (e : Fin i.k),
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) (@Fin.val i.k e) →
        DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Ready i
          (@HAppend.hAppend.{0, 0, 0} (List.{0} (Fin i.k)) (List.{0} (Fin i.k)) (List.{0} (Fin i.k))
            (@instHAppendOfAppend.{0} (List.{0} (Fin i.k)) (@List.instAppend.{0} (Fin i.k))) deleted
            (@List.cons.{0} (Fin i.k) e (@List.nil.{0} (Fin i.k))))
          (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.deletedData s)))) ∧ (((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
      DecrAlmostLinearSSSP.Decremental.InputCapture.RawInput i s →
        DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.Tape i s →
          ∃ cost t q,
            And
              (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.initializeCode s cost t)
              (And
                (@LE.le.{0} Nat instLENat cost
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 700) (instOfNatNat (nat_lit 700)))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n i.k)
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                (And (@DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State.memory i (@List.nil.{0} (Fin i.k)) q t)
                  (And
                    (@Eq.{1} (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n)))
                      (@DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State.queue i (@List.nil.{0} (Fin i.k)) q)
                      (@OfNat.ofNat.{0} (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))) (nat_lit 0)
                        (@Zero.toOfNat0.{0} (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n)))
                          (@Multiset.instZero.{0} (Prod.{0, 0} Nat (Fin i.n))))))
                    (And (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Ready i (@List.nil.{0} (Fin i.k)) t)
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
                                (i.dist (@List.nil.{0} (Fin i.k)) v))
                              (Iff
                                (@Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.stored t.machine (@Fin.val i.n v))
                                  (@Top.top.{0} ENNReal ENNReal.instTop))
                                (Not
                                  (@DecrAlmostLinearSSSP.Decremental.Reachable i.n i.k i.graph
                                    (@DecrAlmostLinearSSSP.Decremental.live i.k (@List.nil.{0} (Fin i.k))) i.source
                                    v))))))))))) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Ready i deleted s →
    ∀ (index : Nat),
      DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Ready i deleted
        { realReg := s.realReg,
          natReg :=
            @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) index,
          realMem := s.realMem, natMem := s.natMem })) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input},
  i.Valid →
    ∀ {deleted : List.{0} (Fin i.k)} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
      DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Ready i deleted s →
        ∀ (e : Fin i.k),
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) (@Fin.val i.k e) →
            ∃ cost t q,
              And
                (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.updateCode s cost t)
                (And
                  (@LE.le.{0} Nat instLENat cost
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 602) (instOfNatNat (nat_lit 602)))
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n i.k)
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                  (And
                    (@DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State.memory i
                      (@HAppend.hAppend.{0, 0, 0} (List.{0} (Fin i.k)) (List.{0} (Fin i.k)) (List.{0} (Fin i.k))
                        (@instHAppendOfAppend.{0} (List.{0} (Fin i.k)) (@List.instAppend.{0} (Fin i.k))) deleted
                        (@List.cons.{0} (Fin i.k) e (@List.nil.{0} (Fin i.k))))
                      q t)
                    (And
                      (@Eq.{1} (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n)))
                        (@DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State.queue i
                          (@HAppend.hAppend.{0, 0, 0} (List.{0} (Fin i.k)) (List.{0} (Fin i.k)) (List.{0} (Fin i.k))
                            (@instHAppendOfAppend.{0} (List.{0} (Fin i.k)) (@List.instAppend.{0} (Fin i.k))) deleted
                            (@List.cons.{0} (Fin i.k) e (@List.nil.{0} (Fin i.k))))
                          q)
                        (@OfNat.ofNat.{0} (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))) (nat_lit 0)
                          (@Zero.toOfNat0.{0} (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n)))
                            (@Multiset.instZero.{0} (Prod.{0, 0} Nat (Fin i.n))))))
                      (And
                        (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Ready i
                          (@HAppend.hAppend.{0, 0, 0} (List.{0} (Fin i.k)) (List.{0} (Fin i.k)) (List.{0} (Fin i.k))
                            (@instHAppendOfAppend.{0} (List.{0} (Fin i.k)) (@List.instAppend.{0} (Fin i.k))) deleted
                            (@List.cons.{0} (Fin i.k) e (@List.nil.{0} (Fin i.k))))
                          t)
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
                                  (i.dist
                                    (@HAppend.hAppend.{0, 0, 0} (List.{0} (Fin i.k)) (List.{0} (Fin i.k))
                                      (List.{0} (Fin i.k))
                                      (@instHAppendOfAppend.{0} (List.{0} (Fin i.k)) (@List.instAppend.{0} (Fin i.k)))
                                      deleted (@List.cons.{0} (Fin i.k) e (@List.nil.{0} (Fin i.k))))
                                    v))
                                (Iff
                                  (@Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.stored t.machine (@Fin.val i.n v))
                                    (@Top.top.{0} ENNReal ENNReal.instTop))
                                  (Not
                                    (@DecrAlmostLinearSSSP.Decremental.Reachable i.n i.k i.graph
                                      (@DecrAlmostLinearSSSP.Decremental.live i.k
                                        (@HAppend.hAppend.{0, 0, 0} (List.{0} (Fin i.k)) (List.{0} (Fin i.k))
                                          (List.{0} (Fin i.k))
                                          (@instHAppendOfAppend.{0} (List.{0} (Fin i.k))
                                            (@List.instAppend.{0} (Fin i.k)))
                                          deleted (@List.cons.{0} (Fin i.k) e (@List.nil.{0} (Fin i.k)))))
                                      i.source v))))))))))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∃ cost c,
      And
        (DecrAlmostLinearSSSP.Decremental.Ends DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.hostProgram
          (DecrAlmostLinearSSSP.Decremental.initialMachine DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.hostProgram
            i)
          c)
        (And
          (@Eq.{1} Nat c.work
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cost
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (And
            (@LE.le.{0} Nat instLENat cost
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 700) (instOfNatNat (nat_lit 700)))
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n i.k)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
            (And
              (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Ready i (@List.nil.{0} (Fin i.k))
                (DecrAlmostLinearSSSP.Decremental.Structured.data c))
              (∃ q,
                And
                  (@DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State.memory i (@List.nil.{0} (Fin i.k)) q
                    (DecrAlmostLinearSSSP.Decremental.Structured.data c))
                  (@Eq.{1} (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n)))
                    (@DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State.queue i (@List.nil.{0} (Fin i.k)) q)
                    (@OfNat.ofNat.{0} (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))) (nat_lit 0)
                      (@Zero.toOfNat0.{0} (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n)))
                        (@Multiset.instZero.{0} (Prod.{0, 0} Nat (Fin i.n))))))))))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (deleted : List.{0} (Fin i.k)) (c : DecrAlmostLinearSSSP.Decremental.Machine),
      DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Ready i deleted
          (DecrAlmostLinearSSSP.Decremental.Structured.data c) →
        ∀ (e : Fin i.k),
          ∃ cost d,
            And
              (DecrAlmostLinearSSSP.Decremental.Ends DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.hostProgram
                (DecrAlmostLinearSSSP.Decremental.deletionMachine
                  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.hostProgram c (@Fin.val i.k e))
                d)
              (And
                (@Eq.{1} Nat d.work
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work cost)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (And
                  (@LE.le.{0} Nat instLENat cost
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 602) (instOfNatNat (nat_lit 602)))
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n i.k)
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                  (And
                    (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Ready i
                      (@HAppend.hAppend.{0, 0, 0} (List.{0} (Fin i.k)) (List.{0} (Fin i.k)) (List.{0} (Fin i.k))
                        (@instHAppendOfAppend.{0} (List.{0} (Fin i.k)) (@List.instAppend.{0} (Fin i.k))) deleted
                        (@List.cons.{0} (Fin i.k) e (@List.nil.{0} (Fin i.k))))
                      (DecrAlmostLinearSSSP.Decremental.Structured.data d))
                    (∃ q,
                      And
                        (@DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State.memory i
                          (@HAppend.hAppend.{0, 0, 0} (List.{0} (Fin i.k)) (List.{0} (Fin i.k)) (List.{0} (Fin i.k))
                            (@instHAppendOfAppend.{0} (List.{0} (Fin i.k)) (@List.instAppend.{0} (Fin i.k))) deleted
                            (@List.cons.{0} (Fin i.k) e (@List.nil.{0} (Fin i.k))))
                          q (DecrAlmostLinearSSSP.Decremental.Structured.data d))
                        (@Eq.{1} (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n)))
                          (@DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State.queue i
                            (@HAppend.hAppend.{0, 0, 0} (List.{0} (Fin i.k)) (List.{0} (Fin i.k)) (List.{0} (Fin i.k))
                              (@instHAppendOfAppend.{0} (List.{0} (Fin i.k)) (@List.instAppend.{0} (Fin i.k))) deleted
                              (@List.cons.{0} (Fin i.k) e (@List.nil.{0} (Fin i.k))))
                            q)
                          (@OfNat.ofNat.{0} (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))) (nat_lit 0)
                            (@Zero.toOfNat0.{0} (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n)))
                              (@Multiset.instZero.{0} (Prod.{0, 0} Nat (Fin i.n)))))))))))))))) ∧ (((((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)}
  {c : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Completed i deleted c →
    DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Ready i deleted (DecrAlmostLinearSSSP.Decremental.Structured.data c)) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input},
  i.Valid →
    ∀ {deleted : List.{0} (Fin i.k)} {c : DecrAlmostLinearSSSP.Decremental.Machine},
      DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Completed i deleted c →
        DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Good i deleted c)) ∧ ((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c d : DecrAlmostLinearSSSP.Decremental.Machine),
  @Eq.{1} Bool c.halted Bool.false →
    DecrAlmostLinearSSSP.Decremental.Ends p c d →
      @LE.le.{0} Nat instLENat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        d.work) ∧ (∀ (D overhead before after cost : Nat),
  @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) before
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      after →
    @LE.le.{0} Nat instLENat cost
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) D
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) after before))
          overhead) →
      @LE.le.{0} Nat instLENat cost
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) D overhead)
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) after before))))) ∧ (((∀ {k : Nat} (ds : List.{0} (Fin k)) (j : Nat),
  @LE.le.{0} (Finset.{0} (Fin k))
    (@Preorder.toLE.{0} (Finset.{0} (Fin k))
      (@PartialOrder.toPreorder.{0} (Finset.{0} (Fin k)) (@Finset.instPartialOrder.{0} (Fin k))))
    (@DecrAlmostLinearSSSP.Decremental.live k ds)
    (@DecrAlmostLinearSSSP.Decremental.live k (@List.take.{0} (Fin k) j ds))) ∧ (∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {i : DecrAlmostLinearSSSP.Decremental.Input} {ds : List.{0} (Fin i.k)}
  {cs : List.{0} DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.OnlineRun p i ds cs →
    ∃ c,
      And
        (@Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Machine)
          (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Machine) Nat
            DecrAlmostLinearSSSP.Decremental.Machine
            (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Machine as))
            (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Machine) cs
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Machine c))
        (DecrAlmostLinearSSSP.Decremental.Ends p (DecrAlmostLinearSSSP.Decremental.initialMachine p i) c))) ∧ ((∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {C : Real} {a : Nat → Real} {queryBound : Nat} {logWeights : Bool}
  {i : DecrAlmostLinearSSSP.Decremental.Input},
  DecrAlmostLinearSSSP.Decremental.Maintains p C a queryBound logWeights i →
    ∃ c,
      And (DecrAlmostLinearSSSP.Decremental.Ends p (DecrAlmostLinearSSSP.Decremental.initialMachine p i) c)
        (And
          (@Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.stored c (@Fin.val i.n i.source))
            (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero)))
          (And
            (∀ (v : Fin i.n),
              And
                (@LE.le.{0} Nat instLENat (c.natMem (@Fin.val i.n v))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (@Eq.{1} Nat (c.natMem (@Fin.val i.n v)) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                  @LE.le.{0} Real Real.instLE
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                    (c.realMem (@Fin.val i.n v))))
            (And
              (∀ (v : Fin i.n),
                And
                  (@LE.le.{0} ENNReal ENNReal.instLE (i.dist (@List.nil.{0} (Fin i.k)) v)
                    (DecrAlmostLinearSSSP.Decremental.stored c (@Fin.val i.n v)))
                  (And
                    (@LE.le.{0} ENNReal ENNReal.instLE (DecrAlmostLinearSSSP.Decremental.stored c (@Fin.val i.n v))
                      (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                        (@instHMul.{0} ENNReal
                          (@Distrib.toMul.{0} ENNReal
                            (@instDistribOfSemiring.{0} ENNReal
                              (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                        (ENNReal.ofReal
                          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) i.accuracy))
                        (i.dist (@List.nil.{0} (Fin i.k)) v)))
                    (Iff
                      (@Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.stored c (@Fin.val i.n v))
                        (@Top.top.{0} ENNReal ENNReal.instTop))
                      (Not
                        (@DecrAlmostLinearSSSP.Decremental.Reachable i.n i.k i.graph
                          (@DecrAlmostLinearSSSP.Decremental.live i.k (@List.nil.{0} (Fin i.k))) i.source v)))))
              (@LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast c.work)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
                        (@Nat.cast.{0} Real Real.instNatCast i.size))
                      (a i.size))
                    i.accuracy)
                  (@ite.{1} Real (@Eq.{1} Bool logWeights Bool.true) (instDecidableEqBool logWeights Bool.true)
                    (@Max.max.{0} Real Real.instMax
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                      (DecrAlmostLinearSSSP.Decremental.logarithm2 (@Nat.cast.{0} Real Real.instNatCast i.W)))
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))))))) ∧ ((∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {c d e : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.Ends p c d →
    DecrAlmostLinearSSSP.Decremental.Ends p c e → @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine d e) ∧ (∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {i : DecrAlmostLinearSSSP.Decremental.Input} {ds : List.{0} (Fin i.k)}
  {cs : List.{0} DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.OnlineRun p i ds cs →
    @Eq.{1} Nat (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Machine cs)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))) ∧ ((((∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {i : DecrAlmostLinearSSSP.Decremental.Input} {ds : List.{0} (Fin i.k)}
  {cs : List.{0} DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.OnlineRun p i ds cs →
    ∀ (k : Nat) (hk : @LT.lt.{0} Nat instLTNat k (@List.length.{0} (Fin i.k) ds)),
      ∃ c d,
        And
          (@Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Machine)
            (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Machine) Nat
              DecrAlmostLinearSSSP.Decremental.Machine
              (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Machine as))
              (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Machine) cs k)
            (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Machine c))
          (And
            (@Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Machine)
              (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Machine) Nat
                DecrAlmostLinearSSSP.Decremental.Machine
                (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Machine as))
                (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Machine) cs
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Machine d))
            (DecrAlmostLinearSSSP.Decremental.Ends p
              (DecrAlmostLinearSSSP.Decremental.deletionMachine p c
                (@Fin.val i.k
                  (@GetElem.getElem.{0, 0, 0} (List.{0} (Fin i.k)) Nat (Fin i.k)
                    (fun as i_1 => @LT.lt.{0} Nat instLTNat i_1 (@List.length.{0} (Fin i.k) as))
                    (@List.instGetElemNatLtLength.{0} (Fin i.k)) ds k hk)))
              d))) ∧ (∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {c d : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.Ends p c d → @LE.le.{0} Nat instLENat c.work d.work)) ∧ ((∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {i : DecrAlmostLinearSSSP.Decremental.Input} {ds : List.{0} (Fin i.k)}
  {cs : List.{0} DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.OnlineRun p i ds cs →
    ∀ (last : DecrAlmostLinearSSSP.Decremental.Machine),
      @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Machine)
          (@List.getLast?.{0} DecrAlmostLinearSSSP.Decremental.Machine cs)
          (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Machine last) →
        ∀ (c : DecrAlmostLinearSSSP.Decremental.Machine),
          @Membership.mem.{0, 0} DecrAlmostLinearSSSP.Decremental.Machine
              (List.{0} DecrAlmostLinearSSSP.Decremental.Machine)
              (@List.instMembership.{0} DecrAlmostLinearSSSP.Decremental.Machine) cs c →
            @LE.le.{0} Nat instLENat c.work last.work) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (ds : List.{0} (Fin i.k)),
      ∃ cs last,
        And
          (DecrAlmostLinearSSSP.Decremental.OnlineRun DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.hostProgram i ds
            cs)
          (And
            (@Eq.{1} Nat (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Machine cs)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (And
              (@Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Machine)
                (@List.getLast?.{0} DecrAlmostLinearSSSP.Decremental.Machine cs)
                (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Machine last))
              (And (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Completed i ds last)
                (And
                  (∀ (j : Nat) (c : DecrAlmostLinearSSSP.Decremental.Machine),
                    @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Machine)
                        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Machine) Nat
                          DecrAlmostLinearSSSP.Decremental.Machine
                          (fun as i =>
                            @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Machine as))
                          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Machine) cs j)
                        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Machine c) →
                      DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Completed i (@List.take.{0} (Fin i.k) j ds) c)
                  (@LE.le.{0} Nat instLENat
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) last.work
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) (@List.length.{0} (Fin i.k) ds)))
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000)))
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n i.k)
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))))))) ∧ (((DecrAlmostLinearSSSP.Decremental.Subpolynomial DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.overhead) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    @LE.le.{0} Real Real.instLE
      (@Nat.cast.{0} Real Real.instNatCast
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.overhead i.size)
        (@Max.max.{0} Real Real.instMax (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (DecrAlmostLinearSSSP.Decremental.logarithm2 (@Nat.cast.{0} Real Real.instNatCast i.W)))))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    @LE.le.{0} Real Real.instLE i.accuracy
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@Nat.cast.{0} Real Real.instNatCast i.size)) →
      @LE.le.{0} Real Real.instLE
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 10000)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 10000) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 9999) (instOfNatNat (nat_lit 9999)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 9998) (instOfNatNat (nat_lit 9998)))))))
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
              (@Nat.cast.{0} Real Real.instNatCast i.size)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (@Nat.cast.{0} Real Real.instNatCast
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@OfNat.ofNat.{0} Real (nat_lit 10000)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 10000) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 9999) (instOfNatNat (nat_lit 9999)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 9998) (instOfNatNat (nat_lit 9998)))))))
                (@Nat.cast.{0} Real Real.instNatCast i.size))
              (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.overhead i.size))
            i.accuracy)
          (@Max.max.{0} Real Real.instMax (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (DecrAlmostLinearSSSP.Decremental.logarithm2 (@Nat.cast.{0} Real Real.instNatCast i.W))))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (ds : List.{0} (Fin i.k)),
      @DecrAlmostLinearSSSP.Decremental.Legal i.k ds →
        @LE.le.{0} Nat instLENat
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000)))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n i.k)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 10000) (instOfNatNat (nat_lit 10000)))
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) i.size
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    @LE.le.{0} Real Real.instLE i.accuracy
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@Nat.cast.{0} Real Real.instNatCast i.size)) →
      DecrAlmostLinearSSSP.Decremental.Maintains DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.hostProgram
        (@OfNat.ofNat.{0} Real (nat_lit 10000)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 10000) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 9999) (instOfNatNat (nat_lit 9999)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 9998) (instOfNatNat (nat_lit 9998)))))))
        DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.overhead
        (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) Bool.true i)))))))) := by
  exact ⟨⟨⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.popped_eval,DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.popped_nat_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.popped_real_frame,DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory.popped⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.remainingDegree_empty,DecrAlmostLinearSSSP.Decremental.Exact.remainingDegree_insert⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.potential_skip,DecrAlmostLinearSSSP.Decremental.Exact.potential_settle⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.potential_initial,DecrAlmostLinearSSSP.Decremental.Structured.eval_loop_amortized⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.body_append,DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State.step⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State.run,DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State.source_normalized⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State.exact_infinity,⟨DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.resetBody_eval,DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.resetBody_fields⟩⟩⟩⟩⟩,⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.resetBody_nat_frame,DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.resetLoop_nat_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.resetLoop_real_frame,DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.resetLoop_eval⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory.ready,DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Ready.frame⟩,⟨DecrAlmostLinearSSSP.Decremental.InputCapture.Captured.frame,⟨DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.install_eval,DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.install_nat_frame⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.install_real_frame,DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.install_ready⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.powers_real_frame,DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Preparation.powers⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.InputCapture.raw_initial,DecrAlmostLinearSSSP.Decremental.InputCapture.captures_raw⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.prepareGraph_eval,⟨DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Ready.register_frame,DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Ready.reset⟩⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.root_eval,DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.root_nat_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.root_real_frame,DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Ready.root_fields⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Ready.root_memory,DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Ready.initialState⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.code_append,DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Ready.execute⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.delete_eval,DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.delete_nat_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.delete_real_frame,DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Ready.delete⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.initialize_eval,DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Ready.external⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.update_eval,⟨DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.program_initialization,DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.program_update⟩⟩⟩⟩⟩,⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Completed.ready,DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Completed.good⟩,⟨DecrAlmostLinearSSSP.Decremental.ends_running_work_positive,DecrAlmostLinearSSSP.Decremental.call_overhead_absorbed⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.live_take_subset,DecrAlmostLinearSSSP.Decremental.OnlineRun.initial_execution⟩,⟨DecrAlmostLinearSSSP.Decremental.Maintains.initialization,⟨DecrAlmostLinearSSSP.Decremental.Ends.deterministic,DecrAlmostLinearSSSP.Decremental.OnlineRun.length⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.OnlineRun.transition_at,DecrAlmostLinearSSSP.Decremental.Ends.work_mono⟩,⟨DecrAlmostLinearSSSP.Decremental.OnlineRun.work_le_last,DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.online⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.overhead_subpolynomial,DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.height_work_bound⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.small_accuracy_work_bound,⟨DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.stream_work_bound,DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.exact_small_accuracy_maintains⟩⟩⟩⟩⟩⟩⟩
