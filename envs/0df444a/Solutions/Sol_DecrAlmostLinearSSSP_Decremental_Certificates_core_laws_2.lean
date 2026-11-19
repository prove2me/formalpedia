-- Prove2me | solution 1 for DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T17:36:26.953444+00:00
-- url     : https://prove2.me/submissions/08b43024-fe7f-46db-96f0-2e36949d4531

import Definitions.Def_DecrAlmostLinearSSSP_CoreRAMFoundation
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_2
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_3
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_4
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_5
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_6
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_7
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_8
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_normal_laws_1
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_normal_laws_2
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_normal_laws_3
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_normal_laws_4
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_normal_laws_5
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_normal_laws_6
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_normal_laws_7
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_normal_laws_8
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_normal_laws_9
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_normal_laws_10
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_normal_laws_11
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_normal_laws_12
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_core_laws_1
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
open scoped ENNReal NNReal
attribute [local instance] Classical.propDecidable
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
theorem DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image.count : ∀ {s : DecrAlmostLinearSSSP.Decremental.Structured.Data} {height : Nat}
  {tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie height},
  @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image s height tree →
    @Ne.{1} Nat (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root height tree)
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
      @Eq.{1} Nat (s.natMem (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root height tree))
        (@DecrAlmostLinearSSSP.Decremental.RadixQueue.count height
          (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.abstract height tree)) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.1.1.2.2.1.1
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
theorem DecrAlmostLinearSSSP.Decremental.Structured.eval_nadd : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (d a b : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.nadd d a b) s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    { realReg := s.realReg,
      natReg :=
        @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natReg d
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (s.natReg a) (s.natReg b)),
      realMem := s.realMem, natMem := s.natMem } := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.1.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Structured.eval_store : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (a d : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.store a d) s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    { realReg := s.realReg, natReg := s.natReg,
      realMem := @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realMem (s.natReg a) (s.realReg d),
      natMem := s.natMem } := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.2.1.1.1.2
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
theorem DecrAlmostLinearSSSP.Decremental.Structured.Eval.no_real_memory : ∀ {cmd : DecrAlmostLinearSSSP.Decremental.Structured.Cmd} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {cost : Nat},
  DecrAlmostLinearSSSP.Decremental.Structured.Eval cmd s cost t →
    DecrAlmostLinearSSSP.Decremental.Structured.NoRealMemory cmd → @Eq.{1} (Nat → Real) t.realMem s.realMem := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_3.1.2.2.1.1.2
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
theorem DecrAlmostLinearSSSP.Decremental.subpolynomial_constant : ∀ (c : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) c →
    DecrAlmostLinearSSSP.Decremental.Subpolynomial fun x => c := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.1.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.subpolynomial_add : ∀ (a b : Nat → Real),
  DecrAlmostLinearSSSP.Decremental.Subpolynomial a →
    DecrAlmostLinearSSSP.Decremental.Subpolynomial b →
      DecrAlmostLinearSSSP.Decremental.Subpolynomial fun m =>
        @HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (a m) (b m) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.1.2.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.Powers.Prefix.step : ∀ {bound base d : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Powers.Prefix bound base d s →
    DecrAlmostLinearSSSP.Decremental.Exact.Powers.Prefix bound base
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (DecrAlmostLinearSSSP.Decremental.Exact.Powers.advanced s) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.1.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.bankAddress_injective : ∀ {base j k a b : Nat},
  @Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.bankAddress base j a)
      (DecrAlmostLinearSSSP.Decremental.bankAddress base k b) →
    And (@Eq.{1} Nat j k) (@Eq.{1} Nat a b) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.ShadowRep.scratch : ∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    ∀ (x : Nat),
      DecrAlmostLinearSSSP.Decremental.ShadowRep base F
        { pc := c.pc, realReg := c.realReg,
          natReg :=
            @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat c.natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) x,
          realMem := c.realMem, natMem := c.natMem, halted := c.halted, fault := c.fault, work := c.work }
        g := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.2.2.2.1.1
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
theorem DecrAlmostLinearSSSP.Decremental.InputCapture.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.InputCapture.code s
    (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19)))
    (DecrAlmostLinearSSSP.Decremental.InputCapture.result s) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.1.2.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.InputCapture.no_memory : DecrAlmostLinearSSSP.Decremental.Structured.NoMemory DecrAlmostLinearSSSP.Decremental.InputCapture.code := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.1.2.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.InputCapture.captures_initial : ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (i : DecrAlmostLinearSSSP.Decremental.Input),
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i
    (DecrAlmostLinearSSSP.Decremental.InputCapture.result
      (DecrAlmostLinearSSSP.Decremental.Structured.data (DecrAlmostLinearSSSP.Decremental.initialMachine p i))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.1.2.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.InputCapture.initial_shadow_zero : ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (i : DecrAlmostLinearSSSP.Decremental.Input) (j : Nat),
  And
    (@Eq.{1} Nat
      ((DecrAlmostLinearSSSP.Decremental.InputCapture.result
            (DecrAlmostLinearSSSP.Decremental.Structured.data
              (DecrAlmostLinearSSSP.Decremental.initialMachine p i))).natReg
        (DecrAlmostLinearSSSP.Decremental.shadowReg j))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@Eq.{1} Real
      ((DecrAlmostLinearSSSP.Decremental.InputCapture.result
            (DecrAlmostLinearSSSP.Decremental.Structured.data
              (DecrAlmostLinearSSSP.Decremental.initialMachine p i))).realReg
        (DecrAlmostLinearSSSP.Decremental.shadowReg j))
      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.1.2.2.2.1.1
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
theorem DecrAlmostLinearSSSP.Decremental.initial_nat_tape : ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (i : DecrAlmostLinearSSSP.Decremental.Input) (e : Fin i.k)
  (offset : Nat),
  @LT.lt.{0} Nat instLTNat offset (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
    @Eq.{1} Nat
      ((DecrAlmostLinearSSSP.Decremental.initialMachine p i).natMem
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (@Fin.val i.k e)))
          offset))
      (@ite.{1} Nat (@Eq.{1} Nat offset (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (instDecidableEqNat offset (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@Fin.val i.n (@DecrAlmostLinearSSSP.Decremental.Digraph.tail i.n i.k i.graph e))
        (@ite.{1} Nat (@Eq.{1} Nat offset (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (instDecidableEqNat offset (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@Fin.val i.n (@DecrAlmostLinearSSSP.Decremental.Digraph.head i.n i.k i.graph e)) (i.weight e))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_6.1.2.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.initial_nat_above_tape : ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (i : DecrAlmostLinearSSSP.Decremental.Input) (address : Nat),
  @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
      address →
    @Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.initialMachine p i).natMem address)
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_6.1.2.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.initial_source_bank_zero : ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (i : DecrAlmostLinearSSSP.Decremental.Input) (B F : Nat),
  @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
      B →
    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) F →
      ∀ (address : Nat),
        And
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.initialMachine p i).natMem
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) address)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@Eq.{1} Real
            ((DecrAlmostLinearSSSP.Decremental.initialMachine p i).realMem
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) address)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_6.1.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.StaticImage.frame : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {l : DecrAlmostLinearSSSP.Decremental.Exact.Layout.Addresses}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.StaticImage i l s →
    (∀ (a : Nat),
        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
            (DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.staticFootprint i l) a →
          @Eq.{1} Nat (t.natMem a) (s.natMem a)) →
      DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.StaticImage i l t := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_6.2.2.1.1.2.2
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
theorem DecrAlmostLinearSSSP.Decremental.Exact.Heap.Image.count : ∀ {n h base slot : Nat} {tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin n))} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  @DecrAlmostLinearSSSP.Decremental.Exact.Heap.Image n h base slot tree queue s →
    @Eq.{1} Nat
      (@DecrAlmostLinearSSSP.Decremental.RadixQueue.count h
        (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.abstract h tree))
      (@Multiset.card.{0} (Prod.{0, 0} Nat (Fin n)) queue) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_7.1.1.1.1.1.2
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
theorem DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory.target : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)} {tentative : Fin i.n → Option.{0} Nat}
  {settled : Finset.{0} (Fin i.n)}
  {tree :
    DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled tree queue s →
    ∀ (v : Fin i.n),
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 310) (instOfNatNat (nat_lit 310)))) (@Fin.val i.n v) →
        And
          (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled tree queue
            (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.targetData s))
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.targetData s).natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 320) (instOfNatNat (nat_lit 320))))
            (@ite.{1} Nat
              (@Membership.mem.{0, 0} (Fin i.n) (Finset.{0} (Fin i.n))
                (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin i.n)) (Fin i.n) (@Finset.instSetLike.{0} (Fin i.n)))
                settled v)
              (@Finset.decidableMem.{0} (Fin i.n) (instDecidableEqFin i.n) v settled)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_7.2.1.2.2.1.2
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
theorem DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Ready.frame : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)}
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
              DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Ready i deleted t := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_8.1.2.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.InputCapture.Captured.frame : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i s →
    (∀ (j : Nat),
        @LE.le.{0} Nat instLENat j (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74))) →
          @Eq.{1} Nat (t.natReg j) (s.natReg j)) →
      (∀ (j : Nat),
          @LE.le.{0} Nat instLENat j (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64))) →
            @Eq.{1} Real (t.realReg j) (s.realReg j)) →
        DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i t := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_8.1.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.program_initialization : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
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
                        (@Multiset.instZero.{0} (Prod.{0, 0} Nat (Fin i.n)))))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_8.2.1.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.program_update : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
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
                              (@Multiset.instZero.{0} (Prod.{0, 0} Nat (Fin i.n)))))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_8.2.1.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Maintains.initialization : ∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {C : Real} {a : Nat → Real} {queryBound : Nat} {logWeights : Bool}
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
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_8.2.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Ends.deterministic : ∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {c d e : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.Ends p c d →
    DecrAlmostLinearSSSP.Decremental.Ends p c e → @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine d e := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_8.2.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.OnlineRun.length : ∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {i : DecrAlmostLinearSSSP.Decremental.Input} {ds : List.{0} (Fin i.k)}
  {cs : List.{0} DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.OnlineRun p i ds cs →
    @Eq.{1} Nat (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Machine cs)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_8.2.2.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Ends.work_mono : ∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {c d : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.Ends p c d → @LE.le.{0} Nat instLENat c.work d.work := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_8.2.2.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.online : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
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
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_8.2.2.2.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.overhead_subpolynomial : DecrAlmostLinearSSSP.Decremental.Subpolynomial DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.overhead := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_8.2.2.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.Structured.loop_bounded : ∀ (test : DecrAlmostLinearSSSP.Decremental.Structured.Test) (body : DecrAlmostLinearSSSP.Decremental.Structured.Cmd)
  (invariant : DecrAlmostLinearSSSP.Decremental.Structured.Data → Prop)
  (rank : DecrAlmostLinearSSSP.Decremental.Structured.Data → Nat) (B : Nat),
  (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
      invariant s →
        test.holds s →
          ∃ t cost,
            And (DecrAlmostLinearSSSP.Decremental.Structured.Eval body s cost t)
              (And (invariant t)
                (And (@LT.lt.{0} Nat instLTNat (rank t) (rank s)) (@LE.le.{0} Nat instLENat cost B)))) →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
      invariant s →
        ∃ t cost,
          And
            (DecrAlmostLinearSSSP.Decremental.Structured.Eval
              (DecrAlmostLinearSSSP.Decremental.Structured.Cmd.loop test body) s cost t)
            (And (invariant t)
              (@LE.le.{0} Nat instLENat cost
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (rank s))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_1.1.1.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.Structured.eval_loop_stops : ∀ (test : DecrAlmostLinearSSSP.Decremental.Structured.Test) (body : DecrAlmostLinearSSSP.Decremental.Structured.Cmd)
  (cost : Nat) (s t : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.Cmd.loop test body) s
      cost t →
    Not (test.holds t) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_1.1.1.1.1.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.PreservesOutside.trans : ∀ {base F : Nat} {c d e : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.PreservesOutside base F c d →
    DecrAlmostLinearSSSP.Decremental.PreservesOutside base F d e →
      DecrAlmostLinearSSSP.Decremental.PreservesOutside base F c e := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_2.1.1.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.eval_shadow_action : ∀ {B F : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
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
                      (DecrAlmostLinearSSSP.Decremental.instructionEffect ins g))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_2.1.1.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.shadowAction_memory_frame : ∀ {B F : Nat} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
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
                  (@Eq.{1} Nat (t.natMem address) (s.natMem address)) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_2.1.1.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.Structured.Eval.flag_bound : ∀ {cmd : DecrAlmostLinearSSSP.Decremental.Structured.Cmd} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {cost k : Nat},
  DecrAlmostLinearSSSP.Decremental.Structured.Eval cmd s cost t →
    DecrAlmostLinearSSSP.Decremental.Structured.FlagFrame cmd k →
      @LE.le.{0} Nat instLENat (s.natReg k) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
        @LE.le.{0} Nat instLENat (t.natReg k) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_2.1.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.shadowAction_nat_frame : ∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction) (k : Nat),
  @LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) →
    @Ne.{1} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k →
      @Ne.{1} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) k →
        @Ne.{1} Nat (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) k →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.shadowAction ins) k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_2.1.1.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.shadowAction_real_frame : ∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction) (k : Nat),
  @LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.shadowAction ins) k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_2.1.1.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.shadowAction_flag_frame : ∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
  DecrAlmostLinearSSSP.Decremental.Structured.FlagFrame (DecrAlmostLinearSSSP.Decremental.shadowAction ins)
    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_2.1.2.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.shadowAction_even_frame : ∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction) (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.shadowAction ins) k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_2.1.2.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.shadowAction_real_even_frame : ∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction) (k : Nat),
  @Even.{0} Nat instAddNat k →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.shadowAction ins) k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_2.2.1.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.Layout.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (B n S reserve stride : Nat),
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
                    (And (@Eq.{1} (Nat → Real) t.realMem s.realMem) (@Eq.{1} (Nat → Nat) t.natMem s.natMem))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_2.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Layout.real_frame : ∀ (stride k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.Layout.code stride) k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_3.1.1.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.Prepass.nat_frame : ∀ (coefficient stride k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 84) (instOfNatNat (nat_lit 84))) →
      @Even.{0} Nat instAddNat k →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 48) (instOfNatNat (nat_lit 48))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 60) (instOfNatNat (nat_lit 60))) →
              @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))) →
                @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))) →
                  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
                    (DecrAlmostLinearSSSP.Decremental.Prepass.code coefficient stride) k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_3.1.1.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Prepass.real_frame : ∀ (coefficient stride k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 84) (instOfNatNat (nat_lit 84))) →
              DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
                (DecrAlmostLinearSSSP.Decremental.Prepass.code coefficient stride) k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_3.1.1.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Prepass.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i s →
      ∀ (coefficient stride : Nat),
        ∃ cost t,
          And
            (DecrAlmostLinearSSSP.Decremental.Structured.Eval
              (DecrAlmostLinearSSSP.Decremental.Prepass.code coefficient stride) s cost t)
            (And
              (DecrAlmostLinearSSSP.Decremental.Layout.Represents t
                (DecrAlmostLinearSSSP.Decremental.Layout.addresses
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) coefficient
                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) i.size
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  stride))
              (And
                (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 60) (instOfNatNat (nat_lit 60))))
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) coefficient
                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) i.size
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (And
                  (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
                    (DecrAlmostLinearSSSP.Decremental.scaleCount i))
                  (And
                    (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))))
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) i.n
                        (DecrAlmostLinearSSSP.Decremental.scaleCount i)))
                    (And
                      (@LE.le.{0} Nat instLENat cost
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
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
                                      (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))
                                      (DecrAlmostLinearSSSP.Decremental.utilityDepth i.size))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))))
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (DecrAlmostLinearSSSP.Decremental.dispatchCharge
                                        DecrAlmostLinearSSSP.Decremental.ScaledCeiling.ceilingProgram.code)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))
                                      (DecrAlmostLinearSSSP.Decremental.scaleCount i))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))))
                              coefficient)
                            stride)
                          (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19)))))
                      (∀ (address : Nat),
                        (∀ (a : Nat),
                            @Ne.{1} Nat address
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a))
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                          And (@Eq.{1} Real (t.realMem address) (s.realMem address))
                            (@Eq.{1} Nat (t.natMem address) (s.natMem address)))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_3.1.2.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Fill.eval_code : ∀ (n base stride value : Nat) (realValue : Real) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) stride →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 116) (instOfNatNat (nat_lit 116)))) base →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 118) (instOfNatNat (nat_lit 118)))) n →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 120) (instOfNatNat (nat_lit 120)))) stride →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 122) (instOfNatNat (nat_lit 122))))
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 124) (instOfNatNat (nat_lit 124)))) value →
              @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 116) (instOfNatNat (nat_lit 116)))) realValue →
                @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                  ∃ t,
                    And
                      (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Fill.code s
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) n)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        t)
                      (And
                        (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 116) (instOfNatNat (nat_lit 116))))
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) stride n)))
                        (And
                          (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 118) (instOfNatNat (nat_lit 118))))
                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                          (And
                            (∀ (j : Nat),
                              @LT.lt.{0} Nat instLTNat j n →
                                And
                                  (@Eq.{1} Nat
                                    (t.natMem
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) stride j)))
                                    value)
                                  (@Eq.{1} Real
                                    (t.realMem
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) stride j)))
                                    realValue))
                            (∀ (address : Nat),
                              (∀ (j : Nat),
                                  @LT.lt.{0} Nat instLTNat j n →
                                    @Ne.{1} Nat address
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) stride j))) →
                                And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                  (@Eq.{1} Real (t.realMem address) (s.realMem address)))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_3.1.2.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.Fill.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 116) (instOfNatNat (nat_lit 116))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 118) (instOfNatNat (nat_lit 118))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Fill.code k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_3.1.2.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.Fill.real_frame : ∀ (k : Nat), DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Fill.code k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_3.1.2.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.SnapshotFill.eval_code : ∀ (N : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
        ∃ t,
          And
            (DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.SnapshotFill.code N) s
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) N)
                (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
              t)
            (And
              (∀ (j : Nat),
                @LT.lt.{0} Nat instLTNat j N →
                  And
                    (@Eq.{1} Nat
                      (t.natMem
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                    (@Eq.{1} Real
                      (t.realMem
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
              (∀ (address : Nat),
                (∀ (j : Nat),
                    @LT.lt.{0} Nat instLTNat j N →
                      @Ne.{1} Nat address
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j))) →
                  And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                    (@Eq.{1} Real (t.realMem address) (s.realMem address)))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_3.1.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.SnapshotFill.nat_frame : ∀ (N k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 116) (instOfNatNat (nat_lit 116))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 118) (instOfNatNat (nat_lit 118))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 120) (instOfNatNat (nat_lit 120))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 122) (instOfNatNat (nat_lit 122))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 124) (instOfNatNat (nat_lit 124))) →
            DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.SnapshotFill.code N)
              k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_3.1.2.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.SnapshotFill.real_frame : ∀ (N k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 116) (instOfNatNat (nat_lit 116))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.SnapshotFill.code N) k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_3.1.2.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.SourceMemory.Image.frame : ∀ {B bank : Nat} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {natural : Nat → Nat} {real : Nat → Real},
  DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B bank s natural real →
    (∀ (a : Nat),
        And
          (@Eq.{1} Nat (t.natMem (DecrAlmostLinearSSSP.Decremental.bankAddress B bank a))
            (s.natMem (DecrAlmostLinearSSSP.Decremental.bankAddress B bank a)))
          (@Eq.{1} Real (t.realMem (DecrAlmostLinearSSSP.Decremental.bankAddress B bank a))
            (s.realMem (DecrAlmostLinearSSSP.Decremental.bankAddress B bank a)))) →
      DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B bank t natural real := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_4.1.1.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.TapeCopy.Stable.seq : ∀ {a b : DecrAlmostLinearSSSP.Decremental.Structured.Cmd},
  DecrAlmostLinearSSSP.Decremental.TapeCopy.Stable a →
    DecrAlmostLinearSSSP.Decremental.TapeCopy.Stable b → DecrAlmostLinearSSSP.Decremental.TapeCopy.Stable (a.seq b) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_4.1.2.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.TapeCopy.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (count N B bank tail origin logical high : Nat)
  (delta cutoff : Real) (raw natural : Nat → Nat) (real : Nat → Real),
  DecrAlmostLinearSSSP.Decremental.TapeCopy.Env B bank tail high delta cutoff s →
    DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B bank s natural real →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 162) (instOfNatNat (nat_lit 162)))) origin →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 164) (instOfNatNat (nat_lit 164))))
            (DecrAlmostLinearSSSP.Decremental.bankAddress B bank logical) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 166) (instOfNatNat (nat_lit 166)))) count →
            @LE.le.{0} Nat instLENat
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) origin
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) count))
                B →
              @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                  delta →
                (∀ (address : Nat), @LE.le.{0} Nat instLENat address B → @Eq.{1} Nat (s.natMem address) (raw address)) →
                  (∀ (j : Nat),
                      @LT.lt.{0} Nat instLTNat j count →
                        @LE.le.{0} Real Real.instLE
                          (@Nat.cast.{0} Real Real.instNatCast
                            (raw
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) origin
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j))))
                          (@HPow.hPow.{0, 0, 0} Real Nat Real
                            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                            (@OfNat.ofNat.{0} Real (nat_lit 2)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                            N)) →
                    (∀ (j : Nat),
                        @LT.lt.{0} Nat instLTNat j count →
                          @LE.le.{0} Real Real.instLE
                            (@Nat.cast.{0} Real Real.instNatCast
                              (raw
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) origin
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                            (@HPow.hPow.{0, 0, 0} Real Nat Real
                              (@instHPow.{0, 0} Real Nat
                                (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                              (@OfNat.ofNat.{0} Real (nat_lit 2)
                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                    (@Nat.instNeZeroSucc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                              N)) →
                      (∀ (j : Nat),
                          @LT.lt.{0} Nat instLTNat j count →
                            @LE.le.{0} Real Real.instLE
                                (@Nat.cast.{0} Real Real.instNatCast
                                  (raw
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) origin
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j))
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                                cutoff →
                              @LE.le.{0} Real Real.instLE
                                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                  (@Nat.cast.{0} Real Real.instNatCast
                                    (raw
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) origin
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j))
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                                  delta)
                                (@HPow.hPow.{0, 0, 0} Real Nat Real
                                  (@instHPow.{0, 0} Real Nat
                                    (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                      (@Nat.instAtLeastTwoHAddOfNat
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                        (@Nat.instNeZeroSucc
                                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                                  N)) →
                        ∃ cost t,
                          And
                            (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                              DecrAlmostLinearSSSP.Decremental.TapeCopy.code s cost t)
                            (And
                              (@LE.le.{0} Nat instLENat cost
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) count
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (DecrAlmostLinearSSSP.Decremental.dispatchCharge
                                              DecrAlmostLinearSSSP.Decremental.ScaledCeiling.ceilingProgram.code)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16))) N)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))))
                                      (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                              (And
                                (DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B bank t
                                  (DecrAlmostLinearSSSP.Decremental.TapeCopy.tapeImage raw delta cutoff high count
                                    natural origin logical)
                                  real)
                                (And (DecrAlmostLinearSSSP.Decremental.TapeCopy.Env B bank tail high delta cutoff t)
                                  (And
                                    (@Eq.{1} Nat
                                      (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 162) (instOfNatNat (nat_lit 162))))
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) origin
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) count)))
                                    (And
                                      (@Eq.{1} Nat
                                        (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 164) (instOfNatNat (nat_lit 164))))
                                        (DecrAlmostLinearSSSP.Decremental.bankAddress B bank
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) logical
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) count))))
                                      (And
                                        (@Eq.{1} Nat
                                          (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 166) (instOfNatNat (nat_lit 166))))
                                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                        (And
                                          (∀ (address : Nat),
                                            @LE.le.{0} Nat instLENat address B →
                                              @Eq.{1} Nat (t.natMem address) (raw address))
                                          (∀ (address : Nat),
                                            (∀ (j : Nat),
                                                @LT.lt.{0} Nat instLTNat j
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                                      count) →
                                                  @Ne.{1} Nat address
                                                    (DecrAlmostLinearSSSP.Decremental.bankAddress B bank
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        logical j))) →
                                              (∀ (a : Nat),
                                                  @Ne.{1} Nat address
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (s.natReg
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 48)
                                                            (instOfNatNat (nat_lit 48))))
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                          a))
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                                                And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                                  (@Eq.{1} Real (t.realMem address) (s.realMem address)))))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_4.1.2.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.RecordHeader.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.RecordHeader.code s
    (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19)))
    (DecrAlmostLinearSSSP.Decremental.RecordHeader.result s) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_4.1.2.2.1.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.RecordHeader.values : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
      And
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.RecordHeader.result s).natMem
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106)))))
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 108) (instOfNatNat (nat_lit 108)))))
        (And
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.RecordHeader.result s).natMem
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 134) (instOfNatNat (nat_lit 134))))))
          (And
            (@Eq.{1} Nat
              ((DecrAlmostLinearSSSP.Decremental.RecordHeader.result s).natMem
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112)))))
            (And
              (@Eq.{1} Nat
                ((DecrAlmostLinearSSSP.Decremental.RecordHeader.result s).natMem
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (And
                (@Eq.{1} Real
                  ((DecrAlmostLinearSSSP.Decremental.RecordHeader.result s).realMem
                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106)))))
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@OfNat.ofNat.{0} Real (nat_lit 2)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                    (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 146) (instOfNatNat (nat_lit 146))))))
                (And
                  (@Eq.{1} Real
                    ((DecrAlmostLinearSSSP.Decremental.RecordHeader.result s).realMem
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64))))
                        (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 146) (instOfNatNat (nat_lit 146)))))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@OfNat.ofNat.{0} Real (nat_lit 128)
                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 128) Real.instNatCast
                            (@Nat.instAtLeastTwoHAddOfNat
                              (@OfNat.ofNat.{0} Nat (nat_lit 127) (instOfNatNat (nat_lit 127)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 126) (instOfNatNat (nat_lit 126)))))))
                        (@Nat.cast.{0} Real Real.instNatCast
                          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 66) (instOfNatNat (nat_lit 66))))))))
                  (And
                    (@Eq.{1} Nat
                      ((DecrAlmostLinearSSSP.Decremental.RecordHeader.result s).natReg
                        (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))
                    (And
                      (@Eq.{1} Real
                        ((DecrAlmostLinearSSSP.Decremental.RecordHeader.result s).realReg
                          (@OfNat.ofNat.{0} Nat (nat_lit 148) (instOfNatNat (nat_lit 148))))
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@OfNat.ofNat.{0} Real (nat_lit 2)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                          (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 146) (instOfNatNat (nat_lit 146))))))
                      (@Eq.{1} Real
                        ((DecrAlmostLinearSSSP.Decremental.RecordHeader.result s).realReg
                          (@OfNat.ofNat.{0} Nat (nat_lit 70) (instOfNatNat (nat_lit 70))))
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64))))
                            (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 146) (instOfNatNat (nat_lit 146)))))
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@OfNat.ofNat.{0} Real (nat_lit 128)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 128) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 127) (instOfNatNat (nat_lit 127)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 126) (instOfNatNat (nat_lit 126)))))))
                            (@Nat.cast.{0} Real Real.instNatCast
                              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 66) (instOfNatNat (nat_lit 66))))))))))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_4.1.2.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.RecordHeader.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 216) (instOfNatNat (nat_lit 216))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 212) (instOfNatNat (nat_lit 212))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.RecordHeader.code k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_4.1.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.RecordHeader.real_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 148) (instOfNatNat (nat_lit 148))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 210) (instOfNatNat (nat_lit 210))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 212) (instOfNatNat (nat_lit 212))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 70) (instOfNatNat (nat_lit 70))) →
          DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.RecordHeader.code k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_4.1.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.TailFrame.seq : ∀ {a b : DecrAlmostLinearSSSP.Decremental.Structured.Cmd},
  DecrAlmostLinearSSSP.Decremental.TailFrame a →
    DecrAlmostLinearSSSP.Decremental.TailFrame b → DecrAlmostLinearSSSP.Decremental.TailFrame (a.seq b) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_4.2.1.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.TailFrame.branch : ∀ (test : DecrAlmostLinearSSSP.Decremental.Structured.Test) {a b : DecrAlmostLinearSSSP.Decremental.Structured.Cmd},
  DecrAlmostLinearSSSP.Decremental.TailFrame a →
    DecrAlmostLinearSSSP.Decremental.TailFrame b →
      DecrAlmostLinearSSSP.Decremental.TailFrame (DecrAlmostLinearSSSP.Decremental.Structured.Cmd.branch test a b) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_4.2.1.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.TailFrame.loop : ∀ (test : DecrAlmostLinearSSSP.Decremental.Structured.Test) {body : DecrAlmostLinearSSSP.Decremental.Structured.Cmd},
  DecrAlmostLinearSSSP.Decremental.TailFrame body →
    DecrAlmostLinearSSSP.Decremental.TailFrame (DecrAlmostLinearSSSP.Decremental.Structured.Cmd.loop test body) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_4.2.1.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.SourceSetup.eval_code : ∀ (N entry B F : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data)
  (g : DecrAlmostLinearSSSP.Decremental.Machine),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))) B →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112)))) F →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
        @Eq.{1} Nat g.pc entry →
          @Eq.{1} Nat
              (s.natMem
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
              g.work →
            @Eq.{1} Bool g.halted Bool.false →
              @Eq.{1} Bool g.fault Bool.false →
                (∀ (a : Nat),
                    @Eq.{1} Real
                      (s.realMem
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                      (g.realMem a)) →
                  (∀ (a : Nat),
                      @Eq.{1} Nat
                        (s.natMem
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F (g.natMem a))) →
                    (∀ (j : Nat),
                        @LT.lt.{0} Nat instLTNat j N →
                          And
                            (@Eq.{1} Nat
                              (s.natMem
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F (g.natReg j)))
                            (@Eq.{1} Real
                              (s.realMem
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
                              (g.realReg j))) →
                      (∀ (j : Nat),
                          @LE.le.{0} Nat instLENat N j →
                            And
                              (@Eq.{1} Nat (s.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg j))
                                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                              (@Eq.{1} Real (s.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg j))
                                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))) →
                        DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail N g →
                          ∃ t,
                            And
                              (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                (DecrAlmostLinearSSSP.Decremental.SourceSetup.code N entry) s
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) N))
                                t)
                              (And (DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F t g)
                                (And
                                  (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                    B)
                                  (And
                                    (@Eq.{1} Nat
                                      (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                    (And
                                      (@Eq.{1} Nat
                                        (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) F)
                                      (And
                                        (@Eq.{1} Real
                                          (t.realReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                                          (@Nat.cast.{0} Real Real.instNatCast F))
                                        (And
                                          (@Eq.{1} Nat
                                            (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                          (And (@Eq.{1} (Nat → Real) t.realMem s.realMem)
                                            (@Eq.{1} (Nat → Nat) t.natMem s.natMem)))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_5.1.2.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.SourceSnapshot.nat_frame : ∀ (N k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 54) (instOfNatNat (nat_lit 54))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.SourceSnapshot.code N) k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_5.2.1.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.SourceSnapshot.eval_code : ∀ (N : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
        (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) →
    ∃ t,
      And
        (DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.SourceSnapshot.code N) s
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) N)
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          t)
        (And
          (@Eq.{1} Nat
            (t.natMem
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
                (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
          (And
            (∀ (j : Nat),
              @LT.lt.{0} Nat instLTNat j N →
                And
                  (@Eq.{1} Nat
                    (t.natMem
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
                    (s.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg j)))
                  (@Eq.{1} Real
                    (t.realMem
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
                    (s.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg j))))
            (∀ (address : Nat),
              @Ne.{1} Nat address
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))) →
                (∀ (j : Nat),
                    @LT.lt.{0} Nat instLTNat j N →
                      @Ne.{1} Nat address
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j))) →
                  And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                    (@Eq.{1} Real (t.realMem address) (s.realMem address))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_5.2.1.2.1.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.SourceCall.eval_code : ∀ (N entry B bank : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data)
  (p : DecrAlmostLinearSSSP.Decremental.Program) (g final : DecrAlmostLinearSSSP.Decremental.Machine),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))) B →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))))
        (DecrAlmostLinearSSSP.Decremental.bankFactor bank) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
        @Eq.{1} Nat g.pc entry →
          @Eq.{1} Nat
              (s.natMem
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
              g.work →
            @Eq.{1} Bool g.halted Bool.false →
              @Eq.{1} Bool g.fault Bool.false →
                (∀ (a : Nat),
                    @Eq.{1} Real
                      (s.realMem
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                      (g.realMem a)) →
                  (∀ (a : Nat),
                      @Eq.{1} Nat
                        (s.natMem
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (DecrAlmostLinearSSSP.Decremental.bankFactor bank) (g.natMem a))) →
                    (∀ (j : Nat),
                        @LT.lt.{0} Nat instLTNat j N →
                          And
                            (@Eq.{1} Nat
                              (s.natMem
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (DecrAlmostLinearSSSP.Decremental.bankFactor bank) (g.natReg j)))
                            (@Eq.{1} Real
                              (s.realMem
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
                              (g.realReg j))) →
                      (∀ (j : Nat),
                          @LE.le.{0} Nat instLENat N j →
                            And
                              (@Eq.{1} Nat (s.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg j))
                                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                              (@Eq.{1} Real (s.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg j))
                                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))) →
                        DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail N g →
                          DecrAlmostLinearSSSP.Decremental.Ends p g final →
                            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) →
                              (∃ r,
                                  @Eq.{1} Nat
                                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                                ∃ cost t,
                                  And
                                    (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                      (DecrAlmostLinearSSSP.Decremental.SourceCall.code N entry p) s cost t)
                                    (And
                                      (@LE.le.{0} Nat instLENat cost
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (DecrAlmostLinearSSSP.Decremental.dispatchCharge p.code)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                                                final.work g.work))
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) N))
                                          (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))))
                                      (And
                                        (DecrAlmostLinearSSSP.Decremental.ShadowDataRep B
                                          (DecrAlmostLinearSSSP.Decremental.bankFactor bank) t final)
                                        (And
                                          (@Eq.{1} Nat
                                            (t.natMem
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (s.natReg
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
                                                (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
                                            final.work)
                                          (And
                                            (∀ (j : Nat),
                                              @LT.lt.{0} Nat instLTNat j N →
                                                And
                                                  (@Eq.{1} Nat
                                                    (t.natMem
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (s.natReg
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 50)
                                                            (instOfNatNat (nat_lit 50))))
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                          j)))
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
                                                      (final.natReg j)))
                                                  (@Eq.{1} Real
                                                    (t.realMem
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (s.natReg
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 50)
                                                            (instOfNatNat (nat_lit 50))))
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                          j)))
                                                    (final.realReg j)))
                                            (∀ (address : Nat),
                                              (∀ (a : Nat),
                                                  @Ne.{1} Nat address
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                              (instOfNatNat (nat_lit 2)))
                                                            a)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                            (instOfNatNat (nat_lit 1))))))) →
                                                @Ne.{1} Nat address
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (s.natReg
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 106)
                                                          (instOfNatNat (nat_lit 106))))
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))) →
                                                  (∀ (j : Nat),
                                                      @LT.lt.{0} Nat instLTNat j N →
                                                        @Ne.{1} Nat address
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat)
                                                            (s.natReg
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 50)
                                                                (instOfNatNat (nat_lit 50))))
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                (instOfNatNat (nat_lit 2)))
                                                              j))) →
                                                    And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                                      (@Eq.{1} Real (t.realMem address) (s.realMem address))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_5.2.1.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.ExtendedMax.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
    @LE.le.{0} Nat instLENat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @LE.le.{0} Nat instLENat (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
        (@Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))))
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
            @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))))) →
          (@Eq.{1} Nat (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
              @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                (s.realMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))) →
            ∃ cost t,
              And
                (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.ExtendedMax.code s
                  cost t)
                (And (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                  (And
                    (@LE.le.{0} Nat instLENat
                      (t.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (And
                      (@Eq.{1} Nat (t.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                        @LE.le.{0} Real Real.instLE
                          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                          (t.realMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))))))
                      (And
                        (@Eq.{1} ENNReal
                          (DecrAlmostLinearSSSP.Decremental.ExtendedMax.cell t
                            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
                          (@Max.max.{0} ENNReal ENNReal.instMax
                            (DecrAlmostLinearSSSP.Decremental.ExtendedMax.cell s
                              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
                            (DecrAlmostLinearSSSP.Decremental.ExtendedMax.incoming s)))
                        (∀ (address : Nat),
                          @Ne.{1} Nat address
                              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))) →
                            And (@Eq.{1} Real (t.realMem address) (s.realMem address))
                              (@Eq.{1} Nat (t.natMem address) (s.natMem address))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_5.2.2.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.ScaledReadout.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (F flag : Nat) (delta r : Real),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) F →
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) delta →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 132) (instOfNatNat (nat_lit 132)))) F →
        @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 70) (instOfNatNat (nat_lit 70)))) delta →
          @LE.le.{0} Nat instLENat flag (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
            @Eq.{1} Nat (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 128) (instOfNatNat (nat_lit 128)))))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F flag) →
              @Eq.{1} Real (s.realMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 128) (instOfNatNat (nat_lit 128))))) r →
                (@Eq.{1} Nat flag (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                    @LE.le.{0} Real Real.instLE
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) r) →
                  ∃ cost t,
                    And
                      (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                        DecrAlmostLinearSSSP.Decremental.ScaledReadout.code s cost t)
                      (And (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                        (And
                          (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))) flag)
                          (And
                            (@Eq.{1} Real (t.realReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))))
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) delta r))
                            (And
                              (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                                @LE.le.{0} Real Real.instLE
                                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                  (t.realReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
                              (And
                                (@Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.ExtendedMax.incoming t)
                                  (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                                    (@instHMul.{0} ENNReal
                                      (@Distrib.toMul.{0} ENNReal
                                        (@instDistribOfSemiring.{0} ENNReal
                                          (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                                    (ENNReal.ofReal delta)
                                    (@ite.{1} ENNReal
                                      (@Eq.{1} Nat flag (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                      (instDecidableEqNat flag
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                      (@Top.top.{0} ENNReal ENNReal.instTop) (ENNReal.ofReal r))))
                                (And (@Eq.{1} (Nat → Real) t.realMem s.realMem)
                                  (@Eq.{1} (Nat → Nat) t.natMem s.natMem))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_5.2.2.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.ScaledReadout.no_memory : DecrAlmostLinearSSSP.Decremental.Structured.NoMemory DecrAlmostLinearSSSP.Decremental.ScaledReadout.code := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_5.2.2.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.CacheCopy.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 128) (instOfNatNat (nat_lit 128))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 130) (instOfNatNat (nat_lit 130))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 176) (instOfNatNat (nat_lit 176))) →
            DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CacheCopy.body k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_5.2.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CacheCopy.real_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CacheCopy.body k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_5.2.2.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.CacheCopy.eval_code : ∀ (count sourceBase cacheBase stride F : Nat) (delta : Real) (flags : Nat → Nat) (values : Nat → Real)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) F →
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) delta →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 132) (instOfNatNat (nat_lit 132)))) F →
        @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 70) (instOfNatNat (nat_lit 70)))) delta →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 128) (instOfNatNat (nat_lit 128)))) sourceBase →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))) cacheBase →
              @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 170) (instOfNatNat (nat_lit 170)))) stride →
                @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 176) (instOfNatNat (nat_lit 176)))) count →
                  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                        (∀ (j : Nat),
                            @LT.lt.{0} Nat instLTNat j count →
                              @LE.le.{0} Nat instLENat (flags j)
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                          (∀ (j : Nat),
                              @LT.lt.{0} Nat instLTNat j count →
                                @Eq.{1} Nat (flags j) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                                  @LE.le.{0} Real Real.instLE
                                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                    (values j)) →
                            (∀ (j : Nat),
                                @LT.lt.{0} Nat instLTNat j count →
                                  @Eq.{1} Nat
                                    (s.natMem
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) sourceBase
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) stride j)))
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F (flags j))) →
                              (∀ (j : Nat),
                                  @LT.lt.{0} Nat instLTNat j count →
                                    @Eq.{1} Real
                                      (s.realMem
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) sourceBase
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) stride j)))
                                      (values j)) →
                                (∀ (j : Nat),
                                    @LT.lt.{0} Nat instLTNat j count →
                                      ∀ (k : Nat),
                                        @LT.lt.{0} Nat instLTNat k count →
                                          @Ne.{1} Nat
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) sourceBase
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) stride
                                                j))
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cacheBase
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k))) →
                                  ∃ cost t,
                                    And
                                      (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                        DecrAlmostLinearSSSP.Decremental.CacheCopy.code s cost t)
                                      (And
                                        (@LE.le.{0} Nat instLENat cost
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13))) count)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                        (And
                                          (@Eq.{1} Nat
                                            (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 128) (instOfNatNat (nat_lit 128))))
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) sourceBase
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) stride
                                                count)))
                                          (And
                                            (@Eq.{1} Nat
                                              (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))))
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cacheBase
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) count)))
                                            (And
                                              (@Eq.{1} Nat
                                                (t.natReg
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 176) (instOfNatNat (nat_lit 176))))
                                                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                              (And
                                                (∀ (j : Nat),
                                                  @LT.lt.{0} Nat instLTNat j count →
                                                    And
                                                      (@Eq.{1} Nat
                                                        (t.natMem
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat) cacheBase
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                (instOfNatNat (nat_lit 2)))
                                                              j)))
                                                        (flags j))
                                                      (@Eq.{1} Real
                                                        (t.realMem
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat) cacheBase
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                (instOfNatNat (nat_lit 2)))
                                                              j)))
                                                        (@HMul.hMul.{0, 0, 0} Real Real Real
                                                          (@instHMul.{0} Real Real.instMul) delta (values j))))
                                                (∀ (address : Nat),
                                                  (∀ (j : Nat),
                                                      @LT.lt.{0} Nat instLTNat j count →
                                                        @Ne.{1} Nat address
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat) cacheBase
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                (instOfNatNat (nat_lit 2)))
                                                              j))) →
                                                    And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                                      (@Eq.{1} Real (t.realMem address) (s.realMem address)))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_5.2.2.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame.seq : ∀ {a b : DecrAlmostLinearSSSP.Decremental.Structured.Cmd},
  DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame a →
    DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame b →
      DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame (a.seq b) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_5.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame.loop : ∀ (test : DecrAlmostLinearSSSP.Decremental.Structured.Test) {body : DecrAlmostLinearSSSP.Decremental.Structured.Cmd},
  DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame body →
    DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame (DecrAlmostLinearSSSP.Decremental.Structured.Cmd.loop test body) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_5.2.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.BankFrame.seq : ∀ {a b : DecrAlmostLinearSSSP.Decremental.Structured.Cmd},
  DecrAlmostLinearSSSP.Decremental.Native.BankFrame a →
    DecrAlmostLinearSSSP.Decremental.Native.BankFrame b → DecrAlmostLinearSSSP.Decremental.Native.BankFrame (a.seq b) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_6.1.1.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.Native.BankFrame.loop : ∀ (test : DecrAlmostLinearSSSP.Decremental.Structured.Test) {body : DecrAlmostLinearSSSP.Decremental.Structured.Cmd},
  DecrAlmostLinearSSSP.Decremental.Native.BankFrame body →
    DecrAlmostLinearSSSP.Decremental.Native.BankFrame (DecrAlmostLinearSSSP.Decremental.Structured.Cmd.loop test body) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_6.1.1.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.TapeCopy.ConstantFrame.seq : ∀ {a b : DecrAlmostLinearSSSP.Decremental.Structured.Cmd},
  DecrAlmostLinearSSSP.Decremental.TapeCopy.ConstantFrame a →
    DecrAlmostLinearSSSP.Decremental.TapeCopy.ConstantFrame b →
      DecrAlmostLinearSSSP.Decremental.TapeCopy.ConstantFrame (a.seq b) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_6.2.1.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Native.RecordImage.frame : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {j record cache next : Nat}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.RecordImage i j record cache next s →
    (∀ (offset : Nat),
        @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat)
            (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (@List.nil.{0} Nat))))
            offset →
          And
            (@Eq.{1} Nat (t.natMem (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record offset))
              (s.natMem (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record offset)))
            (@Eq.{1} Real (t.realMem (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record offset))
              (s.realMem (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record offset)))) →
      DecrAlmostLinearSSSP.Decremental.Native.RecordImage i j record cache next t := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_6.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.ControlFrame.seq : ∀ {a b : DecrAlmostLinearSSSP.Decremental.Structured.Cmd},
  DecrAlmostLinearSSSP.Decremental.Native.ControlFrame a →
    DecrAlmostLinearSSSP.Decremental.Native.ControlFrame b →
      DecrAlmostLinearSSSP.Decremental.Native.ControlFrame (a.seq b) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_6.2.2.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.CacheImage.frame : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {j cache : Nat} {b : Fin i.n → ENNReal}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.CacheImage i j cache b s →
    (∀ (v : Fin i.n),
        And
          (@Eq.{1} Nat
            (t.natMem
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cache
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val i.n v))))
            (s.natMem
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cache
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val i.n v)))))
          (@Eq.{1} Real
            (t.realMem
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cache
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val i.n v))))
            (s.realMem
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cache
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val i.n v)))))) →
      DecrAlmostLinearSSSP.Decremental.Native.CacheImage i j cache b t := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_7.1.2.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.Native.ScaleMemory.frame : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program}
  {B j record cache next : Nat} {g : DecrAlmostLinearSSSP.Decremental.Machine} {b : Fin i.n → ENNReal}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.ScaleMemory i p B j record cache next g b s →
    (∀ (r : Nat),
        @LT.lt.{0} Nat instLTNat r
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (DecrAlmostLinearSSSP.Decremental.registerBound p.code)
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) →
          And
            (@Eq.{1} Nat
              (t.natMem
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)))
              (s.natMem
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))))
            (@Eq.{1} Real
              (t.realMem
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)))
              (s.realMem
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))))) →
      (∀ (v : Nat),
          And
            (@Eq.{1} Nat (t.natMem (DecrAlmostLinearSSSP.Decremental.bankAddress B j v))
              (s.natMem (DecrAlmostLinearSSSP.Decremental.bankAddress B j v)))
            (@Eq.{1} Real (t.realMem (DecrAlmostLinearSSSP.Decremental.bankAddress B j v))
              (s.realMem (DecrAlmostLinearSSSP.Decremental.bankAddress B j v)))) →
        (∀ (v : Fin i.n),
            And
              (@Eq.{1} Nat
                (t.natMem
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cache
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val i.n v))))
                (s.natMem
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cache
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val i.n v)))))
              (@Eq.{1} Real
                (t.realMem
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cache
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val i.n v))))
                (s.realMem
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cache
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val i.n v)))))) →
          DecrAlmostLinearSSSP.Decremental.Native.ScaleMemory i p B j record cache next g b t := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_7.1.2.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.LinkedScan.eval_code : ∀ (rows : List.{0} DecrAlmostLinearSSSP.Decremental.LinkedScan.Row)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (vertex : Nat),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
      (DecrAlmostLinearSSSP.Decremental.LinkedScan.headAddress rows) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 38) (instOfNatNat (nat_lit 38)))) vertex →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 34) (instOfNatNat (nat_lit 34))))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 36) (instOfNatNat (nat_lit 36))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
          DecrAlmostLinearSSSP.Decremental.LinkedScan.RowsView s vertex rows →
            ∃ cost t,
              And
                (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.LinkedScan.code s
                  cost t)
                (And
                  (@LE.le.{0} Nat instLENat cost
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
                        (DecrAlmostLinearSSSP.Decremental.LinkedScan.skipped rows))
                      (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))))
                  (And
                    (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
                      (DecrAlmostLinearSSSP.Decremental.LinkedScan.selectedAddress rows))
                    (And
                      (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      (And (@Eq.{1} (Nat → Real) t.realMem s.realMem) (@Eq.{1} (Nat → Nat) t.natMem s.natMem))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_8.1.1.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.DirtyMark.eval_code : ∀ {n : Nat} (flagBase listBase : Nat) (xs : List.{0} (Fin n)) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data)
  (v : Fin n),
  @DecrAlmostLinearSSSP.Decremental.DirtyMark.View n flagBase listBase xs s →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 98) (instOfNatNat (nat_lit 98)))) flagBase →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94)))) (@Fin.val n v) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
            (∀ (u : Fin n),
                @LT.lt.{0} Nat instLTNat
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) flagBase
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val n u)))
                  listBase) →
              ∃ cost t ys,
                And
                  (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.DirtyMark.code s
                    cost t)
                  (And (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                    (And
                      (@Eq.{1} (List.{0} (Fin n)) ys
                        (@ite.{1} (List.{0} (Fin n))
                          (@Membership.mem.{0, 0} (Fin n) (List.{0} (Fin n)) (@List.instMembership.{0} (Fin n)) xs v)
                          (@List.instDecidableMemOfLawfulBEq.{0} (Fin n)
                            (@instBEqOfDecidableEq.{0} (Fin n) (instDecidableEqFin n))
                            (@Std.LawfulBEqOrd.lawfulBEq.{0} (Fin n)
                              (@instBEqOfDecidableEq.{0} (Fin n) (instDecidableEqFin n)) (instOrdFin n)
                              (@Std.LawfulBCmp.toLawfulBEqCmp.{0} (Fin n)
                                (@Preorder.toLE.{0} (Fin n)
                                  (@PartialOrder.toPreorder.{0} (Fin n)
                                    (@LinearOrder.toPartialOrder.{0} (Fin n) (@Fin.instLinearOrder n))))
                                (@Preorder.toLT.{0} (Fin n)
                                  (@PartialOrder.toPreorder.{0} (Fin n)
                                    (@LinearOrder.toPartialOrder.{0} (Fin n) (@Fin.instLinearOrder n))))
                                (@instBEqOfDecidableEq.{0} (Fin n) (instDecidableEqFin n))
                                (@Ord.compare.{0} (Fin n) (instOrdFin n))
                                (@instLawfulBCmpCompare_mathlib.{0} (Fin n) (@Fin.instLinearOrder n)))
                              (Fin.instLawfulEqOrd n))
                            v xs)
                          xs
                          (@HAppend.hAppend.{0, 0, 0} (List.{0} (Fin n)) (List.{0} (Fin n)) (List.{0} (Fin n))
                            (@instHAppendOfAppend.{0} (List.{0} (Fin n)) (@List.instAppend.{0} (Fin n))) xs
                            (@List.cons.{0} (Fin n) v (@List.nil.{0} (Fin n))))))
                      (And (@DecrAlmostLinearSSSP.Decremental.DirtyMark.View n flagBase listBase ys t)
                        (And (@LE.le.{0} Nat instLENat (@List.length.{0} (Fin n) ys) n)
                          (And (@Eq.{1} (Nat → Real) t.realMem s.realMem)
                            (∀ (address : Nat),
                              @Ne.{1} Nat address
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) flagBase
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val n v))) →
                                @Ne.{1} Nat address
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) listBase
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                        (@List.length.{0} (Fin n) xs))) →
                                  @Eq.{1} Nat (t.natMem address) (s.natMem address))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_8.2.1.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.Native.PublicFrame.trans : ∀ {l : DecrAlmostLinearSSSP.Decremental.Native.PointerLayout} {n : Nat}
  {s t u : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.PublicFrame l n s t →
    DecrAlmostLinearSSSP.Decremental.Native.PublicFrame l n t u →
      DecrAlmostLinearSSSP.Decremental.Native.PublicFrame l n s u := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_8.2.2.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.PointerBases.start : ∀ {record pointer flags list cost : Nat} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.PointerBases record pointer flags list s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Native.pointerStart s cost t →
      DecrAlmostLinearSSSP.Decremental.Native.PointerBases record pointer flags list t := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_9.1.1.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.PointerRead.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    ∃ cost t,
      And (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.PointerRead.code s cost t)
        (And (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
          (And
            (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))))
              (@ite.{1} Nat
                (@Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.PointerRead.pointer s)
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                (instDecidableEqNat (DecrAlmostLinearSSSP.Decremental.PointerRead.pointer s)
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (s.natMem (DecrAlmostLinearSSSP.Decremental.PointerRead.cellAddress s))))
            (And
              (@Eq.{1} Real (t.realReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))))
                (@ite.{1} Real
                  (@Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.PointerRead.pointer s)
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (instDecidableEqNat (DecrAlmostLinearSSSP.Decremental.PointerRead.pointer s)
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                  (s.realMem (DecrAlmostLinearSSSP.Decremental.PointerRead.cellAddress s))))
              (And (@Eq.{1} (Nat → Real) t.realMem s.realMem) (@Eq.{1} (Nat → Nat) t.natMem s.natMem))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_9.1.1.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.PointerRead.no_memory : DecrAlmostLinearSSSP.Decremental.Structured.NoMemory DecrAlmostLinearSSSP.Decremental.PointerRead.code := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_9.1.1.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.SelectedRead.no_memory : DecrAlmostLinearSSSP.Decremental.Structured.NoMemory DecrAlmostLinearSSSP.Decremental.SelectedRead.code := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_9.1.1.2.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.SelectedRead.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    ∃ cost t,
      And (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.SelectedRead.code s cost t)
        (And (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11))))
          (And
            (@Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.ExtendedMax.incoming t)
              (DecrAlmostLinearSSSP.Decremental.SelectedRead.value s))
            (And (@Eq.{1} (Nat → Real) t.realMem s.realMem) (@Eq.{1} (Nat → Nat) t.natMem s.natMem)))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_9.1.1.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.SelectedRead.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 38) (instOfNatNat (nat_lit 38))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 196) (instOfNatNat (nat_lit 196))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 44) (instOfNatNat (nat_lit 44))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) →
              DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.SelectedRead.code k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_9.1.2.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.AnswerTable.Image.frame : ∀ {n : Nat} {l : DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout n}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  @DecrAlmostLinearSSSP.Decremental.AnswerTable.Image n l s →
    (∀ (address : Nat),
        @DecrAlmostLinearSSSP.Decremental.AnswerTable.Protected n l address →
          And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
            (@Eq.{1} Real (t.realMem address) (s.realMem address))) →
      @DecrAlmostLinearSSSP.Decremental.AnswerTable.Image n l t := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_9.1.2.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.DirtyCommit.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 38) (instOfNatNat (nat_lit 38))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 196) (instOfNatNat (nat_lit 196))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 44) (instOfNatNat (nat_lit 44))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) →
              @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94))) →
                @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 184) (instOfNatNat (nat_lit 184))) →
                  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 192) (instOfNatNat (nat_lit 192))) →
                    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 194) (instOfNatNat (nat_lit 194))) →
                      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
                        DecrAlmostLinearSSSP.Decremental.DirtyCommit.body k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_9.1.2.2.1.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.DirtyCommit.eval_code : ∀ {n : Nat} (l : DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout n) (flagBase listBase : Nat),
  @LE.le.{0} Nat instLENat n flagBase →
    @LE.le.{0} Nat instLENat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) flagBase
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
        listBase →
      (∀ (address : Nat),
          @DecrAlmostLinearSSSP.Decremental.AnswerTable.Protected n l address →
            And (@LE.le.{0} Nat instLENat n address)
              (∀ (v : Fin n),
                @Ne.{1} Nat address
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) flagBase
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val n v))))) →
        ∀ (xs : List.{0} (Fin n)) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
          @DecrAlmostLinearSSSP.Decremental.DirtyMark.View n flagBase listBase xs s →
            @DecrAlmostLinearSSSP.Decremental.AnswerTable.Image n l s →
              @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 96) (instOfNatNat (nat_lit 96))))
                  (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.pointerBase n l) →
                @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72))))
                    (@Fin.val n (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.source n l)) →
                  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 98) (instOfNatNat (nat_lit 98)))) flagBase →
                    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 102) (instOfNatNat (nat_lit 102)))) listBase →
                      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                            (∀ v ∉ xs,
                                And
                                  (@Eq.{1} Nat (s.natMem (@Fin.val n v))
                                    (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.flag n l v))
                                  (@Eq.{1} Real (s.realMem (@Fin.val n v))
                                    (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.realValue n l v))) →
                              ∃ cost t,
                                And
                                  (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                    DecrAlmostLinearSSSP.Decremental.DirtyCommit.code s cost t)
                                  (And
                                    (@LE.le.{0} Nat instLENat cost
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))
                                          (@List.length.{0} (Fin n) xs))
                                        (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
                                    (And
                                      (@DecrAlmostLinearSSSP.Decremental.DirtyMark.View n flagBase listBase
                                        (@List.nil.{0} (Fin n)) t)
                                      (And (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Image n l t)
                                        (And
                                          (∀ (v : Fin n),
                                            And
                                              (@Eq.{1} Nat (t.natMem (@Fin.val n v))
                                                (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.flag n l v))
                                              (@Eq.{1} Real (t.realMem (@Fin.val n v))
                                                (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.realValue n l v)))
                                          (∀ (address : Nat),
                                            (∀ (v : Fin n),
                                                @Membership.mem.{0, 0} (Fin n) (List.{0} (Fin n))
                                                    (@List.instMembership.{0} (Fin n)) xs v →
                                                  And (@Ne.{1} Nat address (@Fin.val n v))
                                                    (@Ne.{1} Nat address
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        flagBase
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                          (@Fin.val n v))))) →
                                              And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                                (@Eq.{1} Real (t.realMem address) (s.realMem address))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_9.2.1.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.SelectedRead.real_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.SelectedRead.code k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_9.2.1.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Native.PublicControlFrame.seq : ∀ {a b : DecrAlmostLinearSSSP.Decremental.Structured.Cmd},
  DecrAlmostLinearSSSP.Decremental.Native.PublicControlFrame a →
    DecrAlmostLinearSSSP.Decremental.Native.PublicControlFrame b →
      DecrAlmostLinearSSSP.Decremental.Native.PublicControlFrame (a.seq b) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_10.1.1.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Native.NormalMemory.source : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program} {B reserve : Nat}
  {g : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → DecrAlmostLinearSSSP.Decremental.Machine}
  {b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal} {ptr : Fin i.n → Nat}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.NormalMemory i p B reserve g b ptr s →
    @Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.stored s.machine (@Fin.val i.n i.source))
      (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero)) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_10.1.1.2.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.subpolynomial_rescale : ∀ (a : Nat → Real),
  DecrAlmostLinearSSSP.Decremental.Subpolynomial a →
    ∀ (c : Nat),
      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) c →
        DecrAlmostLinearSSSP.Decremental.Subpolynomial fun m =>
          a (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) c m) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_10.1.1.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Native.CacheRefresh.eval_code : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (B j cache : Nat) (g : DecrAlmostLinearSSSP.Decremental.Machine) (b : Fin i.n → ENNReal) (v : Fin i.n)
      (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
      DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B j s g.natMem g.realMem →
        DecrAlmostLinearSSSP.Decremental.Native.CacheImage i j cache b s →
          (∀ (u : Fin i.n),
              And
                (@LE.le.{0} Nat instLENat (g.natMem (@Fin.val i.n u))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (@Eq.{1} Nat (g.natMem (@Fin.val i.n u)) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                  @LE.le.{0} Real Real.instLE
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                    (g.realMem (@Fin.val i.n u)))) →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
              @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94))))
                    (@Fin.val i.n v) →
                  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 198) (instOfNatNat (nat_lit 198))))
                      (DecrAlmostLinearSSSP.Decremental.bankAddress B j (@Fin.val i.n v)) →
                    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))))
                        (DecrAlmostLinearSSSP.Decremental.bankFactor j) →
                      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 108) (instOfNatNat (nat_lit 108)))) cache →
                        @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 70) (instOfNatNat (nat_lit 70))))
                            (DecrAlmostLinearSSSP.Decremental.delta i j) →
                          ∃ cost t,
                            And
                              (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                DecrAlmostLinearSSSP.Decremental.Native.CacheRefresh.code s cost t)
                              (And
                                (@LE.le.{0} Nat instLENat cost
                                  (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16))))
                                (And
                                  (DecrAlmostLinearSSSP.Decremental.Native.CacheImage i j cache
                                    (@Function.update.{1, 1} (Fin i.n) (fun a => ENNReal) (instDecidableEqFin i.n) b v
                                      (@Max.max.{0} ENNReal ENNReal.instMax (b v)
                                        (DecrAlmostLinearSSSP.Decremental.stored g (@Fin.val i.n v))))
                                    t)
                                  (∀ (address : Nat),
                                    @Ne.{1} Nat address
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cache
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                            (@Fin.val i.n v))) →
                                      And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                        (@Eq.{1} Real (t.realMem address) (s.realMem address))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_10.1.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.PointerRefresh.eval_code : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (recordBase cacheBase stride pointerBase : Nat)
  (b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal) (v : Fin i.n) (start : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Native.ScanTable i recordBase cacheBase stride b s →
    @LE.le.{0} Nat instLENat recordBase cacheBase →
      @LE.le.{0} Nat instLENat start (DecrAlmostLinearSSSP.Decremental.scaleCount i) →
        @Eq.{1} Nat
            (s.natMem
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pointerBase
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val i.n v))))
            (DecrAlmostLinearSSSP.Decremental.Native.scanRecord i recordBase stride start) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94)))) (@Fin.val i.n v) →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 96) (instOfNatNat (nat_lit 96)))) pointerBase →
              @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 34) (instOfNatNat (nat_lit 34))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 36) (instOfNatNat (nat_lit 36))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                  ∃ cost t,
                    And
                      (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                        DecrAlmostLinearSSSP.Decremental.Native.PointerRefresh.code s cost t)
                      (And
                        (@LE.le.{0} Nat instLENat cost
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
                              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                                (DecrAlmostLinearSSSP.Decremental.advance i b v
                                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                                    (DecrAlmostLinearSSSP.Decremental.scaleCount i) start)
                                  start)
                                start))
                            (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
                        (And
                          (@Eq.{1} (Nat → Nat) t.natMem
                            (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natMem
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pointerBase
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val i.n v)))
                              (DecrAlmostLinearSSSP.Decremental.Native.scanRecord i recordBase stride
                                (DecrAlmostLinearSSSP.Decremental.advance i b v
                                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                                    (DecrAlmostLinearSSSP.Decremental.scaleCount i) start)
                                  start))))
                          (@Eq.{1} (Nat → Real) t.realMem s.realMem))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_10.1.2.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.Native.PointerRefresh.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 38) (instOfNatNat (nat_lit 38))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 196) (instOfNatNat (nat_lit 196))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 42) (instOfNatNat (nat_lit 42))) →
              @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 44) (instOfNatNat (nat_lit 44))) →
                @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 46) (instOfNatNat (nat_lit 46))) →
                  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
                    DecrAlmostLinearSSSP.Decremental.Native.PointerRefresh.code k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_10.1.2.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.Native.PointerRefresh.real_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))) →
      DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Native.PointerRefresh.code
        k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_10.1.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.DirtyMark.View.frame : ∀ {n flags list : Nat} {xs : List.{0} (Fin n)} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  @DecrAlmostLinearSSSP.Decremental.DirtyMark.View n flags list xs s →
    (∀ (v : Fin n),
        @Eq.{1} Nat
          (t.natMem
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) flags
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val n v))))
          (s.natMem
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) flags
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val n v))))) →
      (∀ (j : Nat),
          @LT.lt.{0} Nat instLTNat j (@List.length.{0} (Fin n) xs) →
            @Eq.{1} Nat
              (t.natMem
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) list
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
              (s.natMem
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) list
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))) →
        @Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 182) (instOfNatNat (nat_lit 182))))
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 182) (instOfNatNat (nat_lit 182)))) →
          @Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 180) (instOfNatNat (nat_lit 180))))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 180) (instOfNatNat (nat_lit 180)))) →
            @DecrAlmostLinearSSSP.Decremental.DirtyMark.View n flags list xs t := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_10.1.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.AdapterMemory.frame : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B reserve N : Nat} {a : DecrAlmostLinearSSSP.Decremental.AdapterState i}
  {xs : List.{0} (Fin i.n)} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.AdapterMemory i B reserve N a xs s →
    @Eq.{1} (Nat → Nat) t.natMem s.natMem →
      @Eq.{1} (Nat → Real) t.realMem s.realMem →
        @Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 182) (instOfNatNat (nat_lit 182))))
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 182) (instOfNatNat (nat_lit 182)))) →
          @Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 180) (instOfNatNat (nat_lit 180))))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 180) (instOfNatNat (nat_lit 180)))) →
            DecrAlmostLinearSSSP.Decremental.Native.AdapterMemory i B reserve N a xs t := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_10.1.2.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Native.CacheRefresh.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 128) (instOfNatNat (nat_lit 128))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 132) (instOfNatNat (nat_lit 132))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 38) (instOfNatNat (nat_lit 38))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 130) (instOfNatNat (nat_lit 130))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) →
              @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 24) (instOfNatNat (nat_lit 24))) →
                DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
                  DecrAlmostLinearSSSP.Decremental.Native.CacheRefresh.code k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_10.2.1.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.Native.CacheRefresh.real_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) →
      DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Native.CacheRefresh.code k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_10.2.1.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Native.DirtyMark.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 186) (instOfNatNat (nat_lit 186))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 184) (instOfNatNat (nat_lit 184))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 188) (instOfNatNat (nat_lit 188))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 180) (instOfNatNat (nat_lit 180))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 182) (instOfNatNat (nat_lit 182))) →
            DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.DirtyMark.code k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_10.2.1.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.DirtyMark.real_frame : ∀ (k : Nat), DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.DirtyMark.code k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_10.2.1.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.ReportDecode.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (B bank a N : Nat),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))) B →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))))
        (DecrAlmostLinearSSSP.Decremental.bankFactor bank) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 198) (instOfNatNat (nat_lit 198))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
          @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
              @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast a)
                  (@HPow.hPow.{0, 0, 0} Real Nat Real
                    (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                    (@OfNat.ofNat.{0} Real (nat_lit 2)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                    N) →
                ∃ cost t,
                  And
                    (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.ReportDecode.code
                      s cost t)
                    (And (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94)))) a)
                      (And
                        (@LE.le.{0} Nat instLENat cost
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (DecrAlmostLinearSSSP.Decremental.dispatchCharge
                                  DecrAlmostLinearSSSP.Decremental.ScaledCeiling.ceilingProgram.code)
                                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16))) N)
                                (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))))
                            (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))))
                        (∀ (address : Nat),
                          (∀ (r : Nat),
                              @Ne.{1} Nat address
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 48) (instOfNatNat (nat_lit 48))))
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                            And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                              (@Eq.{1} Real (t.realMem address) (s.realMem address))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_10.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.ReportDecode.nat_frame : ∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.ReportDecode.code k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_10.2.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.ReportDecode.real_frame : ∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 202) (instOfNatNat (nat_lit 202))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 204) (instOfNatNat (nat_lit 204))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 206) (instOfNatNat (nat_lit 206))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
              DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.ReportDecode.code k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_10.2.2.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Native.ReportFrame.trans : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B reserve N j : Nat}
  {s t u : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.ReportFrame i B reserve N j s t →
    DecrAlmostLinearSSSP.Decremental.Native.ReportFrame i B reserve N j t u →
      DecrAlmostLinearSSSP.Decremental.Native.ReportFrame i B reserve N j s u := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_11.1.1.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.ReportFrame.source : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B reserve N j q : Nat}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.Native.ReportFrame i B reserve N j s t →
    DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B q s g.natMem g.realMem →
      DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B q t g.natMem g.realMem := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_11.1.2.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.Queue.head : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B reserve N offset address : Nat} {rest : List.{0} Nat}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.Queue i B reserve N offset (@List.cons.{0} Nat address rest) s →
    @Eq.{1} Nat (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 210) (instOfNatNat (nat_lit 210))))) address := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_11.2.1.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.eval_code : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (B reserve N : Nat),
      @LE.le.{0} Nat instLENat i.n B →
        ∀ (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (g : DecrAlmostLinearSSSP.Decremental.Machine)
          (reports : List.{0} Nat),
          (∀ (address : Nat),
              @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat) reports address →
                ∃ logical,
                  @Eq.{1} Nat address
                    (DecrAlmostLinearSSSP.Decremental.bankAddress B
                      (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) logical)) →
            (∀ (z : Fin i.n),
                And
                  (@LE.le.{0} Nat instLENat (g.natMem (@Fin.val i.n z))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@Eq.{1} Nat (g.natMem (@Fin.val i.n z))
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                    @LE.le.{0} Real Real.instLE
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                      (g.realMem (@Fin.val i.n z)))) →
              ∀ (a : DecrAlmostLinearSSSP.Decremental.AdapterState i) (xs : List.{0} (Fin i.n))
                (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
                DecrAlmostLinearSSSP.Decremental.Native.AdapterMemory i B reserve N a xs s →
                  DecrAlmostLinearSSSP.Decremental.Native.Globals i B
                      (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n
                          (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).utility
                      s →
                    (∀ (z : Fin i.n),
                        DecrAlmostLinearSSSP.Decremental.PointerValid i
                          (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i a) z
                          (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i a z)) →
                      DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B
                          (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) s g.natMem g.realMem →
                        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))))
                            (DecrAlmostLinearSSSP.Decremental.bankFactor
                              (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)) →
                          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 108) (instOfNatNat (nat_lit 108))))
                              (DecrAlmostLinearSSSP.Decremental.Native.cacheAt
                                (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                                    (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).cache
                                i.n (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)) →
                            @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 70) (instOfNatNat (nat_lit 70))))
                                (DecrAlmostLinearSSSP.Decremental.delta i
                                  (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)) →
                              @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 96) (instOfNatNat (nat_lit 96))))
                                  (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                                      (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).pointer →
                                @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 98) (instOfNatNat (nat_lit 98))))
                                    (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                                        (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).flags →
                                  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 92) (instOfNatNat (nat_lit 92))))
                                      (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n
                                          (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).reports →
                                    DecrAlmostLinearSSSP.Decremental.ReportLog
                                        (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n
                                            (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).reports
                                        reports s →
                                      @LE.le.{0} Nat instLENat (@List.length.{0} Nat reports) reserve →
                                        ∃ cost t ys,
                                          And
                                            (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                              DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.code s cost t)
                                            (And
                                              (@LE.le.{0} Nat instLENat cost
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat)
                                                            (DecrAlmostLinearSSSP.Decremental.dispatchCharge
                                                              DecrAlmostLinearSSSP.Decremental.ScaledCeiling.ceilingProgram.code)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 3)
                                                              (instOfNatNat (nat_lit 3))))
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat)
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 16)
                                                                (instOfNatNat (nat_lit 16)))
                                                              (DecrAlmostLinearSSSP.Decremental.utilityDepth i.size))
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 32)
                                                              (instOfNatNat (nat_lit 32)))))
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 61) (instOfNatNat (nat_lit 61))))
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@List.length.{0} Nat reports)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
                                                      (DecrAlmostLinearSSSP.Decremental.pointerTravel i a
                                                        (DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.allEvents
                                                          i B j g reports))))
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                              (And
                                                (DecrAlmostLinearSSSP.Decremental.Native.AdapterMemory i B reserve N
                                                  (DecrAlmostLinearSSSP.Decremental.adapterTrace i a
                                                    (DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.allEvents i B
                                                      j g reports))
                                                  ys t)
                                                (And
                                                  (@LE.le.{0} Nat instLENat (@List.length.{0} (Fin i.n) ys)
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@List.length.{0} (Fin i.n) xs) (@List.length.{0} Nat reports)))
                                                  (And
                                                    (DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.Environment i
                                                      B reserve N j g t)
                                                    (And
                                                      (@Eq.{1} Nat
                                                        (t.natReg
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 214)
                                                            (instOfNatNat (nat_lit 214))))
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                      (DecrAlmostLinearSSSP.Decremental.Native.ReportFrame i B reserve N
                                                        (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) s
                                                        t)))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_11.2.1.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Native.UpdateHeader.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Native.UpdateHeader.code s
    (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))
    (DecrAlmostLinearSSSP.Decremental.Native.UpdateHeader.result s) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_11.2.1.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.UpdateHeader.no_memory : DecrAlmostLinearSSSP.Decremental.Structured.NoMemory DecrAlmostLinearSSSP.Decremental.Native.UpdateHeader.code := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_11.2.1.2.1.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Native.UpdateHeader.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 54) (instOfNatNat (nat_lit 54))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 108) (instOfNatNat (nat_lit 108))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) →
              @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) →
                @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))) →
                  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
                    DecrAlmostLinearSSSP.Decremental.Native.UpdateHeader.code k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_11.2.1.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.Native.UpdateHeader.real_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 70) (instOfNatNat (nat_lit 70))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Native.UpdateHeader.code k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_11.2.1.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.Native.SavedDeletion.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (p : DecrAlmostLinearSSSP.Decremental.Program)
  (g : DecrAlmostLinearSSSP.Decremental.Machine) (F e N : Nat),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112)))) F →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 78) (instOfNatNat (nat_lit 78)))) e →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
        @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
          @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast e)
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                N) →
            (∀ (j : Nat),
                @LT.lt.{0} Nat instLTNat j (DecrAlmostLinearSSSP.Decremental.registerBound p.code) →
                  And
                    (@Eq.{1} Nat
                      (s.natMem
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F (g.natReg j)))
                    (@Eq.{1} Real
                      (s.realMem
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
                      (g.realReg j))) →
              (∀ (j : Nat),
                  @LT.lt.{0} Nat instLTNat j (DecrAlmostLinearSSSP.Decremental.registerBound p.code) →
                    @LT.lt.{0} Nat instLTNat
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j))
                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 48) (instOfNatNat (nat_lit 48))))) →
                ∃ cost t,
                  And
                    (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                      DecrAlmostLinearSSSP.Decremental.Native.SavedDeletion.code s cost t)
                    (And
                      (@LE.le.{0} Nat instLENat cost
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (DecrAlmostLinearSSSP.Decremental.dispatchCharge
                                DecrAlmostLinearSSSP.Decremental.ScaledCeiling.ceilingProgram.code)
                              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16))) N)
                              (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))))
                          (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                      (And
                        (∀ (j : Nat),
                          @LT.lt.{0} Nat instLTNat j (DecrAlmostLinearSSSP.Decremental.registerBound p.code) →
                            And
                              (@Eq.{1} Nat
                                (t.natMem
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
                                  ((DecrAlmostLinearSSSP.Decremental.deletionMachine p g e).natReg j)))
                              (@Eq.{1} Real
                                (t.realMem
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
                                ((DecrAlmostLinearSSSP.Decremental.deletionMachine p g e).realReg j)))
                        (∀ (address : Nat),
                          @Ne.{1} Nat address
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                                (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))) →
                            (∀ (a : Nat),
                                @Ne.{1} Nat address
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 48) (instOfNatNat (nat_lit 48))))
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                              And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                (@Eq.{1} Real (t.realMem address) (s.realMem address))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_11.2.1.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.SavedDeletion.nat_frame : ∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 208) (instOfNatNat (nat_lit 208))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 54) (instOfNatNat (nat_lit 54))) →
              DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
                DecrAlmostLinearSSSP.Decremental.Native.SavedDeletion.code k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_11.2.1.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Native.SavedDeletion.real_frame : ∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 200) (instOfNatNat (nat_lit 200))) →
          DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
            DecrAlmostLinearSSSP.Decremental.Native.SavedDeletion.code k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_11.2.2.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.ObservedSourceCall.eval_code : ∀ (N entry B bank start : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data)
  (p : DecrAlmostLinearSSSP.Decremental.Program) (g final : DecrAlmostLinearSSSP.Decremental.Machine),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))) B →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))))
        (DecrAlmostLinearSSSP.Decremental.bankFactor bank) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
        @Eq.{1} Nat g.pc entry →
          @Eq.{1} Nat
              (s.natMem
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
              g.work →
            @Eq.{1} Bool g.halted Bool.false →
              @Eq.{1} Bool g.fault Bool.false →
                (∀ (a : Nat),
                    @Eq.{1} Real
                      (s.realMem
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                      (g.realMem a)) →
                  (∀ (a : Nat),
                      @Eq.{1} Nat
                        (s.natMem
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (DecrAlmostLinearSSSP.Decremental.bankFactor bank) (g.natMem a))) →
                    (∀ (j : Nat),
                        @LT.lt.{0} Nat instLTNat j N →
                          And
                            (@Eq.{1} Nat
                              (s.natMem
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (DecrAlmostLinearSSSP.Decremental.bankFactor bank) (g.natReg j)))
                            (@Eq.{1} Real
                              (s.realMem
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
                              (g.realReg j))) →
                      (∀ (j : Nat),
                          @LE.le.{0} Nat instLENat N j →
                            And
                              (@Eq.{1} Nat (s.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg j))
                                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                              (@Eq.{1} Real (s.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg j))
                                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))) →
                        DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail N g →
                          DecrAlmostLinearSSSP.Decremental.Ends p g final →
                            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                              DecrAlmostLinearSSSP.Decremental.ReportLog start (@List.nil.{0} Nat) s →
                                (∃ r,
                                    @Eq.{1} Nat start
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                                  ∃ cost steps t,
                                    And
                                      (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                        (DecrAlmostLinearSSSP.Decremental.ObservedSourceCall.code N entry p) s cost t)
                                      (And
                                        (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                                          (DecrAlmostLinearSSSP.Decremental.execute p g steps) final)
                                        (And
                                          (@Eq.{1} Nat steps
                                            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) final.work
                                              g.work))
                                          (And
                                            (@LE.le.{0} Nat instLENat cost
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (DecrAlmostLinearSSSP.Decremental.observedDispatchCharge p.code)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                                                      final.work g.work))
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) N))
                                                (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))))
                                            (And
                                              (DecrAlmostLinearSSSP.Decremental.ShadowDataRep B
                                                (DecrAlmostLinearSSSP.Decremental.bankFactor bank) t final)
                                              (And
                                                (DecrAlmostLinearSSSP.Decremental.ReportLog start
                                                  (DecrAlmostLinearSSSP.Decremental.physicalTraceWrites B bank p g
                                                    steps)
                                                  t)
                                                (∀ (address : Nat),
                                                  (∀ (a : Nat),
                                                      @Ne.{1} Nat address
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          B
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                (@instHMul.{0} Nat instMulNat)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                  (instOfNatNat (nat_lit 2)))
                                                                a)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                (instOfNatNat (nat_lit 1))))))) →
                                                    (∀ (j : Nat),
                                                        @LE.le.{0} Nat instLENat j
                                                            (@HSub.hSub.{0, 0, 0} Nat Nat Nat
                                                              (@instHSub.{0} Nat instSubNat) final.work g.work) →
                                                          @Ne.{1} Nat address
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat) start
                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                (@instHMul.{0} Nat instMulNat)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                  (instOfNatNat (nat_lit 2)))
                                                                j))) →
                                                      And (@Eq.{1} Real (t.realMem address) (s.realMem address))
                                                        (@Eq.{1} Nat (t.natMem address) (s.natMem address)))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_11.2.2.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.Native.SourceUpdateFrame.trans : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B reserve N j : Nat}
  {s t u : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.SourceUpdateFrame i B reserve N j s t →
    DecrAlmostLinearSSSP.Decremental.Native.SourceUpdateFrame i B reserve N j t u →
      DecrAlmostLinearSSSP.Decremental.Native.SourceUpdateFrame i B reserve N j s u := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_12.1.1.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.Native.SourceUpdateFrame.host : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B reserve N j address : Nat}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.SourceUpdateFrame i B reserve N j s t →
    (∃ r,
        @Eq.{1} Nat address
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
      @LT.lt.{0} Nat instLTNat address
          (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i)
              reserve N).reports →
        @Ne.{1} Nat address
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (DecrAlmostLinearSSSP.Decremental.Native.sourceRecord i B reserve N j)
              (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))) →
          (∀ (r : Nat),
              @LT.lt.{0} Nat instLTNat r N →
                @Ne.{1} Nat address
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (DecrAlmostLinearSSSP.Decremental.Native.sourceRecord i B reserve N j)
                      (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))) →
            And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
              (@Eq.{1} Real (t.realMem address) (s.realMem address)) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_12.1.1.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.FamilyMemory.update : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program} {B reserve : Nat}
  {f : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → DecrAlmostLinearSSSP.Decremental.Machine}
  {a b : DecrAlmostLinearSSSP.Decremental.AdapterState i} {s u t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.FamilyMemory i p B reserve f a s →
    ∀ (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (final : DecrAlmostLinearSSSP.Decremental.Machine),
      DecrAlmostLinearSSSP.Decremental.Native.SourceUpdateFrame i B reserve
          (DecrAlmostLinearSSSP.Decremental.registerBound p.code)
          (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) s u →
        DecrAlmostLinearSSSP.Decremental.Native.ReportFrame i B reserve
            (DecrAlmostLinearSSSP.Decremental.registerBound p.code)
            (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) u t →
          (∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
              DecrAlmostLinearSSSP.Decremental.Native.CacheImage i
                (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q)
                (DecrAlmostLinearSSSP.Decremental.Native.cacheAt
                  (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n
                      (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve
                      (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).caches
                  i.n (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q))
                (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i b q) t) →
            DecrAlmostLinearSSSP.Decremental.Native.ScaleMemory i p B
                (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)
                (DecrAlmostLinearSSSP.Decremental.Native.sourceRecord i B reserve
                  (DecrAlmostLinearSSSP.Decremental.registerBound p.code)
                  (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j))
                (DecrAlmostLinearSSSP.Decremental.Native.cacheAt
                  (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n
                      (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve
                      (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).caches
                  i.n (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j))
                (DecrAlmostLinearSSSP.Decremental.Native.nextRecord
                  (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n
                      (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve
                      (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).records
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                      (DecrAlmostLinearSSSP.Decremental.registerBound p.code))
                    (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                  (DecrAlmostLinearSSSP.Decremental.scaleCount i)
                  (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j))
                final (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i b j) t →
              DecrAlmostLinearSSSP.Decremental.Native.FamilyMemory i p B reserve
                (@Function.update.{1, 1} (Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i))
                  (fun a => DecrAlmostLinearSSSP.Decremental.Machine)
                  (instDecidableEqFin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) f j final)
                b t := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_12.2.1.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.Normalize.oldEdge_injective : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  @Function.Injective.{1, 1} (Fin i.k) (Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n))
    (DecrAlmostLinearSSSP.Decremental.Normalize.oldEdge i) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_1.1.1.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Normalize.active_live : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (ds : List.{0} (Fin i.k)),
  @Eq.{1} (Finset.{0} (Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n)))
    (DecrAlmostLinearSSSP.Decremental.Normalize.active i (@DecrAlmostLinearSSSP.Decremental.live i.k ds))
    (@DecrAlmostLinearSSSP.Decremental.live (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n)
      (@List.map.{0, 0} (Fin i.k) (Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n))
        (DecrAlmostLinearSSSP.Decremental.Normalize.oldEdge i) ds)) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_1.1.1.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.Normalize.sanitize_correct : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (a : Finset.{0} (Fin i.k)) (v : Fin i.n) (D : ENNReal),
      @LE.le.{0} ENNReal ENNReal.instLE
          (@DecrAlmostLinearSSSP.Decremental.distance (DecrAlmostLinearSSSP.Decremental.Normalize.input i).n
            (DecrAlmostLinearSSSP.Decremental.Normalize.input i).k
            (DecrAlmostLinearSSSP.Decremental.Normalize.input i).graph
            (DecrAlmostLinearSSSP.Decremental.Normalize.active i a)
            (fun e =>
              @Nat.cast.{0} ENNReal
                (@AddMonoidWithOne.toNatCast.{0} ENNReal
                  (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                (DecrAlmostLinearSSSP.Decremental.Normalize.weight i e))
            (DecrAlmostLinearSSSP.Decremental.Normalize.source i)
            (DecrAlmostLinearSSSP.Decremental.Normalize.oldVertex i v))
          D →
        @LE.le.{0} ENNReal ENNReal.instLE D
            (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
              (@instHMul.{0} ENNReal
                (@Distrib.toMul.{0} ENNReal
                  (@instDistribOfSemiring.{0} ENNReal (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
              (ENNReal.ofReal
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) i.accuracy))
              (@DecrAlmostLinearSSSP.Decremental.distance (DecrAlmostLinearSSSP.Decremental.Normalize.input i).n
                (DecrAlmostLinearSSSP.Decremental.Normalize.input i).k
                (DecrAlmostLinearSSSP.Decremental.Normalize.input i).graph
                (DecrAlmostLinearSSSP.Decremental.Normalize.active i a)
                (fun e =>
                  @Nat.cast.{0} ENNReal
                    (@AddMonoidWithOne.toNatCast.{0} ENNReal
                      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                    (DecrAlmostLinearSSSP.Decremental.Normalize.weight i e))
                (DecrAlmostLinearSSSP.Decremental.Normalize.source i)
                (DecrAlmostLinearSSSP.Decremental.Normalize.oldVertex i v))) →
          And
            (@LE.le.{0} ENNReal ENNReal.instLE
              (@DecrAlmostLinearSSSP.Decremental.distance i.n i.k i.graph a
                (fun e =>
                  @Nat.cast.{0} ENNReal
                    (@AddMonoidWithOne.toNatCast.{0} ENNReal
                      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                    (i.weight e))
                i.source v)
              (DecrAlmostLinearSSSP.Decremental.Normalize.sanitize i D))
            (And
              (@LE.le.{0} ENNReal ENNReal.instLE (DecrAlmostLinearSSSP.Decremental.Normalize.sanitize i D)
                (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                  (@instHMul.{0} ENNReal
                    (@Distrib.toMul.{0} ENNReal
                      (@instDistribOfSemiring.{0} ENNReal
                        (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                  (ENNReal.ofReal
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) i.accuracy))
                  (@DecrAlmostLinearSSSP.Decremental.distance i.n i.k i.graph a
                    (fun e =>
                      @Nat.cast.{0} ENNReal
                        (@AddMonoidWithOne.toNatCast.{0} ENNReal
                          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                        (i.weight e))
                    i.source v)))
              (Iff
                (@Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.Normalize.sanitize i D)
                  (@Top.top.{0} ENNReal ENNReal.instTop))
                (Not (@DecrAlmostLinearSSSP.Decremental.Reachable i.n i.k i.graph a i.source v)))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_1.1.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Instrumented.interpreter_ends : ∀ {action : DecrAlmostLinearSSSP.Decremental.Instruction → DecrAlmostLinearSSSP.Decremental.Structured.Cmd}
  {bound : DecrAlmostLinearSSSP.Decremental.Instruction → Nat}
  {P : DecrAlmostLinearSSSP.Decremental.Structured.Data → DecrAlmostLinearSSSP.Decremental.Machine → Prop} {B F : Nat},
  DecrAlmostLinearSSSP.Decremental.Instrumented.ActionSpec action bound P B F →
    ∀ (guest : DecrAlmostLinearSSSP.Decremental.Program) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data)
      (g final : DecrAlmostLinearSSSP.Decremental.Machine),
      DecrAlmostLinearSSSP.Decremental.Instrumented.MachineRep B F s g →
        P s g →
          DecrAlmostLinearSSSP.Decremental.Ends guest g final →
            ∃ cost u,
              And
                (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                  (DecrAlmostLinearSSSP.Decremental.Instrumented.interpreter action guest.code) s cost u)
                (And
                  (@LE.le.{0} Nat instLENat cost
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (DecrAlmostLinearSSSP.Decremental.Instrumented.charge bound guest.code)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) final.work g.work))
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (And (DecrAlmostLinearSSSP.Decremental.Instrumented.MachineRep B F u final) (P u final))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_1.1.2.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.inner_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Normalize.Native.inner s
    (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))
    (DecrAlmostLinearSSSP.Decremental.Normalize.Native.committed s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_1.1.2.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.committed_memory : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
    And
      (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.Normalize.Native.committed s).natMem
        (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natMem
          (s.natMem
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@ite.{1} Nat
            (Or
              (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))))
              (@LT.lt.{0} Real Real.instLT (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
                (s.realMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))
            (@instDecidableOr
              (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))))
              (@LT.lt.{0} Real Real.instLT (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
                (s.realMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))))
              (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))))
              ((s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26)))).decidableLT
                (s.realMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.Normalize.Native.committed s).realMem
        (@Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realMem
          (s.natMem
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (s.realMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_1.1.2.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.callback_nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
            DecrAlmostLinearSSSP.Decremental.Normalize.Native.callback k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_1.1.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.callback_real_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Normalize.Native.callback k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_1.1.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.inner_nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Normalize.Native.inner k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_1.1.2.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.inner_real_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Normalize.Native.inner k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_1.2.1.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.inner_shadow : ∀ {B : Nat} (n : Nat),
  @LE.le.{0} Nat instLENat n B →
    ∀ {s : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
      DecrAlmostLinearSSSP.Decremental.ShadowDataRep B (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) s
          g →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
          @LT.lt.{0} Nat instLTNat
              (s.natMem
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              n →
            DecrAlmostLinearSSSP.Decremental.ShadowDataRep B
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (DecrAlmostLinearSSSP.Decremental.Normalize.Native.committed s) g := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_1.2.1.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.Image.header : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B : Nat} {bad : Option.{0} Nat}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.Normalize.Native.Image i B bad s g →
    DecrAlmostLinearSSSP.Decremental.Normalize.Native.Image i B bad
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
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) } := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_1.2.1.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.Image.scratch : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B : Nat} {bad : Option.{0} Nat}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.Normalize.Native.Image i B bad s g →
    ∀ (x : Nat),
      DecrAlmostLinearSSSP.Decremental.Normalize.Native.Image i B bad
        { realReg := s.realReg,
          natReg :=
            @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) x,
          realMem := s.realMem, natMem := s.natMem }
        g := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_1.2.1.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.Image.remove_bad : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B : Nat} {bad : Option.{0} Nat}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.Normalize.Native.Image i B bad s g →
    (∀ (v : Fin i.n), @Ne.{1} (Option.{0} Nat) bad (@Option.some.{0} Nat (@Fin.val i.n v))) →
      DecrAlmostLinearSSSP.Decremental.Normalize.Native.Image i B (@Option.none.{0} Nat) s g := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_1.2.1.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.Image.normal : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.Normalize.Native.Image i B (@Option.none.{0} Nat) s g →
    (∀ (v : Fin i.n),
        And
          (@LE.le.{0} Nat instLENat (g.natMem (@Fin.val i.n v))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@Eq.{1} Nat (g.natMem (@Fin.val i.n v)) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
            @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              (g.realMem (@Fin.val i.n v)))) →
      ∀ (v : Fin i.n),
        And
          (@LE.le.{0} Nat instLENat (s.natMem (@Fin.val i.n v))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@Eq.{1} Nat (s.natMem (@Fin.val i.n v)) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
            @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              (s.realMem (@Fin.val i.n v))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_1.2.1.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.Image.stored : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.Normalize.Native.Image i B (@Option.none.{0} Nat) s g →
    ∀ (v : Fin i.n),
      @LE.le.{0} Nat instLENat (g.natMem (@Fin.val i.n v))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
        @Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.stored s.machine (@Fin.val i.n v))
          (DecrAlmostLinearSSSP.Decremental.Normalize.sanitize i
            (DecrAlmostLinearSSSP.Decremental.stored g (@Fin.val i.n v))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_1.2.1.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.weightCode_eval : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i s →
    ∃ t,
      And
        (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Normalize.Native.weightCode s
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
          t)
        (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 78) (instOfNatNat (nat_lit 78))))
          (DecrAlmostLinearSSSP.Decremental.Normalize.sentinel i)) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_1.2.1.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.headerCode_eval : ∀ (entry : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Normalize.Native.headerCode entry)
    s (@OfNat.ofNat.{0} Nat (nat_lit 24) (instOfNatNat (nat_lit 24)))
    (DecrAlmostLinearSSSP.Decremental.Normalize.Native.headerData entry s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_1.2.1.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.weightCode_no_memory : DecrAlmostLinearSSSP.Decremental.Structured.NoMemory DecrAlmostLinearSSSP.Decremental.Normalize.Native.weightCode := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_1.2.1.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.weightCode_nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 76) (instOfNatNat (nat_lit 76))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 78) (instOfNatNat (nat_lit 78))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
            DecrAlmostLinearSSSP.Decremental.Normalize.Native.weightCode k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_1.2.1.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.weightCode_real_frame : ∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Normalize.Native.weightCode k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_1.2.1.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.weightCode_captured : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {cost : Nat},
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Normalize.Native.weightCode s cost
        t →
      DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i t := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_1.2.1.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.weightCode_vertices : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {cost : Nat},
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Normalize.Native.weightCode s cost
        t →
      @Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 76) (instOfNatNat (nat_lit 76))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_1.2.1.2.1.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.headerCode_no_memory : ∀ (entry : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.NoMemory
    (DecrAlmostLinearSSSP.Decremental.Normalize.Native.headerCode entry) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_1.2.1.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.headerCode_nat_frame : ∀ (entry k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18))) k →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
      (DecrAlmostLinearSSSP.Decremental.Normalize.Native.headerCode entry) k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_1.2.1.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.headerCode_real_frame : ∀ (entry k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 28) (instOfNatNat (nat_lit 28))) →
          DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
            (DecrAlmostLinearSSSP.Decremental.Normalize.Native.headerCode entry) k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_1.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.field_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Normalize.Native.fieldCode s
    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
    (DecrAlmostLinearSSSP.Decremental.Normalize.Native.fieldData s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_1.2.1.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.field_pointers : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 88) (instOfNatNat (nat_lit 88))))
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
      And
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.Normalize.Native.fieldData s).natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.Normalize.Native.fieldData s).natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))))
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_1.2.2.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.field_nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 84) (instOfNatNat (nat_lit 84))) →
        DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Normalize.Native.fieldCode
          k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_1.2.2.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.field_real_frame : ∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Normalize.Native.fieldCode k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_1.2.2.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.head_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  ∃ cost,
    And
      (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Normalize.Native.headCode s
        cost (DecrAlmostLinearSSSP.Decremental.Normalize.Native.headData s))
      (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_1.2.2.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.head_pointers : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 88) (instOfNatNat (nat_lit 88))))
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
      And
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.Normalize.Native.headData s).natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.Normalize.Native.headData s).natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))))
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_1.2.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.head_nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 84) (instOfNatNat (nat_lit 84))) →
        DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Normalize.Native.headCode
          k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_1.2.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.head_real_frame : ∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Normalize.Native.headCode k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_1.2.2.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.field_image : ∀ (B logical : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (natural : Nat → Nat) (real : Nat → Real),
  DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) s
      natural real →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))))
        (DecrAlmostLinearSSSP.Decremental.bankAddress B (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          logical) →
      DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (DecrAlmostLinearSSSP.Decremental.Normalize.Native.fieldData s)
        (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat natural logical
          (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))))
        real := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_1.2.2.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.head_image : ∀ (B logical : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (natural : Nat → Nat) (real : Nat → Real),
  DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) s
      natural real →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))))
        (DecrAlmostLinearSSSP.Decremental.bankAddress B (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          logical) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
        DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (DecrAlmostLinearSSSP.Decremental.Normalize.Native.headData s)
          (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat natural logical
            (@ite.{1} Nat
              (@Eq.{1} Nat (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80)))))
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72)))))
              (instDecidableEqNat (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80)))))
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72)))))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 66) (instOfNatNat (nat_lit 66))))
              (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80)))))))
          real := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_1.2.2.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.field_prefix : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (B : Nat),
  @LE.le.{0} Nat instLENat B (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82)))) →
    ∀ (a : Nat),
      @LT.lt.{0} Nat instLTNat a B →
        And (@Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.Normalize.Native.fieldData s).natMem a) (s.natMem a))
          (@Eq.{1} Real ((DecrAlmostLinearSSSP.Decremental.Normalize.Native.fieldData s).realMem a) (s.realMem a)) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_1.2.2.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.head_prefix : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (B : Nat),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @LE.le.{0} Nat instLENat B (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82)))) →
      ∀ (a : Nat),
        @LT.lt.{0} Nat instLTNat a B →
          And (@Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.Normalize.Native.headData s).natMem a) (s.natMem a))
            (@Eq.{1} Real ((DecrAlmostLinearSSSP.Decremental.Normalize.Native.headData s).realMem a) (s.realMem a)) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_1.2.2.2.1.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.record_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  ∃ cost,
    And
      (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Normalize.Native.recordCode s
        cost (DecrAlmostLinearSSSP.Decremental.Normalize.Native.recordData s))
      (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 21) (instOfNatNat (nat_lit 21)))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_1.2.2.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.record_nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 84) (instOfNatNat (nat_lit 84))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 90) (instOfNatNat (nat_lit 90))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
            DecrAlmostLinearSSSP.Decremental.Normalize.Native.recordCode k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_1.2.2.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.record_real_frame : ∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Normalize.Native.recordCode k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_1.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.record_pointers : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 88) (instOfNatNat (nat_lit 88))))
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
      And
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.Normalize.Native.recordData s).natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (And
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.Normalize.Native.recordData s).natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))))
              (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))))
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.Normalize.Native.recordData s).natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 90) (instOfNatNat (nat_lit 90))))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 90) (instOfNatNat (nat_lit 90))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_1.2.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.record_captured : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i s →
    DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i
      (DecrAlmostLinearSSSP.Decremental.Normalize.Native.recordData s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_1.2.2.2.2.2.2.2
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
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end s36
section s37
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end s37
section s38
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental.Structured
end s38
section s39
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s39
section s40
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s40
section s41
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s41
section s42
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s42
section s43
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s43
section s44
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s44
section s45
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Normalize
end DecrAlmostLinearSSSP.Decremental.Normalize
end s45
section s46
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize
end DecrAlmostLinearSSSP.Decremental.Normalize
end s46
section s47
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Normalize
end DecrAlmostLinearSSSP.Decremental.Normalize
end s47
section s48
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s48
section s49
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Normalize
end DecrAlmostLinearSSSP.Decremental.Normalize
end s49
section s50
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Normalize
end DecrAlmostLinearSSSP.Decremental.Normalize
end s50
section s51
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Normalize
end DecrAlmostLinearSSSP.Decremental.Normalize
end s51
section s52
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end s52
section s53
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end s53
section s54
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end s54
section s55
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end s55
section s56
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end s56
section s57
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end s57
section s58
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Instrumented
open Structured
end DecrAlmostLinearSSSP.Decremental.Instrumented
end s58
section s59
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Instrumented
open Structured
end DecrAlmostLinearSSSP.Decremental.Instrumented
end s59
section s60
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s60
section s61
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end s61
section s62
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end s62
section s63
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end s63
section s64
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s64
section s65
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s65
section s66
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s66
section s67
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.InputCapture
open Structured
end DecrAlmostLinearSSSP.Decremental.InputCapture
end s67
section s68
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s68
section s69
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s69
section s70
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s70
section s71
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.ScaledCeiling
open Structured
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental.ScaledCeiling
end s71
section s72
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.ScaledCeiling
open Structured
end DecrAlmostLinearSSSP.Decremental.ScaledCeiling
end s72
section s73
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.ScaledCeiling
open Structured
end DecrAlmostLinearSSSP.Decremental.ScaledCeiling
end s73
section s74
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.ScaledCeiling
open Structured
end DecrAlmostLinearSSSP.Decremental.ScaledCeiling
end s74
section s75
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s75
section s76
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s76
section s77
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s77
section s78
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s78
section s79
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s79
section s80
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s80
section s81
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental
end s81
section s82
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s82
section s83
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s83
section s84
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s84
section s85
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s85
section s86
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s86
section s87
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental
end s87
section s88
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s88
section s89
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s89
section s90
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental
end s90
section s91
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental
end s91
section s92
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s92
section s93
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s93
section s94
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s94
section s95
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s95
section s96
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s96
section s97
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.ScaledCeiling
open Structured
end DecrAlmostLinearSSSP.Decremental.ScaledCeiling
end s97
section s98
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end s98
section s99
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end s99
section s100
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.ScaledCeiling
open Structured
end DecrAlmostLinearSSSP.Decremental.ScaledCeiling
end s100
section s101
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.ScaledCeiling
open Structured
end DecrAlmostLinearSSSP.Decremental.ScaledCeiling
end s101
section s102
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.ScaledCeiling
open Structured
end DecrAlmostLinearSSSP.Decremental.ScaledCeiling
end s102
section s103
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.ScaledCeiling
open Structured
end DecrAlmostLinearSSSP.Decremental.ScaledCeiling
end s103
section s104
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.TapeCopy
open Structured
end DecrAlmostLinearSSSP.Decremental.TapeCopy
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
namespace DecrAlmostLinearSSSP.Decremental.SourceMemory
open Structured
end DecrAlmostLinearSSSP.Decremental.SourceMemory
end s107
section s108
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.SourceMemory
open Structured
end DecrAlmostLinearSSSP.Decremental.SourceMemory
end s108
section s109
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s109
section s110
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s110
section s111
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
lemma record_prefix (s : Data) (B : ℕ) (h1 : s.natReg 26 = 1) (h4 : s.natReg 88 = 4)
    (hB : B ≤ s.natReg 82) (a : ℕ) (ha : a < B) :
    (recordData s).natMem a = s.natMem a ∧ (recordData s).realMem a = s.realMem a := by
  have f26 (t : Data) : (fieldData t).natReg 26 = t.natReg 26 := (field_eval t).nat_frame (field_nat_frame 26 (by decide) (by decide) (by decide))
  have f88 (t : Data) : (fieldData t).natReg 88 = t.natReg 88 := (field_eval t).nat_frame (field_nat_frame 88 (by decide) (by decide) (by decide))
  have hp1 := field_pointers s h1 h4
  have hp2 := head_pointers (fieldData s) (by rw [f26,h1]) (by rw [f88,h4])
  have hz : (fieldData s).natReg 56 = s.natReg 56 := (field_eval s).nat_frame (field_nat_frame 56 (by decide) (by decide) (by decide))
  obtain ⟨c,hc,_⟩ := head_eval (fieldData s)
  have hheadMem : (headData (fieldData s)).natMem a = (fieldData s).natMem a ∧
      (headData (fieldData s)).realMem a = (fieldData s).realMem a := by
    unfold headData redirected headLoaded
    split_ifs <;> simp [headSuffixAtoms,Atom.effect,instructionEffect,data,Data.machine,
      Function.update_of_ne (show a ≠ (fieldData s).natReg 82 by omega)]
  have hfield1 := field_prefix s B hB a ha
  have hfield2 := field_prefix (headData (fieldData s)) B (by omega) a ha
  exact ⟨hfield2.1.trans (hheadMem.1.trans hfield1.1),hfield2.2.trans (hheadMem.2.trans hfield1.2)⟩
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s111
section s112
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
lemma field_captured {i : Input} {s : Data} (h : InputCapture.Captured i s) : InputCapture.Captured i (fieldData s) :=
  h.frame (fun k hk => (field_eval s).nat_frame (field_nat_frame k (by omega) (by omega) (by omega)))
    (fun k _ => (field_eval s).real_frame (field_real_frame k))
lemma head_captured {i : Input} {s : Data} (h : InputCapture.Captured i s) : InputCapture.Captured i (headData s) := by
  obtain ⟨c,he,_⟩ := head_eval s
  exact h.frame (fun k hk => he.nat_frame (head_nat_frame k (by omega) (by omega) (by omega)))
    (fun k _ => he.real_frame (head_real_frame k))
lemma record_image (i : Input) (B logical a0 a1 a2 : ℕ) (s : Data) (natural : ℕ → ℕ) (real : ℕ → ℝ)
    (h : SourceMemory.Image B 0 s natural real) (hcap : InputCapture.Captured i s)
    (hdest : s.natReg 82 = bankAddress B 0 logical) (hstride : s.natReg 88 = 4)
    (hsrc : s.natReg 80+3 ≤ B)
    (h0 : s.natMem (s.natReg 80) = a0) (h1 : s.natMem (s.natReg 80+1) = a1)
    (h2 : s.natMem (s.natReg 80+2) = a2) :
    SourceMemory.Image B 0 (recordData s)
      (Function.update (Function.update (Function.update natural logical a0)
        (logical+1) (if a1 = i.source.val then i.n else a1)) (logical+2) a2) real := by
  let u := fieldData s
  let v := headData u
  let w := fieldData v
  have huCap : InputCapture.Captured i u := field_captured hcap
  have hvCap : InputCapture.Captured i v := head_captured huCap
  have huStride : u.natReg 88 = 4 := (field_eval s).nat_frame (field_nat_frame 88 (by decide) (by decide) (by decide)) |>.trans hstride
  obtain ⟨ch,heHead,_⟩ := head_eval u
  have hvStride : v.natReg 88 = 4 := (heHead.nat_frame (head_nat_frame 88 (by decide) (by decide) (by decide))).trans huStride
  have hpU := field_pointers s hcap.unit hstride
  have hpV := head_pointers u huCap.unit huStride
  have hB : B ≤ s.natReg 82 := by rw [hdest];dsimp [bankAddress,bankFactor];omega
  have huDest : u.natReg 82 = bankAddress B 0 (logical+1) := by
    rw [hpU.2,hdest]
    dsimp [bankAddress,bankFactor]
    omega
  have hvDest : v.natReg 82 = bankAddress B 0 (logical+2) := by
    rw [hpV.2,huDest]
    dsimp [bankAddress,bankFactor]
    omega
  have huRead : u.natMem (u.natReg 80) = a1 := by
    rw [hpU.1]
    exact (field_prefix s B hB (s.natReg 80+1) (by omega)).1.trans h1
  have hvRead : v.natMem (v.natReg 80) = a2 := by
    rw [hpV.1,hpU.1]
    have ha : s.natReg 80+1+1 = s.natReg 80+2 := by omega
    rw [ha]
    have hbu : B ≤ u.natReg 82 := by rw [hpU.2];omega
    have hh := (head_prefix u B huCap.zeroN hbu (s.natReg 80+2) (by omega)).1
    have hf := (field_prefix s B hB (s.natReg 80+2) (by omega)).1
    exact hh.trans (hf.trans h2)
  have huImage := field_image B logical s natural real h hdest
  rw [h0] at huImage
  have hvImage := head_image B (logical+1) u _ real huImage huDest huCap.zeroN
  rw [huRead,huCap.source,huCap.vertices] at hvImage
  have hwImage := field_image B (logical+2) v _ real hvImage hvDest
  rw [hvRead] at hwImage
  exact ⟨hwImage.natMem,hwImage.realMem⟩
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s112
section s113
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s113
section s114
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize
lemma natPrefix_step_three (f : ℕ → ℕ) (bound : ℕ) :
    Function.update (Function.update (Function.update (natPrefix f bound) bound (f bound))
      (bound+1) (f (bound+1))) (bound+2) (f (bound+2)) = natPrefix f (bound+3) := by
  funext a
  by_cases h0 : a = bound
  · subst a;simp [natPrefix]
  · by_cases h1 : a = bound+1
    · subst a;simp [natPrefix]
    · by_cases h2 : a = bound+2
      · subst a;simp [natPrefix]
      · simp only [Function.update_of_ne h0,Function.update_of_ne h1,Function.update_of_ne h2,natPrefix]
        have hh : (a < bound) ↔ a < bound+3 := by omega
        simp only [hh]
end DecrAlmostLinearSSSP.Decremental.Normalize
end s114
section s115
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize
lemma initial_old_tail (i : Input) (p : Program) (e : Fin i.k) :
    (initialMachine p (input i)).natMem (i.n+1+3*e.val) = (i.graph.tail e).val := by
  have hh := initial_nat_tape p (input i) (oldEdge i e) 0 (by omega)
  simpa [input,oldEdge,addedEdge,tail,head,weight,oldVertex,sink,source,target,Fin.ext_iff] using hh
lemma initial_old_head (i : Input) (p : Program) (e : Fin i.k) :
    (initialMachine p (input i)).natMem (i.n+1+3*e.val+1) =
      if (i.graph.head e).val = i.source.val then i.n else (i.graph.head e).val := by
  have hh := initial_nat_tape p (input i) (oldEdge i e) 1 (by omega)
  by_cases he : (i.graph.head e).val = i.source.val <;>
    simpa [input,oldEdge,addedEdge,tail,head,weight,oldVertex,sink,source,target,Fin.ext_iff,he] using hh
lemma initial_old_weight (i : Input) (p : Program) (e : Fin i.k) :
    (initialMachine p (input i)).natMem (i.n+1+3*e.val+2) = i.weight e := by
  have hh := initial_nat_tape p (input i) (oldEdge i e) 2 (by omega)
  simpa [input,oldEdge,addedEdge,tail,head,weight,oldVertex,sink,source,target,Fin.ext_iff] using hh
lemma initial_added_tail (i : Input) (p : Program) (v : Fin i.n) :
    (initialMachine p (input i)).natMem (i.n+1+3*(i.k+v.val)) = i.source.val := by
  have hh := initial_nat_tape p (input i) (addedEdge i v) 0 (by omega)
  simpa [input,oldEdge,addedEdge,tail,head,weight,oldVertex,sink,source,target,Fin.ext_iff] using hh
lemma initial_added_head (i : Input) (p : Program) (v : Fin i.n) :
    (initialMachine p (input i)).natMem (i.n+1+3*(i.k+v.val)+1) =
      if v.val < i.source.val then v.val else v.val+1 := by
  have hh := initial_nat_tape p (input i) (addedEdge i v) 1 (by omega)
  simpa [input,oldEdge,addedEdge,tail,head,weight,oldVertex,sink,source,target,Fin.ext_iff] using hh
lemma initial_added_weight (i : Input) (p : Program) (v : Fin i.n) :
    (initialMachine p (input i)).natMem (i.n+1+3*(i.k+v.val)+2) = sentinel i := by
  have hh := initial_nat_tape p (input i) (addedEdge i v) 2 (by omega)
  simpa [input,oldEdge,addedEdge,tail,head,weight,oldVertex,sink,source,target,Fin.ext_iff] using hh
lemma initial_prefix_zero (i : Input) (p : Program) : natPrefix (initialMachine p (input i)).natMem (i.n+1) = fun _ => 0 := by
  funext a
  by_cases ha : a < i.n+1
  · have hn : ¬(input i).n ≤ a := by simpa only [input] using not_le.mpr ha
    simp only [natPrefix,if_pos ha,initialMachine,dif_neg (show ¬((input i).n ≤ a ∧ (a-(input i).n)/3 < (input i).k) by tauto)]
  · simp only [natPrefix,if_neg ha]
lemma initial_prefix_full (i : Input) (p : Program) :
    natPrefix (initialMachine p (input i)).natMem (i.n+1+3*(i.k+i.n)) = (initialMachine p (input i)).natMem := by
  funext a
  by_cases ha : a < i.n+1+3*(i.k+i.n)
  · simp only [natPrefix,if_pos ha]
  · simp only [natPrefix,if_neg ha]
    exact (initial_nat_above_tape p (input i) a (by dsimp [input];omega)).symm
end DecrAlmostLinearSSSP.Decremental.Normalize
end s115
section s116
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
lemma CopyInvariant.step {i : Input} {p : Program} {B : ℕ} {s : Data}
    (h : CopyInvariant i p B s) (hc : s.natReg 90 < i.k) : CopyInvariant i p B (recordData s) := by
  let e : Fin i.k := ⟨s.natReg 90,hc⟩
  have hsourceRoom : s.natReg 80+3 ≤ B := by rw [h.source];have he := e.isLt;have hb := h.base_room;omega
  have ht0 : s.natMem (s.natReg 80) = (i.graph.tail e).val := by
    rw [h.source,h.raw _ (by have hb := h.base_room;omega)]
    simpa [e] using initial_nat_tape p i e 0 (by omega)
  have ht1 : s.natMem (s.natReg 80+1) = (i.graph.head e).val := by
    rw [h.source,h.raw _ (by have hb := h.base_room;omega)]
    simpa [e] using initial_nat_tape p i e 1 (by omega)
  have ht2 : s.natMem (s.natReg 80+2) = i.weight e := by
    rw [h.source,h.raw _ (by have hb := h.base_room;omega)]
    simpa [e] using initial_nat_tape p i e 2 (by omega)
  have himg := record_image i B (i.n+1+3*s.natReg 90) _ _ _ s _ _ h.image h.captured h.dest h.stride hsourceRoom ht0 ht1 ht2
  let f := (initialMachine p (input i)).natMem
  have hf0 : f (i.n+1+3*s.natReg 90) = (i.graph.tail e).val := initial_old_tail i p e
  have hf1 : f (i.n+1+3*s.natReg 90+1) = if (i.graph.head e).val = i.source.val then i.n else (i.graph.head e).val := initial_old_head i p e
  have hf2 : f (i.n+1+3*s.natReg 90+2) = i.weight e := initial_old_weight i p e
  have heq : Function.update (Function.update (Function.update (natPrefix f (i.n+1+3*s.natReg 90))
      (i.n+1+3*s.natReg 90) (i.graph.tail e).val) (i.n+1+3*s.natReg 90+1)
      (if (i.graph.head e).val = i.source.val then i.n else (i.graph.head e).val)) (i.n+1+3*s.natReg 90+2) (i.weight e) =
      natPrefix f (i.n+1+3*(s.natReg 90+1)) := by
    rw [← hf0,← hf1,← hf2,natPrefix_step_three]
    congr 1
  rw [heq] at himg
  obtain ⟨h80,h82,h90⟩ := record_pointers s h.captured.unit h.stride
  obtain ⟨cost,he,_⟩ := record_eval s
  have hstride : (recordData s).natReg 88 = 4 :=
    (he.nat_frame (record_nat_frame 88 (by decide) (by decide) (by decide) (by decide))).trans h.stride
  refine ⟨record_captured h.captured,h.base_room,?_,?_,?_,hstride,?_,?_⟩
  · rw [h90];omega
  · rw [h80,h90,h.source];omega
  · rw [h82,h90,h.dest]
    dsimp [bankAddress,bankFactor]
    omega
  · rwa [h90]
  · intro a ha
    have hB : B ≤ s.natReg 82 := by rw [h.dest];dsimp [bankAddress,bankFactor];omega
    exact (record_prefix s B h.captured.unit h.stride hB a ha).1.trans (h.raw a ha)
lemma CopyInvariant.copy_loop {i : Input} {p : Program} {B : ℕ} {s : Data}
    (h : CopyInvariant i p B s) :
    ∃ cost t, Eval copyLoop s cost t ∧ cost ≤ 23*(i.k-s.natReg 90)+2 ∧
      CopyInvariant i p B t ∧ t.natReg 90 = i.k := by
  obtain ⟨t,cost,he,ht,hcost⟩ := loop_bounded (.natLess 90 68) recordCode (CopyInvariant i p B)
    (fun s => i.k-s.natReg 90) 21 (fun s hs htest => by
      have hc : s.natReg 90 < i.k := by change s.natReg 90 < s.natReg 68 at htest; rwa [hs.captured.edges] at htest
      obtain ⟨c,he,hcst⟩ := record_eval s
      refine ⟨recordData s,c,he,hs.step hc,?_,hcst⟩
      obtain ⟨_,_,h90⟩ := record_pointers s hs.captured.unit hs.stride
      rw [h90]
      omega) s h
  refine ⟨cost,t,he,hcost,ht,?_⟩
  have hstop := eval_loop_stops (.natLess 90 68) recordCode cost s t he
  change ¬t.natReg 90 < t.natReg 68 at hstop
  rw [ht.captured.edges] at hstop
  have hh := ht.count
  omega
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s116
section s117
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
lemma header_registers (i : Input) (p : Program) (s : Data) (h : InputCapture.Captured i s)
    (h76 : s.natReg 76 = i.n+1) (h78 : s.natReg 78 = sentinel i)
    (hN : ∀ j, s.natReg (shadowReg j) = 0) (hR : ∀ j, s.realReg (shadowReg j) = 0) :
    Registers i p (headerData p.initPC s) := by
  have hm : ∀ j, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 3 → j ≠ 4 →
      shadowReg j ≠ 9 ∧ shadowReg j ≠ 11 ∧ shadowReg j ≠ 13 ∧ shadowReg j ≠ 15 ∧ shadowReg j ≠ 17 := by
    intro j h0 h1 h2 h3 h4
    dsimp [shadowReg]
    omega
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals try { simp [headerData,headerAtoms,Atom.effect,instructionEffect,data,Data.machine,h.base,h.vertices,h76,h78,h.zeroN,h.two];done }
  · intro j
    by_cases h0 : j = 0
    · subst j
      simp [headerData,headerAtoms,Atom.effect,instructionEffect,data,Data.machine,shadowReg,initialMachine,input,h76]
      omega
    · by_cases h1 : j = 1
      · subst j
        simp [headerData,headerAtoms,Atom.effect,instructionEffect,data,Data.machine,shadowReg,initialMachine,input,h.edges,h.vertices]
        omega
      · by_cases h2 : j = 2
        · subst j
          simp [headerData,headerAtoms,Atom.effect,instructionEffect,data,Data.machine,shadowReg,initialMachine,input,h.size]
          omega
        · by_cases h3 : j = 3
          · subst j
            simp [headerData,headerAtoms,Atom.effect,instructionEffect,data,Data.machine,shadowReg,initialMachine,input,h78]
            omega
          · by_cases h4 : j = 4
            · subst j
              simp [headerData,headerAtoms,Atom.effect,instructionEffect,data,Data.machine,shadowReg,initialMachine,input,source,oldVertex,h.source]
              omega
            · obtain ⟨h9,h11,h13,h15,h17⟩ := hm j h0 h1 h2 h3 h4
              simp [headerData,headerAtoms,Atom.effect,instructionEffect,data,Data.machine,initialMachine,h0,h1,h2,h3,h4,
                h9,h11,h13,h15,h17,show shadowReg j ≠ 0 by unfold shadowReg;omega,
                show shadowReg j ≠ 1 by unfold shadowReg;omega,show shadowReg j ≠ 2 by unfold shadowReg;omega,
                show shadowReg j ≠ 3 by unfold shadowReg;omega,show shadowReg j ≠ 4 by unfold shadowReg;omega,
                show shadowReg j ≠ 5 by unfold shadowReg;omega,show shadowReg j ≠ 7 by unfold shadowReg;omega,
                show shadowReg j ≠ 16 by unfold shadowReg;omega,hN j]
  · intro j
    by_cases h0 : j = 0
    · subst j
      simp [headerData,headerAtoms,Atom.effect,instructionEffect,data,Data.machine,shadowReg,initialMachine,input,h.accuracy,h.zeroR]
    · have h9 : shadowReg j ≠ 9 := by unfold shadowReg;omega
      have h7 : shadowReg j ≠ 7 := by unfold shadowReg;omega
      have h26 : shadowReg j ≠ 26 := by unfold shadowReg;omega
      have h28 : shadowReg j ≠ 28 := by unfold shadowReg;omega
      simp [headerData,headerAtoms,Atom.effect,instructionEffect,data,Data.machine,initialMachine,h0,h9,h7,h26,h28,hR j]
  · simp [headerData,headerAtoms,Atom.effect,instructionEffect,data,Data.machine,h.vertices,h.base,h.two]
    omega
  · simp [headerData,headerAtoms,Atom.effect,instructionEffect,data,Data.machine,h78,sentinel,cutoff]
    ring
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s117
section s118
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end s118
section s119
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
lemma copyStart_eval (s : Data) : Eval copyStart s 7 (copyStarted s) := eval_sequence_atoms copyStartAtoms s
lemma copyStart_memory (s : Data) : (copyStarted s).natMem = s.natMem ∧ (copyStarted s).realMem = s.realMem := ⟨rfl,rfl⟩
lemma copyStart_nat_frame (k : ℕ) (h80 : k ≠ 80) (h82 : k ≠ 82) (h88 : k ≠ 88) (h90 : k ≠ 90) : NatFrame copyStart k := by
  simp [copyStart,copyStartAtoms,Structured.sequence,NatFrame,writesNat,Ne.symm h80,Ne.symm h82,Ne.symm h88,Ne.symm h90]
lemma copyStart_real_frame (k : ℕ) : RealFrame copyStart k := by
  simp [copyStart,copyStartAtoms,Structured.sequence,RealFrame,writesReal]
lemma copyStart_invariant (i : Input) (p : Program) (s : Data) (hcap : InputCapture.Captured i s)
    (h76 : s.natReg 76 = i.n+1) (hzero : SourceMemory.Image (i.n+3*i.k+2) 0 s (fun _ => 0) (fun _ => 0))
    (hraw : ∀ a, a < i.n+3*i.k+2 → s.natMem a = (initialMachine p i).natMem a) :
    CopyInvariant i p (i.n+3*i.k+2) (copyStarted s) := by
  have hc : InputCapture.Captured i (copyStarted s) := hcap.frame
    (fun k hk => (copyStart_eval s).nat_frame (copyStart_nat_frame k (by omega) (by omega) (by omega) (by omega)))
    (fun k _ => (copyStart_eval s).real_frame (copyStart_real_frame k))
  have hn : (copyStarted s).natReg 90 = 0 := by simp [copyStarted,copyStartAtoms,Atom.effect,instructionEffect,data,Data.machine]
  refine ⟨hc,by omega,by rw [hn];omega,?_,?_,?_,?_,hraw⟩
  · simp [copyStarted,copyStartAtoms,Atom.effect,instructionEffect,data,Data.machine,hcap.vertices,hcap.zeroN]
  · simp [copyStarted,copyStartAtoms,Atom.effect,instructionEffect,data,Data.machine,h76,hcap.base,hcap.two,bankAddress,bankFactor]
    omega
  · simp [copyStarted,copyStartAtoms,Atom.effect,instructionEffect,data,Data.machine]
  · rw [hn]
    have hz : SourceMemory.Image (i.n+3*i.k+2) 0 (copyStarted s) (fun _ => 0) (fun _ => 0) := ⟨hzero.natMem,hzero.realMem⟩
    simpa only [Nat.mul_zero,Nat.add_zero,initial_prefix_zero] using hz
lemma copyLoop_no_real_memory : NoRealMemory copyLoop := by
  simp [copyLoop,recordCode,fieldCode,fieldAtoms,headCode,headRedirect,headSuffix,headSuffixAtoms,Structured.sequence,
    NoRealMemory,NoRealStore,nadd,loadN,storeN]
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s119
section s120
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
attribute [local instance] Classical.propDecidable
lemma sentinel_eval (s : Data) : ∃ cost, Eval sentinelBody s cost (sentinelData s) ∧ cost ≤ 16 := by
  have hp : Eval sentinelPrefix s 4 (sentinelPrepared s) := eval_sequence_atoms sentinelPrefixAtoms s
  let t := sentinelPrepared s
  by_cases ht : t.natReg 90 < t.natReg 72
  · have he : Eval (.branch (.natLess 90 72) .skip (nadd 84 84 26)) t 1 t := Eval.branchYes ht (Eval.skip t)
    have hs : sentinelShifted t = t := if_pos ht
    refine ⟨4+(1+9),Eval.seq hp (Eval.seq ?_ (eval_sequence_atoms sentinelSuffixAtoms _)),by omega⟩
    change Eval (.branch (.natLess 90 72) .skip (nadd 84 84 26)) t 1 (sentinelShifted t)
    rw [hs]
    exact he
  · have he : Eval (.branch (.natLess 90 72) .skip (nadd 84 84 26)) t 3
        {t with natReg := Function.update t.natReg 84 (t.natReg 84+t.natReg 26)} :=
      Eval.branchNo ht (eval_nadd t 84 84 26)
    refine ⟨4+(3+9),Eval.seq hp (Eval.seq ?_ (eval_sequence_atoms sentinelSuffixAtoms _)),by omega⟩
    change Eval (.branch (.natLess 90 72) .skip (nadd 84 84 26)) t 3 (sentinelShifted t)
    simpa only [sentinelShifted,if_neg ht] using he
lemma sentinel_memory (s : Data) (hz : s.natReg 56 = 0) (h1 : s.natReg 26 = 1) (h4 : s.natReg 88 = 4) :
    (sentinelData s).natMem =
      Function.update (Function.update (Function.update (Function.update s.natMem (s.natReg 82) (2*s.natReg 72))
        (s.natReg 82+4) (2*(if s.natReg 90 < s.natReg 72 then s.natReg 90 else s.natReg 90+1)))
        (s.natReg 82+8) (2*s.natReg 78)) (s.natReg 92) (s.natReg 90) ∧
      (sentinelData s).realMem = s.realMem := by
  by_cases hj : s.natReg 90 < s.natReg 72 <;>
    simp [sentinelData,sentinelShifted,sentinelPrepared,sentinelPrefixAtoms,sentinelSuffixAtoms,
      Atom.effect,instructionEffect,data,Data.machine,hz,h1,h4,hj,two_mul,Nat.add_assoc]
lemma sentinel_pointers (s : Data) (h1 : s.natReg 26 = 1) (h4 : s.natReg 88 = 4) :
    (sentinelData s).natReg 82 = s.natReg 82+12 ∧ (sentinelData s).natReg 92 = s.natReg 92+4 ∧
      (sentinelData s).natReg 90 = s.natReg 90+1 := by
  by_cases hj : s.natReg 90 < s.natReg 72 <;>
    simp [sentinelData,sentinelShifted,sentinelPrepared,sentinelPrefixAtoms,sentinelSuffixAtoms,
      Atom.effect,instructionEffect,data,Data.machine,h1,h4,hj,Nat.add_assoc]
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s120
section s121
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
lemma Registers.frame {i : Input} {p : Program} {s t : Data} (h : Registers i p s)
    (hsmall : ∀ k, k ≤ 17 → t.natReg k = s.natReg k)
    (hNat : ∀ j, t.natReg (shadowReg j) = s.natReg (shadowReg j)) (hReal : t.realReg = s.realReg) : Registers i p t :=
  ⟨(hsmall 0 (by omega)).trans h.base,(hsmall 1 (by omega)).trans h.unit,
    (hsmall 7 (by omega)).trans h.factor,by simpa only [hReal] using h.realFactor,
    (hsmall 2 (by omega)).trans h.pc,(hsmall 3 (by omega)).trans h.work,
    (hsmall 4 (by omega)).trans h.halted,(hsmall 5 (by omega)).trans h.fault,
    fun j => (hNat j).trans (h.natReg j),fun j => by simpa only [hReal] using h.realReg j,
    (hsmall 16 (by omega)).trans h.limit,by simpa only [hReal] using h.threshold⟩
lemma Registers.copyStart {i : Input} {p : Program} {s : Data} (h : Registers i p s) : Registers i p (copyStarted s) := by
  have he := copyStart_eval s
  exact h.frame (fun k hk => he.nat_frame (copyStart_nat_frame k (by omega) (by omega) (by omega) (by omega)))
    (fun j => he.nat_frame (copyStart_nat_frame _ (by unfold shadowReg;omega) (by unfold shadowReg;omega)
      (by unfold shadowReg;omega) (by unfold shadowReg;omega))) (funext fun k => he.real_frame (copyStart_real_frame k))
lemma Registers.copyLoop {i : Input} {p : Program} {s t : Data} {cost : ℕ}
    (h : Registers i p s) (he : Eval copyLoop s cost t) : Registers i p t := by
  exact h.frame (fun k hk => he.nat_frame (record_nat_frame k (by omega) (by omega) (by omega) (by omega)))
    (fun j => he.nat_frame (record_nat_frame _ (by unfold shadowReg;omega) (by unfold shadowReg;omega)
      (by unfold shadowReg;omega) (by unfold shadowReg;omega))) (funext fun k => he.real_frame (record_real_frame k))
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s121
section s122
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
lemma sentinel_nat_frame (k : ℕ) (h82 : k ≠ 82) (h84 : k ≠ 84) (h90 : k ≠ 90) (h92 : k ≠ 92) : NatFrame sentinelBody k := by
  simp [sentinelBody,sentinelPrefix,sentinelSuffix,sentinelPrefixAtoms,sentinelSuffixAtoms,Structured.sequence,
    NatFrame,writesNat,nadd,storeN,Ne.symm h82,Ne.symm h84,Ne.symm h90,Ne.symm h92]
lemma sentinel_real_frame (k : ℕ) : RealFrame sentinelBody k := by
  simp [sentinelBody,sentinelPrefix,sentinelSuffix,sentinelPrefixAtoms,sentinelSuffixAtoms,Structured.sequence,
    RealFrame,writesReal,nadd,storeN]
lemma sentinel_no_real_memory : NoRealMemory sentinelBody := by
  simp [sentinelBody,sentinelPrefix,sentinelSuffix,sentinelPrefixAtoms,sentinelSuffixAtoms,Structured.sequence,
    NoRealMemory,NoRealStore,nadd,storeN]
lemma sentinel_captured {i : Input} {s : Data} (h : InputCapture.Captured i s) : InputCapture.Captured i (sentinelData s) := by
  obtain ⟨c,he,_⟩ := sentinel_eval s
  exact h.frame (fun k hk => he.nat_frame (sentinel_nat_frame k (by omega) (by omega) (by omega) (by omega)))
    (fun k _ => he.real_frame (sentinel_real_frame k))
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s122
section s123
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.SourceMemory
open Structured
lemma Image.three_with_mapping {B logical a0 a1 a2 j : ℕ} {s t : Data} {natural : ℕ → ℕ} {real : ℕ → ℝ}
    (h : Image B 0 s natural real)
    (hn : t.natMem = Function.update (Function.update (Function.update (Function.update s.natMem
      (bankAddress B 0 logical) (2*a0)) (bankAddress B 0 (logical+1)) (2*a1))
      (bankAddress B 0 (logical+2)) (2*a2)) (B+4*j+3) j)
    (hr : t.realMem = s.realMem) :
    Image B 0 t (Function.update (Function.update (Function.update natural logical a0) (logical+1) a1) (logical+2) a2) real := by
  constructor
  · intro a
    rw [hn,Function.update_of_ne (by dsimp [bankAddress,bankFactor];omega : bankAddress B 0 a ≠ B+4*j+3)]
    by_cases h0 : a = logical
    · subst a
      simp [bankAddress,bankFactor,Function.update_of_ne,show ¬logical = logical+1 by omega,show ¬logical = logical+2 by omega]
    · by_cases h1 : a = logical+1
      · subst a
        simp [bankAddress,bankFactor,show ¬logical+1 = logical+2 by omega]
      · by_cases h2 : a = logical+2
        · subst a;simp [bankAddress,bankFactor]
        · have hn0 : bankAddress B 0 a ≠ bankAddress B 0 logical := fun he => h0 (bankAddress_injective he).2
          have hn1 : bankAddress B 0 a ≠ bankAddress B 0 (logical+1) := fun he => h1 (bankAddress_injective he).2
          have hn2 : bankAddress B 0 a ≠ bankAddress B 0 (logical+2) := fun he => h2 (bankAddress_injective he).2
          rw [Function.update_of_ne hn2,Function.update_of_ne hn1,Function.update_of_ne hn0,
            Function.update_of_ne h2,Function.update_of_ne h1,Function.update_of_ne h0]
          exact h.natMem a
  · intro a
    rw [hr]
    exact h.realMem a
end DecrAlmostLinearSSSP.Decremental.SourceMemory
end s123
section s124
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
lemma SentinelInvariant.step {i : Input} {p : Program} {B : ℕ} {s : Data}
    (h : SentinelInvariant i p B s) (hc : s.natReg 90 < i.n) : SentinelInvariant i p B (sentinelData s) := by
  let j : Fin i.n := ⟨s.natReg 90,hc⟩
  let logical := i.n+1+3*(i.k+s.natReg 90)
  let f := (initialMachine p (input i)).natMem
  obtain ⟨hmN,hmR⟩ := sentinel_memory s h.captured.zeroN h.captured.unit h.stride
  rw [h.dest,h.map,h.captured.source,h.weight] at hmN
  have hb1 : bankAddress B 0 logical+4 = bankAddress B 0 (logical+1) := by dsimp [bankAddress,bankFactor];omega
  have hb2 : bankAddress B 0 logical+8 = bankAddress B 0 (logical+2) := by dsimp [bankAddress,bankFactor];omega
  change (sentinelData s).natMem = Function.update (Function.update (Function.update (Function.update s.natMem
    (bankAddress B 0 logical) (2*i.source.val)) (bankAddress B 0 logical+4)
    (2*(if s.natReg 90 < i.source.val then s.natReg 90 else s.natReg 90+1)))
    (bankAddress B 0 logical+8) (2*sentinel i)) (B+4*s.natReg 90+3) (s.natReg 90) at hmN
  rw [hb1,hb2] at hmN
  have hi := h.image.three_with_mapping hmN hmR
  have hf0 : f logical = i.source.val := initial_added_tail i p j
  have hf1 : f (logical+1) = if s.natReg 90 < i.source.val then s.natReg 90 else s.natReg 90+1 := initial_added_head i p j
  have hf2 : f (logical+2) = sentinel i := initial_added_weight i p j
  have heq : Function.update (Function.update (Function.update (natPrefix f logical) logical i.source.val)
      (logical+1) (if s.natReg 90 < i.source.val then s.natReg 90 else s.natReg 90+1)) (logical+2) (sentinel i) =
      natPrefix f (i.n+1+3*(i.k+(s.natReg 90+1))) := by
    rw [← hf1,← hf0,← hf2,natPrefix_step_three]
    congr 1
  rw [heq] at hi
  obtain ⟨h82,h92,h90⟩ := sentinel_pointers s h.captured.unit h.stride
  obtain ⟨cost,he,_⟩ := sentinel_eval s
  have hstride := (he.nat_frame (sentinel_nat_frame 88 (by decide) (by decide) (by decide) (by decide))).trans h.stride
  have hweight := (he.nat_frame (sentinel_nat_frame 78 (by decide) (by decide) (by decide) (by decide))).trans h.weight
  refine ⟨sentinel_captured h.captured,?_,?_,?_,hstride,hweight,?_,?_,?_⟩
  · rw [h90];omega
  · rw [h82,h90,h.dest]
    dsimp [bankAddress,bankFactor]
    omega
  · rw [h92,h90,h.map];omega
  · rwa [h90]
  · intro v hv
    rw [h90] at hv
    rw [hmN,Function.update_apply]
    by_cases hvj : v.val = s.natReg 90
    · simp [hvj]
    · have hne : B+4*v.val+3 ≠ B+4*s.natReg 90+3 := by omega
      simp only [hne,if_false]
      have hnv0 : B+4*v.val+3 ≠ bankAddress B 0 logical := by dsimp [bankAddress,bankFactor];omega
      have hnv1 : B+4*v.val+3 ≠ bankAddress B 0 (logical+1) := by dsimp [bankAddress,bankFactor];omega
      have hnv2 : B+4*v.val+3 ≠ bankAddress B 0 (logical+2) := by dsimp [bankAddress,bankFactor];omega
      rw [Function.update_of_ne hnv2,Function.update_of_ne hnv1,Function.update_of_ne hnv0]
      exact h.mapping v (by omega)
  · intro a ha
    rw [hmN]
    have hne0 : a ≠ bankAddress B 0 logical := by dsimp [bankAddress,bankFactor];omega
    have hne1 : a ≠ bankAddress B 0 (logical+1) := by dsimp [bankAddress,bankFactor];omega
    have hne2 : a ≠ bankAddress B 0 (logical+2) := by dsimp [bankAddress,bankFactor];omega
    rw [Function.update_of_ne (by omega : a ≠ B+4*s.natReg 90+3),Function.update_of_ne hne2,Function.update_of_ne hne1,Function.update_of_ne hne0]
    exact h.raw a ha
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s124
section s125
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
lemma SentinelInvariant.loop {i : Input} {p : Program} {B : ℕ} {s : Data}
    (h : SentinelInvariant i p B s) :
    ∃ cost t, Eval sentinelLoop s cost t ∧ cost ≤ 18*(i.n-s.natReg 90)+2 ∧
      SentinelInvariant i p B t ∧ t.natReg 90 = i.n := by
  obtain ⟨t,cost,he,ht,hcost⟩ := loop_bounded (.natLess 90 66) sentinelBody (SentinelInvariant i p B)
    (fun s => i.n-s.natReg 90) 16 (fun s hs htest => by
      have hc : s.natReg 90 < i.n := by change s.natReg 90 < s.natReg 66 at htest;rwa [hs.captured.vertices] at htest
      obtain ⟨c,he,hcst⟩ := sentinel_eval s
      refine ⟨sentinelData s,c,he,hs.step hc,?_,hcst⟩
      obtain ⟨_,_,h90⟩ := sentinel_pointers s hs.captured.unit hs.stride
      rw [h90]
      omega) s h
  refine ⟨cost,t,he,hcost,ht,?_⟩
  have hstop := eval_loop_stops (.natLess 90 66) sentinelBody cost s t he
  change ¬t.natReg 90 < t.natReg 66 at hstop
  rw [ht.captured.vertices] at hstop
  have hh := ht.count
  omega
lemma Registers.sentinelLoop {i : Input} {p : Program} {s t : Data} {cost : ℕ}
    (h : Registers i p s) (he : Eval sentinelLoop s cost t) : Registers i p t := by
  exact h.frame (fun k hk => he.nat_frame (sentinel_nat_frame k (by omega) (by omega) (by omega) (by omega)))
    (fun j => he.nat_frame (sentinel_nat_frame _ (by unfold shadowReg;omega) (by unfold shadowReg;omega)
      (by unfold shadowReg;omega) (by unfold shadowReg;omega))) (funext fun k => he.real_frame (sentinel_real_frame k))
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s125
section s126
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
lemma sentinelStart_eval (s : Data) : Eval sentinelStart s 3 (sentinelStarted s) := eval_sequence_atoms sentinelStartAtoms s
lemma sentinelStart_nat_frame (k : ℕ) (h90 : k ≠ 90) (h92 : k ≠ 92) : NatFrame sentinelStart k := by
  simp [sentinelStart,sentinelStartAtoms,Structured.sequence,NatFrame,writesNat,Ne.symm h90,Ne.symm h92]
lemma sentinelStart_real_frame (k : ℕ) : RealFrame sentinelStart k := by
  simp [sentinelStart,sentinelStartAtoms,Structured.sequence,RealFrame,writesReal]
lemma sentinelStart_invariant (i : Input) (p : Program) (s : Data)
    (h : CopyInvariant i p (i.n+3*i.k+2) s) (hc : s.natReg 90 = i.k) (hW : s.natReg 78 = sentinel i) :
    SentinelInvariant i p (i.n+3*i.k+2) (sentinelStarted s) := by
  have he := sentinelStart_eval s
  have hcap : InputCapture.Captured i (sentinelStarted s) := h.captured.frame
    (fun k hk => he.nat_frame (sentinelStart_nat_frame k (by omega) (by omega)))
    (fun k _ => he.real_frame (sentinelStart_real_frame k))
  have hn : (sentinelStarted s).natReg 90 = 0 := by simp [sentinelStarted,sentinelStartAtoms,Atom.effect,instructionEffect,data,Data.machine]
  refine ⟨hcap,by rw [hn];omega,?_,?_,?_,?_,?_,?_,h.raw⟩
  · simp only [sentinelStarted,sentinelStartAtoms,List.foldl_cons,List.foldl_nil,Atom.effect,instructionEffect,data,Data.machine]
    simp (disch := decide) only [Function.update_of_ne]
    simpa only [hc,Nat.add_zero,Function.update_self] using h.dest
  · simp [sentinelStarted,sentinelStartAtoms,Atom.effect,instructionEffect,data,Data.machine,h.captured.base,h.captured.unit,h.captured.two]
  · simpa [sentinelStarted,sentinelStartAtoms,Atom.effect,instructionEffect,data,Data.machine] using h.stride
  · simpa [sentinelStarted,sentinelStartAtoms,Atom.effect,instructionEffect,data,Data.machine] using hW
  · have himage := h.image
    rw [hc] at himage
    rw [hn]
    exact ⟨himage.natMem,himage.realMem⟩
  · intro v hv
    rw [hn] at hv
    omega
lemma Registers.sentinelStart {i : Input} {p : Program} {s : Data} (h : Registers i p s) : Registers i p (sentinelStarted s) := by
  have he := sentinelStart_eval s
  exact h.frame (fun k hk => he.nat_frame (sentinelStart_nat_frame k (by omega) (by omega)))
    (fun j => he.nat_frame (sentinelStart_nat_frame _ (by unfold shadowReg;omega) (by unfold shadowReg;omega)))
    (funext fun k => he.real_frame (sentinelStart_real_frame k))
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s126
section s127
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
lemma header_captured {i : Input} (entry : ℕ) {s : Data} (h : InputCapture.Captured i s) :
    InputCapture.Captured i (headerData entry s) := by
  have he := headerCode_eval entry s
  have hn (k : ℕ) (hk : 18 ≤ k) : (headerData entry s).natReg k = s.natReg k :=
    he.nat_frame (headerCode_nat_frame entry k hk)
  have hr (k : ℕ) (hk : k ≠ 7 ∧ k ≠ 9 ∧ k ≠ 26 ∧ k ≠ 28) : (headerData entry s).realReg k = s.realReg k :=
    he.real_frame (headerCode_real_frame entry k hk.1 hk.2.1 hk.2.2.1 hk.2.2.2)
  refine ⟨(hn 56 (by omega)).trans h.zeroN,(hr 56 (by omega)).trans h.zeroR,
    (hn 26 (by omega)).trans h.unit,?_,(hn 34 (by omega)).trans h.scanZero,(hn 36 (by omega)).trans h.scanUnit,
    (hn 64 (by omega)).trans h.size,(hn 66 (by omega)).trans h.vertices,(hn 68 (by omega)).trans h.edges,
    (hn 70 (by omega)).trans h.weightBound,(hn 72 (by omega)).trans h.source,(hr 64 (by omega)).trans h.accuracy,
    (hn 74 (by omega)).trans h.base,(hn 48 (by omega)).trans h.utilityBase,(hn 58 (by omega)).trans h.factor,
    (hr 58 (by omega)).trans h.argument⟩
  simpa [headerData,headerAtoms,Atom.effect,instructionEffect,data,Data.machine] using h.two
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s127
section s128
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
attribute [local instance] Classical.propDecidable
lemma Image.commit {i : Input} {B a : ℕ} {s : Data} {g : Machine}
    (h : Image i B (some a) s g) (ha : a < i.n) (haddr : s.natReg 6 = B+4*a+2)
    (h1 : s.natReg 1 = 1) (hrep : ShadowDataRep B 2 s g) : Image i B none (committed s) g := by
  let v : Fin i.n := ⟨a,ha⟩
  have hdecode : s.natMem (s.natReg 6+1) = a := by
    rw [haddr,show B+4*a+2+1 = B+4*a+3 by omega]
    exact h.mapping v
  have hnat : s.natMem (s.natReg 6) = 2*g.natMem a := by
    rw [haddr]
    simpa only [Data.machine,show B+2*(2*a+1) = B+4*a+2 by omega] using hrep.natMem a
  have hreal : s.realMem (s.natReg 6) = g.realMem a := by
    rw [haddr]
    simpa only [Data.machine,show B+2*(2*a+1) = B+4*a+2 by omega] using hrep.realMem a
  obtain ⟨hmN,hmR⟩ := committed_memory s h1
  rw [hdecode,hreal] at hmN hmR
  rw [h.threshold] at hmN
  have hflag : (1 < s.natMem (s.natReg 6) ∨ (cutoff i : ℝ) < g.realMem a) ↔
      (0 < g.natMem a ∨ (cutoff i : ℝ) < g.realMem a) := by
    have hh : 1 < 2*g.natMem a ↔ 0 < g.natMem a := by omega
    simpa only [hnat] using or_congr hh (Iff.rfl : ((cutoff i : ℝ) < g.realMem a) ↔ ((cutoff i : ℝ) < g.realMem a))
  simp only [hflag] at hmN
  have he := inner_eval s
  refine ⟨h.room,?_,?_,?_,?_,?_⟩
  · exact (he.nat_frame (inner_nat_frame 16 (by decide) (by decide) (by decide) (by decide))).trans h.limit
  · exact (he.real_frame (inner_real_frame 26 (by decide))).trans h.threshold
  · intro w
    rw [hmN,Function.update_of_ne (by have hw := w.isLt;have hr := h.room;omega : B+4*w.val+3 ≠ a)]
    exact h.mapping w
  · intro w _
    rw [hmR]
    by_cases hw : w.val = a
    · rw [hw,Function.update_self]
    · rw [Function.update_of_ne hw]
      exact h.values w (by simp [Ne.symm hw])
  · intro w _
    rw [hmN]
    by_cases hw : w.val = a
    · rw [hw,Function.update_self]
      rfl
    · rw [Function.update_of_ne hw]
      exact h.flags w (by simp [Ne.symm hw])
lemma callback_image {i : Input} {B a : ℕ} {s : Data} {g : Machine}
    (h : Image i B (some a) s g) (haddr : s.natReg 6 = B+4*a+2)
    (h1 : s.natReg 1 = 1) (hrep : ShadowDataRep B 2 s g) :
    ∃ cost t, Eval callback s cost t ∧ cost ≤ 12 ∧ ShadowDataRep B 2 t g ∧ Image i B none t g := by
  by_cases ha : a < i.n
  · have htest : (Test.natLess 6 16).holds s := by change s.natReg 6 < s.natReg 16;rw [haddr,h.limit];omega
    have hpub : s.natMem (s.natReg 6+1) < i.n := by
      rw [haddr,show B+4*a+2+1 = B+4*a+3 by omega,h.mapping ⟨a,ha⟩]
      exact ha
    exact ⟨12,committed s,Eval.branchYes htest (inner_eval s),le_rfl,
      inner_shadow i.n h.room hrep h1 hpub,h.commit ha haddr h1 hrep⟩
  · have htest : ¬(Test.natLess 6 16).holds s := by change ¬s.natReg 6 < s.natReg 16;rw [haddr,h.limit];omega
    exact ⟨2,s,Eval.branchNo htest (Eval.skip s),by omega,hrep,h.remove_bad (fun v => by have hv := v.isLt;intro he;have hh := Option.some.inj he;omega)⟩
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s128
section s129
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
lemma source_memory_away (ins : Instruction) (g : Machine) (v : ℕ)
    (hv : writtenAddress ins g ≠ some v) :
    (instructionEffect ins g).natMem v = g.natMem v ∧ (instructionEffect ins g).realMem v = g.realMem v := by
  cases ins <;> simp only [writtenAddress] at hv
  all_goals try exact ⟨rfl,rfl⟩
  all_goals simp only [instructionEffect]
  all_goals try simp only [ne_eq,Option.some.injEq] at hv
  all_goals simp_all [Function.update_of_ne]
  all_goals first | exact Function.update_of_ne (Ne.symm hv) _ _ | (split <;> exact ⟨rfl,rfl⟩)
lemma Image.action {i : Input} {B : ℕ} {s t : Data} {g : Machine}
    (h : Image i B none s g) (hrep : ShadowDataRep B 2 s g) (hb : s.natReg 0 = B)
    (hF : s.natReg 7 = 2) (ins : Instruction) (cost : ℕ) (he : Eval (shadowAction ins) s cost t) :
    Image i B (writtenAddress ins g) t (instructionEffect ins g) := by
  have h16 := he.nat_frame (shadowAction_even_frame ins 16 (by omega) (by decide))
  have hr26 := he.real_frame (shadowAction_real_even_frame ins 26 (by decide))
  have hmem (address : ℕ) (hout : ∀ a, address ≠ B+2*(2*a+1)) :
      t.realMem address = s.realMem address ∧ t.natMem address = s.natMem address :=
    shadowAction_memory_frame hrep hb hF ins cost he address hout
  refine ⟨h.room,h16.trans h.limit,hr26.trans h.threshold,?_,?_,?_⟩
  · intro v
    exact (hmem (B+4*v.val+3) (fun a => by omega)).2.trans (h.mapping v)
  · intro v hv
    have hm := hmem v.val (fun a => by have hv := v.isLt;have hn := h.room;omega)
    rw [hm.1,h.values v (by simp),(source_memory_away ins g v.val hv).2]
  · intro v hv
    have hm := hmem v.val (fun a => by have hv := v.isLt;have hn := h.room;omega)
    rw [hm.2,h.flags v (by simp)]
    unfold answerFlag
    rw [(source_memory_away ins g v.val hv).1,(source_memory_away ins g v.val hv).2]
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s129
section s130
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
lemma shadow_store_address {B F : ℕ} {s t : Data} {g : Machine}
    (h : ShadowDataRep B F s g) (hb : s.natReg 0 = B) (hf : s.natReg 7 = F)
    (a d cost : ℕ) (he : Eval (shadowAction (.store a d)) s cost t) :
    t.natReg 6 = B+F*(2*g.natReg a+1) := by
  obtain ⟨u,hu,hrep,ha⟩ := eval_shadow_address h hb hf a
  have hfull := Eval.seq hu (eval_store u 6 (shadowReg d))
  obtain ⟨_,rfl⟩ := he.deterministic hfull
  exact ha
lemma shadow_storeN_address {B F : ℕ} {s t : Data} {g : Machine}
    (h : ShadowDataRep B F s g) (hb : s.natReg 0 = B) (hf : s.natReg 7 = F)
    (a d cost : ℕ) (he : Eval (shadowAction (.storeN a d)) s cost t) :
    t.natReg 6 = B+F*(2*g.natReg a+1) := by
  obtain ⟨u,hu,hrep,ha⟩ := eval_shadow_address h hb hf a
  have hfull := Eval.seq hu (eval_storeN u 6 (shadowReg d))
  obtain ⟨_,rfl⟩ := he.deterministic hfull
  exact ha
end DecrAlmostLinearSSSP.Decremental
end s130
section s131
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured Instrumented
lemma shadow_machine_rep {B F : ℕ} {s t : Data} {g : Machine} (h : MachineRep B F s g)
    (ins : Instruction) (cost : ℕ) (he : Eval (shadowAction ins) s cost t)
    (ht : ShadowDataRep B F t (instructionEffect ins g)) : MachineRep B F t (instructionEffect ins g) := by
  refine ⟨ht,?_,?_,?_,?_,?_⟩
  · exact (he.nat_frame (shadowAction_nat_frame ins 0 (by omega) (by omega) (by omega) (by omega))).trans h.2.1
  · exact (he.nat_frame (shadowAction_nat_frame ins 1 (by omega) (by omega) (by omega) (by omega))).trans h.2.2.1
  · exact (he.nat_frame (shadowAction_nat_frame ins 7 (by omega) (by omega) (by omega) (by omega))).trans h.2.2.2.1
  · exact (he.real_frame (shadowAction_real_frame ins 7 (by omega))).trans h.2.2.2.2.1
  · exact he.flag_bound (shadowAction_flag_frame ins) h.2.2.2.2.2
lemma callback_machine_rep {B F : ℕ} {s t : Data} {g : Machine} (h : MachineRep B F s g)
    (cost : ℕ) (he : Eval callback s cost t) (ht : ShadowDataRep B F t g) : MachineRep B F t g := by
  refine ⟨ht,?_,?_,?_,?_,?_⟩
  · exact (he.nat_frame (callback_nat_frame 0 (by decide) (by decide) (by decide) (by decide))).trans h.2.1
  · exact (he.nat_frame (callback_nat_frame 1 (by decide) (by decide) (by decide) (by decide))).trans h.2.2.1
  · exact (he.nat_frame (callback_nat_frame 7 (by decide) (by decide) (by decide) (by decide))).trans h.2.2.2.1
  · exact (he.real_frame (callback_real_frame 7 (by decide))).trans h.2.2.2.2.1
  · rw [he.nat_frame (callback_nat_frame 4 (by decide) (by decide) (by decide) (by decide))]
    exact h.2.2.2.2.2
lemma action_spec (i : Input) (B : ℕ) : ActionSpec action bound (Image i B none) B 2 := by
  refine ⟨fun s g h => h.header,fun s g x h => h.scratch x,?_⟩
  intro s g ins h hp
  obtain ⟨cost,u,he,hcost,hrep⟩ := eval_shadow_action h.1 (by omega) h.2.1 h.2.2.2.1 h.2.2.2.2.1 ins
  have hu := shadow_machine_rep h ins cost he hrep
  have himage := hp.action h.1 h.2.1 h.2.2.2.1 ins cost he
  by_cases hs : NoStore ins
  · have ha : action ins = shadowAction ins := by cases ins <;> simp_all [action,writtenAddress,NoStore]
    have hnone : writtenAddress ins g = none := by cases ins <;> simp_all [action,writtenAddress,NoStore]
    rw [hnone] at himage
    exact ⟨cost,u,by rwa [ha],by unfold bound;omega,hu,himage⟩
  · cases ins with
    | store a d =>
      have haddr : u.natReg 6 = B+4*g.natReg a+2 := by
        have ha := shadow_store_address h.1 h.2.1 h.2.2.2.1 a d cost he
        omega
      obtain ⟨cc,t,ht,hcc,htrep,htim⟩ := callback_image himage haddr hu.2.2.1 hrep
      exact ⟨cost+cc,t,Eval.seq he ht,by unfold bound;omega,callback_machine_rep hu cc ht htrep,htim⟩
    | storeN a d =>
      have haddr : u.natReg 6 = B+4*g.natReg a+2 := by
        have ha := shadow_storeN_address h.1 h.2.1 h.2.2.2.1 a d cost he
        omega
      obtain ⟨cc,t,ht,hcc,htrep,htim⟩ := callback_image himage haddr hu.2.2.1 hrep
      exact ⟨cost+cc,t,Eval.seq he ht,by unfold bound;omega,callback_machine_rep hu cc ht htrep,htim⟩
    | _ => all_goals exact False.elim (hs trivial)
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s131
section s132
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured Instrumented
lemma boot_no_real_memory (p : Program) : NoRealMemory (bootCode p) := by
  refine ⟨?_,?_,?_,?_,copyLoop_no_real_memory,?_,sentinel_no_real_memory⟩
  · simp [InputCapture.code,InputCapture.atoms,Structured.sequence,NoRealMemory,NoRealStore]
  · simp [weightCode,prepareCode,prepareAtoms,accumulate,Structured.sequence,NoRealMemory,NoRealStore,nadd]
  · simp [headerCode,headerAtoms,Structured.sequence,NoRealMemory,NoRealStore]
  · simp [copyStart,copyStartAtoms,Structured.sequence,NoRealMemory,NoRealStore]
  · simp [sentinelStart,sentinelStartAtoms,Structured.sequence,NoRealMemory,NoRealStore]
lemma boot_eval (i : Input) (hi : i.Valid) (host p : Program) :
    ∃ cost s, Eval (bootCode p) (data (initialMachine host i)) cost s ∧ cost ≤ 50*i.size+100 ∧
      Registers i p s ∧ SentinelInvariant i p (i.n+3*i.k+2) s ∧ s.natReg 90 = i.n := by
  let start := data (initialMachine host i)
  let a := InputCapture.result start
  have ha : Eval InputCapture.code start 19 a := InputCapture.eval_code start
  have haCap : InputCapture.Captured i a := InputCapture.captures_initial host i
  obtain ⟨b,hb,hbW⟩ := weightCode_eval i a haCap
  have hbCap := weightCode_captured haCap hb
  have hb76 := weightCode_vertices haCap hb
  have hz0 := InputCapture.initial_shadow_zero host i
  have hbN : ∀ j, b.natReg (shadowReg j) = 0 := by
    intro j
    have hf := hb.nat_frame (weightCode_nat_frame (shadowReg j) (by unfold shadowReg;omega)
      (by unfold shadowReg;omega) (by unfold shadowReg;omega) (by unfold shadowReg;omega))
    exact hf.trans (hz0 j).1
  have hbR : ∀ j, b.realReg (shadowReg j) = 0 := by
    intro j
    exact (hb.real_frame (weightCode_real_frame _)).trans (hz0 j).2
  let c := headerData p.initPC b
  have hc := headerCode_eval p.initPC b
  have hcCap := header_captured p.initPC hbCap
  have hcRegs : Registers i p c := header_registers i p b hbCap hb76 hbW hbN hbR
  have hc76 : c.natReg 76 = i.n+1 := (hc.nat_frame (headerCode_nat_frame _ 76 (by omega))).trans hb76
  have hcW : c.natReg 78 = sentinel i := (hc.nat_frame (headerCode_nat_frame _ 78 (by omega))).trans hbW
  obtain ⟨haR,haN⟩ := ha.no_memory InputCapture.no_memory
  obtain ⟨hbRmem,hbNmem⟩ := hb.no_memory weightCode_no_memory
  obtain ⟨hcRmem,hcNmem⟩ := hc.no_memory (headerCode_no_memory _)
  have hcMem : c.natMem = start.natMem ∧ c.realMem = start.realMem :=
    ⟨hcNmem.trans (hbNmem.trans haN),hcRmem.trans (hbRmem.trans haR)⟩
  have hcZero : SourceMemory.Image (i.n+3*i.k+2) 0 c (fun _ => 0) (fun _ => 0) := by
    constructor
    · intro x
      rw [hcMem.1]
      have hh := (initial_source_bank_zero host i (i.n+3*i.k+2) 2 (by omega) (by omega) x).1
      simpa [start,data,bankAddress,bankFactor] using hh
    · intro x
      rw [hcMem.2]
      rfl
  have hcRaw : ∀ x, x < i.n+3*i.k+2 → c.natMem x = (initialMachine p i).natMem x := by
    intro x _
    rw [hcMem.1]
    rfl
  let d := copyStarted c
  have hd := copyStart_eval c
  have hdInv := copyStart_invariant i p c hcCap hc76 hcZero hcRaw
  obtain ⟨cl,e,he,heCost,heInv,heCount⟩ := hdInv.copy_loop
  have hdRegs : Registers i p d := hcRegs.copyStart
  have heRegs : Registers i p e := hdRegs.copyLoop he
  have hdW : d.natReg 78 = sentinel i := (hd.nat_frame (copyStart_nat_frame 78 (by omega) (by omega) (by omega) (by omega))).trans hcW
  have heW : e.natReg 78 = sentinel i := (he.nat_frame (record_nat_frame 78 (by omega) (by omega) (by omega) (by omega))).trans hdW
  let f := sentinelStarted e
  have hf := sentinelStart_eval e
  have hfInv := sentinelStart_invariant i p e heInv heCount heW
  have hfRegs : Registers i p f := heRegs.sentinelStart
  obtain ⟨cs,g,hg,hgCost,hgInv,hgCount⟩ := hfInv.loop
  have hgRegs : Registers i p g := hfRegs.sentinelLoop hg
  have hd0 : d.natReg 90 = 0 := by simp [d,copyStarted,copyStartAtoms,Atom.effect,instructionEffect,data,Data.machine]
  have hf0 : f.natReg 90 = 0 := by simp [f,sentinelStarted,sentinelStartAtoms,Atom.effect,instructionEffect,data,Data.machine]
  rw [hd0,Nat.sub_zero] at heCost
  rw [hf0,Nat.sub_zero] at hgCost
  refine ⟨19 + ((4 * (i.n + 1) + 8) + (24 + (7 + (cl + (3 + cs))))),g,
    Eval.seq ha (Eval.seq hb (Eval.seq hc (Eval.seq hd (Eval.seq he (Eval.seq hf hg))))),?_,hgRegs,hgInv,hgCount⟩
  have hn := hi.1
  have hk := hi.2.1
  omega
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s132
section s133
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured Instrumented
lemma initial_nat_below (p : Program) (i : Input) (a : ℕ) (ha : a < i.n) :
    (initialMachine p i).natMem a = 0 := by
  simp [initialMachine,show ¬i.n ≤ a from not_le.mpr ha]
lemma Registers.machine_rep {i : Input} {p : Program} {s : Data} (h : Registers i p s)
    (hm : SourceMemory.Image (i.n+3*i.k+2) 0 s (initialMachine p (input i)).natMem (initialMachine p (input i)).realMem) :
    MachineRep (i.n+3*i.k+2) 2 s (initialMachine p (input i)) := by
  refine ⟨?_,h.base,h.unit,h.factor,h.realFactor,by rw [h.halted];omega⟩
  refine ⟨h.pc,h.work,?_,?_,h.realReg,h.natReg,?_,?_⟩
  · change (s.natReg 4 == 1) = false
    simp [h.halted]
  · change (s.natReg 5 == 1) = false
    simp [h.fault]
  · intro a
    simpa [Data.machine,bankAddress,bankFactor] using hm.realMem a
  · intro a
    simpa [Data.machine,bankAddress,bankFactor] using hm.natMem a
lemma boot_ready (i : Input) (hi : i.Valid) (host p : Program) :
    ∃ cost s, Eval (bootCode p) (data (initialMachine host i)) cost s ∧ cost ≤ 50*i.size+100 ∧
      MachineRep (i.n+3*i.k+2) 2 s (initialMachine p (input i)) ∧ Image i (i.n+3*i.k+2) none s (initialMachine p (input i)) := by
  obtain ⟨cost,s,he,hcost,hr,hs,hcount⟩ := boot_eval i hi host p
  have himage := hs.image
  rw [hcount,initial_prefix_full] at himage
  have hrm : s.realMem = (fun _ => 0) := he.no_real_memory (boot_no_real_memory p)
  have hMachine := hr.machine_rep himage
  refine ⟨cost,s,he,hcost,hMachine,?_,?_,?_,?_,?_,?_⟩
  · omega
  · exact hr.limit
  · exact hr.threshold
  · intro v
    exact hs.mapping v (by rw [hcount];exact v.isLt)
  · intro v _
    rw [hrm]
    rfl
  · intro v _
    have hv := v.isLt
    rw [hs.raw v.val (by omega),initial_nat_below p i v.val hv]
    unfold answerFlag
    rw [initial_nat_below p (input i) v.val (by change v.val < i.n+1;omega)]
    change 0 = if 0 < 0 ∨ (cutoff i : ℝ) < 0 then 1 else 0
    simp only [lt_self_iff_false,false_or,not_lt_of_ge (Nat.cast_nonneg (cutoff i)),if_false]
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s133
section s134
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured Instrumented
lemma updateHeader_eval (p : Program) (s : Data) (e : ℕ) :
    Eval (updateHeader p) (externallySupplied s e) 4 (updateStarted p s e) := eval_sequence_atoms (updateHeaderAtoms p.update) _
lemma updateHeader_rep (p : Program) (B : ℕ) (s : Data) (g : Machine) (e : ℕ)
    (h : MachineRep B 2 s g) : MachineRep B 2 (updateStarted p s e) (deletionMachine p g e) := by
  have hn (j : ℕ) (h2 : j ≠ 2) (h4 : j ≠ 4) (h5 : j ≠ 5) (h19 : j ≠ 19) :
      (updateStarted p s e).natReg j = s.natReg j := by
    simp [updateStarted,externallySupplied,updateHeaderAtoms,Atom.effect,instructionEffect,data,Data.machine,
      Function.update_of_ne h2,Function.update_of_ne h4,Function.update_of_ne h5,Function.update_of_ne h19]
  have hn2 : (updateStarted p s e).natReg 2 = p.update := by simp [updateStarted,externallySupplied,updateHeaderAtoms,Atom.effect,instructionEffect,data,Data.machine]
  have hn4 : (updateStarted p s e).natReg 4 = 0 := by simp [updateStarted,externallySupplied,updateHeaderAtoms,Atom.effect,instructionEffect,data,Data.machine]
  have hn5 : (updateStarted p s e).natReg 5 = 0 := by simp [updateStarted,externallySupplied,updateHeaderAtoms,Atom.effect,instructionEffect,data,Data.machine]
  refine ⟨?_,(hn 0 (by decide) (by decide) (by decide) (by decide)).trans h.2.1,
    (hn 1 (by decide) (by decide) (by decide) (by decide)).trans h.2.2.1,
    (hn 7 (by decide) (by decide) (by decide) (by decide)).trans h.2.2.2.1,h.2.2.2.2.1,by rw [hn4];omega⟩
  refine ⟨hn2,(hn 3 (by decide) (by decide) (by decide) (by decide)).trans h.1.work,?_,?_,?_,?_,h.1.realMem,h.1.natMem⟩
  · change ((updateStarted p s e).natReg 4 == 1) = false
    simp [hn4]
  · change ((updateStarted p s e).natReg 5 == 1) = false
    simp [hn5]
  · intro j
    exact h.1.realReg j
  · intro j
    by_cases hj : j = 5
    · subst j
      change (updateStarted p s e).natReg 19 = 2*e
      simp [updateStarted,externallySupplied,updateHeaderAtoms,Atom.effect,instructionEffect,data,Data.machine]
      omega
    · have h19 : shadowReg j ≠ 19 := by unfold shadowReg;omega
      change (updateStarted p s e).natReg (shadowReg j) = 2*Function.update g.natReg 5 e j
      rw [hn (shadowReg j) (by unfold shadowReg;omega) (by unfold shadowReg;omega) (by unfold shadowReg;omega) h19,Function.update_of_ne hj]
      exact h.1.natReg j
lemma Image.updateHeader {i : Input} {B : ℕ} {s : Data} {g : Machine} (h : Image i B none s g)
    (p : Program) (e : ℕ) : Image i B none (updateStarted p s e) (deletionMachine p g e) := by
  refine ⟨h.room,?_,h.threshold,h.mapping,h.values,h.flags⟩
  simpa [updateStarted,externallySupplied,updateHeaderAtoms,Atom.effect,instructionEffect,data,Data.machine] using h.limit
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s134
section s135
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s135
section s136
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s136
section s137
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s137
section s138
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s138
section s139
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured Instrumented
lemma program_query (p : Program) (c : Machine) (v : ℕ) :
    ∃ d, Ends (program p) {resume c (program p).query with natReg := Function.update c.natReg 5 v} d ∧
      d.work+6 ≤ c.work+9 ∧ d.natReg 6 = c.natMem v ∧ d.realReg 1 = c.realMem v ∧
      d.realMem = c.realMem ∧ d.natMem = c.natMem := program_query_nine (initialization p) (update p) c v
lemma program_initialization (i : Input) (hi : i.Valid) (hn : 2 ≤ i.n) (p : Program) (g : Machine)
    (hEnd : Ends p (initialMachine p (input i)) g) :
    ∃ c, Ends (program p) (initialMachine (program p) i) c ∧ Boundary i c g ∧
      c.work ≤ dispatchCost p*g.work+200*i.size := by
  obtain ⟨cb,s,hb,hcb,hrep,hImage⟩ := boot_ready i hi (program p) p
  obtain ⟨ci,t,hint,hci,htrep,htImage⟩ := interpreter_ends (action_spec i (i.n+3*i.k+2)) p s
    (initialMachine p (input i)) g hrep hImage hEnd
  have heval : Eval (initialization p) (data (initialMachine (program p) i)) (cb+ci) t := Eval.seq hb hint
  obtain ⟨c,hc,hdata,hwork⟩ := command_ends heval (program p) 0 (initialMachine (program p) i)
    (program_init _ _) rfl rfl rfl rfl (by simpa only [program,Nat.zero_add] using program_init_halt (initialization p) (update p))
  refine ⟨c,hc,?_,?_⟩
  · rw [Boundary,hdata]
    exact ⟨htrep,htImage⟩
  · change c.work = 0+(cb+ci)+1 at hwork
    change ci ≤ (charge bound p.code+2)*(g.work-0)+2 at hci
    simp only [Nat.sub_zero] at hci
    have hmul := Nat.mul_le_mul_right g.work (show charge bound p.code+2 ≤ dispatchCost p by dsimp [dispatchCost];omega)
    have hm : 2 ≤ i.size := hn.trans hi.1
    omega
lemma program_update (i : Input) (p : Program) (c g g' : Machine) (e : ℕ)
    (h : Boundary i c g) (hEnd : Ends p (deletionMachine p g e) g') :
    ∃ d, Ends (program p) (deletionMachine (program p) c e) d ∧ Boundary i d g' ∧
      d.work ≤ c.work+dispatchCost p*(g'.work-g.work)+7 := by
  let a := updateStarted p (data c) e
  have ha := updateHeader_eval p (data c) e
  have hrep := updateHeader_rep p (i.n+3*i.k+2) (data c) g e h.1
  have hImage := h.2.updateHeader p e
  obtain ⟨ci,t,hint,hci,htrep,htImage⟩ := interpreter_ends (action_spec i (i.n+3*i.k+2)) p a
    (deletionMachine p g e) g' hrep hImage hEnd
  have hstart : data (deletionMachine (program p) c e) = externallySupplied (data c) e := rfl
  have heval : Eval (update p) (data (deletionMachine (program p) c e)) (4+ci) t := by rw [hstart];exact Eval.seq ha hint
  obtain ⟨d,hd,hdata,hwork⟩ := command_ends heval (program p) (program p).update (deletionMachine (program p) c e)
    (Structured.program_update _ _) rfl rfl rfl rfl (program_update_halt _ _)
  refine ⟨d,hd,?_,?_⟩
  · rw [Boundary,hdata]
    exact ⟨htrep,htImage⟩
  · change d.work = c.work+(4+ci)+1 at hwork
    change ci ≤ (charge bound p.code+2)*(g'.work-g.work)+2 at hci
    have hmul := Nat.mul_le_mul_right (g'.work-g.work) (show charge bound p.code+2 ≤ dispatchCost p by dsimp [dispatchCost];omega)
    omega
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s139
section s140
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
lemma online (i : Input) (hi : i.Valid) (hn : 2 ≤ i.n) (p : Program)
    {sourceDs : List (Fin (input i).k)} {sourceCs : List Machine}
    (hr : OnlineRun p (input i) sourceDs sourceCs) :
    ∀ ds : List (Fin i.k), sourceDs = ds.map (oldEdge i) →
    ∃ cs c g, OnlineRun (program p) i ds cs ∧ cs.length = sourceCs.length ∧ cs.getLast? = some c ∧
      sourceCs.getLast? = some g ∧ Boundary i c g ∧
      c.work+6*ds.length ≤ dispatchCost p*(g.work+6*ds.length)+200*i.size ∧
      ∀ (j : ℕ) (c' g' : Machine), cs[j]? = some c' → sourceCs[j]? = some g' → Boundary i c' g' := by
  induction hr with
  | @init g hEnd =>
    intro ds hds
    have hd : ds = [] := List.map_eq_nil_iff.mp hds.symm
    subst ds
    obtain ⟨c,hc,hBoundary,hwork⟩ := program_initialization i hi hn p g hEnd
    refine ⟨[c],c,g,OnlineRun.init hc,rfl,rfl,rfl,hBoundary,by simpa using hwork,?_⟩
    intro j c' g' hc' hg'
    cases j with
    | zero =>
      have hec : c = c' := Option.some.inj hc'
      have heg : g = g' := Option.some.inj hg'
      subst c';subst g';exact hBoundary
    | succ j => simp at hc'
  | @next augDs augCs g g' hr hlast eAug hEnd ih =>
    intro original hds
    cases original using List.reverseRecOn with
    | nil =>
      have hh : (augDs++[eAug]).length = 0 := congrArg List.length hds
      have hbad : augDs.length+1 = 0 := (List.length_append (as := augDs) (bs := [eAug])).symm.trans hh
      omega
    | append_singleton ds e _ =>
      have hmap : augDs++[eAug] = ds.map (oldEdge i)++[oldEdge i e] := by simpa only [List.map_append,List.map_singleton] using hds
      dsimp only [input] at hmap
      have hlen : augDs.length = (ds.map (oldEdge i)).length := by
        have hleft := List.length_append (as := augDs) (bs := [eAug])
        have hright := List.length_append (as := ds.map (oldEdge i)) (bs := [oldEdge i e])
        have hh : augDs.length+1 = (ds.map (oldEdge i)).length+1 :=
          hleft.symm.trans ((congrArg List.length hmap).trans hright)
        exact Nat.add_right_cancel hh
      obtain ⟨hd,he⟩ := List.append_inj hmap hlen
      have he' : eAug = oldEdge i e := (List.cons.inj he).1
      subst eAug
      obtain ⟨cs,c,g0,hnRun,hCsLen,hLast,hSourceLast,hBoundary,hwork,hprefix⟩ := ih ds hd
      have hg0 : g0 = g := Option.some.inj (hSourceLast.symm.trans hlast)
      subst g0
      obtain ⟨d,hdEnd,hdBoundary,hdWork⟩ := program_update i p c g g' e.val hBoundary hEnd
      have hMono : g.work ≤ g'.work := hEnd.work_mono
      have hDelta : dispatchCost p*(g'.work-g.work)+dispatchCost p*g.work = dispatchCost p*g'.work := by
        rw [← Nat.mul_add,Nat.sub_add_cancel hMono]
      have hD : 3 ≤ dispatchCost p := by unfold dispatchCost;omega
      have hdBudget : d.work+6*(ds++[e]).length ≤ dispatchCost p*(g'.work+6*(ds++[e]).length)+200*i.size := by
        simp only [List.length_append,List.length_singleton,Nat.mul_add] at hwork ⊢
        omega
      refine ⟨cs++[d],d,g',OnlineRun.next hnRun hLast e hdEnd,by simp only [List.length_append,List.length_singleton,hCsLen],by simp,by simp,hdBoundary,hdBudget,?_⟩
      intro j c' g'' hc' hg''
      by_cases hj : j < cs.length
      · rw [List.getElem?_append_left hj] at hc'
        rw [List.getElem?_append_left (by omega : j < augCs.length)] at hg''
        exact hprefix j c' g'' hc' hg''
      · have hjlen : j < (cs++[d]).length := by
          by_contra hnot
          have hh : (cs++[d])[j]? = none := List.getElem?_eq_none_iff.mpr (by omega)
          rw [hh] at hc';contradiction
        have hjeq : j = cs.length := by simp only [List.length_append,List.length_singleton] at hjlen;omega
        subst j
        rw [List.getElem?_append_right le_rfl,Nat.sub_self] at hc'
        have hcEq : d = c' := Option.some.inj hc'
        subst c'
        rw [hCsLen,List.getElem?_append_right le_rfl,Nat.sub_self] at hg''
        have hgEq : g' = g'' := Option.some.inj hg''
        subst g''
        exact hdBoundary
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s140
section s141
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
lemma Boundary.correct {i : Input} {c g : Machine} (hi : i.Valid) (ds : List (Fin i.k))
    (h : Boundary i c g) (hg : Correct (input i) (ds.map (oldEdge i)) g) : Correct i ds c := by
  have hNorm : ∀ v : Fin i.n, g.natMem v.val ≤ 1 ∧ (g.natMem v.val = 0 → 0 ≤ g.realMem v.val) :=
    fun v => hg.2.1 (oldVertex i v)
  have hstored : ∀ v : Fin i.n, stored c v.val = sanitize i (stored g v.val) :=
    fun v => h.2.stored v (hNorm v).1
  have hsource : stored c i.source.val = 0 := by
    rw [hstored i.source]
    have hz : stored g i.source.val = 0 := hg.1
    rw [hz]
    simp [sanitize]
  refine ⟨hsource,h.2.normal hNorm,?_⟩
  intro v
  rw [hstored v]
  have hacc := hg.2.2 (oldVertex i v)
  have hl : distance (input i).graph (active i (live ds)) (fun e => (weight i e : ℝ≥0∞))
      (source i) (oldVertex i v) ≤ stored g v.val := by
    have hh := hacc.1
    change distance (input i).graph (live (ds.map (oldEdge i))) (fun e => (weight i e : ℝ≥0∞))
      (source i) (oldVertex i v) ≤ stored g v.val at hh
    dsimp only [input] at hh ⊢
    rwa [← active_live i ds] at hh
  have hu : stored g v.val ≤ ENNReal.ofReal (1+i.accuracy)*distance (input i).graph (active i (live ds))
      (fun e => (weight i e : ℝ≥0∞)) (source i) (oldVertex i v) := by
    have hh := hacc.2.1
    change stored g v.val ≤ ENNReal.ofReal (1+i.accuracy)*distance (input i).graph (live (ds.map (oldEdge i)))
      (fun e => (weight i e : ℝ≥0∞)) (source i) (oldVertex i v) at hh
    dsimp only [input] at hh ⊢
    rwa [← active_live i ds] at hh
  exact sanitize_correct i hi (live ds) v (stored g v.val) hl hu
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s141
section s142
set_option autoImplicit false
open Filter
open scoped Topology
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s142
section s143
set_option autoImplicit false
open Filter
open scoped Topology
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s143
section s144
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
lemma overhead_subpolynomial (a : ℕ → ℝ) (ha : Subpolynomial a) : Subpolynomial (overhead a) :=
  subpolynomial_add _ _ (subpolynomial_constant 1 (by norm_num)) (subpolynomial_rescale a ha 4 (by omega))
lemma work_arithmetic (H G M D C A eps : ℝ) (hM : 0 ≤ M) (hD : 0 ≤ D) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (heps : 0 < eps) (heps1 : eps ≤ 1) (hH : H ≤ D*G+200*M) (hG : G ≤ C*(4*M)*A/eps) :
    H ≤ (4*D*C+200)*M*(1+A)/eps := by
  have hG' := (le_div_iff₀ heps).mp hG
  have hH' := mul_le_mul_of_nonneg_right hH heps.le
  have hDG := mul_le_mul_of_nonneg_left hG' hD
  have hboot := mul_le_mul_of_nonneg_left heps1 (show 0 ≤ 200*M by positivity)
  apply (le_div_iff₀ heps).mpr
  have hDCM : 0 ≤ D*C*M := by positivity
  have hMA : 0 ≤ M*A := mul_nonneg hM hA
  nlinarith only [hH',hDG,hboot,hDCM,hMA]
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s144
section s145
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
lemma maintains (i : Input) (hi : i.Valid) (hn : 2 ≤ i.n) (p : Program) (C : ℝ) (a : ℕ → ℝ)
    (queryBound : ℕ) (hC : 0 ≤ C) (ha : Subpolynomial a) (hsource : Maintains p C a queryBound false (input i)) :
    Maintains (program p) (4*(dispatchCost p : ℝ)*C+200) (overhead a) 9 false i := by
  intro ds hlegal
  have hSourceLegal : Legal (ds.map (oldEdge i)) := List.Nodup.map (oldEdge_injective i) hlegal
  obtain ⟨sourceCs,hr,hSourceLen,hSourceCorrect,hSourceBudget,_⟩ := hsource (ds.map (oldEdge i)) hSourceLegal
  obtain ⟨cs,c,g,hnRun,hLen,hLast,hSourceLast,hBoundary,hBudget,hprefix⟩ := online i hi hn p hr ds rfl
  refine ⟨cs,hnRun,?_,?_,?_,?_⟩
  · have hmapLen : (ds.map (oldEdge i)).length = ds.length := List.length_map (oldEdge i)
    exact hLen.trans (hSourceLen.trans (congrArg (fun n : ℕ => n+1) hmapLen))
  · intro j c' hc'
    have hj : j < cs.length := (List.getElem?_eq_some_iff.mp hc').1
    have hjS : j < sourceCs.length := by omega
    let g' := sourceCs[j]
    have hg' : sourceCs[j]? = some g' := List.getElem?_eq_getElem hjS
    have hB := hprefix j c' g' hc' hg'
    have hS : Correct (input i) ((ds.take j).map (oldEdge i)) g' := by
      have hh : Correct (input i) ((ds.map (oldEdge i)).take j) g' := hSourceCorrect j g' hg'
      have htake : (ds.take j).map (oldEdge i) = (ds.map (oldEdge i)).take j := List.map_take
      exact (congrArg (fun es => Correct (input i) es g') htake).mpr hh
    exact hB.correct hi (ds.take j) hS
  · intro c' hc'
    have heq : c = c' := Option.some.inj (hLast.symm.trans hc')
    subst c'
    have hS := hSourceBudget g hSourceLast
    simp only [List.length_map,input,Bool.false_eq_true,if_false,mul_one,Nat.cast_mul,Nat.cast_ofNat] at hS
    have hR : ((c.work+6*ds.length : ℕ) : ℝ) ≤
        (dispatchCost p : ℝ)*((g.work+6*ds.length : ℕ) : ℝ)+200*(i.size : ℝ) := by exact_mod_cast hBudget
    have hw := work_arithmetic _ _ (i.size : ℝ) (dispatchCost p : ℝ) C (a (4*i.size)) i.accuracy
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) hC (ha.1 _).le hi.2.2.2.1 hi.2.2.2.2.1 hR hS
    simpa only [overhead,Bool.false_eq_true,if_false,mul_one] using hw
  · intro c' hc' v
    exact program_query p c' v.val
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s145
section s146
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
lemma Walk.incoming {n k : ℕ} {g : Digraph n k} {active : Finset (Fin k)}
    {u v : Fin n} {es : List (Fin k)} (h : Walk g active u v es) (hne : u ≠ v) :
    ∃ e, g.head e = v := by
  induction h with
  | nil v => exact False.elim (hne rfl)
  | @cons u v es e he h ih =>
    by_cases hv : g.head e = v
    · exact ⟨e, hv⟩
    · exact ih hv
lemma core_indegree_pos (b : Core) (v : Fin b.input.n) (hv : v ≠ b.input.source) :
    1 ≤ indegree b v := by
  classical
  obtain ⟨es, hw⟩ := b.initially_reachable v
  obtain ⟨e, he⟩ := hw.incoming hv.symm
  simp only [indegree, if_neg hv]
  exact Finset.one_le_card.mpr ⟨e, by simp [he]⟩
lemma core_A_ge (b : Core) : 32 ≤ A b := by
  have hm : (2 : ℝ) ≤ b.input.size := by exact_mod_cast (b.two.trans b.valid.1)
  have he := b.valid.2.2.2.1
  have he' := b.valid.2.2.2.2.1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl : 1 ≤ logarithm2 (b.input.size + 1) := by
    unfold logarithm2
    apply (le_div_iff₀ hlog2).mpr
    simpa using Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : (2 : ℝ) ≤ b.input.size + 1)
  have ha : 32 * logarithm2 (b.input.size + 1) / b.input.accuracy ≤ A b := by
    exact Nat.le_ceil _
  have h32 : 32 ≤ 32 * logarithm2 (b.input.size + 1) / b.input.accuracy := by
    apply (le_div_iff₀ he).mpr
    nlinarith
  exact h32.trans ha
lemma core_Q_ge (b : Core) : 4 * (b.input.n : ℝ) ≤ Q b := by
  have hn : (2 : ℝ) ≤ b.input.n := by exact_mod_cast b.two
  have hw : (1 : ℝ) ≤ b.input.W := by exact_mod_cast b.valid.2.2.1
  dsimp [Q, H]
  nlinarith [mul_le_mul hn hw (by norm_num : (0 : ℝ) ≤ 1) (by linarith : (0 : ℝ) ≤ b.input.n)]
lemma core_cost_bounds (b : Core) (active : Finset (Fin b.input.k)) (e : Fin b.input.k) :
    0 ≤ cost b active (.inl e) ∧ cost b active (.inl e) ≤ 1 / (8 * b.input.n) := by
  have hn : (0 : ℝ) < b.input.n := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) b.two)
  have hw : (0 : ℝ) < b.input.W := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) b.valid.2.2.1)
  have hH : 0 < H b := by dsimp [H]; positivity
  have hQ : 0 < Q b := by dsimp [Q]; positivity
  have hedge : (b.input.weight e : ℝ) ≤ H b := by
    have he : (b.input.weight e : ℝ) ≤ b.input.W := by exact_mod_cast (b.valid.2.2.2.2.2 e).2
    have hn' : (2 : ℝ) ≤ b.input.n := by exact_mod_cast b.two
    dsimp [H]
    nlinarith
  have he : cost b active (.inl e) ≤ H b / Q b := by
    simp only [cost]
    split_ifs
    · exact div_le_div_of_nonneg_right hedge hQ.le
    · exact le_rfl
  refine ⟨?_, he.trans ?_⟩
  · simp only [cost]
    split_ifs <;> positivity
  · dsimp [Q]
    field_simp
    ring_nf
    exact le_rfl
lemma core_coefficient_bounds (b : Core) (e : Edge b) :
    1 ≤ coefficient b e ∧ coefficient b e ≤ A b * b.input.size := by
  have hA : 1 ≤ A b := le_trans (by norm_num) (core_A_ge b)
  have hm : (1 : ℝ) ≤ b.input.size := by exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) (b.two.trans b.valid.1))
  cases e with
  | inl e =>
    simp only [coefficient]
    constructor
    · rfl
    · nlinarith
  | inr v =>
    have hq : (1 : ℝ) ≤ indegree b v.val := by exact_mod_cast core_indegree_pos b v.val v.property
    have hqm : (indegree b v.val : ℝ) ≤ b.input.size := by
      have hqk : indegree b v.val ≤ b.input.k := by
        simp only [indegree, if_neg v.property]
        exact (Finset.card_filter_le _ _).trans (by simp)
      exact_mod_cast hqk.trans b.valid.2.1
    simp only [coefficient]
    constructor
    · nlinarith
    · exact mul_le_mul_of_nonneg_left hqm (by linarith)
lemma core_coefficient_sum (b : Core) :
    (∑ e, coefficient b e) ≤ 2 * A b * (b.input.size : ℝ) ^ 2 := by
  have hc : Fintype.card (Edge b) ≤ 2 * b.input.size := by
    rw [Fintype.card_sum]
    have hv : Fintype.card (ReturnVertex b) ≤ b.input.n := by
      simpa only [ReturnVertex, Fintype.card_fin] using
        (Fintype.card_subtype_le (fun v : Fin b.input.n => v ≠ b.input.source))
    simpa only [Fintype.card_fin, two_mul] using Nat.add_le_add b.valid.2.1 (hv.trans b.valid.1)
  calc
    (∑ e, coefficient b e) ≤ ∑ _ : Edge b, A b * b.input.size :=
      Finset.sum_le_sum fun e _ => (core_coefficient_bounds b e).2
    _ = Fintype.card (Edge b) * (A b * b.input.size) := by simp
    _ ≤ (2 * b.input.size) * (A b * b.input.size) := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (by
        have := core_A_ge b
        positivity)
    _ = 2 * A b * (b.input.size : ℝ) ^ 2 := by ring
lemma core_kappa_bounds (b : Core) :
    0 < kappa b ∧ kappa b ≤ 1 ∧
      4 * (b.input.n : ℝ) * A b * (b.input.size : ℝ) ^ 2 * kappa b ≤ 1 := by
  have hn : (2 : ℝ) ≤ b.input.n := by exact_mod_cast b.two
  have hm : (2 : ℝ) ≤ b.input.size := by exact_mod_cast b.two.trans b.valid.1
  have hA := core_A_ge b
  have hQ := core_Q_ge b
  have hQpos : 0 < Q b := by linarith
  have hpos : 0 < A b * b.input.size * Q b := by positivity
  have hge : 1 ≤ A b * b.input.size * Q b := by
    have h1 : (1 : ℝ) ≤ A b := by linarith
    have h2 : (1 : ℝ) ≤ b.input.size := by linarith
    have h3 : (1 : ℝ) ≤ Q b := by linarith
    calc
      1 = 1 * 1 * 1 := by norm_num
      _ ≤ A b * b.input.size * Q b :=
        mul_le_mul (mul_le_mul h1 h2 (by norm_num) (by positivity)) h3 (by norm_num) (by positivity)
  have hsq : 4 * (b.input.n : ℝ) ≤ A b * (Q b) ^ 2 := by
    have hq : 1 ≤ Q b := by linarith
    have hqq : Q b ≤ (Q b) ^ 2 := by nlinarith
    have hqa : (Q b) ^ 2 ≤ A b * (Q b) ^ 2 := by nlinarith [sq_nonneg (Q b)]
    linarith
  have hbig : 4 * (b.input.n : ℝ) * A b * (b.input.size : ℝ) ^ 2 ≤
      (A b * b.input.size * Q b) ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hsq (show 0 ≤ A b * (b.input.size : ℝ) ^ 2 by positivity)
    nlinarith only [hh]
  simp only [kappa, zpow_neg, zpow_ofNat, ← one_div]
  refine ⟨by positivity, ?_, ?_⟩
  · apply (div_le_one (by positivity : (0 : ℝ) < (A b * b.input.size * Q b) ^ 2)).mpr
    nlinarith
  · rw [mul_one_div]
    exact (div_le_one (by positivity)).mpr hbig
end DecrAlmostLinearSSSP.Decremental
end s146
section s147
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s147
section s148
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s148
section s149
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s149
section s150
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s150
section s151
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s151
section s152
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s152
section s153
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s153
section s154
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s154
section s155
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s155
section s156
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s156
section s157
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s157
section s158
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s158
section s159
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s159
section s160
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s160
section s161
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s161
section s162
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s162
section s163
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s163
section s164
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s164
section s165
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s165
section s166
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s166
section s167
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s167
section s168
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s168
section s169
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s169
section s170
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s170
section s171
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s171
section s172
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s172
section s173
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s173
section s174
set_option autoImplicit false
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
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s176
section s177
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s177
section s178
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s178
section s179
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s179
section s180
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end s180
section s181
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRequest
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreRequest
end s181
section s182
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRequest
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreRequest
end s182
section s183
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s183
section s184
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s184
section s185
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.RegisterSave
open Structured
end DecrAlmostLinearSSSP.Decremental.RegisterSave
end s185
section s186
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.RegisterSave
open Structured
end DecrAlmostLinearSSSP.Decremental.RegisterSave
end s186
section s187
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.RegisterSave
open Structured
end DecrAlmostLinearSSSP.Decremental.RegisterSave
end s187
section s188
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.SourceSetup
open Structured
open RegisterSave
end DecrAlmostLinearSSSP.Decremental.SourceSetup
end s188
section s189
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end s189
section s190
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end s190
section s191
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
namespace RegisterSave
end RegisterSave
namespace SourceSetup
end SourceSetup
end DecrAlmostLinearSSSP.Decremental
end s191
section s192
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.SourceSnapshot
open Structured
open RegisterSave
end DecrAlmostLinearSSSP.Decremental.SourceSnapshot
end s192
section s193
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.SourceCall
open Structured
end DecrAlmostLinearSSSP.Decremental.SourceCall
end s193
section s194
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreSource
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreSource
end s194
section s195
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreSource
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreSource
end s195
section s196
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRequest
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreRequest
end s196
section s197
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreSource
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreSource
end s197
section s198
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRequest
end DecrAlmostLinearSSSP.Decremental.CoreRequest
end s198
section s199
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRequest
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreRequest
end s199
section s200
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CorePending
open Structured
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental.CorePending
end s200
section s201
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s201
section s202
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreMemory
end DecrAlmostLinearSSSP.Decremental.CoreMemory
end s202
section s203
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGeometry
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreGeometry
end s203
section s204
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRecord
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreRecord
end s204
section s205
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreEdgeAddress
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreEdgeAddress
end s205
section s206
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreReturnCoefficient
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreReturnCoefficient
end s206
section s207
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreDegree
open Structured
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental.CoreDegree
end s207
section s208
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact
end DecrAlmostLinearSSSP.Decremental.Exact
end s208
section s209
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact
end DecrAlmostLinearSSSP.Decremental.Exact
end s209
section s210
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact
end DecrAlmostLinearSSSP.Decremental.Exact
end s210
section s211
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact
end DecrAlmostLinearSSSP.Decremental.Exact
end s211
section s212
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact
end DecrAlmostLinearSSSP.Decremental.Exact
end s212
section s213
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact
end DecrAlmostLinearSSSP.Decremental.Exact
end s213
section s214
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact
end DecrAlmostLinearSSSP.Decremental.Exact
end s214
section s215
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreDegree
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental.CoreDegree
end s215
section s216
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreTape
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreTape
end s216
section s217
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitialDifference
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitialDifference
end s217
section s218
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s218
section s219
set_option autoImplicit false
open Filter
open scoped Topology
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s219
section s220
set_option autoImplicit false
open Filter
open scoped Topology
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s220
section s221
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact
end DecrAlmostLinearSSSP.Decremental.Exact
end s221
section s222
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Powers
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Powers
end s222
section s223
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Powers
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Powers
end s223
section s224
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Layout
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Layout
end s224
section s225
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Clear
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Clear
end s225
section s226
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild
end s226
section s227
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild
end s227
section s228
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact
open Structured
namespace Adjacency
end Adjacency
end DecrAlmostLinearSSSP.Decremental.Exact
end s228
section s229
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeHeader
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitializeHeader
end s229
section s230
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreParameters
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreParameters
end s230
section s231
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreParameters
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreParameters
end s231
section s232
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreParameters
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreParameters
end s232
section s233
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreControl
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreControl
end s233
section s234
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.InputCapture
open Structured
end DecrAlmostLinearSSSP.Decremental.InputCapture
end s234
section s235
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreControl
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreControl
end s235
section s236
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeHeader
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitializeHeader
end s236
section s237
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
end s237
section s238
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRefresh
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreRefresh
end s238
section s239
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
end s239
section s240
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
end s240
section s241
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGeometry
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreGeometry
end s241
section s242
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRecord
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreRecord
end s242
section s243
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.CoreOutput
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreOutput
end s243
section s244
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreOutput
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreOutput
end s244
section s245
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreReturn
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreReturn
end s245
section s246
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
end s246
section s247
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreNonzero
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNonzero
end s247
section s248
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGradient
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreGradient
end s248
section s249
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGradient
open Structured
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental.CoreGradient
end s249
section s250
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGradientEndpoints
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreGradientEndpoints
end s250
section s251
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGradientEndpoints
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreGradientEndpoints
end s251
section s252
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end s252
section s253
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
end s253
section s254
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
end s254
section s255
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreMemory
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreMemory
end s255
section s256
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreMemory
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreMemory
end s256
section s257
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s257
section s258
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
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
end DecrAlmostLinearSSSP.Decremental
end s260
section s261
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreControl
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreControl
end s261
section s262
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
end s262
section s263
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
end s263
section s264
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
end s264
section s265
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge
end s265
section s266
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge
end s266
section s267
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge
end s267
section s268
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeHeader
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitializeHeader
end s268
section s269
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeStore
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitializeStore
end s269
section s270
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeContributions
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitializeContributions
end s270
section s271
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end s271
section s272
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge
end s272
section s273
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge
end s273
section s274
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge
end s274
section s275
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge
end s275
section s276
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
end s276
section s277
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitialize
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitialize
end s277
section s278
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
namespace DecrAlmostLinearSSSP.Decremental.CorePending
end DecrAlmostLinearSSSP.Decremental.CorePending
end s278
section s279
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CorePending
open Structured
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental.CorePending
end s279
section s280
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CorePending
open Structured
end DecrAlmostLinearSSSP.Decremental.CorePending
end s280
section s281
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreHost
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreHost
end s281
section s282
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRequest
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreRequest
end s282
section s283
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRequest
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreRequest
end s283
section s284
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreHost
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreHost
end s284
section s285
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreHost
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreHost
end s285
section s286
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s286
section s287
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreHost
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreHost
end s287
section s288
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRequest
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreRequest
end s288
section s289
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s289
section s290
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s290
section s291
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreSource
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreSource
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s291
section s292
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreHost
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreHost
end s292
section s293
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s293
section s294
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s294
section s295
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s295
section s296
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s296
section s297
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s297
section s298
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s298
section s299
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s299
section s300
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s300
section s301
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s301
section s302
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s302
section s303
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s303
section s304
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s304
section s305
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s305
section s306
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s306
section s307
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s307
section s308
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s308
section s309
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s309
section s310
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s310
section s311
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s311
section s312
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s312
section s313
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s313
section s314
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s314
section s315
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s315
section s316
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s316
section s317
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s317
section s318
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s318
section s319
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s319
section s320
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s320
section s321
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s321
section s322
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGeometry
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreGeometry
end s322
section s323
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s323
section s324
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRefreshRead
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreRefreshRead
end s324
section s325
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRefresh
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreRefresh
end s325
section s326
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGeometry
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreGeometry
end s326
section s327
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreHost
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreHost
end s327
section s328
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGradientDelta
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreGradientDelta
end s328
section s329
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGeometry
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreGeometry
namespace DecrAlmostLinearSSSP.Decremental.CoreHost
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreHost
end s329
section s330
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreSource
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreSource
end s330
section s331
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreHost
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreHost
end s331
section s332
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreHost
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreHost
end s332
section s333
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreSource
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreSource
end s333
section s334
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreCommit
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreCommit
end s334
section s335
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGeometry
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreGeometry
end s335
section s336
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreHost
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreHost
end s336
section s337
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreCommit
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreCommit
end s337
section s338
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreCommit
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreCommit
end s338
section s339
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s339
section s340
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreHeadSelect
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreHeadSelect
end s340
section s341
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s341
section s342
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreCommit
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreCommit
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s342
section s343
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreReports
open Structured
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental.CoreReports
end s343
section s344
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreReports
open Structured
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental.CoreReports
end s344
section s345
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreReports
open Structured
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental.CoreReports
end s345
section s346
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreReports
open Structured
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental.CoreReports
end s346
section s347
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreReports
end DecrAlmostLinearSSSP.Decremental.CoreReports
end s347
section s348
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s348
section s349
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreReports
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreReports
end s349
section s350
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreSource
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreSource
end s350
section s351
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreHost
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreHost
end s351
section s352
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreReports
end DecrAlmostLinearSSSP.Decremental.CoreReports
end s352
section s353
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s353
section s354
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s354
section s355
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreCommit
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreCommit
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s355
section s356
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRatioGuard
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreRatioGuard
end s356
section s357
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRepair
end DecrAlmostLinearSSSP.Decremental.CoreRepair
end s357
section s358
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRepair
end DecrAlmostLinearSSSP.Decremental.CoreRepair
end s358
section s359
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRepair
end DecrAlmostLinearSSSP.Decremental.CoreRepair
end s359
section s360
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s360
section s361
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s361
section s362
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Repair
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Repair
end s362
section s363
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end s363
section s364
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end s364
section s365
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Repair
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Repair
end s365
section s366
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRepairControl
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreRepairControl
end s366
section s367
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s367
section s368
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreDeletion
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreDeletion
end s368
section s369
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGeometry
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreGeometry
end s369
section s370
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreHost
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreHost
end s370
section s371
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreDeletion
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreDeletion
end s371
section s372
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreDeletion
end DecrAlmostLinearSSSP.Decremental.CoreDeletion
end s372
section s373
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreHost
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreHost
end s373
section s374
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreHost
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreHost
end s374
section s375
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreDeletion
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreDeletion
end s375
section s376
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRepair
end DecrAlmostLinearSSSP.Decremental.CoreRepair
end s376
section s377
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s377
section s378
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s378
section s379
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s379
section s380
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s380
section s381
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s381
section s382
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s382
section s383
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.CoreHost
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreHost
end s383
section s384
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CutQualityNative
open Structured
end DecrAlmostLinearSSSP.Decremental.CutQualityNative
end s384
section s385
set_option autoImplicit false
open Filter
open scoped Topology
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s385
section s386
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CutQualityNative
open Structured
end DecrAlmostLinearSSSP.Decremental.CutQualityNative
end s386
section s387
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CutQualityNative
open Structured
end DecrAlmostLinearSSSP.Decremental.CutQualityNative
end s387
section s388
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CutQualityNative
open Structured
end DecrAlmostLinearSSSP.Decremental.CutQualityNative
end s388
section s389
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CutQualityNative
open Structured
end DecrAlmostLinearSSSP.Decremental.CutQualityNative
end s389
section s390
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CutQualityNative
open Structured
end DecrAlmostLinearSSSP.Decremental.CutQualityNative
end s390
section s391
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CutQualityNative
open Structured
end DecrAlmostLinearSSSP.Decremental.CutQualityNative
end s391
section s392
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CutQualityNative
open Structured
end DecrAlmostLinearSSSP.Decremental.CutQualityNative
end s392
section s393
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CutQualityNative
open Structured
end DecrAlmostLinearSSSP.Decremental.CutQualityNative
end s393
section s394
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreQuality
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreQuality
end s394
section s395
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreParameters
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreParameters
end s395
section s396
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreCeiling
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreCeiling
end s396
section s397
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreCeiling
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreCeiling
end s397
section s398
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreParameters
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreParameters
end s398
section s399
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreInitialize
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitialize
end s399
section s400
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreInitialize
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitialize
end s400
section s401
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end s401
section s402
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGuestEdge
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreGuestEdge
end s402
section s403
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGuestEdge
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreGuestEdge
end s403
section s404
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGuestGamma
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreGuestGamma
end s404
section s405
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
end s405
section s406
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
end s406
section s407
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
end s407
section s408
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
end s408
section s409
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
end s409
section s410
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
end s410
section s411
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
end s411
section s412
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
end s412
section s413
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
end s413
section s414
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Fill
open Structured
end DecrAlmostLinearSSSP.Decremental.Fill
end s414
section s415
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.SnapshotFill
open Structured
end DecrAlmostLinearSSSP.Decremental.SnapshotFill
end s415
section s416
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitialSaved
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitialSaved
end s416
section s417
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitialSaved
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitialSaved
end s417
section s418
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitialSaved
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitialSaved
end s418
section s419
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreSource
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreSource
end s419
section s420
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreHost
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreHost
end s420
section s421
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreInitialize
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitialize
end s421
section s422
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s422
section s423
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreInitialize
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitialize
end s423
section s424
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreInitialize
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreInitialize
end s424
section s425
set_option autoImplicit false
open Filter
open scoped Topology
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s425
section s426
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s426
section s427
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s427
section s428
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s428
section s429
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s429
section s430
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s430
section s431
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s431
section s432
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s432
section s433
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreRepair
end DecrAlmostLinearSSSP.Decremental.CoreRepair
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s433
section s434
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s434
section s435
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s435
section s436
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s436
section s437
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s437
section s438
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s438
section s439
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s439
section s440
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s440
section s441
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s441
section s442
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s442
theorem solution : (((((((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (B : Nat),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 88) (instOfNatNat (nat_lit 88))))
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
      @LE.le.{0} Nat instLENat B (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82)))) →
        ∀ (a : Nat),
          @LT.lt.{0} Nat instLTNat a B →
            And (@Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.Normalize.Native.recordData s).natMem a) (s.natMem a))
              (@Eq.{1} Real ((DecrAlmostLinearSSSP.Decremental.Normalize.Native.recordData s).realMem a) (s.realMem a))) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i s →
    DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i
      (DecrAlmostLinearSSSP.Decremental.Normalize.Native.fieldData s))) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i s →
    DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i
      (DecrAlmostLinearSSSP.Decremental.Normalize.Native.headData s)) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (B logical a0 a1 a2 : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (natural : Nat → Nat) (real : Nat → Real),
  DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) s
      natural real →
    DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i s →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))))
          (DecrAlmostLinearSSSP.Decremental.bankAddress B (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            logical) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 88) (instOfNatNat (nat_lit 88))))
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
          @LE.le.{0} Nat instLENat
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              B →
            @Eq.{1} Nat (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))) a0 →
              @Eq.{1} Nat
                  (s.natMem
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  a1 →
                @Eq.{1} Nat
                    (s.natMem
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    a2 →
                  DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                    (DecrAlmostLinearSSSP.Decremental.Normalize.Native.recordData s)
                    (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
                      (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
                        (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat natural logical a0)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) logical
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        (@ite.{1} Nat (@Eq.{1} Nat a1 (@Fin.val i.n i.source))
                          (instDecidableEqNat a1 (@Fin.val i.n i.source)) i.n a1))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) logical
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      a2)
                    real))) ∧ (((∀ (f : Nat → Nat) (bound : Nat),
  @Eq.{1} (Nat → Nat)
    (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
      (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
        (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
          (DecrAlmostLinearSSSP.Decremental.Normalize.natPrefix f bound) bound (f bound))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) bound
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (f
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) bound
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) bound
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (f
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) bound
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (DecrAlmostLinearSSSP.Decremental.Normalize.natPrefix f
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) bound
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (p : DecrAlmostLinearSSSP.Decremental.Program) (e : Fin i.k),
  @Eq.{1} Nat
    ((DecrAlmostLinearSSSP.Decremental.initialMachine p (DecrAlmostLinearSSSP.Decremental.Normalize.input i)).natMem
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (@Fin.val i.k e))))
    (@Fin.val i.n (@DecrAlmostLinearSSSP.Decremental.Digraph.tail i.n i.k i.graph e)))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (p : DecrAlmostLinearSSSP.Decremental.Program) (e : Fin i.k),
  @Eq.{1} Nat
    ((DecrAlmostLinearSSSP.Decremental.initialMachine p (DecrAlmostLinearSSSP.Decremental.Normalize.input i)).natMem
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (@Fin.val i.k e)))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@ite.{1} Nat
      (@Eq.{1} Nat (@Fin.val i.n (@DecrAlmostLinearSSSP.Decremental.Digraph.head i.n i.k i.graph e))
        (@Fin.val i.n i.source))
      (instDecidableEqNat (@Fin.val i.n (@DecrAlmostLinearSSSP.Decremental.Digraph.head i.n i.k i.graph e))
        (@Fin.val i.n i.source))
      i.n (@Fin.val i.n (@DecrAlmostLinearSSSP.Decremental.Digraph.head i.n i.k i.graph e)))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (p : DecrAlmostLinearSSSP.Decremental.Program) (e : Fin i.k),
  @Eq.{1} Nat
    ((DecrAlmostLinearSSSP.Decremental.initialMachine p (DecrAlmostLinearSSSP.Decremental.Normalize.input i)).natMem
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (@Fin.val i.k e)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (i.weight e)) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (p : DecrAlmostLinearSSSP.Decremental.Program) (v : Fin i.n),
  @Eq.{1} Nat
    ((DecrAlmostLinearSSSP.Decremental.initialMachine p (DecrAlmostLinearSSSP.Decremental.Normalize.input i)).natMem
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k (@Fin.val i.n v)))))
    (@Fin.val i.n i.source)))))) ∧ ((((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (p : DecrAlmostLinearSSSP.Decremental.Program) (v : Fin i.n),
  @Eq.{1} Nat
    ((DecrAlmostLinearSSSP.Decremental.initialMachine p (DecrAlmostLinearSSSP.Decremental.Normalize.input i)).natMem
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k (@Fin.val i.n v))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@ite.{1} Nat (@LT.lt.{0} Nat instLTNat (@Fin.val i.n v) (@Fin.val i.n i.source))
      ((@Fin.val i.n v).decLt (@Fin.val i.n i.source)) (@Fin.val i.n v)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Fin.val i.n v)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (p : DecrAlmostLinearSSSP.Decremental.Program) (v : Fin i.n),
  @Eq.{1} Nat
    ((DecrAlmostLinearSSSP.Decremental.initialMachine p (DecrAlmostLinearSSSP.Decremental.Normalize.input i)).natMem
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k (@Fin.val i.n v))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (DecrAlmostLinearSSSP.Decremental.Normalize.sentinel i))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (p : DecrAlmostLinearSSSP.Decremental.Program),
  @Eq.{1} (Nat → Nat)
    (DecrAlmostLinearSSSP.Decremental.Normalize.natPrefix
      (DecrAlmostLinearSSSP.Decremental.initialMachine p (DecrAlmostLinearSSSP.Decremental.Normalize.input i)).natMem
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    fun x => @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (p : DecrAlmostLinearSSSP.Decremental.Program),
  @Eq.{1} (Nat → Nat)
    (DecrAlmostLinearSSSP.Decremental.Normalize.natPrefix
      (DecrAlmostLinearSSSP.Decremental.initialMachine p (DecrAlmostLinearSSSP.Decremental.Normalize.input i)).natMem
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n))))
    (DecrAlmostLinearSSSP.Decremental.initialMachine p (DecrAlmostLinearSSSP.Decremental.Normalize.input i)).natMem))) ∧ (((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program} {B : Nat}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Normalize.Native.CopyInvariant i p B s →
    @LT.lt.{0} Nat instLTNat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 90) (instOfNatNat (nat_lit 90)))) i.k →
      DecrAlmostLinearSSSP.Decremental.Normalize.Native.CopyInvariant i p B
        (DecrAlmostLinearSSSP.Decremental.Normalize.Native.recordData s)) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program} {B : Nat}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Normalize.Native.CopyInvariant i p B s →
    ∃ cost t,
      And
        (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Normalize.Native.copyLoop s
          cost t)
        (And
          (@LE.le.{0} Nat instLENat cost
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 23) (instOfNatNat (nat_lit 23)))
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) i.k
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 90) (instOfNatNat (nat_lit 90))))))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (And (DecrAlmostLinearSSSP.Decremental.Normalize.Native.CopyInvariant i p B t)
            (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 90) (instOfNatNat (nat_lit 90)))) i.k))))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (p : DecrAlmostLinearSSSP.Decremental.Program)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i s →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 76) (instOfNatNat (nat_lit 76))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 78) (instOfNatNat (nat_lit 78))))
          (DecrAlmostLinearSSSP.Decremental.Normalize.sentinel i) →
        (∀ (j : Nat),
            @Eq.{1} Nat (s.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg j))
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
          (∀ (j : Nat),
              @Eq.{1} Real (s.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg j))
                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) →
            DecrAlmostLinearSSSP.Decremental.Normalize.Native.Registers i p
              (DecrAlmostLinearSSSP.Decremental.Normalize.Native.headerData p.initPC s)) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Normalize.Native.copyStart s
    (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
    (DecrAlmostLinearSSSP.Decremental.Normalize.Native.copyStarted s)) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  And (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.Normalize.Native.copyStarted s).natMem s.natMem)
    (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.Normalize.Native.copyStarted s).realMem s.realMem))))))) ∧ (((((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 88) (instOfNatNat (nat_lit 88))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 90) (instOfNatNat (nat_lit 90))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
            DecrAlmostLinearSSSP.Decremental.Normalize.Native.copyStart k) ∧ (∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Normalize.Native.copyStart k)) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (p : DecrAlmostLinearSSSP.Decremental.Program)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i s →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 76) (instOfNatNat (nat_lit 76))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
      (DecrAlmostLinearSSSP.Decremental.SourceMemory.Image
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) s
          (fun x => @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) fun x =>
          @OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
        (∀ (a : Nat),
            @LT.lt.{0} Nat instLTNat a
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
              @Eq.{1} Nat (s.natMem a) ((DecrAlmostLinearSSSP.Decremental.initialMachine p i).natMem a)) →
          DecrAlmostLinearSSSP.Decremental.Normalize.Native.CopyInvariant i p
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (DecrAlmostLinearSSSP.Decremental.Normalize.Native.copyStarted s)) ∧ (DecrAlmostLinearSSSP.Decremental.Structured.NoRealMemory DecrAlmostLinearSSSP.Decremental.Normalize.Native.copyLoop))) ∧ (((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  ∃ cost,
    And
      (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Normalize.Native.sentinelBody s
        cost (DecrAlmostLinearSSSP.Decremental.Normalize.Native.sentinelData s))
      (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16))))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 88) (instOfNatNat (nat_lit 88))))
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
        And
          (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.Normalize.Native.sentinelData s).natMem
            (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
              (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
                (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
                  (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natMem
                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))))
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72))))))
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (@ite.{1} Nat
                      (@LT.lt.{0} Nat instLTNat
                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 90) (instOfNatNat (nat_lit 90))))
                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72)))))
                      ((s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 90) (instOfNatNat (nat_lit 90)))).decLt
                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72)))))
                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 90) (instOfNatNat (nat_lit 90))))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 90) (instOfNatNat (nat_lit 90))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 78) (instOfNatNat (nat_lit 78))))))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 92) (instOfNatNat (nat_lit 92))))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 90) (instOfNatNat (nat_lit 90))))))
          (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.Normalize.Native.sentinelData s).realMem s.realMem))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 88) (instOfNatNat (nat_lit 88))))
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
      And
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.Normalize.Native.sentinelData s).natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))))
            (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))))
        (And
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.Normalize.Native.sentinelData s).natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 92) (instOfNatNat (nat_lit 92))))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 92) (instOfNatNat (nat_lit 92))))
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.Normalize.Native.sentinelData s).natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 90) (instOfNatNat (nat_lit 90))))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 90) (instOfNatNat (nat_lit 90))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Normalize.Native.Registers i p s →
    (∀ (k : Nat),
        @LE.le.{0} Nat instLENat k (@OfNat.ofNat.{0} Nat (nat_lit 17) (instOfNatNat (nat_lit 17))) →
          @Eq.{1} Nat (t.natReg k) (s.natReg k)) →
      (∀ (j : Nat),
          @Eq.{1} Nat (t.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg j))
            (s.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg j))) →
        @Eq.{1} (Nat → Real) t.realReg s.realReg → DecrAlmostLinearSSSP.Decremental.Normalize.Native.Registers i p t) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Normalize.Native.Registers i p s →
    DecrAlmostLinearSSSP.Decremental.Normalize.Native.Registers i p
      (DecrAlmostLinearSSSP.Decremental.Normalize.Native.copyStarted s)))))) ∧ ((((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {cost : Nat},
  DecrAlmostLinearSSSP.Decremental.Normalize.Native.Registers i p s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Normalize.Native.copyLoop s cost
        t →
      DecrAlmostLinearSSSP.Decremental.Normalize.Native.Registers i p t) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 84) (instOfNatNat (nat_lit 84))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 90) (instOfNatNat (nat_lit 90))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 92) (instOfNatNat (nat_lit 92))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
            DecrAlmostLinearSSSP.Decremental.Normalize.Native.sentinelBody k)) ∧ ((∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Normalize.Native.sentinelBody k) ∧ ((DecrAlmostLinearSSSP.Decremental.Structured.NoRealMemory DecrAlmostLinearSSSP.Decremental.Normalize.Native.sentinelBody) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i s →
    DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i
      (DecrAlmostLinearSSSP.Decremental.Normalize.Native.sentinelData s))))) ∧ (((∀ {B logical a0 a1 a2 j : Nat} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {natural : Nat → Nat}
  {real : Nat → Real},
  DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) s
      natural real →
    @Eq.{1} (Nat → Nat) t.natMem
        (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
          (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
            (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
              (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natMem
                (DecrAlmostLinearSSSP.Decremental.bankAddress B
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) logical)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a0))
              (DecrAlmostLinearSSSP.Decremental.bankAddress B
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) logical
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a1))
            (DecrAlmostLinearSSSP.Decremental.bankAddress B
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) logical
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a2))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) j))
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          j) →
      @Eq.{1} (Nat → Real) t.realMem s.realMem →
        DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) t
          (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
            (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
              (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat natural logical a0)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) logical
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              a1)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) logical
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            a2)
          real) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program} {B : Nat}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Normalize.Native.SentinelInvariant i p B s →
    @LT.lt.{0} Nat instLTNat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 90) (instOfNatNat (nat_lit 90)))) i.n →
      DecrAlmostLinearSSSP.Decremental.Normalize.Native.SentinelInvariant i p B
        (DecrAlmostLinearSSSP.Decremental.Normalize.Native.sentinelData s))) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program} {B : Nat}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Normalize.Native.SentinelInvariant i p B s →
    ∃ cost t,
      And
        (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Normalize.Native.sentinelLoop
          s cost t)
        (And
          (@LE.le.{0} Nat instLENat cost
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) i.n
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 90) (instOfNatNat (nat_lit 90))))))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (And (DecrAlmostLinearSSSP.Decremental.Normalize.Native.SentinelInvariant i p B t)
            (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 90) (instOfNatNat (nat_lit 90)))) i.n)))) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {cost : Nat},
  DecrAlmostLinearSSSP.Decremental.Normalize.Native.Registers i p s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Normalize.Native.sentinelLoop s
        cost t →
      DecrAlmostLinearSSSP.Decremental.Normalize.Native.Registers i p t) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Normalize.Native.sentinelStart s
    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
    (DecrAlmostLinearSSSP.Decremental.Normalize.Native.sentinelStarted s)))))))) ∧ ((((((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 90) (instOfNatNat (nat_lit 90))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 92) (instOfNatNat (nat_lit 92))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
        DecrAlmostLinearSSSP.Decremental.Normalize.Native.sentinelStart k) ∧ (∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Normalize.Native.sentinelStart
    k)) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (p : DecrAlmostLinearSSSP.Decremental.Program)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Normalize.Native.CopyInvariant i p
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      s →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 90) (instOfNatNat (nat_lit 90)))) i.k →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 78) (instOfNatNat (nat_lit 78))))
          (DecrAlmostLinearSSSP.Decremental.Normalize.sentinel i) →
        DecrAlmostLinearSSSP.Decremental.Normalize.Native.SentinelInvariant i p
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (DecrAlmostLinearSSSP.Decremental.Normalize.Native.sentinelStarted s)) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Normalize.Native.Registers i p s →
    DecrAlmostLinearSSSP.Decremental.Normalize.Native.Registers i p
      (DecrAlmostLinearSSSP.Decremental.Normalize.Native.sentinelStarted s)))) ∧ (((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} (entry : Nat) {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i s →
    DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i
      (DecrAlmostLinearSSSP.Decremental.Normalize.Native.headerData entry s)) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B a : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.Normalize.Native.Image i B (@Option.some.{0} Nat a) s g →
    @LT.lt.{0} Nat instLTNat a i.n →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) a))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
          DecrAlmostLinearSSSP.Decremental.ShadowDataRep B (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              s g →
            DecrAlmostLinearSSSP.Decremental.Normalize.Native.Image i B (@Option.none.{0} Nat)
              (DecrAlmostLinearSSSP.Decremental.Normalize.Native.committed s) g)) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B a : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.Normalize.Native.Image i B (@Option.some.{0} Nat a) s g →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) a))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
        DecrAlmostLinearSSSP.Decremental.ShadowDataRep B (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) s
            g →
          ∃ cost t,
            And
              (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                DecrAlmostLinearSSSP.Decremental.Normalize.Native.callback s cost t)
              (And (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))
                (And
                  (DecrAlmostLinearSSSP.Decremental.ShadowDataRep B
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) t g)
                  (DecrAlmostLinearSSSP.Decremental.Normalize.Native.Image i B (@Option.none.{0} Nat) t g)))) ∧ ((∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction) (g : DecrAlmostLinearSSSP.Decremental.Machine) (v : Nat),
  @Ne.{1} (Option.{0} Nat) (DecrAlmostLinearSSSP.Decremental.Normalize.Native.writtenAddress ins g)
      (@Option.some.{0} Nat v) →
    And (@Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.instructionEffect ins g).natMem v) (g.natMem v))
      (@Eq.{1} Real ((DecrAlmostLinearSSSP.Decremental.instructionEffect ins g).realMem v) (g.realMem v))) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B : Nat} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.Normalize.Native.Image i B (@Option.none.{0} Nat) s g →
    DecrAlmostLinearSSSP.Decremental.ShadowDataRep B (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) s g →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) B →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
          ∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction) (cost : Nat),
            DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.shadowAction ins) s cost
                t →
              DecrAlmostLinearSSSP.Decremental.Normalize.Native.Image i B
                (DecrAlmostLinearSSSP.Decremental.Normalize.Native.writtenAddress ins g) t
                (DecrAlmostLinearSSSP.Decremental.instructionEffect ins g)))))) ∧ ((((∀ {B F : Nat} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
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
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) ∧ (∀ {B F : Nat} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
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
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))) ∧ ((∀ {B F : Nat} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.Instrumented.MachineRep B F s g →
    ∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction) (cost : Nat),
      DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.shadowAction ins) s cost t →
        DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F t
            (DecrAlmostLinearSSSP.Decremental.instructionEffect ins g) →
          DecrAlmostLinearSSSP.Decremental.Instrumented.MachineRep B F t
            (DecrAlmostLinearSSSP.Decremental.instructionEffect ins g)) ∧ ((∀ {B F : Nat} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.Instrumented.MachineRep B F s g →
    ∀ (cost : Nat),
      DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Normalize.Native.callback s cost
          t →
        DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F t g →
          DecrAlmostLinearSSSP.Decremental.Instrumented.MachineRep B F t g) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (B : Nat),
  DecrAlmostLinearSSSP.Decremental.Instrumented.ActionSpec DecrAlmostLinearSSSP.Decremental.Normalize.Native.action
    DecrAlmostLinearSSSP.Decremental.Normalize.Native.bound
    (DecrAlmostLinearSSSP.Decremental.Normalize.Native.Image i B (@Option.none.{0} Nat)) B
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))) ∧ (((∀ (p : DecrAlmostLinearSSSP.Decremental.Program),
  DecrAlmostLinearSSSP.Decremental.Structured.NoRealMemory
    (DecrAlmostLinearSSSP.Decremental.Normalize.Native.bootCode p)) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (host p : DecrAlmostLinearSSSP.Decremental.Program),
      ∃ cost s,
        And
          (DecrAlmostLinearSSSP.Decremental.Structured.Eval
            (DecrAlmostLinearSSSP.Decremental.Normalize.Native.bootCode p)
            (DecrAlmostLinearSSSP.Decremental.Structured.data (DecrAlmostLinearSSSP.Decremental.initialMachine host i))
            cost s)
          (And
            (@LE.le.{0} Nat instLENat cost
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))) i.size)
                (@OfNat.ofNat.{0} Nat (nat_lit 100) (instOfNatNat (nat_lit 100)))))
            (And (DecrAlmostLinearSSSP.Decremental.Normalize.Native.Registers i p s)
              (And
                (DecrAlmostLinearSSSP.Decremental.Normalize.Native.SentinelInvariant i p
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  s)
                (@Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 90) (instOfNatNat (nat_lit 90)))) i.n)))))) ∧ ((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (i : DecrAlmostLinearSSSP.Decremental.Input) (a : Nat),
  @LT.lt.{0} Nat instLTNat a i.n →
    @Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.initialMachine p i).natMem a)
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Normalize.Native.Registers i p s →
    DecrAlmostLinearSSSP.Decremental.SourceMemory.Image
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) s
        (DecrAlmostLinearSSSP.Decremental.initialMachine p (DecrAlmostLinearSSSP.Decremental.Normalize.input i)).natMem
        (DecrAlmostLinearSSSP.Decremental.initialMachine p
            (DecrAlmostLinearSSSP.Decremental.Normalize.input i)).realMem →
      DecrAlmostLinearSSSP.Decremental.Instrumented.MachineRep
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) s
        (DecrAlmostLinearSSSP.Decremental.initialMachine p (DecrAlmostLinearSSSP.Decremental.Normalize.input i))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (host p : DecrAlmostLinearSSSP.Decremental.Program),
      ∃ cost s,
        And
          (DecrAlmostLinearSSSP.Decremental.Structured.Eval
            (DecrAlmostLinearSSSP.Decremental.Normalize.Native.bootCode p)
            (DecrAlmostLinearSSSP.Decremental.Structured.data (DecrAlmostLinearSSSP.Decremental.initialMachine host i))
            cost s)
          (And
            (@LE.le.{0} Nat instLENat cost
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))) i.size)
                (@OfNat.ofNat.{0} Nat (nat_lit 100) (instOfNatNat (nat_lit 100)))))
            (And
              (DecrAlmostLinearSSSP.Decremental.Instrumented.MachineRep
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) s
                (DecrAlmostLinearSSSP.Decremental.initialMachine p
                  (DecrAlmostLinearSSSP.Decremental.Normalize.input i)))
              (DecrAlmostLinearSSSP.Decremental.Normalize.Native.Image i
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@Option.none.{0} Nat) s
                (DecrAlmostLinearSSSP.Decremental.initialMachine p
                  (DecrAlmostLinearSSSP.Decremental.Normalize.input i))))))))))) ∧ (((((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (e : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Normalize.Native.updateHeader p)
    (DecrAlmostLinearSSSP.Decremental.Normalize.Native.externallySupplied s e)
    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
    (DecrAlmostLinearSSSP.Decremental.Normalize.Native.updateStarted p s e)) ∧ (∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (B : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data)
  (g : DecrAlmostLinearSSSP.Decremental.Machine) (e : Nat),
  DecrAlmostLinearSSSP.Decremental.Instrumented.MachineRep B
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) s g →
    DecrAlmostLinearSSSP.Decremental.Instrumented.MachineRep B
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
      (DecrAlmostLinearSSSP.Decremental.Normalize.Native.updateStarted p s e)
      (DecrAlmostLinearSSSP.Decremental.deletionMachine p g e))) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.Normalize.Native.Image i B (@Option.none.{0} Nat) s g →
    ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (e : Nat),
      DecrAlmostLinearSSSP.Decremental.Normalize.Native.Image i B (@Option.none.{0} Nat)
        (DecrAlmostLinearSSSP.Decremental.Normalize.Native.updateStarted p s e)
        (DecrAlmostLinearSSSP.Decremental.deletionMachine p g e)) ∧ (∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (v : Nat),
  ∃ d,
    And
      (DecrAlmostLinearSSSP.Decremental.Ends (DecrAlmostLinearSSSP.Decremental.Normalize.Native.program p)
        (have __src :=
          DecrAlmostLinearSSSP.Decremental.resume c (DecrAlmostLinearSSSP.Decremental.Normalize.Native.program p).query;
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
            (And (@Eq.{1} (Nat → Real) d.realMem c.realMem) (@Eq.{1} (Nat → Nat) d.natMem c.natMem)))))))) ∧ (((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) i.n →
      ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (g : DecrAlmostLinearSSSP.Decremental.Machine),
        DecrAlmostLinearSSSP.Decremental.Ends p
            (DecrAlmostLinearSSSP.Decremental.initialMachine p (DecrAlmostLinearSSSP.Decremental.Normalize.input i)) g →
          ∃ c,
            And
              (DecrAlmostLinearSSSP.Decremental.Ends (DecrAlmostLinearSSSP.Decremental.Normalize.Native.program p)
                (DecrAlmostLinearSSSP.Decremental.initialMachine
                  (DecrAlmostLinearSSSP.Decremental.Normalize.Native.program p) i)
                c)
              (And (DecrAlmostLinearSSSP.Decremental.Normalize.Native.Boundary i c g)
                (@LE.le.{0} Nat instLENat c.work
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (DecrAlmostLinearSSSP.Decremental.Normalize.Native.dispatchCost p) g.work)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 200) (instOfNatNat (nat_lit 200))) i.size))))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (p : DecrAlmostLinearSSSP.Decremental.Program)
  (c g g' : DecrAlmostLinearSSSP.Decremental.Machine) (e : Nat),
  DecrAlmostLinearSSSP.Decremental.Normalize.Native.Boundary i c g →
    DecrAlmostLinearSSSP.Decremental.Ends p (DecrAlmostLinearSSSP.Decremental.deletionMachine p g e) g' →
      ∃ d,
        And
          (DecrAlmostLinearSSSP.Decremental.Ends (DecrAlmostLinearSSSP.Decremental.Normalize.Native.program p)
            (DecrAlmostLinearSSSP.Decremental.deletionMachine
              (DecrAlmostLinearSSSP.Decremental.Normalize.Native.program p) c e)
            d)
          (And (DecrAlmostLinearSSSP.Decremental.Normalize.Native.Boundary i d g')
            (@LE.le.{0} Nat instLENat d.work
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (DecrAlmostLinearSSSP.Decremental.Normalize.Native.dispatchCost p)
                    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) g'.work g.work)))
                (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) i.n →
      ∀ (p : DecrAlmostLinearSSSP.Decremental.Program)
        {sourceDs : List.{0} (Fin (DecrAlmostLinearSSSP.Decremental.Normalize.input i).k)}
        {sourceCs : List.{0} DecrAlmostLinearSSSP.Decremental.Machine},
        DecrAlmostLinearSSSP.Decremental.OnlineRun p (DecrAlmostLinearSSSP.Decremental.Normalize.input i) sourceDs
            sourceCs →
          ∀ (ds : List.{0} (Fin i.k)),
            @Eq.{1} (List.{0} (Fin (DecrAlmostLinearSSSP.Decremental.Normalize.input i).k)) sourceDs
                (@List.map.{0, 0} (Fin i.k)
                  (Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n))
                  (DecrAlmostLinearSSSP.Decremental.Normalize.oldEdge i) ds) →
              ∃ cs c g,
                And
                  (DecrAlmostLinearSSSP.Decremental.OnlineRun
                    (DecrAlmostLinearSSSP.Decremental.Normalize.Native.program p) i ds cs)
                  (And
                    (@Eq.{1} Nat (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Machine cs)
                      (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Machine sourceCs))
                    (And
                      (@Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Machine)
                        (@List.getLast?.{0} DecrAlmostLinearSSSP.Decremental.Machine cs)
                        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Machine c))
                      (And
                        (@Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Machine)
                          (@List.getLast?.{0} DecrAlmostLinearSSSP.Decremental.Machine sourceCs)
                          (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Machine g))
                        (And (DecrAlmostLinearSSSP.Decremental.Normalize.Native.Boundary i c g)
                          (And
                            (@LE.le.{0} Nat instLENat
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                                  (@List.length.{0} (Fin i.k) ds)))
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (DecrAlmostLinearSSSP.Decremental.Normalize.Native.dispatchCost p)
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.work
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                                      (@List.length.{0} (Fin i.k) ds))))
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 200) (instOfNatNat (nat_lit 200))) i.size)))
                            (∀ (j : Nat) (c' g' : DecrAlmostLinearSSSP.Decremental.Machine),
                              @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Machine)
                                  (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Machine) Nat
                                    DecrAlmostLinearSSSP.Decremental.Machine
                                    (fun as i =>
                                      @LT.lt.{0} Nat instLTNat i
                                        (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Machine as))
                                    (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Machine) cs j)
                                  (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Machine c') →
                                @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Machine)
                                    (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Machine)
                                      Nat DecrAlmostLinearSSSP.Decremental.Machine
                                      (fun as i =>
                                        @LT.lt.{0} Nat instLTNat i
                                          (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Machine as))
                                      (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Machine)
                                      sourceCs j)
                                    (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Machine g') →
                                  DecrAlmostLinearSSSP.Decremental.Normalize.Native.Boundary i c' g'))))))) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  i.Valid →
    ∀ (ds : List.{0} (Fin i.k)),
      DecrAlmostLinearSSSP.Decremental.Normalize.Native.Boundary i c g →
        DecrAlmostLinearSSSP.Decremental.Normalize.Native.Correct (DecrAlmostLinearSSSP.Decremental.Normalize.input i)
            (@List.map.{0, 0} (Fin i.k) (Fin (DecrAlmostLinearSSSP.Decremental.Normalize.input i).k)
              (DecrAlmostLinearSSSP.Decremental.Normalize.oldEdge i) ds)
            g →
          DecrAlmostLinearSSSP.Decremental.Normalize.Native.Correct i ds c) ∧ (∀ (a : Nat → Real),
  DecrAlmostLinearSSSP.Decremental.Subpolynomial a →
    DecrAlmostLinearSSSP.Decremental.Subpolynomial (DecrAlmostLinearSSSP.Decremental.Normalize.Native.overhead a)))))) ∧ ((((∀ (H G M D C A eps : Real),
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) M →
    @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) D →
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C →
        @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) A →
          @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) eps →
            @LE.le.{0} Real Real.instLE eps (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
              @LE.le.{0} Real Real.instLE H
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) D G)
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@OfNat.ofNat.{0} Real (nat_lit 200)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 200) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat
                            (@OfNat.ofNat.{0} Nat (nat_lit 199) (instOfNatNat (nat_lit 199)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 198) (instOfNatNat (nat_lit 198)))))))
                      M)) →
                @LE.le.{0} Real Real.instLE G
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@OfNat.ofNat.{0} Real (nat_lit 4)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                            M))
                        A)
                      eps) →
                  @LE.le.{0} Real Real.instLE H
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                (@OfNat.ofNat.{0} Real (nat_lit 4)
                                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                                    (@Nat.instAtLeastTwoHAddOfNat
                                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                      (@Nat.instNeZeroSucc
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                                D)
                              C)
                            (@OfNat.ofNat.{0} Real (nat_lit 200)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 200) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 199) (instOfNatNat (nat_lit 199)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 198) (instOfNatNat (nat_lit 198))))))))
                          M)
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) A))
                      eps)) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) i.n →
      ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (C : Real) (a : Nat → Real) (queryBound : Nat),
        @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C →
          DecrAlmostLinearSSSP.Decremental.Subpolynomial a →
            DecrAlmostLinearSSSP.Decremental.Maintains p C a queryBound Bool.false
                (DecrAlmostLinearSSSP.Decremental.Normalize.input i) →
              DecrAlmostLinearSSSP.Decremental.Maintains (DecrAlmostLinearSSSP.Decremental.Normalize.Native.program p)
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@OfNat.ofNat.{0} Real (nat_lit 4)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                      (@Nat.cast.{0} Real Real.instNatCast
                        (DecrAlmostLinearSSSP.Decremental.Normalize.Native.dispatchCost p)))
                    C)
                  (@OfNat.ofNat.{0} Real (nat_lit 200)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 200) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 199) (instOfNatNat (nat_lit 199)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 198) (instOfNatNat (nat_lit 198))))))))
                (DecrAlmostLinearSSSP.Decremental.Normalize.Native.overhead a)
                (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) Bool.false i)) ∧ ((∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {u v : Fin n}
  {es : List.{0} (Fin k)},
  @DecrAlmostLinearSSSP.Decremental.Walk n k g active u v es →
    @Ne.{1} (Fin n) u v → ∃ e, @Eq.{1} (Fin n) (@DecrAlmostLinearSSSP.Decremental.Digraph.head n k g e) v) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (v : Fin b.input.n),
  @Ne.{1} (Fin b.input.n) v b.input.source →
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (DecrAlmostLinearSSSP.Decremental.indegree b v)) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core),
  @LE.le.{0} Real Real.instLE
    (@OfNat.ofNat.{0} Real (nat_lit 32)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
    (DecrAlmostLinearSSSP.Decremental.A b))))) ∧ (((∀ (b : DecrAlmostLinearSSSP.Decremental.Core),
  @LE.le.{0} Real Real.instLE
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real (nat_lit 4)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
      (@Nat.cast.{0} Real Real.instNatCast b.input.n))
    (DecrAlmostLinearSSSP.Decremental.Q b)) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (active : Finset.{0} (Fin b.input.k)) (e : Fin b.input.k),
  And
    (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (DecrAlmostLinearSSSP.Decremental.cost b active
        (@Sum.inl.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) e)))
    (@LE.le.{0} Real Real.instLE
      (DecrAlmostLinearSSSP.Decremental.cost b active
        (@Sum.inl.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) e))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real (nat_lit 8)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))
          (@Nat.cast.{0} Real Real.instNatCast b.input.n)))))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (e : DecrAlmostLinearSSSP.Decremental.Edge b),
  And
    (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
      (DecrAlmostLinearSSSP.Decremental.coefficient b e))
    (@LE.le.{0} Real Real.instLE (DecrAlmostLinearSSSP.Decremental.coefficient b e)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (DecrAlmostLinearSSSP.Decremental.A b)
        (@Nat.cast.{0} Real Real.instNatCast b.input.size)))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core),
  @LE.le.{0} Real Real.instLE (∑ e, DecrAlmostLinearSSSP.Decremental.coefficient b e)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (DecrAlmostLinearSSSP.Decremental.A b))
      (@HPow.hPow.{0, 0, 0} Real Nat Real
        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
        (@Nat.cast.{0} Real Real.instNatCast b.input.size)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core),
  And
    (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (DecrAlmostLinearSSSP.Decremental.kappa b))
    (And
      (@LE.le.{0} Real Real.instLE (DecrAlmostLinearSSSP.Decremental.kappa b)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      (@LE.le.{0} Real Real.instLE
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@OfNat.ofNat.{0} Real (nat_lit 4)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                (@Nat.cast.{0} Real Real.instNatCast b.input.n))
              (DecrAlmostLinearSSSP.Decremental.A b))
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
              (@Nat.cast.{0} Real Real.instNatCast b.input.size)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (DecrAlmostLinearSSSP.Decremental.kappa b))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))))))))) := by
  exact ⟨⟨⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Normalize.Native.record_prefix,DecrAlmostLinearSSSP.Decremental.Normalize.Native.field_captured⟩,⟨DecrAlmostLinearSSSP.Decremental.Normalize.Native.head_captured,DecrAlmostLinearSSSP.Decremental.Normalize.Native.record_image⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Normalize.natPrefix_step_three,DecrAlmostLinearSSSP.Decremental.Normalize.initial_old_tail⟩,⟨DecrAlmostLinearSSSP.Decremental.Normalize.initial_old_head,⟨DecrAlmostLinearSSSP.Decremental.Normalize.initial_old_weight,DecrAlmostLinearSSSP.Decremental.Normalize.initial_added_tail⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Normalize.initial_added_head,DecrAlmostLinearSSSP.Decremental.Normalize.initial_added_weight⟩,⟨DecrAlmostLinearSSSP.Decremental.Normalize.initial_prefix_zero,DecrAlmostLinearSSSP.Decremental.Normalize.initial_prefix_full⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Normalize.Native.CopyInvariant.step,DecrAlmostLinearSSSP.Decremental.Normalize.Native.CopyInvariant.copy_loop⟩,⟨DecrAlmostLinearSSSP.Decremental.Normalize.Native.header_registers,⟨DecrAlmostLinearSSSP.Decremental.Normalize.Native.copyStart_eval,DecrAlmostLinearSSSP.Decremental.Normalize.Native.copyStart_memory⟩⟩⟩⟩⟩,⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Normalize.Native.copyStart_nat_frame,DecrAlmostLinearSSSP.Decremental.Normalize.Native.copyStart_real_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.Normalize.Native.copyStart_invariant,DecrAlmostLinearSSSP.Decremental.Normalize.Native.copyLoop_no_real_memory⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Normalize.Native.sentinel_eval,DecrAlmostLinearSSSP.Decremental.Normalize.Native.sentinel_memory⟩,⟨DecrAlmostLinearSSSP.Decremental.Normalize.Native.sentinel_pointers,⟨DecrAlmostLinearSSSP.Decremental.Normalize.Native.Registers.frame,DecrAlmostLinearSSSP.Decremental.Normalize.Native.Registers.copyStart⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Normalize.Native.Registers.copyLoop,DecrAlmostLinearSSSP.Decremental.Normalize.Native.sentinel_nat_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.Normalize.Native.sentinel_real_frame,⟨DecrAlmostLinearSSSP.Decremental.Normalize.Native.sentinel_no_real_memory,DecrAlmostLinearSSSP.Decremental.Normalize.Native.sentinel_captured⟩⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.SourceMemory.Image.three_with_mapping,DecrAlmostLinearSSSP.Decremental.Normalize.Native.SentinelInvariant.step⟩,⟨DecrAlmostLinearSSSP.Decremental.Normalize.Native.SentinelInvariant.loop,⟨DecrAlmostLinearSSSP.Decremental.Normalize.Native.Registers.sentinelLoop,DecrAlmostLinearSSSP.Decremental.Normalize.Native.sentinelStart_eval⟩⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Normalize.Native.sentinelStart_nat_frame,DecrAlmostLinearSSSP.Decremental.Normalize.Native.sentinelStart_real_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.Normalize.Native.sentinelStart_invariant,DecrAlmostLinearSSSP.Decremental.Normalize.Native.Registers.sentinelStart⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Normalize.Native.header_captured,DecrAlmostLinearSSSP.Decremental.Normalize.Native.Image.commit⟩,⟨DecrAlmostLinearSSSP.Decremental.Normalize.Native.callback_image,⟨DecrAlmostLinearSSSP.Decremental.Normalize.Native.source_memory_away,DecrAlmostLinearSSSP.Decremental.Normalize.Native.Image.action⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.shadow_store_address,DecrAlmostLinearSSSP.Decremental.shadow_storeN_address⟩,⟨DecrAlmostLinearSSSP.Decremental.Normalize.Native.shadow_machine_rep,⟨DecrAlmostLinearSSSP.Decremental.Normalize.Native.callback_machine_rep,DecrAlmostLinearSSSP.Decremental.Normalize.Native.action_spec⟩⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Normalize.Native.boot_no_real_memory,DecrAlmostLinearSSSP.Decremental.Normalize.Native.boot_eval⟩,⟨DecrAlmostLinearSSSP.Decremental.Normalize.Native.initial_nat_below,⟨DecrAlmostLinearSSSP.Decremental.Normalize.Native.Registers.machine_rep,DecrAlmostLinearSSSP.Decremental.Normalize.Native.boot_ready⟩⟩⟩⟩⟩,⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Normalize.Native.updateHeader_eval,DecrAlmostLinearSSSP.Decremental.Normalize.Native.updateHeader_rep⟩,⟨DecrAlmostLinearSSSP.Decremental.Normalize.Native.Image.updateHeader,DecrAlmostLinearSSSP.Decremental.Normalize.Native.program_query⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Normalize.Native.program_initialization,DecrAlmostLinearSSSP.Decremental.Normalize.Native.program_update⟩,⟨DecrAlmostLinearSSSP.Decremental.Normalize.Native.online,⟨DecrAlmostLinearSSSP.Decremental.Normalize.Native.Boundary.correct,DecrAlmostLinearSSSP.Decremental.Normalize.Native.overhead_subpolynomial⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Normalize.Native.work_arithmetic,DecrAlmostLinearSSSP.Decremental.Normalize.Native.maintains⟩,⟨DecrAlmostLinearSSSP.Decremental.Walk.incoming,⟨DecrAlmostLinearSSSP.Decremental.core_indegree_pos,DecrAlmostLinearSSSP.Decremental.core_A_ge⟩⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.core_Q_ge,DecrAlmostLinearSSSP.Decremental.core_cost_bounds⟩,⟨DecrAlmostLinearSSSP.Decremental.core_coefficient_bounds,⟨DecrAlmostLinearSSSP.Decremental.core_coefficient_sum,DecrAlmostLinearSSSP.Decremental.core_kappa_bounds⟩⟩⟩⟩⟩⟩⟩
