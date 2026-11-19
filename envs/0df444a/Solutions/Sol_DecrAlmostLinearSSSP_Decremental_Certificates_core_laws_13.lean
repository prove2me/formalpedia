-- Prove2me | solution 1 for DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_13
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T17:36:37.080877+00:00
-- url     : https://prove2.me/submissions/41b58cad-6f25-4a06-8f85-cd83a0df40e5

import Definitions.Def_DecrAlmostLinearSSSP_CoreRAMFoundation
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_2
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_3
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_4
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_5
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_6
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_7
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_8
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
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_normal_laws_13
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_core_laws_1
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_core_laws_2
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_core_laws_3
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_core_laws_4
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_core_laws_5
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_core_laws_6
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_core_laws_7
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_core_laws_8
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_core_laws_9
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_core_laws_10
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_core_laws_11
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_core_laws_12
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
theorem DecrAlmostLinearSSSP.Decremental.log_size_positive : ∀ (m : Nat),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
    (Real.log
      (@Nat.cast.{0} Real Real.instNatCast
        (@Max.max.{0} Nat Nat.instMax (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.1.2.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.subpolynomial_constant : ∀ (c : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) c →
    DecrAlmostLinearSSSP.Decremental.Subpolynomial fun x => c := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.1.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.subpolynomial_mul : ∀ (a b : Nat → Real),
  DecrAlmostLinearSSSP.Decremental.Subpolynomial a →
    DecrAlmostLinearSSSP.Decremental.Subpolynomial b →
      DecrAlmostLinearSSSP.Decremental.Subpolynomial fun m =>
        @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (a m) (b m) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.1.2.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.subpolynomial_add : ∀ (a b : Nat → Real),
  DecrAlmostLinearSSSP.Decremental.Subpolynomial a →
    DecrAlmostLinearSSSP.Decremental.Subpolynomial b →
      DecrAlmostLinearSSSP.Decremental.Subpolynomial fun m =>
        @HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (a m) (b m) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.1.2.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.subpolynomial_log_size : DecrAlmostLinearSSSP.Decremental.Subpolynomial fun m =>
  Real.log
    (@Nat.cast.{0} Real Real.instNatCast
      (@Max.max.{0} Nat Nat.instMax (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.1.2.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.subpolynomial_pow : ∀ (a : Nat → Real),
  DecrAlmostLinearSSSP.Decremental.Subpolynomial a →
    ∀ (k : Nat),
      DecrAlmostLinearSSSP.Decremental.Subpolynomial fun m =>
        @HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) (a m) k := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.1.2.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.height_spec : ∀ (bound : Nat),
  @LT.lt.{0} Nat instLTNat bound
    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
      (DecrAlmostLinearSSSP.Decremental.Exact.height bound)) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.1.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.Powers.Prefix.step : ∀ {bound base d : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Powers.Prefix bound base d s →
    DecrAlmostLinearSSSP.Decremental.Exact.Powers.Prefix bound base
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (DecrAlmostLinearSSSP.Decremental.Exact.Powers.advanced s) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.1.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.ShadowRep.real_memory : ∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) F →
      ∀ (a : Nat) (x : Real),
        DecrAlmostLinearSSSP.Decremental.ShadowRep base F
          { pc := c.pc, realReg := c.realReg, natReg := c.natReg,
            realMem :=
              @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat c.realMem
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                x,
            natMem := c.natMem, halted := c.halted, fault := c.fault, work := c.work }
          { pc := g.pc, realReg := g.realReg, natReg := g.natReg,
            realMem := @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat g.realMem a x, natMem := g.natMem,
            halted := g.halted, fault := g.fault, work := g.work } := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.2.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.ShadowRep.nat_memory : ∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) F →
      ∀ (a x : Nat),
        DecrAlmostLinearSSSP.Decremental.ShadowRep base F
          { pc := c.pc, realReg := c.realReg, natReg := c.natReg, realMem := c.realMem,
            natMem :=
              @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat c.natMem
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F x),
            halted := c.halted, fault := c.fault, work := c.work }
          { pc := g.pc, realReg := g.realReg, natReg := g.natReg, realMem := g.realMem,
            natMem := @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat g.natMem a x, halted := g.halted,
            fault := g.fault, work := g.work } := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.2.2.1.2.2.2
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
theorem DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.edge_nat_frame : ∀
  j ∉
    @Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
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
                        (@OfNat.ofNat.{0} Nat (nat_lit 314) (instOfNatNat (nat_lit 314)))))))))))),
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.edge j := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_6.1.2.2.1.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory.edgeBody : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)} {tentative : Fin i.n → Option.{0} Nat}
  {settled : Finset.{0} (Fin i.n)}
  {tree :
    DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled tree queue s →
    ∀ (e : Fin i.k) (key : Nat),
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 308) (instOfNatNat (nat_lit 308))))
          (@DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.nodeAddress
            (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.layout i) i.k e) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 304) (instOfNatNat (nat_lit 304)))) key →
          @LT.lt.{0} Nat instLTNat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) key (i.weight e))
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)) →
            have r :=
              @DecrAlmostLinearSSSP.Decremental.Exact.relax i.n i.k i.graph
                (@DecrAlmostLinearSSSP.Decremental.live i.k deleted) i.weight settled key e tentative queue;
            ∃ cost t next,
              And
                (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.edgeBody s cost t)
                (And
                  (@LE.le.{0} Nat instLENat cost
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80)))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                  (And
                    (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted
                      (@Prod.fst.{0, 0} (Fin i.n → Option.{0} Nat) (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))) r) settled
                      next (@Prod.snd.{0, 0} (Fin i.n → Option.{0} Nat) (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))) r) t)
                    (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 308) (instOfNatNat (nat_lit 308))))
                      (@DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.root
                        (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.layout i) i.k
                        (@DecrAlmostLinearSSSP.Decremental.Exact.adjacency i.n i.k i.graph (@Fin.val i.k e)
                          (@DecrAlmostLinearSSSP.Decremental.Digraph.tail i.n i.k i.graph e)))))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_7.2.2.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory.edgeLoop : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)} {tentative : Fin i.n → Option.{0} Nat}
  {settled : Finset.{0} (Fin i.n)}
  {tree :
    DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled tree queue s →
    ∀ (key : Nat) (es : List.{0} (Fin i.k)),
      @DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.Chain i.k
          (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.layout i) s es →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 308) (instOfNatNat (nat_lit 308))))
            (@DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.root
              (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.layout i) i.k es) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 304) (instOfNatNat (nat_lit 304)))) key →
            (∀ (e : Fin i.k),
                @Membership.mem.{0, 0} (Fin i.k) (List.{0} (Fin i.k)) (@List.instMembership.{0} (Fin i.k)) es e →
                  @LT.lt.{0} Nat instLTNat
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) key (i.weight e))
                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                      (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i))) →
              have r :=
                @DecrAlmostLinearSSSP.Decremental.Exact.scanEdges i.n i.k i.graph
                  (@DecrAlmostLinearSSSP.Decremental.live i.k deleted) i.weight settled key es tentative queue;
              ∃ cost t next,
                And
                  (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                    DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.edgeLoop s cost t)
                  (And
                    (@LE.le.{0} Nat instLENat cost
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82)))
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                          (@List.length.{0} (Fin i.k) es))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (And
                      (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted
                        (@Prod.fst.{0, 0} (Fin i.n → Option.{0} Nat) (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))) r)
                        settled next
                        (@Prod.snd.{0, 0} (Fin i.n → Option.{0} Nat) (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))) r) t)
                      (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 308) (instOfNatNat (nat_lit 308))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_7.2.2.2.1.1.1
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
theorem DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory.ready : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)} {tentative : Fin i.n → Option.{0} Nat}
  {settled : Finset.{0} (Fin i.n)}
  {tree :
    DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled tree queue s →
    DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Ready i deleted s := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_8.1.2.1.2.1.1
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
theorem DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.initialize_eval : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
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
                                    v)))))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_8.2.1.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Ready.external : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Ready i deleted s →
    ∀ (index : Nat),
      DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Ready i deleted
        { realReg := s.realReg,
          natReg :=
            @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) index,
          realMem := s.realMem, natMem := s.natMem } := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_8.2.1.2.2.1.2
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
theorem DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Completed.ready : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)}
  {c : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Completed i deleted c →
    DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Ready i deleted (DecrAlmostLinearSSSP.Decremental.Structured.data c) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_8.2.2.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.OnlineRun.length : ∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {i : DecrAlmostLinearSSSP.Decremental.Input} {ds : List.{0} (Fin i.k)}
  {cs : List.{0} DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.OnlineRun p i ds cs →
    @Eq.{1} Nat (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Machine cs)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_8.2.2.1.2.2.2.2
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
theorem DecrAlmostLinearSSSP.Decremental.PreservesOutside.trans : ∀ {base F : Nat} {c d e : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.PreservesOutside base F c d →
    DecrAlmostLinearSSSP.Decremental.PreservesOutside base F d e →
      DecrAlmostLinearSSSP.Decremental.PreservesOutside base F c e := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_2.1.1.1.1.2.2
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
theorem DecrAlmostLinearSSSP.Decremental.ScaleParameters.fields_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.ScaleParameters.writeFields s
    (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
    (DecrAlmostLinearSSSP.Decremental.ScaleParameters.fieldData s) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_3.2.1.2.1.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.Native.BankFrame.seq : ∀ {a b : DecrAlmostLinearSSSP.Decremental.Structured.Cmd},
  DecrAlmostLinearSSSP.Decremental.Native.BankFrame a →
    DecrAlmostLinearSSSP.Decremental.Native.BankFrame b → DecrAlmostLinearSSSP.Decremental.Native.BankFrame (a.seq b) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_6.1.1.2.2.1.1
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
theorem DecrAlmostLinearSSSP.Decremental.Native.RecordImage.source_frame : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {j B record cache next N : Nat}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.RecordImage i j record cache next s →
    (∃ r,
        @Eq.{1} Nat record
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
      (∀ (address : Nat),
          (∀ (a : Nat),
              @Ne.{1} Nat address
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (DecrAlmostLinearSSSP.Decremental.bankFactor j)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) →
            @Ne.{1} Nat address
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record
                  (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))) →
              (∀ (r : Nat),
                  @LT.lt.{0} Nat instLTNat r N →
                    @Ne.{1} Nat address
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record
                          (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))) →
                And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                  (@Eq.{1} Real (t.realMem address) (s.realMem address))) →
        DecrAlmostLinearSSSP.Decremental.Native.RecordImage i j record cache next t := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_6.2.2.1.2.2.2.2
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
theorem DecrAlmostLinearSSSP.Decremental.Native.CacheImage.initial : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {j cache : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {g : DecrAlmostLinearSSSP.Decremental.Machine},
  i.Valid →
    (∀ (v : Fin i.n),
        And
          (@Eq.{1} Nat
            (s.natMem
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cache
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val i.n v))))
            (g.natMem (@Fin.val i.n v)))
          (And
            (@Eq.{1} Real
              (s.realMem
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cache
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val i.n v))))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (DecrAlmostLinearSSSP.Decremental.delta i j) (g.realMem (@Fin.val i.n v))))
            (@Eq.{1} ENNReal
              (DecrAlmostLinearSSSP.Decremental.ExtendedMax.cell s
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cache
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val i.n v))))
              (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                (@instHMul.{0} ENNReal
                  (@Distrib.toMul.{0} ENNReal
                    (@instDistribOfSemiring.{0} ENNReal
                      (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                (ENNReal.ofReal (DecrAlmostLinearSSSP.Decremental.delta i j))
                (DecrAlmostLinearSSSP.Decremental.stored g (@Fin.val i.n v)))))) →
      (∀ (v : Fin i.n),
          And
            (@LE.le.{0} Nat instLENat (g.natMem (@Fin.val i.n v))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@Eq.{1} Nat (g.natMem (@Fin.val i.n v)) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
              @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                (g.realMem (@Fin.val i.n v)))) →
        DecrAlmostLinearSSSP.Decremental.Native.CacheImage i j cache
          (fun v => DecrAlmostLinearSSSP.Decremental.stored g (@Fin.val i.n v)) s := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_7.1.2.1.1.1.2
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
theorem DecrAlmostLinearSSSP.Decremental.DirtyMark.prefix_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.DirtyMark.prefixCode s
    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
    (DecrAlmostLinearSSSP.Decremental.DirtyMark.prefixData s) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_8.2.1.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.DirtyMark.prefix_fields : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  And
    (@Eq.{1} Nat
      ((DecrAlmostLinearSSSP.Decremental.DirtyMark.prefixData s).natReg
        (@OfNat.ofNat.{0} Nat (nat_lit 184) (instOfNatNat (nat_lit 184))))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 98) (instOfNatNat (nat_lit 98))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94)))))))
    (And
      (@Eq.{1} Nat
        ((DecrAlmostLinearSSSP.Decremental.DirtyMark.prefixData s).natReg
          (@OfNat.ofNat.{0} Nat (nat_lit 188) (instOfNatNat (nat_lit 188))))
        (s.natMem
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 98) (instOfNatNat (nat_lit 98))))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94))))))))
      (∀ (k : Nat),
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 186) (instOfNatNat (nat_lit 186))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 184) (instOfNatNat (nat_lit 184))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 188) (instOfNatNat (nat_lit 188))) →
              @Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.DirtyMark.prefixData s).natReg k) (s.natReg k))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_8.2.1.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.DirtyMark.prefix_memory : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  And (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.DirtyMark.prefixData s).natMem s.natMem)
    (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.DirtyMark.prefixData s).realMem s.realMem) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_8.2.1.1.1.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.Native.PointerBases.body : ∀ {record pointer flags list cost : Nat} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.PointerBases record pointer flags list s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Native.pointerBody s cost t →
      DecrAlmostLinearSSSP.Decremental.Native.PointerBases record pointer flags list t := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_8.2.2.1.1.1.1
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
theorem DecrAlmostLinearSSSP.Decremental.SelectedRead.prefix_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.SelectedRead.prefixCode s
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    (DecrAlmostLinearSSSP.Decremental.SelectedRead.prefixData s) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_9.1.1.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.SelectedRead.prefix_fields : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  And
    (@Eq.{1} Nat
      ((DecrAlmostLinearSSSP.Decremental.SelectedRead.prefixData s).natReg
        (@OfNat.ofNat.{0} Nat (nat_lit 38) (instOfNatNat (nat_lit 38))))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94))))))
    (And
      (@Eq.{1} Nat
        ((DecrAlmostLinearSSSP.Decremental.SelectedRead.prefixData s).natReg
          (@OfNat.ofNat.{0} Nat (nat_lit 196) (instOfNatNat (nat_lit 196))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 96) (instOfNatNat (nat_lit 96))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94)))))))
      (∀ (k : Nat),
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 38) (instOfNatNat (nat_lit 38))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 196) (instOfNatNat (nat_lit 196))) →
            @Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.SelectedRead.prefixData s).natReg k) (s.natReg k))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_9.1.1.2.1.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.SelectedRead.fields : ∀ {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {cost : Nat},
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.SelectedRead.code s cost t →
      And
        (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))))
          (DecrAlmostLinearSSSP.Decremental.SelectedRead.flag s))
        (@Eq.{1} Real (t.realReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))))
          (DecrAlmostLinearSSSP.Decremental.SelectedRead.realValue s)) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_9.1.1.2.2.2.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.fields_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.fields s
    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
    (DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.fieldData s) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_11.1.1.1.1.2.2
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
theorem DecrAlmostLinearSSSP.Decremental.Native.UpdateHeader.fields : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (j record cache next : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106)))) record →
    DecrAlmostLinearSSSP.Decremental.Native.RecordImage i j record cache next s →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
        And
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.Native.UpdateHeader.result s).natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))))
            (DecrAlmostLinearSSSP.Decremental.bankFactor j))
          (And
            (@Eq.{1} Nat
              ((DecrAlmostLinearSSSP.Decremental.Native.UpdateHeader.result s).natReg
                (@OfNat.ofNat.{0} Nat (nat_lit 108) (instOfNatNat (nat_lit 108))))
              cache)
            (And
              (@Eq.{1} Real
                ((DecrAlmostLinearSSSP.Decremental.Native.UpdateHeader.result s).realReg
                  (@OfNat.ofNat.{0} Nat (nat_lit 70) (instOfNatNat (nat_lit 70))))
                (DecrAlmostLinearSSSP.Decremental.delta i j))
              (And
                (@Eq.{1} Nat
                  ((DecrAlmostLinearSSSP.Decremental.Native.UpdateHeader.result s).natReg
                    (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record
                    (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))
                (And
                  (DecrAlmostLinearSSSP.Decremental.ReportLog
                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 92) (instOfNatNat (nat_lit 92)))) (@List.nil.{0} Nat)
                    (DecrAlmostLinearSSSP.Decremental.Native.UpdateHeader.result s))
                  (@Eq.{1} Nat
                    ((DecrAlmostLinearSSSP.Decremental.Native.UpdateHeader.result s).natReg
                      (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_11.2.1.2.1.2.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.ObservedSourceCall.snapshot : ∀ (N B bank start : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data)
  (g : DecrAlmostLinearSSSP.Decremental.Machine) (reports : List.{0} Nat),
  DecrAlmostLinearSSSP.Decremental.ShadowDataRep B (DecrAlmostLinearSSSP.Decremental.bankFactor bank) s g →
    DecrAlmostLinearSSSP.Decremental.ReportLog start reports s →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
            (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) →
        (∃ r,
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
          @LT.lt.{0} Nat instLTNat
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) N
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
              start →
            ∃ t,
              And
                (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                  (DecrAlmostLinearSSSP.Decremental.SourceSnapshot.code N) s
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) N)
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                  t)
                (And
                  (DecrAlmostLinearSSSP.Decremental.ShadowDataRep B (DecrAlmostLinearSSSP.Decremental.bankFactor bank) t
                    g)
                  (And (DecrAlmostLinearSSSP.Decremental.ReportLog start reports t)
                    (And
                      (@Eq.{1} Nat
                        (t.natMem
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
                            (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
                        g.work)
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
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (DecrAlmostLinearSSSP.Decremental.bankFactor bank) (g.natReg j)))
                              (@Eq.{1} Real
                                (t.realMem
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
                                (g.realReg j)))
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
                                (@Eq.{1} Real (t.realMem address) (s.realMem address))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_12.1.1.1.1.1.1
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
theorem DecrAlmostLinearSSSP.Decremental.Native.SourceUpdateFrame.cache : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B reserve N : Nat}
  {j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.SourceUpdateFrame i B reserve N
      (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) s t →
    ∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n),
      And
        (@Eq.{1} Nat
          (t.natMem
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (DecrAlmostLinearSSSP.Decremental.Native.cacheAt
                (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n
                    (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).caches
                i.n (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val i.n v))))
          (s.natMem
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (DecrAlmostLinearSSSP.Decremental.Native.cacheAt
                (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n
                    (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).caches
                i.n (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val i.n v)))))
        (@Eq.{1} Real
          (t.realMem
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (DecrAlmostLinearSSSP.Decremental.Native.cacheAt
                (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n
                    (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).caches
                i.n (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val i.n v))))
          (s.realMem
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (DecrAlmostLinearSSSP.Decremental.Native.cacheAt
                (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n
                    (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).caches
                i.n (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val i.n v))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_12.1.1.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Native.AdapterMemory.source_frame : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B reserve N : Nat}
  {j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)} {a : DecrAlmostLinearSSSP.Decremental.AdapterState i}
  {xs : List.{0} (Fin i.n)} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.AdapterMemory i B reserve N a xs s →
    @LE.le.{0} Nat instLENat i.n B →
      DecrAlmostLinearSSSP.Decremental.Native.SourceUpdateFrame i B reserve N
          (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) s t →
        @Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 182) (instOfNatNat (nat_lit 182))))
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 182) (instOfNatNat (nat_lit 182)))) →
          @Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 180) (instOfNatNat (nat_lit 180))))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 180) (instOfNatNat (nat_lit 180)))) →
            DecrAlmostLinearSSSP.Decremental.Native.AdapterMemory i B reserve N a xs t := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_12.1.1.2.2.1.1
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
theorem DecrAlmostLinearSSSP.Decremental.Native.NormalRunState.work_bound : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program} {C : Real}
  {a : Nat → Real} {ds : List.{0} (Fin i.k)} {guides : DecrAlmostLinearSSSP.Decremental.Native.BarrierGuides i p C a ds}
  {coefficient : Nat} {initial : DecrAlmostLinearSSSP.Decremental.Machine}
  (st :
    DecrAlmostLinearSSSP.Decremental.Native.NormalRunState i p C a ds guides coefficient initial
      (Fin.last (@List.length.{0} (Fin i.k) ds))),
  @LE.le.{0} Nat instLENat
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@DecrAlmostLinearSSSP.Decremental.Native.NormalRunState.machine i p C a ds guides coefficient initial
          (Fin.last (@List.length.{0} (Fin i.k) ds)) st).work
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) (@List.length.{0} (Fin i.k) ds)))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) initial.work
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (DecrAlmostLinearSSSP.Decremental.Native.normalMaintenanceCharge p i.size)
          (@DecrAlmostLinearSSSP.Decremental.Native.sourceSumWork i p C a ds guides
            (Fin.last (@List.length.{0} (Fin i.k) ds)))))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13))) i.n)
        (DecrAlmostLinearSSSP.Decremental.scaleCount i))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_13.2.2.1.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.Image.stored : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.Normalize.Native.Image i B (@Option.none.{0} Nat) s g →
    ∀ (v : Fin i.n),
      @LE.le.{0} Nat instLENat (g.natMem (@Fin.val i.n v))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
        @Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.stored s.machine (@Fin.val i.n v))
          (DecrAlmostLinearSSSP.Decremental.Normalize.sanitize i
            (DecrAlmostLinearSSSP.Decremental.stored g (@Fin.val i.n v))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_1.2.1.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.CopyInvariant.step : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program} {B : Nat}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Normalize.Native.CopyInvariant i p B s →
    @LT.lt.{0} Nat instLTNat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 90) (instOfNatNat (nat_lit 90)))) i.k →
      DecrAlmostLinearSSSP.Decremental.Normalize.Native.CopyInvariant i p B
        (DecrAlmostLinearSSSP.Decremental.Normalize.Native.recordData s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_2.1.1.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.Registers.frame : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Normalize.Native.Registers i p s →
    (∀ (k : Nat),
        @LE.le.{0} Nat instLENat k (@OfNat.ofNat.{0} Nat (nat_lit 17) (instOfNatNat (nat_lit 17))) →
          @Eq.{1} Nat (t.natReg k) (s.natReg k)) →
      (∀ (j : Nat),
          @Eq.{1} Nat (t.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg j))
            (s.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg j))) →
        @Eq.{1} (Nat → Real) t.realReg s.realReg → DecrAlmostLinearSSSP.Decremental.Normalize.Native.Registers i p t := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_2.1.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.SentinelInvariant.step : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program} {B : Nat}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Normalize.Native.SentinelInvariant i p B s →
    @LT.lt.{0} Nat instLTNat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 90) (instOfNatNat (nat_lit 90)))) i.n →
      DecrAlmostLinearSSSP.Decremental.Normalize.Native.SentinelInvariant i p B
        (DecrAlmostLinearSSSP.Decremental.Normalize.Native.sentinelData s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_2.1.2.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.program_initialization : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
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
                      (@OfNat.ofNat.{0} Nat (nat_lit 200) (instOfNatNat (nat_lit 200))) i.size)))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_2.2.2.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.program_update : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (p : DecrAlmostLinearSSSP.Decremental.Program)
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
                (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_2.2.2.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.online : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
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
                                  DecrAlmostLinearSSSP.Decremental.Normalize.Native.Boundary i c' g')))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_2.2.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.Boundary.correct : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  i.Valid →
    ∀ (ds : List.{0} (Fin i.k)),
      DecrAlmostLinearSSSP.Decremental.Normalize.Native.Boundary i c g →
        DecrAlmostLinearSSSP.Decremental.Normalize.Native.Correct (DecrAlmostLinearSSSP.Decremental.Normalize.input i)
            (@List.map.{0, 0} (Fin i.k) (Fin (DecrAlmostLinearSSSP.Decremental.Normalize.input i).k)
              (DecrAlmostLinearSSSP.Decremental.Normalize.oldEdge i) ds)
            g →
          DecrAlmostLinearSSSP.Decremental.Normalize.Native.Correct i ds c := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_2.2.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.overhead_subpolynomial : ∀ (a : Nat → Real),
  DecrAlmostLinearSSSP.Decremental.Subpolynomial a →
    DecrAlmostLinearSSSP.Decremental.Subpolynomial (DecrAlmostLinearSSSP.Decremental.Normalize.Native.overhead a) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_2.2.2.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.maintains : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
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
                (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) Bool.false i := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_2.2.2.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.core_A_ge : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core),
  @LE.le.{0} Real Real.instLE
    (@OfNat.ofNat.{0} Real (nat_lit 32)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
    (DecrAlmostLinearSSSP.Decremental.A b) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_2.2.2.2.1.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.core_Q_ge : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core),
  @LE.le.{0} Real Real.instLE
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real (nat_lit 4)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
      (@Nat.cast.{0} Real Real.instNatCast b.input.n))
    (DecrAlmostLinearSSSP.Decremental.Q b) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_2.2.2.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.core_kappa_bounds : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core),
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
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_2.2.2.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.attained_toggle_count : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LE.le.{0} Real Real.instLE
      (@OfNat.ofNat.{0} Real (nat_lit 32)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
      K →
    ∀ (choose : DecrAlmostLinearSSSP.Decremental.State b → DecrAlmostLinearSSSP.Decremental.CutReply b),
      DecrAlmostLinearSSSP.Decremental.CutQuality b K choose →
        ∀ (s : DecrAlmostLinearSSSP.Decremental.State b),
          DecrAlmostLinearSSSP.Decremental.Attained b K choose s →
            @LE.le.{0} Real Real.instLE
              (@Nat.cast.{0} Real Real.instNatCast (@DecrAlmostLinearSSSP.Decremental.State.toggles b s))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@OfNat.ofNat.{0} Real (nat_lit 16)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))))))
                      (@HPow.hPow.{0, 0, 0} Real Nat Real
                        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) K
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                    (DecrAlmostLinearSSSP.Decremental.A b))
                  (@Nat.cast.{0} Real Real.instNatCast b.input.size))
                (Real.log
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@OfNat.ofNat.{0} Real (nat_lit 2)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                    (DecrAlmostLinearSSSP.Decremental.Q b)))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_3.2.1.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.RuntimeInvariant.initial : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
    DecrAlmostLinearSSSP.Decremental.RuntimeInvariant b K (DecrAlmostLinearSSSP.Decremental.initializeState b) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_3.2.1.2.1.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.RuntimeInvariant.toggle_count : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.State b),
      DecrAlmostLinearSSSP.Decremental.RuntimeInvariant b K s →
        @LE.le.{0} Real Real.instLE
          (@Nat.cast.{0} Real Real.instNatCast (@DecrAlmostLinearSSSP.Decremental.State.toggles b s))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@OfNat.ofNat.{0} Real (nat_lit 16)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))))))
                  (@HPow.hPow.{0, 0, 0} Real Nat Real
                    (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) K
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                (DecrAlmostLinearSSSP.Decremental.A b))
              (@Nat.cast.{0} Real Real.instNatCast b.input.size))
            (Real.log
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                (DecrAlmostLinearSSSP.Decremental.Q b)))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_3.2.1.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.ImplementsCut.initialize_session : ∀ {impl : DecrAlmostLinearSSSP.Decremental.CutImplementation} {m exponent : Nat} {K h Γ init ξ : Real},
  DecrAlmostLinearSSSP.Decremental.ImplementsCut impl m exponent K h Γ init ξ →
    ∀ {n k : Nat} (graph : DecrAlmostLinearSSSP.Decremental.Physical n k) (capacityBound : Real),
      @DecrAlmostLinearSSSP.Decremental.Physical.Valid n k graph m exponent →
        @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            capacityBound →
          @LE.le.{0} Real Real.instLE capacityBound
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                (@Max.max.{0} Real Real.instMax
                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                  (@Nat.cast.{0} Real Real.instNatCast m))
                exponent) →
            (∀ (e : Fin k),
                @Membership.mem.{0, 0} (Fin k) (Finset.{0} (Fin k))
                    (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin k)) (Fin k) (@Finset.instSetLike.{0} (Fin k)))
                    (@DecrAlmostLinearSSSP.Decremental.Physical.active n k graph) e →
                  @LE.le.{0} Real Real.instLE (@DecrAlmostLinearSSSP.Decremental.Physical.u n k graph e)
                    capacityBound) →
              ∃ first,
                And
                  (DecrAlmostLinearSSSP.Decremental.Ends impl.program
                    (@DecrAlmostLinearSSSP.Decremental.cutInitial n k impl.program graph m ξ capacityBound) first)
                  (And
                    (@Eq.{1} (DecrAlmostLinearSSSP.Decremental.Physical n k)
                      (@DecrAlmostLinearSSSP.Decremental.CutState.physical n k (impl.view n k first)) graph)
                    (And
                      (@Eq.{1} (Fin n → Real) (@DecrAlmostLinearSSSP.Decremental.CutState.y n k (impl.view n k first))
                        (@OfNat.ofNat.{0} (Fin n → Real) (nat_lit 0)
                          (@Zero.toOfNat0.{0} (Fin n → Real)
                            (@Pi.instZero.{0, 0} (Fin n) (fun a => Real) fun i => Real.instZero))))
                      (And
                        (@Eq.{1} (Fin k → Real)
                          (@DecrAlmostLinearSSSP.Decremental.CutState.baseline n k (impl.view n k first))
                          (@OfNat.ofNat.{0} (Fin k → Real) (nat_lit 0)
                            (@Zero.toOfNat0.{0} (Fin k → Real)
                              (@Pi.instZero.{0, 0} (Fin k) (fun a => Real) fun i => Real.instZero))))
                        (And
                          (@Eq.{1} Bool (@DecrAlmostLinearSSSP.Decremental.CutState.hasCut n k (impl.view n k first))
                            Bool.false)
                          (And (@LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast first.work) init)
                            (DecrAlmostLinearSSSP.Decremental.CutSession impl n k m exponent first K ξ h Γ init)))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.1.1.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreRequest.nat_frame : ∀ (slot source k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
      (DecrAlmostLinearSSSP.Decremental.CoreRequest.natCode slot source) k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.1.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreRequest.real_frame : ∀ (slot source k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
    (DecrAlmostLinearSSSP.Decremental.CoreRequest.realCode slot source) k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.1.2.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreRequest.SavedImage.resume : ∀ (N entry : Nat) (g : DecrAlmostLinearSSSP.Decremental.Machine) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreRequest.SavedImage N g s →
    DecrAlmostLinearSSSP.Decremental.CoreRequest.SavedImage N (DecrAlmostLinearSSSP.Decremental.resume g entry) s := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.1.2.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail.ends_of_bound : ∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {c d : DecrAlmostLinearSSSP.Decremental.Machine} {N : Nat},
  DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail N c →
    @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.registerBound p.code) N →
      DecrAlmostLinearSSSP.Decremental.Ends p c d → DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail N d := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.1.2.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.cutInitial_zero_tail : ∀ {n k N : Nat} (p : DecrAlmostLinearSSSP.Decremental.Program) (h : DecrAlmostLinearSSSP.Decremental.Physical n k)
  (m : Nat) (ξ cap : Real),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) N →
    DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail N (@DecrAlmostLinearSSSP.Decremental.cutInitial n k p h m ξ cap) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.2.1.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreSource.Image.call : ∀ (B R N entry : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program)
  (g final : DecrAlmostLinearSSSP.Decremental.Machine) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N g s →
    @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.registerBound p.code) N →
      (∃ r,
          @Eq.{1} Nat R
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
        @Eq.{1} Nat g.pc entry →
          @Eq.{1} Bool g.halted Bool.false →
            @Eq.{1} Bool g.fault Bool.false →
              DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail N g →
                DecrAlmostLinearSSSP.Decremental.Ends p g final →
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
                                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) final.work g.work))
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) N))
                            (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))))
                        (And (DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N final t)
                          (And
                            (DecrAlmostLinearSSSP.Decremental.ShadowDataRep B
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) t final)
                            (∀ (address : Nat),
                              (∀ (a : Nat),
                                  @Ne.{1} Nat address
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) →
                                @Ne.{1} Nat address
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) R
                                      (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))) →
                                  (∀ (j : Nat),
                                      @LT.lt.{0} Nat instLTNat j N →
                                        @Ne.{1} Nat address
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) R
                                              (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j))) →
                                    And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                      (@Eq.{1} Real (t.realMem address) (s.realMem address)))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.2.1.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreSource.Image.resume : ∀ (B R N entry : Nat) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N g s →
    DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N (DecrAlmostLinearSSSP.Decremental.resume g entry) s := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.2.1.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.CorePending.prefix_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CorePending.prefixCode s
    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
    (DecrAlmostLinearSSSP.Decremental.CorePending.prefixData s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.2.2.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.CorePending.prefix_fields : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  And
    (@Eq.{1} Nat
      ((DecrAlmostLinearSSSP.Decremental.CorePending.prefixData s).natReg
        (@OfNat.ofNat.{0} Nat (nat_lit 568) (instOfNatNat (nat_lit 568))))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 552) (instOfNatNat (nat_lit 552))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560)))))))
    (And
      (@Eq.{1} Nat
        ((DecrAlmostLinearSSSP.Decremental.CorePending.prefixData s).natReg
          (@OfNat.ofNat.{0} Nat (nat_lit 570) (instOfNatNat (nat_lit 570))))
        (s.natMem
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 552) (instOfNatNat (nat_lit 552))))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))))))
      (And
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.CorePending.prefixData s).natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 572) (instOfNatNat (nat_lit 572))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 552) (instOfNatNat (nat_lit 552))))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))))
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))))
        (∀ (k : Nat),
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 562) (instOfNatNat (nat_lit 562))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 564) (instOfNatNat (nat_lit 564))) →
              @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 566) (instOfNatNat (nat_lit 566))) →
                @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 568) (instOfNatNat (nat_lit 568))) →
                  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 570) (instOfNatNat (nat_lit 570))) →
                    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 572) (instOfNatNat (nat_lit 572))) →
                      @Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.CorePending.prefixData s).natReg k) (s.natReg k)))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.2.2.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.CorePending.prefix_memory : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  And (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.CorePending.prefixData s).natMem s.natMem)
    (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.CorePending.prefixData s).realMem s.realMem) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.2.2.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.logicalCount_le : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core),
  @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.logicalCount b)
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.2.2.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreMemory.source_guest_disjoint : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B offset a : Nat),
  @Ne.{1} Nat
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) offset))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) a))
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.2.2.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreGeometry.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreGeometry.code s
    (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))
    (DecrAlmostLinearSSSP.Decremental.CoreGeometry.result s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.1.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreGeometry.values : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
    And
      (@Eq.{1} Real
        ((DecrAlmostLinearSSSP.Decremental.CoreGeometry.result s).realReg
          (@OfNat.ofNat.{0} Nat (nat_lit 600) (instOfNatNat (nat_lit 600))))
        (s.realMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 568) (instOfNatNat (nat_lit 568))))))
      (And
        (@Eq.{1} Real
          ((DecrAlmostLinearSSSP.Decremental.CoreGeometry.result s).realReg
            (@OfNat.ofNat.{0} Nat (nat_lit 602) (instOfNatNat (nat_lit 602))))
          (s.realMem
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 568) (instOfNatNat (nat_lit 568))))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
        (And
          (@Eq.{1} Real
            ((DecrAlmostLinearSSSP.Decremental.CoreGeometry.result s).realReg
              (@OfNat.ofNat.{0} Nat (nat_lit 604) (instOfNatNat (nat_lit 604))))
            (s.realMem
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 568) (instOfNatNat (nat_lit 568))))
                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
          (And
            (@Eq.{1} Real
              ((DecrAlmostLinearSSSP.Decremental.CoreGeometry.result s).realReg
                (@OfNat.ofNat.{0} Nat (nat_lit 606) (instOfNatNat (nat_lit 606))))
              (s.realMem
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 568) (instOfNatNat (nat_lit 568))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))
            (And
              (@Eq.{1} Nat
                ((DecrAlmostLinearSSSP.Decremental.CoreGeometry.result s).natReg
                  (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626))))
                (s.natMem
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 568) (instOfNatNat (nat_lit 568))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
              (And
                (@Eq.{1} Nat
                  ((DecrAlmostLinearSSSP.Decremental.CoreGeometry.result s).natReg
                    (@OfNat.ofNat.{0} Nat (nat_lit 628) (instOfNatNat (nat_lit 628))))
                  (s.natMem
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 568) (instOfNatNat (nat_lit 568))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))))
                (@Eq.{1} Nat
                  ((DecrAlmostLinearSSSP.Decremental.CoreGeometry.result s).natReg
                    (@OfNat.ofNat.{0} Nat (nat_lit 648) (instOfNatNat (nat_lit 648))))
                  (s.natMem
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 568) (instOfNatNat (nat_lit 568))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.1.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreGeometry.no_memory : DecrAlmostLinearSSSP.Decremental.Structured.NoMemory DecrAlmostLinearSSSP.Decremental.CoreGeometry.code := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.1.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreGeometry.nat_frame : ∀ (k : Nat),
  Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 574) (instOfNatNat (nat_lit 574))))
      (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 580) (instOfNatNat (nat_lit 580))) k) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 628) (instOfNatNat (nat_lit 628))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 648) (instOfNatNat (nat_lit 648))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreGeometry.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.1.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreGeometry.real_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 600) (instOfNatNat (nat_lit 600))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 602) (instOfNatNat (nat_lit 602))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 604) (instOfNatNat (nat_lit 604))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 606) (instOfNatNat (nat_lit 606))) →
          DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreGeometry.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.1.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreRecord.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreRecord.code s
    (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) (DecrAlmostLinearSSSP.Decremental.CoreRecord.result s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.1.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreRecord.Addresses.frame : ∀ (base : Nat) {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.CoreRecord.Addresses base s →
    (∀ (k : Nat),
        @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat)
            (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 568) (instOfNatNat (nat_lit 568)))
              (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 574) (instOfNatNat (nat_lit 574)))
                (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 576) (instOfNatNat (nat_lit 576)))
                  (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 578) (instOfNatNat (nat_lit 578)))
                    (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 580) (instOfNatNat (nat_lit 580)))
                      (@List.nil.{0} Nat))))))
            k →
          @Eq.{1} Nat (t.natReg k) (s.natReg k)) →
      DecrAlmostLinearSSSP.Decremental.CoreRecord.Addresses base t := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.1.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreRecord.fields : ∀ (base : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreRecord.Addresses base s →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
      And
        (@Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.CoreRecord.result s).natMem base)
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (And
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.CoreRecord.result s).natMem
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (And
            (@Eq.{1} Nat
              ((DecrAlmostLinearSSSP.Decremental.CoreRecord.result s).natMem
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626)))))
            (And
              (@Eq.{1} Nat
                ((DecrAlmostLinearSSSP.Decremental.CoreRecord.result s).natMem
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 628) (instOfNatNat (nat_lit 628)))))
              (And
                (@Eq.{1} Nat
                  ((DecrAlmostLinearSSSP.Decremental.CoreRecord.result s).natMem
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                      (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 648) (instOfNatNat (nat_lit 648)))))
                (And
                  (@Eq.{1} Real ((DecrAlmostLinearSSSP.Decremental.CoreRecord.result s).realMem base)
                    (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 612) (instOfNatNat (nat_lit 612)))))
                  (And
                    (@Eq.{1} Real
                      ((DecrAlmostLinearSSSP.Decremental.CoreRecord.result s).realMem
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 602) (instOfNatNat (nat_lit 602)))))
                    (And
                      (@Eq.{1} Real
                        ((DecrAlmostLinearSSSP.Decremental.CoreRecord.result s).realMem
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
                        (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 604) (instOfNatNat (nat_lit 604)))))
                      (And
                        (@Eq.{1} Real
                          ((DecrAlmostLinearSSSP.Decremental.CoreRecord.result s).realMem
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                              (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
                          (s.realMem
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                              (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))))
                        (@Eq.{1} Real
                          ((DecrAlmostLinearSSSP.Decremental.CoreRecord.result s).realMem
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                              (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))
                          (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 606) (instOfNatNat (nat_lit 606))))))))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.1.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreRecord.frame : ∀ (base : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreRecord.Addresses base s →
    ∀ (j : Nat),
      @Ne.{1} Nat j base →
        @Ne.{1} Nat j
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
          @Ne.{1} Nat j
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) →
            @Ne.{1} Nat j
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                  (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))) →
              @Ne.{1} Nat j
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                    (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) →
                And (@Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.CoreRecord.result s).natMem j) (s.natMem j))
                  (@Eq.{1} Real ((DecrAlmostLinearSSSP.Decremental.CoreRecord.result s).realMem j) (s.realMem j)) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.1.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreRecord.nat_frame : ∀ (k : Nat), DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreRecord.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.1.2.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreRecord.real_frame : ∀ (k : Nat), DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreRecord.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.1.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreEdgeAddress.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreEdgeAddress.code s
    (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))
    (DecrAlmostLinearSSSP.Decremental.CoreEdgeAddress.result s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.1.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreEdgeAddress.values : ∀ (B e : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 552) (instOfNatNat (nat_lit 552))))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) e) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
        DecrAlmostLinearSSSP.Decremental.CoreRecord.Addresses
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) e))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (DecrAlmostLinearSSSP.Decremental.CoreEdgeAddress.result s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreEdgeAddress.no_memory : DecrAlmostLinearSSSP.Decremental.Structured.NoMemory DecrAlmostLinearSSSP.Decremental.CoreEdgeAddress.code := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.1.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreEdgeAddress.nat_frame : ∀ (k : Nat),
  Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 562) (instOfNatNat (nat_lit 562))))
      (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 580) (instOfNatNat (nat_lit 580))) k) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreEdgeAddress.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.1.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreEdgeAddress.real_frame : ∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreEdgeAddress.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.2.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreReturnCoefficient.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreReturnCoefficient.code s
    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
    (DecrAlmostLinearSSSP.Decremental.CoreReturnCoefficient.result s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.2.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreReturnCoefficient.value : ∀ (base v q : Nat) (A : Real) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 554) (instOfNatNat (nat_lit 554)))) base →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626)))) v →
      @Eq.{1} Nat
          (s.natMem
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) v)))
          q →
        @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 504) (instOfNatNat (nat_lit 504)))) A →
          @Eq.{1} Real
            ((DecrAlmostLinearSSSP.Decremental.CoreReturnCoefficient.result s).realReg
              (@OfNat.ofNat.{0} Nat (nat_lit 602) (instOfNatNat (nat_lit 602))))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) A
              (@Nat.cast.{0} Real Real.instNatCast q)) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.2.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreReturnCoefficient.no_memory : DecrAlmostLinearSSSP.Decremental.Structured.NoMemory DecrAlmostLinearSSSP.Decremental.CoreReturnCoefficient.code := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.2.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreReturnCoefficient.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 620) (instOfNatNat (nat_lit 620))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 662) (instOfNatNat (nat_lit 662))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreReturnCoefficient.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.2.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreReturnCoefficient.real_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 602) (instOfNatNat (nat_lit 602))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreReturnCoefficient.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.2.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreDegree.eval_code : ∀ (vertex : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.CoreDegree.code vertex) s
    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
    (DecrAlmostLinearSSSP.Decremental.CoreDegree.result vertex s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreDegree.values : ∀ (vertex base v : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 554) (instOfNatNat (nat_lit 554)))) base →
    @Eq.{1} Nat (s.natReg vertex) v →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
        And
          (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.CoreDegree.result vertex s).natMem
            (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natMem
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) v))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (s.natMem
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) v)))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
          (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.CoreDegree.result vertex s).realMem s.realMem) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreDegree.nat_frame : ∀ (vertex k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 620) (instOfNatNat (nat_lit 620))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 662) (instOfNatNat (nat_lit 662))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.CoreDegree.code vertex) k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.2.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreDegree.real_frame : ∀ (vertex k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.CoreDegree.code vertex) k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.2.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreTape.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreTape.code s
    (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (DecrAlmostLinearSSSP.Decremental.CoreTape.result s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.2.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreTape.values : ∀ (pointer a z w : Nat) (Q : Real) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 652) (instOfNatNat (nat_lit 652)))) pointer →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 502) (instOfNatNat (nat_lit 502)))) Q →
        @Eq.{1} Nat (s.natMem pointer) a →
          @Eq.{1} Nat
              (s.natMem
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pointer
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              z →
            @Eq.{1} Nat
                (s.natMem
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pointer
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                w →
              And
                (@Eq.{1} Nat
                  ((DecrAlmostLinearSSSP.Decremental.CoreTape.result s).natReg
                    (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626))))
                  a)
                (And
                  (@Eq.{1} Nat
                    ((DecrAlmostLinearSSSP.Decremental.CoreTape.result s).natReg
                      (@OfNat.ofNat.{0} Nat (nat_lit 628) (instOfNatNat (nat_lit 628))))
                    z)
                  (And
                    (@Eq.{1} Nat
                      ((DecrAlmostLinearSSSP.Decremental.CoreTape.result s).natReg
                        (@OfNat.ofNat.{0} Nat (nat_lit 654) (instOfNatNat (nat_lit 654))))
                      w)
                    (And
                      (@Eq.{1} Nat
                        ((DecrAlmostLinearSSSP.Decremental.CoreTape.result s).natReg
                          (@OfNat.ofNat.{0} Nat (nat_lit 652) (instOfNatNat (nat_lit 652))))
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pointer
                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                      (@Eq.{1} Real
                        ((DecrAlmostLinearSSSP.Decremental.CoreTape.result s).realReg
                          (@OfNat.ofNat.{0} Nat (nat_lit 604) (instOfNatNat (nat_lit 604))))
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (@Nat.cast.{0} Real Real.instNatCast w) Q))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.2.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreTape.no_memory : DecrAlmostLinearSSSP.Decremental.Structured.NoMemory DecrAlmostLinearSSSP.Decremental.CoreTape.code := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreTape.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 628) (instOfNatNat (nat_lit 628))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 652) (instOfNatNat (nat_lit 652))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 654) (instOfNatNat (nat_lit 654))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreTape.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreTape.real_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 604) (instOfNatNat (nat_lit 604))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreTape.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.2.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreInitialDifference.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
    ∃ cost,
      And
        (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreInitialDifference.code s
          cost (DecrAlmostLinearSSSP.Decremental.CoreInitialDifference.result s))
        (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.2.1.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreInitialDifference.value : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (e : Fin b.input.k)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626))))
      (@Fin.val b.input.n (@DecrAlmostLinearSSSP.Decremental.Digraph.tail b.input.n b.input.k b.input.graph e)) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72))))
        (@Fin.val b.input.n b.input.source) →
      @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 514) (instOfNatNat (nat_lit 514))))
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              (DecrAlmostLinearSSSP.Decremental.Q b))) →
        @Eq.{1} Real
          ((DecrAlmostLinearSSSP.Decremental.CoreInitialDifference.result s).realReg
            (@OfNat.ofNat.{0} Nat (nat_lit 606) (instOfNatNat (nat_lit 606))))
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (DecrAlmostLinearSSSP.Decremental.initialLabel b
              (DecrAlmostLinearSSSP.Decremental.tail b
                (@Sum.inl.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) e)))
            (DecrAlmostLinearSSSP.Decremental.initialLabel b
              (DecrAlmostLinearSSSP.Decremental.head b
                (@Sum.inl.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) e)))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.2.1.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreInitialDifference.no_memory : DecrAlmostLinearSSSP.Decremental.Structured.NoMemory DecrAlmostLinearSSSP.Decremental.CoreInitialDifference.code := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.2.1.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreInitialDifference.nat_frame : ∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreInitialDifference.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.2.1.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreInitialDifference.real_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 606) (instOfNatNat (nat_lit 606))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreInitialDifference.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.2.1.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreInitializeHeader.eval_code : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (e : Fin b.input.k)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.Tape b.input s →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72))))
            (@Fin.val b.input.n b.input.source) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 552) (instOfNatNat (nat_lit 552))))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val b.input.k e)) →
              @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 652) (instOfNatNat (nat_lit 652))))
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b.input.n
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (@Fin.val b.input.k e))) →
                @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
                  @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 502) (instOfNatNat (nat_lit 502))))
                      (DecrAlmostLinearSSSP.Decremental.Q b) →
                    @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 514) (instOfNatNat (nat_lit 514))))
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@OfNat.ofNat.{0} Real (nat_lit 2)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                            (DecrAlmostLinearSSSP.Decremental.Q b))) →
                      ∃ cost t,
                        And
                          (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                            DecrAlmostLinearSSSP.Decremental.CoreInitializeHeader.code s cost t)
                          (And
                            (@LE.le.{0} Nat instLENat cost
                              (@OfNat.ofNat.{0} Nat (nat_lit 25) (instOfNatNat (nat_lit 25))))
                            (And (DecrAlmostLinearSSSP.Decremental.CoreInitializeHeader.Loaded b B e t)
                              (And (@Eq.{1} (Nat → Real) t.realMem s.realMem) (@Eq.{1} (Nat → Nat) t.natMem s.natMem)))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.2.1.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreControl.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreControl.code s
    (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19)))
    (DecrAlmostLinearSSSP.Decremental.CoreControl.result s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.2.2.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreControl.values : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real) (B : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured b.input s →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))) B →
      DecrAlmostLinearSSSP.Decremental.CoreParameters.Values b K s →
        And
          (DecrAlmostLinearSSSP.Decremental.CoreControl.Layout b B
            (DecrAlmostLinearSSSP.Decremental.CoreControl.result s))
          (And
            (@Eq.{1} Nat
              ((DecrAlmostLinearSSSP.Decremental.CoreControl.result s).natReg
                (@OfNat.ofNat.{0} Nat (nat_lit 546) (instOfNatNat (nat_lit 546))))
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
            (And
              (@Eq.{1} Nat
                ((DecrAlmostLinearSSSP.Decremental.CoreControl.result s).natReg
                  (@OfNat.ofNat.{0} Nat (nat_lit 550) (instOfNatNat (nat_lit 550))))
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (And
                (@Eq.{1} Nat
                  ((DecrAlmostLinearSSSP.Decremental.CoreControl.result s).natReg
                    (@OfNat.ofNat.{0} Nat (nat_lit 650) (instOfNatNat (nat_lit 650))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (@Eq.{1} Real
                  ((DecrAlmostLinearSSSP.Decremental.CoreControl.result s).realReg
                    (@OfNat.ofNat.{0} Nat (nat_lit 520) (instOfNatNat (nat_lit 520))))
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@Neg.neg.{0} Real Real.instNeg
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@OfNat.ofNat.{0} Real (nat_lit 4)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                      K)))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.2.2.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreControl.nat_frame : ∀ (k : Nat),
  Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
      (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))) k) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))) →
      Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 542) (instOfNatNat (nat_lit 542))))
          (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 650) (instOfNatNat (nat_lit 650))) k) →
        DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreControl.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.2.2.2.1.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreControl.real_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 520) (instOfNatNat (nat_lit 520))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 656) (instOfNatNat (nat_lit 656))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 658) (instOfNatNat (nat_lit 658))) →
        DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreControl.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.2.2.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreControl.no_memory : DecrAlmostLinearSSSP.Decremental.Structured.NoMemory DecrAlmostLinearSSSP.Decremental.CoreControl.code := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.2.2.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreControl.captured : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured b.input s →
    DecrAlmostLinearSSSP.Decremental.InputCapture.Captured b.input
      (DecrAlmostLinearSSSP.Decremental.CoreControl.result s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreControl.parameters : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreParameters.Values b K s →
    DecrAlmostLinearSSSP.Decremental.CoreParameters.Values b K (DecrAlmostLinearSSSP.Decremental.CoreControl.result s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.2.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreInitializeHeader.nat_frame : ∀ (k : Nat),
  Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 562) (instOfNatNat (nat_lit 562))))
      (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 654) (instOfNatNat (nat_lit 654))) k) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreInitializeHeader.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.1.1.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreInitializeHeader.real_frame : ∀ (k : Nat),
  Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 602) (instOfNatNat (nat_lit 602))))
      (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 606) (instOfNatNat (nat_lit 606))) k) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreInitializeHeader.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.1.1.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreInitializeHeader.no_memory : DecrAlmostLinearSSSP.Decremental.Structured.NoMemory DecrAlmostLinearSSSP.Decremental.CoreInitializeHeader.code := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.1.1.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreInitializeHeader.captured : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {cost : Nat},
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured b.input s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreInitializeHeader.code s cost
        t →
      DecrAlmostLinearSSSP.Decremental.InputCapture.Captured b.input t := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.1.1.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreInitializeHeader.parameters : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real) {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {cost : Nat},
  DecrAlmostLinearSSSP.Decremental.CoreParameters.Values b K s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreInitializeHeader.code s cost
        t →
      DecrAlmostLinearSSSP.Decremental.CoreParameters.Values b K t := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.1.1.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreRefresh.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreRefresh.code s
      (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
      (DecrAlmostLinearSSSP.Decremental.CoreRefresh.result s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.1.2.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreRefresh.no_memory : DecrAlmostLinearSSSP.Decremental.Structured.NoMemory DecrAlmostLinearSSSP.Decremental.CoreRefresh.code := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.1.2.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreRefresh.nat_frame : ∀ (k : Nat), DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreRefresh.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.1.2.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreRefresh.real_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 612) (instOfNatNat (nat_lit 612))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 614) (instOfNatNat (nat_lit 614))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 616) (instOfNatNat (nat_lit 616))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 618) (instOfNatNat (nat_lit 618))) →
          DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreRefresh.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.1.2.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreGeometry.loaded_image : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (e : DecrAlmostLinearSSSP.Decremental.Edge b) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreGeometry.Image b B state s →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 568) (instOfNatNat (nat_lit 568))))
        (DecrAlmostLinearSSSP.Decremental.CoreMemory.field b B e
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
        DecrAlmostLinearSSSP.Decremental.CoreGeometry.Loaded b state e
          (DecrAlmostLinearSSSP.Decremental.CoreGeometry.result s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.1.2.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreRecord.Initialized.frame : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (e : DecrAlmostLinearSSSP.Decremental.Edge b)
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.CoreRecord.Initialized b B e s →
    (∀ (j : Nat),
        @LT.lt.{0} Nat instLTNat j (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
          @Eq.{1} Nat (t.natMem (DecrAlmostLinearSSSP.Decremental.CoreMemory.field b B e j))
            (s.natMem (DecrAlmostLinearSSSP.Decremental.CoreMemory.field b B e j))) →
      (∀ (j : Nat),
          @LT.lt.{0} Nat instLTNat j (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
            @Eq.{1} Real (t.realMem (DecrAlmostLinearSSSP.Decremental.CoreMemory.field b B e j))
              (s.realMem (DecrAlmostLinearSSSP.Decremental.CoreMemory.field b B e j))) →
        DecrAlmostLinearSSSP.Decremental.CoreRecord.Initialized b B e t := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.1.2.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreOutput.eval_code : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (v : Nat)
  (r : Real),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 620) (instOfNatNat (nat_lit 620)))) v →
    @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 616) (instOfNatNat (nat_lit 616)))) r →
      @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
        @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 502) (instOfNatNat (nat_lit 502))))
            (DecrAlmostLinearSSSP.Decremental.Q b) →
          @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 534) (instOfNatNat (nat_lit 534))))
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (DecrAlmostLinearSSSP.Decremental.H b)
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))) →
            @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 518) (instOfNatNat (nat_lit 518))))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) b.input.accuracy
                      (@OfNat.ofNat.{0} Real (nat_lit 2)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
                  (DecrAlmostLinearSSSP.Decremental.Q b)) →
              ∃ cost t,
                And
                  (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreOutput.code s
                    cost t)
                  (And (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))
                    (And
                      (@Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.stored t.machine v)
                        (DecrAlmostLinearSSSP.Decremental.readout b r))
                      (And
                        (@LE.le.{0} Nat instLENat (t.natMem v)
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        (And
                          (@Eq.{1} Nat (t.natMem v) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                            @LE.le.{0} Real Real.instLE
                              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (t.realMem v))
                          (∀ (j : Nat),
                            @Ne.{1} Nat j v →
                              And (@Eq.{1} Nat (t.natMem j) (s.natMem j))
                                (@Eq.{1} Real (t.realMem j) (s.realMem j))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.1.2.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreOutput.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 622) (instOfNatNat (nat_lit 622))) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreOutput.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.2.1.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreOutput.real_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 620) (instOfNatNat (nat_lit 620))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 624) (instOfNatNat (nat_lit 624))) →
      DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreOutput.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.2.1.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreReturn.eval_code : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data)
  (v sampleAddress : Nat) (r : Real),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626)))) v →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 578) (instOfNatNat (nat_lit 578)))) sampleAddress →
      @Ne.{1} Nat sampleAddress v →
        @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 616) (instOfNatNat (nat_lit 616)))) r →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
            @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
              @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 502) (instOfNatNat (nat_lit 502))))
                  (DecrAlmostLinearSSSP.Decremental.Q b) →
                @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 534) (instOfNatNat (nat_lit 534))))
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (DecrAlmostLinearSSSP.Decremental.H b)
                      (@OfNat.ofNat.{0} Real (nat_lit 2)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))) →
                  @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 518) (instOfNatNat (nat_lit 518))))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) b.input.accuracy
                            (@OfNat.ofNat.{0} Real (nat_lit 2)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
                        (DecrAlmostLinearSSSP.Decremental.Q b)) →
                    ∃ cost t,
                      And
                        (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                          DecrAlmostLinearSSSP.Decremental.CoreReturn.code s cost t)
                        (And
                          (@LE.le.{0} Nat instLENat cost
                            (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11))))
                          (And
                            (@Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.stored t.machine v)
                              (DecrAlmostLinearSSSP.Decremental.readout b r))
                            (And (@Eq.{1} Real (t.realMem sampleAddress) r)
                              (And
                                (@LE.le.{0} Nat instLENat (t.natMem v)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                (And
                                  (@Eq.{1} Nat (t.natMem v)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                                    @LE.le.{0} Real Real.instLE
                                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                      (t.realMem v))
                                  (And (∀ (j : Nat), @Ne.{1} Nat j v → @Eq.{1} Nat (t.natMem j) (s.natMem j))
                                    (∀ (j : Nat),
                                      @Ne.{1} Nat j v →
                                        @Ne.{1} Nat j sampleAddress → @Eq.{1} Real (t.realMem j) (s.realMem j)))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.2.1.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreReturn.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 620) (instOfNatNat (nat_lit 620))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 622) (instOfNatNat (nat_lit 622))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreReturn.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.2.1.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreReturn.real_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 620) (instOfNatNat (nat_lit 620))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 624) (instOfNatNat (nat_lit 624))) →
      DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreReturn.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.2.1.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreNonzero.eval_code : ∀ (source target : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
    ∃ cost,
      And
        (DecrAlmostLinearSSSP.Decremental.Structured.Eval
          (DecrAlmostLinearSSSP.Decremental.CoreNonzero.code source target) s cost
          (DecrAlmostLinearSSSP.Decremental.CoreNonzero.result source target s))
        (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.2.1.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreNonzero.no_memory : ∀ (source target : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.NoMemory (DecrAlmostLinearSSSP.Decremental.CoreNonzero.code source target) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.2.1.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreNonzero.nat_frame : ∀ (source target k : Nat),
  @Ne.{1} Nat k target →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
      (DecrAlmostLinearSSSP.Decremental.CoreNonzero.code source target) k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.2.1.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreNonzero.real_frame : ∀ (source target k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
    (DecrAlmostLinearSSSP.Decremental.CoreNonzero.code source target) k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.2.1.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreGradient.prefix_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreGradient.prefixCode s
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    (DecrAlmostLinearSSSP.Decremental.CoreGradient.prepared s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.2.1.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreGradient.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
    ∃ cost,
      And
        (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreGradient.code s cost
          (DecrAlmostLinearSSSP.Decremental.CoreGradient.result s))
        (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.2.1.2.1.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreGradient.values : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  And
    (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.CoreGradient.result s).realMem
      (@Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realMem
        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 620) (instOfNatNat (nat_lit 620))))
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (s.realMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 620) (instOfNatNat (nat_lit 620)))))
          (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626)))))))
    (And (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.CoreGradient.result s).natMem s.natMem)
      (@Eq.{1} Nat
        ((DecrAlmostLinearSSSP.Decremental.CoreGradient.result s).natReg
          (@OfNat.ofNat.{0} Nat (nat_lit 550) (instOfNatNat (nat_lit 550))))
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 550) (instOfNatNat (nat_lit 550))))
            (DecrAlmostLinearSSSP.Decremental.nonzero
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (s.realMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 620) (instOfNatNat (nat_lit 620)))))
                (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626)))))))
          (DecrAlmostLinearSSSP.Decremental.nonzero
            (s.realMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 620) (instOfNatNat (nat_lit 620))))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.2.1.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreGradient.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 550) (instOfNatNat (nat_lit 550))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 632) (instOfNatNat (nat_lit 632))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 634) (instOfNatNat (nat_lit 634))) →
        DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreGradient.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.2.1.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreGradient.real_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 628) (instOfNatNat (nat_lit 628))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
      DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreGradient.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreGradientEndpoints.eval_code : ∀ {n : Nat} (base : Nat) (g : Fin n → Real) (a z : Fin n) (f : Real)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @DecrAlmostLinearSSSP.Decremental.CoreGradient.Image n base g s →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 554) (instOfNatNat (nat_lit 554)))) base →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626)))) (@Fin.val n a) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 628) (instOfNatNat (nat_lit 628)))) (@Fin.val n z) →
          @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 612) (instOfNatNat (nat_lit 612)))) f →
            @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
              ∃ cost t,
                And
                  (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                    DecrAlmostLinearSSSP.Decremental.CoreGradientEndpoints.code s cost t)
                  (And (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 36) (instOfNatNat (nat_lit 36))))
                    (And
                      (@DecrAlmostLinearSSSP.Decremental.CoreGradient.Image n base
                        (fun v =>
                          @HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (g v)
                              (@ite.{1} Real (@Eq.{1} (Fin n) v a) (instDecidableEqFin n v a) f
                                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
                            (@ite.{1} Real (@Eq.{1} (Fin n) v z) (instDecidableEqFin n v z) f
                              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
                        t)
                      (And (@Eq.{1} (Nat → Nat) t.natMem s.natMem)
                        (∀ (j : Nat),
                          @Ne.{1} Nat j
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val n a))) →
                            @Ne.{1} Nat j
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val n z))) →
                              @Eq.{1} Real (t.realMem j) (s.realMem j))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.2.2.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreGradientEndpoints.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 550) (instOfNatNat (nat_lit 550))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 620) (instOfNatNat (nat_lit 620))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 632) (instOfNatNat (nat_lit 632))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 634) (instOfNatNat (nat_lit 634))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
            DecrAlmostLinearSSSP.Decremental.CoreGradientEndpoints.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.2.2.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreGradientEndpoints.real_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 628) (instOfNatNat (nat_lit 628))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
        DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
          DecrAlmostLinearSSSP.Decremental.CoreGradientEndpoints.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.2.2.2.1.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Structured.evenRegisters_frames : ∀ (cmd : DecrAlmostLinearSSSP.Decremental.Structured.Cmd),
  @Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.Structured.evenRegisters cmd) Bool.true →
    ∀ (k : Nat),
      @Eq.{1} Nat
          (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) k
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
        And (DecrAlmostLinearSSSP.Decremental.Structured.NatFrame cmd k)
          (DecrAlmostLinearSSSP.Decremental.Structured.RealFrame cmd k) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.2.2.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.even_registers : @Eq.{1} Bool
  (DecrAlmostLinearSSSP.Decremental.Structured.evenRegisters DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.code)
  Bool.true := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_7.1.1.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreMemory.Frame.trans : ∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {B : Nat} {s t u : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.CoreMemory.Frame b B s t →
    DecrAlmostLinearSSSP.Decremental.CoreMemory.Frame b B t u →
      DecrAlmostLinearSSSP.Decremental.CoreMemory.Frame b B s u := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_7.1.1.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreMemory.ReturnFrame.trans : ∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {B : Nat} {s t u : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.CoreMemory.ReturnFrame b B s t →
    DecrAlmostLinearSSSP.Decremental.CoreMemory.ReturnFrame b B t u →
      DecrAlmostLinearSSSP.Decremental.CoreMemory.ReturnFrame b B s u := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_7.1.2.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.Invariant.step : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (upto : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @LE.le.{0} Nat instLENat b.input.n B →
    DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.Invariant b B K upto s →
      @LT.lt.{0} Nat instLTNat upto b.input.n →
        ∃ cost t,
          And
            (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.body
              s cost t)
            (And (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 87) (instOfNatNat (nat_lit 87))))
              (And
                (DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.Invariant b B K
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) upto
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  t)
                (DecrAlmostLinearSSSP.Decremental.CoreMemory.ReturnFrame b B s t))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_7.2.1.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.nat_frame : ∀ (k : Nat),
  Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 550) (instOfNatNat (nat_lit 550))))
      (Or (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 552) (instOfNatNat (nat_lit 552))))
        (Or (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 554) (instOfNatNat (nat_lit 554))))
          (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 662) (instOfNatNat (nat_lit 662))) k))) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_7.2.1.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.real_frame : ∀ (k : Nat),
  Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 602) (instOfNatNat (nat_lit 602))))
      (Or (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 608) (instOfNatNat (nat_lit 608))))
        (Or (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 610) (instOfNatNat (nat_lit 610))))
          (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) k))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_7.2.1.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.even_registers : @Eq.{1} Bool
  (DecrAlmostLinearSSSP.Decremental.Structured.evenRegisters DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.code)
  Bool.true := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_7.2.1.2.1.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.captured : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {cost : Nat},
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured b.input s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.code s cost t →
      DecrAlmostLinearSSSP.Decremental.InputCapture.Captured b.input t := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_7.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.parameters : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real) {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {cost : Nat},
  DecrAlmostLinearSSSP.Decremental.CoreParameters.Values b K s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.code s cost t →
      DecrAlmostLinearSSSP.Decremental.CoreParameters.Values b K t := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_7.2.1.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.layout : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {cost : Nat},
  DecrAlmostLinearSSSP.Decremental.CoreControl.Layout b B s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.code s cost t →
      DecrAlmostLinearSSSP.Decremental.CoreControl.Layout b B t := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_7.2.1.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreInitializeStore.nat_frame : ∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreInitializeStore.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_7.2.2.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreInitializeStore.real_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 612) (instOfNatNat (nat_lit 612))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 614) (instOfNatNat (nat_lit 614))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 616) (instOfNatNat (nat_lit 616))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 618) (instOfNatNat (nat_lit 618))) →
          DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
            DecrAlmostLinearSSSP.Decremental.CoreInitializeStore.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_7.2.2.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreInitializeStore.eval_code : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (e : Fin b.input.k)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreInitializeHeader.Loaded b B e s →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
      @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
        @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 506) (instOfNatNat (nat_lit 506))))
            (DecrAlmostLinearSSSP.Decremental.kappa b) →
          @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 608) (instOfNatNat (nat_lit 608))))
              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
            @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 610) (instOfNatNat (nat_lit 610))))
                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
              And
                (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                  DecrAlmostLinearSSSP.Decremental.CoreInitializeStore.code s
                  (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))
                  (DecrAlmostLinearSSSP.Decremental.CoreInitializeStore.result s))
                (And
                  (DecrAlmostLinearSSSP.Decremental.CoreRecord.Initialized b B
                    (@Sum.inl.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) e)
                    (DecrAlmostLinearSSSP.Decremental.CoreInitializeStore.result s))
                  (And
                    (@Eq.{1} Real
                      ((DecrAlmostLinearSSSP.Decremental.CoreInitializeStore.result s).realReg
                        (@OfNat.ofNat.{0} Nat (nat_lit 612) (instOfNatNat (nat_lit 612))))
                      (DecrAlmostLinearSSSP.Decremental.capacity b
                        (@Finset.univ.{0} (Fin b.input.k) (Fin.fintype b.input.k))
                        (DecrAlmostLinearSSSP.Decremental.initialLabel b)
                        (@Sum.inl.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) e)))
                    (∀ (j : Nat),
                      (∀ (offset : Nat),
                          @LT.lt.{0} Nat instLTNat offset
                              (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
                            @Ne.{1} Nat j
                              (DecrAlmostLinearSSSP.Decremental.CoreMemory.field b B
                                (@Sum.inl.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) e)
                                offset)) →
                        And
                          (@Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.CoreInitializeStore.result s).natMem j)
                            (s.natMem j))
                          (@Eq.{1} Real ((DecrAlmostLinearSSSP.Decremental.CoreInitializeStore.result s).realMem j)
                            (s.realMem j))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_7.2.2.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreInitializeContributions.eval_code : ∀ {n : Nat} (base counter : Nat) (heads : List.{0} (Fin n)) (g : Fin n → Real) (a z : Fin n) (f : Real)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @DecrAlmostLinearSSSP.Decremental.CoreDegree.Image n base heads s →
    @DecrAlmostLinearSSSP.Decremental.CoreGradient.Image n base g s →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 554) (instOfNatNat (nat_lit 554)))) base →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626)))) (@Fin.val n a) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 628) (instOfNatNat (nat_lit 628)))) (@Fin.val n z) →
            @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 612) (instOfNatNat (nat_lit 612)))) f →
              @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
                @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) counter) →
                      ∃ cost t,
                        And
                          (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                            DecrAlmostLinearSSSP.Decremental.CoreInitializeContributions.code s cost t)
                          (And
                            (@LE.le.{0} Nat instLENat cost
                              (@OfNat.ofNat.{0} Nat (nat_lit 42) (instOfNatNat (nat_lit 42))))
                            (And
                              (@DecrAlmostLinearSSSP.Decremental.CoreDegree.Image n base
                                (@List.cons.{0} (Fin n) z heads) t)
                              (And
                                (@DecrAlmostLinearSSSP.Decremental.CoreGradient.Image n base
                                  (fun v =>
                                    @HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (g v)
                                        (@ite.{1} Real (@Eq.{1} (Fin n) v a) (instDecidableEqFin n v a) f
                                          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
                                      (@ite.{1} Real (@Eq.{1} (Fin n) v z) (instDecidableEqFin n v z) f
                                        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
                                  t)
                                (And
                                  (@Eq.{1} Nat
                                    (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) counter
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                  (And
                                    (∀ (j : Nat),
                                      @Ne.{1} Nat j
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                              (@Fin.val n z))) →
                                        @Eq.{1} Nat (t.natMem j) (s.natMem j))
                                    (∀ (j : Nat),
                                      @Ne.{1} Nat j
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                              (@Fin.val n a))) →
                                        @Ne.{1} Nat j
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                (@Fin.val n z))) →
                                          @Eq.{1} Real (t.realMem j) (s.realMem j))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_7.2.2.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreInitializeContributions.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 550) (instOfNatNat (nat_lit 550))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 620) (instOfNatNat (nat_lit 620))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 632) (instOfNatNat (nat_lit 632))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 634) (instOfNatNat (nat_lit 634))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 662) (instOfNatNat (nat_lit 662))) →
              DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
                DecrAlmostLinearSSSP.Decremental.CoreInitializeContributions.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_7.2.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Structured.Eval.assoc : ∀ {a b c : DecrAlmostLinearSSSP.Decremental.Structured.Cmd} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {cost : Nat},
  DecrAlmostLinearSSSP.Decremental.Structured.Eval ((a.seq b).seq c) s cost t →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval (a.seq (b.seq c)) s cost t := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_7.2.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.eval_code : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (e : Fin b.input.k)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured b.input s →
    DecrAlmostLinearSSSP.Decremental.CoreParameters.Values b K s →
      DecrAlmostLinearSSSP.Decremental.CoreControl.Layout b B s →
        DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.Tape b.input s →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val b.input.k e)) →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 652) (instOfNatNat (nat_lit 652))))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b.input.n
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (@Fin.val b.input.k e))) →
              @DecrAlmostLinearSSSP.Decremental.CoreDegree.Image b.input.n
                  (DecrAlmostLinearSSSP.Decremental.CoreMemory.gradientBase b B)
                  (DecrAlmostLinearSSSP.Decremental.CoreDegree.heads b (@Fin.val b.input.k e)) s →
                @DecrAlmostLinearSSSP.Decremental.CoreGradient.Image b.input.n
                    (DecrAlmostLinearSSSP.Decremental.CoreMemory.gradientBase b B)
                    (DecrAlmostLinearSSSP.Decremental.initialGradientThrough b (@Fin.val b.input.k e)) s →
                  @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 608) (instOfNatNat (nat_lit 608))))
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
                    @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 610) (instOfNatNat (nat_lit 610))))
                        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
                      ∃ cost t,
                        And
                          (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                            DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.code s cost t)
                          (And
                            (@LE.le.{0} Nat instLENat cost
                              (@OfNat.ofNat.{0} Nat (nat_lit 83) (instOfNatNat (nat_lit 83))))
                            (And
                              (DecrAlmostLinearSSSP.Decremental.CoreRecord.Initialized b B
                                (@Sum.inl.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) e) t)
                              (And
                                (@DecrAlmostLinearSSSP.Decremental.CoreDegree.Image b.input.n
                                  (DecrAlmostLinearSSSP.Decremental.CoreMemory.gradientBase b B)
                                  (DecrAlmostLinearSSSP.Decremental.CoreDegree.heads b
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@Fin.val b.input.k e)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                  t)
                                (And
                                  (@DecrAlmostLinearSSSP.Decremental.CoreGradient.Image b.input.n
                                    (DecrAlmostLinearSSSP.Decremental.CoreMemory.gradientBase b B)
                                    (DecrAlmostLinearSSSP.Decremental.initialGradientThrough b
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@Fin.val b.input.k e)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                    t)
                                  (And
                                    (@Eq.{1} Nat
                                      (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@Fin.val b.input.k e)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                    (And
                                      (@Eq.{1} Nat
                                        (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 652) (instOfNatNat (nat_lit 652))))
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b.input.n
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Fin.val b.input.k e)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                                      (∀ (j : Nat),
                                        (∀ (offset : Nat),
                                            @LT.lt.{0} Nat instLTNat offset
                                                (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
                                              @Ne.{1} Nat j
                                                (DecrAlmostLinearSSSP.Decremental.CoreMemory.field b B
                                                  (@Sum.inl.{0, 0} (Fin b.input.k)
                                                    (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) e)
                                                  offset)) →
                                          @Ne.{1} Nat j
                                              (DecrAlmostLinearSSSP.Decremental.CoreMemory.gradientCell b B
                                                (@DecrAlmostLinearSSSP.Decremental.Digraph.tail b.input.n b.input.k
                                                  b.input.graph e)) →
                                            @Ne.{1} Nat j
                                                (DecrAlmostLinearSSSP.Decremental.CoreMemory.gradientCell b B
                                                  (@DecrAlmostLinearSSSP.Decremental.Digraph.head b.input.n b.input.k
                                                    b.input.graph e)) →
                                              And (@Eq.{1} Nat (t.natMem j) (s.natMem j))
                                                (@Eq.{1} Real (t.realMem j) (s.realMem j))))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_7.2.2.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.Invariant.step : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (upto : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b.input.n
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) b.input.k))
      B →
    DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.Invariant b B K upto s →
      @LT.lt.{0} Nat instLTNat upto b.input.k →
        ∃ cost t,
          And
            (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.code s
              cost t)
            (And (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 83) (instOfNatNat (nat_lit 83))))
              (And
                (DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.Invariant b B K
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) upto
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  t)
                (DecrAlmostLinearSSSP.Decremental.CoreMemory.Frame b B s t))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_7.2.2.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.Invariant.start : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured b.input s →
    DecrAlmostLinearSSSP.Decremental.CoreParameters.Values b K s →
      DecrAlmostLinearSSSP.Decremental.CoreControl.Layout b B s →
        DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.Tape b.input s →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 550) (instOfNatNat (nat_lit 550))))
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
            (∀ (v : Fin b.input.n),
                And
                  (@Eq.{1} Nat (s.natMem (DecrAlmostLinearSSSP.Decremental.CoreMemory.gradientCell b B v))
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (@Eq.{1} Real (s.realMem (DecrAlmostLinearSSSP.Decremental.CoreMemory.gradientCell b B v))
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))) →
              DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.Invariant b B K
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.started s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_7.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CorePending.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 546) (instOfNatNat (nat_lit 546))) →
    Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 562) (instOfNatNat (nat_lit 562))))
        (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 572) (instOfNatNat (nat_lit 572))) k) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CorePending.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_8.1.1.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.CorePending.real_frame : ∀ (k : Nat), DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CorePending.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_8.1.1.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.CorePending.MemoryFrame.trans : ∀ {B l : Nat} {s t u : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.CorePending.MemoryFrame B l s t →
    DecrAlmostLinearSSSP.Decremental.CorePending.MemoryFrame B l t u →
      DecrAlmostLinearSSSP.Decremental.CorePending.MemoryFrame B l s u := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_8.1.1.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreHost.Address.below_source : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B address : Nat),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Address b B address →
    @LT.lt.{0} Nat instLTNat address (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_8.1.2.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreHost.Address.guest_disjoint : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B address : Nat),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Address b B address →
    ∀ (a : Nat),
      @Ne.{1} Nat address
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_8.1.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreHost.source_frame : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B N entry : Nat) (K : Real)
  (state : DecrAlmostLinearSSSP.Decremental.State b) (p : DecrAlmostLinearSSSP.Decremental.Program)
  (s t : DecrAlmostLinearSSSP.Decremental.Structured.Data) (cost : Nat),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    @LE.le.{0} Nat instLENat b.input.n B →
      DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.SourceCall.code N entry p) s
          cost t →
        (∀ (address : Nat),
            (∀ (a : Nat),
                @Ne.{1} Nat address
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) →
              @Ne.{1} Nat address
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B)
                    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))) →
                (∀ (j : Nat),
                    @LT.lt.{0} Nat instLTNat j N →
                      @Ne.{1} Nat address
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B)
                            (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j))) →
                  And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                    (@Eq.{1} Real (t.realMem address) (s.realMem address))) →
          DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state t := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_8.1.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreHost.Preserves.seq : ∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {B : Nat} {K : Real} {state : DecrAlmostLinearSSSP.Decremental.State b}
  {a c : DecrAlmostLinearSSSP.Decremental.Structured.Cmd},
  DecrAlmostLinearSSSP.Decremental.CoreHost.Preserves b B K state a →
    DecrAlmostLinearSSSP.Decremental.CoreHost.Preserves b B K state c →
      DecrAlmostLinearSSSP.Decremental.CoreHost.Preserves b B K state (a.seq c) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_8.2.1.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreNativeCut.call : ∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {B N m exponent : Nat} {K K0 ξ h Γ init : Real}
  {state : DecrAlmostLinearSSSP.Decremental.State b} {impl : DecrAlmostLinearSSSP.Decremental.CutImplementation}
  {first current : DecrAlmostLinearSSSP.Decremental.Machine}
  {ops : List.{0} (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b))}
  {cs : List.{0} DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.CutSession impl b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b) m
      exponent first K0 ξ h Γ init →
    DecrAlmostLinearSSSP.Decremental.CutRun impl b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b) m exponent
        first ops cs →
      @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Machine)
          (@List.getLast?.{0} DecrAlmostLinearSSSP.Decremental.Machine cs)
          (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Machine current) →
        ∀ (op : DecrAlmostLinearSSSP.Decremental.CutOp b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)),
          @DecrAlmostLinearSSSP.Decremental.CutOp.Valid b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
              (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b) current) op →
            @DecrAlmostLinearSSSP.Decremental.Physical.Valid b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                (@DecrAlmostLinearSSSP.Decremental.applyPhysical b.input.n
                  (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                  (@DecrAlmostLinearSSSP.Decremental.CutState.physical b.input.n
                    (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                    (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b) current))
                  op)
                m exponent →
              @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) N →
                @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.registerBound impl.program.code) N →
                  DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail N current →
                    ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
                      DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
                        @LE.le.{0} Nat instLENat b.input.n B →
                          ∀ (setup : DecrAlmostLinearSSSP.Decremental.Structured.Cmd) (setupCost : Nat),
                            DecrAlmostLinearSSSP.Decremental.CoreHost.Preserves b B K state setup →
                              (∃ u,
                                  And (DecrAlmostLinearSSSP.Decremental.Structured.Eval setup s setupCost u)
                                    (DecrAlmostLinearSSSP.Decremental.CoreSource.Image B
                                      (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N
                                      (@DecrAlmostLinearSSSP.Decremental.cutRequest b.input.n
                                        (DecrAlmostLinearSSSP.Decremental.logicalCount b) impl.program current op)
                                      u)) →
                                ∃ cost t final,
                                  And
                                    (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                      (setup.seq
                                        (DecrAlmostLinearSSSP.Decremental.SourceCall.code N impl.program.update
                                          impl.program))
                                      s cost t)
                                    (And
                                      (@LE.le.{0} Nat instLENat cost
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) setupCost
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (DecrAlmostLinearSSSP.Decremental.dispatchCharge impl.program.code)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                                                  final.work current.work)))
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) N))
                                          (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))))
                                      (And (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state t)
                                        (And
                                          (DecrAlmostLinearSSSP.Decremental.CoreSource.Image B
                                            (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N final t)
                                          (And
                                            (DecrAlmostLinearSSSP.Decremental.ShadowDataRep B
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) t final)
                                            (And (DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail N final)
                                              (And
                                                (DecrAlmostLinearSSSP.Decremental.Ends impl.program
                                                  (@DecrAlmostLinearSSSP.Decremental.cutRequest b.input.n
                                                    (DecrAlmostLinearSSSP.Decremental.logicalCount b) impl.program
                                                    current op)
                                                  final)
                                                (And
                                                  (@DecrAlmostLinearSSSP.Decremental.CutTransition b.input.n
                                                    (DecrAlmostLinearSSSP.Decremental.logicalCount b) K0 ξ
                                                    (impl.view b.input.n
                                                      (DecrAlmostLinearSSSP.Decremental.logicalCount b) current)
                                                    op final
                                                    (impl.view b.input.n
                                                      (DecrAlmostLinearSSSP.Decremental.logicalCount b) final))
                                                  (DecrAlmostLinearSSSP.Decremental.CutRun impl b.input.n
                                                    (DecrAlmostLinearSSSP.Decremental.logicalCount b) m exponent first
                                                    (@HAppend.hAppend.{0, 0, 0}
                                                      (List.{0}
                                                        (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                          (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                                      (List.{0}
                                                        (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                          (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                                      (List.{0}
                                                        (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                          (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                                      (@instHAppendOfAppend.{0}
                                                        (List.{0}
                                                          (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                            (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                                        (@List.instAppend.{0}
                                                          (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                            (DecrAlmostLinearSSSP.Decremental.logicalCount b))))
                                                      ops
                                                      (@List.cons.{0}
                                                        (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                          (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                                        op
                                                        (@List.nil.{0}
                                                          (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                            (DecrAlmostLinearSSSP.Decremental.logicalCount b)))))
                                                    (@HAppend.hAppend.{0, 0, 0}
                                                      (List.{0} DecrAlmostLinearSSSP.Decremental.Machine)
                                                      (List.{0} DecrAlmostLinearSSSP.Decremental.Machine)
                                                      (List.{0} DecrAlmostLinearSSSP.Decremental.Machine)
                                                      (@instHAppendOfAppend.{0}
                                                        (List.{0} DecrAlmostLinearSSSP.Decremental.Machine)
                                                        (@List.instAppend.{0} DecrAlmostLinearSSSP.Decremental.Machine))
                                                      cs
                                                      (@List.cons.{0} DecrAlmostLinearSSSP.Decremental.Machine final
                                                        (@List.nil.{0}
                                                          DecrAlmostLinearSSSP.Decremental.Machine))))))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_8.2.1.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.report_bound : ∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {B N m exponent : Nat} {K0 ξ h Γ init : Real}
  {impl : DecrAlmostLinearSSSP.Decremental.CutImplementation} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  (ctx : DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context b B N m exponent impl K0 ξ h Γ init s),
  @LE.le.{0} Real Real.instLE
    (@Nat.cast.{0} Real Real.instNatCast
      (DecrAlmostLinearSSSP.Decremental.reportVolume
        (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines b B N m exponent impl K0 ξ h Γ init s ctx)))
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Γ
        (@Nat.cast.{0} Real Real.instNatCast
          (@DecrAlmostLinearSSSP.Decremental.toggleVolume b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
            (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N m exponent impl K0 ξ h Γ init s ctx))))
      ξ) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_8.2.2.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.work_bound : ∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {B N m exponent : Nat} {K0 ξ h Γ init : Real}
  {impl : DecrAlmostLinearSSSP.Decremental.CutImplementation} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  (ctx : DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context b B N m exponent impl K0 ξ h Γ init s),
  @LE.le.{0} Real Real.instLE
    (@Nat.cast.{0} Real Real.instNatCast
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m exponent impl K0 ξ h Γ init s ctx).work
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
          (@List.length.{0}
            (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b))
            (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N m exponent impl K0 ξ h Γ init s ctx)))))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) init
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) h
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (@Nat.cast.{0} Real Real.instNatCast
            (@List.length.{0}
              (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b))
              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N m exponent impl K0 ξ h Γ init s ctx)))
          (@Nat.cast.{0} Real Real.instNatCast
            (DecrAlmostLinearSSSP.Decremental.reportVolume
              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines b B N m exponent impl K0 ξ h Γ init s
                ctx)))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_8.2.2.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.query : ∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {B N m exponent : Nat} {K K0 ξ h Γ init : Real}
  {impl : DecrAlmostLinearSSSP.Decremental.CutImplementation} {state : DecrAlmostLinearSSSP.Decremental.State b}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  (ctx : DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context b B N m exponent impl K0 ξ h Γ init s),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    @LE.le.{0} Nat instLENat b.input.n B →
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) N →
        @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.registerBound impl.program.code) N →
          @DecrAlmostLinearSSSP.Decremental.Physical.Valid b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
              (@DecrAlmostLinearSSSP.Decremental.CutState.physical b.input.n
                (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                  (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m exponent impl K0 ξ h Γ init s
                    ctx)))
              m exponent →
            ∀ (source : Nat),
              @Ne.{1} Nat source (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
                @Ne.{1} Nat source (@OfNat.ofNat.{0} Nat (nat_lit 632) (instOfNatNat (nat_lit 632))) →
                  ∀ (v : Fin b.input.n),
                    @Eq.{1} Nat (s.natReg source)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val b.input.n v)) →
                      ∃ cost t next,
                        And
                          (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                            (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.queryCode N source impl.program) s cost t)
                          (And
                            (@LE.le.{0} Nat instLENat cost
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (DecrAlmostLinearSSSP.Decremental.dispatchCharge impl.program.code)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                                      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m exponent
                                          impl K0 ξ h Γ init t next).work
                                      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m exponent
                                          impl K0 ξ h Γ init s ctx).work))
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) N))
                                (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))))
                            (And (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state t)
                              (And
                                (@Eq.{1}
                                  (DecrAlmostLinearSSSP.Decremental.CutState b.input.n
                                    (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                  (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                    (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m exponent
                                      impl K0 ξ h Γ init t next))
                                  (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                    (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m exponent
                                      impl K0 ξ h Γ init s ctx)))
                                (And
                                  (@Eq.{1} Real
                                    (t.realReg (@OfNat.ofNat.{0} Nat (nat_lit 29) (instOfNatNat (nat_lit 29))))
                                    (@DecrAlmostLinearSSSP.Decremental.CutState.y b.input.n
                                      (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                      (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                        (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m
                                          exponent impl K0 ξ h Γ init s ctx))
                                      v))
                                  (And
                                    (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                                      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.first b B N m exponent
                                        impl K0 ξ h Γ init t next)
                                      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.first b B N m exponent
                                        impl K0 ξ h Γ init s ctx))
                                    (And
                                      (@Eq.{1}
                                        (List.{0}
                                          (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                            (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                        (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N m exponent
                                          impl K0 ξ h Γ init t next)
                                        (@HAppend.hAppend.{0, 0, 0}
                                          (List.{0}
                                            (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                              (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                          (List.{0}
                                            (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                              (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                          (List.{0}
                                            (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                              (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                          (@instHAppendOfAppend.{0}
                                            (List.{0}
                                              (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                            (@List.instAppend.{0}
                                              (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                (DecrAlmostLinearSSSP.Decremental.logicalCount b))))
                                          (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N m exponent
                                            impl K0 ξ h Γ init s ctx)
                                          (@List.cons.{0}
                                            (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                              (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                            (@DecrAlmostLinearSSSP.Decremental.CutOp.queryY b.input.n
                                              (DecrAlmostLinearSSSP.Decremental.logicalCount b) v)
                                            (@List.nil.{0}
                                              (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                (DecrAlmostLinearSSSP.Decremental.logicalCount b))))))
                                      (And
                                        (@Eq.{1} (List.{0} DecrAlmostLinearSSSP.Decremental.Machine)
                                          (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines b B N m
                                            exponent impl K0 ξ h Γ init t next)
                                          (@HAppend.hAppend.{0, 0, 0}
                                            (List.{0} DecrAlmostLinearSSSP.Decremental.Machine)
                                            (List.{0} DecrAlmostLinearSSSP.Decremental.Machine)
                                            (List.{0} DecrAlmostLinearSSSP.Decremental.Machine)
                                            (@instHAppendOfAppend.{0}
                                              (List.{0} DecrAlmostLinearSSSP.Decremental.Machine)
                                              (@List.instAppend.{0} DecrAlmostLinearSSSP.Decremental.Machine))
                                            (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines b B N m
                                              exponent impl K0 ξ h Γ init s ctx)
                                            (@List.cons.{0} DecrAlmostLinearSSSP.Decremental.Machine
                                              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m
                                                exponent impl K0 ξ h Γ init t next)
                                              (@List.nil.{0} DecrAlmostLinearSSSP.Decremental.Machine))))
                                        (And
                                          (@LE.le.{0} Nat instLENat
                                            (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m
                                                exponent impl K0 ξ h Γ init s ctx).work
                                            (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m
                                                exponent impl K0 ξ h Γ init t next).work)
                                          (@Eq.{1} Nat
                                            (DecrAlmostLinearSSSP.Decremental.reportVolume
                                              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines b B N m
                                                exponent impl K0 ξ h Γ init t next))
                                            (DecrAlmostLinearSSSP.Decremental.reportVolume
                                              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines b B N m
                                                exponent impl K0 ξ h Γ init s ctx))))))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_8.2.2.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.Physical.Valid.erase : ∀ {n k m exponent : Nat} (h : DecrAlmostLinearSSSP.Decremental.Physical n k),
  @DecrAlmostLinearSSSP.Decremental.Physical.Valid n k h m exponent →
    ∀ (e : Fin k),
      (∀ (x : Fin n → Real),
          @Eq.{1} Real
              (@DecrAlmostLinearSSSP.Decremental.physicalNorm n k
                (@DecrAlmostLinearSSSP.Decremental.applyPhysical n k h
                  (@DecrAlmostLinearSSSP.Decremental.CutOp.erase n k e))
                x)
              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
            ∀ (v w : Fin n), @Eq.{1} Real (x v) (x w)) →
        @DecrAlmostLinearSSSP.Decremental.Physical.Valid n k
          (@DecrAlmostLinearSSSP.Decremental.applyPhysical n k h (@DecrAlmostLinearSSSP.Decremental.CutOp.erase n k e))
          m exponent := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_9.1.1.2.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.RuntimeBounds.initial : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
    DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K (DecrAlmostLinearSSSP.Decremental.initializeState b) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_9.1.2.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.cache_total_upper : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real) (s : DecrAlmostLinearSSSP.Decremental.State b),
  DecrAlmostLinearSSSP.Decremental.CacheInvariant b K s →
    @LE.le.{0} Real Real.instLE (∑ e, @DecrAlmostLinearSSSP.Decremental.State.cache b s e)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
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
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (DecrAlmostLinearSSSP.Decremental.kappa b)) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_9.2.1.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.core_cache_total_capacityBound : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core),
  @LE.le.{0} Real Real.instLE
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
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
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (DecrAlmostLinearSSSP.Decremental.kappa b))
    (@HPow.hPow.{0, 0, 0} Real Int Real
      (@instHPow.{0, 0} Real Int (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
      (DecrAlmostLinearSSSP.Decremental.kappa b)
      (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_9.2.1.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.core_Q_polynomial : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core),
  @LE.le.{0} Real Real.instLE (DecrAlmostLinearSSSP.Decremental.Q b)
    (@HPow.hPow.{0, 0, 0} Real Nat Real
      (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
      (@Nat.cast.{0} Real Real.instNatCast b.input.size)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b.weightExponent
        (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_9.2.1.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.core_capacityBound_range : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core),
  And
    (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (@HPow.hPow.{0, 0, 0} Real Int Real
        (@instHPow.{0, 0} Real Int (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
        (DecrAlmostLinearSSSP.Decremental.kappa b)
        (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))))))
    (@LE.le.{0} Real Real.instLE
      (@HPow.hPow.{0, 0, 0} Real Int Real
        (@instHPow.{0, 0} Real Int (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
        (DecrAlmostLinearSSSP.Decremental.kappa b)
        (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
      (@HPow.hPow.{0, 0, 0} Real Nat Real
        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
        (@Max.max.{0} Real Real.instMax
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
            (@Nat.cast.{0} Real Real.instNatCast b.input.size)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
          (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68)))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_9.2.1.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.runtime_indexed_physical_valid : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real) (s : DecrAlmostLinearSSSP.Decremental.State b),
  DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K s →
    ∀ {l : Nat} (E : Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)),
      @LE.le.{0} Nat instLENat l
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size) →
        @DecrAlmostLinearSSSP.Decremental.Physical.Valid b.input.n l
          (@DecrAlmostLinearSSSP.Decremental.indexedPhysical b s l E)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
            (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68)))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_9.2.1.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.CutModel.query : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) {l : Nat}
  (E : Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)) (s : DecrAlmostLinearSSSP.Decremental.State b)
  (c t : DecrAlmostLinearSSSP.Decremental.CutState b.input.n l) (K ξ : Real)
  (g : DecrAlmostLinearSSSP.Decremental.Machine) (v : Fin b.input.n),
  @DecrAlmostLinearSSSP.Decremental.CutModel b l E s c →
    @DecrAlmostLinearSSSP.Decremental.CutTransition b.input.n l K ξ c
        (@DecrAlmostLinearSSSP.Decremental.CutOp.queryY b.input.n l v) g t →
      And (@Eq.{1} (DecrAlmostLinearSSSP.Decremental.CutState b.input.n l) t c)
        (@Eq.{1} Real (g.realReg (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))))
          (@DecrAlmostLinearSSSP.Decremental.State.y b s v)) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_9.2.1.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.CutModel.initial : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) {l : Nat}
  (E : Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l))
  (c : DecrAlmostLinearSSSP.Decremental.CutState b.input.n l),
  @Eq.{1} (DecrAlmostLinearSSSP.Decremental.Physical b.input.n l)
      (@DecrAlmostLinearSSSP.Decremental.CutState.physical b.input.n l c)
      (@DecrAlmostLinearSSSP.Decremental.indexedPhysical b (DecrAlmostLinearSSSP.Decremental.initializeState b) l E) →
    @Eq.{1} (Fin b.input.n → Real) (@DecrAlmostLinearSSSP.Decremental.CutState.y b.input.n l c)
        (@OfNat.ofNat.{0} (Fin b.input.n → Real) (nat_lit 0)
          (@Zero.toOfNat0.{0} (Fin b.input.n → Real)
            (@Pi.instZero.{0, 0} (Fin b.input.n) (fun a => Real) fun i => Real.instZero))) →
      @Eq.{1} (Fin l → Real) (@DecrAlmostLinearSSSP.Decremental.CutState.baseline b.input.n l c)
          (@OfNat.ofNat.{0} (Fin l → Real) (nat_lit 0)
            (@Zero.toOfNat0.{0} (Fin l → Real) (@Pi.instZero.{0, 0} (Fin l) (fun a => Real) fun i => Real.instZero))) →
        @DecrAlmostLinearSSSP.Decremental.CutModel b l E (DecrAlmostLinearSSSP.Decremental.initializeState b) c := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_9.2.1.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreGeometry.Loaded.frame : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (e : DecrAlmostLinearSSSP.Decremental.Edge b) {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.CoreGeometry.Loaded b state e s →
    (∀ (k : Nat),
        @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat)
            (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626)))
              (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 628) (instOfNatNat (nat_lit 628)))
                (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 648) (instOfNatNat (nat_lit 648)))
                  (@List.nil.{0} Nat))))
            k →
          @Eq.{1} Nat (t.natReg k) (s.natReg k)) →
      (∀ (k : Nat),
          @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat)
              (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 600) (instOfNatNat (nat_lit 600)))
                (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 602) (instOfNatNat (nat_lit 602)))
                  (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 604) (instOfNatNat (nat_lit 604)))
                    (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 606) (instOfNatNat (nat_lit 606)))
                      (@List.nil.{0} Nat)))))
              k →
            @Eq.{1} Real (t.realReg k) (s.realReg k)) →
        DecrAlmostLinearSSSP.Decremental.CoreGeometry.Loaded b state e t := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_9.2.2.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreRefreshRead.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreRefreshRead.code s
    (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19)))
    (DecrAlmostLinearSSSP.Decremental.CoreRefreshRead.result s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_9.2.2.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreRefreshRead.no_memory : DecrAlmostLinearSSSP.Decremental.Structured.NoMemory DecrAlmostLinearSSSP.Decremental.CoreRefreshRead.code := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_10.1.1.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreRefreshRead.even_registers : @Eq.{1} Bool
  (DecrAlmostLinearSSSP.Decremental.Structured.evenRegisters DecrAlmostLinearSSSP.Decremental.CoreRefreshRead.code)
  Bool.true := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_10.1.1.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreRefreshRead.nat_frame : ∀ (k : Nat),
  Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 562) (instOfNatNat (nat_lit 562))))
      (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 648) (instOfNatNat (nat_lit 648))) k) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreRefreshRead.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_10.1.1.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreRefreshRead.real_frame : ∀ (k : Nat),
  Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 600) (instOfNatNat (nat_lit 600))))
      (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 606) (instOfNatNat (nat_lit 606))) k) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreRefreshRead.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_10.1.1.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreRefreshRead.correct : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (e : DecrAlmostLinearSSSP.Decremental.Edge b) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    @LE.le.{0} Nat instLENat b.input.n B →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
          (DecrAlmostLinearSSSP.Decremental.CoreMemory.encodedEdge b e) →
        And
          (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state
            (DecrAlmostLinearSSSP.Decremental.CoreRefreshRead.result s))
          (And
            (DecrAlmostLinearSSSP.Decremental.CoreGeometry.Loaded b state e
              (DecrAlmostLinearSSSP.Decremental.CoreRefreshRead.result s))
            (And
              (DecrAlmostLinearSSSP.Decremental.CoreRecord.Addresses
                (DecrAlmostLinearSSSP.Decremental.CoreMemory.field b B e
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                (DecrAlmostLinearSSSP.Decremental.CoreRefreshRead.result s))
              (And
                (@Eq.{1} Nat
                  ((DecrAlmostLinearSSSP.Decremental.CoreRefreshRead.result s).natReg
                    (@OfNat.ofNat.{0} Nat (nat_lit 636) (instOfNatNat (nat_lit 636))))
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (@Fin.val b.input.n (DecrAlmostLinearSSSP.Decremental.tail b e))))
                (@Eq.{1} Nat
                  ((DecrAlmostLinearSSSP.Decremental.CoreRefreshRead.result s).natReg
                    (@OfNat.ofNat.{0} Nat (nat_lit 638) (instOfNatNat (nat_lit 638))))
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (@Fin.val b.input.n (DecrAlmostLinearSSSP.Decremental.head b e))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_10.1.1.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreRefreshRead.source_frame : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B N : Nat) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreSource.Image B (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N g
      s →
    DecrAlmostLinearSSSP.Decremental.CoreSource.Image B (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N
      g (DecrAlmostLinearSSSP.Decremental.CoreRefreshRead.result s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_10.1.1.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreGradientDelta.even_registers : @Eq.{1} Bool
  (DecrAlmostLinearSSSP.Decremental.Structured.evenRegisters DecrAlmostLinearSSSP.Decremental.CoreGradientDelta.code)
  Bool.true := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_10.1.1.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreGradientDelta.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 550) (instOfNatNat (nat_lit 550))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 620) (instOfNatNat (nat_lit 620))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 632) (instOfNatNat (nat_lit 632))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 634) (instOfNatNat (nat_lit 634))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreGradientDelta.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_10.1.1.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreGradientDelta.real_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 612) (instOfNatNat (nat_lit 612))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 698) (instOfNatNat (nat_lit 698))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 628) (instOfNatNat (nat_lit 628))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
            DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
              DecrAlmostLinearSSSP.Decremental.CoreGradientDelta.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_10.1.1.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreGradientDelta.eval_code : ∀ {n : Nat} (base : Nat) (g : Fin n → Real) (a z : Fin n) (delta f : Real)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @DecrAlmostLinearSSSP.Decremental.CoreGradient.Image n base g s →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 554) (instOfNatNat (nat_lit 554)))) base →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626)))) (@Fin.val n a) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 628) (instOfNatNat (nat_lit 628)))) (@Fin.val n z) →
          @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 614) (instOfNatNat (nat_lit 614)))) delta →
            @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 612) (instOfNatNat (nat_lit 612)))) f →
              @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
                ∃ cost t,
                  And
                    (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                      DecrAlmostLinearSSSP.Decremental.CoreGradientDelta.code s cost t)
                    (And (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 39) (instOfNatNat (nat_lit 39))))
                      (And
                        (@DecrAlmostLinearSSSP.Decremental.CoreGradient.Image n base
                          (fun v =>
                            @HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (g v)
                                (@ite.{1} Real (@Eq.{1} (Fin n) v a) (instDecidableEqFin n v a) delta
                                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
                              (@ite.{1} Real (@Eq.{1} (Fin n) v z) (instDecidableEqFin n v z) delta
                                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
                          t)
                        (And
                          (@Eq.{1} Real (t.realReg (@OfNat.ofNat.{0} Nat (nat_lit 612) (instOfNatNat (nat_lit 612)))) f)
                          (And (@Eq.{1} (Nat → Nat) t.natMem s.natMem)
                            (∀ (j : Nat),
                              @Ne.{1} Nat j
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val n a))) →
                                @Ne.{1} Nat j
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val n z))) →
                                  @Eq.{1} Real (t.realMem j) (s.realMem j)))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_10.1.1.2.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreCommit.prefix_eval : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B N : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (e : DecrAlmostLinearSSSP.Decremental.Edge b) (f delta : Real) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    DecrAlmostLinearSSSP.Decremental.CoreSource.Image B (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N
        g s →
      @LE.le.{0} Nat instLENat b.input.n B →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 568) (instOfNatNat (nat_lit 568))))
            (DecrAlmostLinearSSSP.Decremental.CoreMemory.field b B e
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626))))
              (@Fin.val b.input.n (DecrAlmostLinearSSSP.Decremental.tail b e)) →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 628) (instOfNatNat (nat_lit 628))))
                (@Fin.val b.input.n (DecrAlmostLinearSSSP.Decremental.head b e)) →
              @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 612) (instOfNatNat (nat_lit 612)))) f →
                @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 614) (instOfNatNat (nat_lit 614)))) delta →
                  ∃ cost t,
                    And
                      (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                        DecrAlmostLinearSSSP.Decremental.CoreCommit.prefixCode s cost t)
                      (And
                        (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40))))
                        (And
                          (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K
                            (DecrAlmostLinearSSSP.Decremental.CoreCommit.cacheGradientState b state e f delta) t)
                          (And
                            (DecrAlmostLinearSSSP.Decremental.CoreSource.Image B
                              (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N g t)
                            (@Eq.{1} Real (t.realReg (@OfNat.ofNat.{0} Nat (nat_lit 612) (instOfNatNat (nat_lit 612))))
                              f)))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_10.1.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreHeadSelect.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreHeadSelect.code s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    (DecrAlmostLinearSSSP.Decremental.CoreHeadSelect.result s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_10.1.2.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreHeadSelect.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreHeadSelect.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_10.1.2.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreHeadSelect.real_frame : ∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreHeadSelect.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_10.1.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreHeadSelect.no_memory : DecrAlmostLinearSSSP.Decremental.Structured.NoMemory DecrAlmostLinearSSSP.Decremental.CoreHeadSelect.code := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_10.1.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreHeadSelect.even_registers : @Eq.{1} Bool
  (DecrAlmostLinearSSSP.Decremental.Structured.evenRegisters DecrAlmostLinearSSSP.Decremental.CoreHeadSelect.code)
  Bool.true := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_10.1.2.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreHeadSelect.correct : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B N : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (e : DecrAlmostLinearSSSP.Decremental.Edge b) (xs : List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
  (g : DecrAlmostLinearSSSP.Decremental.Machine) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    DecrAlmostLinearSSSP.Decremental.CoreSource.Image B (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N
        g s →
      @LE.le.{0} Nat instLENat b.input.n B →
        @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
            (@DecrAlmostLinearSSSP.Decremental.State.pending b state)
            (@List.cons.{0} (DecrAlmostLinearSSSP.Decremental.Edge b) e xs) →
          And
            (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state
              (DecrAlmostLinearSSSP.Decremental.CoreHeadSelect.result s))
            (And
              (DecrAlmostLinearSSSP.Decremental.CoreSource.Image B
                (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N g
                (DecrAlmostLinearSSSP.Decremental.CoreHeadSelect.result s))
              (@Eq.{1} Nat
                ((DecrAlmostLinearSSSP.Decremental.CoreHeadSelect.result s).natReg
                  (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
                (DecrAlmostLinearSSSP.Decremental.CoreMemory.encodedEdge b e))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_10.2.1.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreReports.eval_code : ∀ (B l : Nat) (g : DecrAlmostLinearSSSP.Decremental.Machine) (xs : List.{0} (Fin l))
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreReports.Environment B l s →
    @DecrAlmostLinearSSSP.Decremental.CorePending.View l B xs s →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
        DecrAlmostLinearSSSP.Decremental.ShadowDataRep B (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) s
            g →
          ∃ cost t,
            And
              (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreReports.code s cost
                t)
              (And
                (@LE.le.{0} Nat instLENat cost
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))
                      (DecrAlmostLinearSSSP.Decremental.reportCount g))
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
                (And
                  (@DecrAlmostLinearSSSP.Decremental.CorePending.View l B
                    (DecrAlmostLinearSSSP.Decremental.CoreReports.consume l xs
                      (DecrAlmostLinearSSSP.Decremental.CoreReports.reportList g))
                    t)
                  (And (DecrAlmostLinearSSSP.Decremental.CoreReports.Environment B l t)
                    (And (@Eq.{1} (Nat → Real) t.realMem s.realMem)
                      (And
                        (∀ (j : Nat),
                          @Eq.{1} Nat
                            (t.natMem
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) j))
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                            (s.natMem
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) j))
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                        (And
                          (∀ (e : Fin l),
                            Iff
                              (@Membership.mem.{0, 0} (Fin l) (List.{0} (Fin l)) (@List.instMembership.{0} (Fin l))
                                (DecrAlmostLinearSSSP.Decremental.CoreReports.consume l xs
                                  (DecrAlmostLinearSSSP.Decremental.CoreReports.reportList g))
                                e)
                              (Or
                                (@Membership.mem.{0, 0} (Fin l) (List.{0} (Fin l)) (@List.instMembership.{0} (Fin l)) xs
                                  e)
                                (@DecrAlmostLinearSSSP.Decremental.Reported l g e)))
                          (DecrAlmostLinearSSSP.Decremental.CorePending.MemoryFrame B l s t))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_10.2.2.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreRatioGuard.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreRatioGuard.code s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    (DecrAlmostLinearSSSP.Decremental.CoreRatioGuard.result s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_11.1.1.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreRatioGuard.nat_frame : ∀ (k : Nat), DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreRatioGuard.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_11.1.1.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreRatioGuard.real_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 700) (instOfNatNat (nat_lit 700))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreRatioGuard.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_11.1.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Repair.step : ∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {B N offset : Nat} {K K0 h Γ init : Real}
  {impl : DecrAlmostLinearSSSP.Decremental.CutImplementation} {first : DecrAlmostLinearSSSP.Decremental.Machine}
  {active : Finset.{0} (Fin b.input.k)},
  @LE.le.{0} Nat instLENat b.input.n B →
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) N →
      @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.registerBound impl.program.code) N →
        @LE.le.{0} Real Real.instLE
            (@OfNat.ofNat.{0} Real (nat_lit 32)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
            K →
          @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K0 →
            @LE.le.{0} Real Real.instLE K0 K →
              DecrAlmostLinearSSSP.Decremental.CutSession impl b.input.n
                  (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                    (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                  first K0
                  (@HPow.hPow.{0, 0, 0} Real Int Real
                    (@instHPow.{0, 0} Real Int
                      (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                    K (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                  h Γ init →
                ∀ (q : DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Repair.Snapshot b)
                  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
                  DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Repair.Repr b B N offset K K0 h Γ init impl first
                      active q s →
                    (DecrAlmostLinearSSSP.Decremental.Structured.Test.natLess
                            (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56)))
                            (@OfNat.ofNat.{0} Nat (nat_lit 650) (instOfNatNat (nat_lit 650)))).holds
                        s →
                      ∃ q' t cost,
                        And
                          (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                            (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.bodyCode N impl.program) s cost t)
                          (And
                            (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Repair.Repr b B N offset K K0 h Γ init impl
                              first active q' t)
                            (And (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Repair.relation b K q' q)
                              (@LE.le.{0} Nat instLENat
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cost
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Repair.credit b N impl.program q))
                                (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Repair.credit b N impl.program q')))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_11.1.2.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Repair.Repr.stopped : ∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {B N offset : Nat} {K K0 h Γ init : Real}
  {impl : DecrAlmostLinearSSSP.Decremental.CutImplementation} {first : DecrAlmostLinearSSSP.Decremental.Machine}
  {active : Finset.{0} (Fin b.input.k)} {q : DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Repair.Snapshot b}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Repair.Repr b B N offset K K0 h Γ init impl first active q s →
    Not
        ((DecrAlmostLinearSSSP.Decremental.Structured.Test.natLess
              (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56)))
              (@OfNat.ofNat.{0} Nat (nat_lit 650) (instOfNatNat (nat_lit 650)))).holds
          s) →
      @Eq.{1} Bool
        (@DecrAlmostLinearSSSP.Decremental.State.stopped b
          (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Repair.Snapshot.state b q))
        Bool.true := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_11.1.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreRepairControl.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreRepairControl.code s
    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
    (DecrAlmostLinearSSSP.Decremental.CoreRepairControl.result s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_11.1.2.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreRepairControl.values : ∀ (K : Real) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512)))) K →
    And
      (@Eq.{1} Nat
        ((DecrAlmostLinearSSSP.Decremental.CoreRepairControl.result s).natReg
          (@OfNat.ofNat.{0} Nat (nat_lit 650) (instOfNatNat (nat_lit 650))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@Eq.{1} Real
        ((DecrAlmostLinearSSSP.Decremental.CoreRepairControl.result s).realReg
          (@OfNat.ofNat.{0} Nat (nat_lit 520) (instOfNatNat (nat_lit 520))))
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 4)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
            K))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_11.2.1.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreRepairControl.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 650) (instOfNatNat (nat_lit 650))) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreRepairControl.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_11.2.1.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreRepairControl.real_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 520) (instOfNatNat (nat_lit 520))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 656) (instOfNatNat (nat_lit 656))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 658) (instOfNatNat (nat_lit 658))) →
        DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreRepairControl.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_11.2.1.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreRepairControl.no_memory : DecrAlmostLinearSSSP.Decremental.Structured.NoMemory DecrAlmostLinearSSSP.Decremental.CoreRepairControl.code := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_11.2.1.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreRepairControl.even_registers : @Eq.{1} Bool
  (DecrAlmostLinearSSSP.Decremental.Structured.evenRegisters DecrAlmostLinearSSSP.Decremental.CoreRepairControl.code)
  Bool.true := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_11.2.1.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.repair : ∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {B N : Nat} {K K0 h Γ init : Real}
  {impl : DecrAlmostLinearSSSP.Decremental.CutImplementation} {state : DecrAlmostLinearSSSP.Decremental.State b}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  (ctx :
    DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context b B N
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
        (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
      impl K0
      (@HPow.hPow.{0, 0, 0} Real Int Real
        (@instHPow.{0, 0} Real Int (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid))) K
        (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
      h Γ init s),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    @LE.le.{0} Nat instLENat b.input.n B →
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) N →
        @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.registerBound impl.program.code) N →
          @LE.le.{0} Real Real.instLE
              (@OfNat.ofNat.{0} Real (nat_lit 32)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
              K →
            @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K0 →
              @LE.le.{0} Real Real.instLE K0 K →
                DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K state →
                  @DecrAlmostLinearSSSP.Decremental.CutModel b (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                      (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b) state
                      (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                        (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                            (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                          impl K0
                          (@HPow.hPow.{0, 0, 0} Real Int Real
                            (@instHPow.{0, 0} Real Int
                              (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                            K
                            (@Neg.neg.{0} Int Int.instNegInt
                              (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                          h Γ init s ctx)) →
                    @Eq.{1} Bool (@DecrAlmostLinearSSSP.Decremental.State.stopped b state) Bool.false →
                      ∀ (offset : Nat),
                        DecrAlmostLinearSSSP.Decremental.CoreRepair.OperationDebt b state
                            (@List.length.{0}
                              (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                impl K0
                                (@HPow.hPow.{0, 0, 0} Real Int Real
                                  (@instHPow.{0, 0} Real Int
                                    (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                  K
                                  (@Neg.neg.{0} Int Int.instNegInt
                                    (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                h Γ init s ctx))
                            (DecrAlmostLinearSSSP.Decremental.reportVolume
                              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines b B N
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                impl K0
                                (@HPow.hPow.{0, 0, 0} Real Int Real
                                  (@instHPow.{0, 0} Real Int
                                    (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                  K
                                  (@Neg.neg.{0} Int Int.instNegInt
                                    (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                h Γ init s ctx))
                            offset →
                          @Eq.{1} Nat
                              (@DecrAlmostLinearSSSP.Decremental.toggleVolume b.input.n
                                (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                  impl K0
                                  (@HPow.hPow.{0, 0, 0} Real Int Real
                                    (@instHPow.{0, 0} Real Int
                                      (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                    K
                                    (@Neg.neg.{0} Int Int.instNegInt
                                      (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                  h Γ init s ctx))
                              (@DecrAlmostLinearSSSP.Decremental.State.toggles b state) →
                            ∃ cost t after next,
                              And
                                (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                  (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.repairCode N impl.program) s cost t)
                                (And (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K after t)
                                  (And (DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K after)
                                    (And
                                      (@DecrAlmostLinearSSSP.Decremental.CutModel b
                                        (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                        (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b) after
                                        (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                          (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                              b.input.size)
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                b.weightExponent)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                            impl K0
                                            (@HPow.hPow.{0, 0, 0} Real Int Real
                                              (@instHPow.{0, 0} Real Int
                                                (@ZPow.toPow.{0} Real
                                                  (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                              K
                                              (@Neg.neg.{0} Int Int.instNegInt
                                                (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                            h Γ init t next)))
                                      (And
                                        (@Eq.{1} Bool (@DecrAlmostLinearSSSP.Decremental.State.stopped b after)
                                          Bool.true)
                                        (And (DecrAlmostLinearSSSP.Decremental.ReadoutCertificate b after)
                                          (And
                                            (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                                              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.first b B N
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                  b.input.size)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                    b.weightExponent)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                impl K0
                                                (@HPow.hPow.{0, 0, 0} Real Int Real
                                                  (@instHPow.{0, 0} Real Int
                                                    (@ZPow.toPow.{0} Real
                                                      (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                  K
                                                  (@Neg.neg.{0} Int Int.instNegInt
                                                    (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                                h Γ init t next)
                                              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.first b B N
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                  b.input.size)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                    b.weightExponent)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                impl K0
                                                (@HPow.hPow.{0, 0, 0} Real Int Real
                                                  (@instHPow.{0, 0} Real Int
                                                    (@ZPow.toPow.{0} Real
                                                      (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                  K
                                                  (@Neg.neg.{0} Int Int.instNegInt
                                                    (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                                h Γ init s ctx))
                                            (And
                                              (DecrAlmostLinearSSSP.Decremental.CoreRepair.OperationDebt b after
                                                (@List.length.{0}
                                                  (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                    (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                                  (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                      b.input.size)
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                        b.weightExponent)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                    impl K0
                                                    (@HPow.hPow.{0, 0, 0} Real Int Real
                                                      (@instHPow.{0, 0} Real Int
                                                        (@ZPow.toPow.{0} Real
                                                          (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                      K
                                                      (@Neg.neg.{0} Int Int.instNegInt
                                                        (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                                    h Γ init t next))
                                                (DecrAlmostLinearSSSP.Decremental.reportVolume
                                                  (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines b B
                                                    N
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                      b.input.size)
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                        b.weightExponent)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                    impl K0
                                                    (@HPow.hPow.{0, 0, 0} Real Int Real
                                                      (@instHPow.{0, 0} Real Int
                                                        (@ZPow.toPow.{0} Real
                                                          (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                      K
                                                      (@Neg.neg.{0} Int Int.instNegInt
                                                        (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                                    h Γ init t next))
                                                offset)
                                              (And
                                                (@Eq.{1} Nat
                                                  (@DecrAlmostLinearSSSP.Decremental.toggleVolume b.input.n
                                                    (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                                    (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                        b.input.size)
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                          b.weightExponent)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                      impl K0
                                                      (@HPow.hPow.{0, 0, 0} Real Int Real
                                                        (@instHPow.{0, 0} Real Int
                                                          (@ZPow.toPow.{0} Real
                                                            (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                        K
                                                        (@Neg.neg.{0} Int Int.instNegInt
                                                          (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                                      h Γ init t next))
                                                  (@DecrAlmostLinearSSSP.Decremental.State.toggles b after))
                                                (And
                                                  (@Eq.{1} (Finset.{0} (Fin b.input.k))
                                                    (@DecrAlmostLinearSSSP.Decremental.State.active b after)
                                                    (@DecrAlmostLinearSSSP.Decremental.State.active b state))
                                                  (And
                                                    (@Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
                                                      (@DecrAlmostLinearSSSP.Decremental.State.pending b after)
                                                      (@List.nil.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)))
                                                    (@LE.le.{0} Nat instLENat
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        cost
                                                        (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.credit b N
                                                          impl.program state
                                                          (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current
                                                            b B N
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                (instOfNatNat (nat_lit 2)))
                                                              b.input.size)
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                (@instHMul.{0} Nat instMulNat)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                  (instOfNatNat (nat_lit 4)))
                                                                b.weightExponent)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                                (instOfNatNat (nat_lit 68))))
                                                            impl K0
                                                            (@HPow.hPow.{0, 0, 0} Real Int Real
                                                              (@instHPow.{0, 0} Real Int
                                                                (@ZPow.toPow.{0} Real
                                                                  (@DivInvMonoid.toZPow.{0} Real
                                                                    Real.instDivInvMonoid)))
                                                              K
                                                              (@Neg.neg.{0} Int Int.instNegInt
                                                                (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                                  (@instOfNat (nat_lit 2)))))
                                                            h Γ init s ctx)
                                                          (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b
                                                            B N
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                (instOfNatNat (nat_lit 2)))
                                                              b.input.size)
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                (@instHMul.{0} Nat instMulNat)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                  (instOfNatNat (nat_lit 4)))
                                                                b.weightExponent)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                                (instOfNatNat (nat_lit 68))))
                                                            impl K0
                                                            (@HPow.hPow.{0, 0, 0} Real Int Real
                                                              (@instHPow.{0, 0} Real Int
                                                                (@ZPow.toPow.{0} Real
                                                                  (@DivInvMonoid.toZPow.{0} Real
                                                                    Real.instDivInvMonoid)))
                                                              K
                                                              (@Neg.neg.{0} Int Int.instNegInt
                                                                (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                                  (@instOfNat (nat_lit 2)))))
                                                            h Γ init s ctx)
                                                          (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines
                                                            b B N
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                (instOfNatNat (nat_lit 2)))
                                                              b.input.size)
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                (@instHMul.{0} Nat instMulNat)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                  (instOfNatNat (nat_lit 4)))
                                                                b.weightExponent)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                                (instOfNatNat (nat_lit 68))))
                                                            impl K0
                                                            (@HPow.hPow.{0, 0, 0} Real Int Real
                                                              (@instHPow.{0, 0} Real Int
                                                                (@ZPow.toPow.{0} Real
                                                                  (@DivInvMonoid.toZPow.{0} Real
                                                                    Real.instDivInvMonoid)))
                                                              K
                                                              (@Neg.neg.{0} Int Int.instNegInt
                                                                (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                                  (@instOfNat (nat_lit 2)))))
                                                            h Γ init s ctx)))
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.credit b N
                                                          impl.program after
                                                          (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current
                                                            b B N
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                (instOfNatNat (nat_lit 2)))
                                                              b.input.size)
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                (@instHMul.{0} Nat instMulNat)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                  (instOfNatNat (nat_lit 4)))
                                                                b.weightExponent)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                                (instOfNatNat (nat_lit 68))))
                                                            impl K0
                                                            (@HPow.hPow.{0, 0, 0} Real Int Real
                                                              (@instHPow.{0, 0} Real Int
                                                                (@ZPow.toPow.{0} Real
                                                                  (@DivInvMonoid.toZPow.{0} Real
                                                                    Real.instDivInvMonoid)))
                                                              K
                                                              (@Neg.neg.{0} Int Int.instNegInt
                                                                (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                                  (@instOfNat (nat_lit 2)))))
                                                            h Γ init t next)
                                                          (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b
                                                            B N
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                (instOfNatNat (nat_lit 2)))
                                                              b.input.size)
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                (@instHMul.{0} Nat instMulNat)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                  (instOfNatNat (nat_lit 4)))
                                                                b.weightExponent)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                                (instOfNatNat (nat_lit 68))))
                                                            impl K0
                                                            (@HPow.hPow.{0, 0, 0} Real Int Real
                                                              (@instHPow.{0, 0} Real Int
                                                                (@ZPow.toPow.{0} Real
                                                                  (@DivInvMonoid.toZPow.{0} Real
                                                                    Real.instDivInvMonoid)))
                                                              K
                                                              (@Neg.neg.{0} Int Int.instNegInt
                                                                (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                                  (@instOfNat (nat_lit 2)))))
                                                            h Γ init t next)
                                                          (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines
                                                            b B N
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                (instOfNatNat (nat_lit 2)))
                                                              b.input.size)
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                (@instHMul.{0} Nat instMulNat)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                  (instOfNatNat (nat_lit 4)))
                                                                b.weightExponent)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                                (instOfNatNat (nat_lit 68))))
                                                            impl K0
                                                            (@HPow.hPow.{0, 0, 0} Real Int Real
                                                              (@instHPow.{0, 0} Real Int
                                                                (@ZPow.toPow.{0} Real
                                                                  (@DivInvMonoid.toZPow.{0} Real
                                                                    Real.instDivInvMonoid)))
                                                              K
                                                              (@Neg.neg.{0} Int Int.instNegInt
                                                                (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                                  (@instOfNat (nat_lit 2)))))
                                                            h Γ init t next))
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 7)
                                                          (instOfNatNat (nat_lit 7))))))))))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_11.2.1.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.update : ∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {B N : Nat} {K K0 h Γ init : Real}
  {impl : DecrAlmostLinearSSSP.Decremental.CutImplementation} {state : DecrAlmostLinearSSSP.Decremental.State b}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  (ctx :
    DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context b B N
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
        (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
      impl K0
      (@HPow.hPow.{0, 0, 0} Real Int Real
        (@instHPow.{0, 0} Real Int (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid))) K
        (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
      h Γ init s),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    @LE.le.{0} Nat instLENat b.input.n B →
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) N →
        @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.registerBound impl.program.code) N →
          @LE.le.{0} Real Real.instLE
              (@OfNat.ofNat.{0} Real (nat_lit 32)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
              K →
            @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K0 →
              @LE.le.{0} Real Real.instLE K0 K →
                DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K state →
                  @DecrAlmostLinearSSSP.Decremental.CutModel b (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                      (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b) state
                      (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                        (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                            (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                          impl K0
                          (@HPow.hPow.{0, 0, 0} Real Int Real
                            (@instHPow.{0, 0} Real Int
                              (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                            K
                            (@Neg.neg.{0} Int Int.instNegInt
                              (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                          h Γ init s ctx)) →
                    ∀ (e : Fin b.input.k),
                      @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
                          (@DecrAlmostLinearSSSP.Decremental.State.pending b state)
                          (@List.nil.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) →
                        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                            (@Fin.val b.input.k e) →
                          ∀ (offset : Nat),
                            DecrAlmostLinearSSSP.Decremental.CoreRepair.OperationDebt b state
                                (@List.length.{0}
                                  (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                    (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                  (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                    impl K0
                                    (@HPow.hPow.{0, 0, 0} Real Int Real
                                      (@instHPow.{0, 0} Real Int
                                        (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                      K
                                      (@Neg.neg.{0} Int Int.instNegInt
                                        (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                    h Γ init s ctx))
                                (DecrAlmostLinearSSSP.Decremental.reportVolume
                                  (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines b B N
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                    impl K0
                                    (@HPow.hPow.{0, 0, 0} Real Int Real
                                      (@instHPow.{0, 0} Real Int
                                        (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                      K
                                      (@Neg.neg.{0} Int Int.instNegInt
                                        (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                    h Γ init s ctx))
                                offset →
                              @Eq.{1} Nat
                                  (@DecrAlmostLinearSSSP.Decremental.toggleVolume b.input.n
                                    (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                    (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                          b.weightExponent)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                      impl K0
                                      (@HPow.hPow.{0, 0, 0} Real Int Real
                                        (@instHPow.{0, 0} Real Int
                                          (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                        K
                                        (@Neg.neg.{0} Int Int.instNegInt
                                          (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                      h Γ init s ctx))
                                  (@DecrAlmostLinearSSSP.Decremental.State.toggles b state) →
                                ∃ cost t after next,
                                  And
                                    (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                      (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.updateCode N impl.program) s cost
                                      t)
                                    (And (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K after t)
                                      (And (DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K after)
                                        (And
                                          (@DecrAlmostLinearSSSP.Decremental.CutModel b
                                            (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                            (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b) after
                                            (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                  b.input.size)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                    b.weightExponent)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                impl K0
                                                (@HPow.hPow.{0, 0, 0} Real Int Real
                                                  (@instHPow.{0, 0} Real Int
                                                    (@ZPow.toPow.{0} Real
                                                      (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                  K
                                                  (@Neg.neg.{0} Int Int.instNegInt
                                                    (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                                h Γ init t next)))
                                          (And
                                            (@Eq.{1} Bool (@DecrAlmostLinearSSSP.Decremental.State.stopped b after)
                                              Bool.true)
                                            (And (DecrAlmostLinearSSSP.Decremental.ReadoutCertificate b after)
                                              (And
                                                (@Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
                                                  (@DecrAlmostLinearSSSP.Decremental.State.pending b after)
                                                  (@List.nil.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)))
                                                (And
                                                  (@Eq.{1} (Finset.{0} (Fin b.input.k))
                                                    (@DecrAlmostLinearSSSP.Decremental.State.active b after)
                                                    (@Finset.erase.{0} (Fin b.input.k) (instDecidableEqFin b.input.k)
                                                      (@DecrAlmostLinearSSSP.Decremental.State.active b state) e))
                                                  (And
                                                    (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                                                      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.first b B
                                                        N
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                          b.input.size)
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                              (instOfNatNat (nat_lit 4)))
                                                            b.weightExponent)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                            (instOfNatNat (nat_lit 68))))
                                                        impl K0
                                                        (@HPow.hPow.{0, 0, 0} Real Int Real
                                                          (@instHPow.{0, 0} Real Int
                                                            (@ZPow.toPow.{0} Real
                                                              (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                          K
                                                          (@Neg.neg.{0} Int Int.instNegInt
                                                            (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                              (@instOfNat (nat_lit 2)))))
                                                        h Γ init t next)
                                                      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.first b B
                                                        N
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                          b.input.size)
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                              (instOfNatNat (nat_lit 4)))
                                                            b.weightExponent)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                            (instOfNatNat (nat_lit 68))))
                                                        impl K0
                                                        (@HPow.hPow.{0, 0, 0} Real Int Real
                                                          (@instHPow.{0, 0} Real Int
                                                            (@ZPow.toPow.{0} Real
                                                              (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                          K
                                                          (@Neg.neg.{0} Int Int.instNegInt
                                                            (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                              (@instOfNat (nat_lit 2)))))
                                                        h Γ init s ctx))
                                                    (And
                                                      (DecrAlmostLinearSSSP.Decremental.CoreRepair.OperationDebt b after
                                                        (@List.length.{0}
                                                          (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                            (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                                          (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b
                                                            B N
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                (instOfNatNat (nat_lit 2)))
                                                              b.input.size)
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                (@instHMul.{0} Nat instMulNat)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                  (instOfNatNat (nat_lit 4)))
                                                                b.weightExponent)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                                (instOfNatNat (nat_lit 68))))
                                                            impl K0
                                                            (@HPow.hPow.{0, 0, 0} Real Int Real
                                                              (@instHPow.{0, 0} Real Int
                                                                (@ZPow.toPow.{0} Real
                                                                  (@DivInvMonoid.toZPow.{0} Real
                                                                    Real.instDivInvMonoid)))
                                                              K
                                                              (@Neg.neg.{0} Int Int.instNegInt
                                                                (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                                  (@instOfNat (nat_lit 2)))))
                                                            h Γ init t next))
                                                        (DecrAlmostLinearSSSP.Decremental.reportVolume
                                                          (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines
                                                            b B N
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                (instOfNatNat (nat_lit 2)))
                                                              b.input.size)
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                (@instHMul.{0} Nat instMulNat)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                  (instOfNatNat (nat_lit 4)))
                                                                b.weightExponent)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                                (instOfNatNat (nat_lit 68))))
                                                            impl K0
                                                            (@HPow.hPow.{0, 0, 0} Real Int Real
                                                              (@instHPow.{0, 0} Real Int
                                                                (@ZPow.toPow.{0} Real
                                                                  (@DivInvMonoid.toZPow.{0} Real
                                                                    Real.instDivInvMonoid)))
                                                              K
                                                              (@Neg.neg.{0} Int Int.instNegInt
                                                                (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                                  (@instOfNat (nat_lit 2)))))
                                                            h Γ init t next))
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          offset
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 6)
                                                            (instOfNatNat (nat_lit 6)))))
                                                      (And
                                                        (@Eq.{1} Nat
                                                          (@DecrAlmostLinearSSSP.Decremental.toggleVolume b.input.n
                                                            (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                                            (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops
                                                              b B N
                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                (@instHMul.{0} Nat instMulNat)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                  (instOfNatNat (nat_lit 2)))
                                                                b.input.size)
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat)
                                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                  (@instHMul.{0} Nat instMulNat)
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                    (instOfNatNat (nat_lit 4)))
                                                                  b.weightExponent)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                                  (instOfNatNat (nat_lit 68))))
                                                              impl K0
                                                              (@HPow.hPow.{0, 0, 0} Real Int Real
                                                                (@instHPow.{0, 0} Real Int
                                                                  (@ZPow.toPow.{0} Real
                                                                    (@DivInvMonoid.toZPow.{0} Real
                                                                      Real.instDivInvMonoid)))
                                                                K
                                                                (@Neg.neg.{0} Int Int.instNegInt
                                                                  (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                                    (@instOfNat (nat_lit 2)))))
                                                              h Γ init t next))
                                                          (@DecrAlmostLinearSSSP.Decremental.State.toggles b after))
                                                        (@LE.le.{0} Nat instLENat
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat)
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat) cost
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 7)
                                                                (instOfNatNat (nat_lit 7))))
                                                            (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.credit b N
                                                              impl.program state
                                                              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current
                                                                b B N
                                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                  (@instHMul.{0} Nat instMulNat)
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                    (instOfNatNat (nat_lit 2)))
                                                                  b.input.size)
                                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                  (@instHAdd.{0} Nat instAddNat)
                                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                    (@instHMul.{0} Nat instMulNat)
                                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                      (instOfNatNat (nat_lit 4)))
                                                                    b.weightExponent)
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                                    (instOfNatNat (nat_lit 68))))
                                                                impl K0
                                                                (@HPow.hPow.{0, 0, 0} Real Int Real
                                                                  (@instHPow.{0, 0} Real Int
                                                                    (@ZPow.toPow.{0} Real
                                                                      (@DivInvMonoid.toZPow.{0} Real
                                                                        Real.instDivInvMonoid)))
                                                                  K
                                                                  (@Neg.neg.{0} Int Int.instNegInt
                                                                    (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                                      (@instOfNat (nat_lit 2)))))
                                                                h Γ init s ctx)
                                                              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops
                                                                b B N
                                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                  (@instHMul.{0} Nat instMulNat)
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                    (instOfNatNat (nat_lit 2)))
                                                                  b.input.size)
                                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                  (@instHAdd.{0} Nat instAddNat)
                                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                    (@instHMul.{0} Nat instMulNat)
                                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                      (instOfNatNat (nat_lit 4)))
                                                                    b.weightExponent)
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                                    (instOfNatNat (nat_lit 68))))
                                                                impl K0
                                                                (@HPow.hPow.{0, 0, 0} Real Int Real
                                                                  (@instHPow.{0, 0} Real Int
                                                                    (@ZPow.toPow.{0} Real
                                                                      (@DivInvMonoid.toZPow.{0} Real
                                                                        Real.instDivInvMonoid)))
                                                                  K
                                                                  (@Neg.neg.{0} Int Int.instNegInt
                                                                    (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                                      (@instOfNat (nat_lit 2)))))
                                                                h Γ init s ctx)
                                                              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines
                                                                b B N
                                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                  (@instHMul.{0} Nat instMulNat)
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                    (instOfNatNat (nat_lit 2)))
                                                                  b.input.size)
                                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                  (@instHAdd.{0} Nat instAddNat)
                                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                    (@instHMul.{0} Nat instMulNat)
                                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                      (instOfNatNat (nat_lit 4)))
                                                                    b.weightExponent)
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                                    (instOfNatNat (nat_lit 68))))
                                                                impl K0
                                                                (@HPow.hPow.{0, 0, 0} Real Int Real
                                                                  (@instHPow.{0, 0} Real Int
                                                                    (@ZPow.toPow.{0} Real
                                                                      (@DivInvMonoid.toZPow.{0} Real
                                                                        Real.instDivInvMonoid)))
                                                                  K
                                                                  (@Neg.neg.{0} Int Int.instNegInt
                                                                    (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                                      (@instOfNat (nat_lit 2)))))
                                                                h Γ init s ctx)))
                                                          (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.credit b N
                                                            impl.program after
                                                            (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current
                                                              b B N
                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                (@instHMul.{0} Nat instMulNat)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                  (instOfNatNat (nat_lit 2)))
                                                                b.input.size)
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat)
                                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                  (@instHMul.{0} Nat instMulNat)
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                    (instOfNatNat (nat_lit 4)))
                                                                  b.weightExponent)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                                  (instOfNatNat (nat_lit 68))))
                                                              impl K0
                                                              (@HPow.hPow.{0, 0, 0} Real Int Real
                                                                (@instHPow.{0, 0} Real Int
                                                                  (@ZPow.toPow.{0} Real
                                                                    (@DivInvMonoid.toZPow.{0} Real
                                                                      Real.instDivInvMonoid)))
                                                                K
                                                                (@Neg.neg.{0} Int Int.instNegInt
                                                                  (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                                    (@instOfNat (nat_lit 2)))))
                                                              h Γ init t next)
                                                            (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops
                                                              b B N
                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                (@instHMul.{0} Nat instMulNat)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                  (instOfNatNat (nat_lit 2)))
                                                                b.input.size)
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat)
                                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                  (@instHMul.{0} Nat instMulNat)
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                    (instOfNatNat (nat_lit 4)))
                                                                  b.weightExponent)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                                  (instOfNatNat (nat_lit 68))))
                                                              impl K0
                                                              (@HPow.hPow.{0, 0, 0} Real Int Real
                                                                (@instHPow.{0, 0} Real Int
                                                                  (@ZPow.toPow.{0} Real
                                                                    (@DivInvMonoid.toZPow.{0} Real
                                                                      Real.instDivInvMonoid)))
                                                                K
                                                                (@Neg.neg.{0} Int Int.instNegInt
                                                                  (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                                    (@instOfNat (nat_lit 2)))))
                                                              h Γ init t next)
                                                            (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines
                                                              b B N
                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                (@instHMul.{0} Nat instMulNat)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                  (instOfNatNat (nat_lit 2)))
                                                                b.input.size)
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat)
                                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                  (@instHMul.{0} Nat instMulNat)
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                    (instOfNatNat (nat_lit 4)))
                                                                  b.weightExponent)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                                  (instOfNatNat (nat_lit 68))))
                                                              impl K0
                                                              (@HPow.hPow.{0, 0, 0} Real Int Real
                                                                (@instHPow.{0, 0} Real Int
                                                                  (@ZPow.toPow.{0} Real
                                                                    (@DivInvMonoid.toZPow.{0} Real
                                                                      Real.instDivInvMonoid)))
                                                                K
                                                                (@Neg.neg.{0} Int Int.instNegInt
                                                                  (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                                    (@instOfNat (nat_lit 2)))))
                                                              h Γ init t next))))))))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_11.2.2.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.ReadoutCertificate.correct : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (s : DecrAlmostLinearSSSP.Decremental.State b),
  DecrAlmostLinearSSSP.Decremental.ReadoutCertificate b s →
    And
      (@Eq.{1} ENNReal (@DecrAlmostLinearSSSP.Decremental.State.output b s b.input.source)
        (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero)))
      (∀ (v : Fin b.input.n),
        And
          (@LE.le.{0} ENNReal ENNReal.instLE
            (@DecrAlmostLinearSSSP.Decremental.distance b.input.n b.input.k b.input.graph
              (@DecrAlmostLinearSSSP.Decremental.State.active b s)
              (fun e =>
                @Nat.cast.{0} ENNReal
                  (@AddMonoidWithOne.toNatCast.{0} ENNReal
                    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                  (b.input.weight e))
              b.input.source v)
            (@DecrAlmostLinearSSSP.Decremental.State.output b s v))
          (And
            (@LE.le.{0} ENNReal ENNReal.instLE (@DecrAlmostLinearSSSP.Decremental.State.output b s v)
              (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                (@instHMul.{0} ENNReal
                  (@Distrib.toMul.{0} ENNReal
                    (@instDistribOfSemiring.{0} ENNReal
                      (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                (ENNReal.ofReal
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) b.input.accuracy))
                (@DecrAlmostLinearSSSP.Decremental.distance b.input.n b.input.k b.input.graph
                  (@DecrAlmostLinearSSSP.Decremental.State.active b s)
                  (fun e =>
                    @Nat.cast.{0} ENNReal
                      (@AddMonoidWithOne.toNatCast.{0} ENNReal
                        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                      (b.input.weight e))
                  b.input.source v)))
            (Iff
              (@Eq.{1} ENNReal (@DecrAlmostLinearSSSP.Decremental.State.output b s v)
                (@Top.top.{0} ENNReal ENNReal.instTop))
              (Not
                (@DecrAlmostLinearSSSP.Decremental.Reachable b.input.n b.input.k b.input.graph
                  (@DecrAlmostLinearSSSP.Decremental.State.active b s) b.input.source v))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_11.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreHost.Image.certified : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    DecrAlmostLinearSSSP.Decremental.ReadoutCertificate b state →
      And
        (@Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.stored s.machine (@Fin.val b.input.n b.input.source))
          (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero)))
        (And
          (∀ (v : Fin b.input.n),
            And
              (@LE.le.{0} Nat instLENat (s.natMem (@Fin.val b.input.n v))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@Eq.{1} Nat (s.natMem (@Fin.val b.input.n v))
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                  (s.realMem (@Fin.val b.input.n v))))
          (∀ (v : Fin b.input.n),
            And
              (@LE.le.{0} ENNReal ENNReal.instLE
                (@DecrAlmostLinearSSSP.Decremental.distance b.input.n b.input.k b.input.graph
                  (@DecrAlmostLinearSSSP.Decremental.State.active b state)
                  (fun e =>
                    @Nat.cast.{0} ENNReal
                      (@AddMonoidWithOne.toNatCast.{0} ENNReal
                        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                      (b.input.weight e))
                  b.input.source v)
                (DecrAlmostLinearSSSP.Decremental.stored s.machine (@Fin.val b.input.n v)))
              (And
                (@LE.le.{0} ENNReal ENNReal.instLE
                  (DecrAlmostLinearSSSP.Decremental.stored s.machine (@Fin.val b.input.n v))
                  (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                    (@instHMul.{0} ENNReal
                      (@Distrib.toMul.{0} ENNReal
                        (@instDistribOfSemiring.{0} ENNReal
                          (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                    (ENNReal.ofReal
                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) b.input.accuracy))
                    (@DecrAlmostLinearSSSP.Decremental.distance b.input.n b.input.k b.input.graph
                      (@DecrAlmostLinearSSSP.Decremental.State.active b state)
                      (fun e =>
                        @Nat.cast.{0} ENNReal
                          (@AddMonoidWithOne.toNatCast.{0} ENNReal
                            (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                          (b.input.weight e))
                      b.input.source v)))
                (Iff
                  (@Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.stored s.machine (@Fin.val b.input.n v))
                    (@Top.top.{0} ENNReal ENNReal.instTop))
                  (Not
                    (@DecrAlmostLinearSSSP.Decremental.Reachable b.input.n b.input.k b.input.graph
                      (@DecrAlmostLinearSSSP.Decremental.State.active b state) b.input.source v)))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_11.2.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.cutLogHeight_log_upper : ∀ (m : Nat),
  @LE.le.{0} Real Real.instLE
    (Real.log
      (@Nat.cast.{0} Real Real.instNatCast
        (@Max.max.{0} Nat Nat.instMax (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))
    (@Nat.cast.{0} Real Real.instNatCast (DecrAlmostLinearSSSP.Decremental.cutLogHeight m)) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_12.1.1.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.cutRoot_ge_two : ∀ (m : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    (DecrAlmostLinearSSSP.Decremental.cutRoot m) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_12.1.1.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.cutRoot_power_lower : ∀ (m : Nat),
  @LT.lt.{0} Nat instLTNat (DecrAlmostLinearSSSP.Decremental.cutLogHeight m)
    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
      (DecrAlmostLinearSSSP.Decremental.cutRoot m) (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_12.1.1.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.cutRoot_log_power_bound : ∀ (m : Nat),
  @LE.le.{0} Real Real.instLE
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HPow.hPow.{0, 0, 0} Real Nat Real
        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
        (@Nat.cast.{0} Real Real.instNatCast (DecrAlmostLinearSSSP.Decremental.cutRoot m))
        (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))
      (Real.log
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real (nat_lit 8192)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 8192) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 8191) (instOfNatNat (nat_lit 8191)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 8190) (instOfNatNat (nat_lit 8190)))))))
      (Real.log
        (@Nat.cast.{0} Real Real.instNatCast
          (@Max.max.{0} Nat Nat.instMax (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_12.1.1.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreQuality.eval_code : ∀ (N : Nat) (i : DecrAlmostLinearSSSP.Decremental.Input),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) i.size →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
      DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i s →
        ∃ t cost,
          And
            (DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.CoreQuality.code N) s
              cost t)
            (And (DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i t)
              (And
                (@Eq.{1} Real (t.realReg (@OfNat.ofNat.{0} Nat (nat_lit 442) (instOfNatNat (nat_lit 442))))
                  (DecrAlmostLinearSSSP.Decremental.computableCutQuality N
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) i.size)))
                (And
                  (@LE.le.{0} Nat instLENat cost
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 80000) (instOfNatNat (nat_lit 80000)))
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) N
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        i.size)
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                  (And (@Eq.{1} (Nat → Real) t.realMem s.realMem) (@Eq.{1} (Nat → Nat) t.natMem s.natMem))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_12.2.1.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreCeiling.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 526) (instOfNatNat (nat_lit 526))) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
      (DecrAlmostLinearSSSP.Decremental.CoreCeiling.start.seq DecrAlmostLinearSSSP.Decremental.CoreCeiling.loop) k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_12.2.1.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreCeiling.real_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 526) (instOfNatNat (nat_lit 526))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
      (DecrAlmostLinearSSSP.Decremental.CoreCeiling.start.seq DecrAlmostLinearSSSP.Decremental.CoreCeiling.loop) k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_12.2.1.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreCeiling.no_memory : DecrAlmostLinearSSSP.Decremental.Structured.NoMemory
  (DecrAlmostLinearSSSP.Decremental.CoreCeiling.start.seq DecrAlmostLinearSSSP.Decremental.CoreCeiling.loop) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_12.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreParameters.eval_code : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured b.input s →
    @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 442) (instOfNatNat (nat_lit 442)))) K →
      ∃ t cost,
        And
          (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreParameters.code s cost
            t)
          (And (DecrAlmostLinearSSSP.Decremental.InputCapture.Captured b.input t)
            (And (DecrAlmostLinearSSSP.Decremental.CoreParameters.Values b K t)
              (And
                (@LE.le.{0} Nat instLENat cost
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                      (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
                        (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing)
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@OfNat.ofNat.{0} Real (nat_lit 32)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
                            (DecrAlmostLinearSSSP.Decremental.logarithm2
                              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                (@Nat.cast.{0} Real Real.instNatCast b.input.size)
                                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
                          b.input.accuracy)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 45) (instOfNatNat (nat_lit 45)))))
                (And (@Eq.{1} (Nat → Real) t.realMem s.realMem) (@Eq.{1} (Nat → Nat) t.natMem s.natMem))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_12.2.1.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreInitialize.boot_records_eval : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (N : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program),
  have B :=
    @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b.input.n
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) b.input.k))
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)));
  have K :=
    DecrAlmostLinearSSSP.Decremental.computableCutQuality N
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size);
  ∃ cost t,
    And
      (DecrAlmostLinearSSSP.Decremental.Structured.Eval
        (DecrAlmostLinearSSSP.Decremental.CoreInitialize.bootRecordsCode N)
        (DecrAlmostLinearSSSP.Decremental.Structured.data (DecrAlmostLinearSSSP.Decremental.initialMachine p b.input))
        cost t)
      (And
        (@LE.le.{0} Nat instLENat cost
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 80000) (instOfNatNat (nat_lit 80000)))
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) N
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 180) (instOfNatNat (nat_lit 180))))
                b.input.size)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
                  (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing)
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@OfNat.ofNat.{0} Real (nat_lit 32)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
                      (DecrAlmostLinearSSSP.Decremental.logarithm2
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@Nat.cast.{0} Real Real.instNatCast b.input.size)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
                    b.input.accuracy))))
            (@OfNat.ofNat.{0} Nat (nat_lit 86) (instOfNatNat (nat_lit 86)))))
        (And
          (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K (DecrAlmostLinearSSSP.Decremental.initializeState b) t)
          (And
            (∀ (j : Nat),
              And
                (@Eq.{1} Nat
                  (t.natMem
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) j))
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                (@Eq.{1} Real
                  (t.realMem
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) j))
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
            (And
              (@Eq.{1} Nat
                (t.natMem
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B)
                    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (∀ (j : Nat),
                And
                  (@Eq.{1} Nat (t.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg j))
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (@Eq.{1} Real (t.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg j))
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_12.2.2.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreGuestEdge.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreGuestEdge.code s
    (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))
    (DecrAlmostLinearSSSP.Decremental.CoreGuestEdge.result s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_12.2.2.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreGuestEdge.nat_memory : ∀ (B e : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))) B →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) e) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 690) (instOfNatNat (nat_lit 690))))
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
          @Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.CoreGuestEdge.result s).natMem
            (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
              (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
                (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natMem
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) e))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626))))))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) e))
                  (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 628) (instOfNatNat (nat_lit 628))))))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) e))
                (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_12.2.2.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreGuestEdge.real_memory : ∀ (B e : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))) B →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) e) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
        @Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.CoreGuestEdge.result s).realMem
          (@Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realMem
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) e))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 600) (instOfNatNat (nat_lit 600))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_12.2.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreGuestEdge.counter : ∀ (e : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) e) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
      @Eq.{1} Nat
        ((DecrAlmostLinearSSSP.Decremental.CoreGuestEdge.result s).natReg
          (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) e
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_12.2.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreGuestEdge.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))) →
    Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 680) (instOfNatNat (nat_lit 680))))
        (Or (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 690) (instOfNatNat (nat_lit 690))))
          (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 692) (instOfNatNat (nat_lit 692))) k)) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreGuestEdge.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_12.2.2.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreGuestEdge.real_frame : ∀ (k : Nat), DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreGuestEdge.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_12.2.2.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreGuestEdge.fields : ∀ (B e : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))) B →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) e) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 690) (instOfNatNat (nat_lit 690))))
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
          And
            (@Eq.{1} Nat
              ((DecrAlmostLinearSSSP.Decremental.CoreGuestEdge.result s).natMem
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) e))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626))))))
            (And
              (@Eq.{1} Nat
                ((DecrAlmostLinearSSSP.Decremental.CoreGuestEdge.result s).natMem
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) e))
                    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 628) (instOfNatNat (nat_lit 628))))))
              (And
                (@Eq.{1} Nat
                  ((DecrAlmostLinearSSSP.Decremental.CoreGuestEdge.result s).natMem
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) e))
                      (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@Eq.{1} Real
                  ((DecrAlmostLinearSSSP.Decremental.CoreGuestEdge.result s).realMem
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) e))
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 600) (instOfNatNat (nat_lit 600))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_12.2.2.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreGuestEdge.nat_memory_frame : ∀ (B e : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))) B →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) e) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 690) (instOfNatNat (nat_lit 690))))
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
          ∀ (j : Nat),
            @Ne.{1} Nat j
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) e))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
              @Ne.{1} Nat j
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) e))
                    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))) →
                @Ne.{1} Nat j
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) e))
                      (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))) →
                  @Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.CoreGuestEdge.result s).natMem j) (s.natMem j) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_12.2.2.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreGuestEdge.real_memory_frame : ∀ (B e : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))) B →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) e) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
        ∀ (j : Nat),
          @Ne.{1} Nat j
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) e))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
            @Eq.{1} Real ((DecrAlmostLinearSSSP.Decremental.CoreGuestEdge.result s).realMem j) (s.realMem j) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_12.2.2.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreGuestEdge.host_geometry : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B e : Nat) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreGeometry.Image b B state s →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))) B →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) e) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 690) (instOfNatNat (nat_lit 690))))
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
            DecrAlmostLinearSSSP.Decremental.CoreGeometry.Image b B state
              (DecrAlmostLinearSSSP.Decremental.CoreGuestEdge.result s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_12.2.2.2.1.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreGuestGamma.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreGuestGamma.code s
    (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))
    (DecrAlmostLinearSSSP.Decremental.CoreGuestGamma.result s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_12.2.2.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreGuestGamma.real_memory : ∀ (B G l v : Nat) (gamma : Real) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))) B →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 554) (instOfNatNat (nat_lit 554)))) G →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 542) (instOfNatNat (nat_lit 542))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) l) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626)))) v →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
            @Eq.{1} Real
                (s.realMem
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) G
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) v)))
                gamma →
              @Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.CoreGuestGamma.result s).realMem
                (@Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realMem
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) l v)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  gamma) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_12.2.2.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreGuestGamma.nat_memory : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.CoreGuestGamma.result s).natMem s.natMem := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_12.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreGuestGamma.vertex : ∀ (v : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626)))) v →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @Eq.{1} Nat
        ((DecrAlmostLinearSSSP.Decremental.CoreGuestGamma.result s).natReg
          (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) v
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_12.2.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreGuestGamma.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626))) →
    Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 680) (instOfNatNat (nat_lit 680))))
        (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 684) (instOfNatNat (nat_lit 684))) k) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreGuestGamma.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_12.2.2.2.2.2.2.2
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
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s111
section s112
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
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
end DecrAlmostLinearSSSP.Decremental.Normalize
end s114
section s115
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize
end DecrAlmostLinearSSSP.Decremental.Normalize
end s115
section s116
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s116
section s117
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
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
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s119
section s120
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s120
section s121
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s121
section s122
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s122
section s123
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.SourceMemory
open Structured
end DecrAlmostLinearSSSP.Decremental.SourceMemory
end s123
section s124
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s124
section s125
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s125
section s126
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s126
section s127
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s127
section s128
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s128
section s129
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s129
section s130
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end s130
section s131
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured Instrumented
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s131
section s132
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured Instrumented
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s132
section s133
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured Instrumented
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s133
section s134
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured Instrumented
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
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s139
section s140
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s140
section s141
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
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
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s144
section s145
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s145
section s146
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
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
lemma real_frame (k : ℕ) (hk : k ≠ 694) : RealFrame code k := by simp [code,atoms,Structured.sequence,RealFrame,writesReal,Ne.symm hk]
end DecrAlmostLinearSSSP.Decremental.CoreGuestGamma
end s404
section s405
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
open Structured
lemma edge_nat_frame (k : ℕ) (hk : k < 560 ∨ k = 690 ∨ 692 < k) : NatFrame edgeBody k := by
  refine ⟨?_,CoreGeometry.nat_frame k (by omega) (by omega) (by omega) (by omega),CoreGuestEdge.nat_frame k (by omega) (by omega)⟩
  simp [CorePending.prefixCode,CorePending.prefixAtoms,Structured.sequence,NatFrame,writesNat]
  omega
lemma edge_real_frame (k : ℕ) (h600 : k ≠ 600) (h602 : k ≠ 602) (h604 : k ≠ 604) (h606 : k ≠ 606) : RealFrame edgeBody k := by
  refine ⟨?_,CoreGeometry.real_frame k h600 h602 h604 h606,CoreGuestEdge.real_frame k⟩
  simp [CorePending.prefixCode,CorePending.prefixAtoms,Structured.sequence,RealFrame,writesReal]
lemma nat_frame (k : ℕ) (hk : k < 560 ∨ 692 < k) : NatFrame code k := by
  refine ⟨?_,edge_nat_frame k (by omega),?_,CoreGuestGamma.nat_frame k (by omega) (by omega)⟩
  · simp [edgeStart,Structured.sequence,NatFrame,natural,writesNat]
    omega
  · simp [NatFrame,natural,writesNat]
    omega
lemma real_frame (k : ℕ) (h600 : k ≠ 600) (h602 : k ≠ 602) (h604 : k ≠ 604) (h606 : k ≠ 606) (h694 : k ≠ 694) : RealFrame code k := by
  exact ⟨by simp [edgeStart,Structured.sequence,RealFrame,natural,writesReal],
    edge_real_frame k h600 h602 h604 h606,by simp [RealFrame,natural,writesReal],CoreGuestGamma.real_frame k h694⟩
lemma even_registers : evenRegisters code = true := by decide
end DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
end s405
section s406
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
open Structured
lemma edge_body_eval (b : Core) (B : ℕ) (state : State b) (d : Fin (logicalCount b)) (s : Data)
    (h : CoreGeometry.Image b B state s) (hB : s.natReg 74 = B) (hbase : s.natReg 552 = B+1)
    (he : s.natReg 560 = 2*d.val) (h2 : s.natReg 14 = 2) (h4 : s.natReg 690 = 4) :
    ∃ t, Eval edgeBody s 33 t ∧ CoreGeometry.Image b B state t ∧ t.natReg 560 = 2*(d.val+1) ∧
      t.natMem (B+12*d.val+2) = 2*(tail b ((logicalIndexEquiv b).symm d)).val ∧
      t.natMem (B+12*d.val+6) = 2*(head b ((logicalIndexEquiv b).symm d)).val ∧
      t.natMem (B+12*d.val+10) = 2 ∧
      t.realMem (B+4*d.val+2) = state.cache ((logicalIndexEquiv b).symm d) ∧
      (∀ j, j ≠ B+12*d.val+2 → j ≠ B+12*d.val+6 → j ≠ B+12*d.val+10 → t.natMem j = s.natMem j) ∧
      (∀ j, j ≠ B+4*d.val+2 → t.realMem j = s.realMem j) := by
  let p := CorePending.prefixData s
  have hp := CorePending.prefix_eval s
  have hpm := CorePending.prefix_memory s
  obtain ⟨hptr,hflag,hnext,hpreg⟩ := CorePending.prefix_fields s
  have hpn (k : ℕ) (hk : k ≠ 562 ∧ k ≠ 564 ∧ k ≠ 566 ∧ k ≠ 568 ∧ k ≠ 570 ∧ k ≠ 572) : p.natReg k = s.natReg k :=
    hpreg k hk.1 hk.2.1 hk.2.2.1 hk.2.2.2.1 hk.2.2.2.2.1 hk.2.2.2.2.2
  have hpi : CoreGeometry.Image b B state p := h.frame b B state (fun _ _ _ => congrFun hpm.2 _) (fun _ _ _ => congrFun hpm.1 _)
  have hpaddr : p.natReg 568 = CoreMemory.field b B ((logicalIndexEquiv b).symm d) 0 := by
    rw [hptr,hbase,he]
    simp only [CoreMemory.field,Equiv.apply_symm_apply,Nat.mul_zero,Nat.add_zero]
    omega
  let u := CoreGeometry.result p
  have hu := CoreGeometry.eval_code p
  have hum := hu.no_memory CoreGeometry.no_memory
  have hul := CoreGeometry.loaded_image b B state ((logicalIndexEquiv b).symm d) p hpi hpaddr ((hpn 14 (by omega)).trans h2)
  have hui : CoreGeometry.Image b B state u := hpi.frame b B state (fun _ _ _ => congrFun hum.1 _) (fun _ _ _ => congrFun hum.2 _)
  have hun (k : ℕ) (hk : k < 574 ∨ 580 < k) (h626 : k ≠ 626) (h628 : k ≠ 628) (h648 : k ≠ 648) : u.natReg k = p.natReg k := hu.nat_frame (CoreGeometry.nat_frame k hk h626 h628 h648)
  have huB : u.natReg 74 = B := (hun 74 (by omega) (by omega) (by omega) (by omega)).trans ((hpn 74 (by omega)).trans hB)
  have hue : u.natReg 560 = 2*d.val := (hun 560 (by omega) (by omega) (by omega) (by omega)).trans ((hpn 560 (by omega)).trans he)
  have hu2 : u.natReg 14 = 2 := (hun 14 (by omega) (by omega) (by omega) (by omega)).trans ((hpn 14 (by omega)).trans h2)
  have hu4 : u.natReg 690 = 4 := (hun 690 (by omega) (by omega) (by omega) (by omega)).trans ((hpn 690 (by omega)).trans h4)
  let t := CoreGuestEdge.result u
  have ht := CoreGuestEdge.eval_code u
  obtain ⟨h0,h1,h2',hr⟩ := CoreGuestEdge.fields B d.val u huB hue hu2 hu4
  refine ⟨t,Eval.seq hp (Eval.seq hu ht),CoreGuestEdge.host_geometry b B d.val state u hui huB hue hu2 hu4,
    CoreGuestEdge.counter d.val u hue hu2,?_,?_,h2',?_,?_,?_⟩
  · exact h0.trans (congrArg (fun x => 2*x) hul.tail)
  · exact h1.trans (congrArg (fun x => 2*x) hul.head)
  · exact hr.trans hul.oldCache
  · intro j h0 h1 h2'
    exact (CoreGuestEdge.nat_memory_frame B d.val u huB hue hu2 hu4 j h0 h1 h2').trans ((congrFun hum.2 j).trans (congrFun hpm.1 j))
  · intro j hj
    exact (CoreGuestEdge.real_memory_frame B d.val u huB hue hu2 j hj).trans ((congrFun hum.1 j).trans (congrFun hpm.2 j))
end DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
end s406
section s407
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
open Structured
lemma EdgeInvariant.step (b : Core) (B : ℕ) (state : State b) (upto : ℕ) (s : Data)
    (h : EdgeInvariant b B state upto s) (hlt : upto < logicalCount b) :
    ∃ t, Eval edgeBody s 33 t ∧ EdgeInvariant b B state (upto+1) t ∧
      (∀ j, (∀ i, i < logicalCount b → ∀ offset < 3, j ≠ B+12*i+4*offset+2) → t.natMem j = s.natMem j) ∧
      (∀ j, (∀ i, i < logicalCount b → j ≠ B+4*i+2) → t.realMem j = s.realMem j) := by
  let d : Fin (logicalCount b) := ⟨upto,hlt⟩
  have hdval : d.val = upto := rfl
  obtain ⟨t,he,hgeom,hcounter,h0,h1,h2,hcap,hN,hR⟩ := edge_body_eval b B state d s h.geometry h.base h.layout.recordBase h.counter h.captured.two h.four
  have hn (k : ℕ) (hk : k < 560 ∨ k = 690 ∨ 692 < k) : t.natReg k = s.natReg k := he.nat_frame (edge_nat_frame k hk)
  have hr (k : ℕ) (hk : k ≠ 600 ∧ k ≠ 602 ∧ k ≠ 604 ∧ k ≠ 606) : t.realReg k = s.realReg k := he.real_frame (edge_real_frame k hk.1 hk.2.1 hk.2.2.1 hk.2.2.2)
  have hcells : EdgePrefix b B state (upto+1) t := by
    constructor
    · intro q hq
      by_cases hqd : q.val = upto
      · have hh : q = d := Fin.ext hqd
        simpa only [hh] using h0
      · have hqold : q.val < upto := by omega
        rw [hN _ (by omega) (by omega) (by omega)]
        exact h.cells.tails q hqold
    · intro q hq
      by_cases hqd : q.val = upto
      · have hh : q = d := Fin.ext hqd
        simpa only [hh] using h1
      · have hqold : q.val < upto := by omega
        rw [hN _ (by omega) (by omega) (by omega)]
        exact h.cells.heads q hqold
    · intro q hq
      by_cases hqd : q.val = upto
      · have hh : q = d := Fin.ext hqd
        simpa only [hh] using h2
      · have hqold : q.val < upto := by omega
        rw [hN _ (by omega) (by omega) (by omega)]
        exact h.cells.active q hqold
    · intro q hq
      by_cases hqd : q.val = upto
      · have hh : q = d := Fin.ext hqd
        simpa only [hh] using hcap
      · have hqold : q.val < upto := by omega
        rw [hR _ (by omega)]
        exact h.cells.capacities q hqold
    · intro j hj
      rw [hN _ (by omega) (by omega) (by omega)]
      exact h.cells.natZero j (by omega)
    · intro j hj
      rw [hR _ (by omega)]
      exact h.cells.realZero j (by omega)
  have hgrad : CoreGradient.Image (CoreMemory.gradientBase b B) state.cachedGradient t := h.gradient.frame _ _
    (by intro v;apply hR;dsimp [CoreMemory.gradientBase];omega) (hn 550 (by omega))
  have hcapt : InputCapture.Captured b.input t := h.captured.named_frame b.input
    (fun k hk => hn k (by simp at hk;omega)) (fun k hk => hr k (by simp at hk;omega))
  have hlay : CoreControl.Layout b B t := h.layout.frame b B (fun k hk => hn k (by simp at hk;omega))
  refine ⟨t,he,⟨by omega,hgeom,hgrad,hcapt,hlay,(hn 74 (by omega)).trans h.base,hcounter,(hn 690 (by omega)).trans h.four,hcells⟩,?_,?_⟩
  · intro j hj
    exact hN j (by simpa using hj upto hlt 0 (by omega))
      (by simpa using hj upto hlt 1 (by omega)) (by simpa using hj upto hlt 2 (by omega))
  · intro j hj
    exact hR j (hj upto hlt)
end DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
end s407
section s408
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
open Structured
lemma edge_loop_eval (b : Core) (B : ℕ) (state : State b) (upto : ℕ) (s : Data)
    (h : EdgeInvariant b B state upto s) :
    ∃ t, Eval edgeLoop s (35*(logicalCount b-upto)+2) t ∧ EdgeInvariant b B state (logicalCount b) t ∧
      (∀ j, (∀ i, i < logicalCount b → ∀ offset < 3, j ≠ B+12*i+4*offset+2) → t.natMem j = s.natMem j) ∧
      (∀ j, (∀ i, i < logicalCount b → j ≠ B+4*i+2) → t.realMem j = s.realMem j) := by
  suffices ∀ fuel upto s, upto+fuel = logicalCount b → EdgeInvariant b B state upto s →
      ∃ t, Eval edgeLoop s (35*fuel+2) t ∧ EdgeInvariant b B state (logicalCount b) t ∧
        (∀ j, (∀ i, i < logicalCount b → ∀ offset < 3, j ≠ B+12*i+4*offset+2) → t.natMem j = s.natMem j) ∧
        (∀ j, (∀ i, i < logicalCount b → j ≠ B+4*i+2) → t.realMem j = s.realMem j) by
    exact this (logicalCount b-upto) upto s (by have hh := h.bound;omega) h
  intro fuel
  induction fuel with
  | zero =>
    intro upto s heq hs
    have hu : upto = logicalCount b := by omega
    have ht : ¬ (Test.natLess 560 542).holds s := by simp only [Test.holds,hs.counter,hs.layout.edgeLimit,hu,lt_self_iff_false,not_false_eq_true]
    exact ⟨s,Eval.loopNo s ht,by simpa only [hu] using hs,fun _ _ => rfl,fun _ _ => rfl⟩
  | succ fuel ih =>
    intro upto s heq hs
    have hlt : upto < logicalCount b := by omega
    obtain ⟨u,hu,hum,hun,hur⟩ := hs.step b B state upto s hlt
    obtain ⟨t,ht,htm,htn,htr⟩ := ih (upto+1) u (by omega) hum
    have htest : (Test.natLess 560 542).holds s := by simp only [Test.holds,hs.counter,hs.layout.edgeLimit];omega
    refine ⟨t,?_,htm,fun j hj => (htn j hj).trans (hun j hj),fun j hj => (htr j hj).trans (hur j hj)⟩
    have he := Eval.loopYes htest hu ht
    convert he using 1 <;> first | rfl | omega
end DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
end s408
section s409
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
open Structured
lemma edge_start_eval (s : Data) : Eval edgeStart s 2 (edgesStarted s) := by
  exact Eval.seq (eval_natural s 560 0) (Eval.seq (eval_natural _ 690 4) (Eval.skip _))
lemma edge_start_nat_frame (k : ℕ) (h560 : k ≠ 560) (h690 : k ≠ 690) : NatFrame edgeStart k := by
  simp [edgeStart,Structured.sequence,NatFrame,natural,writesNat,Ne.symm h560,Ne.symm h690]
lemma EdgeInvariant.start (b : Core) (B : ℕ) (state : State b) (s : Data)
    (hg : CoreGeometry.Image b B state s) (hgrad : CoreGradient.Image (CoreMemory.gradientBase b B) state.cachedGradient s)
    (hc : InputCapture.Captured b.input s) (hl : CoreControl.Layout b B s) (hB : s.natReg 74 = B)
    (hzero : ∀ j, s.natMem (B+4*j+2) = 0 ∧ s.realMem (B+4*j+2) = 0) :
    EdgeInvariant b B state 0 (edgesStarted s) := by
  have he := edge_start_eval s
  have hn (k : ℕ) (hk : k ≠ 560 ∧ k ≠ 690) : (edgesStarted s).natReg k = s.natReg k := he.nat_frame (edge_start_nat_frame k hk.1 hk.2)
  refine ⟨by omega,hg.frame b B state (fun _ _ _ => rfl) (fun _ _ _ => rfl),
    hgrad.frame _ _ (fun _ => rfl) (hn 550 (by omega)),
    hc.named_frame b.input (fun k hk => hn k (by simp at hk;omega)) (fun _ _ => rfl),
    hl.frame b B (fun k hk => hn k (by simp at hk;omega)),(hn 74 (by omega)).trans hB,?_,?_,?_⟩
  · simp [edgesStarted]
  · simp [edgesStarted]
  · exact ⟨by intro d hd;omega,by intro d hd;omega,by intro d hd;omega,by intro d hd;omega,
      fun j _ => (hzero j).1,fun j _ => (hzero j).2⟩
lemma edge_pass_eval (b : Core) (B : ℕ) (state : State b) (s : Data)
    (hg : CoreGeometry.Image b B state s) (hgrad : CoreGradient.Image (CoreMemory.gradientBase b B) state.cachedGradient s)
    (hc : InputCapture.Captured b.input s) (hl : CoreControl.Layout b B s) (hB : s.natReg 74 = B)
    (hzero : ∀ j, s.natMem (B+4*j+2) = 0 ∧ s.realMem (B+4*j+2) = 0) :
    ∃ t, Eval (.seq edgeStart edgeLoop) s (35*logicalCount b+4) t ∧ EdgeInvariant b B state (logicalCount b) t ∧
      (∀ j, (∀ i, i < logicalCount b → ∀ offset < 3, j ≠ B+12*i+4*offset+2) → t.natMem j = s.natMem j) ∧
      (∀ j, (∀ i, i < logicalCount b → j ≠ B+4*i+2) → t.realMem j = s.realMem j) := by
  have hstart := EdgeInvariant.start b B state s hg hgrad hc hl hB hzero
  obtain ⟨t,ht,hti,htn,htr⟩ := edge_loop_eval b B state 0 (edgesStarted s) hstart
  refine ⟨t,?_,hti,htn,htr⟩
  have he := Eval.seq (edge_start_eval s) ht
  convert he using 1 <;> first | rfl | omega
end DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
end s409
section s410
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
open Structured
lemma GammaInvariant.step (b : Core) (B : ℕ) (state : State b) (upto : ℕ) (s : Data)
    (h : GammaInvariant b B state upto s) (hlt : upto < b.input.n) :
    ∃ t, Eval CoreGuestGamma.code s 9 t ∧ GammaInvariant b B state (upto+1) t ∧
      t.natMem = s.natMem ∧
      (∀ j, (∀ v, v < b.input.n → j ≠ B+4*(logicalCount b+v)+2) → t.realMem j = s.realMem j) := by
  let v : Fin b.input.n := ⟨upto,hlt⟩
  let t := CoreGuestGamma.result s
  have he := CoreGuestGamma.eval_code s
  have hG : s.realMem (CoreMemory.gradientBase b B+2*upto) = state.cachedGradient v := h.gradient.entries v
  have hr : t.realMem = Function.update s.realMem (B+4*(logicalCount b+upto)+2) (state.cachedGradient v) := CoreGuestGamma.real_memory B (CoreMemory.gradientBase b B) (logicalCount b) upto (state.cachedGradient v) s
    h.base h.layout.gradientBase h.layout.edgeLimit h.vertex h.captured.two hG
  have hn : t.natMem = s.natMem := CoreGuestGamma.nat_memory s
  have hrf (j : ℕ) (hj : j ≠ B+4*(logicalCount b+upto)+2) : t.realMem j = s.realMem j := by rw [hr,Function.update_of_ne hj]
  have hregN (k : ℕ) (hk : k ≠ 626 ∧ (k < 680 ∨ 684 < k)) : t.natReg k = s.natReg k := he.nat_frame (CoreGuestGamma.nat_frame k hk.1 hk.2)
  have hregR (k : ℕ) (hk : k ≠ 694) : t.realReg k = s.realReg k := he.real_frame (CoreGuestGamma.real_frame k hk)
  have hcells : GammaPrefix b B state (upto+1) t := by
    refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
    · simpa only [hn] using h.cells.tails
    · simpa only [hn] using h.cells.heads
    · simpa only [hn] using h.cells.active
    · intro d
      rw [hrf _ (by have hd := d.isLt;omega)]
      exact h.cells.capacities d
    · intro w hw
      by_cases hval : w.val = upto
      · have hwv : w = v := Fin.ext hval
        subst w
        rw [hr,Function.update_self]
      · rw [hrf _ (by omega)]
        exact h.cells.gamma w (by omega)
    · simpa only [hn] using h.cells.natZero
    · intro j hj
      rw [hrf _ (by omega)]
      exact h.cells.realZero j (by omega)
  have hgeom : CoreGeometry.Image b B state t := h.geometry.frame b B state
    (by intro e offset ho;apply hrf;dsimp [CoreMemory.field];omega) (fun _ _ _ => congrFun hn _)
  have hgrad : CoreGradient.Image (CoreMemory.gradientBase b B) state.cachedGradient t := h.gradient.frame _ _
    (by intro u;apply hrf;dsimp [CoreMemory.gradientBase];omega) (hregN 550 (by omega))
  have hcapt : InputCapture.Captured b.input t := h.captured.named_frame b.input
    (fun k hk => hregN k (by simp at hk;omega)) (fun k hk => hregR k (by simp at hk;omega))
  have hlay : CoreControl.Layout b B t := h.layout.frame b B (fun k hk => hregN k (by simp at hk;omega))
  refine ⟨t,he,⟨by omega,hgeom,hgrad,hcapt,hlay,(hregN 74 (by omega)).trans h.base,
    CoreGuestGamma.vertex upto s h.vertex h.captured.unit,hcells⟩,hn,?_⟩
  intro j hj
  exact hrf j (hj upto hlt)
end DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
end s410
section s411
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
open Structured
lemma gamma_loop_eval (b : Core) (B : ℕ) (state : State b) (upto : ℕ) (s : Data)
    (h : GammaInvariant b B state upto s) :
    ∃ t, Eval gammaLoop s (11*(b.input.n-upto)+2) t ∧ GammaInvariant b B state b.input.n t ∧
      t.natMem = s.natMem ∧ (∀ j, (∀ v, v < b.input.n → j ≠ B+4*(logicalCount b+v)+2) → t.realMem j = s.realMem j) := by
  suffices ∀ fuel upto s, upto+fuel = b.input.n → GammaInvariant b B state upto s →
      ∃ t, Eval gammaLoop s (11*fuel+2) t ∧ GammaInvariant b B state b.input.n t ∧
        t.natMem = s.natMem ∧ (∀ j, (∀ v, v < b.input.n → j ≠ B+4*(logicalCount b+v)+2) → t.realMem j = s.realMem j) by
    exact this (b.input.n-upto) upto s (by have hh := h.bound;omega) h
  intro fuel
  induction fuel with
  | zero =>
    intro upto s heq hs
    have hu : upto = b.input.n := by omega
    have ht : ¬ (Test.natLess 626 66).holds s := by simp only [Test.holds,hs.vertex,hs.captured.vertices,hu,lt_self_iff_false,not_false_eq_true]
    exact ⟨s,Eval.loopNo s ht,by simpa only [hu] using hs,rfl,fun _ _ => rfl⟩
  | succ fuel ih =>
    intro upto s heq hs
    have hlt : upto < b.input.n := by omega
    obtain ⟨u,hu,hum,hun,hur⟩ := hs.step b B state upto s hlt
    obtain ⟨t,ht,htm,htn,htr⟩ := ih (upto+1) u (by omega) hum
    have htest : (Test.natLess 626 66).holds s := by simpa only [Test.holds,hs.vertex,hs.captured.vertices] using hlt
    refine ⟨t,?_,htm,htn.trans hun,fun j hj => (htr j hj).trans (hur j hj)⟩
    have he := Eval.loopYes htest hu ht
    convert he using 1 <;> first | rfl | omega
lemma GammaInvariant.start (b : Core) (B : ℕ) (state : State b) (s : Data)
    (h : EdgeInvariant b B state (logicalCount b) s) :
    GammaInvariant b B state 0 {s with natReg := Function.update s.natReg 626 0} := by
  let t : Data := {s with natReg := Function.update s.natReg 626 0}
  have hn (k : ℕ) (hk : k ≠ 626) : t.natReg k = s.natReg k := by simp [t,Function.update_of_ne hk]
  refine ⟨by omega,h.geometry.frame b B state (fun _ _ _ => rfl) (fun _ _ _ => rfl),
    h.gradient.frame _ _ (fun _ => rfl) (hn 550 (by omega)),
    h.captured.named_frame b.input (fun k hk => hn k (by simp at hk;omega)) (fun _ _ => rfl),
    h.layout.frame b B (fun k hk => hn k (by simp at hk;omega)),(hn 74 (by omega)).trans h.base,?_,?_⟩
  · simp [t]
  · exact ⟨fun d => h.cells.tails d d.isLt,fun d => h.cells.heads d d.isLt,
      fun d => h.cells.active d d.isLt,fun d => h.cells.capacities d d.isLt,
      by intro v hv;omega,h.cells.natZero,by simpa only [Nat.add_zero] using h.cells.realZero⟩
lemma gamma_pass_eval (b : Core) (B : ℕ) (state : State b) (s : Data)
    (h : EdgeInvariant b B state (logicalCount b) s) :
    ∃ t, Eval (.seq (natural 626 0) gammaLoop) s (11*b.input.n+3) t ∧ GammaInvariant b B state b.input.n t ∧
      t.natMem = s.natMem ∧ (∀ j, (∀ v, v < b.input.n → j ≠ B+4*(logicalCount b+v)+2) → t.realMem j = s.realMem j) := by
  let u : Data := {s with natReg := Function.update s.natReg 626 0}
  have hu := eval_natural s 626 0
  have hum : GammaInvariant b B state 0 u := GammaInvariant.start b B state s h
  obtain ⟨t,ht,hti,htn,htr⟩ := gamma_loop_eval b B state 0 u hum
  refine ⟨t,?_,hti,htn,htr⟩
  have he := Eval.seq hu ht
  convert he using 1 <;> first | rfl | omega
end DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
end s411
section s412
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
open Structured
lemma GammaInvariant.input_nat (b : Core) (B : ℕ) (state : State b) (s : Data)
    (h : GammaInvariant b B state b.input.n s) (p : Program) (m : ℕ) (ξ cap : ℝ) :
    ∀ j, s.natMem (B+2*(2*j+1)) = 2*(cutInitial p (indexedPhysical b state (logicalIndexEquiv b)) m ξ cap).natMem j := by
  intro j
  by_cases hj : j/3 < logicalCount b
  · let d : Fin (logicalCount b) := ⟨j/3,hj⟩
    by_cases hm0 : j%3 = 0
    · have haddr : B+2*(2*j+1) = B+12*d.val+2 := by dsimp [d];omega
      rw [haddr]
      simpa [cutInitial,indexedPhysical,hj,hm0,d] using h.cells.tails d
    · by_cases hm1 : j%3 = 1
      · have haddr : B+2*(2*j+1) = B+12*d.val+6 := by dsimp [d];omega
        rw [haddr]
        simpa [cutInitial,indexedPhysical,hj,hm0,hm1,d] using h.cells.heads d
      · have hm2 : j%3 = 2 := by omega
        have haddr : B+2*(2*j+1) = B+12*d.val+10 := by dsimp [d];omega
        rw [haddr]
        simpa [cutInitial,indexedPhysical,hj,hm0,hm1,d] using h.cells.active d
  · have haddr : B+2*(2*j+1) = B+4*j+2 := by omega
    rw [haddr,h.cells.natZero j (by omega)]
    simp [cutInitial,hj]
lemma GammaInvariant.input_real (b : Core) (B : ℕ) (state : State b) (s : Data)
    (h : GammaInvariant b B state b.input.n s) (p : Program) (m : ℕ) (ξ cap : ℝ) :
    ∀ j, s.realMem (B+2*(2*j+1)) = (cutInitial p (indexedPhysical b state (logicalIndexEquiv b)) m ξ cap).realMem j := by
  intro j
  by_cases hj : j < logicalCount b
  · let d : Fin (logicalCount b) := ⟨j,hj⟩
    have haddr : B+2*(2*j+1) = B+4*d.val+2 := by dsimp [d];omega
    rw [haddr]
    simpa [cutInitial,indexedPhysical,hj,d] using h.cells.capacities d
  · by_cases hv : j-logicalCount b < b.input.n
    · let v : Fin b.input.n := ⟨j-logicalCount b,hv⟩
      have haddr : B+2*(2*j+1) = B+4*(logicalCount b+v.val)+2 := by dsimp [v];omega
      rw [haddr]
      simpa [cutInitial,indexedPhysical,hj,hv,v] using h.cells.gamma v v.isLt
    · have haddr : B+2*(2*j+1) = B+4*j+2 := by omega
      rw [haddr,h.cells.realZero j (by omega)]
      simp [cutInitial,hj,hv]
end DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
end s412
section s413
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGuestCopy
open Structured
lemma eval_code (b : Core) (B : ℕ) (state : State b) (s : Data)
    (hg : CoreGeometry.Image b B state s) (hgrad : CoreGradient.Image (CoreMemory.gradientBase b B) state.cachedGradient s)
    (hc : InputCapture.Captured b.input s) (hl : CoreControl.Layout b B s) (hB : s.natReg 74 = B)
    (hzero : ∀ j, s.natMem (B+4*j+2) = 0 ∧ s.realMem (B+4*j+2) = 0) :
    ∃ cost t, Eval code s cost t ∧ cost ≤ 85*b.input.size ∧ GammaInvariant b B state b.input.n t ∧
      (∀ j, (∀ i, i < logicalCount b → ∀ offset < 3, j ≠ B+12*i+4*offset+2) → t.natMem j = s.natMem j) ∧
      (∀ j, (∀ i, i < logicalCount b → j ≠ B+4*i+2) →
        (∀ v, v < b.input.n → j ≠ B+4*(logicalCount b+v)+2) → t.realMem j = s.realMem j) := by
  obtain ⟨u,hu,hum,hun,hur⟩ := edge_pass_eval b B state s hg hgrad hc hl hB hzero
  obtain ⟨t,ht,htm,htn,htr⟩ := gamma_pass_eval b B state u hum
  have hlCount := logicalCount_le b
  have hn : b.input.n ≤ b.input.size := b.valid.1
  have hm : 2 ≤ b.input.size := b.two.trans hn
  refine ⟨(35*logicalCount b+4)+(11*b.input.n+3),t,(Eval.seq hu ht).assoc,by omega,htm,?_,?_⟩
  · intro j hj
    exact (congrFun htn j).trans (hun j hj)
  · intro j he hv
    exact (htr j hv).trans (hur j he)
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
lemma fields_eval (s : Data) : Eval fieldCode s 11 (fieldResult s) := eval_sequence_atoms fieldAtoms s
lemma values (s : Data) (hz : s.natReg 56 = 0) (h2 : s.natReg 14 = 2) :
    (fieldResult s).natMem (s.natReg 50) = 2*s.natReg 66 ∧
    (fieldResult s).natMem (s.natReg 50+2) = 2*s.natReg 536 ∧
    (fieldResult s).natMem (s.natReg 50+4) = 2*s.natReg 540 ∧
    (fieldResult s).realMem (s.natReg 50) = s.realReg 510 ∧
    (fieldResult s).realMem (s.natReg 50+2) = s.realReg 508 := by
  simp (disch := omega) [fieldResult,fieldAtoms,Atom.effect,instructionEffect,data,Data.machine,hz,h2,two_mul]
lemma real_memory (s : Data) (hz : s.natReg 56 = 0) (h2 : s.natReg 14 = 2) :
    (fieldResult s).realMem = Function.update (Function.update s.realMem (s.natReg 50) (s.realReg 510))
      (s.natReg 50+2) (s.realReg 508) := by
  simp [fieldResult,fieldAtoms,Atom.effect,instructionEffect,data,Data.machine,hz,h2]
lemma frame (s : Data) (hz : s.natReg 56 = 0) (h2 : s.natReg 14 = 2) (j : ℕ)
    (h0 : j ≠ s.natReg 50) (h1 : j ≠ s.natReg 50+2) (h2' : j ≠ s.natReg 50+4) :
    (fieldResult s).natMem j = s.natMem j ∧ (fieldResult s).realMem j = s.realMem j := by
  simp [fieldResult,fieldAtoms,Atom.effect,instructionEffect,data,Data.machine,hz,h2,
    Function.update_of_ne h0,Function.update_of_ne h1,Function.update_of_ne h2']
lemma nat_frame (k : ℕ) (h630 : k ≠ 630) (h670 : k ≠ 670) (h672 : k ≠ 672) (h674 : k ≠ 674) : NatFrame fieldCode k := by
  simp [fieldCode,fieldAtoms,Structured.sequence,NatFrame,writesNat,Ne.symm h630,Ne.symm h670,Ne.symm h672,Ne.symm h674]
lemma real_frame (k : ℕ) : RealFrame fieldCode k := by
  simp [fieldCode,fieldAtoms,Structured.sequence,RealFrame,writesReal]
end DecrAlmostLinearSSSP.Decremental.CoreInitialSaved
end s416
section s417
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitialSaved
open Structured
lemma snapshot {n l : ℕ} (p : Program) (graph : Physical n l) (m N : ℕ) (ξ cap : ℝ) (s : Data)
    (hz : s.natReg 56 = 0) (h2 : s.natReg 14 = 2)
    (hn : s.natReg 66 = n) (hl : s.natReg 536 = l) (hm : s.natReg 540 = m)
    (hξ : s.realReg 510 = ξ) (hcap : s.realReg 508 = cap)
    (hzero : ∀ j < N, s.natMem (s.natReg 50+2*j) = 0 ∧ s.realMem (s.natReg 50+2*j) = 0) :
    CoreRequest.SavedImage N (cutInitial p graph m ξ cap) (fieldResult s) := by
  obtain ⟨h0,h1,h2',hr0,hr1⟩ := values s hz h2
  have hbase : (fieldResult s).natReg 50 = s.natReg 50 := (fields_eval s).nat_frame (nat_frame 50 (by omega) (by omega) (by omega) (by omega))
  refine ⟨?_,?_⟩
  · intro j hj
    rw [hbase]
    by_cases hj3 : j < 3
    · interval_cases j
      · simpa [cutInitial,hn] using h0
      · simpa [cutInitial,hl] using h1
      · simpa [cutInitial,hm] using h2'
    · rw [(frame s hz h2 (s.natReg 50+2*j) (by omega) (by omega) (by omega)).1,(hzero j hj).1]
      simp [cutInitial,show j ≠ 0 by omega,show j ≠ 1 by omega,show j ≠ 2 by omega]
  · intro j hj
    rw [hbase]
    by_cases hj0 : j = 0
    · subst j
      simpa [cutInitial,hξ] using hr0
    · by_cases hj1 : j = 1
      · subst j
        simpa [cutInitial,hcap] using hr1
      · rw [real_memory s hz h2,Function.update_of_ne (show s.natReg 50+2*j ≠ s.natReg 50+2 by omega),
          Function.update_of_ne (show s.natReg 50+2*j ≠ s.natReg 50 by omega),(hzero j hj).2]
        simp [cutInitial,hj0,hj1]
end DecrAlmostLinearSSSP.Decremental.CoreInitialSaved
end s417
section s418
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitialSaved
open Structured
lemma nat_frame_code (N k : ℕ) (hf : k < 116 ∨ 124 < k) (hs : k < 630 ∨ 674 < k) : NatFrame (code N) k := by
  refine ⟨SnapshotFill.nat_frame N k (by omega) (by omega) (by omega) (by omega) (by omega),nat_frame k (by omega) (by omega) (by omega) (by omega)⟩
lemma real_frame_code (N k : ℕ) (hk : k ≠ 116) : RealFrame (code N) k := ⟨SnapshotFill.real_frame N k hk,real_frame k⟩
lemma eval_code {n l : ℕ} (p : Program) (graph : Physical n l) (m N : ℕ) (hN : 3 ≤ N) (ξ cap : ℝ) (s : Data)
    (hz : s.natReg 56 = 0) (h2 : s.natReg 14 = 2) (hunit : s.natReg 26 = 1)
    (hn : s.natReg 66 = n) (hl : s.natReg 536 = l) (hm : s.natReg 540 = m)
    (hξ : s.realReg 510 = ξ) (hcap : s.realReg 508 = cap) :
    ∃ t, Eval (code N) s (6*N+19) t ∧ CoreRequest.SavedImage N (cutInitial p graph m ξ cap) t ∧
      (∀ address, (∀ j < N, address ≠ s.natReg 50+2*j) →
        t.natMem address = s.natMem address ∧ t.realMem address = s.realMem address) := by
  obtain ⟨u,hu,huzero,huframe⟩ := SnapshotFill.eval_code N s hz h2 hunit
  have huf (k : ℕ) (hk : k < 116 ∨ 124 < k) : u.natReg k = s.natReg k :=
    hu.nat_frame (SnapshotFill.nat_frame N k (by omega) (by omega) (by omega) (by omega) (by omega))
  have hur (k : ℕ) (hk : k ≠ 116) : u.realReg k = s.realReg k := hu.real_frame (SnapshotFill.real_frame N k hk)
  have huz : u.natReg 56 = 0 := (huf 56 (by omega)).trans hz
  have hu2 : u.natReg 14 = 2 := (huf 14 (by omega)).trans h2
  have hsaved := snapshot p graph m N ξ cap u huz hu2 ((huf 66 (by omega)).trans hn)
    ((huf 536 (by omega)).trans hl) ((huf 540 (by omega)).trans hm)
    ((hur 510 (by omega)).trans hξ) ((hur 508 (by omega)).trans hcap)
    (by intro j hj;rw [huf 50 (by omega)];exact huzero j hj)
  refine ⟨fieldResult u,?_,hsaved,?_⟩
  · have he := Eval.seq hu (fields_eval u)
    convert he using 1 <;> first | rfl | omega
  · intro address hout
    have hf := frame u huz hu2 address
      (by rw [huf 50 (by omega)];simpa using hout 0 (by omega))
      (by rw [huf 50 (by omega)];simpa using hout 1 (by omega))
      (by rw [huf 50 (by omega)];simpa using hout 2 (by omega))
    exact ⟨hf.1.trans (huframe address hout).1,hf.2.trans (huframe address hout).2⟩
end DecrAlmostLinearSSSP.Decremental.CoreInitialSaved
end s418
section s419
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreSource
open Structured
lemma initial_saved_image (b : Core) (B N : ℕ) (K : ℝ) (state : State b) (s : Data)
    (h : CoreGuestCopy.GammaInvariant b B state b.input.n s)
    (hp : CoreParameters.Values b K s)
    (p : Program) (hN : 10 ≤ N)
    (hz : s.natReg 56 = 0)
    (hw : s.natMem (CoreMemory.sourceRecord b B+6) = 0)
    (htail : ∀ j, N ≤ j → s.natReg (shadowReg j) = 0 ∧ s.realReg (shadowReg j) = 0) :
    ∃ t, Eval (CoreInitialSaved.code N) s (6*N+19) t ∧
      Image B (CoreMemory.sourceRecord b B) N
        (cutInitial p (indexedPhysical b state (logicalIndexEquiv b)) (2*b.input.size)
          (K^(-2 : ℤ)) ((kappa b)^(-2 : ℤ))) t ∧
      ∀ address, address < CoreMemory.sourceRecord b B+8 →
        t.natMem address = s.natMem address ∧ t.realMem address = s.realMem address := by
  obtain ⟨t,he,hs,hframe⟩ := CoreInitialSaved.eval_code p
    (indexedPhysical b state (logicalIndexEquiv b)) (2*b.input.size) N (by omega)
    (K^(-2 : ℤ)) ((kappa b)^(-2 : ℤ)) s hz h.captured.two h.captured.unit
    h.captured.vertices hp.edgeCount hp.cutSize hp.threshold hp.capacityBound
  have hn (k : ℕ) (h1 : k < 116 ∨ 124 < k) (h2 : k < 630 ∨ 674 < k) :
      t.natReg k = s.natReg k := he.nat_frame (CoreInitialSaved.nat_frame_code N k h1 h2)
  have hg (a : ℕ) : ∀ j < N, B+2*(2*a+1) ≠ s.natReg 50+2*j := by
    intro j hj
    rw [h.layout.savedBase]
    have hh := CoreMemory.source_guest_disjoint b B (4+j) a
    omega
  have hwork : ∀ j < N, CoreMemory.sourceRecord b B+6 ≠ s.natReg 50+2*j := by
    intro j hj
    rw [h.layout.savedBase]
    omega
  refine ⟨t,he,⟨(hn 74 (by omega) (by omega)).trans h.base,
    (hn 112 (by omega) (by omega)).trans h.layout.bankFactor,
    (hn 106 (by omega) (by omega)).trans h.layout.sourceRecord,
    (hn 50 (by omega) (by omega)).trans h.layout.savedBase,
    (hn 56 (by omega) (by omega)).trans hz,?_,?_,?_,hs,?_⟩,?_⟩
  · intro a
    exact (hframe _ (hg a)).2.trans (h.input_real b B state s p _ _ _ a)
  · intro a
    exact (hframe _ (hg a)).1.trans (h.input_nat b B state s p _ _ _ a)
  · exact (hframe _ hwork).1.trans hw
  · intro j hj
    obtain ⟨hnz,hrz⟩ := htail j hj
    have hodd : shadowReg j % 2 = 1 := by simp [shadowReg]
    have heven : evenRegisters (CoreInitialSaved.code N) = true := by
      simp [CoreInitialSaved.code,CoreInitialSaved.fieldCode,CoreInitialSaved.fieldAtoms,
        SnapshotFill.code,SnapshotFill.setup,SnapshotFill.setupAtoms,Fill.code,Fill.body,
        Structured.sequence,evenRegisters,evenDestination,storeN,store,nadd,nsub]
    have hf := evenRegisters_frames _ heven (shadowReg j) hodd
    constructor
    · exact (he.nat_frame hf.1).trans hnz
    · exact (he.real_frame hf.2).trans hrz
  · intro address ha
    exact hframe address (by intro j hj;rw [h.layout.savedBase];omega)
end DecrAlmostLinearSSSP.Decremental.CoreSource
end s419
section s420
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreHost
open Structured
lemma guest_frame (b : Core) (B : ℕ) (K : ℝ) (state : State b) (s t : Data) (cost : ℕ)
    (h : Image b B K state s) (hB : b.input.n ≤ B)
    (he : Eval CoreGuestCopy.code s cost t)
    (hn : ∀ j, (∀ i, i < logicalCount b → ∀ offset < 3, j ≠ B+12*i+4*offset+2) → t.natMem j = s.natMem j)
    (hr : ∀ j, (∀ i, i < logicalCount b → j ≠ B+4*i+2) →
      (∀ v, v < b.input.n → j ≠ B+4*(logicalCount b+v)+2) → t.realMem j = s.realMem j) :
    Image b B K state t := by
  apply h.frame b B K state hB
  · intro k hk
    exact he.nat_frame (CoreGuestCopy.nat_frame k (Or.inl (by simp only [NatRegisters,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hk;omega)))
  · intro k hk
    exact he.real_frame (CoreGuestCopy.real_frame k (by simp only [RealRegisters,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hk;omega)
      (by simp only [RealRegisters,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hk;omega)
      (by simp only [RealRegisters,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hk;omega)
      (by simp only [RealRegisters,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hk;omega)
      (by simp only [RealRegisters,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hk;omega))
  · intro address ha
    have hd (a : ℕ) : address ≠ B+4*a+2 := by simpa only [show B+2*(2*a+1) = B+4*a+2 by omega] using ha.guest_disjoint b B address a
    constructor
    · apply hn address
      intro i hi offset ho
      have hh := hd (3*i+offset)
      omega
    · apply hr address
      · intro i hi;exact hd i
      · intro v hv;exact hd (logicalCount b+v)
lemma saved_frame (b : Core) (B N : ℕ) (K : ℝ) (state : State b) (s t : Data) (cost : ℕ)
    (h : Image b B K state s) (hB : b.input.n ≤ B)
    (he : Eval (CoreInitialSaved.code N) s cost t)
    (hm : ∀ address, address < CoreMemory.sourceRecord b B+8 →
      t.natMem address = s.natMem address ∧ t.realMem address = s.realMem address) :
    Image b B K state t := by
  apply h.frame b B K state hB
  · intro k hk
    have hh : (k < 116 ∨ 124 < k) ∧ (k < 630 ∨ 674 < k) := by
      simp only [NatRegisters,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hk
      omega
    exact he.nat_frame (CoreInitialSaved.nat_frame_code N k hh.1 hh.2)
  · intro k hk
    exact he.real_frame (CoreInitialSaved.real_frame_code N k
      (by simp only [RealRegisters,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hk;omega))
  · intro address ha
    exact hm address (by have hh := ha.below_source b B address;omega)
end DecrAlmostLinearSSSP.Decremental.CoreHost
end s420
section s421
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreInitialize
open Structured
lemma boot_cut_input_eval (b : Core) (N registers : ℕ) (p cut : Program) (hreg : 10 ≤ registers) :
    let B := b.input.n+3*b.input.k+2
    let K := computableCutQuality N (2*b.input.size)
    ∃ cost t, Eval (bootCutInputCode N registers) (data (initialMachine p b.input)) cost t ∧
      cost ≤ (80000*(N+1)+265)*b.input.size+
        4*⌈32*logarithm2 (b.input.size+1)/b.input.accuracy⌉₊+6*registers+105 ∧
      CoreHost.Image b B K (initializeState b) t ∧
      CoreSource.Image B (CoreMemory.sourceRecord b B) registers
        (cutInitial cut (indexedPhysical b (initializeState b) (logicalIndexEquiv b))
          (2*b.input.size) (K^(-2 : ℤ)) ((kappa b)^(-2 : ℤ))) t := by
  dsimp only
  let B := b.input.n+3*b.input.k+2
  let K := computableCutQuality N (2*b.input.size)
  have hn : b.input.n ≤ B := by dsimp [B];omega
  obtain ⟨cu,u,hu,hcu,hum,huzero,huw,hutail⟩ := boot_records_eval b N p
  obtain ⟨cv,v,hv,hcv,hvm,hvn,hvr⟩ := CoreGuestCopy.eval_code b B (initializeState b) u
    hum.geometry hum.gradient hum.captured hum.layout hum.base huzero
  have hvmHost := CoreHost.guest_frame b B K (initializeState b) u v cv hum hn hv hvn hvr
  have hvw : v.natMem (CoreMemory.sourceRecord b B+6) = 0 := by
    have hg (a : ℕ) := CoreMemory.source_guest_disjoint b B 3 a
    have hf := hvn (CoreMemory.sourceRecord b B+6) (by
      intro i hi offset ho
      have hh := hg (3*i+offset)
      omega)
    exact hf.trans huw
  have hvtail : ∀ j, registers ≤ j → v.natReg (shadowReg j) = 0 ∧ v.realReg (shadowReg j) = 0 := by
    intro j hj
    have hodd : shadowReg j%2 = 1 := by simp [shadowReg]
    have hf := evenRegisters_frames _ CoreGuestCopy.even_registers (shadowReg j) hodd
    rw [hv.nat_frame hf.1,hv.real_frame hf.2]
    exact hutail j
  obtain ⟨t,ht,htimage,htframe⟩ := CoreSource.initial_saved_image b B registers K (initializeState b) v
    hvm hvmHost.parameters cut hreg hvmHost.captured.zeroN hvw hvtail
  have htmHost := CoreHost.saved_frame b B registers K (initializeState b) v t _ hvmHost hn ht htframe
  refine ⟨cu+(cv+(6*registers+19)),t,Eval.seq hu (Eval.seq hv ht),?_,htmHost,htimage⟩
  nlinarith only [hcu,hcv]
end DecrAlmostLinearSSSP.Decremental.CoreInitialize
end s421
section s422
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental
lemma core_cut_start (b : Core) (K K0 h Γ init : ℝ) (hK : 0 < K)
    (impl : CutImplementation)
    (himpl : ImplementsCut impl (2*b.input.size) (4*b.weightExponent+68) K0 h Γ init (K^(-2 : ℤ))) :
    ∃ first,
      Ends impl.program (cutInitial impl.program
        (indexedPhysical b (initializeState b) (logicalIndexEquiv b)) (2*b.input.size)
        (K^(-2 : ℤ)) ((kappa b)^(-2 : ℤ))) first ∧
      CutModel b (logicalIndexEquiv b) (initializeState b)
        (impl.view b.input.n (logicalCount b) first) ∧
      (impl.view b.input.n (logicalCount b) first).hasCut = false ∧
      (first.work : ℝ) ≤ init ∧
      CutSession impl b.input.n (logicalCount b) (2*b.input.size) (4*b.weightExponent+68)
        first K0 (K^(-2 : ℤ)) h Γ init := by
  have hs := RuntimeBounds.initial b K hK
  have hv := runtime_indexed_physical_valid b K (initializeState b) hs
    (logicalIndexEquiv b) (logicalCount_le b)
  have hcap : 0 < (kappa b)^(-2 : ℤ) := zpow_pos (core_kappa_bounds b).1 _
  obtain ⟨first,he,hp,hy,hb,hh,hw,hr⟩ := himpl.initialize_session
    (indexedPhysical b (initializeState b) (logicalIndexEquiv b)) ((kappa b)^(-2 : ℤ))
    hv hcap (by simpa only [Nat.cast_mul,Nat.cast_ofNat] using (core_capacityBound_range b).2) (by
      intro e he
      change (initializeState b).cache ((logicalIndexEquiv b).symm e) ≤ _
      have hf0 : ∀ d, 0 ≤ (initializeState b).cache d := fun d => (by norm_num : (0:ℝ) ≤ 1).trans (hs.lower d)
      exact (Finset.single_le_sum (fun d _ => hf0 d) (Finset.mem_univ _)).trans
        ((cache_total_upper b K _ hs.invariant.cache).trans (core_cache_total_capacityBound b)))
  exact ⟨first,he,CutModel.initial b (logicalIndexEquiv b) _ hp hy hb,hh,hw,hr⟩
end DecrAlmostLinearSSSP.Decremental
end s422
section s423
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreInitialize
open Structured
lemma boot_cut_eval (b : Core) (N : ℕ) (p : Program) (impl : CutImplementation)
    (K0 h Γ init : ℝ)
    (himpl : ImplementsCut impl (2*b.input.size) (4*b.weightExponent+68) K0 h Γ init
      ((computableCutQuality N (2*b.input.size))^(-2 : ℤ))) :
    let B := b.input.n+3*b.input.k+2
    let K := computableCutQuality N (2*b.input.size)
    let registers := sourceRegisters impl.program
    ∃ cost t first, Eval (bootCutCode N impl.program) (data (initialMachine p b.input)) cost t ∧
      (cost : ℝ) ≤ ((80000*(N+1)+265)*b.input.size+
        4*⌈32*logarithm2 (b.input.size+1)/b.input.accuracy⌉₊+14*registers+120 : ℕ)+
        (dispatchCharge impl.program.code+2)*init ∧
      CoreHost.Image b B K (initializeState b) t ∧
      CoreSource.Image B (CoreMemory.sourceRecord b B) registers first t ∧
      CutModel b (logicalIndexEquiv b) (initializeState b) (impl.view b.input.n (logicalCount b) first) ∧
      (impl.view b.input.n (logicalCount b) first).hasCut = false ∧
      (first.work : ℝ) ≤ init ∧
      Ends impl.program (cutInitial impl.program (indexedPhysical b (initializeState b) (logicalIndexEquiv b))
        (2*b.input.size) (K^(-2 : ℤ)) ((kappa b)^(-2 : ℤ))) first ∧
      CutSession impl b.input.n (logicalCount b) (2*b.input.size) (4*b.weightExponent+68)
        first K0 (K^(-2 : ℤ)) h Γ init := by
  dsimp only
  let B := b.input.n+3*b.input.k+2
  let K := computableCutQuality N (2*b.input.size)
  let registers := sourceRegisters impl.program
  have hreg : 10 ≤ registers := by dsimp [registers,sourceRegisters];omega
  have hbound : registerBound impl.program.code ≤ registers := by dsimp [registers,sourceRegisters];omega
  have hK : 0 < K := by exact pow_pos (by norm_num) _
  obtain ⟨first,hfirst,hmodel,hhas,hwork,hsession⟩ := core_cut_start b K K0 h Γ init hK impl himpl
  obtain ⟨cu,u,hu,hcu,hum,hus⟩ := boot_cut_input_eval b N registers p impl.program hreg
  let g := cutInitial impl.program (indexedPhysical b (initializeState b) (logicalIndexEquiv b))
    (2*b.input.size) (K^(-2 : ℤ)) ((kappa b)^(-2 : ℤ))
  have hodd : ∃ r, CoreMemory.sourceRecord b B = B+2*r+1 := by
    exact ⟨5*logicalCount b+b.input.n,by dsimp [CoreMemory.sourceRecord,CoreMemory.gradientBase];omega⟩
  obtain ⟨cc,t,ht,hcc,hts,htrep,htframe⟩ := hus.call B (CoreMemory.sourceRecord b B) registers impl.program.initPC
    impl.program g first u hbound hodd rfl rfl rfl
    (cutInitial_zero_tail impl.program _ _ _ _ (by omega)) hfirst
  have htm := CoreHost.source_frame b B registers impl.program.initPC K (initializeState b) impl.program
    u t cc hum (by dsimp [B];omega) ht htframe
  refine ⟨cu+cc,t,first,Eval.seq hu ht,?_,htm,hts,hmodel,hhas,hwork,hfirst,hsession⟩
  have hcc' : cc ≤ (dispatchCharge impl.program.code+2)*first.work+8*registers+15 := by
    simpa only [g,cutInitial,Nat.sub_zero] using hcc
  have hsum : cu+cc ≤ (80000*(N+1)+265)*b.input.size+
      4*⌈32*logarithm2 (b.input.size+1)/b.input.accuracy⌉₊+14*registers+120+
      (dispatchCharge impl.program.code+2)*first.work := by omega
  have hr : (cu+cc : ℝ) ≤ ((80000*(N+1)+265)*b.input.size+
      4*⌈32*logarithm2 (b.input.size+1)/b.input.accuracy⌉₊+14*registers+120 : ℕ)+
      (dispatchCharge impl.program.code+2)*first.work := by exact_mod_cast hsum
  have hmul : ((dispatchCharge impl.program.code : ℝ)+2)*first.work ≤
      ((dispatchCharge impl.program.code : ℝ)+2)*init := mul_le_mul_of_nonneg_left hwork (by positivity)
  dsimp only [registers] at hr
  push_cast at hr ⊢
  linarith only [hr,hmul]
end DecrAlmostLinearSSSP.Decremental.CoreInitialize
end s423
section s424
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreInitialize
open Structured
lemma boot_context_eval (b : Core) (N : ℕ) (p : Program) (impl : CutImplementation)
    (K0 h Γ init : ℝ)
    (himpl : ImplementsCut impl (2*b.input.size) (4*b.weightExponent+68) K0 h Γ init
      ((computableCutQuality N (2*b.input.size))^(-2 : ℤ))) :
    let B := b.input.n+3*b.input.k+2
    let K := computableCutQuality N (2*b.input.size)
    let registers := sourceRegisters impl.program
    ∃ cost t, ∃ ctx : CoreNativeCut.Context b B registers (2*b.input.size) (4*b.weightExponent+68)
        impl K0 (K^(-2 : ℤ)) h Γ init t,
      Eval (bootCutCode N impl.program) (data (initialMachine p b.input)) cost t ∧
      (cost : ℝ) ≤ ((80000*(N+1)+265)*b.input.size+
        4*⌈32*logarithm2 (b.input.size+1)/b.input.accuracy⌉₊+14*registers+120 : ℕ)+
        (dispatchCharge impl.program.code+2)*init ∧
      CoreHost.Image b B K (initializeState b) t ∧
      CutModel b (logicalIndexEquiv b) (initializeState b) (impl.view b.input.n (logicalCount b) ctx.current) ∧
      (impl.view b.input.n (logicalCount b) ctx.current).hasCut = false ∧
      ctx.ops = [] ∧ ctx.machines = [ctx.current] ∧ ctx.first = ctx.current := by
  dsimp only
  let B := b.input.n+3*b.input.k+2
  let K := computableCutQuality N (2*b.input.size)
  let registers := sourceRegisters impl.program
  obtain ⟨cost,t,first,he,hcost,htm,hts,hmodel,hhas,hwork,hEnd,hsession⟩ := boot_cut_eval b N p impl K0 h Γ init himpl
  have hbound : registerBound impl.program.code ≤ registers := by dsimp [registers,sourceRegisters];omega
  have hzero : ZeroRegisterTail registers first :=
    (cutInitial_zero_tail impl.program (indexedPhysical b (initializeState b) (logicalIndexEquiv b))
      (2*b.input.size) (K^(-2 : ℤ)) ((kappa b)^(-2 : ℤ)) (by dsimp [registers,sourceRegisters];omega)).ends_of_bound hbound hEnd
  let ctx : CoreNativeCut.Context b B registers (2*b.input.size) (4*b.weightExponent+68)
      impl K0 (K^(-2 : ℤ)) h Γ init t :=
    ⟨first,first,[],[first],hsession,CutRun.start,by rfl,hzero,hts⟩
  exact ⟨cost,t,ctx,he,hcost,htm,hmodel,hhas,rfl,rfl,rfl⟩
end DecrAlmostLinearSSSP.Decremental.CoreInitialize
end s424
section s425
set_option autoImplicit false
open Filter
open scoped Topology
namespace DecrAlmostLinearSSSP.Decremental
lemma cutLogHeight_tendsto : Tendsto cutLogHeight atTop atTop := by
  apply tendsto_atTop.mpr
  intro B
  filter_upwards [eventually_ge_atTop (2^B)] with m hm
  have hp := Exact.height_spec (max 2 m)
  change max 2 m < 2^cutLogHeight m at hp
  have hlarge : 2^B ≤ max 2 m := hm.trans (le_max_right _ _)
  have hstrict : B < cutLogHeight m := by
    by_contra h
    have hh := Nat.pow_le_pow_right (by norm_num : 0 < 2) (not_lt.mp h)
    omega
  omega
lemma cutRoot_tendsto : Tendsto cutRoot atTop atTop := by
  apply tendsto_atTop.mpr
  intro B
  filter_upwards [cutLogHeight_tendsto.eventually_ge_atTop (B^12)] with m hm
  have hh : B ≤ Nat.nthRoot 12 (cutLogHeight m) :=
    (Nat.le_nthRoot_iff (by norm_num : (12 : ℕ) ≠ 0)).mpr hm
  dsimp [cutRoot]
  omega
lemma cutRoot_real_tendsto : Tendsto (fun m => (cutRoot m : ℝ)) atTop atTop :=
  (tendsto_natCast_atTop_atTop (R := ℝ)).comp cutRoot_tendsto
lemma computableCutQuality_log_ratio (N m : ℕ) :
    Real.log (computableCutQuality N m)/Real.log (max 2 m : ℕ) ≤ 8192*(N : ℝ)/(cutRoot m : ℝ) := by
  have hr : (0 : ℝ) < cutRoot m := by exact_mod_cast (show 0 < cutRoot m by have hh := cutRoot_ge_two m;omega)
  have hlog := log_size_positive m
  have hbound : ((cutRoot m : ℝ)^11*Real.log 2)/Real.log (max 2 m : ℕ) ≤ 8192/(cutRoot m : ℝ) := by
    apply (div_le_div_iff₀ hlog hr).mpr
    calc
      ((cutRoot m : ℝ)^11*Real.log 2)*(cutRoot m : ℝ) = (cutRoot m : ℝ)^12*Real.log 2 := by ring
      _ ≤ _ := cutRoot_log_power_bound m
  rw [computableCutQuality,Real.log_pow]
  simp only [Nat.cast_mul,Nat.cast_pow]
  calc
    (N : ℝ)*(cutRoot m : ℝ)^11*Real.log 2/Real.log (max 2 m : ℕ) =
      (N : ℝ)*(((cutRoot m : ℝ)^11*Real.log 2)/Real.log (max 2 m : ℕ)) := by ring
    _ ≤ (N : ℝ)*(8192/(cutRoot m : ℝ)) := mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg _)
    _ = _ := by ring
lemma computableCutQuality_subpolynomial (N : ℕ) : Subpolynomial (computableCutQuality N) := by
  refine ⟨fun m => pow_pos (by norm_num) _,?_⟩
  have hu : Tendsto (fun m => 8192*(N : ℝ)/(cutRoot m : ℝ)) atTop (nhds 0) :=
    cutRoot_real_tendsto.const_div_atTop _
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
  · intro m
    have hK : 1 ≤ computableCutQuality N m := one_le_pow₀ (by norm_num)
    exact div_nonneg (Real.log_nonneg hK) (log_size_positive m).le
  · exact computableCutQuality_log_ratio N
lemma computableCutQuality_ge_32 (N m : ℕ) (hN : 5 ≤ N) : 32 ≤ computableCutQuality N m := by
  have hr := cutRoot_ge_two m
  have hpow : 1 ≤ (cutRoot m)^11 := Nat.one_le_pow _ _ (by omega)
  have hexp : 5 ≤ N*(cutRoot m)^11 := by nlinarith only [hN,hpow]
  have hh := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hexp
  norm_num at hh
  exact hh
end DecrAlmostLinearSSSP.Decremental
end s425
section s426
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
lemma initialize_eval (b : Core) (qualityPower : ℕ) (hpower : 5 ≤ qualityPower) (p : Program) (impl : CutImplementation)
    (K0 h Γ init : ℝ) (hK0 : 0 < K0)
    (hKK : K0 ≤ computableCutQuality qualityPower (2*b.input.size))
    (himpl : ImplementsCut impl (2*b.input.size) (4*b.weightExponent+68) K0 h Γ init
      ((computableCutQuality qualityPower (2*b.input.size))^(-2 : ℤ))) :
    let B := b.input.n+3*b.input.k+2
    let K := computableCutQuality qualityPower (2*b.input.size)
    let registers := CoreInitialize.sourceRegisters impl.program
    ∃ cost t, ∃ after : State b,
    ∃ next : Context b B registers (2*b.input.size) (4*b.weightExponent+68) impl K0 (K^(-2 : ℤ)) h Γ init t,
      Eval (initCode qualityPower impl.program) (data (initialMachine p b.input)) cost t ∧
      CoreHost.Image b B K after t ∧ RuntimeBounds b K after ∧
      CutModel b (logicalIndexEquiv b) after (impl.view b.input.n (logicalCount b) next.current) ∧
      after.stopped = true ∧ ReadoutCertificate b after ∧ after.active = Finset.univ ∧ after.pending = [] ∧
      CoreRepair.OperationDebt b after next.ops.length (reportVolume next.machines) 0 ∧
      toggleVolume next.ops = after.toggles ∧
      (cost : ℝ) ≤ ((80000*(qualityPower+1)+265)*b.input.size+
        4*⌈32*logarithm2 (b.input.size+1)/b.input.accuracy⌉₊+14*registers+120 : ℕ)+
        (dispatchCharge impl.program.code+2)*init+
        (credit b registers impl.program after next.current next.ops next.machines : ℕ)+7 := by
  dsimp only
  let B := b.input.n+3*b.input.k+2
  let K := computableCutQuality qualityPower (2*b.input.size)
  let registers := CoreInitialize.sourceRegisters impl.program
  have hK : 32 ≤ K := computableCutQuality_ge_32 qualityPower (2*b.input.size) hpower
  have hB : b.input.n ≤ B := by dsimp [B];omega
  have hN : 10 ≤ registers := by dsimp [registers,CoreInitialize.sourceRegisters];omega
  have hBound : registerBound impl.program.code ≤ registers := by dsimp [registers,CoreInitialize.sourceRegisters];omega
  obtain ⟨cu,u,ctx,hu,hcu,hum,humodel,huhas,huops,humachines,hufirst⟩ :=
    CoreInitialize.boot_context_eval b qualityPower p impl K0 h Γ init himpl
  have hdebt : CoreRepair.OperationDebt b (initializeState b) ctx.ops.length (reportVolume ctx.machines) 0 := by
    simp [CoreRepair.OperationDebt,CoreRepair.stoppedBit,initializeState,huops,humachines,reportVolume]
  have hToggle : toggleVolume ctx.ops = (initializeState b).toggles := by rw [huops];simp [toggleVolume,initializeState]
  obtain ⟨cr,t,after,next,ht,htm,htbounds,htmodel,htstop,htcert,htfirst,htdebt,htToggle,htactive,htpending,htcost⟩ :=
    ctx.repair hum hB hN hBound hK hK0 hKK (RuntimeBounds.initial b K (by linarith)) humodel rfl 0 hdebt hToggle
  have hactive : after.active = Finset.univ := htactive
  change cr+credit b registers impl.program (initializeState b) ctx.current ctx.ops ctx.machines ≤
    credit b registers impl.program after next.current next.ops next.machines+7 at htcost
  have hcr : cr ≤ credit b registers impl.program after next.current next.ops next.machines+7 := by omega
  have hcrReal : (cr : ℝ) ≤ (credit b registers impl.program after next.current next.ops next.machines : ℕ)+7 := by exact_mod_cast hcr
  refine ⟨cu+cr,t,after,next,Eval.seq hu ht,htm,htbounds,htmodel,htstop,htcert,hactive,htpending,htdebt,htToggle,?_⟩
  dsimp only [registers] at hcrReal
  push_cast at hcu hcrReal ⊢
  linarith only [hcu,hcrReal]
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s426
section s427
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
lemma coreProgram_query (qualityPower : ℕ) (p : Program) (c : Machine) (v : ℕ) :
    ∃ d, Ends (coreProgram qualityPower p)
      {resume c (coreProgram qualityPower p).query with natReg := Function.update c.natReg 5 v} d ∧
      d.work+6 ≤ c.work+9 ∧ d.natReg 6 = c.natMem v ∧ d.realReg 1 = c.realMem v ∧
      d.realMem = c.realMem ∧ d.natMem = c.natMem :=
  program_query_nine (initCode qualityPower p) (updateCode (CoreInitialize.sourceRegisters p) p) c v
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s427
section s428
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
lemma program_initialization (b : Core) (qualityPower : ℕ) (hpower : 5 ≤ qualityPower) (impl : CutImplementation)
    (K0 h Γ init : ℝ) (hK0 : 0 < K0)
    (hKK : K0 ≤ computableCutQuality qualityPower (2*b.input.size))
    (himpl : ImplementsCut impl (2*b.input.size) (4*b.weightExponent+68) K0 h Γ init
      ((computableCutQuality qualityPower (2*b.input.size))^(-2 : ℤ))) :
    let B := b.input.n+3*b.input.k+2
    let K := computableCutQuality qualityPower (2*b.input.size)
    let registers := CoreInitialize.sourceRegisters impl.program
    ∃ cost c, Ends (coreProgram qualityPower impl.program)
      (initialMachine (coreProgram qualityPower impl.program) b.input) c ∧ c.work = cost+1 ∧
    ∃ ready : Ready b B registers K K0 h Γ init impl [] (data c),
      (c.work : ℝ) ≤ ((80000*(qualityPower+1)+265)*b.input.size+
        4*⌈32*logarithm2 (b.input.size+1)/b.input.accuracy⌉₊+14*registers+120 : ℕ)+
        (dispatchCharge impl.program.code+2)*init+(ready.credit : ℝ)+8 := by
  dsimp only
  let p := coreProgram qualityPower impl.program
  let B := b.input.n+3*b.input.k+2
  let K := computableCutQuality qualityPower (2*b.input.size)
  let registers := CoreInitialize.sourceRegisters impl.program
  obtain ⟨cost,t,after,ctx,he,htm,htbounds,htmodel,htstop,htcert,htactive,htpending,htdebt,htToggle,hcost⟩ :=
    initialize_eval b qualityPower hpower p impl K0 h Γ init hK0 hKK himpl
  obtain ⟨c,hend,hdata,hwork⟩ := command_ends he p 0 (initialMachine p b.input)
    (program_init _ _) rfl rfl rfl rfl (by simpa only [p,coreProgram,Nat.zero_add] using program_init_halt (initCode qualityPower impl.program) (updateCode registers impl.program))
  subst t
  have hcwork : c.work = cost+1 := by simpa only [initialMachine,Nat.zero_add] using hwork
  let ready : Ready b B registers K K0 h Γ init impl [] (data c) :=
    ⟨after,ctx,htm,htbounds,htmodel,htstop,htcert,htpending,by simpa [live] using htactive,htdebt,htToggle⟩
  refine ⟨cost,c,hend,hcwork,ready,?_⟩
  rw [hcwork]
  change ((cost+1 : ℕ) : ℝ) ≤ ((80000*(qualityPower+1)+265)*b.input.size+
    4*⌈32*logarithm2 (b.input.size+1)/b.input.accuracy⌉₊+14*registers+120 : ℕ)+
    (dispatchCharge impl.program.code+2)*init+(credit b registers impl.program after ctx.current ctx.ops ctx.machines : ℝ)+8
  change (cost : ℝ) ≤ ((80000*(qualityPower+1)+265)*b.input.size+
    4*⌈32*logarithm2 (b.input.size+1)/b.input.accuracy⌉₊+14*registers+120 : ℕ)+
    (dispatchCharge impl.program.code+2)*init+(credit b registers impl.program after ctx.current ctx.ops ctx.machines : ℝ)+7 at hcost
  push_cast at hcost ⊢
  linarith only [hcost]
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s428
section s429
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
lemma Ready.external_credit {b : Core} {B N : ℕ} {K K0 h Γ init : ℝ} {impl : CutImplementation}
    {deleted : List (Fin b.input.k)} {s : Data} (r : Ready b B N K K0 h Γ init impl deleted s)
    (hB : b.input.n ≤ B) (value : ℕ) : (r.external hB value).credit = r.credit := rfl
lemma live_append_singleton {k : ℕ} (deleted : List (Fin k)) (e : Fin k) :
    live (deleted++[e]) = (live deleted).erase e := by
  ext d
  simp [live,Finset.mem_erase,and_comm,ne_comm]
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s429
section s430
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
lemma program_update (b : Core) (qualityPower : ℕ) (hpower : 5 ≤ qualityPower) (impl : CutImplementation)
    (K0 h Γ init : ℝ) (hK0 : 0 < K0) (hKK : K0 ≤ computableCutQuality qualityPower (2*b.input.size))
    (deleted : List (Fin b.input.k)) (c : Machine)
    (ready : Ready b (b.input.n+3*b.input.k+2) (CoreInitialize.sourceRegisters impl.program)
      (computableCutQuality qualityPower (2*b.input.size)) K0 h Γ init impl deleted (data c)) (e : Fin b.input.k) :
    ∃ cost d, Ends (coreProgram qualityPower impl.program) (deletionMachine (coreProgram qualityPower impl.program) c e.val) d ∧
      d.work = c.work+cost+1 ∧
    ∃ next : Ready b (b.input.n+3*b.input.k+2) (CoreInitialize.sourceRegisters impl.program)
      (computableCutQuality qualityPower (2*b.input.size)) K0 h Γ init impl (deleted++[e]) (data d),
      d.work+6+ready.credit ≤ c.work+next.credit := by
  let p := coreProgram qualityPower impl.program
  let B := b.input.n+3*b.input.k+2
  let N := CoreInitialize.sourceRegisters impl.program
  let K := computableCutQuality qualityPower (2*b.input.size)
  let start := deletionMachine p c e.val
  have hB : b.input.n ≤ B := by dsimp [B];omega
  have hN : 10 ≤ N := by dsimp [N,CoreInitialize.sourceRegisters];omega
  have hBound : registerBound impl.program.code ≤ N := by dsimp [N,CoreInitialize.sourceRegisters];omega
  have hK : 32 ≤ K := computableCutQuality_ge_32 qualityPower (2*b.input.size) hpower
  let hs : Ready b B N K K0 h Γ init impl deleted (data start) := by
    change Ready b B N K K0 h Γ init impl deleted {data c with natReg := Function.update (data c).natReg 5 e.val}
    exact ready.external hB e.val
  obtain ⟨cost,t,after,ctx,he,htm,htbounds,htmodel,htstop,htcert,htpending,htactive,htfirst,htdebt,htToggle,htcost⟩ :=
    hs.context.update hs.host hB hN hBound hK hK0 hKK hs.bounds hs.model e hs.pending rfl (6*deleted.length) hs.debt hs.toggles
  obtain ⟨d,hend,hdata,hwork⟩ := command_ends he p p.update start (Structured.program_update _ _) rfl rfl rfl rfl
    (program_update_halt _ _)
  subst t
  have hdwork : d.work = c.work+cost+1 := hwork
  have hactive : after.active = live (deleted++[e]) := by rw [htactive,hs.active,live_append_singleton]
  have hdebt : CoreRepair.OperationDebt b after ctx.ops.length (reportVolume ctx.machines) (6*(deleted++[e]).length) := by
    simpa [List.length_append,Nat.mul_add] using htdebt
  let next : Ready b B N K K0 h Γ init impl (deleted++[e]) (data d) :=
    ⟨after,ctx,htm,htbounds,htmodel,htstop,htcert,htpending,hactive,hdebt,htToggle⟩
  have hbudget : cost+7+ready.credit ≤ next.credit := htcost
  exact ⟨cost,d,hend,hdwork,next,by omega⟩
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s430
section s431
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
lemma online (b : Core) (qualityPower : ℕ) (hpower : 5 ≤ qualityPower) (impl : CutImplementation)
    (K0 h Γ init : ℝ) (hK0 : 0 < K0) (hKK : K0 ≤ computableCutQuality qualityPower (2*b.input.size))
    (himpl : ImplementsCut impl (2*b.input.size) (4*b.weightExponent+68) K0 h Γ init
      ((computableCutQuality qualityPower (2*b.input.size))^(-2 : ℤ))) (ds : List (Fin b.input.k)) :
    ∃ (cs : List Machine) (last : Machine), OnlineRun (coreProgram qualityPower impl.program) b.input ds cs ∧
      cs.length = ds.length+1 ∧ cs.getLast? = some last ∧ Completed b qualityPower impl K0 h Γ init ds last ∧
      ∀ j c, cs[j]? = some c → Completed b qualityPower impl K0 h Γ init (ds.take j) c := by
  classical
  induction ds using List.reverseRecOn with
  | nil =>
    obtain ⟨cost,c,he,hw,ready,hwork⟩ := program_initialization b qualityPower hpower impl K0 h Γ init hK0 hKK himpl
    have hcompleted : Completed b qualityPower impl K0 h Γ init [] c := by
      refine ⟨ready,?_⟩
      simpa only [initialBudget,List.length_nil,Nat.mul_zero,Nat.add_zero,add_assoc,add_comm,add_left_comm] using hwork
    refine ⟨[c],c,OnlineRun.init he,rfl,rfl,hcompleted,?_⟩
    intro j d hd
    cases j with
    | zero =>
      have hdc : c = d := Option.some.inj hd
      subst d
      exact hcompleted
    | succ j => simp at hd
  | append_singleton ds e ih =>
    obtain ⟨cs,c,hr,hlen,hlast,hcompleted,hprefix⟩ := ih
    obtain ⟨ready,hwork⟩ := hcompleted
    obtain ⟨cost,d,he,hdwork,next,hcharge⟩ := program_update b qualityPower hpower impl K0 h Γ init hK0 hKK ds c ready e
    have hdCompleted : Completed b qualityPower impl K0 h Γ init (ds++[e]) d := by
      refine ⟨next,?_⟩
      have hchargeR : (d.work : ℝ)+6+(ready.credit : ℝ) ≤ (c.work : ℝ)+(next.credit : ℝ) := by exact_mod_cast hcharge
      push_cast at hwork ⊢
      simp only [List.length_append,List.length_singleton,Nat.cast_add,Nat.cast_one]
      linarith only [hwork,hchargeR]
    refine ⟨cs++[d],d,OnlineRun.next hr hlast e he,?_,by simp,hdCompleted,?_⟩
    · simp only [List.length_append,List.length_singleton,hlen]
    · intro j z hz
      by_cases hj : j < cs.length
      · have hget : cs[j]? = some z := by rwa [List.getElem?_append_left hj] at hz
        have hjds : j ≤ ds.length := by omega
        have htake : (ds++[e]).take j = ds.take j := by
          rw [List.take_append]
          simp only [Nat.sub_eq_zero_of_le hjds,List.take_zero,List.append_nil]
        rw [htake]
        exact hprefix j z hget
      · have hjlen : j < (cs++[d]).length := by
          by_contra hn
          have hnone : (cs++[d])[j]? = none := List.getElem?_eq_none_iff.mpr (by omega)
          rw [hnone] at hz
          contradiction
        have hjeq : j = cs.length := by simp only [List.length_append,List.length_singleton] at hjlen;omega
        subst j
        rw [List.getElem?_append_right le_rfl,Nat.sub_self] at hz
        have hdz : d = z := Option.some.inj hz
        subst z
        have htake : (ds++[e]).take cs.length = ds++[e] := by
          apply List.take_of_length_le
          simp only [List.length_append,List.length_singleton,hlen]
          exact le_rfl
        rw [htake]
        exact hdCompleted
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s431
section s432
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
lemma Completed.correct {b : Core} {qualityPower : ℕ} {impl : CutImplementation}
    {K0 h Γ init : ℝ} {deleted : List (Fin b.input.k)} {c : Machine}
    (hc : Completed b qualityPower impl K0 h Γ init deleted c) :
    stored c b.input.source.val = 0 ∧
      (∀ v : Fin b.input.n, c.natMem v.val ≤ 1 ∧ (c.natMem v.val = 0 → 0 ≤ c.realMem v.val)) ∧
      ∀ v : Fin b.input.n, b.input.dist deleted v ≤ stored c v.val ∧
        stored c v.val ≤ ENNReal.ofReal (1+b.input.accuracy)*b.input.dist deleted v ∧
        (stored c v.val = ⊤ ↔ ¬Reachable b.input.graph (live deleted) b.input.source v) := by
  obtain ⟨ready,_⟩ := hc
  have hcorrect := ready.host.certified b _ _ ready.state (Structured.data c) ready.certificate
  rw [ready.active] at hcorrect
  exact hcorrect
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s432
section s433
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreRepair
lemma stoppedBit_le_one {b : Core} (s : State b) : stoppedBit s ≤ 1 := by
  unfold stoppedBit
  split <;> omega
end DecrAlmostLinearSSSP.Decremental.CoreRepair
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
lemma Context.credit_bound {b : Core} {B N : ℕ} {K K0 h Γ init : ℝ} {impl : CutImplementation}
    {s : Structured.Data} (ctx : Context b B N (2*b.input.size) (4*b.weightExponent+68) impl K0 (K^(-2 : ℤ)) h Γ init s)
    (state : State b) (offset : ℕ) (T : ℝ) (hh : 0 ≤ h) (hΓ : 0 ≤ Γ)
    (hT : (state.toggles : ℝ) ≤ T)
    (hdebt : CoreRepair.OperationDebt b state ctx.ops.length (reportVolume ctx.machines) offset)
    (hToggle : toggleVolume ctx.ops = state.toggles) :
    (credit b N impl.program state ctx.current ctx.ops ctx.machines : ℝ) ≤
      (dispatchCharge impl.program.code+2 : ℕ)*init+
      ((dispatchCharge impl.program.code+2 : ℕ)*h+100*(N+1 : ℕ))*
        (5*(Γ*K^2*T)+2*T+offset+1)+
      ((dispatchCharge impl.program.code+2 : ℕ)*h+20)*(Γ*K^2*T)+10 := by
  let D : ℝ := (dispatchCharge impl.program.code+2 : ℕ)
  let C : ℝ := 100*((N+1 : ℕ) : ℝ)
  let R : ℝ := (reportVolume ctx.machines : ℕ)
  let L : ℝ := (ctx.ops.length : ℕ)
  let W : ℝ := (ctx.current.work : ℕ)
  have hD : 0 ≤ D := Nat.cast_nonneg _
  have hC : 0 ≤ C := by dsimp [C];positivity
  have hR0 : 0 ≤ R := Nat.cast_nonneg _
  have hL0 : 0 ≤ L := Nat.cast_nonneg _
  have hR : R ≤ Γ*K^2*T := by
    have hr := ctx.report_bound
    rw [hToggle] at hr
    have hr' : R ≤ Γ*(state.toggles : ℝ)*K^2 := by
      simpa only [R,div_eq_mul_inv,zpow_neg,zpow_ofNat,inv_inv] using hr
    calc
      R ≤ Γ*(state.toggles : ℝ)*K^2 := hr'
      _ = (Γ*K^2)*(state.toggles : ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hT (mul_nonneg hΓ (sq_nonneg K))
  have hLNat : ctx.ops.length ≤ 5*reportVolume ctx.machines+2*state.toggles+offset+1 := by
    have hb := CoreRepair.stoppedBit_le_one state
    unfold CoreRepair.OperationDebt at hdebt
    omega
  have hLRaw : L ≤ 5*R+2*(state.toggles : ℝ)+offset+1 := by
    change (ctx.ops.length : ℝ) ≤ 5*(reportVolume ctx.machines : ℝ)+2*(state.toggles : ℝ)+(offset : ℝ)+1
    exact_mod_cast hLNat
  have hL : L ≤ 5*(Γ*K^2*T)+2*T+offset+1 := by linarith only [hLRaw,hR,hT]
  have hW : W ≤ init+h*(L+R) := by
    have hw := ctx.work_bound
    push_cast at hw
    change W+6*L ≤ init+h*(L+R) at hw
    linarith only [hw,hL0]
  have hbit : (CoreRepair.stoppedBit state : ℝ) ≤ 1 := by exact_mod_cast CoreRepair.stoppedBit_le_one state
  have hCredit : (credit b N impl.program state ctx.current ctx.ops ctx.machines : ℝ) =
      D*W+C*L+20*R+10*(CoreRepair.stoppedBit state : ℝ) := by
    simp [credit,CoreRepair.nativeCredit,D,C,W,L,R]
  rw [hCredit]
  change D*W+C*L+20*R+10*(CoreRepair.stoppedBit state : ℝ) ≤
    D*init+(D*h+C)*(5*(Γ*K^2*T)+2*T+offset+1)+(D*h+20)*(Γ*K^2*T)+10
  calc
    _ ≤ D*(init+h*(L+R))+C*L+20*R+10 := by
      have hw := mul_le_mul_of_nonneg_left hW hD
      have hb := mul_le_mul_of_nonneg_left hbit (by norm_num : (0:ℝ) ≤ 10)
      linarith only [hw,hb]
    _ = D*init+(D*h+C)*L+(D*h+20)*R+10 := by ring
    _ ≤ _ := by
      have hl := mul_le_mul_of_nonneg_left hL (add_nonneg (mul_nonneg hD hh) hC)
      have hr := mul_le_mul_of_nonneg_left hR (add_nonneg (mul_nonneg hD hh) (by norm_num : (0:ℝ) ≤ 20))
      linarith only [hl,hr]
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s433
section s434
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
lemma dynamic_budget_arithmetic (D C d h Γ K L M : ℝ)
    (hD : 0 ≤ D) (hC : 20 ≤ C) (hd : 1 ≤ d) (hh : 0 ≤ h) (hΓ : 0 ≤ Γ)
    (hK : 1 ≤ K) (hL : 1 ≤ L) (hM : 1 ≤ M) (offset : ℝ) (hoff0 : 0 ≤ offset) (hoff : offset ≤ 6*M) :
    let T := 1040*d*K^3*L^2*M
    (D*h+C)*(5*(Γ*K^2*T)+2*T+offset+1)+(D*h+20)*(Γ*K^2*T)+10 ≤
      10000*d*(D+C)*(1+h)*(1+Γ)*K^5*L^2*M+10 := by
  dsimp only
  have hDCh : D*h+C ≤ (D+C)*(1+h) := by nlinarith
  have hD20h : D*h+20 ≤ (D+C)*(1+h) := by nlinarith
  have hKpow : K^3 ≤ K^5 := by
    exact pow_le_pow_right₀ hK (by omega)
  have hKL : 1 ≤ K^5*L^2 := by
    have hK5 : 1 ≤ K^5 := one_le_pow₀ hK
    have hL2 : 1 ≤ L^2 := one_le_pow₀ hL
    nlinarith
  have hT : 1040*d*K^3*L^2*M ≤ 1040*d*K^5*L^2*M := by gcongr
  have hR : Γ*K^2*(1040*d*K^3*L^2*M) = 1040*d*Γ*K^5*L^2*M := by ring
  rw [hR]
  have hbase : offset+1 ≤ 7*d*K^5*L^2*M := by
    have hprod : M ≤ d*(K^5*L^2)*M := by nlinarith [mul_le_mul_of_nonneg_right hKL (show 0 ≤ M by linarith)]
    nlinarith
  have hcalls : 5*(1040*d*Γ*K^5*L^2*M)+2*(1040*d*K^3*L^2*M)+offset+1 ≤
      8000*d*(1+Γ)*K^5*L^2*M := by
    have hp : 0 ≤ d*K^5*L^2*M := by positivity
    nlinarith only [hT,hbase,mul_nonneg hΓ hp,hp]
  have hreports : 1040*d*Γ*K^5*L^2*M ≤ 1040*d*(1+Γ)*K^5*L^2*M := by gcongr;linarith
  have hcoef : 0 ≤ (D+C)*(1+h) := by positivity
  calc
    _ ≤ (D+C)*(1+h)*(8000*d*(1+Γ)*K^5*L^2*M)+
        (D+C)*(1+h)*(1040*d*(1+Γ)*K^5*L^2*M)+10 := by
      exact add_le_add (add_le_add
        (mul_le_mul hDCh hcalls (by positivity) hcoef)
        (mul_le_mul hD20h hreports (by positivity) hcoef)) le_rfl
    _ ≤ _ := by
      have hp : 0 ≤ d*(D+C)*(1+h)*(1+Γ)*K^5*L^2*M := by positivity
      nlinarith only [hp]
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s434
section s435
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma coreLogOverhead_positive (m : ℕ) : 0 < coreLogOverhead m := by
  dsimp [coreLogOverhead]
  linarith only [log_size_positive m]
lemma coreLogOverhead_subpolynomial : Subpolynomial coreLogOverhead :=
  subpolynomial_add _ _ (subpolynomial_constant 1 (by norm_num)) subpolynomial_log_size
lemma core_A_near_linear (b : Core) : A b ≤ 65*coreLogOverhead b.input.size/b.input.accuracy := by
  have hm : (2 : ℝ) ≤ b.input.size := by exact_mod_cast b.two.trans b.valid.1
  have heps := b.valid.2.2.2.1
  have heps1 : b.input.accuracy ≤ 1 := b.epsilon_high.le
  have hlog2 : (1/2 : ℝ) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    linarith
  have hlog2' : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    exact hh
  have hl : Real.log ((b.input.size : ℝ)+1) ≤ coreLogOverhead b.input.size := by
    have hh := Real.log_le_log (by linarith : (0 : ℝ) < (b.input.size : ℝ)+1)
      (show (b.input.size : ℝ)+1 ≤ 2*b.input.size by linarith)
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by linarith : (b.input.size : ℝ) ≠ 0)] at hh
    dsimp [coreLogOverhead]
    rw [max_eq_right (show 2 ≤ b.input.size from b.two.trans b.valid.1)]
    linarith
  have hL := coreLogOverhead_positive b.input.size
  have hl2 : logarithm2 ((b.input.size : ℝ)+1) ≤ 2*coreLogOverhead b.input.size := by
    unfold logarithm2
    apply (div_le_iff₀ (by linarith : 0 < Real.log 2)).mpr
    nlinarith only [hl,mul_le_mul_of_nonneg_left hlog2 (show 0 ≤ 2*coreLogOverhead b.input.size by positivity)]
  have hx : 0 ≤ 32*logarithm2 ((b.input.size : ℝ)+1)/b.input.accuracy := by
    unfold logarithm2
    exact div_nonneg (mul_nonneg (by norm_num) (div_nonneg (Real.log_nonneg (by linarith)) (by linarith))) heps.le
  have hceil := (Nat.ceil_lt_add_one hx).le
  change (⌈32*logarithm2 ((b.input.size : ℝ)+1)/b.input.accuracy⌉₊ : ℝ) ≤ _
  apply hceil.trans
  apply (le_div_iff₀ heps).mpr
  have hL1 : 1 ≤ coreLogOverhead b.input.size := by
    dsimp [coreLogOverhead]
    linarith only [(log_size_positive b.input.size).le]
  have hmul := mul_le_mul_of_nonneg_right hl2 (by norm_num : (0 : ℝ) ≤ 32)
  have hxid : (32*logarithm2 ((b.input.size : ℝ)+1)/b.input.accuracy+1)*b.input.accuracy =
      32*logarithm2 ((b.input.size : ℝ)+1)+b.input.accuracy := by field_simp
  rw [hxid]
  nlinarith only [hmul,heps1,hL1]
lemma core_log_Q_near_linear (b : Core) : Real.log (2*Q b) ≤ (b.weightExponent+8 : ℕ)*coreLogOverhead b.input.size := by
  have hm : (2 : ℝ) ≤ b.input.size := by exact_mod_cast b.two.trans b.valid.1
  have hQ : 0 < Q b := by
    have hh := core_Q_ge b
    have hn : (2 : ℝ) ≤ b.input.n := by exact_mod_cast b.two
    linarith
  have hp : 2*Q b ≤ (b.input.size : ℝ)^(b.weightExponent+8) := by
    calc
      _ ≤ (b.input.size : ℝ)*(b.input.size : ℝ)^(b.weightExponent+7) := by gcongr;exact core_Q_polynomial b
      _ = _ := by rw [show b.weightExponent+8 = (b.weightExponent+7)+1 by omega,pow_succ];ring
  have hl := Real.log_le_log (mul_pos (by norm_num) hQ) hp
  rw [Real.log_pow] at hl
  have hlog : Real.log (b.input.size : ℝ) ≤ coreLogOverhead b.input.size := by
    dsimp [coreLogOverhead]
    rw [max_eq_right (show 2 ≤ b.input.size from b.two.trans b.valid.1)]
    linarith
  exact hl.trans (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _))
end DecrAlmostLinearSSSP.Decremental
end s435
section s436
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma coreRuntimeOverhead_subpolynomial (h Γ a : ℕ → ℝ) (N : ℕ)
    (hh : Subpolynomial h) (hΓ : Subpolynomial Γ) (ha : Subpolynomial a) :
    Subpolynomial (coreRuntimeOverhead h Γ a N) := by
  have hc := subpolynomial_constant 1 (by norm_num : (0 : ℝ) < 1)
  have hrh := subpolynomial_rescale h hh 2 (by omega)
  have hrΓ := subpolynomial_rescale Γ hΓ 2 (by omega)
  have hra := subpolynomial_rescale a ha 2 (by omega)
  have hrK := subpolynomial_rescale (computableCutQuality N) (computableCutQuality_subpolynomial N) 2 (by omega)
  exact subpolynomial_add _ _ (subpolynomial_add _ _ hc hra)
    (subpolynomial_mul _ _ (subpolynomial_mul _ _
      (subpolynomial_mul _ _ (subpolynomial_add _ _ hc hrh) (subpolynomial_add _ _ hc hrΓ))
      (subpolynomial_pow _ hrK 5)) (subpolynomial_pow _ coreLogOverhead_subpolynomial 2))
lemma coreRuntimeOverhead_init_bound (h Γ a : ℕ → ℝ) (N m : ℕ)
    (hh : 0 ≤ h (2*m)) (hΓ : 0 ≤ Γ (2*m)) (ha : 0 ≤ a (2*m)) :
    1+a (2*m) ≤ coreRuntimeOverhead h Γ a N m := by
  have hK := (computableCutQuality_subpolynomial N).1 (2*m)
  unfold coreRuntimeOverhead
  apply le_add_of_nonneg_right
  positivity
lemma coreRuntimeOverhead_dynamic_bound (h Γ a : ℕ → ℝ) (N m : ℕ)
    (ha : 0 ≤ a (2*m)) :
    (1+h (2*m))*(1+Γ (2*m))*(computableCutQuality N (2*m))^5*(coreLogOverhead m)^2 ≤
      coreRuntimeOverhead h Γ a N m := by
  unfold coreRuntimeOverhead
  linarith
end DecrAlmostLinearSSSP.Decremental
end s436
section s437
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma RuntimeInvariant.toggle_count_near_linear (b : Core) (K : ℝ) (hK : 0 < K)
    (s : State b) (hs : RuntimeInvariant b K s) :
    (s.toggles : ℝ) ≤ 1040*(b.weightExponent+8 : ℕ)*K^3*b.input.size*
      (coreLogOverhead b.input.size)^2/b.input.accuracy := by
  have hA := core_A_near_linear b
  have hQ := core_log_Q_near_linear b
  have hL := coreLogOverhead_positive b.input.size
  have heps := b.valid.2.2.2.1
  have hA0 : 0 ≤ A b := (core_A_ge b).trans' (by norm_num)
  have hQ0 : 0 ≤ Real.log (2*Q b) := by
    apply Real.log_nonneg
    have hh := core_Q_ge b
    have hn : (2 : ℝ) ≤ b.input.n := by exact_mod_cast b.two
    linarith
  calc
    (s.toggles : ℝ) ≤ 16*K^3*A b*b.input.size*Real.log (2*Q b) := hs.toggle_count b K hK s
    _ ≤ 16*K^3*(65*coreLogOverhead b.input.size/b.input.accuracy)*b.input.size*
        ((b.weightExponent+8 : ℕ)*coreLogOverhead b.input.size) := by gcongr <;> positivity
    _ = _ := by ring
end DecrAlmostLinearSSSP.Decremental
end s437
section s438
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
lemma scale_bounds (b : Core) (N : ℕ) (h Γ a : ℕ → ℝ)
    (hh : 0 ≤ h (2*b.input.size)) (hΓ : 0 ≤ Γ (2*b.input.size)) (ha : 0 ≤ a (2*b.input.size)) :
    let m : ℝ := b.input.size
    let M := m/b.input.accuracy
    let O := coreRuntimeOverhead h Γ a N b.input.size
    let K := computableCutQuality N (2*b.input.size)
    let L := coreLogOverhead b.input.size
    1 ≤ M ∧ m ≤ M ∧ 1 ≤ L ∧
      1 ≤ O ∧ a (2*b.input.size) ≤ O ∧
      (1+h (2*b.input.size))*(1+Γ (2*b.input.size))*K^5*L^2 ≤ O ∧
      L/b.input.accuracy ≤ O*M := by
  dsimp only
  let m : ℝ := b.input.size
  let M := m/b.input.accuracy
  let O := coreRuntimeOverhead h Γ a N b.input.size
  let K := computableCutQuality N (2*b.input.size)
  let L := coreLogOverhead b.input.size
  have hm : 2 ≤ m := by dsimp [m];exact_mod_cast b.two.trans b.valid.1
  have heps := b.valid.2.2.2.1
  have heps1 := b.epsilon_high.le
  have hM : m ≤ M := (le_div_iff₀ heps).mpr (by nlinarith)
  have hL : 1 ≤ L := by
    dsimp [L,coreLogOverhead]
    linarith only [(log_size_positive b.input.size).le]
  have hK : 1 ≤ K := by
    unfold K computableCutQuality
    exact one_le_pow₀ (by norm_num)
  have hF : (1+h (2*b.input.size))*(1+Γ (2*b.input.size))*K^5*L^2 ≤ O :=
    coreRuntimeOverhead_dynamic_bound h Γ a N b.input.size ha
  have hO : 1 ≤ O := by
    have ho := coreRuntimeOverhead_init_bound h Γ a N b.input.size hh hΓ ha
    linarith only [ho,ha]
  have haO : a (2*b.input.size) ≤ O := by
    have ho := coreRuntimeOverhead_init_bound h Γ a N b.input.size hh hΓ ha
    linarith only [ho]
  have hLO : L ≤ O := by
    have hK5 : 1 ≤ K^5 := one_le_pow₀ hK
    have hL2 : L ≤ L^2 := by nlinarith
    have hpair : 1 ≤ (1+h (2*b.input.size))*(1+Γ (2*b.input.size)) := by nlinarith
    have hprod : 1 ≤ (1+h (2*b.input.size))*(1+Γ (2*b.input.size))*K^5 := by nlinarith only [hpair,hK5,mul_nonneg (sub_nonneg.mpr hpair) (sub_nonneg.mpr hK5)]
    have hmul := mul_le_mul_of_nonneg_right hprod (show 0 ≤ L^2 by positivity)
    nlinarith only [hF,hL2,hmul]
  refine ⟨by linarith only [hm,hM],hM,hL,hO,haO,hF,?_⟩
  change L/b.input.accuracy ≤ O*(m/b.input.accuracy)
  rw [← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ heps.le
  have hOm := mul_le_mul_of_nonneg_left (show 1 ≤ m by linarith) (show 0 ≤ O by linarith)
  nlinarith only [hLO,hOm]
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s438
section s439
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
lemma Completed.work_bound {b : Core} {qualityPower : ℕ} (hpower : 5 ≤ qualityPower)
    {impl : CutImplementation} (K0 C : ℝ) (h Γ a : ℕ → ℝ) (hC : 0 ≤ C)
    (hh : 0 ≤ h (2*b.input.size)) (hΓ : 0 ≤ Γ (2*b.input.size)) (ha : 0 ≤ a (2*b.input.size))
    {ds : List (Fin b.input.k)} {c : Machine} (hlegal : Legal ds)
    (hc : Completed b qualityPower impl K0 (h (2*b.input.size)) (Γ (2*b.input.size))
      (C*(2*b.input.size)*a (2*b.input.size)) ds c) :
    ((c.work+6*ds.length : ℕ) : ℝ) ≤ coreConstant b.weightExponent qualityPower impl.program C*
      b.input.size*coreRuntimeOverhead h Γ a qualityPower b.input.size/b.input.accuracy := by
  obtain ⟨ready,hwork⟩ := hc
  let m : ℝ := b.input.size
  let M := m/b.input.accuracy
  let O := coreRuntimeOverhead h Γ a qualityPower b.input.size
  let K := computableCutQuality qualityPower (2*b.input.size)
  let L := coreLogOverhead b.input.size
  let N := CoreInitialize.sourceRegisters impl.program
  let D : ℝ := (dispatchCharge impl.program.code+2 : ℕ)
  let d : ℝ := (b.weightExponent+8 : ℕ)
  let T := 1040*d*K^3*L^2*M
  obtain ⟨hM,hmM,hL,hO,haO,hFO,hLM⟩ := scale_bounds b qualityPower h Γ a hh hΓ ha
  change 1 ≤ M at hM
  change m ≤ M at hmM
  change 1 ≤ L at hL
  change 1 ≤ O at hO
  change a (2*b.input.size) ≤ O at haO
  change (1+h (2*b.input.size))*(1+Γ (2*b.input.size))*K^5*L^2 ≤ O at hFO
  change L/b.input.accuracy ≤ O*M at hLM
  have hD : 0 ≤ D := by positivity
  have hd : 1 ≤ d := by dsimp [d];exact_mod_cast (show 1 ≤ b.weightExponent+8 by omega)
  have hK32 : 32 ≤ K := computableCutQuality_ge_32 qualityPower (2*b.input.size) hpower
  have hK : 1 ≤ K := by linarith
  have ht : (ready.state.toggles : ℝ) ≤ T := by
    have ht := ready.bounds.invariant.toggle_count_near_linear b K (by linarith) ready.state
    convert ht using 1 <;> dsimp [T,d,M,m,L] <;> ring
  have hlen : ds.length ≤ b.input.size := by
    have hk := List.Nodup.length_le_card hlegal
    simp only [Fintype.card_fin] at hk
    exact hk.trans b.valid.2.1
  have hoff : (6*ds.length : ℕ) ≤ (6:ℝ)*M := by
    have hn : (ds.length : ℝ) ≤ m := by dsimp [m];exact_mod_cast hlen
    push_cast
    linarith only [hn,hmM]
  have hcBound := ready.context.credit_bound ready.state (6*ds.length) T hh hΓ ht ready.debt ready.toggles
  change (ready.credit : ℝ) ≤ D*(C*(2*b.input.size)*a (2*b.input.size))+
    (D*h (2*b.input.size)+100*(N+1 : ℕ))*(5*(Γ (2*b.input.size)*K^2*T)+2*T+(6*ds.length : ℕ)+1)+
    (D*h (2*b.input.size)+20)*(Γ (2*b.input.size)*K^2*T)+10 at hcBound
  have harith := dynamic_budget_arithmetic D (100*((N+1 : ℕ) : ℝ)) d
    (h (2*b.input.size)) (Γ (2*b.input.size)) K L M hD (by exact_mod_cast (show 20 ≤ 100*(N+1) by omega)) hd hh hΓ hK hL hM
    ((6*ds.length : ℕ) : ℝ) (Nat.cast_nonneg _) hoff
  change _ ≤ 10000*d*(D+100*((N+1 : ℕ) : ℝ))*(1+h (2*b.input.size))*(1+Γ (2*b.input.size))*K^5*L^2*M+10 at harith
  have hdyn : (ready.credit : ℝ) ≤ D*(C*(2*b.input.size)*a (2*b.input.size))+
      10000*d*(D+100*((N+1 : ℕ) : ℝ))*O*M+10 := by
    have hp := mul_le_mul_of_nonneg_left hFO (show 0 ≤ 10000*d*(D+100*((N+1 : ℕ) : ℝ)) by positivity)
    have hpM := mul_le_mul_of_nonneg_right hp (show 0 ≤ M by linarith)
    nlinarith only [hcBound,harith,hpM]
  have hA : (⌈32*logarithm2 (b.input.size+1)/b.input.accuracy⌉₊ : ℝ) ≤ 65*L/b.input.accuracy := core_A_near_linear b
  have hAO : (⌈32*logarithm2 (b.input.size+1)/b.input.accuracy⌉₊ : ℝ) ≤ 65*(O*M) := by
    calc
      _ ≤ 65*L/b.input.accuracy := hA
      _ = 65*(L/b.input.accuracy) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hLM (by norm_num)
  have hOM : 1 ≤ O*M := by nlinarith only [hO,hM,mul_nonneg (sub_nonneg.mpr hO) (sub_nonneg.mpr hM)]
  have hmOM : m ≤ O*M := by
    have hp := mul_le_mul_of_nonneg_right hO (show 0 ≤ M by linarith)
    nlinarith only [hmM,hp]
  have hi : 2*D*(C*(2*b.input.size)*a (2*b.input.size)) ≤ 4*D*C*(O*M) := by
    have hma := mul_le_mul hmM haO ha (show 0 ≤ M by linarith)
    have hp := mul_le_mul_of_nonneg_left hma (show 0 ≤ 4*D*C by positivity)
    dsimp [m] at hp
    push_cast at hp ⊢
    nlinarith only [hp]
  have hboot : (initialBudget b qualityPower impl.program (C*(2*b.input.size)*a (2*b.input.size)))+10 ≤
      (80000*(qualityPower+1)+265+14*N+400 : ℕ)*(O*M)+D*(C*(2*b.input.size)*a (2*b.input.size)) := by
    unfold initialBudget
    have hDval : (dispatchCharge impl.program.code : ℝ)+2 = D := by simp [D]
    rw [hDval]
    change ((80000*(qualityPower+1)+265)*b.input.size+4*⌈32*logarithm2 (b.input.size+1)/b.input.accuracy⌉₊+14*N+120 : ℕ)+
      D*(C*(2*b.input.size)*a (2*b.input.size))+8+10 ≤ _
    push_cast
    have hp := mul_le_mul_of_nonneg_left hmOM (show 0 ≤ ((80000*(qualityPower+1)+265 : ℕ) : ℝ) by positivity)
    have hn := mul_le_mul_of_nonneg_left hOM (show (0:ℝ) ≤ 14*(N:ℝ)+140 by exact add_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (by norm_num))
    push_cast at hp
    dsimp [m] at hp
    nlinarith only [hAO,hp,hn,hOM]
  have hsum := add_le_add hwork (show (10:ℝ) ≤ 10 by rfl)
  dsimp [coreConstant]
  change _ ≤ (((80000*(qualityPower+1)+265+14*N+400 : ℕ) : ℝ)+4*D*C+
    10000*d*(D+100*((N+1 : ℕ) : ℝ)))*m*O/b.input.accuracy
  have hid : (((80000*(qualityPower+1)+265+14*N+400 : ℕ) : ℝ)+4*D*C+
    10000*d*(D+100*((N+1 : ℕ) : ℝ)))*m*O/b.input.accuracy =
    (((80000*(qualityPower+1)+265+14*N+400 : ℕ) : ℝ)+4*D*C+
    10000*d*(D+100*((N+1 : ℕ) : ℝ)))*(O*M) := by dsimp [M];ring
  rw [hid]
  nlinarith only [hwork,hdyn,hboot,hi]
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s439
section s440
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma cutRoot_quality_exponent (C : ℝ) (hC : 0 ≤ C) (m : ℕ) :
    C*(Real.log (max 2 m : ℕ))^(5/6 : ℝ)*max 1 (Real.log (Real.log (max 2 m : ℕ))) ≤
      12*C*(cutRoot m : ℝ)^11 := by
  have hr : (2 : ℝ) ≤ cutRoot m := by exact_mod_cast cutRoot_ge_two m
  have hr0 : (0 : ℝ) ≤ cutRoot m := by linarith
  have hrpos : (0 : ℝ) < cutRoot m := by linarith
  have hlog := log_size_positive m
  have hlogroot : Real.log (max 2 m : ℕ) ≤ (cutRoot m : ℝ)^12 := by
    have hh : (cutLogHeight m : ℝ) ≤ (cutRoot m : ℝ)^12 := by exact_mod_cast (cutRoot_power_lower m).le
    exact (cutLogHeight_log_upper m).trans hh
  have hpow : (Real.log (max 2 m : ℕ))^(5/6 : ℝ) ≤ (cutRoot m : ℝ)^10 := by
    have hh := Real.rpow_le_rpow hlog.le hlogroot (by norm_num : (0 : ℝ) ≤ 5/6)
    have hid := Real.rpow_mul hr0 (12 : ℝ) (5/6 : ℝ)
    norm_num only [show (12 : ℝ)*(5/6)=10 by norm_num,Real.rpow_natCast,Real.rpow_ofNat] at hid
    rwa [← hid] at hh
  have hloglog : Real.log (Real.log (max 2 m : ℕ)) ≤ 12*(cutRoot m : ℝ) := by
    have hh := Real.log_le_log hlog hlogroot
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    have hl := Real.log_le_sub_one_of_pos hrpos
    linarith only [hh,hl]
  have hmax : max 1 (Real.log (Real.log (max 2 m : ℕ))) ≤ 12*(cutRoot m : ℝ) :=
    max_le (by linarith) hloglog
  calc
    _ ≤ C*(cutRoot m : ℝ)^10*(12*(cutRoot m : ℝ)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hpow hC) hmax
        ((by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)) (mul_nonneg hC (pow_nonneg hr0 _))
    _ = _ := by ring
lemma exists_computable_cut_quality_envelope (C : ℝ) (hC : 0 ≤ C) :
    ∃ N : ℕ, 5 ≤ N ∧ ∀ m : ℕ,
      (2 : ℝ)^(C*(Real.log (max 2 m : ℕ))^(5/6 : ℝ)*max 1 (Real.log (Real.log (max 2 m : ℕ)))) ≤
        computableCutQuality N m := by
  obtain ⟨n,hn⟩ := exists_nat_gt (12*C)
  let N := max 5 n
  have hN : (12*C : ℝ) ≤ N := hn.le.trans (by exact_mod_cast le_max_right 5 n)
  refine ⟨N,le_max_left _ _,?_⟩
  intro m
  have hh := (cutRoot_quality_exponent C hC m).trans
    (mul_le_mul_of_nonneg_right hN (pow_nonneg (Nat.cast_nonneg _) _))
  have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hh
  have heq : ((N*(cutRoot m)^11 : ℕ) : ℝ) = (N : ℝ)*(cutRoot m : ℝ)^11 := by push_cast;rfl
  rw [← heq,Real.rpow_natCast] at hp
  exact hp
end DecrAlmostLinearSSSP.Decremental
end s440
section s441
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
lemma maintains (b : Core) (qualityPower : ℕ) (hpower : 5 ≤ qualityPower)
    (impl : CutImplementation) (K0 C : ℝ) (h Γ a : ℕ → ℝ) (hC : 0 ≤ C)
    (hh : 0 ≤ h (2*b.input.size)) (hΓ : 0 ≤ Γ (2*b.input.size)) (ha : 0 ≤ a (2*b.input.size))
    (hK0 : 0 < K0) (hKK : K0 ≤ computableCutQuality qualityPower (2*b.input.size))
    (himpl : ImplementsCut impl (2*b.input.size) (4*b.weightExponent+68) K0
      (h (2*b.input.size)) (Γ (2*b.input.size)) (C*(2*b.input.size)*a (2*b.input.size))
      ((computableCutQuality qualityPower (2*b.input.size))^(-2 : ℤ))) :
    Maintains (coreProgram qualityPower impl.program) (coreConstant b.weightExponent qualityPower impl.program C)
      (coreRuntimeOverhead h Γ a qualityPower) 9 false b.input := by
  intro ds hlegal
  obtain ⟨cs,last,hr,hlen,hlast,hcompleted,hprefix⟩ :=
    online b qualityPower hpower impl K0 _ _ _ hK0 hKK himpl ds
  refine ⟨cs,hr,hlen,?_,?_,?_⟩
  · intro j c hc
    exact (hprefix j c hc).correct
  · intro c hc
    have heq : last = c := Option.some.inj (hlast.symm.trans hc)
    subst c
    simpa only [Bool.false_eq_true,if_false,mul_one] using
      hcompleted.work_bound hpower K0 C h Γ a hC hh hΓ ha hlegal
  · intro c hc v
    exact coreProgram_query qualityPower impl.program c v.val
lemma coreConstant_positive (d N : ℕ) (p : Program) (C : ℝ) (hC : 0 ≤ C) :
    0 < coreConstant d N p C := by
  unfold coreConstant
  positivity
lemma normalized_core_from_cut (d : ℕ)
    (hcut : ∃ (impl : CutImplementation) (K h Γ a : ℕ → ℝ) (C : ℝ),
      0 < C ∧ Subpolynomial K ∧ Subpolynomial h ∧ Subpolynomial Γ ∧ Subpolynomial a ∧
      (∀ m, 32 ≤ K m ∧ K m ≤ Real.rpow 2
        (C * Real.rpow (Real.log (max 2 m : ℕ)) (5 / 6 : ℝ) *
          max 1 (Real.log (Real.log (max 2 m : ℕ))))) ∧
      ∀ m ξ, 0 < ξ → ImplementsCut impl m (4*d+68) (K m) (h m) (Γ m) (C*m*a m) ξ) :
    ∃ (p : Program) (C : ℝ) (a : ℕ → ℝ), 0 < C ∧ Subpolynomial a ∧
      ∀ b : Core, b.weightExponent = d → Maintains p C a 9 false b.input := by
  obtain ⟨impl,K,h,Γ,a,C,hC,hK,hh,hΓ,ha,hquality,himpl⟩ := hcut
  obtain ⟨N,hN,henv⟩ := exists_computable_cut_quality_envelope C hC.le
  refine ⟨coreProgram N impl.program,coreConstant d N impl.program C,coreRuntimeOverhead h Γ a N,
    coreConstant_positive d N impl.program C hC.le,coreRuntimeOverhead_subpolynomial h Γ a N hh hΓ ha,?_⟩
  intro b hd
  have hKK : K (2*b.input.size) ≤ computableCutQuality N (2*b.input.size) :=
    (hquality _).2.trans (henv _)
  have hxi : 0 < (computableCutQuality N (2*b.input.size))^(-2 : ℤ) := by
    have h32 := computableCutQuality_ge_32 N (2*b.input.size) hN
    positivity
  have hi := himpl (2*b.input.size) _ hxi
  rw [← hd] at hi
  have hm := maintains b N hN impl (K (2*b.input.size)) C h Γ a hC.le
    (hh.1 _).le (hΓ.1 _).le (ha.1 _).le (hK.1 _) hKK (by simpa only [Nat.cast_mul,Nat.cast_ofNat] using hi)
  rwa [hd] at hm
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s441
section s442
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma polynomial_from_normalized_core (d : ℕ)
    (hcore : ∃ (p : Program) (C : ℝ) (a : ℕ → ℝ), 0 < C ∧ Subpolynomial a ∧
      ∀ b : Core, b.weightExponent = d+3 → Maintains p C a 9 false b.input) :
    ∃ (p : Program) (C : ℝ) (a : ℕ → ℝ) (queryBound : ℕ),
      0 < C ∧ 0 < queryBound ∧ Subpolynomial a ∧
      (∀ i : Input, i.Valid → 2 ≤ i.n → i.W ≤ i.size^d →
        1/(i.size : ℝ) < i.accuracy → i.accuracy < 1 → Maintains p C a queryBound false i) ∧
      (∀ (b : Core) (K : ℝ), 32 ≤ K → ∀ choose : State b → CutReply b,
        CutQuality b K choose → ∀ s, Attained b K choose s →
        (s.toggles : ℝ) ≤ 16*K^3*A b*b.input.size*Real.log (2*Q b)) := by
  obtain ⟨p,C,a,hC,ha,hcore⟩ := hcore
  refine ⟨Normalize.Native.program p,4*(Normalize.Native.dispatchCost p : ℝ)*C+200,
    Normalize.Native.overhead a,9,by positivity,by omega,Normalize.Native.overhead_subpolynomial a ha,?_,?_⟩
  · intro i hi hn hW heps heps1
    let b := Normalize.core i hi hn d hW heps heps1
    have hsource := hcore b rfl
    change Maintains p C a 9 false (Normalize.input i) at hsource
    exact Normalize.Native.maintains i hi hn p C a 9 hC.le ha hsource
  · exact attained_toggle_count
end DecrAlmostLinearSSSP.Decremental
end s442
theorem solution : (((((((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 694) (instOfNatNat (nat_lit 694))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreGuestGamma.code k) ∧ (∀ (k : Nat),
  Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
      (Or (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 690) (instOfNatNat (nat_lit 690))))
        (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 692) (instOfNatNat (nat_lit 692))) k)) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.edgeBody k)) ∧ ((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 600) (instOfNatNat (nat_lit 600))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 602) (instOfNatNat (nat_lit 602))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 604) (instOfNatNat (nat_lit 604))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 606) (instOfNatNat (nat_lit 606))) →
          DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.edgeBody
            k) ∧ (∀ (k : Nat),
  Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
      (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 692) (instOfNatNat (nat_lit 692))) k) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.code k))) ∧ (((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 600) (instOfNatNat (nat_lit 600))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 602) (instOfNatNat (nat_lit 602))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 604) (instOfNatNat (nat_lit 604))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 606) (instOfNatNat (nat_lit 606))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 694) (instOfNatNat (nat_lit 694))) →
            DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.code k) ∧ (@Eq.{1} Bool
  (DecrAlmostLinearSSSP.Decremental.Structured.evenRegisters DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.code)
  Bool.true)) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (d : Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreGeometry.Image b B state s →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))) B →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 552) (instOfNatNat (nat_lit 552))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@Fin.val (DecrAlmostLinearSSSP.Decremental.logicalCount b) d)) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 690) (instOfNatNat (nat_lit 690))))
                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
              ∃ t,
                And
                  (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                    DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.edgeBody s
                    (@OfNat.ofNat.{0} Nat (nat_lit 33) (instOfNatNat (nat_lit 33))) t)
                  (And (DecrAlmostLinearSSSP.Decremental.CoreGeometry.Image b B state t)
                    (And
                      (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@Fin.val (DecrAlmostLinearSSSP.Decremental.logicalCount b) d)
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                      (And
                        (@Eq.{1} Nat
                          (t.natMem
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))
                                  (@Fin.val (DecrAlmostLinearSSSP.Decremental.logicalCount b) d)))
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                            (@Fin.val b.input.n
                              (DecrAlmostLinearSSSP.Decremental.tail b
                                (@DFunLike.coe.{1, 1, 1}
                                  (Equiv.{1, 1} (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                    (DecrAlmostLinearSSSP.Decremental.Edge b))
                                  (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                  (fun x => DecrAlmostLinearSSSP.Decremental.Edge b)
                                  (@EquivLike.toFunLike.{1, 1, 1}
                                    (Equiv.{1, 1} (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                      (DecrAlmostLinearSSSP.Decremental.Edge b))
                                    (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                    (DecrAlmostLinearSSSP.Decremental.Edge b)
                                    (@Equiv.instEquivLike.{1, 1} (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                      (DecrAlmostLinearSSSP.Decremental.Edge b)))
                                  (@Equiv.symm.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
                                    (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                    (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b))
                                  d)))))
                        (And
                          (@Eq.{1} Nat
                            (t.natMem
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))
                                    (@Fin.val (DecrAlmostLinearSSSP.Decremental.logicalCount b) d)))
                                (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                              (@Fin.val b.input.n
                                (DecrAlmostLinearSSSP.Decremental.head b
                                  (@DFunLike.coe.{1, 1, 1}
                                    (Equiv.{1, 1} (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                      (DecrAlmostLinearSSSP.Decremental.Edge b))
                                    (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                    (fun x => DecrAlmostLinearSSSP.Decremental.Edge b)
                                    (@EquivLike.toFunLike.{1, 1, 1}
                                      (Equiv.{1, 1} (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                        (DecrAlmostLinearSSSP.Decremental.Edge b))
                                      (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                      (DecrAlmostLinearSSSP.Decremental.Edge b)
                                      (@Equiv.instEquivLike.{1, 1}
                                        (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                        (DecrAlmostLinearSSSP.Decremental.Edge b)))
                                    (@Equiv.symm.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
                                      (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                      (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b))
                                    d)))))
                          (And
                            (@Eq.{1} Nat
                              (t.natMem
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))
                                      (@Fin.val (DecrAlmostLinearSSSP.Decremental.logicalCount b) d)))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))))
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (And
                              (@Eq.{1} Real
                                (t.realMem
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                        (@Fin.val (DecrAlmostLinearSSSP.Decremental.logicalCount b) d)))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                (@DecrAlmostLinearSSSP.Decremental.State.cache b state
                                  (@DFunLike.coe.{1, 1, 1}
                                    (Equiv.{1, 1} (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                      (DecrAlmostLinearSSSP.Decremental.Edge b))
                                    (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                    (fun x => DecrAlmostLinearSSSP.Decremental.Edge b)
                                    (@EquivLike.toFunLike.{1, 1, 1}
                                      (Equiv.{1, 1} (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                        (DecrAlmostLinearSSSP.Decremental.Edge b))
                                      (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                      (DecrAlmostLinearSSSP.Decremental.Edge b)
                                      (@Equiv.instEquivLike.{1, 1}
                                        (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                        (DecrAlmostLinearSSSP.Decremental.Edge b)))
                                    (@Equiv.symm.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
                                      (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                      (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b))
                                    d)))
                              (And
                                (∀ (j : Nat),
                                  @Ne.{1} Nat j
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))
                                            (@Fin.val (DecrAlmostLinearSSSP.Decremental.logicalCount b) d)))
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
                                    @Ne.{1} Nat j
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))
                                              (@Fin.val (DecrAlmostLinearSSSP.Decremental.logicalCount b) d)))
                                          (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))) →
                                      @Ne.{1} Nat j
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))
                                                (@Fin.val (DecrAlmostLinearSSSP.Decremental.logicalCount b) d)))
                                            (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))) →
                                        @Eq.{1} Nat (t.natMem j) (s.natMem j))
                                (∀ (j : Nat),
                                  @Ne.{1} Nat j
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                            (@Fin.val (DecrAlmostLinearSSSP.Decremental.logicalCount b) d)))
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
                                    @Eq.{1} Real (t.realMem j) (s.realMem j)))))))))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (state : DecrAlmostLinearSSSP.Decremental.State b) (upto : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.EdgeInvariant b B state upto s →
    @LT.lt.{0} Nat instLTNat upto (DecrAlmostLinearSSSP.Decremental.logicalCount b) →
      ∃ t,
        And
          (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.edgeBody s
            (@OfNat.ofNat.{0} Nat (nat_lit 33) (instOfNatNat (nat_lit 33))) t)
          (And
            (DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.EdgeInvariant b B state
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) upto
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              t)
            (And
              (∀ (j : Nat),
                (∀ (i : Nat),
                    @LT.lt.{0} Nat instLTNat i (DecrAlmostLinearSSSP.Decremental.logicalCount b) →
                      ∀ (offset : Nat),
                        @LT.lt.{0} Nat instLTNat offset (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                          @Ne.{1} Nat j
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) i))
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) offset))
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
                  @Eq.{1} Nat (t.natMem j) (s.natMem j))
              (∀ (j : Nat),
                (∀ (i : Nat),
                    @LT.lt.{0} Nat instLTNat i (DecrAlmostLinearSSSP.Decremental.logicalCount b) →
                      @Ne.{1} Nat j
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) i))
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
                  @Eq.{1} Real (t.realMem j) (s.realMem j)))))))) ∧ ((((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (state : DecrAlmostLinearSSSP.Decremental.State b) (upto : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.EdgeInvariant b B state upto s →
    ∃ t,
      And
        (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.edgeLoop s
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 35) (instOfNatNat (nat_lit 35)))
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                (DecrAlmostLinearSSSP.Decremental.logicalCount b) upto))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          t)
        (And
          (DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.EdgeInvariant b B state
            (DecrAlmostLinearSSSP.Decremental.logicalCount b) t)
          (And
            (∀ (j : Nat),
              (∀ (i : Nat),
                  @LT.lt.{0} Nat instLTNat i (DecrAlmostLinearSSSP.Decremental.logicalCount b) →
                    ∀ (offset : Nat),
                      @LT.lt.{0} Nat instLTNat offset (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                        @Ne.{1} Nat j
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) i))
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) offset))
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
                @Eq.{1} Nat (t.natMem j) (s.natMem j))
            (∀ (j : Nat),
              (∀ (i : Nat),
                  @LT.lt.{0} Nat instLTNat i (DecrAlmostLinearSSSP.Decremental.logicalCount b) →
                    @Ne.{1} Nat j
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) i))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
                @Eq.{1} Real (t.realMem j) (s.realMem j))))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.edgeStart s
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    (DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.edgesStarted s))) ∧ ((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 690) (instOfNatNat (nat_lit 690))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.edgeStart k) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreGeometry.Image b B state s →
    @DecrAlmostLinearSSSP.Decremental.CoreGradient.Image b.input.n
        (DecrAlmostLinearSSSP.Decremental.CoreMemory.gradientBase b B)
        (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b state) s →
      DecrAlmostLinearSSSP.Decremental.InputCapture.Captured b.input s →
        DecrAlmostLinearSSSP.Decremental.CoreControl.Layout b B s →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))) B →
            (∀ (j : Nat),
                And
                  (@Eq.{1} Nat
                    (s.natMem
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) j))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (@Eq.{1} Real
                    (s.realMem
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) j))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))) →
              DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.EdgeInvariant b B state
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.edgesStarted s)))) ∧ (((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreGeometry.Image b B state s →
    @DecrAlmostLinearSSSP.Decremental.CoreGradient.Image b.input.n
        (DecrAlmostLinearSSSP.Decremental.CoreMemory.gradientBase b B)
        (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b state) s →
      DecrAlmostLinearSSSP.Decremental.InputCapture.Captured b.input s →
        DecrAlmostLinearSSSP.Decremental.CoreControl.Layout b B s →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))) B →
            (∀ (j : Nat),
                And
                  (@Eq.{1} Nat
                    (s.natMem
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) j))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (@Eq.{1} Real
                    (s.realMem
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) j))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))) →
              ∃ t,
                And
                  (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                    (DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.edgeStart.seq
                      DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.edgeLoop)
                    s
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 35) (instOfNatNat (nat_lit 35)))
                        (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                    t)
                  (And
                    (DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.EdgeInvariant b B state
                      (DecrAlmostLinearSSSP.Decremental.logicalCount b) t)
                    (And
                      (∀ (j : Nat),
                        (∀ (i : Nat),
                            @LT.lt.{0} Nat instLTNat i (DecrAlmostLinearSSSP.Decremental.logicalCount b) →
                              ∀ (offset : Nat),
                                @LT.lt.{0} Nat instLTNat offset
                                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                                  @Ne.{1} Nat j
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) i))
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) offset))
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
                          @Eq.{1} Nat (t.natMem j) (s.natMem j))
                      (∀ (j : Nat),
                        (∀ (i : Nat),
                            @LT.lt.{0} Nat instLTNat i (DecrAlmostLinearSSSP.Decremental.logicalCount b) →
                              @Ne.{1} Nat j
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) i))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
                          @Eq.{1} Real (t.realMem j) (s.realMem j))))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (state : DecrAlmostLinearSSSP.Decremental.State b) (upto : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.GammaInvariant b B state upto s →
    @LT.lt.{0} Nat instLTNat upto b.input.n →
      ∃ t,
        And
          (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreGuestGamma.code s
            (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) t)
          (And
            (DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.GammaInvariant b B state
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) upto
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              t)
            (And (@Eq.{1} (Nat → Nat) t.natMem s.natMem)
              (∀ (j : Nat),
                (∀ (v : Nat),
                    @LT.lt.{0} Nat instLTNat v b.input.n →
                      @Ne.{1} Nat j
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (DecrAlmostLinearSSSP.Decremental.logicalCount b) v)))
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
                  @Eq.{1} Real (t.realMem j) (s.realMem j)))))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (state : DecrAlmostLinearSSSP.Decremental.State b) (upto : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.GammaInvariant b B state upto s →
    ∃ t,
      And
        (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.gammaLoop s
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) b.input.n upto))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          t)
        (And (DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.GammaInvariant b B state b.input.n t)
          (And (@Eq.{1} (Nat → Nat) t.natMem s.natMem)
            (∀ (j : Nat),
              (∀ (v : Nat),
                  @LT.lt.{0} Nat instLTNat v b.input.n →
                    @Ne.{1} Nat j
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (DecrAlmostLinearSSSP.Decremental.logicalCount b) v)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
                @Eq.{1} Real (t.realMem j) (s.realMem j))))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.EdgeInvariant b B state
      (DecrAlmostLinearSSSP.Decremental.logicalCount b) s →
    DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.GammaInvariant b B state
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      { realReg := s.realReg,
        natReg :=
          @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626)))
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))),
        realMem := s.realMem, natMem := s.natMem }) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.EdgeInvariant b B state
      (DecrAlmostLinearSSSP.Decremental.logicalCount b) s →
    ∃ t,
      And
        (DecrAlmostLinearSSSP.Decremental.Structured.Eval
          ((DecrAlmostLinearSSSP.Decremental.Structured.natural
                (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626)))
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).seq
            DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.gammaLoop)
          s
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11))) b.input.n)
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          t)
        (And (DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.GammaInvariant b B state b.input.n t)
          (And (@Eq.{1} (Nat → Nat) t.natMem s.natMem)
            (∀ (j : Nat),
              (∀ (v : Nat),
                  @LT.lt.{0} Nat instLTNat v b.input.n →
                    @Ne.{1} Nat j
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (DecrAlmostLinearSSSP.Decremental.logicalCount b) v)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
                @Eq.{1} Real (t.realMem j) (s.realMem j)))))))))) ∧ (((((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.GammaInvariant b B state b.input.n s →
    ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (m : Nat) (ξ cap : Real) (j : Nat),
      @Eq.{1} Nat
        (s.natMem
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          ((@DecrAlmostLinearSSSP.Decremental.cutInitial b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b) p
                (@DecrAlmostLinearSSSP.Decremental.indexedPhysical b state
                  (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                  (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b))
                m ξ cap).natMem
            j))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.GammaInvariant b B state b.input.n s →
    ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (m : Nat) (ξ cap : Real) (j : Nat),
      @Eq.{1} Real
        (s.realMem
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
        ((@DecrAlmostLinearSSSP.Decremental.cutInitial b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b) p
              (@DecrAlmostLinearSSSP.Decremental.indexedPhysical b state
                (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b))
              m ξ cap).realMem
          j))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreGeometry.Image b B state s →
    @DecrAlmostLinearSSSP.Decremental.CoreGradient.Image b.input.n
        (DecrAlmostLinearSSSP.Decremental.CoreMemory.gradientBase b B)
        (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b state) s →
      DecrAlmostLinearSSSP.Decremental.InputCapture.Captured b.input s →
        DecrAlmostLinearSSSP.Decremental.CoreControl.Layout b B s →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))) B →
            (∀ (j : Nat),
                And
                  (@Eq.{1} Nat
                    (s.natMem
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) j))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (@Eq.{1} Real
                    (s.realMem
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) j))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))) →
              ∃ cost t,
                And
                  (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.code
                    s cost t)
                  (And
                    (@LE.le.{0} Nat instLENat cost
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 85) (instOfNatNat (nat_lit 85))) b.input.size))
                    (And (DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.GammaInvariant b B state b.input.n t)
                      (And
                        (∀ (j : Nat),
                          (∀ (i : Nat),
                              @LT.lt.{0} Nat instLTNat i (DecrAlmostLinearSSSP.Decremental.logicalCount b) →
                                ∀ (offset : Nat),
                                  @LT.lt.{0} Nat instLTNat offset
                                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                                    @Ne.{1} Nat j
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) i))
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) offset))
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
                            @Eq.{1} Nat (t.natMem j) (s.natMem j))
                        (∀ (j : Nat),
                          (∀ (i : Nat),
                              @LT.lt.{0} Nat instLTNat i (DecrAlmostLinearSSSP.Decremental.logicalCount b) →
                                @Ne.{1} Nat j
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) i))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
                            (∀ (v : Nat),
                                @LT.lt.{0} Nat instLTNat v b.input.n →
                                  @Ne.{1} Nat j
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (DecrAlmostLinearSSSP.Decremental.logicalCount b) v)))
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
                              @Eq.{1} Real (t.realMem j) (s.realMem j)))))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreInitialSaved.fieldCode s
    (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))
    (DecrAlmostLinearSSSP.Decremental.CoreInitialSaved.fieldResult s)))) ∧ (((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
      And
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.CoreInitialSaved.fieldResult s).natMem
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50)))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 66) (instOfNatNat (nat_lit 66))))))
        (And
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.CoreInitialSaved.fieldResult s).natMem
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 536) (instOfNatNat (nat_lit 536))))))
          (And
            (@Eq.{1} Nat
              ((DecrAlmostLinearSSSP.Decremental.CoreInitialSaved.fieldResult s).natMem
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 540) (instOfNatNat (nat_lit 540))))))
            (And
              (@Eq.{1} Real
                ((DecrAlmostLinearSSSP.Decremental.CoreInitialSaved.fieldResult s).realMem
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50)))))
                (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 510) (instOfNatNat (nat_lit 510)))))
              (@Eq.{1} Real
                ((DecrAlmostLinearSSSP.Decremental.CoreInitialSaved.fieldResult s).realMem
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 508) (instOfNatNat (nat_lit 508))))))))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
      @Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.CoreInitialSaved.fieldResult s).realMem
        (@Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat
          (@Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realMem
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
            (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 510) (instOfNatNat (nat_lit 510)))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 508) (instOfNatNat (nat_lit 508))))))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
      ∀ (j : Nat),
        @Ne.{1} Nat j (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50)))) →
          @Ne.{1} Nat j
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
            @Ne.{1} Nat j
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) →
              And
                (@Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.CoreInitialSaved.fieldResult s).natMem j) (s.natMem j))
                (@Eq.{1} Real ((DecrAlmostLinearSSSP.Decremental.CoreInitialSaved.fieldResult s).realMem j)
                  (s.realMem j))) ∧ ((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 670) (instOfNatNat (nat_lit 670))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 672) (instOfNatNat (nat_lit 672))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 674) (instOfNatNat (nat_lit 674))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
            DecrAlmostLinearSSSP.Decremental.CoreInitialSaved.fieldCode k) ∧ (∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreInitialSaved.fieldCode k))))) ∧ ((((∀ {n l : Nat} (p : DecrAlmostLinearSSSP.Decremental.Program) (graph : DecrAlmostLinearSSSP.Decremental.Physical n l)
  (m N : Nat) (ξ cap : Real) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 66) (instOfNatNat (nat_lit 66)))) n →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 536) (instOfNatNat (nat_lit 536)))) l →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 540) (instOfNatNat (nat_lit 540)))) m →
            @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 510) (instOfNatNat (nat_lit 510)))) ξ →
              @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 508) (instOfNatNat (nat_lit 508)))) cap →
                (∀ (j : Nat),
                    @LT.lt.{0} Nat instLTNat j N →
                      And
                        (@Eq.{1} Nat
                          (s.natMem
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                        (@Eq.{1} Real
                          (s.realMem
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
                          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))) →
                  DecrAlmostLinearSSSP.Decremental.CoreRequest.SavedImage N
                    (@DecrAlmostLinearSSSP.Decremental.cutInitial n l p graph m ξ cap)
                    (DecrAlmostLinearSSSP.Decremental.CoreInitialSaved.fieldResult s)) ∧ (∀ (N k : Nat),
  Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 116) (instOfNatNat (nat_lit 116))))
      (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 124) (instOfNatNat (nat_lit 124))) k) →
    Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))))
        (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 674) (instOfNatNat (nat_lit 674))) k) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.CoreInitialSaved.code N) k)) ∧ ((∀ (N k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 116) (instOfNatNat (nat_lit 116))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.CoreInitialSaved.code N) k) ∧ (∀ {n l : Nat} (p : DecrAlmostLinearSSSP.Decremental.Program) (graph : DecrAlmostLinearSSSP.Decremental.Physical n l)
  (m N : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) N →
    ∀ (ξ cap : Real) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 66) (instOfNatNat (nat_lit 66)))) n →
              @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 536) (instOfNatNat (nat_lit 536)))) l →
                @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 540) (instOfNatNat (nat_lit 540)))) m →
                  @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 510) (instOfNatNat (nat_lit 510)))) ξ →
                    @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 508) (instOfNatNat (nat_lit 508)))) cap →
                      ∃ t,
                        And
                          (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                            (DecrAlmostLinearSSSP.Decremental.CoreInitialSaved.code N) s
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) N)
                              (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19))))
                            t)
                          (And
                            (DecrAlmostLinearSSSP.Decremental.CoreRequest.SavedImage N
                              (@DecrAlmostLinearSSSP.Decremental.cutInitial n l p graph m ξ cap) t)
                            (∀ (address : Nat),
                              (∀ (j : Nat),
                                  @LT.lt.{0} Nat instLTNat j N →
                                    @Ne.{1} Nat address
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j))) →
                                And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                  (@Eq.{1} Real (t.realMem address) (s.realMem address))))))) ∧ (((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B N : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.GammaInvariant b B state b.input.n s →
    DecrAlmostLinearSSSP.Decremental.CoreParameters.Values b K s →
      ∀ (p : DecrAlmostLinearSSSP.Decremental.Program),
        @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) N →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
            @Eq.{1} Nat
                (s.natMem
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B)
                    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
              (∀ (j : Nat),
                  @LE.le.{0} Nat instLENat N j →
                    And
                      (@Eq.{1} Nat (s.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg j))
                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                      (@Eq.{1} Real (s.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg j))
                        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))) →
                ∃ t,
                  And
                    (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                      (DecrAlmostLinearSSSP.Decremental.CoreInitialSaved.code N) s
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) N)
                        (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19))))
                      t)
                    (And
                      (DecrAlmostLinearSSSP.Decremental.CoreSource.Image B
                        (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N
                        (@DecrAlmostLinearSSSP.Decremental.cutInitial b.input.n
                          (DecrAlmostLinearSSSP.Decremental.logicalCount b) p
                          (@DecrAlmostLinearSSSP.Decremental.indexedPhysical b state
                            (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                            (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b))
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                          (@HPow.hPow.{0, 0, 0} Real Int Real
                            (@instHPow.{0, 0} Real Int
                              (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                            K
                            (@Neg.neg.{0} Int Int.instNegInt
                              (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                          (@HPow.hPow.{0, 0, 0} Real Int Real
                            (@instHPow.{0, 0} Real Int
                              (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                            (DecrAlmostLinearSSSP.Decremental.kappa b)
                            (@Neg.neg.{0} Int Int.instNegInt
                              (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))))))
                        t)
                      (∀ (address : Nat),
                        @LT.lt.{0} Nat instLTNat address
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B)
                              (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) →
                          And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                            (@Eq.{1} Real (t.realMem address) (s.realMem address))))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (s t : DecrAlmostLinearSSSP.Decremental.Structured.Data) (cost : Nat),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    @LE.le.{0} Nat instLENat b.input.n B →
      DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.code s cost t →
        (∀ (j : Nat),
            (∀ (i : Nat),
                @LT.lt.{0} Nat instLTNat i (DecrAlmostLinearSSSP.Decremental.logicalCount b) →
                  ∀ (offset : Nat),
                    @LT.lt.{0} Nat instLTNat offset (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                      @Ne.{1} Nat j
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) i))
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) offset))
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
              @Eq.{1} Nat (t.natMem j) (s.natMem j)) →
          (∀ (j : Nat),
              (∀ (i : Nat),
                  @LT.lt.{0} Nat instLTNat i (DecrAlmostLinearSSSP.Decremental.logicalCount b) →
                    @Ne.{1} Nat j
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) i))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
                (∀ (v : Nat),
                    @LT.lt.{0} Nat instLTNat v b.input.n →
                      @Ne.{1} Nat j
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (DecrAlmostLinearSSSP.Decremental.logicalCount b) v)))
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
                  @Eq.{1} Real (t.realMem j) (s.realMem j)) →
            DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state t)) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B N : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (s t : DecrAlmostLinearSSSP.Decremental.Structured.Data) (cost : Nat),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    @LE.le.{0} Nat instLENat b.input.n B →
      DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.CoreInitialSaved.code N) s cost
          t →
        (∀ (address : Nat),
            @LT.lt.{0} Nat instLTNat address
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B)
                  (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) →
              And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                (@Eq.{1} Real (t.realMem address) (s.realMem address))) →
          DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state t) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (N registers : Nat) (p cut : DecrAlmostLinearSSSP.Decremental.Program),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) registers →
    have B :=
      @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b.input.n
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) b.input.k))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)));
    have K :=
      DecrAlmostLinearSSSP.Decremental.computableCutQuality N
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size);
    ∃ cost t,
      And
        (DecrAlmostLinearSSSP.Decremental.Structured.Eval
          (DecrAlmostLinearSSSP.Decremental.CoreInitialize.bootCutInputCode N registers)
          (DecrAlmostLinearSSSP.Decremental.Structured.data (DecrAlmostLinearSSSP.Decremental.initialMachine p b.input))
          cost t)
        (And
          (@LE.le.{0} Nat instLENat cost
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 80000) (instOfNatNat (nat_lit 80000)))
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) N
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 265) (instOfNatNat (nat_lit 265))))
                    b.input.size)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                    (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
                      (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing)
                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@OfNat.ofNat.{0} Real (nat_lit 32)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
                          (DecrAlmostLinearSSSP.Decremental.logarithm2
                            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                              (@Nat.cast.{0} Real Real.instNatCast b.input.size)
                              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
                        b.input.accuracy))))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) registers))
              (@OfNat.ofNat.{0} Nat (nat_lit 105) (instOfNatNat (nat_lit 105)))))
          (And
            (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K (DecrAlmostLinearSSSP.Decremental.initializeState b)
              t)
            (DecrAlmostLinearSSSP.Decremental.CoreSource.Image B
              (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) registers
              (@DecrAlmostLinearSSSP.Decremental.cutInitial b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                cut
                (@DecrAlmostLinearSSSP.Decremental.indexedPhysical b
                  (DecrAlmostLinearSSSP.Decremental.initializeState b) (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                  (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                (@HPow.hPow.{0, 0, 0} Real Int Real
                  (@instHPow.{0, 0} Real Int
                    (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                  K (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                (@HPow.hPow.{0, 0, 0} Real Int Real
                  (@instHPow.{0, 0} Real Int
                    (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                  (DecrAlmostLinearSSSP.Decremental.kappa b)
                  (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))))))
              t)))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K K0 h Γ init : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
    ∀ (impl : DecrAlmostLinearSSSP.Decremental.CutImplementation),
      DecrAlmostLinearSSSP.Decremental.ImplementsCut impl
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
            (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
          K0 h Γ init
          (@HPow.hPow.{0, 0, 0} Real Int Real
            (@instHPow.{0, 0} Real Int (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid))) K
            (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))))) →
        ∃ first,
          And
            (DecrAlmostLinearSSSP.Decremental.Ends impl.program
              (@DecrAlmostLinearSSSP.Decremental.cutInitial b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                impl.program
                (@DecrAlmostLinearSSSP.Decremental.indexedPhysical b
                  (DecrAlmostLinearSSSP.Decremental.initializeState b) (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                  (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                (@HPow.hPow.{0, 0, 0} Real Int Real
                  (@instHPow.{0, 0} Real Int
                    (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                  K (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                (@HPow.hPow.{0, 0, 0} Real Int Real
                  (@instHPow.{0, 0} Real Int
                    (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                  (DecrAlmostLinearSSSP.Decremental.kappa b)
                  (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))))))
              first)
            (And
              (@DecrAlmostLinearSSSP.Decremental.CutModel b (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b)
                (DecrAlmostLinearSSSP.Decremental.initializeState b)
                (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b) first))
              (And
                (@Eq.{1} Bool
                  (@DecrAlmostLinearSSSP.Decremental.CutState.hasCut b.input.n
                    (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                    (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b) first))
                  Bool.false)
                (And (@LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast first.work) init)
                  (DecrAlmostLinearSSSP.Decremental.CutSession impl b.input.n
                    (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                      (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                    first K0
                    (@HPow.hPow.{0, 0, 0} Real Int Real
                      (@instHPow.{0, 0} Real Int
                        (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                      K (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                    h Γ init))))))))))) ∧ ((((((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (N : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program)
  (impl : DecrAlmostLinearSSSP.Decremental.CutImplementation) (K0 h Γ init : Real),
  DecrAlmostLinearSSSP.Decremental.ImplementsCut impl
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
        (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
      K0 h Γ init
      (@HPow.hPow.{0, 0, 0} Real Int Real
        (@instHPow.{0, 0} Real Int (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
        (DecrAlmostLinearSSSP.Decremental.computableCutQuality N
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size))
        (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))))) →
    have B :=
      @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b.input.n
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) b.input.k))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)));
    have K :=
      DecrAlmostLinearSSSP.Decremental.computableCutQuality N
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size);
    have registers := DecrAlmostLinearSSSP.Decremental.CoreInitialize.sourceRegisters impl.program;
    ∃ cost t first,
      And
        (DecrAlmostLinearSSSP.Decremental.Structured.Eval
          (DecrAlmostLinearSSSP.Decremental.CoreInitialize.bootCutCode N impl.program)
          (DecrAlmostLinearSSSP.Decremental.Structured.data (DecrAlmostLinearSSSP.Decremental.initialMachine p b.input))
          cost t)
        (And
          (@LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast cost)
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@Nat.cast.{0} Real Real.instNatCast
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 80000) (instOfNatNat (nat_lit 80000)))
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) N
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                          (@OfNat.ofNat.{0} Nat (nat_lit 265) (instOfNatNat (nat_lit 265))))
                        b.input.size)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                        (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
                          (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing)
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                              (@OfNat.ofNat.{0} Real (nat_lit 32)
                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
                                    (@Nat.instNeZeroSucc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
                              (DecrAlmostLinearSSSP.Decremental.logarithm2
                                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                  (@Nat.cast.{0} Real Real.instNatCast b.input.size)
                                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
                            b.input.accuracy))))
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))) registers))
                  (@OfNat.ofNat.{0} Nat (nat_lit 120) (instOfNatNat (nat_lit 120)))))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (@Nat.cast.{0} Real Real.instNatCast
                    (DecrAlmostLinearSSSP.Decremental.dispatchCharge impl.program.code))
                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
                init)))
          (And
            (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K (DecrAlmostLinearSSSP.Decremental.initializeState b)
              t)
            (And
              (DecrAlmostLinearSSSP.Decremental.CoreSource.Image B
                (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) registers first t)
              (And
                (@DecrAlmostLinearSSSP.Decremental.CutModel b (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                  (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b)
                  (DecrAlmostLinearSSSP.Decremental.initializeState b)
                  (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b) first))
                (And
                  (@Eq.{1} Bool
                    (@DecrAlmostLinearSSSP.Decremental.CutState.hasCut b.input.n
                      (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                      (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b) first))
                    Bool.false)
                  (And (@LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast first.work) init)
                    (And
                      (DecrAlmostLinearSSSP.Decremental.Ends impl.program
                        (@DecrAlmostLinearSSSP.Decremental.cutInitial b.input.n
                          (DecrAlmostLinearSSSP.Decremental.logicalCount b) impl.program
                          (@DecrAlmostLinearSSSP.Decremental.indexedPhysical b
                            (DecrAlmostLinearSSSP.Decremental.initializeState b)
                            (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                            (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b))
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                          (@HPow.hPow.{0, 0, 0} Real Int Real
                            (@instHPow.{0, 0} Real Int
                              (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                            K
                            (@Neg.neg.{0} Int Int.instNegInt
                              (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                          (@HPow.hPow.{0, 0, 0} Real Int Real
                            (@instHPow.{0, 0} Real Int
                              (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                            (DecrAlmostLinearSSSP.Decremental.kappa b)
                            (@Neg.neg.{0} Int Int.instNegInt
                              (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))))))
                        first)
                      (DecrAlmostLinearSSSP.Decremental.CutSession impl b.input.n
                        (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                          (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                        first K0
                        (@HPow.hPow.{0, 0, 0} Real Int Real
                          (@instHPow.{0, 0} Real Int
                            (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                          K
                          (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                        h Γ init))))))))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (N : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program)
  (impl : DecrAlmostLinearSSSP.Decremental.CutImplementation) (K0 h Γ init : Real),
  DecrAlmostLinearSSSP.Decremental.ImplementsCut impl
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
        (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
      K0 h Γ init
      (@HPow.hPow.{0, 0, 0} Real Int Real
        (@instHPow.{0, 0} Real Int (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
        (DecrAlmostLinearSSSP.Decremental.computableCutQuality N
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size))
        (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))))) →
    have B :=
      @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b.input.n
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) b.input.k))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)));
    have K :=
      DecrAlmostLinearSSSP.Decremental.computableCutQuality N
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size);
    have registers := DecrAlmostLinearSSSP.Decremental.CoreInitialize.sourceRegisters impl.program;
    ∃ cost t ctx,
      And
        (DecrAlmostLinearSSSP.Decremental.Structured.Eval
          (DecrAlmostLinearSSSP.Decremental.CoreInitialize.bootCutCode N impl.program)
          (DecrAlmostLinearSSSP.Decremental.Structured.data (DecrAlmostLinearSSSP.Decremental.initialMachine p b.input))
          cost t)
        (And
          (@LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast cost)
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@Nat.cast.{0} Real Real.instNatCast
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 80000) (instOfNatNat (nat_lit 80000)))
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) N
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                          (@OfNat.ofNat.{0} Nat (nat_lit 265) (instOfNatNat (nat_lit 265))))
                        b.input.size)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                        (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
                          (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing)
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                              (@OfNat.ofNat.{0} Real (nat_lit 32)
                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
                                    (@Nat.instNeZeroSucc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
                              (DecrAlmostLinearSSSP.Decremental.logarithm2
                                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                  (@Nat.cast.{0} Real Real.instNatCast b.input.size)
                                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
                            b.input.accuracy))))
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))) registers))
                  (@OfNat.ofNat.{0} Nat (nat_lit 120) (instOfNatNat (nat_lit 120)))))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (@Nat.cast.{0} Real Real.instNatCast
                    (DecrAlmostLinearSSSP.Decremental.dispatchCharge impl.program.code))
                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
                init)))
          (And
            (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K (DecrAlmostLinearSSSP.Decremental.initializeState b)
              t)
            (And
              (@DecrAlmostLinearSSSP.Decremental.CutModel b (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b)
                (DecrAlmostLinearSSSP.Decremental.initializeState b)
                (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                  (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B registers
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                      (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                    impl K0
                    (@HPow.hPow.{0, 0, 0} Real Int Real
                      (@instHPow.{0, 0} Real Int
                        (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                      K (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                    h Γ init t ctx)))
              (And
                (@Eq.{1} Bool
                  (@DecrAlmostLinearSSSP.Decremental.CutState.hasCut b.input.n
                    (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                    (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B registers
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                          (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                        impl K0
                        (@HPow.hPow.{0, 0, 0} Real Int Real
                          (@instHPow.{0, 0} Real Int
                            (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                          K
                          (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                        h Γ init t ctx)))
                  Bool.false)
                (And
                  (@Eq.{1}
                    (List.{0}
                      (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                        (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                    (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B registers
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                        (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                      impl K0
                      (@HPow.hPow.{0, 0, 0} Real Int Real
                        (@instHPow.{0, 0} Real Int
                          (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                        K (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                      h Γ init t ctx)
                    (@List.nil.{0}
                      (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                        (DecrAlmostLinearSSSP.Decremental.logicalCount b))))
                  (And
                    (@Eq.{1} (List.{0} DecrAlmostLinearSSSP.Decremental.Machine)
                      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines b B registers
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                          (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                        impl K0
                        (@HPow.hPow.{0, 0, 0} Real Int Real
                          (@instHPow.{0, 0} Real Int
                            (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                          K
                          (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                        h Γ init t ctx)
                      (@List.cons.{0} DecrAlmostLinearSSSP.Decremental.Machine
                        (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B registers
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                            (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                          impl K0
                          (@HPow.hPow.{0, 0, 0} Real Int Real
                            (@instHPow.{0, 0} Real Int
                              (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                            K
                            (@Neg.neg.{0} Int Int.instNegInt
                              (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                          h Γ init t ctx)
                        (@List.nil.{0} DecrAlmostLinearSSSP.Decremental.Machine)))
                    (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.first b B registers
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                          (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                        impl K0
                        (@HPow.hPow.{0, 0, 0} Real Int Real
                          (@instHPow.{0, 0} Real Int
                            (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                          K
                          (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                        h Γ init t ctx)
                      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B registers
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                          (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                        impl K0
                        (@HPow.hPow.{0, 0, 0} Real Int Real
                          (@instHPow.{0, 0} Real Int
                            (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                          K
                          (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                        h Γ init t ctx)))))))))) ∧ ((@Filter.Tendsto.{0, 0} Nat Nat DecrAlmostLinearSSSP.Decremental.cutLogHeight (@Filter.atTop.{0} Nat Nat.instPreorder)
  (@Filter.atTop.{0} Nat Nat.instPreorder)) ∧ (@Filter.Tendsto.{0, 0} Nat Nat DecrAlmostLinearSSSP.Decremental.cutRoot (@Filter.atTop.{0} Nat Nat.instPreorder)
  (@Filter.atTop.{0} Nat Nat.instPreorder)))) ∧ (((@Filter.Tendsto.{0, 0} Nat Real
  (fun m => @Nat.cast.{0} Real Real.instNatCast (DecrAlmostLinearSSSP.Decremental.cutRoot m))
  (@Filter.atTop.{0} Nat Nat.instPreorder) (@Filter.atTop.{0} Real Real.instPreorder)) ∧ (∀ (N m : Nat),
  @LE.le.{0} Real Real.instLE
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (Real.log (DecrAlmostLinearSSSP.Decremental.computableCutQuality N m))
      (Real.log
        (@Nat.cast.{0} Real Real.instNatCast
          (@Max.max.{0} Nat Nat.instMax (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))))
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 8192)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 8192) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 8191) (instOfNatNat (nat_lit 8191)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 8190) (instOfNatNat (nat_lit 8190)))))))
        (@Nat.cast.{0} Real Real.instNatCast N))
      (@Nat.cast.{0} Real Real.instNatCast (DecrAlmostLinearSSSP.Decremental.cutRoot m))))) ∧ ((∀ (N : Nat), DecrAlmostLinearSSSP.Decremental.Subpolynomial (DecrAlmostLinearSSSP.Decremental.computableCutQuality N)) ∧ (∀ (N m : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) N →
    @LE.le.{0} Real Real.instLE
      (@OfNat.ofNat.{0} Real (nat_lit 32)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
      (DecrAlmostLinearSSSP.Decremental.computableCutQuality N m))))) ∧ ((((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (qualityPower : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) qualityPower →
    ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (impl : DecrAlmostLinearSSSP.Decremental.CutImplementation)
      (K0 h Γ init : Real),
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K0 →
        @LE.le.{0} Real Real.instLE K0
            (DecrAlmostLinearSSSP.Decremental.computableCutQuality qualityPower
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)) →
          DecrAlmostLinearSSSP.Decremental.ImplementsCut impl
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
              K0 h Γ init
              (@HPow.hPow.{0, 0, 0} Real Int Real
                (@instHPow.{0, 0} Real Int (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                (DecrAlmostLinearSSSP.Decremental.computableCutQuality qualityPower
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size))
                (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))))) →
            have B :=
              @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b.input.n
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) b.input.k))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)));
            have K :=
              DecrAlmostLinearSSSP.Decremental.computableCutQuality qualityPower
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size);
            have registers := DecrAlmostLinearSSSP.Decremental.CoreInitialize.sourceRegisters impl.program;
            ∃ cost t after next,
              And
                (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                  (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.initCode qualityPower impl.program)
                  (DecrAlmostLinearSSSP.Decremental.Structured.data
                    (DecrAlmostLinearSSSP.Decremental.initialMachine p b.input))
                  cost t)
                (And (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K after t)
                  (And (DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K after)
                    (And
                      (@DecrAlmostLinearSSSP.Decremental.CutModel b (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                        (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b) after
                        (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                          (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B registers
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                              (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                            impl K0
                            (@HPow.hPow.{0, 0, 0} Real Int Real
                              (@instHPow.{0, 0} Real Int
                                (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                              K
                              (@Neg.neg.{0} Int Int.instNegInt
                                (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                            h Γ init t next)))
                      (And (@Eq.{1} Bool (@DecrAlmostLinearSSSP.Decremental.State.stopped b after) Bool.true)
                        (And (DecrAlmostLinearSSSP.Decremental.ReadoutCertificate b after)
                          (And
                            (@Eq.{1} (Finset.{0} (Fin b.input.k))
                              (@DecrAlmostLinearSSSP.Decremental.State.active b after)
                              (@Finset.univ.{0} (Fin b.input.k) (Fin.fintype b.input.k)))
                            (And
                              (@Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
                                (@DecrAlmostLinearSSSP.Decremental.State.pending b after)
                                (@List.nil.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)))
                              (And
                                (DecrAlmostLinearSSSP.Decremental.CoreRepair.OperationDebt b after
                                  (@List.length.{0}
                                    (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                      (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                    (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B registers
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                          b.weightExponent)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                      impl K0
                                      (@HPow.hPow.{0, 0, 0} Real Int Real
                                        (@instHPow.{0, 0} Real Int
                                          (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                        K
                                        (@Neg.neg.{0} Int Int.instNegInt
                                          (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                      h Γ init t next))
                                  (DecrAlmostLinearSSSP.Decremental.reportVolume
                                    (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines b B registers
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                          b.weightExponent)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                      impl K0
                                      (@HPow.hPow.{0, 0, 0} Real Int Real
                                        (@instHPow.{0, 0} Real Int
                                          (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                        K
                                        (@Neg.neg.{0} Int Int.instNegInt
                                          (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                      h Γ init t next))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                (And
                                  (@Eq.{1} Nat
                                    (@DecrAlmostLinearSSSP.Decremental.toggleVolume b.input.n
                                      (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B registers
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                            b.weightExponent)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                        impl K0
                                        (@HPow.hPow.{0, 0, 0} Real Int Real
                                          (@instHPow.{0, 0} Real Int
                                            (@ZPow.toPow.{0} Real
                                              (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                          K
                                          (@Neg.neg.{0} Int Int.instNegInt
                                            (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                        h Γ init t next))
                                    (@DecrAlmostLinearSSSP.Decremental.State.toggles b after))
                                  (@LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast cost)
                                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                          (@Nat.cast.{0} Real Real.instNatCast
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 80000)
                                                          (instOfNatNat (nat_lit 80000)))
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          qualityPower
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                            (instOfNatNat (nat_lit 1)))))
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 265) (instOfNatNat (nat_lit 265))))
                                                    b.input.size)
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                    (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
                                                      (@FloorRing.toFloorSemiring.{0} Real Real.instRing
                                                        Real.linearOrder Real.instFloorRing)
                                                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                                        (@instHDiv.{0} Real
                                                          (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                                        (@HMul.hMul.{0, 0, 0} Real Real Real
                                                          (@instHMul.{0} Real Real.instMul)
                                                          (@OfNat.ofNat.{0} Real (nat_lit 32)
                                                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
                                                              (@Nat.instAtLeastTwoHAddOfNat
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 31)
                                                                  (instOfNatNat (nat_lit 31)))
                                                                (@Nat.instNeZeroSucc
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 30)
                                                                    (instOfNatNat (nat_lit 30)))))))
                                                          (DecrAlmostLinearSSSP.Decremental.logarithm2
                                                            (@HAdd.hAdd.{0, 0, 0} Real Real Real
                                                              (@instHAdd.{0} Real Real.instAdd)
                                                              (@Nat.cast.{0} Real Real.instNatCast b.input.size)
                                                              (@OfNat.ofNat.{0} Real (nat_lit 1)
                                                                (@One.toOfNat1.{0} Real Real.instOne)))))
                                                        b.input.accuracy))))
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))
                                                  registers))
                                              (@OfNat.ofNat.{0} Nat (nat_lit 120) (instOfNatNat (nat_lit 120)))))
                                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                              (@Nat.cast.{0} Real Real.instNatCast
                                                (DecrAlmostLinearSSSP.Decremental.dispatchCharge impl.program.code))
                                              (@OfNat.ofNat.{0} Real (nat_lit 2)
                                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                                  (@Nat.instAtLeastTwoHAddOfNat
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                                    (@Nat.instNeZeroSucc
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
                                            init))
                                        (@Nat.cast.{0} Real Real.instNatCast
                                          (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.credit b registers
                                            impl.program after
                                            (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B
                                              registers
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                b.input.size)
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                  b.weightExponent)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                              impl K0
                                              (@HPow.hPow.{0, 0, 0} Real Int Real
                                                (@instHPow.{0, 0} Real Int
                                                  (@ZPow.toPow.{0} Real
                                                    (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                K
                                                (@Neg.neg.{0} Int Int.instNegInt
                                                  (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                              h Γ init t next)
                                            (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B registers
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                b.input.size)
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                  b.weightExponent)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                              impl K0
                                              (@HPow.hPow.{0, 0, 0} Real Int Real
                                                (@instHPow.{0, 0} Real Int
                                                  (@ZPow.toPow.{0} Real
                                                    (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                K
                                                (@Neg.neg.{0} Int Int.instNegInt
                                                  (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                              h Γ init t next)
                                            (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines b B
                                              registers
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                b.input.size)
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                  b.weightExponent)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                              impl K0
                                              (@HPow.hPow.{0, 0, 0} Real Int Real
                                                (@instHPow.{0, 0} Real Int
                                                  (@ZPow.toPow.{0} Real
                                                    (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                K
                                                (@Neg.neg.{0} Int Int.instNegInt
                                                  (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                              h Γ init t next))))
                                      (@OfNat.ofNat.{0} Real (nat_lit 7)
                                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 7) Real.instNatCast
                                          (@Nat.instAtLeastTwoHAddOfNat
                                            (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                                            (@Nat.instNeZeroSucc
                                              (@OfNat.ofNat.{0} Nat (nat_lit 5)
                                                (instOfNatNat (nat_lit 5))))))))))))))))))) ∧ (∀ (qualityPower : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine)
  (v : Nat),
  ∃ d,
    And
      (DecrAlmostLinearSSSP.Decremental.Ends (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.coreProgram qualityPower p)
        (have __src :=
          DecrAlmostLinearSSSP.Decremental.resume c
            (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.coreProgram qualityPower p).query;
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
            (And (@Eq.{1} (Nat → Real) d.realMem c.realMem) (@Eq.{1} (Nat → Nat) d.natMem c.natMem))))))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (qualityPower : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) qualityPower →
    ∀ (impl : DecrAlmostLinearSSSP.Decremental.CutImplementation) (K0 h Γ init : Real),
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K0 →
        @LE.le.{0} Real Real.instLE K0
            (DecrAlmostLinearSSSP.Decremental.computableCutQuality qualityPower
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)) →
          DecrAlmostLinearSSSP.Decremental.ImplementsCut impl
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
              K0 h Γ init
              (@HPow.hPow.{0, 0, 0} Real Int Real
                (@instHPow.{0, 0} Real Int (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                (DecrAlmostLinearSSSP.Decremental.computableCutQuality qualityPower
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size))
                (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))))) →
            have B :=
              @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b.input.n
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) b.input.k))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)));
            have K :=
              DecrAlmostLinearSSSP.Decremental.computableCutQuality qualityPower
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size);
            have registers := DecrAlmostLinearSSSP.Decremental.CoreInitialize.sourceRegisters impl.program;
            ∃ cost c,
              And
                (DecrAlmostLinearSSSP.Decremental.Ends
                  (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.coreProgram qualityPower impl.program)
                  (DecrAlmostLinearSSSP.Decremental.initialMachine
                    (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.coreProgram qualityPower impl.program) b.input)
                  c)
                (And
                  (@Eq.{1} Nat c.work
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cost
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (∃ ready,
                    @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast c.work)
                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                            (@Nat.cast.{0} Real Real.instNatCast
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 80000) (instOfNatNat (nat_lit 80000)))
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) qualityPower
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                        (@OfNat.ofNat.{0} Nat (nat_lit 265) (instOfNatNat (nat_lit 265))))
                                      b.input.size)
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                      (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
                                        (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder
                                          Real.instFloorRing)
                                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                            (@OfNat.ofNat.{0} Real (nat_lit 32)
                                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
                                                (@Nat.instAtLeastTwoHAddOfNat
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
                                                  (@Nat.instNeZeroSucc
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
                                            (DecrAlmostLinearSSSP.Decremental.logarithm2
                                              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                                (@Nat.cast.{0} Real Real.instNatCast b.input.size)
                                                (@OfNat.ofNat.{0} Real (nat_lit 1)
                                                  (@One.toOfNat1.{0} Real Real.instOne)))))
                                          b.input.accuracy))))
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))) registers))
                                (@OfNat.ofNat.{0} Nat (nat_lit 120) (instOfNatNat (nat_lit 120)))))
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                (@Nat.cast.{0} Real Real.instNatCast
                                  (DecrAlmostLinearSSSP.Decremental.dispatchCharge impl.program.code))
                                (@OfNat.ofNat.{0} Real (nat_lit 2)
                                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                    (@Nat.instAtLeastTwoHAddOfNat
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                      (@Nat.instNeZeroSucc
                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
                              init))
                          (@Nat.cast.{0} Real Real.instNatCast
                            (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Ready.credit b B registers K K0 h Γ init
                              impl (@List.nil.{0} (Fin b.input.k)) (DecrAlmostLinearSSSP.Decremental.Structured.data c)
                              ready)))
                        (@OfNat.ofNat.{0} Real (nat_lit 8)
                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
                            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))))))))) ∧ (∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {B N : Nat} {K K0 h Γ init : Real}
  {impl : DecrAlmostLinearSSSP.Decremental.CutImplementation} {deleted : List.{0} (Fin b.input.k)}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  (r : DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Ready b B N K K0 h Γ init impl deleted s)
  (hB : @LE.le.{0} Nat instLENat b.input.n B) (value : Nat),
  @Eq.{1} Nat
    (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Ready.credit b B N K K0 h Γ init impl deleted
      { realReg := s.realReg,
        natReg :=
          @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) value,
        realMem := s.realMem, natMem := s.natMem }
      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Ready.external b B N K K0 h Γ init impl deleted s r hB value))
    (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Ready.credit b B N K K0 h Γ init impl deleted s r)))) ∧ (((∀ {k : Nat} (deleted : List.{0} (Fin k)) (e : Fin k),
  @Eq.{1} (Finset.{0} (Fin k))
    (@DecrAlmostLinearSSSP.Decremental.live k
      (@HAppend.hAppend.{0, 0, 0} (List.{0} (Fin k)) (List.{0} (Fin k)) (List.{0} (Fin k))
        (@instHAppendOfAppend.{0} (List.{0} (Fin k)) (@List.instAppend.{0} (Fin k))) deleted
        (@List.cons.{0} (Fin k) e (@List.nil.{0} (Fin k)))))
    (@Finset.erase.{0} (Fin k) (instDecidableEqFin k) (@DecrAlmostLinearSSSP.Decremental.live k deleted) e)) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (qualityPower : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) qualityPower →
    ∀ (impl : DecrAlmostLinearSSSP.Decremental.CutImplementation) (K0 h Γ init : Real),
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K0 →
        @LE.le.{0} Real Real.instLE K0
            (DecrAlmostLinearSSSP.Decremental.computableCutQuality qualityPower
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)) →
          ∀ (deleted : List.{0} (Fin b.input.k)) (c : DecrAlmostLinearSSSP.Decremental.Machine)
            (ready :
              DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Ready b
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b.input.n
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) b.input.k))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (DecrAlmostLinearSSSP.Decremental.CoreInitialize.sourceRegisters impl.program)
                (DecrAlmostLinearSSSP.Decremental.computableCutQuality qualityPower
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size))
                K0 h Γ init impl deleted (DecrAlmostLinearSSSP.Decremental.Structured.data c))
            (e : Fin b.input.k),
            ∃ cost d,
              And
                (DecrAlmostLinearSSSP.Decremental.Ends
                  (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.coreProgram qualityPower impl.program)
                  (DecrAlmostLinearSSSP.Decremental.deletionMachine
                    (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.coreProgram qualityPower impl.program) c
                    (@Fin.val b.input.k e))
                  d)
                (And
                  (@Eq.{1} Nat d.work
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work cost)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (∃ next,
                    @LE.le.{0} Nat instLENat
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d.work
                          (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                        (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Ready.credit b
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b.input.n
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) b.input.k))
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (DecrAlmostLinearSSSP.Decremental.CoreInitialize.sourceRegisters impl.program)
                          (DecrAlmostLinearSSSP.Decremental.computableCutQuality qualityPower
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size))
                          K0 h Γ init impl deleted (DecrAlmostLinearSSSP.Decremental.Structured.data c) ready))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                        (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Ready.credit b
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b.input.n
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) b.input.k))
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (DecrAlmostLinearSSSP.Decremental.CoreInitialize.sourceRegisters impl.program)
                          (DecrAlmostLinearSSSP.Decremental.computableCutQuality qualityPower
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size))
                          K0 h Γ init impl
                          (@HAppend.hAppend.{0, 0, 0} (List.{0} (Fin b.input.k)) (List.{0} (Fin b.input.k))
                            (List.{0} (Fin b.input.k))
                            (@instHAppendOfAppend.{0} (List.{0} (Fin b.input.k)) (@List.instAppend.{0} (Fin b.input.k)))
                            deleted (@List.cons.{0} (Fin b.input.k) e (@List.nil.{0} (Fin b.input.k))))
                          (DecrAlmostLinearSSSP.Decremental.Structured.data d) next)))))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (qualityPower : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) qualityPower →
    ∀ (impl : DecrAlmostLinearSSSP.Decremental.CutImplementation) (K0 h Γ init : Real),
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K0 →
        @LE.le.{0} Real Real.instLE K0
            (DecrAlmostLinearSSSP.Decremental.computableCutQuality qualityPower
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)) →
          DecrAlmostLinearSSSP.Decremental.ImplementsCut impl
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
              K0 h Γ init
              (@HPow.hPow.{0, 0, 0} Real Int Real
                (@instHPow.{0, 0} Real Int (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                (DecrAlmostLinearSSSP.Decremental.computableCutQuality qualityPower
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size))
                (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))))) →
            ∀ (ds : List.{0} (Fin b.input.k)),
              ∃ cs last,
                And
                  (DecrAlmostLinearSSSP.Decremental.OnlineRun
                    (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.coreProgram qualityPower impl.program) b.input ds
                    cs)
                  (And
                    (@Eq.{1} Nat (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Machine cs)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@List.length.{0} (Fin b.input.k) ds)
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (And
                      (@Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Machine)
                        (@List.getLast?.{0} DecrAlmostLinearSSSP.Decremental.Machine cs)
                        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Machine last))
                      (And
                        (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Completed b qualityPower impl K0 h Γ init ds
                          last)
                        (∀ (j : Nat) (c : DecrAlmostLinearSSSP.Decremental.Machine),
                          @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Machine)
                              (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Machine) Nat
                                DecrAlmostLinearSSSP.Decremental.Machine
                                (fun as i =>
                                  @LT.lt.{0} Nat instLTNat i
                                    (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Machine as))
                                (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Machine) cs j)
                              (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Machine c) →
                            DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Completed b qualityPower impl K0 h Γ init
                              (@List.take.{0} (Fin b.input.k) j ds) c))))) ∧ ((∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {qualityPower : Nat}
  {impl : DecrAlmostLinearSSSP.Decremental.CutImplementation} {K0 h Γ init : Real} {deleted : List.{0} (Fin b.input.k)}
  {c : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Completed b qualityPower impl K0 h Γ init deleted c →
    And
      (@Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.stored c (@Fin.val b.input.n b.input.source))
        (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero)))
      (And
        (∀ (v : Fin b.input.n),
          And
            (@LE.le.{0} Nat instLENat (c.natMem (@Fin.val b.input.n v))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@Eq.{1} Nat (c.natMem (@Fin.val b.input.n v))
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
              @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                (c.realMem (@Fin.val b.input.n v))))
        (∀ (v : Fin b.input.n),
          And
            (@LE.le.{0} ENNReal ENNReal.instLE (b.input.dist deleted v)
              (DecrAlmostLinearSSSP.Decremental.stored c (@Fin.val b.input.n v)))
            (And
              (@LE.le.{0} ENNReal ENNReal.instLE (DecrAlmostLinearSSSP.Decremental.stored c (@Fin.val b.input.n v))
                (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                  (@instHMul.{0} ENNReal
                    (@Distrib.toMul.{0} ENNReal
                      (@instDistribOfSemiring.{0} ENNReal
                        (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                  (ENNReal.ofReal
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) b.input.accuracy))
                  (b.input.dist deleted v)))
              (Iff
                (@Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.stored c (@Fin.val b.input.n v))
                  (@Top.top.{0} ENNReal ENNReal.instTop))
                (Not
                  (@DecrAlmostLinearSSSP.Decremental.Reachable b.input.n b.input.k b.input.graph
                    (@DecrAlmostLinearSSSP.Decremental.live b.input.k deleted) b.input.source v))))))) ∧ (∀ {b : DecrAlmostLinearSSSP.Decremental.Core} (s : DecrAlmostLinearSSSP.Decremental.State b),
  @LE.le.{0} Nat instLENat (@DecrAlmostLinearSSSP.Decremental.CoreRepair.stoppedBit b s)
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))) ∧ (((((∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {B N : Nat} {K K0 h Γ init : Real}
  {impl : DecrAlmostLinearSSSP.Decremental.CutImplementation} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  (ctx :
    DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context b B N
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
        (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
      impl K0
      (@HPow.hPow.{0, 0, 0} Real Int Real
        (@instHPow.{0, 0} Real Int (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid))) K
        (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
      h Γ init s)
  (state : DecrAlmostLinearSSSP.Decremental.State b) (offset : Nat) (T : Real),
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) h →
    @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) Γ →
      @LE.le.{0} Real Real.instLE
          (@Nat.cast.{0} Real Real.instNatCast (@DecrAlmostLinearSSSP.Decremental.State.toggles b state)) T →
        DecrAlmostLinearSSSP.Decremental.CoreRepair.OperationDebt b state
            (@List.length.{0}
              (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b))
              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                  (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                impl K0
                (@HPow.hPow.{0, 0, 0} Real Int Real
                  (@instHPow.{0, 0} Real Int
                    (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                  K (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                h Γ init s ctx))
            (DecrAlmostLinearSSSP.Decremental.reportVolume
              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines b B N
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                  (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                impl K0
                (@HPow.hPow.{0, 0, 0} Real Int Real
                  (@instHPow.{0, 0} Real Int
                    (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                  K (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                h Γ init s ctx))
            offset →
          @Eq.{1} Nat
              (@DecrAlmostLinearSSSP.Decremental.toggleVolume b.input.n
                (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                    (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                  impl K0
                  (@HPow.hPow.{0, 0, 0} Real Int Real
                    (@instHPow.{0, 0} Real Int
                      (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                    K (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                  h Γ init s ctx))
              (@DecrAlmostLinearSSSP.Decremental.State.toggles b state) →
            @LE.le.{0} Real Real.instLE
              (@Nat.cast.{0} Real Real.instNatCast
                (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.credit b N impl.program state
                  (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                      (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                    impl K0
                    (@HPow.hPow.{0, 0, 0} Real Int Real
                      (@instHPow.{0, 0} Real Int
                        (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                      K (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                    h Γ init s ctx)
                  (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                      (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                    impl K0
                    (@HPow.hPow.{0, 0, 0} Real Int Real
                      (@instHPow.{0, 0} Real Int
                        (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                      K (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                    h Γ init s ctx)
                  (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines b B N
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                      (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                    impl K0
                    (@HPow.hPow.{0, 0, 0} Real Int Real
                      (@instHPow.{0, 0} Real Int
                        (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                      K (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                    h Γ init s ctx)))
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@Nat.cast.{0} Real Real.instNatCast
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (DecrAlmostLinearSSSP.Decremental.dispatchCharge impl.program.code)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      init)
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@Nat.cast.{0} Real Real.instNatCast
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (DecrAlmostLinearSSSP.Decremental.dispatchCharge impl.program.code)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                          h)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@OfNat.ofNat.{0} Real (nat_lit 100)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 100) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 99) (instOfNatNat (nat_lit 99)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 98) (instOfNatNat (nat_lit 98)))))))
                          (@Nat.cast.{0} Real Real.instNatCast
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) N
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                              (@OfNat.ofNat.{0} Real (nat_lit 5)
                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 5) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                    (@Nat.instNeZeroSucc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Γ
                                  (@HPow.hPow.{0, 0, 0} Real Nat Real
                                    (@instHPow.{0, 0} Real Nat
                                      (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                                    K (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                T))
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                              (@OfNat.ofNat.{0} Real (nat_lit 2)
                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                    (@Nat.instNeZeroSucc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                              T))
                          (@Nat.cast.{0} Real Real.instNatCast offset))
                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@Nat.cast.{0} Real Real.instNatCast
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (DecrAlmostLinearSSSP.Decremental.dispatchCharge impl.program.code)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                        h)
                      (@OfNat.ofNat.{0} Real (nat_lit 20)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 20) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18))))))))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Γ
                        (@HPow.hPow.{0, 0, 0} Real Nat Real
                          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) K
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      T)))
                (@OfNat.ofNat.{0} Real (nat_lit 10)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 10) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))))) ∧ (∀ (D C d h Γ K L M : Real),
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) D →
    @LE.le.{0} Real Real.instLE
        (@OfNat.ofNat.{0} Real (nat_lit 20)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 20) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))))))
        C →
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) d →
        @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) h →
          @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) Γ →
            @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) K →
              @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) L →
                @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                    M →
                  ∀ (offset : Real),
                    @LE.le.{0} Real Real.instLE
                        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) offset →
                      @LE.le.{0} Real Real.instLE offset
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@OfNat.ofNat.{0} Real (nat_lit 6)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 6) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))
                            M) →
                        have T :=
                          @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                  (@OfNat.ofNat.{0} Real (nat_lit 1040)
                                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 1040) Real.instNatCast
                                      (@Nat.instAtLeastTwoHAddOfNat
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1039) (instOfNatNat (nat_lit 1039)))
                                        (@Nat.instNeZeroSucc
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1038) (instOfNatNat (nat_lit 1038)))))))
                                  d)
                                (@HPow.hPow.{0, 0, 0} Real Nat Real
                                  (@instHPow.{0, 0} Real Nat
                                    (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                                  K (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                              (@HPow.hPow.{0, 0, 0} Real Nat Real
                                (@instHPow.{0, 0} Real Nat
                                  (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                                L (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                            M;
                        @LE.le.{0} Real Real.instLE
                          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) D h) C)
                                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                        (@OfNat.ofNat.{0} Real (nat_lit 5)
                                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 5) Real.instNatCast
                                            (@Nat.instAtLeastTwoHAddOfNat
                                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                              (@Nat.instNeZeroSucc
                                                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Γ
                                            (@HPow.hPow.{0, 0, 0} Real Nat Real
                                              (@instHPow.{0, 0} Real Nat
                                                (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                                              K (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                          T))
                                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                        (@OfNat.ofNat.{0} Real (nat_lit 2)
                                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                            (@Nat.instAtLeastTwoHAddOfNat
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                              (@Nat.instNeZeroSucc
                                                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                                        T))
                                    offset)
                                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) D h)
                                  (@OfNat.ofNat.{0} Real (nat_lit 20)
                                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 20) Real.instNatCast
                                      (@Nat.instAtLeastTwoHAddOfNat
                                        (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19)))
                                        (@Nat.instNeZeroSucc
                                          (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18))))))))
                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Γ
                                    (@HPow.hPow.{0, 0, 0} Real Nat Real
                                      (@instHPow.{0, 0} Real Nat
                                        (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                                      K (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                  T)))
                            (@OfNat.ofNat.{0} Real (nat_lit 10)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 10) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))))
                          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                          (@OfNat.ofNat.{0} Real (nat_lit 10000)
                                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 10000) Real.instNatCast
                                              (@Nat.instAtLeastTwoHAddOfNat
                                                (@OfNat.ofNat.{0} Nat (nat_lit 9999) (instOfNatNat (nat_lit 9999)))
                                                (@Nat.instNeZeroSucc
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 9998)
                                                    (instOfNatNat (nat_lit 9998)))))))
                                          d)
                                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) D C))
                                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) h))
                                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) Γ))
                                  (@HPow.hPow.{0, 0, 0} Real Nat Real
                                    (@instHPow.{0, 0} Real Nat
                                      (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                                    K (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))
                                (@HPow.hPow.{0, 0, 0} Real Nat Real
                                  (@instHPow.{0, 0} Real Nat
                                    (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                                  L (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                              M)
                            (@OfNat.ofNat.{0} Real (nat_lit 10)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 10) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))))))) ∧ ((∀ (m : Nat),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
    (DecrAlmostLinearSSSP.Decremental.coreLogOverhead m)) ∧ (DecrAlmostLinearSSSP.Decremental.Subpolynomial DecrAlmostLinearSSSP.Decremental.coreLogOverhead))) ∧ (((∀ (b : DecrAlmostLinearSSSP.Decremental.Core),
  @LE.le.{0} Real Real.instLE (DecrAlmostLinearSSSP.Decremental.A b)
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 65)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 65) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 63) (instOfNatNat (nat_lit 63)))))))
        (DecrAlmostLinearSSSP.Decremental.coreLogOverhead b.input.size))
      b.input.accuracy)) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core),
  @LE.le.{0} Real Real.instLE
    (Real.log
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (DecrAlmostLinearSSSP.Decremental.Q b)))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@Nat.cast.{0} Real Real.instNatCast
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b.weightExponent
          (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))
      (DecrAlmostLinearSSSP.Decremental.coreLogOverhead b.input.size)))) ∧ ((∀ (h Γ a : Nat → Real) (N : Nat),
  DecrAlmostLinearSSSP.Decremental.Subpolynomial h →
    DecrAlmostLinearSSSP.Decremental.Subpolynomial Γ →
      DecrAlmostLinearSSSP.Decremental.Subpolynomial a →
        DecrAlmostLinearSSSP.Decremental.Subpolynomial (DecrAlmostLinearSSSP.Decremental.coreRuntimeOverhead h Γ a N)) ∧ ((∀ (h Γ a : Nat → Real) (N m : Nat),
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (h
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)) →
    @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (Γ
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)) →
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (a
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)) →
        @LE.le.{0} Real Real.instLE
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (a
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))
          (DecrAlmostLinearSSSP.Decremental.coreRuntimeOverhead h Γ a N m)) ∧ (∀ (h Γ a : Nat → Real) (N m : Nat),
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (a
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)) →
    @LE.le.{0} Real Real.instLE
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
              (h
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
              (Γ
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))))
          (@HPow.hPow.{0, 0, 0} Real Nat Real
            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
            (DecrAlmostLinearSSSP.Decremental.computableCutQuality N
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
            (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))
        (@HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
          (DecrAlmostLinearSSSP.Decremental.coreLogOverhead m)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (DecrAlmostLinearSSSP.Decremental.coreRuntimeOverhead h Γ a N m)))))) ∧ ((((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.State b),
      DecrAlmostLinearSSSP.Decremental.RuntimeInvariant b K s →
        @LE.le.{0} Real Real.instLE
          (@Nat.cast.{0} Real Real.instNatCast (@DecrAlmostLinearSSSP.Decremental.State.toggles b s))
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@OfNat.ofNat.{0} Real (nat_lit 1040)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 1040) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat
                          (@OfNat.ofNat.{0} Nat (nat_lit 1039) (instOfNatNat (nat_lit 1039)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1038) (instOfNatNat (nat_lit 1038)))))))
                    (@Nat.cast.{0} Real Real.instNatCast
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b.weightExponent
                        (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))
                  (@HPow.hPow.{0, 0, 0} Real Nat Real
                    (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) K
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                (@Nat.cast.{0} Real Real.instNatCast b.input.size))
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                (DecrAlmostLinearSSSP.Decremental.coreLogOverhead b.input.size)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            b.input.accuracy)) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (N : Nat) (h Γ a : Nat → Real),
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (h
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)) →
    @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (Γ
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)) →
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (a
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)) →
        have m := @Nat.cast.{0} Real Real.instNatCast b.input.size;
        have M :=
          @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            m b.input.accuracy;
        have O := DecrAlmostLinearSSSP.Decremental.coreRuntimeOverhead h Γ a N b.input.size;
        have K :=
          DecrAlmostLinearSSSP.Decremental.computableCutQuality N
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size);
        have L := DecrAlmostLinearSSSP.Decremental.coreLogOverhead b.input.size;
        And (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) M)
          (And (@LE.le.{0} Real Real.instLE m M)
            (And
              (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) L)
              (And
                (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                  O)
                (And
                  (@LE.le.{0} Real Real.instLE
                    (a
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size))
                    O)
                  (And
                    (@LE.le.{0} Real Real.instLE
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                              (h
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)))
                            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                              (Γ
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size))))
                          (@HPow.hPow.{0, 0, 0} Real Nat Real
                            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                            K (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))
                        (@HPow.hPow.{0, 0, 0} Real Nat Real
                          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) L
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      O)
                    (@LE.le.{0} Real Real.instLE
                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) L b.input.accuracy)
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) O M))))))))) ∧ ((∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {qualityPower : Nat},
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) qualityPower →
    ∀ {impl : DecrAlmostLinearSSSP.Decremental.CutImplementation} (K0 C : Real) (h Γ a : Nat → Real),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C →
        @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (h
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)) →
          @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              (Γ
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)) →
            @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                (a
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)) →
              ∀ {ds : List.{0} (Fin b.input.k)} {c : DecrAlmostLinearSSSP.Decremental.Machine},
                @DecrAlmostLinearSSSP.Decremental.Legal b.input.k ds →
                  DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Completed b qualityPower impl K0
                      (h
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size))
                      (Γ
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@OfNat.ofNat.{0} Real (nat_lit 2)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                            (@Nat.cast.{0} Real Real.instNatCast b.input.size)))
                        (a
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)))
                      ds c →
                    @LE.le.{0} Real Real.instLE
                      (@Nat.cast.{0} Real Real.instNatCast
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                            (@List.length.{0} (Fin b.input.k) ds))))
                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.coreConstant b.weightExponent qualityPower
                              impl.program C)
                            (@Nat.cast.{0} Real Real.instNatCast b.input.size))
                          (DecrAlmostLinearSSSP.Decremental.coreRuntimeOverhead h Γ a qualityPower b.input.size))
                        b.input.accuracy)) ∧ (∀ (C : Real),
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C →
    ∀ (m : Nat),
      @LE.le.{0} Real Real.instLE
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
            (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
              (Real.log
                (@Nat.cast.{0} Real Real.instNatCast
                  (@Max.max.{0} Nat Nat.instMax (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real (nat_lit 5)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 5) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                (@OfNat.ofNat.{0} Real (nat_lit 6)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 6) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))))))
          (@Max.max.{0} Real Real.instMax (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (Real.log
              (Real.log
                (@Nat.cast.{0} Real Real.instNatCast
                  (@Max.max.{0} Nat Nat.instMax (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))))))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 12)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 12) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))))))
            C)
          (@HPow.hPow.{0, 0, 0} Real Nat Real
            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
            (@Nat.cast.{0} Real Real.instNatCast (DecrAlmostLinearSSSP.Decremental.cutRoot m))
            (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))))))) ∧ (((∀ (C : Real),
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C →
    ∃ N,
      And (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) N)
        (∀ (m : Nat),
          @LE.le.{0} Real Real.instLE
            (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
                  (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                    (Real.log
                      (@Nat.cast.{0} Real Real.instNatCast
                        (@Max.max.{0} Nat Nat.instMax (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@OfNat.ofNat.{0} Real (nat_lit 5)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 5) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                      (@OfNat.ofNat.{0} Real (nat_lit 6)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 6) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))))))
                (@Max.max.{0} Real Real.instMax
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                  (Real.log
                    (Real.log
                      (@Nat.cast.{0} Real Real.instNatCast
                        (@Max.max.{0} Nat Nat.instMax (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                          m)))))))
            (DecrAlmostLinearSSSP.Decremental.computableCutQuality N m))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (qualityPower : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) qualityPower →
    ∀ (impl : DecrAlmostLinearSSSP.Decremental.CutImplementation) (K0 C : Real) (h Γ a : Nat → Real),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C →
        @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (h
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)) →
          @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              (Γ
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)) →
            @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                (a
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)) →
              @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                  K0 →
                @LE.le.{0} Real Real.instLE K0
                    (DecrAlmostLinearSSSP.Decremental.computableCutQuality qualityPower
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)) →
                  DecrAlmostLinearSSSP.Decremental.ImplementsCut impl
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                        (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                      K0
                      (h
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size))
                      (Γ
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@OfNat.ofNat.{0} Real (nat_lit 2)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                            (@Nat.cast.{0} Real Real.instNatCast b.input.size)))
                        (a
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)))
                      (@HPow.hPow.{0, 0, 0} Real Int Real
                        (@instHPow.{0, 0} Real Int
                          (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                        (DecrAlmostLinearSSSP.Decremental.computableCutQuality qualityPower
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size))
                        (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))))) →
                    DecrAlmostLinearSSSP.Decremental.Maintains
                      (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.coreProgram qualityPower impl.program)
                      (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.coreConstant b.weightExponent qualityPower
                        impl.program C)
                      (DecrAlmostLinearSSSP.Decremental.coreRuntimeOverhead h Γ a qualityPower)
                      (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) Bool.false b.input)) ∧ ((∀ (d N : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program) (C : Real),
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C →
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.coreConstant d N p C)) ∧ ((∀ (d : Nat),
  (∃ impl K h Γ a C,
      And (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C)
        (And (DecrAlmostLinearSSSP.Decremental.Subpolynomial K)
          (And (DecrAlmostLinearSSSP.Decremental.Subpolynomial h)
            (And (DecrAlmostLinearSSSP.Decremental.Subpolynomial Γ)
              (And (DecrAlmostLinearSSSP.Decremental.Subpolynomial a)
                (And
                  (∀ (m : Nat),
                    And
                      (@LE.le.{0} Real Real.instLE
                        (@OfNat.ofNat.{0} Real (nat_lit 32)
                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
                            (@Nat.instAtLeastTwoHAddOfNat
                              (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
                        (K m))
                      (@LE.le.{0} Real Real.instLE (K m)
                        (Real.rpow
                          (@OfNat.ofNat.{0} Real (nat_lit 2)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
                              ((Real.log
                                    (@Nat.cast.{0} Real Real.instNatCast
                                      (@Max.max.{0} Nat Nat.instMax
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))).rpow
                                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                  (@OfNat.ofNat.{0} Real (nat_lit 5)
                                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 5) Real.instNatCast
                                      (@Nat.instAtLeastTwoHAddOfNat
                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                        (@Nat.instNeZeroSucc
                                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                                  (@OfNat.ofNat.{0} Real (nat_lit 6)
                                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 6) Real.instNatCast
                                      (@Nat.instAtLeastTwoHAddOfNat
                                        (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                                        (@Nat.instNeZeroSucc
                                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))))))
                            (@Max.max.{0} Real Real.instMax
                              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                              (Real.log
                                (Real.log
                                  (@Nat.cast.{0} Real Real.instNatCast
                                    (@Max.max.{0} Nat Nat.instMax
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))))))))
                  (∀ (m : Nat) (ξ : Real),
                    @LT.lt.{0} Real Real.instLT
                        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ξ →
                      DecrAlmostLinearSSSP.Decremental.ImplementsCut impl m
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) d)
                          (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                        (K m) (h m) (Γ m)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
                            (@Nat.cast.{0} Real Real.instNatCast m))
                          (a m))
                        ξ))))))) →
    ∃ p C a,
      And (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C)
        (And (DecrAlmostLinearSSSP.Decremental.Subpolynomial a)
          (∀ (b : DecrAlmostLinearSSSP.Decremental.Core),
            @Eq.{1} Nat b.weightExponent d →
              DecrAlmostLinearSSSP.Decremental.Maintains p C a
                (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) Bool.false b.input))) ∧ (∀ (d : Nat),
  (∃ p C a,
      And (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C)
        (And (DecrAlmostLinearSSSP.Decremental.Subpolynomial a)
          (∀ (b : DecrAlmostLinearSSSP.Decremental.Core),
            @Eq.{1} Nat b.weightExponent
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) →
              DecrAlmostLinearSSSP.Decremental.Maintains p C a
                (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) Bool.false b.input))) →
    ∃ p C a queryBound,
      And (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C)
        (And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) queryBound)
          (And (DecrAlmostLinearSSSP.Decremental.Subpolynomial a)
            (And
              (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
                i.Valid →
                  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) i.n →
                    @LE.le.{0} Nat instLENat i.W
                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                          i.size d) →
                      @LT.lt.{0} Real Real.instLT
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                            (@Nat.cast.{0} Real Real.instNatCast i.size))
                          i.accuracy →
                        @LT.lt.{0} Real Real.instLT i.accuracy
                            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
                          DecrAlmostLinearSSSP.Decremental.Maintains p C a queryBound Bool.false i)
              (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
                @LE.le.{0} Real Real.instLE
                    (@OfNat.ofNat.{0} Real (nat_lit 32)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
                    K →
                  ∀ (choose : DecrAlmostLinearSSSP.Decremental.State b → DecrAlmostLinearSSSP.Decremental.CutReply b),
                    DecrAlmostLinearSSSP.Decremental.CutQuality b K choose →
                      ∀ (s : DecrAlmostLinearSSSP.Decremental.State b),
                        DecrAlmostLinearSSSP.Decremental.Attained b K choose s →
                          @LE.le.{0} Real Real.instLE
                            (@Nat.cast.{0} Real Real.instNatCast (@DecrAlmostLinearSSSP.Decremental.State.toggles b s))
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                    (@OfNat.ofNat.{0} Real (nat_lit 16)
                                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                                        (@Nat.instAtLeastTwoHAddOfNat
                                          (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                                          (@Nat.instNeZeroSucc
                                            (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))))))
                                    (@HPow.hPow.{0, 0, 0} Real Nat Real
                                      (@instHPow.{0, 0} Real Nat
                                        (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                                      K (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                  (DecrAlmostLinearSSSP.Decremental.A b))
                                (@Nat.cast.{0} Real Real.instNatCast b.input.size))
                              (Real.log
                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                      (@Nat.instAtLeastTwoHAddOfNat
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                        (@Nat.instNeZeroSucc
                                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                                  (DecrAlmostLinearSSSP.Decremental.Q b)))))))))))))))) := by
  exact ⟨⟨⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.CoreGuestGamma.real_frame,DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.edge_nat_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.edge_real_frame,DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.nat_frame⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.real_frame,DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.even_registers⟩,⟨DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.edge_body_eval,DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.EdgeInvariant.step⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.edge_loop_eval,DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.edge_start_eval⟩,⟨DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.edge_start_nat_frame,DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.EdgeInvariant.start⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.edge_pass_eval,DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.GammaInvariant.step⟩,⟨DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.gamma_loop_eval,⟨DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.GammaInvariant.start,DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.gamma_pass_eval⟩⟩⟩⟩⟩,⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.GammaInvariant.input_nat,DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.GammaInvariant.input_real⟩,⟨DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.eval_code,DecrAlmostLinearSSSP.Decremental.CoreInitialSaved.fields_eval⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.CoreInitialSaved.values,DecrAlmostLinearSSSP.Decremental.CoreInitialSaved.real_memory⟩,⟨DecrAlmostLinearSSSP.Decremental.CoreInitialSaved.frame,⟨DecrAlmostLinearSSSP.Decremental.CoreInitialSaved.nat_frame,DecrAlmostLinearSSSP.Decremental.CoreInitialSaved.real_frame⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.CoreInitialSaved.snapshot,DecrAlmostLinearSSSP.Decremental.CoreInitialSaved.nat_frame_code⟩,⟨DecrAlmostLinearSSSP.Decremental.CoreInitialSaved.real_frame_code,DecrAlmostLinearSSSP.Decremental.CoreInitialSaved.eval_code⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.CoreSource.initial_saved_image,DecrAlmostLinearSSSP.Decremental.CoreHost.guest_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.CoreHost.saved_frame,⟨DecrAlmostLinearSSSP.Decremental.CoreInitialize.boot_cut_input_eval,DecrAlmostLinearSSSP.Decremental.core_cut_start⟩⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.CoreInitialize.boot_cut_eval,DecrAlmostLinearSSSP.Decremental.CoreInitialize.boot_context_eval⟩,⟨DecrAlmostLinearSSSP.Decremental.cutLogHeight_tendsto,DecrAlmostLinearSSSP.Decremental.cutRoot_tendsto⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.cutRoot_real_tendsto,DecrAlmostLinearSSSP.Decremental.computableCutQuality_log_ratio⟩,⟨DecrAlmostLinearSSSP.Decremental.computableCutQuality_subpolynomial,DecrAlmostLinearSSSP.Decremental.computableCutQuality_ge_32⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.CoreNativeCut.initialize_eval,DecrAlmostLinearSSSP.Decremental.CoreNativeCut.coreProgram_query⟩,⟨DecrAlmostLinearSSSP.Decremental.CoreNativeCut.program_initialization,DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Ready.external_credit⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.CoreNativeCut.live_append_singleton,DecrAlmostLinearSSSP.Decremental.CoreNativeCut.program_update⟩,⟨DecrAlmostLinearSSSP.Decremental.CoreNativeCut.online,⟨DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Completed.correct,DecrAlmostLinearSSSP.Decremental.CoreRepair.stoppedBit_le_one⟩⟩⟩⟩⟩,⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.credit_bound,DecrAlmostLinearSSSP.Decremental.CoreNativeCut.dynamic_budget_arithmetic⟩,⟨DecrAlmostLinearSSSP.Decremental.coreLogOverhead_positive,DecrAlmostLinearSSSP.Decremental.coreLogOverhead_subpolynomial⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.core_A_near_linear,DecrAlmostLinearSSSP.Decremental.core_log_Q_near_linear⟩,⟨DecrAlmostLinearSSSP.Decremental.coreRuntimeOverhead_subpolynomial,⟨DecrAlmostLinearSSSP.Decremental.coreRuntimeOverhead_init_bound,DecrAlmostLinearSSSP.Decremental.coreRuntimeOverhead_dynamic_bound⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.RuntimeInvariant.toggle_count_near_linear,DecrAlmostLinearSSSP.Decremental.CoreNativeCut.scale_bounds⟩,⟨DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Completed.work_bound,DecrAlmostLinearSSSP.Decremental.cutRoot_quality_exponent⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.exists_computable_cut_quality_envelope,DecrAlmostLinearSSSP.Decremental.CoreNativeCut.maintains⟩,⟨DecrAlmostLinearSSSP.Decremental.CoreNativeCut.coreConstant_positive,⟨DecrAlmostLinearSSSP.Decremental.CoreNativeCut.normalized_core_from_cut,DecrAlmostLinearSSSP.Decremental.polynomial_from_normalized_core⟩⟩⟩⟩⟩⟩⟩
