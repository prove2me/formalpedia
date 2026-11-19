-- Prove2me | solution 1 for DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T17:36:26.358+00:00
-- url     : https://prove2.me/submissions/11c0e629-9e06-4c01-bba4-f9bc7088434b

import Definitions.Def_DecrAlmostLinearSSSP_CoreRAMFoundation
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_1
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
theorem DecrAlmostLinearSSSP.Decremental.Structured.eval_natural : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (d q : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.natural d q) s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    { realReg := s.realReg, natReg := @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natReg d q,
      realMem := s.realMem, natMem := s.natMem } := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.1.2.1.1.2
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
theorem DecrAlmostLinearSSSP.Decremental.Exact.Powers.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 248) (instOfNatNat (nat_lit 248))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 250) (instOfNatNat (nat_lit 250))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 252) (instOfNatNat (nat_lit 252))) →
        DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.Powers.code k := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.2.1.1.1.1.1
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
theorem DecrAlmostLinearSSSP.Decremental.Walk.erase_cycles : ∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {u v : Fin n}
  {es : List.{0} (Fin k)},
  @DecrAlmostLinearSSSP.Decremental.Walk n k g active u v es →
    ∃ fs,
      And (@DecrAlmostLinearSSSP.Decremental.Walk n k g active u v fs)
        (And (@List.Sublist.{0} (Fin k) fs es)
          (@List.Nodup.{0} (Fin n)
            (@List.cons.{0} (Fin n) u
              (@List.map.{0, 0} (Fin k) (Fin n) (@DecrAlmostLinearSSSP.Decremental.Digraph.head n k g) fs)))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.2.1.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.Reachable.trans : ∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {u v w : Fin n},
  @DecrAlmostLinearSSSP.Decremental.Reachable n k g active u v →
    @DecrAlmostLinearSSSP.Decremental.Reachable n k g active v w →
      @DecrAlmostLinearSSSP.Decremental.Reachable n k g active u w := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.exists_min_weight_walk : ∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (active : Finset.{0} (Fin k)) (w : Fin k → Real),
  (∀ (e : Fin k),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (w e)) →
    ∀ (u v : Fin n),
      @DecrAlmostLinearSSSP.Decremental.Reachable n k g active u v →
        ∃ es,
          And (@DecrAlmostLinearSSSP.Decremental.Walk n k g active u v es)
            (And (@LT.lt.{0} Nat instLTNat (@List.length.{0} (Fin k) es) n)
              (∀ (fs : List.{0} (Fin k)),
                @DecrAlmostLinearSSSP.Decremental.Walk n k g active u v fs →
                  @LE.le.{0} Real Real.instLE
                    (@List.sum.{0} Real Real.instAdd Real.instZero (@List.map.{0, 0} (Fin k) Real w es))
                    (@List.sum.{0} Real Real.instAdd Real.instZero (@List.map.{0, 0} (Fin k) Real w fs)))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.2.1.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.list_sum_ofReal : ∀ {k : Nat} (w : Fin k → Real),
  (∀ (e : Fin k),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (w e)) →
    ∀ (es : List.{0} (Fin k)),
      @Eq.{1} ENNReal
        (@List.sum.{0} ENNReal ENNReal.instAdd ENNReal.instZero
          (@List.map.{0, 0} (Fin k) ENNReal (fun e => ENNReal.ofReal (w e)) es))
        (ENNReal.ofReal (@List.sum.{0} Real Real.instAdd Real.instZero (@List.map.{0, 0} (Fin k) Real w es))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.2.2.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.distance_le_walk : ∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {u v : Fin n}
  {es : List.{0} (Fin k)},
  @DecrAlmostLinearSSSP.Decremental.Walk n k g active u v es →
    ∀ (w : Fin k → ENNReal),
      @LE.le.{0} ENNReal ENNReal.instLE (@DecrAlmostLinearSSSP.Decremental.distance n k g active w u v)
        (@List.sum.{0} ENNReal ENNReal.instAdd ENNReal.instZero (@List.map.{0, 0} (Fin k) ENNReal w es)) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.2.2.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.distance_min_weight : ∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (active : Finset.{0} (Fin k)) (w : Fin k → Real),
  (∀ (e : Fin k),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (w e)) →
    ∀ (u v : Fin n),
      @DecrAlmostLinearSSSP.Decremental.Reachable n k g active u v →
        ∃ es,
          And (@DecrAlmostLinearSSSP.Decremental.Walk n k g active u v es)
            (And (@LT.lt.{0} Nat instLTNat (@List.length.{0} (Fin k) es) n)
              (@Eq.{1} ENNReal
                (@DecrAlmostLinearSSSP.Decremental.distance n k g active (fun e => ENNReal.ofReal (w e)) u v)
                (ENNReal.ofReal (@List.sum.{0} Real Real.instAdd Real.instZero (@List.map.{0, 0} (Fin k) Real w es))))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.2.2.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.nat_weight_list_real : ∀ {k : Nat} (w : Fin k → Nat) (es : List.{0} (Fin k)),
  @Eq.{1} ENNReal
    (@List.sum.{0} ENNReal ENNReal.instAdd ENNReal.instZero
      (@List.map.{0, 0} (Fin k) ENNReal
        (fun e =>
          @Nat.cast.{0} ENNReal
            (@AddMonoidWithOne.toNatCast.{0} ENNReal
              (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
            (w e))
        es))
    (ENNReal.ofReal
      (@List.sum.{0} Real Real.instAdd Real.instZero
        (@List.map.{0, 0} (Fin k) Real (fun e => @Nat.cast.{0} Real Real.instNatCast (w e)) es))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.2.2.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.real_weight_le_walk_sum : ∀ {k : Nat} (w : Fin k → Nat) (es : List.{0} (Fin k)) (e : Fin k),
  @Membership.mem.{0, 0} (Fin k) (List.{0} (Fin k)) (@List.instMembership.{0} (Fin k)) es e →
    @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast (w e))
      (@List.sum.{0} Real Real.instAdd Real.instZero
        (@List.map.{0, 0} (Fin k) Real (fun e => @Nat.cast.{0} Real Real.instNatCast (w e)) es)) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.2.2.2.1.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.distance_top_of_unreachable : ∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (active : Finset.{0} (Fin k)) (w : Fin k → ENNReal)
  (u v : Fin n),
  Not (@DecrAlmostLinearSSSP.Decremental.Reachable n k g active u v) →
    @Eq.{1} ENNReal (@DecrAlmostLinearSSSP.Decremental.distance n k g active w u v)
      (@Top.top.{0} ENNReal ENNReal.instTop) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.2.2.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.input_reachable_distance_bounds : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (active : Finset.{0} (Fin i.k)) (v : Fin i.n),
      @DecrAlmostLinearSSSP.Decremental.Reachable i.n i.k i.graph active i.source v →
        @Ne.{1} (Fin i.n) v i.source →
          ∃ d,
            And
              (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) d)
              (And
                (@LE.le.{0} Real Real.instLE d
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@Nat.cast.{0} Real Real.instNatCast i.n) (@Nat.cast.{0} Real Real.instNatCast i.W)))
                (@Eq.{1} ENNReal
                  (@DecrAlmostLinearSSSP.Decremental.distance i.n i.k i.graph active
                    (fun e =>
                      @Nat.cast.{0} ENNReal
                        (@AddMonoidWithOne.toNatCast.{0} ENNReal
                          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                        (i.weight e))
                    i.source v)
                  (ENNReal.ofReal d))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.2.2.2.2.2.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.OnlineRun.length : ∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {i : DecrAlmostLinearSSSP.Decremental.Input} {ds : List.{0} (Fin i.k)}
  {cs : List.{0} DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.OnlineRun p i ds cs →
    @Eq.{1} Nat (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Machine cs)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_8.2.2.1.2.2.2.2
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
theorem DecrAlmostLinearSSSP.Decremental.ShadowDataRep.scratch8 : ∀ {B F : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F s g →
    ∀ (x : Nat),
      DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F
        { realReg := s.realReg,
          natReg :=
            @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) x,
          realMem := s.realMem, natMem := s.natMem }
        g := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_2.1.2.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.ShadowDataRep.halt_flag : ∀ {B F : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F s g →
    @LE.le.{0} Nat instLENat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        (@ite.{1} Nat (@Eq.{1} Bool g.halted Bool.true) (instDecidableEqBool g.halted Bool.true)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_2.1.2.2.1.2.2.2
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
theorem DecrAlmostLinearSSSP.Decremental.Fill.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 116) (instOfNatNat (nat_lit 116))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 118) (instOfNatNat (nat_lit 118))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Fill.code k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_3.1.2.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.Fill.real_frame : ∀ (k : Nat), DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Fill.code k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_3.1.2.1.2.1.2
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
theorem DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail.execute : ∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {c : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail (DecrAlmostLinearSSSP.Decremental.registerBound p.code) c →
    ∀ (t : Nat),
      DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail (DecrAlmostLinearSSSP.Decremental.registerBound p.code)
        (DecrAlmostLinearSSSP.Decremental.execute p c t) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_3.2.2.1.2.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.SourceSnapshot.nat_frame : ∀ (N k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 54) (instOfNatNat (nat_lit 54))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.SourceSnapshot.code N) k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_5.2.1.2.1.2.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.Native.PublicFrame.trans : ∀ {l : DecrAlmostLinearSSSP.Decremental.Native.PointerLayout} {n : Nat}
  {s t u : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.PublicFrame l n s t →
    DecrAlmostLinearSSSP.Decremental.Native.PublicFrame l n t u →
      DecrAlmostLinearSSSP.Decremental.Native.PublicFrame l n s u := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_8.2.2.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.PointerBases.start : ∀ {record pointer flags list cost : Nat} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.PointerBases record pointer flags list s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Native.pointerStart s cost t →
      DecrAlmostLinearSSSP.Decremental.Native.PointerBases record pointer flags list t := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_9.1.1.1.1.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.SelectedRead.real_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.SelectedRead.code k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_9.2.1.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.distance_self : ∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (active : Finset.{0} (Fin k)) (w : Fin k → ENNReal)
  (s : Fin n),
  @Eq.{1} ENNReal (@DecrAlmostLinearSSSP.Decremental.distance n k g active w s s)
    (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero)) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_9.2.2.1.2.2.2.2
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
theorem DecrAlmostLinearSSSP.Decremental.Native.ReportFrame.bank : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B reserve N j : Nat}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.ReportFrame i B reserve N j s t →
    ∀ (q v : Nat),
      And
        (@Eq.{1} Nat (t.natMem (DecrAlmostLinearSSSP.Decremental.bankAddress B q v))
          (s.natMem (DecrAlmostLinearSSSP.Decremental.bankAddress B q v)))
        (@Eq.{1} Real (t.realMem (DecrAlmostLinearSSSP.Decremental.bankAddress B q v))
          (s.realMem (DecrAlmostLinearSSSP.Decremental.bankAddress B q v))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_11.1.2.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.Native.ReportFrame.source : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B reserve N j q : Nat}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.Native.ReportFrame i B reserve N j s t →
    DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B q s g.natMem g.realMem →
      DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B q t g.natMem g.realMem := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_11.1.2.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.action_eval : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (B reserve N : Nat),
      @LE.le.{0} Nat instLENat i.n B →
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
                ∀ (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (logical : Nat)
                  (g : DecrAlmostLinearSSSP.Decremental.Machine),
                  DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B
                      (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) s g.natMem g.realMem →
                    (∀ (z : Fin i.n),
                        And
                          (@LE.le.{0} Nat instLENat (g.natMem (@Fin.val i.n z))
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          (@Eq.{1} Nat (g.natMem (@Fin.val i.n z))
                              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                            @LE.le.{0} Real Real.instLE
                              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                              (g.realMem (@Fin.val i.n z)))) →
                      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 198) (instOfNatNat (nat_lit 198))))
                          (DecrAlmostLinearSSSP.Decremental.bankAddress B
                            (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) logical) →
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
                                  @Eq.{1} Nat
                                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 212) (instOfNatNat (nat_lit 212))))
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (DecrAlmostLinearSSSP.Decremental.bankFactor
                                            (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j))
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) i.n)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
                                    ∃ cost t ys,
                                      And
                                        (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                          DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.action s cost t)
                                        (And
                                          (@LE.le.{0} Nat instLENat cost
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (DecrAlmostLinearSSSP.Decremental.dispatchCharge
                                                      DecrAlmostLinearSSSP.Decremental.ScaledCeiling.ceilingProgram.code)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))
                                                      (DecrAlmostLinearSSSP.Decremental.utilityDepth i.size))
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))))
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
                                                  (DecrAlmostLinearSSSP.Decremental.pointerTravel i a
                                                    (DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.events i B j
                                                      g
                                                      (DecrAlmostLinearSSSP.Decremental.bankAddress B
                                                        (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)
                                                        logical)))))
                                              (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56)))))
                                          (And
                                            (DecrAlmostLinearSSSP.Decremental.Native.AdapterMemory i B reserve N
                                              (DecrAlmostLinearSSSP.Decremental.adapterTrace i a
                                                (DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.events i B j g
                                                  (DecrAlmostLinearSSSP.Decremental.bankAddress B
                                                    (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)
                                                    logical)))
                                              ys t)
                                            (And
                                              (@LE.le.{0} Nat instLENat (@List.length.{0} (Fin i.n) ys)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@List.length.{0} (Fin i.n) xs)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (DecrAlmostLinearSSSP.Decremental.Native.ReportFrame i B reserve N
                                                (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) s t)))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_11.1.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.Queue.head : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B reserve N offset address : Nat} {rest : List.{0} Nat}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.Queue i B reserve N offset (@List.cons.{0} Nat address rest) s →
    @Eq.{1} Nat (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 210) (instOfNatNat (nat_lit 210))))) address := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_11.2.1.1.1.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.Native.SourceUpdateFrame.trans : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B reserve N j : Nat}
  {s t u : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.SourceUpdateFrame i B reserve N j s t →
    DecrAlmostLinearSSSP.Decremental.Native.SourceUpdateFrame i B reserve N j t u →
      DecrAlmostLinearSSSP.Decremental.Native.SourceUpdateFrame i B reserve N j s u := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_12.1.1.1.2.1.2
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
lemma accumulate_eval (acc counter limit factor unit : ℕ)
    (hac : acc ≠ counter) (hal : acc ≠ limit) (haf : acc ≠ factor) (hau : acc ≠ unit)
    (hcl : counter ≠ limit) (hcf : counter ≠ factor) (hcu : counter ≠ unit)
    (s : Data) (q : ℕ) (hlim : s.natReg limit = s.natReg counter+q) (hone : s.natReg unit = 1) :
    ∃ t, Eval (accumulate acc counter limit factor unit) s (4*q+2) t ∧
      t.natReg counter = s.natReg counter+q ∧ t.natReg acc = s.natReg acc+q*s.natReg factor := by
  induction q generalizing s with
  | zero =>
    have ht : ¬(Test.natLess counter limit).holds s := by simp only [Test.holds,hlim,Nat.add_zero,lt_self_iff_false,not_false_eq_true]
    exact ⟨s,Eval.loopNo s ht,by simp,by simp⟩
  | succ q ih =>
    let a : Data := {s with natReg := Function.update s.natReg acc (s.natReg acc+s.natReg factor)}
    let b : Data := {a with natReg := Function.update a.natReg counter (a.natReg counter+a.natReg unit)}
    have hbLim : b.natReg limit = b.natReg counter+q := by
      simp only [b,a,Function.update_self,Function.update_of_ne (Ne.symm hal),Function.update_of_ne (Ne.symm hcl),Function.update_of_ne (Ne.symm hac),Function.update_of_ne (Ne.symm hau),hone]
      omega
    have hbOne : b.natReg unit = 1 := by simp [b,a,Function.update_of_ne (Ne.symm hau),Function.update_of_ne (Ne.symm hcu),hone]
    obtain ⟨t,ht,htc,hta⟩ := ih b hbLim hbOne
    have hsTest : (Test.natLess counter limit).holds s := by change s.natReg counter < s.natReg limit;omega
    have heBody : Eval (.seq (nadd acc acc factor) (nadd counter counter unit)) s 2 b :=
      Eval.seq (eval_nadd s acc acc factor) (eval_nadd a counter counter unit)
    refine ⟨t,?_,?_,?_⟩
    · have he := Eval.loopYes hsTest heBody ht
      have heCost : 2+(4*q+2)+2 = 4*(q+1)+2 := by omega
      simpa only [accumulate,heCost] using he
    · rw [htc]
      simp only [b,a,Function.update_self,Function.update_of_ne (Ne.symm hac),Function.update_of_ne (Ne.symm hau),hone]
      omega
    · rw [hta]
      simp only [b,a,Function.update_self,Function.update_of_ne hac,Function.update_of_ne (Ne.symm haf),Function.update_of_ne (Ne.symm hcf)]
      ring
end DecrAlmostLinearSSSP.Decremental.Structured
end s37
section s38
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
attribute [local instance] Classical.propDecidable
lemma conditionalOne_eval (test : Test) (k : ℕ) (s : Data) :
    Eval (conditionalOne test k) s 2 (conditionalOneState test k s) := by
  classical
  by_cases ht : test.holds s
  · simpa only [conditionalOne,conditionalOneState,if_pos ht] using Eval.branchYes ht (eval_natural s k 1)
  · simpa only [conditionalOne,conditionalOneState,if_neg ht] using Eval.branchNo ht (Eval.skip s)
lemma conditionalOneState_mem (test : Test) (k : ℕ) (s : Data) :
    (conditionalOneState test k s).natMem = s.natMem ∧ (conditionalOneState test k s).realMem = s.realMem := by
  unfold conditionalOneState
  split <;> exact ⟨rfl,rfl⟩
lemma conditionalOneState_nat (test : Test) (k : ℕ) (s : Data) :
    (conditionalOneState test k s).natReg k = if test.holds s then 1 else s.natReg k := by
  unfold conditionalOneState
  split <;> simp_all
lemma conditionalOneState_nat_other (test : Test) (k j : ℕ) (s : Data) (hne : j ≠ k) :
    (conditionalOneState test k s).natReg j = s.natReg j := by
  unfold conditionalOneState
  split <;> simp_all
lemma conditionalOneState_real (test : Test) (k : ℕ) (s : Data) :
    (conditionalOneState test k s).realReg = s.realReg := by
  unfold conditionalOneState
  split <;> rfl
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
lemma old_edge_active (i : Input) (a : Finset (Fin i.k)) (e : Fin i.k) :
    oldEdge i e ∈ active i a ↔ e ∈ a := by
  classical
  simp [active,oldEdge]
lemma added_edge_active (i : Input) (a : Finset (Fin i.k)) (v : Fin i.n) :
    addedEdge i v ∈ active i a := by
  classical
  simp [active,addedEdge]
lemma oldEdge_injective (i : Input) : Function.Injective (oldEdge i) := by
  intro a b he
  apply Fin.ext
  exact congrArg (fun z : Fin (i.k+i.n) => z.val) he
lemma active_live (i : Input) (ds : List (Fin i.k)) :
    active i (live ds) = live (ds.map (oldEdge i)) := by
  classical
  ext e
  by_cases he : e.val < i.k
  · let f : Fin i.k := ⟨e.val,he⟩
    have hef : e = oldEdge i f := Fin.ext rfl
    rw [hef,old_edge_active]
    simp [live,List.mem_map,oldEdge_injective i]
  · have hn : ∀ f : Fin i.k, oldEdge i f ≠ e := by
      intro f hf
      have hv := congrArg Fin.val hf
      exact he (hv ▸ f.isLt)
    simp [active,he,live,List.mem_map,hn]
lemma walk_lift (i : Input) (a : Finset (Fin i.k)) {u v : Fin i.n} {es : List (Fin i.k)}
    (hw : Walk i.graph a u v es) (hsource : ∀ e ∈ es, i.graph.head e ≠ i.source) :
    Walk (input i).graph (active i a) (oldVertex i u) (oldVertex i v) (es.map (oldEdge i)) := by
  induction hw with
  | nil v => exact Walk.nil _
  | @cons u v es e he hw ih =>
    have hh : head i (oldEdge i e) = oldVertex i (i.graph.head e) := by
      rw [old_edge_head,if_neg (hsource e List.mem_cons_self)]
    have hi := ih (fun f hf => hsource f (List.mem_cons_of_mem e hf))
    have hi' : Walk (input i).graph (active i a) ((input i).graph.head (oldEdge i e)) (oldVertex i v) (es.map (oldEdge i)) := by simpa only [input,hh] using hi
    have hstep := Walk.cons (u := oldVertex i (i.graph.tail e)) (g := (input i).graph) (oldEdge i e) ((old_edge_active i a e).mpr he) hi'
    simpa only [input,old_edge_tail,hh,List.map_cons] using hstep
lemma walk_from_sink (i : Input) (a : Finset (Fin (i.k+i.n))) {u v : Fin (i.n+1)}
    {es : List (Fin (i.k+i.n))} (hw : Walk (input i).graph a u v es) (hs : u = sink i) : v = sink i := by
  cases hw with
  | nil => exact hs
  | cons e he h => exact False.elim (tail_ne_sink i e hs)
lemma walk_project (i : Input) (a : Finset (Fin i.k)) {u w : Fin (i.n+1)}
    {es : List (Fin (i.k+i.n))} (hw : Walk (input i).graph (active i a) u w es)
    (hall : ∀ e ∈ es, e.val < i.k) (v : Fin i.n) (hwv : w = oldVertex i v) :
    ∃ (x : Fin i.n) (fs : List (Fin i.k)), u = oldVertex i x ∧
      Walk i.graph a x v fs ∧ es = fs.map (oldEdge i) := by
  induction hw generalizing v with
  | nil w =>
    exact ⟨v,[],hwv,Walk.nil v,rfl⟩
  | @cons u w es e he hw ih =>
    obtain ⟨x,fs,hx,hfs,hes⟩ := ih (fun f hf => hall f (List.mem_cons_of_mem e hf)) v hwv
    let f : Fin i.k := ⟨e.val,hall e List.mem_cons_self⟩
    have hef : e = oldEdge i f := Fin.ext rfl
    have hhead : head i e = oldVertex i x := hx
    have hne : i.graph.head f ≠ i.source := by
      intro hn
      rw [hef,old_edge_head,if_pos hn] at hhead
      exact sink_ne_old i x hhead
    have hfx : i.graph.head f = x := by
      rw [hef,old_edge_head,if_neg hne] at hhead
      apply Fin.ext
      exact congrArg (fun z : Fin (i.n+1) => z.val) hhead
    have hf : f ∈ a := (old_edge_active i a f).mp (hef ▸ he)
    refine ⟨i.graph.tail f,f::fs,?_,?_,?_⟩
    · change tail i e = oldVertex i (i.graph.tail f)
      rw [hef,old_edge_tail]
    · rw [← hfx] at hfs
      exact Walk.cons (u := i.graph.tail f) f hf hfs
    · simp only [List.map_cons,hes,hef]
end DecrAlmostLinearSSSP.Decremental.Normalize
end s47
section s48
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
lemma minimum_walk_avoids_source {n k : ℕ} (g : Digraph n k) (a : Finset (Fin k))
    (w : Fin k → ℝ) (hw : ∀ e, 0 ≤ w e) (s v : Fin n) (hr : Reachable g a s v) :
    ∃ es, Walk g a s v es ∧ es.length < n ∧ (∀ e ∈ es, g.head e ≠ s) ∧
      distance g a (fun e => ENNReal.ofReal (w e)) s v = ENNReal.ofReal ((es.map w).sum) := by
  classical
  obtain ⟨fs,hfs,_,hmin⟩ := exists_min_weight_walk g a w hw s v hr
  obtain ⟨es,hes,hsub,hn⟩ := hfs.erase_cycles
  have hlen : es.length < n := by
    have hl := hn.length_le_card
    simpa only [List.length_cons,List.length_map,Fintype.card_fin,Nat.succ_le_iff] using hl
  have havoid : ∀ e ∈ es, g.head e ≠ s := by
    intro e he hh
    have hnot := (List.nodup_cons.mp hn).1
    apply hnot
    rw [← hh]
    exact List.mem_map.mpr ⟨e,he,rfl⟩
  have hcost : ∀ ts, Walk g a s v ts → (es.map w).sum ≤ (ts.map w).sum := by
    intro ts hts
    have hle := List.Sublist.sum_le_sum (hsub.map w)
      (by intro x hx;obtain ⟨e,_,rfl⟩ := List.mem_map.mp hx;exact hw e)
    exact hle.trans (hmin ts hts)
  refine ⟨es,hes,hlen,havoid,le_antisymm ?_ ?_⟩
  · simpa only [list_sum_ofReal w hw] using distance_le_walk hes (fun e => ENNReal.ofReal (w e))
  · apply le_iInf
    intro ts
    apply le_iInf
    intro hts
    rw [list_sum_ofReal w hw]
    exact ENNReal.ofReal_le_ofReal (hcost ts hts)
end DecrAlmostLinearSSSP.Decremental
end s48
section s49
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Normalize
lemma lifted_weight (i : Input) (es : List (Fin i.k)) :
    ((es.map (oldEdge i)).map (fun e => (weight i e : ℝ))).sum =
      (es.map (fun e => (i.weight e : ℝ))).sum := by
  simp only [List.map_map,Function.comp_def,old_edge_weight]
lemma distance_upper (i : Input) (a : Finset (Fin i.k)) (v : Fin i.n)
    (hr : Reachable i.graph a i.source v) :
    distance (input i).graph (active i a) (fun e => (weight i e : ℝ≥0∞)) (source i) (oldVertex i v) ≤
      distance i.graph a (fun e => (i.weight e : ℝ≥0∞)) i.source v := by
  obtain ⟨es,hes,hlen,havoid,hd⟩ := minimum_walk_avoids_source i.graph a
    (fun e => (i.weight e : ℝ)) (fun e => Nat.cast_nonneg _) i.source v hr
  have hl := walk_lift i a hes havoid
  have hu := distance_le_walk hl (fun e => (weight i e : ℝ≥0∞))
  dsimp only [input] at hu
  rw [nat_weight_list_real (weight i) (es.map (oldEdge i)),lifted_weight] at hu
  simpa only [input,source,ENNReal.ofReal_natCast] using hu.trans_eq hd.symm
lemma reachable_active (i : Input) (a : Finset (Fin i.k)) (v : Fin (i.n+1)) :
    Reachable (input i).graph (active i a) (source i) v := by
  by_cases he : v = source i
  · subst v;exact ⟨[],Walk.nil _⟩
  · obtain ⟨j,hj⟩ := target_surjective i v he
    have hw := Walk.cons (u := source i) (g := (input i).graph) (active := active i a)
      (addedEdge i j) (added_edge_active i a j) (Walk.nil ((input i).graph.head (addedEdge i j)))
    refine ⟨[addedEdge i j],?_⟩
    change Walk (input i).graph (active i a) (tail i (addedEdge i j)) (head i (addedEdge i j)) [addedEdge i j] at hw
    rwa [added_edge_tail,added_edge_head,hj] at hw
lemma distance_lower_guarded (i : Input) (a : Finset (Fin i.k)) (v : Fin i.n)
    (hguard : distance (input i).graph (active i a) (fun e => (weight i e : ℝ≥0∞))
      (source i) (oldVertex i v) < (sentinel i : ℝ≥0∞)) :
    distance i.graph a (fun e => (i.weight e : ℝ≥0∞)) i.source v ≤
      distance (input i).graph (active i a) (fun e => (weight i e : ℝ≥0∞)) (source i) (oldVertex i v) := by
  obtain ⟨es,hes,hlen,hd⟩ := distance_min_weight (input i).graph (active i a)
    (fun e => (weight i e : ℝ)) (fun e => Nat.cast_nonneg _) (source i) (oldVertex i v) (reachable_active i a _)
  have hd' : distance (input i).graph (active i a) (fun e => (weight i e : ℝ≥0∞)) (source i) (oldVertex i v) =
      ENNReal.ofReal ((es.map (fun e => (weight i e : ℝ))).sum) := by
    simpa only [input,ENNReal.ofReal_natCast] using hd
  rw [hd'] at hguard ⊢
  have hcost : (es.map (fun e => (weight i e : ℝ))).sum < (sentinel i : ℝ) := by
    have hh := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (show 0 ≤ (es.map (fun e => (weight i e : ℝ))).sum by exact List.sum_nonneg (by intro x hx;obtain ⟨e,_,rfl⟩ := List.mem_map.mp hx;exact Nat.cast_nonneg _))).mp
      (show ENNReal.ofReal ((es.map (fun e => (weight i e : ℝ))).sum) < ENNReal.ofReal (sentinel i) by simpa only [ENNReal.ofReal_natCast] using hguard)
    exact hh
  have hall : ∀ e ∈ es, e.val < i.k := by
    intro e he
    by_contra hn
    have hw : weight i e = sentinel i := by simp [weight,hn]
    have hle := real_weight_le_walk_sum (weight i) es e he
    rw [hw] at hle
    linarith
  obtain ⟨x,fs,hx,hfs,heq⟩ := walk_project i a hes hall v rfl
  have hxs : x = i.source := by
    apply Fin.ext
    exact (congrArg (fun z : Fin (i.n+1) => z.val) hx).symm
  subst x
  have hlo := distance_le_walk hfs (fun e => (i.weight e : ℝ≥0∞))
  rw [nat_weight_list_real] at hlo
  rw [heq,lifted_weight]
  exact hlo
end DecrAlmostLinearSSSP.Decremental.Normalize
end s49
section s50
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Normalize
lemma distance_self (i : Input) (a : Finset (Fin i.k)) :
    distance i.graph a (fun e => (i.weight e : ℝ≥0∞)) i.source i.source = 0 := by
  apply le_antisymm _ zero_le
  simpa only [List.map_nil,List.sum_nil] using distance_le_walk (Walk.nil i.source : Walk i.graph a i.source i.source []) (fun e => (i.weight e : ℝ≥0∞))
lemma finite_distance_bound (i : Input) (hi : i.Valid) (a : Finset (Fin i.k)) (v : Fin i.n)
    (hr : Reachable i.graph a i.source v) :
    distance i.graph a (fun e => (i.weight e : ℝ≥0∞)) i.source v ≤ (i.n*i.W : ℕ) := by
  by_cases he : v = i.source
  · subst v;rw [distance_self];exact zero_le
  · obtain ⟨d,hd0,hdB,hd⟩ := input_reachable_distance_bounds i hi a v hr he
    rw [hd]
    rw [← ENNReal.ofReal_natCast (i.n*i.W)]
    apply ENNReal.ofReal_le_ofReal
    simpa only [Nat.cast_mul] using hdB
lemma finite_sentinel_gap (i : Input) (hi : i.Valid) :
    ((i.n*i.W : ℕ) : ℝ≥0∞) < (sentinel i : ℝ≥0∞) := by
  have hW := hi.2.2.1
  have hn := i.source.isLt
  have hlt : i.n*i.W < sentinel i := by dsimp [sentinel];nlinarith
  exact_mod_cast hlt
lemma distance_eq_original (i : Input) (hi : i.Valid) (a : Finset (Fin i.k)) (v : Fin i.n)
    (hr : Reachable i.graph a i.source v) :
    distance (input i).graph (active i a) (fun e => (weight i e : ℝ≥0∞)) (source i) (oldVertex i v) =
      distance i.graph a (fun e => (i.weight e : ℝ≥0∞)) i.source v := by
  have hu := distance_upper i a v hr
  have hg := hu.trans_lt ((finite_distance_bound i hi a v hr).trans_lt (finite_sentinel_gap i hi))
  exact le_antisymm hu (distance_lower_guarded i a v hg)
lemma unreachable_distance_gap (i : Input) (a : Finset (Fin i.k)) (v : Fin i.n)
    (hr : ¬ Reachable i.graph a i.source v) :
    (sentinel i : ℝ≥0∞) ≤ distance (input i).graph (active i a)
      (fun e => (weight i e : ℝ≥0∞)) (source i) (oldVertex i v) := by
  by_contra hn
  have hg := lt_of_not_ge hn
  have hl := distance_lower_guarded i a v hg
  rw [distance_top_of_unreachable i.graph a _ i.source v hr] at hl
  have ht := top_le_iff.mp hl
  rw [ht] at hg
  exact (not_lt_of_ge le_top) hg
end DecrAlmostLinearSSSP.Decremental.Normalize
end s50
section s51
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Normalize
lemma cutoff_positive (i : Input) (hi : i.Valid) : 0 < cutoff i := by
  have hw := hi.2.2.1
  unfold cutoff
  positivity
lemma finite_cutoff_gap (i : Input) (hi : i.Valid) :
    ENNReal.ofReal (1+i.accuracy)*(i.n*i.W : ℕ) < (cutoff i : ℝ≥0∞) := by
  have heps := hi.2.2.2.2.1
  have hw := hi.2.2.1
  have hc : ENNReal.ofReal (1+i.accuracy) ≤ (2:ℝ≥0∞) := by
    exact (ENNReal.ofReal_le_ofReal (by linarith : 1+i.accuracy ≤ 2)).trans_eq (by norm_num)
  calc
    _ ≤ (2:ℝ≥0∞)*((i.n*i.W : ℕ):ℝ≥0∞) := mul_le_mul_left hc _
    _ < (cutoff i : ℝ≥0∞) := by
      have hn : 2*(i.n*i.W) < cutoff i := by unfold cutoff;nlinarith
      exact_mod_cast hn
lemma sanitize_correct (i : Input) (hi : i.Valid) (a : Finset (Fin i.k)) (v : Fin i.n) (D : ℝ≥0∞)
    (hl : distance (input i).graph (active i a) (fun e => (weight i e : ℝ≥0∞)) (source i) (oldVertex i v) ≤ D)
    (hu : D ≤ ENNReal.ofReal (1+i.accuracy)*distance (input i).graph (active i a)
      (fun e => (weight i e : ℝ≥0∞)) (source i) (oldVertex i v)) :
    distance i.graph a (fun e => (i.weight e : ℝ≥0∞)) i.source v ≤ sanitize i D ∧
    sanitize i D ≤ ENNReal.ofReal (1+i.accuracy)*distance i.graph a (fun e => (i.weight e : ℝ≥0∞)) i.source v ∧
    (sanitize i D = ⊤ ↔ ¬Reachable i.graph a i.source v) := by
  classical
  by_cases hr : Reachable i.graph a i.source v
  · rw [distance_eq_original i hi a v hr] at hl hu
    have hD : D < (cutoff i : ℝ≥0∞) :=
      hu.trans_lt ((mul_le_mul_right (finite_distance_bound i hi a v hr) _).trans_lt (finite_cutoff_gap i hi))
    have hsan : sanitize i D = D := if_neg (not_lt_of_ge hD.le)
    rw [hsan]
    refine ⟨hl,hu,?_⟩
    simp only [hr,not_true,iff_false]
    exact ne_top_of_lt hD
  · have hgap := (unreachable_distance_gap i a v hr).trans hl
    have hcs : (cutoff i : ℝ≥0∞) < (sentinel i : ℝ≥0∞) := by
      have hn : cutoff i < sentinel i := by
        have hw := hi.2.2.1
        unfold cutoff sentinel
        nlinarith
      exact_mod_cast hn
    have hsan : sanitize i D = ⊤ := if_pos (hcs.trans_le hgap)
    rw [hsan,distance_top_of_unreachable i.graph a _ i.source v hr]
    refine ⟨le_rfl,?_,by simp [hr]⟩
    rw [ENNReal.mul_top]
    exact (ENNReal.ofReal_pos.mpr (by linarith only [hi.2.2.2.1] : 0 < 1+i.accuracy)).ne'
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
lemma instruction_eval {action : Instruction → Cmd} {bound : Instruction → ℕ}
    {P : Data → Machine → Prop} {B F : ℕ} (spec : ActionSpec action bound P B F)
    (s : Data) (g : Machine) (h : MachineRep B F s g) (hp : P s g) (ins : Instruction) :
    ∃ cost t, Eval (instruction action g.pc ins) s cost t ∧ cost ≤ bound ins+2 ∧
      MachineRep B F t (instructionEffect ins {g with pc := g.pc+1,work := g.work+1}) ∧
      P t (instructionEffect ins {g with pc := g.pc+1,work := g.work+1}) := by
  let t : Data := {s with natReg := Function.update (Function.update s.natReg 2 (g.pc+1)) 3 (s.natReg 3+1)}
  have he : Eval (.seq (natural 2 (g.pc+1)) (nadd 3 3 1)) s 2 t := by simpa only [h.2.2.1] using eval_shadow_header s g.pc
  have ht : MachineRep B F t {g with pc := g.pc+1,work := g.work+1} := by
    refine ⟨h.1.header h.2.2.1,?_,?_,?_,h.2.2.2.2.1,?_⟩
    all_goals simp only [t,Function.update_of_ne (by decide : (0:ℕ) ≠ 3),Function.update_of_ne (by decide : (0:ℕ) ≠ 2),Function.update_of_ne (by decide : (1:ℕ) ≠ 3),Function.update_of_ne (by decide : (1:ℕ) ≠ 2),Function.update_of_ne (by decide : (7:ℕ) ≠ 3),Function.update_of_ne (by decide : (7:ℕ) ≠ 2),Function.update_of_ne (by decide : (4:ℕ) ≠ 3),Function.update_of_ne (by decide : (4:ℕ) ≠ 2)]
    all_goals first | exact h.2.1 | exact h.2.2.1 | exact h.2.2.2.1 | exact h.2.2.2.2.2
  obtain ⟨cost,u,hu,hcost,hrep,hP⟩ := spec.action_eval t _ ins ht (spec.header s g hp)
  exact ⟨2+cost,u,Eval.seq he hu,by omega,hrep,hP⟩
lemma dispatch_eval {action : Instruction → Cmd} {bound : Instruction → ℕ}
    {P : Data → Machine → Prop} {B F : ℕ} (spec : ActionSpec action bound P B F)
    (code : List Instruction) (start : ℕ) (s : Data) (g : Machine)
    (h : MachineRep B F s g) (hp : P s g) (hstart : start ≤ g.pc) (ins : Instruction)
    (hins : code[g.pc-start]? = some ins) :
    ∃ cost t, Eval (dispatch action start code) s cost t ∧ cost ≤ charge bound code ∧
      MachineRep B F t (instructionEffect ins {g with pc := g.pc+1,work := g.work+1}) ∧
      P t (instructionEffect ins {g with pc := g.pc+1,work := g.work+1}) := by
  induction code generalizing start s with
  | nil => simp at hins
  | cons head rest ih =>
    let t : Data := {s with natReg := Function.update s.natReg 8 (start+1)}
    have ht : MachineRep B F t g := by
      refine ⟨h.1.scratch8 _,?_,?_,?_,h.2.2.2.2.1,?_⟩
      all_goals simp only [t,Function.update_of_ne (by decide : (0:ℕ) ≠ 8),Function.update_of_ne (by decide : (1:ℕ) ≠ 8),Function.update_of_ne (by decide : (7:ℕ) ≠ 8),Function.update_of_ne (by decide : (4:ℕ) ≠ 8)]
      all_goals first | exact h.2.1 | exact h.2.2.1 | exact h.2.2.2.1 | exact h.2.2.2.2.2
    have htP := spec.scratch s g (start+1) hp
    by_cases hpc : g.pc = start
    · have hins' : head = ins := by simpa only [hpc,Nat.sub_self,List.getElem?_cons_zero,Option.some.injEq] using hins
      subst ins
      obtain ⟨cost,u,hu,hcost,hrep,hP⟩ := instruction_eval spec t g ht htP head
      have htest : (Test.natLess 2 8).holds t := by
        change t.natReg 2 < t.natReg 8
        simp only [t,Function.update_self,Function.update_of_ne (by decide : (2:ℕ) ≠ 8)]
        have hh : s.natReg 2 = g.pc := h.1.pc
        omega
      have hu' : Eval (instruction action start head) t cost u := by simpa only [hpc] using hu
      refine ⟨1+(cost+1),u,Eval.seq (eval_natural s 8 (start+1)) (Eval.branchYes htest hu'),?_,hrep,hP⟩
      simp only [charge,List.map_cons,List.sum_cons] at hcost ⊢
      omega
    · have hnext : start+1 ≤ g.pc := by omega
      have hidx : g.pc-start = (g.pc-(start+1))+1 := by omega
      have htail : rest[g.pc-(start+1)]? = some ins := by simpa only [hidx,List.getElem?_cons_succ] using hins
      obtain ⟨cost,u,hu,hcost,hrep,hP⟩ := ih (start+1) t ht htP hnext htail
      have htest : ¬(Test.natLess 2 8).holds t := by
        change ¬t.natReg 2 < t.natReg 8
        simp only [t,Function.update_self,Function.update_of_ne (by decide : (2:ℕ) ≠ 8)]
        have hh : s.natReg 2 = g.pc := h.1.pc
        omega
      refine ⟨1+(cost+2),u,Eval.seq (eval_natural s 8 (start+1)) (Eval.branchNo htest hu),?_,hrep,hP⟩
      simp only [charge,List.map_cons,List.sum_cons] at hcost ⊢
      omega
end DecrAlmostLinearSSSP.Decremental.Instrumented
end s58
section s59
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Instrumented
open Structured
lemma interpreter_eval {action : Instruction → Cmd} {bound : Instruction → ℕ}
    {P : Data → Machine → Prop} {B F : ℕ} (spec : ActionSpec action bound P B F)
    (guest : Program) (t : ℕ) (s : Data) (g : Machine) (h : MachineRep B F s g) (hp : P s g)
    (hvalid : ∀ j < t, (execute guest g j).halted = false → ∃ ins, guest.code[(execute guest g j).pc]? = some ins)
    (hfinal : (execute guest g t).halted = true) :
    ∃ cost u, Eval (interpreter action guest.code) s cost u ∧
      cost ≤ (charge bound guest.code+2)*t+2 ∧ MachineRep B F u (execute guest g t) ∧ P u (execute guest g t) := by
  induction t generalizing s g with
  | zero =>
    have hgh : g.halted = true := hfinal
    have hs := h.1.halt_flag h.2.2.2.2.2
    have htest : ¬(Test.natLess 4 1).holds s := by simp [Test.holds,hs,hgh,h.2.2.1]
    exact ⟨2,s,Eval.loopNo s htest,by simp,h,hp⟩
  | succ t ih =>
    by_cases hgh : g.halted = true
    · have hs := h.1.halt_flag h.2.2.2.2.2
      have htest : ¬(Test.natLess 4 1).holds s := by simp [Test.holds,hs,hgh,h.2.2.1]
      refine ⟨2,s,Eval.loopNo s htest,by omega,?_,?_⟩
      · rwa [execute_halted guest g hgh]
      · rwa [execute_halted guest g hgh]
    · have hgh' : g.halted = false := Bool.eq_false_iff.mpr hgh
      obtain ⟨ins,hins⟩ := hvalid 0 (by omega) hgh'
      obtain ⟨cost,u,he,hcost,hrep,hP⟩ := dispatch_eval spec guest.code 0 s g h hp
        (Nat.zero_le _) ins (by simpa [execute] using hins)
      rw [← step_eq_effect guest g ins hgh' hins] at hrep hP
      have hv : ∀ j < t, (execute guest (step guest g) j).halted = false → ∃ ins, guest.code[(execute guest (step guest g) j).pc]? = some ins := by
        intro j hj hh
        rw [← execute_succ_front] at hh ⊢
        exact hvalid (j+1) (by omega) hh
      have hfin : (execute guest (step guest g) t).halted = true := by rwa [← execute_succ_front]
      obtain ⟨rest,v,hrest,hrestcost,hrestrep,hrestP⟩ := ih u (step guest g) hrep hP hv hfin
      have hs := h.1.halt_flag h.2.2.2.2.2
      have htest : (Test.natLess 4 1).holds s := by simp [Test.holds,hs,hgh',h.2.2.1]
      refine ⟨cost+rest+2,v,Eval.loopYes htest he hrest,?_,?_,?_⟩
      · rw [Nat.mul_succ]
        omega
      · rwa [execute_succ_front]
      · rwa [execute_succ_front]
lemma interpreter_ends {action : Instruction → Cmd} {bound : Instruction → ℕ}
    {P : Data → Machine → Prop} {B F : ℕ} (spec : ActionSpec action bound P B F)
    (guest : Program) (s : Data) (g final : Machine) (h : MachineRep B F s g) (hp : P s g)
    (he : Ends guest g final) :
    ∃ cost u, Eval (interpreter action guest.code) s cost u ∧
      cost ≤ (charge bound guest.code+2)*(final.work-g.work)+2 ∧ MachineRep B F u final ∧ P u final := by
  obtain ⟨t,ht,hhalt,hfault⟩ := he
  have hhalt' : (execute guest g t).halted = true := by rwa [ht]
  obtain ⟨r,_,hrun,hrwork⟩ := terminating_prefix guest g t hhalt'
  have hrfinal : execute guest g r = final := hrun.trans ht
  have hrfault : (execute guest g r).fault = false := by rwa [hrfinal]
  obtain ⟨cost,u,hu,hcost,hrep,hP⟩ := interpreter_eval spec guest r s g h hp
    (execution_valid_code guest g r hrfault) (by rwa [hrfinal])
  rw [ht] at hrwork
  refine ⟨cost,u,hu,?_,?_,?_⟩
  · rwa [← hrwork]
  · rwa [hrfinal] at hrep
  · rwa [hrfinal] at hP
end DecrAlmostLinearSSSP.Decremental.Instrumented
end s59
section s60
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
attribute [local instance] Classical.propDecidable
lemma inner_eval (s : Data) : Eval inner s 11 (committed s) := by
  have hp : Eval prefixCode s 5 (prepared s) := eval_sequence_atoms prefixAtoms s
  have hf : Eval flagCode (prepared s) 4 (flagged (prepared s)) :=
    Eval.seq (conditionalOne_eval _ _ _) (conditionalOne_eval _ _ _)
  have hs := Eval.seq (eval_storeN (flagged (prepared s)) 20 30) (eval_store _ 20 20)
  exact Eval.seq hp (Eval.seq hf hs)
lemma prepared_values (s : Data) (h1 : s.natReg 1 = 1) :
    (prepared s).natReg 20 = s.natMem (s.natReg 6+1) ∧
    (prepared s).natReg 22 = s.natMem (s.natReg 6) ∧ (prepared s).natReg 30 = 0 ∧
    (prepared s).realReg 20 = s.realMem (s.natReg 6) ∧ (prepared s).realReg 26 = s.realReg 26 ∧
    (prepared s).natReg 1 = 1 := by
  simp [prepared,prefixAtoms,Atom.effect,instructionEffect,data,Data.machine,h1]
lemma flagged_values (s : Data) :
    (flagged s).natReg 30 = if s.natReg 1 < s.natReg 22 ∨ s.realReg 26 < s.realReg 20 then 1 else s.natReg 30 := by
  classical
  by_cases hn : s.natReg 1 < s.natReg 22 <;> by_cases hr : s.realReg 26 < s.realReg 20 <;>
    simp [flagged,conditionalOneState,Test.holds,hn,hr]
lemma committed_memory (s : Data) (h1 : s.natReg 1 = 1) :
    (committed s).natMem = Function.update s.natMem (s.natMem (s.natReg 6+1))
      (if 1 < s.natMem (s.natReg 6) ∨ s.realReg 26 < s.realMem (s.natReg 6) then 1 else 0) ∧
    (committed s).realMem = Function.update s.realMem (s.natMem (s.natReg 6+1)) (s.realMem (s.natReg 6)) := by
  classical
  obtain ⟨h20,h22,h30,hr20,hr26,hr1⟩ := prepared_values s h1
  have hf := flagged_values (prepared s)
  have hpMem : (prepared s).natMem = s.natMem ∧ (prepared s).realMem = s.realMem := by
    simp [prepared,prefixAtoms,Atom.effect,instructionEffect,data,Data.machine]
  constructor
  · change Function.update (flagged (prepared s)).natMem ((flagged (prepared s)).natReg 20) ((flagged (prepared s)).natReg 30) = _
    rw [show (flagged (prepared s)).natMem = s.natMem by exact (conditionalOneState_mem _ _ _).1.trans ((conditionalOneState_mem _ _ _).1.trans hpMem.1)]
    rw [show (flagged (prepared s)).natReg 20 = (prepared s).natReg 20 by simp [flagged,conditionalOneState_nat_other,show (20:ℕ) ≠ 30 by decide]]
    rw [hf,h20,h22,h30,hr20,hr26,hr1]
  · change Function.update (flagged (prepared s)).realMem ((flagged (prepared s)).natReg 20) ((flagged (prepared s)).realReg 20) = _
    rw [show (flagged (prepared s)).realMem = s.realMem by exact (conditionalOneState_mem _ _ _).2.trans ((conditionalOneState_mem _ _ _).2.trans hpMem.2)]
    simp only [flagged,conditionalOneState_nat_other _ _ _ _ (by decide : (20:ℕ) ≠ 30),conditionalOneState_real,h20,hr20]
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
lemma callback_nat_frame (k : ℕ) (h18 : k ≠ 18) (h20 : k ≠ 20) (h22 : k ≠ 22) (h30 : k ≠ 30) :
    NatFrame callback k := by
  simp [callback,inner,prefixCode,prefixAtoms,flagCode,conditionalOne,Structured.sequence,NatFrame,writesNat,nadd,loadN,load,Structured.natural,storeN,store,
    Ne.symm h18,Ne.symm h20,Ne.symm h22,Ne.symm h30]
lemma callback_real_frame (k : ℕ) (h20 : k ≠ 20) : RealFrame callback k := by
  simp [callback,inner,prefixCode,prefixAtoms,flagCode,conditionalOne,Structured.sequence,RealFrame,writesReal,nadd,loadN,load,Structured.natural,storeN,store,Ne.symm h20]
lemma inner_nat_frame (k : ℕ) (h18 : k ≠ 18) (h20 : k ≠ 20) (h22 : k ≠ 22) (h30 : k ≠ 30) :
    NatFrame inner k := (callback_nat_frame k h18 h20 h22 h30).1
lemma inner_real_frame (k : ℕ) (h20 : k ≠ 20) : RealFrame inner k := (callback_real_frame k h20).1
lemma inner_shadow {B : ℕ} (n : ℕ) (hn : n ≤ B) {s : Data} {g : Machine}
    (hrep : ShadowDataRep B 2 s g) (h1 : s.natReg 1 = 1)
    (hpublic : s.natMem (s.natReg 6+1) < n) : ShadowDataRep B 2 (committed s) g := by
  have he := inner_eval s
  obtain ⟨hmN,hmR⟩ := committed_memory s h1
  have hnat (k : ℕ) (h18 : k ≠ 18) (h20 : k ≠ 20) (h22 : k ≠ 22) (h30 : k ≠ 30) :
      (committed s).natReg k = s.natReg k := he.nat_frame (inner_nat_frame k h18 h20 h22 h30)
  have hreal (k : ℕ) (h20 : k ≠ 20) : (committed s).realReg k = s.realReg k := he.real_frame (inner_real_frame k h20)
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (hnat 2 (by decide) (by decide) (by decide) (by decide)).trans hrep.pc
  · exact (hnat 3 (by decide) (by decide) (by decide) (by decide)).trans hrep.work
  · change ((committed s).natReg 4 == 1) = g.halted
    rw [hnat 4 (by decide) (by decide) (by decide) (by decide)]
    exact hrep.halted
  · change ((committed s).natReg 5 == 1) = g.fault
    rw [hnat 5 (by decide) (by decide) (by decide) (by decide)]
    exact hrep.fault
  · intro j
    change (committed s).realReg (shadowReg j) = _
    rw [show (committed s).realReg (shadowReg j) = s.realReg (shadowReg j) by apply hreal;unfold shadowReg;omega]
    exact hrep.realReg j
  · intro j
    change (committed s).natReg (shadowReg j) = _
    rw [show (committed s).natReg (shadowReg j) = s.natReg (shadowReg j) by apply hnat <;> unfold shadowReg <;> omega]
    exact hrep.natReg j
  · intro a
    change (committed s).realMem (B+2*(2*a+1)) = _
    rw [hmR,Function.update_of_ne (by omega : B+2*(2*a+1) ≠ s.natMem (s.natReg 6+1))]
    exact hrep.realMem a
  · intro a
    change (committed s).natMem (B+2*(2*a+1)) = _
    rw [hmN,Function.update_of_ne (by omega : B+2*(2*a+1) ≠ s.natMem (s.natReg 6+1))]
    exact hrep.natMem a
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s64
section s65
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
attribute [local instance] Classical.propDecidable
lemma Image.header {i : Input} {B : ℕ} {bad : Option ℕ} {s : Data} {g : Machine}
    (h : Image i B bad s g) :
    Image i B bad {s with natReg := Function.update (Function.update s.natReg 2 (g.pc+1)) 3 (s.natReg 3+1)}
      {g with pc := g.pc+1,work := g.work+1} := by
  exact ⟨h.room,by simpa using h.limit,h.threshold,h.mapping,h.values,h.flags⟩
lemma Image.scratch {i : Input} {B : ℕ} {bad : Option ℕ} {s : Data} {g : Machine}
    (h : Image i B bad s g) (x : ℕ) : Image i B bad {s with natReg := Function.update s.natReg 8 x} g := by
  exact ⟨h.room,by simpa using h.limit,h.threshold,h.mapping,h.values,h.flags⟩
lemma Image.remove_bad {i : Input} {B : ℕ} {bad : Option ℕ} {s : Data} {g : Machine}
    (h : Image i B bad s g) (hn : ∀ v : Fin i.n, bad ≠ some v.val) : Image i B none s g :=
  ⟨h.room,h.limit,h.threshold,h.mapping,fun v _ => h.values v (hn v),fun v _ => h.flags v (hn v)⟩
lemma Image.normal {i : Input} {B : ℕ} {s : Data} {g : Machine} (h : Image i B none s g)
    (hn : ∀ v : Fin i.n, g.natMem v.val ≤ 1 ∧ (g.natMem v.val = 0 → 0 ≤ g.realMem v.val)) :
    ∀ v : Fin i.n, s.natMem v.val ≤ 1 ∧ (s.natMem v.val = 0 → 0 ≤ s.realMem v.val) := by
  intro v
  rw [h.flags v (by simp)]
  constructor
  · unfold answerFlag
    split <;> omega
  · intro hz
    rw [h.values v (by simp)]
    have hzero : g.natMem v.val = 0 := by
      by_contra hg
      have hp : 0 < g.natMem v.val := by omega
      simp [answerFlag,hp] at hz
    exact (hn v).2 hzero
lemma Image.stored {i : Input} {B : ℕ} {s : Data} {g : Machine} (h : Image i B none s g)
    (v : Fin i.n) (hn : g.natMem v.val ≤ 1) :
    stored s.machine v.val = sanitize i (stored g v.val) := by
  classical
  have hN := h.flags v (by simp)
  have hR := h.values v (by simp)
  by_cases hg : g.natMem v.val = 1
  · have hs : s.natMem v.val = 1 := by rw [hN];simp [answerFlag,hg]
    simp only [DecrAlmostLinearSSSP.Decremental.stored,Data.machine,hs,hg,if_pos rfl]
    unfold sanitize
    simp
  · have hg0 : g.natMem v.val = 0 := by omega
    have hcomp : ((cutoff i : ℝ≥0∞) < ENNReal.ofReal (g.realMem v.val)) ↔ (cutoff i : ℝ) < g.realMem v.val := by
      rw [← ENNReal.ofReal_natCast (cutoff i)]
      exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (Nat.cast_nonneg _)
    unfold DecrAlmostLinearSSSP.Decremental.stored sanitize
    change (if s.natMem v.val = 1 then ⊤ else ENNReal.ofReal (s.realMem v.val)) = _
    rw [hN,hR]
    simp only [answerFlag,hg0,lt_self_iff_false,false_or,if_neg (by decide : ¬(0:ℕ) = 1),hcomp]
    split_ifs <;> simp_all
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s65
section s66
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
lemma weightCode_eval (i : Input) (s : Data) (h : InputCapture.Captured i s) :
    ∃ t, Eval weightCode s (4*(i.n+1)+8) t ∧ t.natReg 78 = sentinel i := by
  have he : Eval prepareCode s 6 (prepareData s) := eval_sequence_atoms prepareAtoms s
  have hpLim : (prepareData s).natReg 76 = (prepareData s).natReg 80+(i.n+1) := by
    simp [prepareData,prepareAtoms,Atom.effect,instructionEffect,data,Data.machine,h.vertices,h.unit]
  have hpUnit : (prepareData s).natReg 26 = 1 := by
    simp [prepareData,prepareAtoms,Atom.effect,instructionEffect,data,Data.machine,h.unit]
  obtain ⟨t,ht,htc,hta⟩ := accumulate_eval 78 80 76 82 26 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (prepareData s) (i.n+1) hpLim hpUnit
  refine ⟨t,?_,?_⟩
  · have hh := Eval.seq he ht
    simpa only [weightCode,show 6+(4*(i.n+1)+2) = 4*(i.n+1)+8 by omega] using hh
  · rw [hta]
    simp [prepareData,prepareAtoms,Atom.effect,instructionEffect,data,Data.machine,h.weightBound,sentinel]
    ring
lemma headerCode_eval (entry : ℕ) (s : Data) : Eval (headerCode entry) s 24 (headerData entry s) :=
  eval_sequence_atoms (headerAtoms entry) s
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
lemma weightCode_no_memory : NoMemory weightCode := by
  simp [weightCode,prepareCode,prepareAtoms,accumulate,Structured.sequence,NoMemory,NoStore,nadd]
lemma weightCode_nat_frame (k : ℕ) (h76 : k ≠ 76) (h78 : k ≠ 78) (h80 : k ≠ 80) (h82 : k ≠ 82) : NatFrame weightCode k := by
  simp [weightCode,prepareCode,prepareAtoms,accumulate,Structured.sequence,NatFrame,writesNat,nadd,Structured.natural,
    Ne.symm h76,Ne.symm h78,Ne.symm h80,Ne.symm h82]
lemma weightCode_real_frame (k : ℕ) : RealFrame weightCode k := by
  simp [weightCode,prepareCode,prepareAtoms,accumulate,Structured.sequence,RealFrame,writesReal,nadd,Structured.natural]
lemma weightCode_captured {i : Input} {s t : Data} {cost : ℕ} (h : InputCapture.Captured i s)
    (he : Eval weightCode s cost t) : InputCapture.Captured i t :=
  h.frame (fun k hk => he.nat_frame (weightCode_nat_frame k (by omega) (by omega) (by omega) (by omega)))
    (fun k _ => he.real_frame (weightCode_real_frame k))
lemma weightCode_vertices {i : Input} {s t : Data} {cost : ℕ} (h : InputCapture.Captured i s)
    (he : Eval weightCode s cost t) : t.natReg 76 = i.n+1 := by
  have hpLim : (prepareData s).natReg 76 = (prepareData s).natReg 80+(i.n+1) := by
    simp [prepareData,prepareAtoms,Atom.effect,instructionEffect,data,Data.machine,h.vertices,h.unit]
  have hpUnit : (prepareData s).natReg 26 = 1 := by
    simp [prepareData,prepareAtoms,Atom.effect,instructionEffect,data,Data.machine,h.unit]
  obtain ⟨u,hu,huc,hua⟩ := accumulate_eval 78 80 76 82 26 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (prepareData s) (i.n+1) hpLim hpUnit
  have hp : Eval prepareCode s 6 (prepareData s) := eval_sequence_atoms prepareAtoms s
  have hfull : Eval weightCode s (6+(4*(i.n+1)+2)) u := Eval.seq hp hu
  obtain ⟨_,rfl⟩ := he.deterministic hfull
  have hf : NatFrame (accumulate 78 80 76 82 26) 76 := by simp [accumulate,NatFrame,nadd,writesNat]
  rw [hu.nat_frame hf]
  simp [prepareData,prepareAtoms,Atom.effect,instructionEffect,data,Data.machine,h.vertices,h.unit]
lemma headerCode_no_memory (entry : ℕ) : NoMemory (headerCode entry) := by
  simp [headerCode,headerAtoms,Structured.sequence,NoMemory,NoStore]
lemma headerCode_nat_frame (entry k : ℕ) (hk : 18 ≤ k) : NatFrame (headerCode entry) k := by
  simp [headerCode,headerAtoms,Structured.sequence,NatFrame,writesNat]
  omega
lemma headerCode_real_frame (entry k : ℕ) (h7 : k ≠ 7) (h9 : k ≠ 9) (h26 : k ≠ 26) (h28 : k ≠ 28) : RealFrame (headerCode entry) k := by
  simp [headerCode,headerAtoms,Structured.sequence,RealFrame,writesReal,Ne.symm h7,Ne.symm h9,Ne.symm h26,Ne.symm h28]
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s68
section s69
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
lemma field_eval (s : Data) : Eval fieldCode s 5 (fieldData s) := eval_sequence_atoms fieldAtoms s
lemma field_memory (s : Data) :
    (fieldData s).natMem = Function.update s.natMem (s.natReg 82) (2*s.natMem (s.natReg 80)) ∧
    (fieldData s).realMem = s.realMem := by
  constructor
  · simp [fieldData,fieldAtoms,Atom.effect,instructionEffect,data,Data.machine]
    congr 2
    omega
  · rfl
lemma field_pointers (s : Data) (h1 : s.natReg 26 = 1) (h4 : s.natReg 88 = 4) :
    (fieldData s).natReg 80 = s.natReg 80+1 ∧ (fieldData s).natReg 82 = s.natReg 82+4 := by
  simp [fieldData,fieldAtoms,Atom.effect,instructionEffect,data,Data.machine,h1,h4]
lemma field_nat_frame (k : ℕ) (h80 : k ≠ 80) (h82 : k ≠ 82) (h84 : k ≠ 84) : NatFrame fieldCode k := by
  simp [fieldCode,fieldAtoms,Structured.sequence,NatFrame,writesNat,Ne.symm h80,Ne.symm h82,Ne.symm h84]
lemma field_real_frame (k : ℕ) : RealFrame fieldCode k := by
  simp [fieldCode,fieldAtoms,Structured.sequence,RealFrame,writesReal]
lemma redirect_eval (s : Data) : ∃ cost, Eval headRedirect s cost (redirected s) ∧ cost ≤ 5 := by
  by_cases hlow : s.natReg 84 < s.natReg 72
  · refine ⟨1,?_,by omega⟩
    have he : Eval headRedirect s 1 s := Eval.branchYes (show (Test.natLess 84 72).holds s from hlow) (Eval.skip s)
    simpa only [headRedirect,redirected,if_neg (by omega : s.natReg 84 ≠ s.natReg 72)] using he
  · by_cases hhigh : s.natReg 72 < s.natReg 84
    · refine ⟨3,?_,by omega⟩
      have he : Eval headRedirect s 3 s := Eval.branchNo (show ¬(Test.natLess 84 72).holds s from hlow)
        (Eval.branchYes (show (Test.natLess 72 84).holds s from hhigh) (Eval.skip s))
      simpa only [headRedirect,redirected,if_neg (by omega : s.natReg 84 ≠ s.natReg 72)] using he
    · refine ⟨5,?_,le_rfl⟩
      have he : Eval headRedirect s 5 {s with natReg := Function.update s.natReg 84 (s.natReg 66+s.natReg 56)} := Eval.branchNo (show ¬(Test.natLess 84 72).holds s from hlow)
        (Eval.branchNo (show ¬(Test.natLess 72 84).holds s from hhigh) (eval_nadd s 84 66 56))
      simpa only [headRedirect,redirected,if_pos (by omega : s.natReg 84 = s.natReg 72)] using he
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s69
section s70
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
attribute [local instance] Classical.propDecidable
lemma head_eval (s : Data) : ∃ cost, Eval headCode s cost (headData s) ∧ cost ≤ 10 := by
  obtain ⟨c,hc,hbound⟩ := redirect_eval (headLoaded s)
  refine ⟨1+(c+4),Eval.seq (eval_loadN s 84 80) (Eval.seq hc (eval_sequence_atoms headSuffixAtoms _)),by omega⟩
lemma head_memory (s : Data) (hz : s.natReg 56 = 0) :
    (headData s).natMem = Function.update s.natMem (s.natReg 82)
      (2*(if s.natMem (s.natReg 80) = s.natReg 72 then s.natReg 66 else s.natMem (s.natReg 80))) ∧
    (headData s).realMem = s.realMem := by
  by_cases hh : s.natMem (s.natReg 80) = s.natReg 72
  · simp [headData,redirected,headLoaded,headSuffixAtoms,Atom.effect,instructionEffect,data,Data.machine,hz,hh]
    congr 2
    omega
  · simp [headData,redirected,headLoaded,headSuffixAtoms,Atom.effect,instructionEffect,data,Data.machine,hz,hh]
    congr 2
    omega
lemma head_pointers (s : Data) (h1 : s.natReg 26 = 1) (h4 : s.natReg 88 = 4) :
    (headData s).natReg 80 = s.natReg 80+1 ∧ (headData s).natReg 82 = s.natReg 82+4 := by
  unfold headData redirected headLoaded
  split_ifs <;> simp [headSuffixAtoms,Atom.effect,instructionEffect,data,Data.machine,h1,h4]
lemma head_nat_frame (k : ℕ) (h80 : k ≠ 80) (h82 : k ≠ 82) (h84 : k ≠ 84) : NatFrame headCode k := by
  simp [headCode,headRedirect,headSuffix,headSuffixAtoms,Structured.sequence,NatFrame,writesNat,loadN,nadd,storeN,
    Ne.symm h80,Ne.symm h82,Ne.symm h84]
lemma head_real_frame (k : ℕ) : RealFrame headCode k := by
  simp [headCode,headRedirect,headSuffix,headSuffixAtoms,Structured.sequence,RealFrame,writesReal,loadN,nadd,storeN]
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
lemma Image.write_exact {B bank logical value : ℕ} {s t : Data} {natural : ℕ → ℕ} {real : ℕ → ℝ}
    (h : Image B bank s natural real)
    (hn : t.natMem = Function.update s.natMem (bankAddress B bank logical) (bankFactor bank*value))
    (hr : t.realMem = s.realMem) : Image B bank t (Function.update natural logical value) real := by
  constructor
  · intro a
    rw [hn]
    by_cases ha : a = logical
    · subst a;simp
    · have hne : bankAddress B bank a ≠ bankAddress B bank logical := fun he => ha (bankAddress_injective he).2
      rw [Function.update_of_ne hne,Function.update_of_ne ha]
      exact h.natMem a
  · intro a
    rw [hr]
    exact h.realMem a
end DecrAlmostLinearSSSP.Decremental.SourceMemory
end s108
section s109
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
lemma field_image (B logical : ℕ) (s : Data) (natural : ℕ → ℕ) (real : ℕ → ℝ)
    (h : SourceMemory.Image B 0 s natural real) (hdest : s.natReg 82 = bankAddress B 0 logical) :
    SourceMemory.Image B 0 (fieldData s) (Function.update natural logical (s.natMem (s.natReg 80))) real := by
  obtain ⟨hmN,hmR⟩ := field_memory s
  rw [hdest] at hmN
  exact h.write_exact hmN hmR
lemma head_image (B logical : ℕ) (s : Data) (natural : ℕ → ℕ) (real : ℕ → ℝ)
    (h : SourceMemory.Image B 0 s natural real) (hdest : s.natReg 82 = bankAddress B 0 logical)
    (hz : s.natReg 56 = 0) :
    SourceMemory.Image B 0 (headData s) (Function.update natural logical
      (if s.natMem (s.natReg 80) = s.natReg 72 then s.natReg 66 else s.natMem (s.natReg 80))) real := by
  obtain ⟨hmN,hmR⟩ := head_memory s hz
  rw [hdest] at hmN
  exact h.write_exact hmN hmR
lemma field_prefix (s : Data) (B : ℕ) (hB : B ≤ s.natReg 82) (a : ℕ) (ha : a < B) :
    (fieldData s).natMem a = s.natMem a ∧ (fieldData s).realMem a = s.realMem a := by
  obtain ⟨hn,hr⟩ := field_memory s
  rw [hn,hr,Function.update_of_ne (by omega : a ≠ s.natReg 82)]
  exact ⟨rfl,rfl⟩
lemma head_prefix (s : Data) (B : ℕ) (hz : s.natReg 56 = 0) (hB : B ≤ s.natReg 82) (a : ℕ) (ha : a < B) :
    (headData s).natMem a = s.natMem a ∧ (headData s).realMem a = s.realMem a := by
  obtain ⟨hn,hr⟩ := head_memory s hz
  rw [hn,hr,Function.update_of_ne (by omega : a ≠ s.natReg 82)]
  exact ⟨rfl,rfl⟩
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s109
section s110
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
lemma record_eval (s : Data) : ∃ cost, Eval recordCode s cost (recordData s) ∧ cost ≤ 21 := by
  obtain ⟨c,hc,hbound⟩ := head_eval (fieldData s)
  exact ⟨5+(c+(5+1)),Eval.seq (field_eval s) (Eval.seq hc (Eval.seq (field_eval _) (eval_nadd _ 90 90 26))),by omega⟩
lemma record_nat_frame (k : ℕ) (h80 : k ≠ 80) (h82 : k ≠ 82) (h84 : k ≠ 84) (h90 : k ≠ 90) : NatFrame recordCode k :=
  ⟨field_nat_frame k h80 h82 h84,head_nat_frame k h80 h82 h84,field_nat_frame k h80 h82 h84,Ne.symm h90⟩
lemma record_real_frame (k : ℕ) : RealFrame recordCode k :=
  ⟨field_real_frame k,head_real_frame k,field_real_frame k,not_false⟩
lemma record_pointers (s : Data) (h1 : s.natReg 26 = 1) (h4 : s.natReg 88 = 4) :
    (recordData s).natReg 80 = s.natReg 80+3 ∧ (recordData s).natReg 82 = s.natReg 82+12 ∧
    (recordData s).natReg 90 = s.natReg 90+1 := by
  have f26 (t : Data) : (fieldData t).natReg 26 = t.natReg 26 := (field_eval t).nat_frame (field_nat_frame 26 (by decide) (by decide) (by decide))
  have f88 (t : Data) : (fieldData t).natReg 88 = t.natReg 88 := (field_eval t).nat_frame (field_nat_frame 88 (by decide) (by decide) (by decide))
  have f90 (t : Data) : (fieldData t).natReg 90 = t.natReg 90 := (field_eval t).nat_frame (field_nat_frame 90 (by decide) (by decide) (by decide))
  have h26 (t : Data) : (headData t).natReg 26 = t.natReg 26 := by obtain ⟨c,hc,_⟩ := head_eval t;exact hc.nat_frame (head_nat_frame 26 (by decide) (by decide) (by decide))
  have h88 (t : Data) : (headData t).natReg 88 = t.natReg 88 := by obtain ⟨c,hc,_⟩ := head_eval t;exact hc.nat_frame (head_nat_frame 88 (by decide) (by decide) (by decide))
  have h90 (t : Data) : (headData t).natReg 90 = t.natReg 90 := by obtain ⟨c,hc,_⟩ := head_eval t;exact hc.nat_frame (head_nat_frame 90 (by decide) (by decide) (by decide))
  have hp1 := field_pointers s h1 h4
  have hp2 := head_pointers (fieldData s) (by rw [f26,h1]) (by rw [f88,h4])
  have hp3 := field_pointers (headData (fieldData s)) (by rw [h26,f26,h1]) (by rw [h88,f88,h4])
  obtain ⟨hp1a,hp1b⟩ := hp1
  obtain ⟨hp2a,hp2b⟩ := hp2
  obtain ⟨hp3a,hp3b⟩ := hp3
  have ht80 : (fieldData (headData (fieldData s))).natReg 80 = s.natReg 80+3 := by
    calc
      _ = (headData (fieldData s)).natReg 80+1 := hp3a
      _ = ((fieldData s).natReg 80+1)+1 := congrArg (fun x : ℕ => x+1) hp2a
      _ = ((s.natReg 80+1)+1)+1 := congrArg (fun x : ℕ => (x+1)+1) hp1a
      _ = _ := by omega
  have ht82 : (fieldData (headData (fieldData s))).natReg 82 = s.natReg 82+12 := by
    calc
      _ = (headData (fieldData s)).natReg 82+4 := hp3b
      _ = ((fieldData s).natReg 82+4)+4 := congrArg (fun x : ℕ => x+4) hp2b
      _ = ((s.natReg 82+4)+4)+4 := congrArg (fun x : ℕ => (x+4)+4) hp1b
      _ = _ := by omega
  simp only [recordData,Function.update_of_ne (by decide : (80:ℕ) ≠ 90),Function.update_of_ne (by decide : (82:ℕ) ≠ 90),Function.update_self,f26,h26,f90,h90,h1]
  exact ⟨ht80,ht82,trivial⟩
end DecrAlmostLinearSSSP.Decremental.Normalize.Native
end s110
section s111
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Normalize.Native
open Structured
lemma record_captured {i : Input} {s : Data} (h : InputCapture.Captured i s) :
    InputCapture.Captured i (recordData s) := by
  obtain ⟨c,he,_⟩ := record_eval s
  exact h.frame (fun k hk => he.nat_frame (record_nat_frame k (by omega) (by omega) (by omega) (by omega)))
    (fun k _ => he.real_frame (record_real_frame k))
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
theorem solution : (((((((∀ (acc counter limit factor unit : Nat),
  @Ne.{1} Nat acc counter →
    @Ne.{1} Nat acc limit →
      @Ne.{1} Nat acc factor →
        @Ne.{1} Nat acc unit →
          @Ne.{1} Nat counter limit →
            @Ne.{1} Nat counter factor →
              @Ne.{1} Nat counter unit →
                ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (q : Nat),
                  @Eq.{1} Nat (s.natReg limit)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (s.natReg counter) q) →
                    @Eq.{1} Nat (s.natReg unit) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                      ∃ t,
                        And
                          (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                            (DecrAlmostLinearSSSP.Decremental.Structured.accumulate acc counter limit factor unit) s
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            t)
                          (And
                            (@Eq.{1} Nat (t.natReg counter)
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (s.natReg counter) q))
                            (@Eq.{1} Nat (t.natReg acc)
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (s.natReg acc)
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) q (s.natReg factor)))))) ∧ (∀ (test : DecrAlmostLinearSSSP.Decremental.Structured.Test) (k : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.conditionalOne test k) s
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    (DecrAlmostLinearSSSP.Decremental.Structured.conditionalOneState test k s))) ∧ ((∀ (test : DecrAlmostLinearSSSP.Decremental.Structured.Test) (k : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  And (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.Structured.conditionalOneState test k s).natMem s.natMem)
    (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.Structured.conditionalOneState test k s).realMem s.realMem)) ∧ (∀ (test : DecrAlmostLinearSSSP.Decremental.Structured.Test) (k : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.Structured.conditionalOneState test k s).natReg k)
    (@ite.{1} Nat (test.holds s) (Classical.propDecidable (test.holds s))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (s.natReg k))))) ∧ (((∀ (test : DecrAlmostLinearSSSP.Decremental.Structured.Test) (k j : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Ne.{1} Nat j k →
    @Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.Structured.conditionalOneState test k s).natReg j) (s.natReg j)) ∧ (∀ (test : DecrAlmostLinearSSSP.Decremental.Structured.Test) (k : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.Structured.conditionalOneState test k s).realReg s.realReg)) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (a : Finset.{0} (Fin i.k)) (e : Fin i.k),
  Iff
    (@Membership.mem.{0, 0} (Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n))
      (Finset.{0} (Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n)))
      (@SetLike.instMembership.{0, 0}
        (Finset.{0} (Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n)))
        (Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n))
        (@Finset.instSetLike.{0} (Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n))))
      (DecrAlmostLinearSSSP.Decremental.Normalize.active i a) (DecrAlmostLinearSSSP.Decremental.Normalize.oldEdge i e))
    (@Membership.mem.{0, 0} (Fin i.k) (Finset.{0} (Fin i.k))
      (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin i.k)) (Fin i.k) (@Finset.instSetLike.{0} (Fin i.k))) a e)) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (a : Finset.{0} (Fin i.k)) (v : Fin i.n),
  @Membership.mem.{0, 0} (Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n))
    (Finset.{0} (Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n)))
    (@SetLike.instMembership.{0, 0}
      (Finset.{0} (Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n)))
      (Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n))
      (@Finset.instSetLike.{0} (Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n))))
    (DecrAlmostLinearSSSP.Decremental.Normalize.active i a) (DecrAlmostLinearSSSP.Decremental.Normalize.addedEdge i v)) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  @Function.Injective.{1, 1} (Fin i.k) (Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n))
    (DecrAlmostLinearSSSP.Decremental.Normalize.oldEdge i)))))) ∧ ((((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (ds : List.{0} (Fin i.k)),
  @Eq.{1} (Finset.{0} (Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n)))
    (DecrAlmostLinearSSSP.Decremental.Normalize.active i (@DecrAlmostLinearSSSP.Decremental.live i.k ds))
    (@DecrAlmostLinearSSSP.Decremental.live (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n)
      (@List.map.{0, 0} (Fin i.k) (Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n))
        (DecrAlmostLinearSSSP.Decremental.Normalize.oldEdge i) ds))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (a : Finset.{0} (Fin i.k)) {u v : Fin i.n} {es : List.{0} (Fin i.k)},
  @DecrAlmostLinearSSSP.Decremental.Walk i.n i.k i.graph a u v es →
    (∀ (e : Fin i.k),
        @Membership.mem.{0, 0} (Fin i.k) (List.{0} (Fin i.k)) (@List.instMembership.{0} (Fin i.k)) es e →
          @Ne.{1} (Fin i.n) (@DecrAlmostLinearSSSP.Decremental.Digraph.head i.n i.k i.graph e) i.source) →
      @DecrAlmostLinearSSSP.Decremental.Walk (DecrAlmostLinearSSSP.Decremental.Normalize.input i).n
        (DecrAlmostLinearSSSP.Decremental.Normalize.input i).k
        (DecrAlmostLinearSSSP.Decremental.Normalize.input i).graph
        (DecrAlmostLinearSSSP.Decremental.Normalize.active i a)
        (DecrAlmostLinearSSSP.Decremental.Normalize.oldVertex i u)
        (DecrAlmostLinearSSSP.Decremental.Normalize.oldVertex i v)
        (@List.map.{0, 0} (Fin i.k) (Fin (DecrAlmostLinearSSSP.Decremental.Normalize.input i).k)
          (DecrAlmostLinearSSSP.Decremental.Normalize.oldEdge i) es))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input)
  (a : Finset.{0} (Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n)))
  {u v :
    Fin
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))}
  {es : List.{0} (Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n))},
  @DecrAlmostLinearSSSP.Decremental.Walk (DecrAlmostLinearSSSP.Decremental.Normalize.input i).n
      (DecrAlmostLinearSSSP.Decremental.Normalize.input i).k (DecrAlmostLinearSSSP.Decremental.Normalize.input i).graph
      a u v es →
    @Eq.{1}
        (Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        u (DecrAlmostLinearSSSP.Decremental.Normalize.sink i) →
      @Eq.{1}
        (Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        v (DecrAlmostLinearSSSP.Decremental.Normalize.sink i)) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (a : Finset.{0} (Fin i.k))
  {u w :
    Fin
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))}
  {es : List.{0} (Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n))},
  @DecrAlmostLinearSSSP.Decremental.Walk (DecrAlmostLinearSSSP.Decremental.Normalize.input i).n
      (DecrAlmostLinearSSSP.Decremental.Normalize.input i).k (DecrAlmostLinearSSSP.Decremental.Normalize.input i).graph
      (DecrAlmostLinearSSSP.Decremental.Normalize.active i a) u w es →
    (∀ (e : Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n)),
        @Membership.mem.{0, 0} (Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n))
            (List.{0} (Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n)))
            (@List.instMembership.{0} (Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n)))
            es e →
          @LT.lt.{0} Nat instLTNat
            (@Fin.val (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n) e) i.k) →
      ∀ (v : Fin i.n),
        @Eq.{1}
            (Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            w (DecrAlmostLinearSSSP.Decremental.Normalize.oldVertex i v) →
          ∃ x fs,
            And
              (@Eq.{1}
                (Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                u (DecrAlmostLinearSSSP.Decremental.Normalize.oldVertex i x))
              (And (@DecrAlmostLinearSSSP.Decremental.Walk i.n i.k i.graph a x v fs)
                (@Eq.{1} (List.{0} (Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n))) es
                  (@List.map.{0, 0} (Fin i.k)
                    (Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n))
                    (DecrAlmostLinearSSSP.Decremental.Normalize.oldEdge i) fs)))))) ∧ (((∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (a : Finset.{0} (Fin k)) (w : Fin k → Real),
  (∀ (e : Fin k),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (w e)) →
    ∀ (s v : Fin n),
      @DecrAlmostLinearSSSP.Decremental.Reachable n k g a s v →
        ∃ es,
          And (@DecrAlmostLinearSSSP.Decremental.Walk n k g a s v es)
            (And (@LT.lt.{0} Nat instLTNat (@List.length.{0} (Fin k) es) n)
              (And
                (∀ (e : Fin k),
                  @Membership.mem.{0, 0} (Fin k) (List.{0} (Fin k)) (@List.instMembership.{0} (Fin k)) es e →
                    @Ne.{1} (Fin n) (@DecrAlmostLinearSSSP.Decremental.Digraph.head n k g e) s)
                (@Eq.{1} ENNReal
                  (@DecrAlmostLinearSSSP.Decremental.distance n k g a (fun e => ENNReal.ofReal (w e)) s v)
                  (ENNReal.ofReal
                    (@List.sum.{0} Real Real.instAdd Real.instZero (@List.map.{0, 0} (Fin k) Real w es))))))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (es : List.{0} (Fin i.k)),
  @Eq.{1} Real
    (@List.sum.{0} Real Real.instAdd Real.instZero
      (@List.map.{0, 0} (Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n)) Real
        (fun e => @Nat.cast.{0} Real Real.instNatCast (DecrAlmostLinearSSSP.Decremental.Normalize.weight i e))
        (@List.map.{0, 0} (Fin i.k) (Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n))
          (DecrAlmostLinearSSSP.Decremental.Normalize.oldEdge i) es)))
    (@List.sum.{0} Real Real.instAdd Real.instZero
      (@List.map.{0, 0} (Fin i.k) Real (fun e => @Nat.cast.{0} Real Real.instNatCast (i.weight e)) es)))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (a : Finset.{0} (Fin i.k)) (v : Fin i.n),
  @DecrAlmostLinearSSSP.Decremental.Reachable i.n i.k i.graph a i.source v →
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
      (@DecrAlmostLinearSSSP.Decremental.distance i.n i.k i.graph a
        (fun e =>
          @Nat.cast.{0} ENNReal
            (@AddMonoidWithOne.toNatCast.{0} ENNReal
              (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
            (i.weight e))
        i.source v)) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (a : Finset.{0} (Fin i.k))
  (v :
    Fin
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
  @DecrAlmostLinearSSSP.Decremental.Reachable (DecrAlmostLinearSSSP.Decremental.Normalize.input i).n
    (DecrAlmostLinearSSSP.Decremental.Normalize.input i).k (DecrAlmostLinearSSSP.Decremental.Normalize.input i).graph
    (DecrAlmostLinearSSSP.Decremental.Normalize.active i a) (DecrAlmostLinearSSSP.Decremental.Normalize.source i) v) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (a : Finset.{0} (Fin i.k)) (v : Fin i.n),
  @LT.lt.{0} ENNReal (@Preorder.toLT.{0} ENNReal (@PartialOrder.toPreorder.{0} ENNReal ENNReal.instPartialOrder))
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
      (@Nat.cast.{0} ENNReal
        (@AddMonoidWithOne.toNatCast.{0} ENNReal
          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
        (DecrAlmostLinearSSSP.Decremental.Normalize.sentinel i)) →
    @LE.le.{0} ENNReal ENNReal.instLE
      (@DecrAlmostLinearSSSP.Decremental.distance i.n i.k i.graph a
        (fun e =>
          @Nat.cast.{0} ENNReal
            (@AddMonoidWithOne.toNatCast.{0} ENNReal
              (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
            (i.weight e))
        i.source v)
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
        (DecrAlmostLinearSSSP.Decremental.Normalize.oldVertex i v)))))))) ∧ (((((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (a : Finset.{0} (Fin i.k)),
  @Eq.{1} ENNReal
    (@DecrAlmostLinearSSSP.Decremental.distance i.n i.k i.graph a
      (fun e =>
        @Nat.cast.{0} ENNReal
          (@AddMonoidWithOne.toNatCast.{0} ENNReal
            (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
          (i.weight e))
      i.source i.source)
    (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (a : Finset.{0} (Fin i.k)) (v : Fin i.n),
      @DecrAlmostLinearSSSP.Decremental.Reachable i.n i.k i.graph a i.source v →
        @LE.le.{0} ENNReal ENNReal.instLE
          (@DecrAlmostLinearSSSP.Decremental.distance i.n i.k i.graph a
            (fun e =>
              @Nat.cast.{0} ENNReal
                (@AddMonoidWithOne.toNatCast.{0} ENNReal
                  (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                (i.weight e))
            i.source v)
          (@Nat.cast.{0} ENNReal
            (@AddMonoidWithOne.toNatCast.{0} ENNReal
              (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) i.n i.W)))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    @LT.lt.{0} ENNReal (@Preorder.toLT.{0} ENNReal (@PartialOrder.toPreorder.{0} ENNReal ENNReal.instPartialOrder))
      (@Nat.cast.{0} ENNReal
        (@AddMonoidWithOne.toNatCast.{0} ENNReal
          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) i.n i.W))
      (@Nat.cast.{0} ENNReal
        (@AddMonoidWithOne.toNatCast.{0} ENNReal
          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
        (DecrAlmostLinearSSSP.Decremental.Normalize.sentinel i))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (a : Finset.{0} (Fin i.k)) (v : Fin i.n),
      @DecrAlmostLinearSSSP.Decremental.Reachable i.n i.k i.graph a i.source v →
        @Eq.{1} ENNReal
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
          (@DecrAlmostLinearSSSP.Decremental.distance i.n i.k i.graph a
            (fun e =>
              @Nat.cast.{0} ENNReal
                (@AddMonoidWithOne.toNatCast.{0} ENNReal
                  (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                (i.weight e))
            i.source v)))) ∧ (((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (a : Finset.{0} (Fin i.k)) (v : Fin i.n),
  Not (@DecrAlmostLinearSSSP.Decremental.Reachable i.n i.k i.graph a i.source v) →
    @LE.le.{0} ENNReal ENNReal.instLE
      (@Nat.cast.{0} ENNReal
        (@AddMonoidWithOne.toNatCast.{0} ENNReal
          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
        (DecrAlmostLinearSSSP.Decremental.Normalize.sentinel i))
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
        (DecrAlmostLinearSSSP.Decremental.Normalize.oldVertex i v))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (DecrAlmostLinearSSSP.Decremental.Normalize.cutoff i))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    @LT.lt.{0} ENNReal (@Preorder.toLT.{0} ENNReal (@PartialOrder.toPreorder.{0} ENNReal ENNReal.instPartialOrder))
      (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
        (@instHMul.{0} ENNReal
          (@Distrib.toMul.{0} ENNReal
            (@instDistribOfSemiring.{0} ENNReal (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
        (ENNReal.ofReal
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) i.accuracy))
        (@Nat.cast.{0} ENNReal
          (@AddMonoidWithOne.toNatCast.{0} ENNReal
            (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) i.n i.W)))
      (@Nat.cast.{0} ENNReal
        (@AddMonoidWithOne.toNatCast.{0} ENNReal
          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
        (DecrAlmostLinearSSSP.Decremental.Normalize.cutoff i))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
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
                (Not (@DecrAlmostLinearSSSP.Decremental.Reachable i.n i.k i.graph a i.source v))))) ∧ (∀ {action : DecrAlmostLinearSSSP.Decremental.Instruction → DecrAlmostLinearSSSP.Decremental.Structured.Cmd}
  {bound : DecrAlmostLinearSSSP.Decremental.Instruction → Nat}
  {P : DecrAlmostLinearSSSP.Decremental.Structured.Data → DecrAlmostLinearSSSP.Decremental.Machine → Prop} {B F : Nat},
  DecrAlmostLinearSSSP.Decremental.Instrumented.ActionSpec action bound P B F →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (g : DecrAlmostLinearSSSP.Decremental.Machine),
      DecrAlmostLinearSSSP.Decremental.Instrumented.MachineRep B F s g →
        P s g →
          ∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
            ∃ cost t,
              And
                (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                  (DecrAlmostLinearSSSP.Decremental.Instrumented.instruction action g.pc ins) s cost t)
                (And
                  (@LE.le.{0} Nat instLENat cost
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (bound ins)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (And
                    (DecrAlmostLinearSSSP.Decremental.Instrumented.MachineRep B F t
                      (DecrAlmostLinearSSSP.Decremental.instructionEffect ins
                        {
                          pc :=
                            @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.pc
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))),
                          realReg := g.realReg, natReg := g.natReg, realMem := g.realMem, natMem := g.natMem,
                          halted := g.halted, fault := g.fault,
                          work :=
                            @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.work
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) }))
                    (P t
                      (DecrAlmostLinearSSSP.Decremental.instructionEffect ins
                        {
                          pc :=
                            @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.pc
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))),
                          realReg := g.realReg, natReg := g.natReg, realMem := g.realMem, natMem := g.natMem,
                          halted := g.halted, fault := g.fault,
                          work :=
                            @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.work
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) }))))))))) ∧ ((((∀ {action : DecrAlmostLinearSSSP.Decremental.Instruction → DecrAlmostLinearSSSP.Decremental.Structured.Cmd}
  {bound : DecrAlmostLinearSSSP.Decremental.Instruction → Nat}
  {P : DecrAlmostLinearSSSP.Decremental.Structured.Data → DecrAlmostLinearSSSP.Decremental.Machine → Prop} {B F : Nat},
  DecrAlmostLinearSSSP.Decremental.Instrumented.ActionSpec action bound P B F →
    ∀ (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (start : Nat)
      (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (g : DecrAlmostLinearSSSP.Decremental.Machine),
      DecrAlmostLinearSSSP.Decremental.Instrumented.MachineRep B F s g →
        P s g →
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
                      (DecrAlmostLinearSSSP.Decremental.Instrumented.dispatch action start code) s cost t)
                    (And
                      (@LE.le.{0} Nat instLENat cost (DecrAlmostLinearSSSP.Decremental.Instrumented.charge bound code))
                      (And
                        (DecrAlmostLinearSSSP.Decremental.Instrumented.MachineRep B F t
                          (DecrAlmostLinearSSSP.Decremental.instructionEffect ins
                            {
                              pc :=
                                @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.pc
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))),
                              realReg := g.realReg, natReg := g.natReg, realMem := g.realMem, natMem := g.natMem,
                              halted := g.halted, fault := g.fault,
                              work :=
                                @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.work
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) }))
                        (P t
                          (DecrAlmostLinearSSSP.Decremental.instructionEffect ins
                            {
                              pc :=
                                @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.pc
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))),
                              realReg := g.realReg, natReg := g.natReg, realMem := g.realMem, natMem := g.natMem,
                              halted := g.halted, fault := g.fault,
                              work :=
                                @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.work
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) }))))) ∧ (∀ {action : DecrAlmostLinearSSSP.Decremental.Instruction → DecrAlmostLinearSSSP.Decremental.Structured.Cmd}
  {bound : DecrAlmostLinearSSSP.Decremental.Instruction → Nat}
  {P : DecrAlmostLinearSSSP.Decremental.Structured.Data → DecrAlmostLinearSSSP.Decremental.Machine → Prop} {B F : Nat},
  DecrAlmostLinearSSSP.Decremental.Instrumented.ActionSpec action bound P B F →
    ∀ (guest : DecrAlmostLinearSSSP.Decremental.Program) (t : Nat)
      (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (g : DecrAlmostLinearSSSP.Decremental.Machine),
      DecrAlmostLinearSSSP.Decremental.Instrumented.MachineRep B F s g →
        P s g →
          (∀ (j : Nat),
              @LT.lt.{0} Nat instLTNat j t →
                @Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.execute guest g j).halted Bool.false →
                  ∃ ins,
                    @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                      (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                        DecrAlmostLinearSSSP.Decremental.Instruction
                        (fun as i =>
                          @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                        (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) guest.code
                        (DecrAlmostLinearSSSP.Decremental.execute guest g j).pc)
                      (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins)) →
            @Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.execute guest g t).halted Bool.true →
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
                          t)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (And
                      (DecrAlmostLinearSSSP.Decremental.Instrumented.MachineRep B F u
                        (DecrAlmostLinearSSSP.Decremental.execute guest g t))
                      (P u (DecrAlmostLinearSSSP.Decremental.execute guest g t)))))) ∧ ((∀ {action : DecrAlmostLinearSSSP.Decremental.Instruction → DecrAlmostLinearSSSP.Decremental.Structured.Cmd}
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
                  (And (DecrAlmostLinearSSSP.Decremental.Instrumented.MachineRep B F u final) (P u final)))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Normalize.Native.inner s
    (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))
    (DecrAlmostLinearSSSP.Decremental.Normalize.Native.committed s)) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
    And
      (@Eq.{1} Nat
        ((DecrAlmostLinearSSSP.Decremental.Normalize.Native.prepared s).natReg
          (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))))
        (s.natMem
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (And
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.Normalize.Native.prepared s).natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))))
          (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))))
        (And
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.Normalize.Native.prepared s).natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (And
            (@Eq.{1} Real
              ((DecrAlmostLinearSSSP.Decremental.Normalize.Native.prepared s).realReg
                (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))))
              (s.realMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))))
            (And
              (@Eq.{1} Real
                ((DecrAlmostLinearSSSP.Decremental.Normalize.Native.prepared s).realReg
                  (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
                (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26)))))
              (@Eq.{1} Nat
                ((DecrAlmostLinearSSSP.Decremental.Normalize.Native.prepared s).natReg
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))))) ∧ (((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat
    ((DecrAlmostLinearSSSP.Decremental.Normalize.Native.flagged s).natReg
      (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
    (@ite.{1} Nat
      (Or
        (@LT.lt.{0} Nat instLTNat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))))
        (@LT.lt.{0} Real Real.instLT (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
          (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))))))
      (@instDecidableOr
        (@LT.lt.{0} Nat instLTNat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))))
        (@LT.lt.{0} Real Real.instLT (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
          (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
        ((s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).decLt
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))))
        ((s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26)))).decidableLT
          (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
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
          (s.realMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))))))) ∧ ((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
            DecrAlmostLinearSSSP.Decremental.Normalize.Native.callback k) ∧ ((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Normalize.Native.callback k) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Normalize.Native.inner k))))))) ∧ ((((((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Normalize.Native.inner k) ∧ (∀ {B : Nat} (n : Nat),
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
              (DecrAlmostLinearSSSP.Decremental.Normalize.Native.committed s) g)) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B : Nat} {bad : Option.{0} Nat}
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
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) }) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B : Nat} {bad : Option.{0} Nat}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.Normalize.Native.Image i B bad s g →
    ∀ (x : Nat),
      DecrAlmostLinearSSSP.Decremental.Normalize.Native.Image i B bad
        { realReg := s.realReg,
          natReg :=
            @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) x,
          realMem := s.realMem, natMem := s.natMem }
        g))) ∧ (((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B : Nat} {bad : Option.{0} Nat}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.Normalize.Native.Image i B bad s g →
    (∀ (v : Fin i.n), @Ne.{1} (Option.{0} Nat) bad (@Option.some.{0} Nat (@Fin.val i.n v))) →
      DecrAlmostLinearSSSP.Decremental.Normalize.Native.Image i B (@Option.none.{0} Nat) s g) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data}
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
              (s.realMem (@Fin.val i.n v))))) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.Normalize.Native.Image i B (@Option.none.{0} Nat) s g →
    ∀ (v : Fin i.n),
      @LE.le.{0} Nat instLENat (g.natMem (@Fin.val i.n v))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
        @Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.stored s.machine (@Fin.val i.n v))
          (DecrAlmostLinearSSSP.Decremental.Normalize.sanitize i
            (DecrAlmostLinearSSSP.Decremental.stored g (@Fin.val i.n v)))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
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
          (DecrAlmostLinearSSSP.Decremental.Normalize.sentinel i))) ∧ (∀ (entry : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Normalize.Native.headerCode entry)
    s (@OfNat.ofNat.{0} Nat (nat_lit 24) (instOfNatNat (nat_lit 24)))
    (DecrAlmostLinearSSSP.Decremental.Normalize.Native.headerData entry s)))))) ∧ ((((DecrAlmostLinearSSSP.Decremental.Structured.NoMemory DecrAlmostLinearSSSP.Decremental.Normalize.Native.weightCode) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 76) (instOfNatNat (nat_lit 76))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 78) (instOfNatNat (nat_lit 78))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
            DecrAlmostLinearSSSP.Decremental.Normalize.Native.weightCode k)) ∧ ((∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Normalize.Native.weightCode k) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {cost : Nat},
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Normalize.Native.weightCode s cost
        t →
      DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i t) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {cost : Nat},
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Normalize.Native.weightCode s cost
        t →
      @Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 76) (instOfNatNat (nat_lit 76))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))) ∧ (((∀ (entry : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.NoMemory
    (DecrAlmostLinearSSSP.Decremental.Normalize.Native.headerCode entry)) ∧ (∀ (entry k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18))) k →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
      (DecrAlmostLinearSSSP.Decremental.Normalize.Native.headerCode entry) k)) ∧ ((∀ (entry k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 28) (instOfNatNat (nat_lit 28))) →
          DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
            (DecrAlmostLinearSSSP.Decremental.Normalize.Native.headerCode entry) k) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Normalize.Native.fieldCode s
    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
    (DecrAlmostLinearSSSP.Decremental.Normalize.Native.fieldData s)) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  And
    (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.Normalize.Native.fieldData s).natMem
      (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natMem
        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))))))
    (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.Normalize.Native.fieldData s).realMem s.realMem))))))) ∧ (((((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
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
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 84) (instOfNatNat (nat_lit 84))) →
        DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Normalize.Native.fieldCode
          k)) ∧ ((∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Normalize.Native.fieldCode k) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  ∃ cost,
    And
      (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Normalize.Native.headRedirect s
        cost (DecrAlmostLinearSSSP.Decremental.Normalize.Native.redirected s))
      (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))) ∧ (((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  ∃ cost,
    And
      (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Normalize.Native.headCode s
        cost (DecrAlmostLinearSSSP.Decremental.Normalize.Native.headData s))
      (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    And
      (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.Normalize.Native.headData s).natMem
        (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natMem
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@ite.{1} Nat
              (@Eq.{1} Nat (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80)))))
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72)))))
              (instDecidableEqNat (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80)))))
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72)))))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 66) (instOfNatNat (nat_lit 66))))
              (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80)))))))))
      (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.Normalize.Native.headData s).realMem s.realMem))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
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
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))) ∧ ((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 84) (instOfNatNat (nat_lit 84))) →
        DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Normalize.Native.headCode
          k) ∧ (∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Normalize.Native.headCode k))))) ∧ ((((∀ {B bank logical value : Nat} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {natural : Nat → Nat}
  {real : Nat → Real},
  DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B bank s natural real →
    @Eq.{1} (Nat → Nat) t.natMem
        (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natMem
          (DecrAlmostLinearSSSP.Decremental.bankAddress B bank logical)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (DecrAlmostLinearSSSP.Decremental.bankFactor bank) value)) →
      @Eq.{1} (Nat → Real) t.realMem s.realMem →
        DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B bank t
          (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat natural logical value) real) ∧ (∀ (B logical : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (natural : Nat → Nat) (real : Nat → Real),
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
        real)) ∧ ((∀ (B logical : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (natural : Nat → Nat) (real : Nat → Real),
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
          real) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (B : Nat),
  @LE.le.{0} Nat instLENat B (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82)))) →
    ∀ (a : Nat),
      @LT.lt.{0} Nat instLTNat a B →
        And (@Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.Normalize.Native.fieldData s).natMem a) (s.natMem a))
          (@Eq.{1} Real ((DecrAlmostLinearSSSP.Decremental.Normalize.Native.fieldData s).realMem a) (s.realMem a))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (B : Nat),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @LE.le.{0} Nat instLENat B (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82)))) →
      ∀ (a : Nat),
        @LT.lt.{0} Nat instLTNat a B →
          And (@Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.Normalize.Native.headData s).natMem a) (s.natMem a))
            (@Eq.{1} Real ((DecrAlmostLinearSSSP.Decremental.Normalize.Native.headData s).realMem a) (s.realMem a)))))) ∧ (((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  ∃ cost,
    And
      (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Normalize.Native.recordCode s
        cost (DecrAlmostLinearSSSP.Decremental.Normalize.Native.recordData s))
      (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 21) (instOfNatNat (nat_lit 21))))) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 84) (instOfNatNat (nat_lit 84))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 90) (instOfNatNat (nat_lit 90))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
            DecrAlmostLinearSSSP.Decremental.Normalize.Native.recordCode k)) ∧ ((∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Normalize.Native.recordCode k) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
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
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i s →
    DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i
      (DecrAlmostLinearSSSP.Decremental.Normalize.Native.recordData s))))))))) := by
  exact ⟨⟨⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Structured.accumulate_eval,DecrAlmostLinearSSSP.Decremental.Structured.conditionalOne_eval⟩,⟨DecrAlmostLinearSSSP.Decremental.Structured.conditionalOneState_mem,DecrAlmostLinearSSSP.Decremental.Structured.conditionalOneState_nat⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Structured.conditionalOneState_nat_other,DecrAlmostLinearSSSP.Decremental.Structured.conditionalOneState_real⟩,⟨DecrAlmostLinearSSSP.Decremental.Normalize.old_edge_active,⟨DecrAlmostLinearSSSP.Decremental.Normalize.added_edge_active,DecrAlmostLinearSSSP.Decremental.Normalize.oldEdge_injective⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Normalize.active_live,DecrAlmostLinearSSSP.Decremental.Normalize.walk_lift⟩,⟨DecrAlmostLinearSSSP.Decremental.Normalize.walk_from_sink,DecrAlmostLinearSSSP.Decremental.Normalize.walk_project⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.minimum_walk_avoids_source,DecrAlmostLinearSSSP.Decremental.Normalize.lifted_weight⟩,⟨DecrAlmostLinearSSSP.Decremental.Normalize.distance_upper,⟨DecrAlmostLinearSSSP.Decremental.Normalize.reachable_active,DecrAlmostLinearSSSP.Decremental.Normalize.distance_lower_guarded⟩⟩⟩⟩⟩,⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Normalize.distance_self,DecrAlmostLinearSSSP.Decremental.Normalize.finite_distance_bound⟩,⟨DecrAlmostLinearSSSP.Decremental.Normalize.finite_sentinel_gap,DecrAlmostLinearSSSP.Decremental.Normalize.distance_eq_original⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Normalize.unreachable_distance_gap,DecrAlmostLinearSSSP.Decremental.Normalize.cutoff_positive⟩,⟨DecrAlmostLinearSSSP.Decremental.Normalize.finite_cutoff_gap,⟨DecrAlmostLinearSSSP.Decremental.Normalize.sanitize_correct,DecrAlmostLinearSSSP.Decremental.Instrumented.instruction_eval⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Instrumented.dispatch_eval,DecrAlmostLinearSSSP.Decremental.Instrumented.interpreter_eval⟩,⟨DecrAlmostLinearSSSP.Decremental.Instrumented.interpreter_ends,⟨DecrAlmostLinearSSSP.Decremental.Normalize.Native.inner_eval,DecrAlmostLinearSSSP.Decremental.Normalize.Native.prepared_values⟩⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Normalize.Native.flagged_values,DecrAlmostLinearSSSP.Decremental.Normalize.Native.committed_memory⟩,⟨DecrAlmostLinearSSSP.Decremental.Normalize.Native.callback_nat_frame,⟨DecrAlmostLinearSSSP.Decremental.Normalize.Native.callback_real_frame,DecrAlmostLinearSSSP.Decremental.Normalize.Native.inner_nat_frame⟩⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Normalize.Native.inner_real_frame,DecrAlmostLinearSSSP.Decremental.Normalize.Native.inner_shadow⟩,⟨DecrAlmostLinearSSSP.Decremental.Normalize.Native.Image.header,DecrAlmostLinearSSSP.Decremental.Normalize.Native.Image.scratch⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Normalize.Native.Image.remove_bad,DecrAlmostLinearSSSP.Decremental.Normalize.Native.Image.normal⟩,⟨DecrAlmostLinearSSSP.Decremental.Normalize.Native.Image.stored,⟨DecrAlmostLinearSSSP.Decremental.Normalize.Native.weightCode_eval,DecrAlmostLinearSSSP.Decremental.Normalize.Native.headerCode_eval⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Normalize.Native.weightCode_no_memory,DecrAlmostLinearSSSP.Decremental.Normalize.Native.weightCode_nat_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.Normalize.Native.weightCode_real_frame,⟨DecrAlmostLinearSSSP.Decremental.Normalize.Native.weightCode_captured,DecrAlmostLinearSSSP.Decremental.Normalize.Native.weightCode_vertices⟩⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Normalize.Native.headerCode_no_memory,DecrAlmostLinearSSSP.Decremental.Normalize.Native.headerCode_nat_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.Normalize.Native.headerCode_real_frame,⟨DecrAlmostLinearSSSP.Decremental.Normalize.Native.field_eval,DecrAlmostLinearSSSP.Decremental.Normalize.Native.field_memory⟩⟩⟩⟩⟩,⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Normalize.Native.field_pointers,DecrAlmostLinearSSSP.Decremental.Normalize.Native.field_nat_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.Normalize.Native.field_real_frame,DecrAlmostLinearSSSP.Decremental.Normalize.Native.redirect_eval⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Normalize.Native.head_eval,DecrAlmostLinearSSSP.Decremental.Normalize.Native.head_memory⟩,⟨DecrAlmostLinearSSSP.Decremental.Normalize.Native.head_pointers,⟨DecrAlmostLinearSSSP.Decremental.Normalize.Native.head_nat_frame,DecrAlmostLinearSSSP.Decremental.Normalize.Native.head_real_frame⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.SourceMemory.Image.write_exact,DecrAlmostLinearSSSP.Decremental.Normalize.Native.field_image⟩,⟨DecrAlmostLinearSSSP.Decremental.Normalize.Native.head_image,⟨DecrAlmostLinearSSSP.Decremental.Normalize.Native.field_prefix,DecrAlmostLinearSSSP.Decremental.Normalize.Native.head_prefix⟩⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Normalize.Native.record_eval,DecrAlmostLinearSSSP.Decremental.Normalize.Native.record_nat_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.Normalize.Native.record_real_frame,⟨DecrAlmostLinearSSSP.Decremental.Normalize.Native.record_pointers,DecrAlmostLinearSSSP.Decremental.Normalize.Native.record_captured⟩⟩⟩⟩⟩⟩⟩
