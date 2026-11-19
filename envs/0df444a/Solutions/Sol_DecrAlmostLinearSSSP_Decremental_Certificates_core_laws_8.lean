-- Prove2me | solution 1 for DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_8
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T17:36:30.814582+00:00
-- url     : https://prove2.me/submissions/12126385-96cd-4e74-b4f8-4eaafcd4976a

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
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_core_laws_2
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_core_laws_3
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_core_laws_4
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_core_laws_5
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_core_laws_6
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_core_laws_7
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
theorem DecrAlmostLinearSSSP.Decremental.Structured.CodeAt.left : ∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {start : Nat}
  {a b : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction},
  DecrAlmostLinearSSSP.Decremental.Structured.CodeAt p start
      (@HAppend.hAppend.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (@instHAppendOfAppend.{0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (@List.instAppend.{0} DecrAlmostLinearSSSP.Decremental.Instruction))
        a b) →
    DecrAlmostLinearSSSP.Decremental.Structured.CodeAt p start a := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.1.2.1.2.2.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.Structured.eval_natural : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (d q : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.natural d q) s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    { realReg := s.realReg, natReg := @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natReg d q,
      realMem := s.realMem, natMem := s.natMem } := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.1.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Structured.eval_add : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (d a b : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.add d a b) s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    {
      realReg :=
        @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realReg d
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (s.realReg a) (s.realReg b)),
      natReg := s.natReg, realMem := s.realMem, natMem := s.natMem } := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.1.2.1.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Structured.eval_div : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (d a b : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.div d a b) s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    {
      realReg :=
        @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realReg d
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (s.realReg a) (s.realReg b)),
      natReg := s.natReg, realMem := s.realMem, natMem := s.natMem } := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Structured.eval_nadd : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (d a b : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.nadd d a b) s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    { realReg := s.realReg,
      natReg :=
        @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natReg d
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (s.natReg a) (s.natReg b)),
      realMem := s.realMem, natMem := s.natMem } := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.1.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Structured.eval_nsub : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (d a b : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.nsub d a b) s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    { realReg := s.realReg,
      natReg :=
        @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natReg d
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (s.natReg a) (s.natReg b)),
      realMem := s.realMem, natMem := s.natMem } := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.1.2.2.2.2.2
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
theorem DecrAlmostLinearSSSP.Decremental.Exact.TriePop.body_nat_frame : ∀ k ∉ DecrAlmostLinearSSSP.Decremental.Exact.TriePop.registers,
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.TriePop.body k := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.1.1.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.Powers.body_nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 248) (instOfNatNat (nat_lit 248))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 250) (instOfNatNat (nat_lit 250))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 252) (instOfNatNat (nat_lit 252))) →
        DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.Powers.body k := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.1.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.ShadowRep.real_register : ∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    ∀ (a : Nat) (x : Real),
      DecrAlmostLinearSSSP.Decremental.ShadowRep base F
        { pc := c.pc,
          realReg :=
            @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat c.realReg
              (DecrAlmostLinearSSSP.Decremental.shadowReg a) x,
          natReg := c.natReg, realMem := c.realMem, natMem := c.natMem, halted := c.halted, fault := c.fault,
          work := c.work }
        { pc := g.pc, realReg := @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat g.realReg a x,
          natReg := g.natReg, realMem := g.realMem, natMem := g.natMem, halted := g.halted, fault := g.fault,
          work := g.work } := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.2.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.ShadowRep.nat_register : ∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    ∀ (a x : Nat),
      DecrAlmostLinearSSSP.Decremental.ShadowRep base F
        { pc := c.pc, realReg := c.realReg,
          natReg :=
            @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat c.natReg
              (DecrAlmostLinearSSSP.Decremental.shadowReg a)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F x),
          realMem := c.realMem, natMem := c.natMem, halted := c.halted, fault := c.fault, work := c.work }
        { pc := g.pc, realReg := g.realReg,
          natReg := @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat g.natReg a x, realMem := g.realMem,
          natMem := g.natMem, halted := g.halted, fault := g.fault, work := g.work } := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.2.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.InputCapture.no_memory : DecrAlmostLinearSSSP.Decremental.Structured.NoMemory DecrAlmostLinearSSSP.Decremental.InputCapture.code := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.1.2.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.Powers.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 248) (instOfNatNat (nat_lit 248))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 250) (instOfNatNat (nat_lit 250))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 252) (instOfNatNat (nat_lit 252))) →
        DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.Powers.code k := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.2.1.1.1.1.1
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
theorem DecrAlmostLinearSSSP.Decremental.Reachable.trans : ∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {u v w : Fin n},
  @DecrAlmostLinearSSSP.Decremental.Reachable n k g active u v →
    @DecrAlmostLinearSSSP.Decremental.Reachable n k g active v w →
      @DecrAlmostLinearSSSP.Decremental.Reachable n k g active u w := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.StaticImage.frame : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {l : DecrAlmostLinearSSSP.Decremental.Exact.Layout.Addresses}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.StaticImage i l s →
    (∀ (a : Nat),
        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
            (DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.staticFootprint i l) a →
          @Eq.{1} Nat (t.natMem a) (s.natMem a)) →
      DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.StaticImage i l t := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_6.2.2.1.1.2.2
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
theorem DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory.popped : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)} {tentative : Fin i.n → Option.{0} Nat}
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
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_8.1.1.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State.run : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)},
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
                      (i.dist deleted v))))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_8.1.1.2.2.1.1
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
theorem DecrAlmostLinearSSSP.Decremental.PreservesOutside.refl : ∀ (base F : Nat) (c : DecrAlmostLinearSSSP.Decremental.Machine),
  DecrAlmostLinearSSSP.Decremental.PreservesOutside base F c c := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_2.1.1.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.PreservesOutside.trans : ∀ {base F : Nat} {c d e : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.PreservesOutside base F c d →
    DecrAlmostLinearSSSP.Decremental.PreservesOutside base F d e →
      DecrAlmostLinearSSSP.Decremental.PreservesOutside base F c e := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_2.1.1.1.1.2.2
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
theorem DecrAlmostLinearSSSP.Decremental.TapeCopy.start_nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 162) (instOfNatNat (nat_lit 162))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 164) (instOfNatNat (nat_lit 164))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 170) (instOfNatNat (nat_lit 170))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 166) (instOfNatNat (nat_lit 166))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.TapeCopy.start k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_4.2.2.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.SourceSetup.nat_even_frame : ∀ (N entry k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 54) (instOfNatNat (nat_lit 54))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
            (DecrAlmostLinearSSSP.Decremental.SourceSetup.code N entry) k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_5.2.1.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.SourceSetup.real_even_frame : ∀ (N entry k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.SourceSetup.code N entry)
        k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_5.2.1.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.SourceSnapshot.nat_frame : ∀ (N k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 54) (instOfNatNat (nat_lit 54))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.SourceSnapshot.code N) k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_5.2.1.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.SourceCall.nat_even_frame : ∀ (N entry : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program) (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 54) (instOfNatNat (nat_lit 54))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
            (DecrAlmostLinearSSSP.Decremental.SourceCall.code N entry p) k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_5.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.SourceCall.real_even_frame : ∀ (N entry : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program) (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.SourceCall.code N entry p)
        k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_5.2.1.2.2.2.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.LinkedScan.body_nat_frame : ∀ (k : Nat),
  Or (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 34) (instOfNatNat (nat_lit 34))))
      (Or (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 36) (instOfNatNat (nat_lit 36))))
        (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 38) (instOfNatNat (nat_lit 38))))) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.LinkedScan.body k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_8.1.1.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.LinkedScan.eval_loop : ∀ (rows : List.{0} DecrAlmostLinearSSSP.Decremental.LinkedScan.Row)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (vertex : Nat),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
      (DecrAlmostLinearSSSP.Decremental.LinkedScan.headAddress rows) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 38) (instOfNatNat (nat_lit 38)))) vertex →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 34) (instOfNatNat (nat_lit 34))))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 36) (instOfNatNat (nat_lit 36))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
            DecrAlmostLinearSSSP.Decremental.LinkedScan.RowsView s vertex rows →
              ∃ cost t,
                And
                  (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.LinkedScan.loop s
                    cost t)
                  (And
                    (@LE.le.{0} Nat instLENat cost
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
                          (DecrAlmostLinearSSSP.Decremental.LinkedScan.skipped rows))
                        (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))))
                    (And
                      (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
                        (DecrAlmostLinearSSSP.Decremental.LinkedScan.selectedAddress rows))
                      (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_8.1.1.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.DirtyMark.insert_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
      DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.DirtyMark.insertCode s
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
        (DecrAlmostLinearSSSP.Decremental.DirtyMark.inserted s) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_8.1.2.2.2.2.2.2
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
theorem DecrAlmostLinearSSSP.Decremental.Native.PointerBases.body : ∀ {record pointer flags list cost : Nat} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.PointerBases record pointer flags list s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Native.pointerBody s cost t →
      DecrAlmostLinearSSSP.Decremental.Native.PointerBases record pointer flags list t := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_8.2.2.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.Native.PublicFrame.refl : ∀ (l : DecrAlmostLinearSSSP.Decremental.Native.PointerLayout) (n : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data), DecrAlmostLinearSSSP.Decremental.Native.PublicFrame l n s s := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_8.2.2.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Native.PublicFrame.trans : ∀ {l : DecrAlmostLinearSSSP.Decremental.Native.PointerLayout} {n : Nat}
  {s t u : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.PublicFrame l n s t →
    DecrAlmostLinearSSSP.Decremental.Native.PublicFrame l n t u →
      DecrAlmostLinearSSSP.Decremental.Native.PublicFrame l n s u := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_8.2.2.2.1.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.DirtyCommit.eval_loop : ∀ {n : Nat} (l : DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout n) (flagBase listBase : Nat),
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
        ∀ (xs : List.{0} (Fin n)) (readBase : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
          @LE.le.{0} Nat instLENat listBase readBase →
            @DecrAlmostLinearSSSP.Decremental.AnswerTable.Image n l s →
              @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 96) (instOfNatNat (nat_lit 96))))
                  (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.pointerBase n l) →
                @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72))))
                    (@Fin.val n (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.source n l)) →
                  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 98) (instOfNatNat (nat_lit 98)))) flagBase →
                    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 192) (instOfNatNat (nat_lit 192))))
                              readBase →
                            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 194) (instOfNatNat (nat_lit 194))))
                                (@List.length.{0} (Fin n) xs) →
                              (∀ (j : Nat) (hj : @LT.lt.{0} Nat instLTNat j (@List.length.{0} (Fin n) xs)),
                                  @Eq.{1} Nat
                                    (s.natMem
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) readBase
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
                                    (@Fin.val n
                                      (@GetElem.getElem.{0, 0, 0} (List.{0} (Fin n)) Nat (Fin n)
                                        (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} (Fin n) as))
                                        (@List.instGetElemNatLtLength.{0} (Fin n)) xs j hj))) →
                                ∃ cost t,
                                  And
                                    (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                      DecrAlmostLinearSSSP.Decremental.DirtyCommit.loop s cost t)
                                    (And
                                      (@LE.le.{0} Nat instLENat cost
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))
                                            (@List.length.{0} (Fin n) xs))
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                      (And
                                        (@Eq.{1} Nat
                                          (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 192) (instOfNatNat (nat_lit 192))))
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) readBase
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                              (@List.length.{0} (Fin n) xs))))
                                        (And
                                          (@Eq.{1} Nat
                                            (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 194) (instOfNatNat (nat_lit 194))))
                                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                          (And (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Image n l t)
                                            (And
                                              (∀ (v : Fin n),
                                                @Membership.mem.{0, 0} (Fin n) (List.{0} (Fin n))
                                                    (@List.instMembership.{0} (Fin n)) xs v →
                                                  And
                                                    (@Eq.{1} Nat (t.natMem (@Fin.val n v))
                                                      (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.flag n l v))
                                                    (And
                                                      (@Eq.{1} Real (t.realMem (@Fin.val n v))
                                                        (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.realValue
                                                          n l v))
                                                      (@Eq.{1} Nat
                                                        (t.natMem
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat) flagBase
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                (instOfNatNat (nat_lit 2)))
                                                              (@Fin.val n v))))
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
                                              (∀ (address : Nat),
                                                (∀ (v : Fin n),
                                                    @Membership.mem.{0, 0} (Fin n) (List.{0} (Fin n))
                                                        (@List.instMembership.{0} (Fin n)) xs v →
                                                      And (@Ne.{1} Nat address (@Fin.val n v))
                                                        (@Ne.{1} Nat address
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat) flagBase
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                (instOfNatNat (nat_lit 2)))
                                                              (@Fin.val n v))))) →
                                                  And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                                    (@Eq.{1} Real (t.realMem address) (s.realMem address)))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_9.1.2.2.2.1.2
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
theorem DecrAlmostLinearSSSP.Decremental.Native.ReportFrame.refl : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (B reserve N j : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Native.ReportFrame i B reserve N j s s := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_11.1.1.2.2.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.Native.ReportFrame.reports : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B reserve N : Nat}
  {j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.ReportFrame i B reserve N
      (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) s t →
    ∀ (r : Nat),
      @LE.le.{0} Nat instLENat r reserve →
        @Eq.{1} Nat
          (t.natMem
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i)
                  reserve N).reports
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)))
          (s.natMem
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i)
                  reserve N).reports
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_11.1.2.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.body_nat_frame : ∀ (k : Nat),
  @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat)
      DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.fixedNat k →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.body k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_11.1.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.Queue.head : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B reserve N offset address : Nat} {rest : List.{0} Nat}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.Queue i B reserve N offset (@List.cons.{0} Nat address rest) s →
    @Eq.{1} Nat (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 210) (instOfNatNat (nat_lit 210))))) address := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_11.2.1.1.1.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.Native.UpdateTraversal.start_nat_frame : ∀ (N k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 78) (instOfNatNat (nat_lit 78))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 110) (instOfNatNat (nat_lit 110))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 134) (instOfNatNat (nat_lit 134))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
            (DecrAlmostLinearSSSP.Decremental.Native.UpdateTraversal.start N) k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_12.2.1.2.1.2.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.physical_norm_cut : ∀ {n k : Nat} (h : DecrAlmostLinearSSSP.Decremental.Physical n k) (C : Finset.{0} (Fin n)) (tau : Real),
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) tau →
    @Eq.{1} Real
      (@DecrAlmostLinearSSSP.Decremental.physicalNorm n k h (@DecrAlmostLinearSSSP.Decremental.cutDirection n C tau))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) tau
        (@DecrAlmostLinearSSSP.Decremental.cutCapacity n k h C)) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_3.1.1.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.cachedPhysical_norm_eq : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (s : DecrAlmostLinearSSSP.Decremental.State b) (x : Fin b.input.n → Real),
  @Eq.{1} Real
    (@DecrAlmostLinearSSSP.Decremental.physicalNorm b.input.n
      (@Fintype.card.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)
        (@instFintypeSum.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b)
          (Fin.fintype b.input.k) (DecrAlmostLinearSSSP.Decremental.instFintypeReturnVertex b)))
      (DecrAlmostLinearSSSP.Decremental.cachedPhysical b s) x)
    (DecrAlmostLinearSSSP.Decremental.norm b (@DecrAlmostLinearSSSP.Decremental.State.cache b s) x) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_3.1.1.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.RuntimeInvariant.toggle : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LE.le.{0} Real Real.instLE
      (@OfNat.ofNat.{0} Real (nat_lit 32)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
      K →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.State b),
      DecrAlmostLinearSSSP.Decremental.RuntimeInvariant b K s →
        @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
            (@DecrAlmostLinearSSSP.Decremental.State.pending b s)
            (@List.nil.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) →
          ∀ (r : DecrAlmostLinearSSSP.Decremental.CutReply b),
            @DecrAlmostLinearSSSP.Decremental.RatioGuarantee b.input.n
                (@Fintype.card.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)
                  (@instFintypeSum.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b)
                    (Fin.fintype b.input.k) (DecrAlmostLinearSSSP.Decremental.instFintypeReturnVertex b)))
                (DecrAlmostLinearSSSP.Decremental.cachedPhysical b s) K
                (@DecrAlmostLinearSSSP.Decremental.CutReply.G b r) (@DecrAlmostLinearSSSP.Decremental.CutReply.U b r)
                (@DecrAlmostLinearSSSP.Decremental.CutReply.cut b r) →
              @LT.lt.{0} Real Real.instLT
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@DecrAlmostLinearSSSP.Decremental.CutReply.G b r)
                    (@DecrAlmostLinearSSSP.Decremental.CutReply.U b r))
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@Neg.neg.{0} Real Real.instNeg
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@OfNat.ofNat.{0} Real (nat_lit 4)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                      K)) →
                ∀ (reports : List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)),
                  DecrAlmostLinearSSSP.Decremental.ReportsComplete b K s r reports →
                    DecrAlmostLinearSSSP.Decremental.RuntimeInvariant b K
                      (DecrAlmostLinearSSSP.Decremental.reportedToggle b K s r reports) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_3.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.reportVolume_append : ∀ (cs : List.{0} DecrAlmostLinearSSSP.Decremental.Machine) (current final : DecrAlmostLinearSSSP.Decremental.Machine),
  @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Machine)
      (@List.getLast?.{0} DecrAlmostLinearSSSP.Decremental.Machine cs)
      (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Machine current) →
    @Eq.{1} Nat
      (DecrAlmostLinearSSSP.Decremental.reportVolume
        (@HAppend.hAppend.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Machine)
          (List.{0} DecrAlmostLinearSSSP.Decremental.Machine) (List.{0} DecrAlmostLinearSSSP.Decremental.Machine)
          (@instHAppendOfAppend.{0} (List.{0} DecrAlmostLinearSSSP.Decremental.Machine)
            (@List.instAppend.{0} DecrAlmostLinearSSSP.Decremental.Machine))
          cs
          (@List.cons.{0} DecrAlmostLinearSSSP.Decremental.Machine final
            (@List.nil.{0} DecrAlmostLinearSSSP.Decremental.Machine))))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (DecrAlmostLinearSSSP.Decremental.reportVolume cs) (DecrAlmostLinearSSSP.Decremental.reportCount final)) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.1.2.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreRequest.nat_eval : ∀ (slot source : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.CoreRequest.natCode slot source) s
    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
    (DecrAlmostLinearSSSP.Decremental.CoreRequest.natResult slot source s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.1.2.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreRequest.real_eval : ∀ (slot source : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.CoreRequest.realCode slot source) s
    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
    (DecrAlmostLinearSSSP.Decremental.CoreRequest.realResult slot source s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.1.2.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreRequest.nat_values : ∀ (slot source : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Ne.{1} Nat source (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
    And
      (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.CoreRequest.natResult slot source s).natMem
        (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natMem
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) slot))
          (s.natReg source)))
      (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.CoreRequest.natResult slot source s).realMem s.realMem) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.1.2.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreRequest.real_values : ∀ (slot source : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  And
    (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.CoreRequest.realResult slot source s).realMem
      (@Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realMem
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) slot))
        (s.realReg source)))
    (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.CoreRequest.realResult slot source s).natMem s.natMem) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.1.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreRequest.nat_frame : ∀ (slot source k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
      (DecrAlmostLinearSSSP.Decremental.CoreRequest.natCode slot source) k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.1.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreRequest.real_nat_frame : ∀ (slot source k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
      (DecrAlmostLinearSSSP.Decremental.CoreRequest.realCode slot source) k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.1.2.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreRequest.nat_real_frame : ∀ (slot source k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
    (DecrAlmostLinearSSSP.Decremental.CoreRequest.natCode slot source) k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.1.2.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreRequest.real_frame : ∀ (slot source k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
    (DecrAlmostLinearSSSP.Decremental.CoreRequest.realCode slot source) k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.1.2.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreRequest.SavedImage.nat_patch : ∀ (N slot source value : Nat) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreRequest.SavedImage N g s →
    @Ne.{1} Nat source (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
      @Eq.{1} Nat (s.natReg source)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) value) →
        DecrAlmostLinearSSSP.Decremental.CoreRequest.SavedImage N
          { pc := g.pc, realReg := g.realReg,
            natReg := @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat g.natReg slot value,
            realMem := g.realMem, natMem := g.natMem, halted := g.halted, fault := g.fault, work := g.work }
          (DecrAlmostLinearSSSP.Decremental.CoreRequest.natResult slot source s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.1.2.2.1.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreRequest.SavedImage.real_patch : ∀ (N slot source : Nat) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreRequest.SavedImage N g s →
    DecrAlmostLinearSSSP.Decremental.CoreRequest.SavedImage N
      { pc := g.pc,
        realReg := @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat g.realReg slot (s.realReg source),
        natReg := g.natReg, realMem := g.realMem, natMem := g.natMem, halted := g.halted, fault := g.fault,
        work := g.work }
      (DecrAlmostLinearSSSP.Decremental.CoreRequest.realResult slot source s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.1.2.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreRequest.SavedImage.resume : ∀ (N entry : Nat) (g : DecrAlmostLinearSSSP.Decremental.Machine) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreRequest.SavedImage N g s →
    DecrAlmostLinearSSSP.Decremental.CoreRequest.SavedImage N (DecrAlmostLinearSSSP.Decremental.resume g entry) s := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.1.2.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail.ends_of_bound : ∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {c d : DecrAlmostLinearSSSP.Decremental.Machine} {N : Nat},
  DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail N c →
    @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.registerBound p.code) N →
      DecrAlmostLinearSSSP.Decremental.Ends p c d → DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail N d := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.1.2.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.cutRequest_zero_tail : ∀ {n k N : Nat} (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine)
  (op : DecrAlmostLinearSSSP.Decremental.CutOp n k),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) N →
    DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail N c →
      DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail N (@DecrAlmostLinearSSSP.Decremental.cutRequest n k p c op) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.2.1.1.1.1.1
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
theorem DecrAlmostLinearSSSP.Decremental.CoreSource.Image.nat_patch : ∀ (B R N slot source value : Nat) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N g s →
    (∃ r,
        @Eq.{1} Nat R
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
      @Ne.{1} Nat source (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
        @Eq.{1} Nat (s.natReg source)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) value) →
          DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N
            { pc := g.pc, realReg := g.realReg,
              natReg := @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat g.natReg slot value,
              realMem := g.realMem, natMem := g.natMem, halted := g.halted, fault := g.fault, work := g.work }
            (DecrAlmostLinearSSSP.Decremental.CoreRequest.natResult slot source s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.2.1.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreSource.Image.real_patch : ∀ (B R N slot source : Nat) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N g s →
    (∃ r,
        @Eq.{1} Nat R
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
      DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N
        { pc := g.pc,
          realReg := @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat g.realReg slot (s.realReg source),
          natReg := g.natReg, realMem := g.realMem, natMem := g.natMem, halted := g.halted, fault := g.fault,
          work := g.work }
        (DecrAlmostLinearSSSP.Decremental.CoreRequest.realResult slot source s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.2.1.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreRequest.tag_eval : ∀ (tag : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.CoreRequest.tagCode tag) s
    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
    (DecrAlmostLinearSSSP.Decremental.CoreRequest.tagged tag s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.2.1.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreRequest.SavedImage.tagged : ∀ (N tag : Nat) (g : DecrAlmostLinearSSSP.Decremental.Machine) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreRequest.SavedImage N g s →
    DecrAlmostLinearSSSP.Decremental.CoreRequest.SavedImage N
      { pc := g.pc, realReg := g.realReg,
        natReg :=
          @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat g.natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) tag,
        realMem := g.realMem, natMem := g.natMem, halted := g.halted, fault := g.fault, work := g.work }
      (DecrAlmostLinearSSSP.Decremental.CoreRequest.tagged tag s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.2.1.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreSource.Image.nat_register : ∀ (B R N k value : Nat) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N g s →
    @Eq.{1} Nat
        (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) k
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))) →
              @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))) →
                DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N g
                  { realReg := s.realReg,
                    natReg := @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natReg k value,
                    realMem := s.realMem, natMem := s.natMem } := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.2.1.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreSource.Image.real_register : ∀ (B R N k : Nat) (value : Real) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N g s →
    @Eq.{1} Nat
        (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) k
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
      DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N g
        { realReg := @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realReg k value,
          natReg := s.natReg, realMem := s.realMem, natMem := s.natMem } := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.2.1.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreSource.Image.tagged : ∀ (B R N tag : Nat) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N g s →
    (∃ r,
        @Eq.{1} Nat R
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
      DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N
        { pc := g.pc, realReg := g.realReg,
          natReg :=
            @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat g.natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) tag,
          realMem := g.realMem, natMem := g.natMem, halted := g.halted, fault := g.fault, work := g.work }
        (DecrAlmostLinearSSSP.Decremental.CoreRequest.tagged tag s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.2.1.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreRequest.insert_machine : ∀ {n k : Nat} (p : DecrAlmostLinearSSSP.Decremental.Program) (g : DecrAlmostLinearSSSP.Decremental.Machine) (e : Fin k)
  (a b : Fin n) (u : Real),
  @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
    (@DecrAlmostLinearSSSP.Decremental.cutRequest n k p g (@DecrAlmostLinearSSSP.Decremental.CutOp.insert n k e a b u))
    (have __src := DecrAlmostLinearSSSP.Decremental.resume g p.update;
    { pc := __src.pc,
      realReg :=
        @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat g.realReg
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) u,
      natReg :=
        @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
          (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
            (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
              (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat g.natReg
                (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) (@Fin.val k e))
            (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (@Fin.val n a))
          (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) (@Fin.val n b),
      realMem := __src.realMem, natMem := __src.natMem, halted := __src.halted, fault := __src.fault,
      work := __src.work }) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.2.1.2.1.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreRequest.paired_machine : ∀ {n k : Nat} (p : DecrAlmostLinearSSSP.Decremental.Program) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  (a b : Fin n) (delta : Real),
  @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
    (@DecrAlmostLinearSSSP.Decremental.cutRequest n k p g
      (@DecrAlmostLinearSSSP.Decremental.CutOp.paired n k a b delta))
    (have __src := DecrAlmostLinearSSSP.Decremental.resume g p.update;
    { pc := __src.pc,
      realReg :=
        @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat g.realReg
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) delta,
      natReg :=
        @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
          (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
            (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat g.natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (@Fin.val n a))
          (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) (@Fin.val n b),
      realMem := __src.realMem, natMem := __src.natMem, halted := __src.halted, fault := __src.fault,
      work := __src.work }) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.2.1.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreRequest.tag_nat_frame : ∀ (tag k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 632) (instOfNatNat (nat_lit 632))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.CoreRequest.tagCode tag) k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.2.1.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreRequest.tag_real_frame : ∀ (tag k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.CoreRequest.tagCode tag) k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreRequest.query_eval : ∀ {n k : Nat} (B R N source : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program)
  (g : DecrAlmostLinearSSSP.Decremental.Machine) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (v : Fin n),
  DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N g s →
    (∃ r,
        @Eq.{1} Nat R
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
      @Ne.{1} Nat source (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
        @Ne.{1} Nat source (@OfNat.ofNat.{0} Nat (nat_lit 632) (instOfNatNat (nat_lit 632))) →
          @Eq.{1} Nat (s.natReg source)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val n v)) →
            ∃ t,
              And
                (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                  (DecrAlmostLinearSSSP.Decremental.CoreRequest.queryCode source) s
                  (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))) t)
                (DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N
                  (@DecrAlmostLinearSSSP.Decremental.cutRequest n k p g
                    (@DecrAlmostLinearSSSP.Decremental.CutOp.queryY n k v))
                  t) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.2.2.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.CorePending.address_injective : ∀ {l : Nat} (B : Nat) (e f : Fin l) (a c : Nat),
  @LT.lt.{0} Nat instLTNat a (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
    @LT.lt.{0} Nat instLTNat c (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
      @Eq.{1} Nat (@DecrAlmostLinearSSSP.Decremental.CorePending.address l B e a)
          (@DecrAlmostLinearSSSP.Decremental.CorePending.address l B f c) →
        And (@Eq.{1} (Fin l) e f) (@Eq.{1} Nat a c) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.2.2.1.1.1.2
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
theorem DecrAlmostLinearSSSP.Decremental.CorePending.insert_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
      DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CorePending.insertCode s
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
        (DecrAlmostLinearSSSP.Decremental.CorePending.inserted s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.2.2.1.2.1.2
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
theorem DecrAlmostLinearSSSP.Decremental.CoreEdgeAddress.no_memory : DecrAlmostLinearSSSP.Decremental.Structured.NoMemory DecrAlmostLinearSSSP.Decremental.CoreEdgeAddress.code := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.1.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreEdgeAddress.nat_frame : ∀ (k : Nat),
  Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 562) (instOfNatNat (nat_lit 562))))
      (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 580) (instOfNatNat (nat_lit 580))) k) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreEdgeAddress.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.1.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreEdgeAddress.real_frame : ∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreEdgeAddress.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.2.1.1.1.1
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
theorem DecrAlmostLinearSSSP.Decremental.CoreDegree.nat_frame : ∀ (vertex k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 620) (instOfNatNat (nat_lit 620))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 662) (instOfNatNat (nat_lit 662))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.CoreDegree.code vertex) k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.2.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreDegree.real_frame : ∀ (vertex k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.CoreDegree.code vertex) k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.2.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreDegree.Image.final : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (base : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @DecrAlmostLinearSSSP.Decremental.CoreDegree.Image b.input.n base
      (DecrAlmostLinearSSSP.Decremental.CoreDegree.heads b b.input.k) s →
    ∀ (v : Fin b.input.n),
      @Eq.{1} Nat
        (s.natMem
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val b.input.n v))))
        (DecrAlmostLinearSSSP.Decremental.indegree b v) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.2.2.1.2.2.2
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
theorem DecrAlmostLinearSSSP.Decremental.CoreRefresh.no_memory : DecrAlmostLinearSSSP.Decremental.Structured.NoMemory DecrAlmostLinearSSSP.Decremental.CoreRefresh.code := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.1.2.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreRefresh.nat_frame : ∀ (k : Nat), DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreRefresh.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.1.2.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreRefresh.real_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 612) (instOfNatNat (nat_lit 612))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 614) (instOfNatNat (nat_lit 614))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 616) (instOfNatNat (nat_lit 616))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 618) (instOfNatNat (nat_lit 618))) →
          DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreRefresh.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.1.2.1.2.1.2
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
theorem DecrAlmostLinearSSSP.Decremental.CoreOutput.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 622) (instOfNatNat (nat_lit 622))) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreOutput.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.2.1.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreOutput.real_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 620) (instOfNatNat (nat_lit 620))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 624) (instOfNatNat (nat_lit 624))) →
      DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreOutput.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.2.1.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreReturn.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 620) (instOfNatNat (nat_lit 620))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 622) (instOfNatNat (nat_lit 622))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreReturn.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.2.1.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreReturn.real_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 620) (instOfNatNat (nat_lit 620))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 624) (instOfNatNat (nat_lit 624))) →
      DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreReturn.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.2.1.1.2.1.1
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
theorem DecrAlmostLinearSSSP.Decremental.CoreGradient.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 550) (instOfNatNat (nat_lit 550))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 632) (instOfNatNat (nat_lit 632))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 634) (instOfNatNat (nat_lit 634))) →
        DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreGradient.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.2.1.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreGradient.real_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 628) (instOfNatNat (nat_lit 628))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
      DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreGradient.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.2.1.2.2.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.body_nat_frame : ∀ (k : Nat),
  Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 550) (instOfNatNat (nat_lit 550))))
      (Or (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 552) (instOfNatNat (nat_lit 552))))
        (Or (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 554) (instOfNatNat (nat_lit 554))))
          (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 662) (instOfNatNat (nat_lit 662))) k))) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.body k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_7.1.1.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreMemory.protected_below : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B j : Nat),
  @LE.le.{0} Nat instLENat j B → DecrAlmostLinearSSSP.Decremental.CoreMemory.Protected b B j := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_7.1.1.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreMemory.Frame.refl : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreMemory.Frame b B s s := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_7.1.1.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreMemory.Frame.trans : ∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {B : Nat} {s t u : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.CoreMemory.Frame b B s t →
    DecrAlmostLinearSSSP.Decremental.CoreMemory.Frame b B t u →
      DecrAlmostLinearSSSP.Decremental.CoreMemory.Frame b B s u := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_7.1.1.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreMemory.ReturnFrame.refl : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreMemory.ReturnFrame b B s s := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_7.1.1.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreMemory.ReturnFrame.trans : ∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {B : Nat} {s t u : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.CoreMemory.ReturnFrame b B s t →
    DecrAlmostLinearSSSP.Decremental.CoreMemory.ReturnFrame b B t u →
      DecrAlmostLinearSSSP.Decremental.CoreMemory.ReturnFrame b B s u := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_7.1.2.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.eval_loop : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (upto : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @LE.le.{0} Nat instLENat b.input.n B →
    DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.Invariant b B K upto s →
      ∃ cost t,
        And
          (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.loop s
            cost t)
          (And
            (@LE.le.{0} Nat instLENat cost
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 89) (instOfNatNat (nat_lit 89)))
                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) b.input.n upto))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (And (DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.Invariant b B K b.input.n t)
              (DecrAlmostLinearSSSP.Decremental.CoreMemory.ReturnFrame b B s t))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_7.2.1.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.Invariant.final_geometry : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.Invariant b B K b.input.n s →
    DecrAlmostLinearSSSP.Decremental.CoreGeometry.Image b B (DecrAlmostLinearSSSP.Decremental.initializeState b) s := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_7.2.1.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.Invariant.final_gradient : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.Invariant b B K b.input.n s →
    @DecrAlmostLinearSSSP.Decremental.CoreGradient.Image b.input.n
      (DecrAlmostLinearSSSP.Decremental.CoreMemory.gradientBase b B)
      (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b (DecrAlmostLinearSSSP.Decremental.initializeState b)) s := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_7.2.1.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.Invariant.final_public : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.Invariant b B K b.input.n s →
    And
      (∀ (u : Fin b.input.n),
        @Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.stored s.machine (@Fin.val b.input.n u))
          (@DecrAlmostLinearSSSP.Decremental.State.output b (DecrAlmostLinearSSSP.Decremental.initializeState b) u))
      (∀ (u : Fin b.input.n),
        And
          (@LE.le.{0} Nat instLENat (s.natMem (@Fin.val b.input.n u))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@Eq.{1} Nat (s.natMem (@Fin.val b.input.n u)) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
            @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              (s.realMem (@Fin.val b.input.n u)))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_7.2.1.2.1.1.2
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
theorem DecrAlmostLinearSSSP.Decremental.CoreInitializeContributions.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 550) (instOfNatNat (nat_lit 550))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 620) (instOfNatNat (nat_lit 620))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 632) (instOfNatNat (nat_lit 632))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 634) (instOfNatNat (nat_lit 634))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 662) (instOfNatNat (nat_lit 662))) →
              DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
                DecrAlmostLinearSSSP.Decremental.CoreInitializeContributions.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_7.2.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.eval_loop : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (upto : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b.input.n
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) b.input.k))
      B →
    DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.Invariant b B K upto s →
      ∃ cost t,
        And
          (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.loop s
            cost t)
          (And
            (@LE.le.{0} Nat instLENat cost
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 85) (instOfNatNat (nat_lit 85)))
                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) b.input.k upto))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (And (DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.Invariant b B K b.input.k t)
              (DecrAlmostLinearSSSP.Decremental.CoreMemory.Frame b B s t))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_7.2.2.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.start_nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 652) (instOfNatNat (nat_lit 652))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.startCode
        k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_7.2.2.2.1.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.core_pass_eval : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b.input.n
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) b.input.k))
      B →
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
                ∃ cost t,
                  And
                    (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                      DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.corePassCode s cost t)
                    (And
                      (@LE.le.{0} Nat instLENat cost
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 85) (instOfNatNat (nat_lit 85))) b.input.k)
                          (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
                      (And (DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.Invariant b B K b.input.k t)
                        (DecrAlmostLinearSSSP.Decremental.CoreMemory.Frame b B s t))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_7.2.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.start_invariant : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.Invariant b B K b.input.k s →
    @Eq.{1} Nat (s.natMem (@Fin.val b.input.n b.input.source))
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
      @Eq.{1} Real (s.realMem (@Fin.val b.input.n b.input.source))
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
        DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.Invariant b B K
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          { realReg := s.realReg,
            natReg :=
              @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natReg
                (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626)))
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))),
            realMem := s.realMem, natMem := s.natMem } := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_7.2.2.2.2.2.2.2
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
lemma return_pass_eval (b : Core) (B : ℕ) (K : ℝ) (s : Data) (hB : b.input.n ≤ B)
    (h : CoreInitializeEdge.Invariant b B K b.input.k s)
    (hn : s.natMem b.input.source.val = 0) (hr : s.realMem b.input.source.val = 0) :
    ∃ cost t, Eval code s cost t ∧ cost ≤ 89*b.input.n+3 ∧
      Invariant b B K b.input.n t ∧ CoreMemory.ReturnFrame b B s t := by
  let u : Data := {s with natReg := Function.update s.natReg 626 0}
  have hu := eval_natural s 626 0
  have hum : Invariant b B K 0 u := start_invariant b B K s h hn hr
  obtain ⟨cl,t,ht,hcl,hti,htf⟩ := eval_loop b B K 0 u hB hum
  refine ⟨1+cl,t,Eval.seq hu ht,by omega,hti,?_⟩
  exact (show CoreMemory.ReturnFrame b B s u from fun _ _ _ => ⟨rfl,rfl⟩).trans htf
end DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
end s276
section s277
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitialize
open Structured
lemma records_eval (b : Core) (B : ℕ) (K : ℝ) (s : Data) (hB : b.input.n+3*b.input.k ≤ B)
    (hc : InputCapture.Captured b.input s) (hp : CoreParameters.Values b K s) (hl : CoreControl.Layout b B s)
    (htape : Exact.Adjacency.Tape b.input s) (hcount : s.natReg 550 = 0)
    (hzero : ∀ v : Fin b.input.n, s.natMem (CoreMemory.gradientCell b B v) = 0 ∧ s.realMem (CoreMemory.gradientCell b B v) = 0)
    (hsourceNat : s.natMem b.input.source.val = 0) (hsourceReal : s.realMem b.input.source.val = 0) :
    ∃ cost t, Eval recordsCode s cost t ∧ cost ≤ 180*b.input.size ∧
      CoreInitializeReturn.Invariant b B K b.input.n t ∧ CoreMemory.ReturnFrame b B s t := by
  obtain ⟨cc,u,hu,hcc,hui,huf⟩ := CoreInitializeEdge.core_pass_eval b B K s hB hc hp hl htape hcount hzero
  have hbelow := CoreMemory.protected_below b B b.input.source.val (by have hh := b.input.source.isLt;omega)
  have hsrc := huf b.input.source.val hbelow
  obtain ⟨cr,t,ht,hcr,hti,htf⟩ := CoreInitializeReturn.return_pass_eval b B K u (by omega) hui
    (hsrc.1.trans hsourceNat) (hsrc.2.trans hsourceReal)
  have hn : b.input.n ≤ b.input.size := b.valid.1
  have hk : b.input.k ≤ b.input.size := b.valid.2.1
  have hm : 2 ≤ b.input.size := b.two.trans hn
  refine ⟨cc+cr,t,Eval.seq hu ht,by omega,hti,?_⟩
  exact (show CoreMemory.ReturnFrame b B s u from fun j hj _ => huf j hj).trans htf
lemma records_even : evenRegisters recordsCode = true := by decide
lemma records_head_frame : NatFrame recordsCode 546 := by
  change (NatFrame CoreInitializeEdge.startCode 546 ∧ NatFrame CoreInitializeEdge.code 546) ∧
    (NatFrame (natural 626 0) 546 ∧ NatFrame CoreInitializeReturn.body 546)
  exact ⟨⟨CoreInitializeEdge.start_nat_frame 546 (by omega) (by omega),
    CoreInitializeEdge.nat_frame 546 (by omega)⟩,
    ⟨by simp [NatFrame,natural,writesNat],CoreInitializeReturn.body_nat_frame 546 (by omega)⟩⟩
end DecrAlmostLinearSSSP.Decremental.CoreInitialize
end s277
section s278
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
open Structured
lemma Invariant.final_pending (b : Core) (B : ℕ) (K : ℝ) (s : Data)
    (h : Invariant b B K b.input.n s) (hhead : s.natReg 546 = 0) :
    CorePending.View B ([] : List (Fin (logicalCount b))) s := by
  have hall : ∀ e : Edge b, CoreRecord.Initialized b B e s := by
    intro e
    cases e with
    | inl e => exact h.cores e
    | inr v => exact h.returns v v.val.isLt
  refine ⟨by simp,?_,hhead,True.intro⟩
  intro d
  have hm := (hall ((logicalIndexEquiv b).symm d)).mark
  simpa [CorePending.address,CoreMemory.field] using hm
end DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn
namespace DecrAlmostLinearSSSP.Decremental.CorePending
lemma token_eq_zero {l : ℕ} (xs : List (Fin l)) : token xs = 0 ↔ xs = [] := by
  cases xs with
  | nil => simp [token]
  | cons e xs => simp [token]
lemma View.empty_iff {B l : ℕ} {xs : List (Fin l)} {s : Structured.Data} (h : View B xs s) :
    s.natReg 546 = 0 ↔ xs = [] := by rw [h.head,token_eq_zero]
end DecrAlmostLinearSSSP.Decremental.CorePending
end s278
section s279
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CorePending
open Structured
attribute [local instance] Classical.propDecidable
lemma popTail_eval (s : Data) (hz : s.natReg 56 = 0) :
    Eval (Structured.sequence [loadN 546 572,storeN 568 56]) s 2 (popped s) := by
  have hh := Eval.seq (eval_loadN s 546 572) (Eval.seq (eval_storeN _ 568 56) (Eval.skip _))
  simpa only [Structured.sequence,popped,hz,Function.update_of_ne (by decide : (568 : ℕ) ≠ 546),
    Function.update_of_ne (by decide : (56 : ℕ) ≠ 546)] using hh
lemma dequeue {l : ℕ} (B : ℕ) (xs : List (Fin l)) (e : Fin l) (s : Data)
    (hv : View B (e::xs) s) (hb : s.natReg 552 = B+1)
    (h2 : s.natReg 14 = 2) (hz : s.natReg 56 = 0) :
    ∃ t, Eval popCode s 9 t ∧ View B xs t ∧ t.natReg 560 = 2*e.val ∧
      t.realMem = s.realMem ∧
      (∀ j, j ≠ address B e 0 → t.natMem j = s.natMem j) := by
  let u : Data := {s with natReg := Function.update s.natReg 560 (s.natReg 546-s.natReg 14)}
  have hu := eval_nsub s 560 546 14
  have hu560 : u.natReg 560 = 2*e.val := by simp [u,hv.head,token,h2]
  have hub : u.natReg 552 = B+1 := by simpa [u] using hb
  have hu14 : u.natReg 14 = 2 := by simpa [u] using h2
  let a := prefixData u
  obtain ⟨h0,hflag,h1,hr⟩ := prefix_fields u
  have ha0 : a.natReg 568 = address B e 0 := by dsimp [address];rw [h0,hub,hu560];omega
  have ha1 : a.natReg 572 = address B e 1 := by dsimp [address];rw [h1,hub,hu560,hu14];omega
  have ham : a.natMem = s.natMem := (prefix_memory u).1
  have har : a.realMem = s.realMem := (prefix_memory u).2
  have haz : a.natReg 56 = 0 := by
    rw [hr 56 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    simpa [u] using hz
  have ha560 : a.natReg 560 = 2*e.val := by
    rw [hr 560 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact hu560
  have hm (j : ℕ) : (popped a).natMem j = Function.update s.natMem (address B e 0) 0 j := by
    simp only [popped,ha0,ham]
  have htail : e ∉ xs ∧ xs.Nodup := List.nodup_cons.mp hv.nodup
  have hview : View B xs (popped a) := by
    refine ⟨htail.2,?_,?_,?_⟩
    · intro f
      rw [hm]
      by_cases hf : f = e
      · subst f;simp [htail.1]
      · have hne : address B f 0 ≠ address B e 0 := fun hh => hf (address_injective B f e 0 0 (by omega) (by omega) hh).1
        rw [Function.update_of_ne hne,hv.flags f]
        simp [hf]
    · simpa only [popped,Function.update_self,ha1,ham] using hv.links.1
    · apply hv.links.2.congr
      intro f hf
      have h10 : address B f 1 ≠ address B e 0 := by
        intro hh
        have hh' := address_injective B f e 1 0 (by omega) (by omega) hh
        omega
      rw [hm,Function.update_of_ne h10]
  refine ⟨popped a,Eval.seq hu (Eval.seq (prefix_eval u) (popTail_eval a haz)),hview,?_,har,?_⟩
  · simpa only [popped,Function.update_of_ne (by decide : (560 : ℕ) ≠ 546)] using ha560
  · intro j hj
    rw [hm,Function.update_of_ne hj]
end DecrAlmostLinearSSSP.Decremental.CorePending
end s279
section s280
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CorePending
open Structured
lemma nat_frame (k : ℕ) (h546 : k ≠ 546) (hk : k < 562 ∨ 572 < k) : NatFrame code k := by
  simp [code,prefixCode,prefixAtoms,insertCode,Structured.sequence,NatFrame,storeN,nadd,writesNat]
  omega
lemma real_frame (k : ℕ) : RealFrame code k := by
  simp [code,prefixCode,prefixAtoms,insertCode,Structured.sequence,RealFrame,storeN,nadd,writesReal]
lemma pop_nat_frame (k : ℕ) (h546 : k ≠ 546) (h560 : k ≠ 560)
    (hk : k < 562 ∨ 572 < k) : NatFrame popCode k := by
  simp [popCode,prefixCode,prefixAtoms,Structured.sequence,NatFrame,storeN,loadN,nsub,writesNat]
  omega
lemma pop_real_frame (k : ℕ) : RealFrame popCode k := by
  simp [popCode,prefixCode,prefixAtoms,Structured.sequence,RealFrame,storeN,loadN,nsub,writesReal]
lemma encoded_member {l : ℕ} (e : Fin l) : 2*e.val < 2*l := by omega
lemma record_guest_disjoint {l : ℕ} (B : ℕ) (e : Fin l) (offset j : ℕ) :
    address B e offset ≠ B+4*j+2 := by dsimp [address];omega
lemma MemoryFrame.refl (B l : ℕ) (s : Data) : MemoryFrame B l s s := fun _ _ => rfl
lemma MemoryFrame.trans {B l : ℕ} {s t u : Data} (h : MemoryFrame B l s t) (g : MemoryFrame B l t u) :
    MemoryFrame B l s u := fun j hj => (g j hj).trans (h j hj)
lemma MemoryFrame.guest {B l : ℕ} {s t : Data} (h : MemoryFrame B l s t) (j : ℕ) :
    t.natMem (B+4*j+2) = s.natMem (B+4*j+2) :=
  h _ (fun e => ⟨Ne.symm (record_guest_disjoint B e 0 j),Ne.symm (record_guest_disjoint B e 1 j)⟩)
end DecrAlmostLinearSSSP.Decremental.CorePending
end s280
section s281
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreHost
open Structured
lemma initial_image (b : Core) (B : ℕ) (K : ℝ) (s : Data)
    (h : CoreInitializeReturn.Invariant b B K b.input.n s) (hhead : s.natReg 546 = 0)
    (hbase : s.natReg 74 = B) :
    Image b B K (initializeState b) s := by
  exact ⟨h.captured,h.parameters,h.layout,hbase,
    h.final_geometry b B K s,h.final_gradient b B K s,
    by simpa only [initializeState,List.map_nil] using h.final_pending b B K s hhead,
    (h.final_public b B K s).1,(h.final_public b B K s).2⟩
end DecrAlmostLinearSSSP.Decremental.CoreHost
end s281
section s282
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRequest
open Structured
lemma nat_prefix_frame (slot source R address : ℕ) (s : Data) (hne : source ≠ 630)
    (hbase : s.natReg 50 = R+8) (ha : address < R+8) :
    (natResult slot source s).natMem address = s.natMem address ∧
      (natResult slot source s).realMem address = s.realMem address := by
  rw [(nat_values slot source s hne).1,(nat_values slot source s hne).2,hbase]
  exact ⟨Function.update_of_ne (by omega) _ _,rfl⟩
lemma real_prefix_frame (slot source R address : ℕ) (s : Data)
    (hbase : s.natReg 50 = R+8) (ha : address < R+8) :
    (realResult slot source s).natMem address = s.natMem address ∧
      (realResult slot source s).realMem address = s.realMem address := by
  rw [(real_values slot source s).1,(real_values slot source s).2,hbase]
  exact ⟨rfl,Function.update_of_ne (by omega) _ _⟩
lemma tag_prefix_frame (tag R address : ℕ) (s : Data) (hbase : s.natReg 50 = R+8) (ha : address < R+8) :
    (tagged tag s).natMem address = s.natMem address ∧ (tagged tag s).realMem address = s.realMem address := by
  apply nat_prefix_frame 5 632 R address _ (by omega) _ ha
  simpa only [Function.update_of_ne (by decide : (50:ℕ) ≠ 632)] using hbase
lemma host_nat_frame (cmd : Cmd)
    (hframe : ∀ k, k < 630 ∨ 640 < k → NatFrame cmd k) :
    ∀ k, k ∈ CoreHost.NatRegisters → NatFrame cmd k := by
  intro k hk
  apply hframe
  left
  simp only [CoreHost.NatRegisters,List.mem_cons,List.not_mem_nil,or_false] at hk
  omega
lemma host_real_frame (cmd : Cmd)
    (hframe : ∀ k, k ≠ 640 → RealFrame cmd k) :
    ∀ k, k ∈ CoreHost.RealRegisters → RealFrame cmd k := by
  intro k hk
  apply hframe
  simp only [CoreHost.RealRegisters,List.mem_cons,List.not_mem_nil,or_false] at hk
  omega
lemma erase_nat_frame (k : ℕ) (hk : k ≠ 630) (h632 : k ≠ 632) : NatFrame eraseCode k :=
  ⟨tag_nat_frame 1 k hk h632,nat_frame 6 560 k hk⟩
lemma erase_real_frame (k : ℕ) : RealFrame eraseCode k :=
  ⟨tag_real_frame 1 k,nat_real_frame 6 560 k⟩
lemma query_nat_frame (source k : ℕ) (hk : k ≠ 630) (h632 : k ≠ 632) : NatFrame (queryCode source) k :=
  ⟨tag_nat_frame 5 k hk h632,nat_frame 6 source k hk⟩
lemma query_real_frame (source k : ℕ) : RealFrame (queryCode source) k :=
  ⟨tag_real_frame 5 k,nat_real_frame 6 source k⟩
end DecrAlmostLinearSSSP.Decremental.CoreRequest
end s282
section s283
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRequest
open Structured
lemma endpoint_eval (s : Data) : Eval endpointCode s 2 (endpoints s) := by
  have he := Eval.seq (eval_nadd s 636 626 626)
    (Eval.seq (eval_nadd _ 638 628 628) (Eval.skip _))
  simpa only [endpointCode,Structured.sequence,endpoints,Function.update_of_ne (by decide : (628:ℕ) ≠ 636)] using he
lemma endpoint_nat_frame (k : ℕ) (h636 : k ≠ 636) (h638 : k ≠ 638) : NatFrame endpointCode k := by
  simp [endpointCode,Structured.sequence,NatFrame,nadd,writesNat,Ne.symm h636,Ne.symm h638]
lemma endpoint_real_frame (k : ℕ) : RealFrame endpointCode k := by
  simp [endpointCode,Structured.sequence,RealFrame,nadd,writesReal]
lemma endpoint_image (B R N : ℕ) (g : Machine) (s : Data) (h : CoreSource.Image B R N g s) :
    CoreSource.Image B R N g (endpoints s) := by
  have h1 := h.nat_register B R N 636 (s.natReg 626+s.natReg 626) g s
    (by decide) (by omega) (by omega) (by omega) (by omega) (by omega)
  exact h1.nat_register B R N 638 (s.natReg 628+s.natReg 628) g _
    (by decide) (by omega) (by omega) (by omega) (by omega) (by omega)
lemma toggle_eval {n k : ℕ} (B R N : ℕ) (p : Program) (g : Machine) (s : Data) (tau : ℝ)
    (h : CoreSource.Image B R N g s) (hodd : ∃ r, R = B+2*r+1)
    (htau : s.realReg 510/s.realReg 31 = tau) :
    ∃ t, Eval toggleCode s 8 t ∧ CoreSource.Image B R N (cutRequest p g (CutOp.toggle (n := n) (k := k) tau)) t := by
  let u := tagged 4 s
  have hu : Eval (tagCode 4) s 4 u := tag_eval 4 s
  have hi := (h.resume B R N p.update g s).tagged B R N 4 _ s hodd
  let v : Data := {u with realReg := Function.update u.realReg 640 (u.realReg 510/u.realReg 31)}
  have hv : Eval (div 640 510 31) u 1 v := eval_div u 640 510 31
  have hj := hi.real_register B R N 640 (u.realReg 510/u.realReg 31) _ u (by decide)
  have hval : v.realReg 640 = tau := by
    change Function.update u.realReg 640 (u.realReg 510/u.realReg 31) 640 = tau
    rw [Function.update_self,hu.real_frame (tag_real_frame 4 510),hu.real_frame (tag_real_frame 4 31),htau]
  have hf := hj.real_patch B R N 2 640 _ v hodd
  refine ⟨realResult 2 640 v,Eval.seq hu (Eval.seq hv (real_eval 2 640 v)),?_⟩
  simpa only [cutRequest,resume,hval] using hf
end DecrAlmostLinearSSSP.Decremental.CoreRequest
end s283
section s284
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreHost
open Structured
lemma Address.below_source (b : Core) (B address : ℕ) (h : Address b B address) :
    address < CoreMemory.sourceRecord b B := by
  rcases h with h | ⟨r,hr,hh⟩
  · dsimp [CoreMemory.sourceRecord,CoreMemory.gradientBase];omega
  · exact hh
lemma Address.guest_disjoint (b : Core) (B address : ℕ) (h : Address b B address) (a : ℕ) :
    address ≠ B+2*(2*a+1) := by
  rcases h with h | ⟨r,hr,hh⟩ <;> omega
lemma source_frame (b : Core) (B N entry : ℕ) (K : ℝ) (state : State b) (p : Program)
    (s t : Data) (cost : ℕ) (h : Image b B K state s) (hB : b.input.n ≤ B)
    (he : Eval (SourceCall.code N entry p) s cost t)
    (hm : ∀ address, (∀ a, address ≠ B+2*(2*a+1)) →
      address ≠ CoreMemory.sourceRecord b B+6 →
      (∀ j < N, address ≠ CoreMemory.sourceRecord b B+8+2*j) →
      t.natMem address = s.natMem address ∧ t.realMem address = s.realMem address) :
    Image b B K state t := by
  apply h.frame b B K state hB
  · intro k hk
    have hh : 10 ≤ k ∧ Even k ∧ k ≠ 52 ∧ k ≠ 54 := by
      simp only [NatRegisters,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hk
      rcases hk with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst k <;> decide
    exact he.nat_frame (SourceCall.nat_even_frame N entry p k hh.1 hh.2.1 hh.2.2.1 hh.2.2.2)
  · intro k hk
    have hh : 10 ≤ k ∧ Even k := by
      simp only [RealRegisters,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hk
      rcases hk with h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst k <;> decide
    exact he.real_frame (SourceCall.real_even_frame N entry p k hh.1 hh.2)
  · intro address ha
    have hh := ha.below_source b B address
    exact hm address (ha.guest_disjoint b B address) (by omega) (by intro j hj;omega)
end DecrAlmostLinearSSSP.Decremental.CoreHost
end s284
section s285
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreHost
open Structured
lemma Image.temp_nat (b : Core) (B : ℕ) (K : ℝ) (state : State b) (s : Data)
    (h : Image b B K state s) (hB : b.input.n ≤ B) (k value : ℕ) (hk : 630 ≤ k) :
    Image b B K state {s with natReg := Function.update s.natReg k value} := by
  apply h.frame b B K state hB
  · intro j hj
    apply Function.update_of_ne _ _ _
    simp only [NatRegisters,List.mem_cons,List.not_mem_nil,or_false] at hj
    omega
  · intro j hj;rfl
  · intro j hj;exact ⟨rfl,rfl⟩
lemma Image.temp_real (b : Core) (B : ℕ) (K : ℝ) (state : State b) (s : Data)
    (h : Image b B K state s) (hB : b.input.n ≤ B) (k : ℕ) (value : ℝ) (hk : 630 ≤ k) :
    Image b B K state {s with realReg := Function.update s.realReg k value} := by
  apply h.frame b B K state hB
  · intro j hj;rfl
  · intro j hj
    apply Function.update_of_ne _ _ _
    simp only [RealRegisters,List.mem_cons,List.not_mem_nil,or_false] at hj
    omega
  · intro j hj;exact ⟨rfl,rfl⟩
lemma Image.nat_patch (b : Core) (B : ℕ) (K : ℝ) (state : State b) (s : Data)
    (h : Image b B K state s) (hB : b.input.n ≤ B) (slot source : ℕ) (hne : source ≠ 630) :
    Image b B K state (CoreRequest.natResult slot source s) := by
  have he := CoreRequest.nat_eval slot source s
  apply h.frame b B K state hB
  · intro k hk
    exact he.nat_frame (CoreRequest.nat_frame slot source k (by simp only [NatRegisters,List.mem_cons,List.not_mem_nil,or_false] at hk;omega))
  · intro k hk;exact he.real_frame (CoreRequest.nat_real_frame slot source k)
  · intro address ha
    apply CoreRequest.nat_prefix_frame slot source (CoreMemory.sourceRecord b B) address s hne h.layout.savedBase
    have hh := ha.below_source b B address
    omega
lemma Image.real_patch (b : Core) (B : ℕ) (K : ℝ) (state : State b) (s : Data)
    (h : Image b B K state s) (hB : b.input.n ≤ B) (slot source : ℕ) :
    Image b B K state (CoreRequest.realResult slot source s) := by
  have he := CoreRequest.real_eval slot source s
  apply h.frame b B K state hB
  · intro k hk
    exact he.nat_frame (CoreRequest.real_nat_frame slot source k (by simp only [NatRegisters,List.mem_cons,List.not_mem_nil,or_false] at hk;omega))
  · intro k hk;exact he.real_frame (CoreRequest.real_frame slot source k)
  · intro address ha
    apply CoreRequest.real_prefix_frame slot source (CoreMemory.sourceRecord b B) address s h.layout.savedBase
    have hh := ha.below_source b B address
    omega
lemma Image.tagged (b : Core) (B : ℕ) (K : ℝ) (state : State b) (s : Data)
    (h : Image b B K state s) (hB : b.input.n ≤ B) (tag : ℕ) : Image b B K state (CoreRequest.tagged tag s) := by
  exact (h.temp_nat b B K state s hB 632 (2*tag) (by omega)).nat_patch b B K state _ hB 5 632 (by omega)
lemma Image.endpoints (b : Core) (B : ℕ) (K : ℝ) (state : State b) (s : Data)
    (h : Image b B K state s) (hB : b.input.n ≤ B) : Image b B K state (CoreRequest.endpoints s) := by
  exact (h.temp_nat b B K state s hB 636 (s.natReg 626+s.natReg 626) (by omega)).temp_nat b B K state _ hB
    638 (s.natReg 628+s.natReg 628) (by omega)
lemma Preserves.seq {b : Core} {B : ℕ} {K : ℝ} {state : State b} {a c : Cmd}
    (ha : Preserves b B K state a) (hc : Preserves b B K state c) : Preserves b B K state (.seq a c) := by
  intro s cost t h he
  cases he with
  | seq hx hy => exact hc _ _ _ (ha _ _ _ h hx) hy
lemma preserves_tag (b : Core) (B : ℕ) (K : ℝ) (state : State b) (hB : b.input.n ≤ B) (tag : ℕ) :
    Preserves b B K state (CoreRequest.tagCode tag) := by
  intro s cost t h he
  have ht := (CoreRequest.tag_eval tag s).deterministic he
  rw [← ht.2]
  exact h.tagged b B K state s hB tag
lemma preserves_nat (b : Core) (B : ℕ) (K : ℝ) (state : State b) (hB : b.input.n ≤ B) (slot source : ℕ) (hne : source ≠ 630) :
    Preserves b B K state (CoreRequest.natCode slot source) := by
  intro s cost t h he
  have ht := (CoreRequest.nat_eval slot source s).deterministic he
  rw [← ht.2]
  exact h.nat_patch b B K state s hB slot source hne
lemma preserves_real (b : Core) (B : ℕ) (K : ℝ) (state : State b) (hB : b.input.n ≤ B) (slot source : ℕ) :
    Preserves b B K state (CoreRequest.realCode slot source) := by
  intro s cost t h he
  have ht := (CoreRequest.real_eval slot source s).deterministic he
  rw [← ht.2]
  exact h.real_patch b B K state s hB slot source
lemma preserves_endpoints (b : Core) (B : ℕ) (K : ℝ) (state : State b) (hB : b.input.n ≤ B) :
    Preserves b B K state CoreRequest.endpointCode := by
  intro s cost t h he
  have ht := (CoreRequest.endpoint_eval s).deterministic he
  rw [← ht.2]
  exact h.endpoints b B K state s hB
end DecrAlmostLinearSSSP.Decremental.CoreHost
end s285
section s286
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
lemma call {b : Core} {B N m exponent : ℕ} {K K0 ξ h Γ init : ℝ} {state : State b}
    {impl : CutImplementation} {first current : Machine} {ops : List (CutOp b.input.n (logicalCount b))}
    {cs : List Machine} (hSession : CutSession impl b.input.n (logicalCount b) m exponent first K0 ξ h Γ init)
    (hRun : CutRun impl b.input.n (logicalCount b) m exponent first ops cs)
    (hLast : cs.getLast? = some current) (op : CutOp b.input.n (logicalCount b))
    (hValid : CutOp.Valid (impl.view b.input.n (logicalCount b) current) op)
    (hBounds : (applyPhysical (impl.view b.input.n (logicalCount b) current).physical op).Valid m exponent)
    (hN : 10 ≤ N) (hBound : registerBound impl.program.code ≤ N)
    (hZero : ZeroRegisterTail N current) (s : Data) (host : CoreHost.Image b B K state s)
    (hB : b.input.n ≤ B) (setup : Cmd) (setupCost : ℕ)
    (hPreserves : CoreHost.Preserves b B K state setup)
    (hSetup : ∃ u, Eval setup s setupCost u ∧
      CoreSource.Image B (CoreMemory.sourceRecord b B) N (cutRequest impl.program current op) u) :
    ∃ cost t final,
      Eval (.seq setup (SourceCall.code N impl.program.update impl.program)) s cost t ∧
      cost ≤ setupCost+(dispatchCharge impl.program.code+2)*(final.work-current.work)+8*N+15 ∧
      CoreHost.Image b B K state t ∧ CoreSource.Image B (CoreMemory.sourceRecord b B) N final t ∧
      ShadowDataRep B 2 t final ∧ ZeroRegisterTail N final ∧
      Ends impl.program (cutRequest impl.program current op) final ∧
      CutTransition K0 ξ (impl.view b.input.n (logicalCount b) current) op final
        (impl.view b.input.n (logicalCount b) final) ∧
      CutRun impl b.input.n (logicalCount b) m exponent first (ops++[op]) (cs++[final]) := by
  obtain ⟨final,hEnd,hTransition⟩ := hSession.total ops cs hRun current hLast op hValid hBounds
  obtain ⟨u,hu,hus⟩ := hSetup
  have hum := hPreserves s setupCost u host hu
  have hodd : ∃ r, CoreMemory.sourceRecord b B = B+2*r+1 := by
    exact ⟨5*logicalCount b+b.input.n,by dsimp [CoreMemory.sourceRecord,CoreMemory.gradientBase];omega⟩
  have hz := cutRequest_zero_tail impl.program current op hN hZero
  have hpc : (cutRequest impl.program current op).pc = impl.program.update := by cases op <;> rfl
  have hhalt : (cutRequest impl.program current op).halted = false := by cases op <;> rfl
  have hfault : (cutRequest impl.program current op).fault = false := by cases op <;> rfl
  have hw : (cutRequest impl.program current op).work = current.work := by cases op <;> rfl
  obtain ⟨cc,t,ht,hcc,hts,htrep,htframe⟩ := hus.call B (CoreMemory.sourceRecord b B) N impl.program.update
    impl.program (cutRequest impl.program current op) final u hBound hodd hpc hhalt hfault hz hEnd
  have htm := CoreHost.source_frame b B N impl.program.update K state impl.program u t cc hum hB ht htframe
  refine ⟨setupCost+cc,t,final,Eval.seq hu ht,by rw [hw] at hcc;omega,
    htm,hts,htrep,hz.ends_of_bound hBound hEnd,hEnd,hTransition,?_⟩
  exact CutRun.next hRun hLast op hValid hBounds hEnd
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s286
section s287
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreHost
open Structured
lemma preserves_div (b : Core) (B : ℕ) (K : ℝ) (state : State b) (hB : b.input.n ≤ B) (k a c : ℕ) (hk : 630 ≤ k) :
    Preserves b B K state (div k a c) := by
  intro s cost t h he
  let u : Data := {s with realReg := Function.update s.realReg k (s.realReg a/s.realReg c)}
  have hu : Eval (div k a c) s 1 u := eval_div s k a c
  have ht := hu.deterministic he
  rw [← ht.2]
  exact h.temp_real b B K state s hB k _ hk
lemma preserves_ratio (b : Core) (B : ℕ) (K : ℝ) (state : State b) (hB : b.input.n ≤ B) :
    Preserves b B K state CoreRequest.ratioCode := preserves_tag b B K state hB 3
lemma preserves_erase (b : Core) (B : ℕ) (K : ℝ) (state : State b) (hB : b.input.n ≤ B) :
    Preserves b B K state CoreRequest.eraseCode :=
  (preserves_tag b B K state hB 1).seq (preserves_nat b B K state hB 6 560 (by omega))
lemma preserves_query (b : Core) (B : ℕ) (K : ℝ) (state : State b) (hB : b.input.n ≤ B) (source : ℕ) (hne : source ≠ 630) :
    Preserves b B K state (CoreRequest.queryCode source) :=
  (preserves_tag b B K state hB 5).seq (preserves_nat b B K state hB 6 source hne)
lemma preserves_insert (b : Core) (B : ℕ) (K : ℝ) (state : State b) (hB : b.input.n ≤ B) :
    Preserves b B K state CoreRequest.insertCode :=
  (preserves_tag b B K state hB 0).seq ((preserves_nat b B K state hB 6 560 (by omega)).seq
    ((preserves_endpoints b B K state hB).seq ((preserves_nat b B K state hB 8 636 (by omega)).seq
      ((preserves_nat b B K state hB 9 638 (by omega)).seq (preserves_real b B K state hB 2 612)))))
lemma preserves_paired (b : Core) (B : ℕ) (K : ℝ) (state : State b) (hB : b.input.n ≤ B) :
    Preserves b B K state CoreRequest.pairedCode :=
  (preserves_tag b B K state hB 2).seq ((preserves_endpoints b B K state hB).seq
    ((preserves_nat b B K state hB 8 638 (by omega)).seq
      ((preserves_nat b B K state hB 9 636 (by omega)).seq (preserves_real b B K state hB 2 614))))
lemma preserves_toggle (b : Core) (B : ℕ) (K : ℝ) (state : State b) (hB : b.input.n ≤ B) :
    Preserves b B K state CoreRequest.toggleCode :=
  (preserves_tag b B K state hB 4).seq ((preserves_div b B K state hB 640 510 31 (by omega)).seq
    (preserves_real b B K state hB 2 640))
end DecrAlmostLinearSSSP.Decremental.CoreHost
end s287
section s288
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRequest
open Structured
lemma insert_eval {n k : ℕ} (B R N : ℕ) (p : Program) (g : Machine) (s : Data)
    (e : Fin k) (a b : Fin n) (capacity : ℝ)
    (h : CoreSource.Image B R N g s) (hodd : ∃ r, R = B+2*r+1)
    (he : s.natReg 560 = 2*e.val) (ha : s.natReg 626 = a.val) (hb : s.natReg 628 = b.val)
    (hcap : s.realReg 612 = capacity) :
    ∃ t, Eval insertCode s 18 t ∧ CoreSource.Image B R N (cutRequest p g (.insert e a b capacity)) t := by
  let u := tagged 0 s
  have hu : Eval (tagCode 0) s 4 u := tag_eval 0 s
  have hi := (h.resume B R N p.update g s).tagged B R N 0 _ s hodd
  have hue : u.natReg 560 = 2*e.val := (hu.nat_frame (tag_nat_frame 0 560 (by omega) (by omega))).trans he
  let v := natResult 6 560 u
  have hv : Eval (natCode 6 560) u 3 v := nat_eval 6 560 u
  have hj := hi.nat_patch B R N 6 560 e.val _ u hodd (by omega) hue
  let w := endpoints v
  have hw : Eval endpointCode v 2 w := endpoint_eval v
  have hwimage := endpoint_image B R N _ v hj
  have hwa : w.natReg 636 = 2*a.val := by
    change Function.update (Function.update v.natReg 636 (v.natReg 626+v.natReg 626)) 638 (v.natReg 628+v.natReg 628) 636 = 2*a.val
    rw [Function.update_of_ne (by decide : (636:ℕ) ≠ 638),Function.update_self,
      hv.nat_frame (nat_frame 6 560 626 (by omega)),hu.nat_frame (tag_nat_frame 0 626 (by omega) (by omega)),ha]
    omega
  have hwb : w.natReg 638 = 2*b.val := by
    change Function.update (Function.update v.natReg 636 (v.natReg 626+v.natReg 626)) 638 (v.natReg 628+v.natReg 628) 638 = 2*b.val
    rw [Function.update_self,hv.nat_frame (nat_frame 6 560 628 (by omega)),
      hu.nat_frame (tag_nat_frame 0 628 (by omega) (by omega)),hb]
    omega
  let x := natResult 8 636 w
  have hx : Eval (natCode 8 636) w 3 x := nat_eval 8 636 w
  have hximage := hwimage.nat_patch B R N 8 636 a.val _ w hodd (by omega) hwa
  have hxb : x.natReg 638 = 2*b.val := (hx.nat_frame (nat_frame 8 636 638 (by omega))).trans hwb
  let y := natResult 9 638 x
  have hy : Eval (natCode 9 638) x 3 y := nat_eval 9 638 x
  have hyimage := hximage.nat_patch B R N 9 638 b.val _ x hodd (by omega) hxb
  have hycap : y.realReg 612 = capacity := by
    rw [hy.real_frame (nat_real_frame 9 638 612),hx.real_frame (nat_real_frame 8 636 612),
      hw.real_frame (endpoint_real_frame 612),hv.real_frame (nat_real_frame 6 560 612),
      hu.real_frame (tag_real_frame 0 612),hcap]
  have hzimage := hyimage.real_patch B R N 2 612 _ y hodd
  refine ⟨realResult 2 612 y,Eval.seq hu (Eval.seq hv (Eval.seq hw (Eval.seq hx (Eval.seq hy (real_eval 2 612 y))))),?_⟩
  simpa only [insert_machine,resume,hycap] using hzimage
lemma paired_eval {n k : ℕ} (B R N : ℕ) (p : Program) (g : Machine) (s : Data)
    (a b : Fin n) (delta : ℝ)
    (h : CoreSource.Image B R N g s) (hodd : ∃ r, R = B+2*r+1)
    (ha : s.natReg 628 = a.val) (hb : s.natReg 626 = b.val) (hdelta : s.realReg 614 = delta) :
    ∃ t, Eval pairedCode s 15 t ∧ CoreSource.Image B R N (cutRequest p g (CutOp.paired (k := k) a b delta)) t := by
  let u := tagged 2 s
  have hu : Eval (tagCode 2) s 4 u := tag_eval 2 s
  have hi := (h.resume B R N p.update g s).tagged B R N 2 _ s hodd
  let v := endpoints u
  have hv : Eval endpointCode u 2 v := endpoint_eval u
  have hvimage := endpoint_image B R N _ u hi
  have hva : v.natReg 638 = 2*a.val := by
    change Function.update (Function.update u.natReg 636 (u.natReg 626+u.natReg 626)) 638 (u.natReg 628+u.natReg 628) 638 = 2*a.val
    rw [Function.update_self,hu.nat_frame (tag_nat_frame 2 628 (by omega) (by omega)),ha]
    omega
  have hvb : v.natReg 636 = 2*b.val := by
    change Function.update (Function.update u.natReg 636 (u.natReg 626+u.natReg 626)) 638 (u.natReg 628+u.natReg 628) 636 = 2*b.val
    rw [Function.update_of_ne (by decide : (636:ℕ) ≠ 638),Function.update_self,
      hu.nat_frame (tag_nat_frame 2 626 (by omega) (by omega)),hb]
    omega
  let w := natResult 8 638 v
  have hw : Eval (natCode 8 638) v 3 w := nat_eval 8 638 v
  have hwimage := hvimage.nat_patch B R N 8 638 a.val _ v hodd (by omega) hva
  have hwb : w.natReg 636 = 2*b.val := (hw.nat_frame (nat_frame 8 638 636 (by omega))).trans hvb
  let x := natResult 9 636 w
  have hx : Eval (natCode 9 636) w 3 x := nat_eval 9 636 w
  have hximage := hwimage.nat_patch B R N 9 636 b.val _ w hodd (by omega) hwb
  have hxdelta : x.realReg 614 = delta := by
    rw [hx.real_frame (nat_real_frame 9 636 614),hw.real_frame (nat_real_frame 8 638 614),
      hv.real_frame (endpoint_real_frame 614),hu.real_frame (tag_real_frame 2 614),hdelta]
  have hyimage := hximage.real_patch B R N 2 614 _ x hodd
  refine ⟨realResult 2 614 x,Eval.seq hu (Eval.seq hv (Eval.seq hw (Eval.seq hx (real_eval 2 614 x)))),?_⟩
  simpa only [paired_machine,resume,hxdelta] using hyimage
end DecrAlmostLinearSSSP.Decremental.CoreRequest
end s288
section s289
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
lemma Context.advance {b : Core} {B N m exponent : ℕ} {K K0 ξ h Γ init : ℝ}
    {impl : CutImplementation} {state : State b} {s : Data}
    (ctx : Context b B N m exponent impl K0 ξ h Γ init s) (host : CoreHost.Image b B K state s)
    (hB : b.input.n ≤ B) (hN : 10 ≤ N) (hBound : registerBound impl.program.code ≤ N)
    (op : CutOp b.input.n (logicalCount b))
    (hv : CutOp.Valid (impl.view b.input.n (logicalCount b) ctx.current) op)
    (hb : (applyPhysical (impl.view b.input.n (logicalCount b) ctx.current).physical op).Valid m exponent)
    (setup : Cmd) (setupCost : ℕ) (hp : CoreHost.Preserves b B K state setup)
    (hs : ∃ u, Eval setup s setupCost u ∧
      CoreSource.Image B (CoreMemory.sourceRecord b B) N (cutRequest impl.program ctx.current op) u) :
    ∃ cost t, ∃ next : Context b B N m exponent impl K0 ξ h Γ init t,
      Eval (.seq setup (SourceCall.code N impl.program.update impl.program)) s cost t ∧
      cost ≤ setupCost+(dispatchCharge impl.program.code+2)*(next.current.work-ctx.current.work)+8*N+15 ∧
      CoreHost.Image b B K state t ∧
      ShadowDataRep B 2 t next.current ∧
      CutTransition K0 ξ (impl.view b.input.n (logicalCount b) ctx.current) op next.current
        (impl.view b.input.n (logicalCount b) next.current) ∧
      next.first = ctx.first ∧ next.ops = ctx.ops++[op] ∧ next.machines = ctx.machines++[next.current] ∧ ctx.current.work ≤ next.current.work := by
  obtain ⟨cost,t,final,he,hcost,htm,hts,htrep,htzero,hEnd,hTransition,hRun⟩ :=
    call ctx.session ctx.run ctx.last op hv hb hN hBound ctx.zeroTail s host hB setup setupCost hp hs
  let next : Context b B N m exponent impl K0 ξ h Γ init t :=
    ⟨ctx.first,final,ctx.ops++[op],ctx.machines++[final],ctx.session,hRun,by simp,htzero,hts⟩
  have hmono : ctx.current.work ≤ final.work := by
    have hw : (cutRequest impl.program ctx.current op).work = ctx.current.work := by cases op <;> rfl
    simpa only [hw] using hEnd.work_mono
  exact ⟨cost,t,next,he,hcost,htm,htrep,hTransition,rfl,rfl,rfl,hmono⟩
lemma Context.report_bound {b : Core} {B N m exponent : ℕ} {K0 ξ h Γ init : ℝ}
    {impl : CutImplementation} {s : Data} (ctx : Context b B N m exponent impl K0 ξ h Γ init s) :
    (reportVolume ctx.machines : ℝ) ≤ Γ*toggleVolume ctx.ops/ξ :=
  ctx.session.reports ctx.ops ctx.machines ctx.run
lemma Context.work_bound {b : Core} {B N m exponent : ℕ} {K0 ξ h Γ init : ℝ}
    {impl : CutImplementation} {s : Data} (ctx : Context b B N m exponent impl K0 ξ h Γ init s) :
    (ctx.current.work+6*ctx.ops.length : ℕ) ≤ init+h*((ctx.ops.length : ℝ)+reportVolume ctx.machines) :=
  ctx.session.work ctx.ops ctx.machines ctx.run ctx.current ctx.last
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s289
section s290
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
lemma Context.query {b : Core} {B N m exponent : ℕ} {K K0 ξ h Γ init : ℝ}
    {impl : CutImplementation} {state : State b} {s : Data}
    (ctx : Context b B N m exponent impl K0 ξ h Γ init s) (host : CoreHost.Image b B K state s)
    (hB : b.input.n ≤ B) (hN : 10 ≤ N) (hBound : registerBound impl.program.code ≤ N)
    (hb : (impl.view b.input.n (logicalCount b) ctx.current).physical.Valid m exponent)
    (source : ℕ) (h630 : source ≠ 630) (h632 : source ≠ 632)
    (v : Fin b.input.n) (hv : s.natReg source = 2*v.val) :
    ∃ cost t, ∃ next : Context b B N m exponent impl K0 ξ h Γ init t,
      Eval (queryCode N source impl.program) s cost t ∧
      cost ≤ (dispatchCharge impl.program.code+2)*(next.current.work-ctx.current.work)+8*N+22 ∧
      CoreHost.Image b B K state t ∧
      impl.view b.input.n (logicalCount b) next.current = impl.view b.input.n (logicalCount b) ctx.current ∧
      t.realReg 29 = (impl.view b.input.n (logicalCount b) ctx.current).y v ∧
      next.first = ctx.first ∧ next.ops = ctx.ops++[.queryY v] ∧ next.machines = ctx.machines++[next.current] ∧ ctx.current.work ≤ next.current.work ∧ reportVolume next.machines = reportVolume ctx.machines := by
  have hodd : ∃ r, CoreMemory.sourceRecord b B = B+2*r+1 := by
    exact ⟨5*logicalCount b+b.input.n,by dsimp [CoreMemory.sourceRecord,CoreMemory.gradientBase];omega⟩
  have hsetup := CoreRequest.query_eval (k := logicalCount b) B (CoreMemory.sourceRecord b B) N source impl.program ctx.current s v
    ctx.image hodd h630 h632 hv
  obtain ⟨cost,t,next,he,hcost,htm,hrep,htrans,hfirst,hops,hcs,hmono⟩ := ctx.advance host hB hN hBound (.queryY v)
    trivial hb (CoreRequest.queryCode source) 7 (CoreHost.preserves_query b B K state hB source h630) hsetup
  have hteq : impl.view b.input.n (logicalCount b) next.current = impl.view b.input.n (logicalCount b) ctx.current := htrans.2.1
  have hvalue : next.current.realReg 10 = (impl.view b.input.n (logicalCount b) ctx.current).y v := htrans.2.2.1
  have hnative : t.realReg 29 = next.current.realReg 10 := by
    simpa only [shadowReg,Data.machine] using hrep.realReg 10
  have hR : reportVolume next.machines = reportVolume ctx.machines := by
    rw [hcs,reportVolume_append ctx.machines ctx.current next.current ctx.last,htrans.2.2.2,Nat.add_zero]
  exact ⟨cost,t,next,he,by omega,htm,hteq,hnative.trans hvalue,hfirst,hops,hcs,hmono,hR⟩
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s290
section s291
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreSource
open Structured
lemma Image.command_frame (B R N : ℕ) (g : Machine) {s t : Data} {cost : ℕ} {cmd : Cmd}
    (h : Image B R N g s) (he : Eval cmd s cost t) (hm : NoMemory cmd)
    (heven : evenRegisters cmd = true)
    (hn : ∀ k, k ∈ ([74,112,106,50,56] : List ℕ) → NatFrame cmd k) : Image B R N g t := by
  have hmem := he.no_memory hm
  apply h.frame B R N g (fun k hk => he.nat_frame (hn k hk))
  · intro j hj
    have hf := evenRegisters_frames _ heven (shadowReg j) (by simp [shadowReg])
    exact ⟨he.nat_frame hf.1,he.real_frame hf.2⟩
  · intro a;exact ⟨congrFun hmem.2 _,congrFun hmem.1 _⟩
  · exact congrFun hmem.2 _
  · intro j hj;exact ⟨congrFun hmem.2 _,congrFun hmem.1 _⟩
end DecrAlmostLinearSSSP.Decremental.CoreSource
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s291
section s292
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreHost
open Structured
lemma Image.command_frame (b : Core) (B : ℕ) (K : ℝ) (state : State b) {s t : Data} {cost : ℕ} {cmd : Cmd}
    (h : Image b B K state s) (hB : b.input.n ≤ B) (he : Eval cmd s cost t) (hm : NoMemory cmd)
    (hn : ∀ k, k ∈ NatRegisters → NatFrame cmd k)
    (hr : ∀ k, k ∈ RealRegisters → RealFrame cmd k) : Image b B K state t := by
  have hmem := he.no_memory hm
  exact h.frame b B K state hB (fun k hk => he.nat_frame (hn k hk)) (fun k hk => he.real_frame (hr k hk))
    (fun _ _ => ⟨congrFun hmem.2 _,congrFun hmem.1 _⟩)
end DecrAlmostLinearSSSP.Decremental.CoreHost
end s292
section s293
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
lemma Context.capture_query {b : Core} {B N m exponent : ℕ} {K K0 ξ h Γ init : ℝ}
    {impl : CutImplementation} {state : State b} {s : Data}
    (ctx : Context b B N m exponent impl K0 ξ h Γ init s) (host : CoreHost.Image b B K state s)
    (hB : b.input.n ≤ B) (hN : 10 ≤ N) (hBound : registerBound impl.program.code ≤ N)
    (hb : (impl.view b.input.n (logicalCount b) ctx.current).physical.Valid m exponent)
    (source dest : ℕ) (h630 : source ≠ 630) (h632 : source ≠ 632)
    (hdest : 535 ≤ dest) (heven : dest%2 = 0)
    (v : Fin b.input.n) (hv : s.natReg source = 2*v.val) :
    ∃ cost t, ∃ next : Context b B N m exponent impl K0 ξ h Γ init t,
      Eval (captureQueryCode N source dest impl.program) s cost t ∧
      cost ≤ (dispatchCharge impl.program.code+2)*(next.current.work-ctx.current.work)+8*N+23 ∧
      CoreHost.Image b B K state t ∧
      impl.view b.input.n (logicalCount b) next.current = impl.view b.input.n (logicalCount b) ctx.current ∧
      t.realReg dest = (impl.view b.input.n (logicalCount b) ctx.current).y v ∧
      next.first = ctx.first ∧ next.ops = ctx.ops++[.queryY v] ∧ next.machines = ctx.machines++[next.current] ∧ ctx.current.work ≤ next.current.work ∧ reportVolume next.machines = reportVolume ctx.machines := by
  obtain ⟨cq,q,qctx,hq,hcq,hqm,hview,hvalue,hfirst,hops,hcs,hmono,hR⟩ := ctx.query host hB hN hBound hb source h630 h632 v hv
  let t : Data := {q with realReg := Function.update q.realReg dest (q.realReg 29+q.realReg 56)}
  have ht : Eval (add dest 29 56) q 1 t := eval_add q dest 29 56
  have htm : CoreHost.Image b B K state t := hqm.command_frame b B K state hB ht
    (by simp [NoMemory,NoStore,add])
    (by intro k hk;simp [NatFrame,add,writesNat])
    (by intro k hk;simp only [CoreHost.RealRegisters,List.mem_cons,List.not_mem_nil,or_false] at hk
        simp [RealFrame,add,writesReal];omega)
  have hts : CoreSource.Image B (CoreMemory.sourceRecord b B) N qctx.current t :=
    qctx.image.real_register B _ N dest _ qctx.current q heven
  let next := qctx.of_image hts
  refine ⟨cq+1,t,next,Eval.seq hq ht,by dsimp [next,Context.of_image];omega,htm,hview,?_,hfirst,hops,hcs,hmono,hR⟩
  change Function.update q.realReg dest (q.realReg 29+q.realReg 56) dest = _
  rw [Function.update_self,hqm.captured.zeroR,add_zero,hvalue]
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s293
section s294
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
lemma query_nat_frame (N source : ℕ) (p : Program) (k : ℕ) (hk : 10 ≤ k) (he : Even k)
    (h52 : k ≠ 52) (h54 : k ≠ 54) (h630 : k ≠ 630) (h632 : k ≠ 632) : NatFrame (queryCode N source p) k :=
  ⟨CoreRequest.query_nat_frame source k h630 h632,SourceCall.nat_even_frame N p.update p k hk he h52 h54⟩
lemma query_real_frame (N source : ℕ) (p : Program) (k : ℕ) (hk : 10 ≤ k) (he : Even k) : RealFrame (queryCode N source p) k :=
  ⟨CoreRequest.query_real_frame source k,SourceCall.real_even_frame N p.update p k hk he⟩
lemma capture_nat_frame (N source dest : ℕ) (p : Program) (k : ℕ) (hk : 10 ≤ k) (he : Even k)
    (h52 : k ≠ 52) (h54 : k ≠ 54) (h630 : k ≠ 630) (h632 : k ≠ 632) : NatFrame (captureQueryCode N source dest p) k :=
  ⟨query_nat_frame N source p k hk he h52 h54 h630 h632,by simp [NatFrame,add,writesNat]⟩
lemma capture_real_frame (N source dest : ℕ) (p : Program) (k : ℕ) (hk : 10 ≤ k) (he : Even k)
    (hne : k ≠ dest) : RealFrame (captureQueryCode N source dest p) k :=
  ⟨query_real_frame N source p k hk he,by simp [RealFrame,add,writesReal,Ne.symm hne]⟩
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s294
section s295
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma indexedPhysical_norm_eq (b : Core) (s : State b) {l : ℕ} (E : Edge b ≃ Fin l)
    (x : Fin b.input.n → ℝ) : physicalNorm (indexedPhysical b s E) x = norm b s.cache x := by
  classical
  simp only [physicalNorm,indexedPhysical,norm]
  exact Equiv.sum_comp E.symm (fun e => s.cache e*|incidence b x e|)
lemma indexedPhysical_capacity_eq (b : Core) (s : State b) {l : ℕ} (E : Edge b ≃ Fin l)
    (C : Finset (Fin b.input.n)) : cutCapacity (indexedPhysical b s E) C = cutCapacity (cachedPhysical b s) C := by
  have hi := physical_norm_cut (indexedPhysical b s E) C 1 (by norm_num)
  have hc := physical_norm_cut (cachedPhysical b s) C 1 (by norm_num)
  rw [one_mul] at hi hc
  rw [← hi,← hc,indexedPhysical_norm_eq,cachedPhysical_norm_eq]
lemma indexedPhysical_ratio (b : Core) (s : State b) {l : ℕ} (E : Edge b ≃ Fin l)
    (K G U : ℝ) (C : Finset (Fin b.input.n))
    (h : RatioGuarantee (indexedPhysical b s E) K G U C) : RatioGuarantee (cachedPhysical b s) K G U C := by
  refine ⟨h.1,h.2.1,h.2.2.1,?_,?_⟩
  · rw [← indexedPhysical_capacity_eq b s E C]
    exact h.2.2.2.1
  · intro x hx
    have hxi : 0 < physicalNorm (indexedPhysical b s E) x := by
      rw [indexedPhysical_norm_eq]
      rwa [cachedPhysical_norm_eq] at hx
    have hh := h.2.2.2.2 x hxi
    rw [indexedPhysical_norm_eq] at hh
    rw [cachedPhysical_norm_eq]
    exact hh
end DecrAlmostLinearSSSP.Decremental
end s295
section s296
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
lemma RatioGuarantee.weaken {n k : ℕ} {h : Physical n k} {K K' G U : ℝ} {C : Finset (Fin n)}
    (hq : RatioGuarantee h K G U C) (hK : 0 < K) (hKK : K ≤ K') :
    RatioGuarantee h K' G U C := by
  have hK' : 0 < K' := hK.trans_le hKK
  refine ⟨hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1, ?_⟩
  intro x hx
  by_cases hs : dot h.gamma x ≤ 0
  · have hd : dot h.gamma x / physicalNorm h x ≤ 0 := div_nonpos_of_nonpos_of_nonneg hs hx.le
    have hh : (dot h.gamma x / physicalNorm h x) / K ≤
        (dot h.gamma x / physicalNorm h x) / K' := by
      apply (div_le_div_iff₀ hK hK').mpr
      exact mul_le_mul_of_nonpos_left hKK hd
    exact (hq.2.2.2.2 x hx).trans hh
  · have hg : G / U ≤ 0 := div_nonpos_of_nonpos_of_nonneg hq.1.le hq.2.1.le
    have hr : 0 ≤ (dot h.gamma x / physicalNorm h x) / K' := by
      exact div_nonneg (div_nonneg (le_of_not_ge hs) hx.le) hK'.le
    exact hg.trans hr
end DecrAlmostLinearSSSP.Decremental
end s296
section s297
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma CutModel.toggle_complete (b : Core) {l : ℕ} (E : Edge b ≃ Fin l) (s : State b)
    (c t : CutState b.input.n l) (K K0 : ℝ) (g : Machine) (reports : List (Edge b))
    (h : CutModel b E s c) (hd : s.pending = [])
    (ht : CutTransition K0 (K^(-2 : ℤ)) c (.toggle (1/(K^2*c.lastU))) g t)
    (hreports : ∀ e, e ∈ reports ↔ Reported g (E e)) :
    ReportsComplete b K s (modelReply b c) reports := by
  rcases ht with ⟨hphys,hy,hhas,hcut,hG,hU,hdetect,hbase⟩
  have hp : t.physical = indexedPhysical b s E := hphys.trans h.physical
  have hyt : t.y = (toggle b K s (modelReply b c)).y := by
    funext v
    rw [hy v,h.y]
    rfl
  intro e he
  apply (hreports e).mpr
  apply hdetect (E e) (by rw [hp];exact Finset.mem_univ _)
  have hb : c.baseline (E e) = s.baseline e := h.baseline e (by rw [hd];simp)
  simpa only [hp,indexedPhysical,Equiv.symm_apply_apply,hyt,hb] using he
lemma CutModel.toggle (b : Core) {l : ℕ} (E : Edge b ≃ Fin l) (s : State b)
    (c t : CutState b.input.n l) (K K0 : ℝ) (g : Machine) (reports : List (Edge b))
    (h : CutModel b E s c) (hd : s.pending = [])
    (ht : CutTransition K0 (K^(-2 : ℤ)) c (.toggle (1/(K^2*c.lastU))) g t)
    (hreports : ∀ e, e ∈ reports ↔ Reported g (E e)) :
    CutModel b E (reportedToggle b K s (modelReply b c) reports) t := by
  rcases ht with ⟨hphys,hy,hhas,hcut,hG,hU,hdetect,hbase⟩
  refine ⟨?_,?_,?_⟩
  · exact hphys.trans h.physical
  · funext v
    rw [hy v,h.y]
    rfl
  · intro e he
    have hn : ¬ Reported g (E e) := fun hh => he ((hreports e).mpr hh)
    rw [hbase,if_neg hn,h.baseline e (by rw [hd];simp)]
    rfl
lemma CutModel.ratio (b : Core) {l : ℕ} (E : Edge b ≃ Fin l) (s : State b)
    (c t : CutState b.input.n l) (K K0 ξ : ℝ) (g : Machine)
    (h : CutModel b E s c) (ht : CutTransition K0 ξ c .ratio g t)
    (hn : s.cachedGradient ≠ 0) (hK0 : 0 < K0) (hKK : K0 ≤ K) :
    CutModel b E s t ∧ RatioGuarantee (cachedPhysical b s) K t.lastG t.lastU t.lastCut ∧ t.hasCut = true := by
  rcases ht with ⟨hp,hy,hr,hbase,hquality⟩
  have hphys : t.physical = indexedPhysical b s E := hp.trans h.physical
  have hnonzero : t.physical.gamma ≠ 0 := by simpa only [hphys,indexedPhysical] using hn
  obtain ⟨hq,hhas,hG,hU⟩ := hquality hnonzero
  have hq' : RatioGuarantee (indexedPhysical b s E) K0 t.lastG t.lastU t.lastCut := by
    simpa only [hphys,hG,hU] using hq
  refine ⟨⟨hphys,hy.trans h.y,?_⟩,indexedPhysical_ratio b s E K _ _ _ (hq'.weaken hK0 hKK),hhas⟩
  intro e he
  rw [hbase]
  exact h.baseline e he
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
theorem solution : (((((((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @LE.le.{0} Nat instLENat b.input.n B →
    DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.Invariant b B K b.input.k s →
      @Eq.{1} Nat (s.natMem (@Fin.val b.input.n b.input.source))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
        @Eq.{1} Real (s.realMem (@Fin.val b.input.n b.input.source))
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
          ∃ cost t,
            And
              (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.code s cost t)
              (And
                (@LE.le.{0} Nat instLENat cost
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 89) (instOfNatNat (nat_lit 89))) b.input.n)
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                (And (DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.Invariant b B K b.input.n t)
                  (DecrAlmostLinearSSSP.Decremental.CoreMemory.ReturnFrame b B s t)))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b.input.n
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) b.input.k))
      B →
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
                @Eq.{1} Nat (s.natMem (@Fin.val b.input.n b.input.source))
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                  @Eq.{1} Real (s.realMem (@Fin.val b.input.n b.input.source))
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
                    ∃ cost t,
                      And
                        (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                          DecrAlmostLinearSSSP.Decremental.CoreInitialize.recordsCode s cost t)
                        (And
                          (@LE.le.{0} Nat instLENat cost
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 180) (instOfNatNat (nat_lit 180))) b.input.size))
                          (And (DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.Invariant b B K b.input.n t)
                            (DecrAlmostLinearSSSP.Decremental.CoreMemory.ReturnFrame b B s t))))) ∧ ((@Eq.{1} Bool
  (DecrAlmostLinearSSSP.Decremental.Structured.evenRegisters
    DecrAlmostLinearSSSP.Decremental.CoreInitialize.recordsCode)
  Bool.true) ∧ (DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreInitialize.recordsCode
  (@OfNat.ofNat.{0} Nat (nat_lit 546) (instOfNatNat (nat_lit 546)))))) ∧ (((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.Invariant b B K b.input.n s →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 546) (instOfNatNat (nat_lit 546))))
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
      @DecrAlmostLinearSSSP.Decremental.CorePending.View (DecrAlmostLinearSSSP.Decremental.logicalCount b) B
        (@List.nil.{0} (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))) s) ∧ (∀ {l : Nat} (xs : List.{0} (Fin l)),
  Iff
    (@Eq.{1} Nat (@DecrAlmostLinearSSSP.Decremental.CorePending.token l xs)
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@Eq.{1} (List.{0} (Fin l)) xs (@List.nil.{0} (Fin l))))) ∧ ((∀ {B l : Nat} {xs : List.{0} (Fin l)} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  @DecrAlmostLinearSSSP.Decremental.CorePending.View l B xs s →
    Iff
      (@Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 546) (instOfNatNat (nat_lit 546))))
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@Eq.{1} (List.{0} (Fin l)) xs (@List.nil.{0} (Fin l)))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval
      (DecrAlmostLinearSSSP.Decremental.Structured.sequence
        (@List.cons.{0} DecrAlmostLinearSSSP.Decremental.Structured.Cmd
          (DecrAlmostLinearSSSP.Decremental.Structured.loadN
            (@OfNat.ofNat.{0} Nat (nat_lit 546) (instOfNatNat (nat_lit 546)))
            (@OfNat.ofNat.{0} Nat (nat_lit 572) (instOfNatNat (nat_lit 572))))
          (@List.cons.{0} DecrAlmostLinearSSSP.Decremental.Structured.Cmd
            (DecrAlmostLinearSSSP.Decremental.Structured.storeN
              (@OfNat.ofNat.{0} Nat (nat_lit 568) (instOfNatNat (nat_lit 568)))
              (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
            (@List.nil.{0} DecrAlmostLinearSSSP.Decremental.Structured.Cmd))))
      s (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
      (DecrAlmostLinearSSSP.Decremental.CorePending.popped s)) ∧ (∀ {l : Nat} (B : Nat) (xs : List.{0} (Fin l)) (e : Fin l) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @DecrAlmostLinearSSSP.Decremental.CorePending.View l B (@List.cons.{0} (Fin l) e xs) s →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 552) (instOfNatNat (nat_lit 552))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
          ∃ t,
            And
              (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CorePending.popCode s
                (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) t)
              (And (@DecrAlmostLinearSSSP.Decremental.CorePending.View l B xs t)
                (And
                  (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val l e)))
                  (And (@Eq.{1} (Nat → Real) t.realMem s.realMem)
                    (∀ (j : Nat),
                      @Ne.{1} Nat j
                          (@DecrAlmostLinearSSSP.Decremental.CorePending.address l B e
                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
                        @Eq.{1} Nat (t.natMem j) (s.natMem j)))))))))) ∧ ((((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 546) (instOfNatNat (nat_lit 546))) →
    Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 562) (instOfNatNat (nat_lit 562))))
        (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 572) (instOfNatNat (nat_lit 572))) k) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CorePending.code k) ∧ (∀ (k : Nat), DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CorePending.code k)) ∧ ((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 546) (instOfNatNat (nat_lit 546))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))) →
      Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 562) (instOfNatNat (nat_lit 562))))
          (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 572) (instOfNatNat (nat_lit 572))) k) →
        DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CorePending.popCode k) ∧ (∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CorePending.popCode k))) ∧ (((∀ {l : Nat} (e : Fin l),
  @LT.lt.{0} Nat instLTNat
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val l e))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) l)) ∧ (∀ {l : Nat} (B : Nat) (e : Fin l) (offset j : Nat),
  @Ne.{1} Nat (@DecrAlmostLinearSSSP.Decremental.CorePending.address l B e offset)
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) j))
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))) ∧ ((∀ (B l : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CorePending.MemoryFrame B l s s) ∧ ((∀ {B l : Nat} {s t u : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.CorePending.MemoryFrame B l s t →
    DecrAlmostLinearSSSP.Decremental.CorePending.MemoryFrame B l t u →
      DecrAlmostLinearSSSP.Decremental.CorePending.MemoryFrame B l s u) ∧ (∀ {B l : Nat} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.CorePending.MemoryFrame B l s t →
    ∀ (j : Nat),
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
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))) ∧ (((((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.Invariant b B K b.input.n s →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 546) (instOfNatNat (nat_lit 546))))
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))) B →
        DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K (DecrAlmostLinearSSSP.Decremental.initializeState b) s) ∧ (∀ (slot source R address : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Ne.{1} Nat source (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) R
          (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) →
      @LT.lt.{0} Nat instLTNat address
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) R
            (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) →
        And
          (@Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.CoreRequest.natResult slot source s).natMem address)
            (s.natMem address))
          (@Eq.{1} Real ((DecrAlmostLinearSSSP.Decremental.CoreRequest.natResult slot source s).realMem address)
            (s.realMem address)))) ∧ ((∀ (slot source R address : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) R
        (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) →
    @LT.lt.{0} Nat instLTNat address
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) R
          (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) →
      And
        (@Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.CoreRequest.realResult slot source s).natMem address)
          (s.natMem address))
        (@Eq.{1} Real ((DecrAlmostLinearSSSP.Decremental.CoreRequest.realResult slot source s).realMem address)
          (s.realMem address))) ∧ (∀ (tag R address : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) R
        (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) →
    @LT.lt.{0} Nat instLTNat address
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) R
          (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) →
      And (@Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.CoreRequest.tagged tag s).natMem address) (s.natMem address))
        (@Eq.{1} Real ((DecrAlmostLinearSSSP.Decremental.CoreRequest.tagged tag s).realMem address) (s.realMem address))))) ∧ (((∀ (cmd : DecrAlmostLinearSSSP.Decremental.Structured.Cmd),
  (∀ (k : Nat),
      Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))))
          (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 640) (instOfNatNat (nat_lit 640))) k) →
        DecrAlmostLinearSSSP.Decremental.Structured.NatFrame cmd k) →
    ∀ (k : Nat),
      @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat)
          DecrAlmostLinearSSSP.Decremental.CoreHost.NatRegisters k →
        DecrAlmostLinearSSSP.Decremental.Structured.NatFrame cmd k) ∧ (∀ (cmd : DecrAlmostLinearSSSP.Decremental.Structured.Cmd),
  (∀ (k : Nat),
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 640) (instOfNatNat (nat_lit 640))) →
        DecrAlmostLinearSSSP.Decremental.Structured.RealFrame cmd k) →
    ∀ (k : Nat),
      @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat)
          DecrAlmostLinearSSSP.Decremental.CoreHost.RealRegisters k →
        DecrAlmostLinearSSSP.Decremental.Structured.RealFrame cmd k)) ∧ ((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 632) (instOfNatNat (nat_lit 632))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreRequest.eraseCode k) ∧ ((∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreRequest.eraseCode k) ∧ (∀ (source k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 632) (instOfNatNat (nat_lit 632))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
        (DecrAlmostLinearSSSP.Decremental.CoreRequest.queryCode source) k))))) ∧ ((((∀ (source k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.CoreRequest.queryCode source)
    k) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreRequest.endpointCode s
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    (DecrAlmostLinearSSSP.Decremental.CoreRequest.endpoints s))) ∧ ((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 636) (instOfNatNat (nat_lit 636))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 638) (instOfNatNat (nat_lit 638))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreRequest.endpointCode k) ∧ ((∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreRequest.endpointCode k) ∧ (∀ (B R N : Nat) (g : DecrAlmostLinearSSSP.Decremental.Machine) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N g s →
    DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N g (DecrAlmostLinearSSSP.Decremental.CoreRequest.endpoints s))))) ∧ (((∀ {n k : Nat} (B R N : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program)
  (g : DecrAlmostLinearSSSP.Decremental.Machine) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (tau : Real),
  DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N g s →
    (∃ r,
        @Eq.{1} Nat R
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
      @Eq.{1} Real
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 510) (instOfNatNat (nat_lit 510))))
            (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))))
          tau →
        ∃ t,
          And
            (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreRequest.toggleCode s
              (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) t)
            (DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N
              (@DecrAlmostLinearSSSP.Decremental.cutRequest n k p g
                (@DecrAlmostLinearSSSP.Decremental.CutOp.toggle n k tau))
              t)) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B address : Nat),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Address b B address →
    @LT.lt.{0} Nat instLTNat address (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B address : Nat),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Address b B address →
    ∀ (a : Nat),
      @Ne.{1} Nat address
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B N entry : Nat) (K : Real)
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
          DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state t) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    @LE.le.{0} Nat instLENat b.input.n B →
      ∀ (k value : Nat),
        @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) k →
          DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state
            { realReg := s.realReg,
              natReg := @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natReg k value,
              realMem := s.realMem, natMem := s.natMem }))))))) ∧ ((((((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    @LE.le.{0} Nat instLENat b.input.n B →
      ∀ (k : Nat) (value : Real),
        @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) k →
          DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state
            { realReg := @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realReg k value,
              natReg := s.natReg, realMem := s.realMem, natMem := s.natMem }) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    @LE.le.{0} Nat instLENat b.input.n B →
      ∀ (slot source : Nat),
        @Ne.{1} Nat source (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
          DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state
            (DecrAlmostLinearSSSP.Decremental.CoreRequest.natResult slot source s))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    @LE.le.{0} Nat instLENat b.input.n B →
      ∀ (slot source : Nat),
        DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state
          (DecrAlmostLinearSSSP.Decremental.CoreRequest.realResult slot source s)) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    @LE.le.{0} Nat instLENat b.input.n B →
      ∀ (tag : Nat),
        DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state
          (DecrAlmostLinearSSSP.Decremental.CoreRequest.tagged tag s)))) ∧ (((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    @LE.le.{0} Nat instLENat b.input.n B →
      DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state
        (DecrAlmostLinearSSSP.Decremental.CoreRequest.endpoints s)) ∧ (∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {B : Nat} {K : Real} {state : DecrAlmostLinearSSSP.Decremental.State b}
  {a c : DecrAlmostLinearSSSP.Decremental.Structured.Cmd},
  DecrAlmostLinearSSSP.Decremental.CoreHost.Preserves b B K state a →
    DecrAlmostLinearSSSP.Decremental.CoreHost.Preserves b B K state c →
      DecrAlmostLinearSSSP.Decremental.CoreHost.Preserves b B K state (a.seq c))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b),
  @LE.le.{0} Nat instLENat b.input.n B →
    ∀ (tag : Nat),
      DecrAlmostLinearSSSP.Decremental.CoreHost.Preserves b B K state
        (DecrAlmostLinearSSSP.Decremental.CoreRequest.tagCode tag)) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b),
  @LE.le.{0} Nat instLENat b.input.n B →
    ∀ (slot source : Nat),
      @Ne.{1} Nat source (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
        DecrAlmostLinearSSSP.Decremental.CoreHost.Preserves b B K state
          (DecrAlmostLinearSSSP.Decremental.CoreRequest.natCode slot source)) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b),
  @LE.le.{0} Nat instLENat b.input.n B →
    ∀ (slot source : Nat),
      DecrAlmostLinearSSSP.Decremental.CoreHost.Preserves b B K state
        (DecrAlmostLinearSSSP.Decremental.CoreRequest.realCode slot source)))))) ∧ ((((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b),
  @LE.le.{0} Nat instLENat b.input.n B →
    DecrAlmostLinearSSSP.Decremental.CoreHost.Preserves b B K state
      DecrAlmostLinearSSSP.Decremental.CoreRequest.endpointCode) ∧ (∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {B N m exponent : Nat} {K K0 ξ h Γ init : Real}
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
                                                          DecrAlmostLinearSSSP.Decremental.Machine))))))))))))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b),
  @LE.le.{0} Nat instLENat b.input.n B →
    ∀ (k a c : Nat),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) k →
        DecrAlmostLinearSSSP.Decremental.CoreHost.Preserves b B K state
          (DecrAlmostLinearSSSP.Decremental.Structured.div k a c)) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b),
  @LE.le.{0} Nat instLENat b.input.n B →
    DecrAlmostLinearSSSP.Decremental.CoreHost.Preserves b B K state
      DecrAlmostLinearSSSP.Decremental.CoreRequest.ratioCode) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b),
  @LE.le.{0} Nat instLENat b.input.n B →
    DecrAlmostLinearSSSP.Decremental.CoreHost.Preserves b B K state
      DecrAlmostLinearSSSP.Decremental.CoreRequest.eraseCode)))) ∧ (((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b),
  @LE.le.{0} Nat instLENat b.input.n B →
    ∀ (source : Nat),
      @Ne.{1} Nat source (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
        DecrAlmostLinearSSSP.Decremental.CoreHost.Preserves b B K state
          (DecrAlmostLinearSSSP.Decremental.CoreRequest.queryCode source)) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b),
  @LE.le.{0} Nat instLENat b.input.n B →
    DecrAlmostLinearSSSP.Decremental.CoreHost.Preserves b B K state
      DecrAlmostLinearSSSP.Decremental.CoreRequest.insertCode)) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b),
  @LE.le.{0} Nat instLENat b.input.n B →
    DecrAlmostLinearSSSP.Decremental.CoreHost.Preserves b B K state
      DecrAlmostLinearSSSP.Decremental.CoreRequest.pairedCode) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b),
  @LE.le.{0} Nat instLENat b.input.n B →
    DecrAlmostLinearSSSP.Decremental.CoreHost.Preserves b B K state
      DecrAlmostLinearSSSP.Decremental.CoreRequest.toggleCode) ∧ (∀ {n k : Nat} (B R N : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program)
  (g : DecrAlmostLinearSSSP.Decremental.Machine) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (e : Fin k)
  (a b : Fin n) (capacity : Real),
  DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N g s →
    (∃ r,
        @Eq.{1} Nat R
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val k e)) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626)))) (@Fin.val n a) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 628) (instOfNatNat (nat_lit 628)))) (@Fin.val n b) →
            @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 612) (instOfNatNat (nat_lit 612)))) capacity →
              ∃ t,
                And
                  (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                    DecrAlmostLinearSSSP.Decremental.CoreRequest.insertCode s
                    (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18))) t)
                  (DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N
                    (@DecrAlmostLinearSSSP.Decremental.cutRequest n k p g
                      (@DecrAlmostLinearSSSP.Decremental.CutOp.insert n k e a b capacity))
                    t))))))) ∧ (((((∀ {n k : Nat} (B R N : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program)
  (g : DecrAlmostLinearSSSP.Decremental.Machine) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (a b : Fin n)
  (delta : Real),
  DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N g s →
    (∃ r,
        @Eq.{1} Nat R
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 628) (instOfNatNat (nat_lit 628)))) (@Fin.val n a) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626)))) (@Fin.val n b) →
          @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 614) (instOfNatNat (nat_lit 614)))) delta →
            ∃ t,
              And
                (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                  DecrAlmostLinearSSSP.Decremental.CoreRequest.pairedCode s
                  (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15))) t)
                (DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N
                  (@DecrAlmostLinearSSSP.Decremental.cutRequest n k p g
                    (@DecrAlmostLinearSSSP.Decremental.CutOp.paired n k a b delta))
                  t)) ∧ (∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {B N m exponent : Nat} {K K0 ξ h Γ init : Real}
  {impl : DecrAlmostLinearSSSP.Decremental.CutImplementation} {state : DecrAlmostLinearSSSP.Decremental.State b}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  (ctx : DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context b B N m exponent impl K0 ξ h Γ init s),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    @LE.le.{0} Nat instLENat b.input.n B →
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) N →
        @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.registerBound impl.program.code) N →
          ∀ (op : DecrAlmostLinearSSSP.Decremental.CutOp b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)),
            @DecrAlmostLinearSSSP.Decremental.CutOp.Valid b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                  (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m exponent impl K0 ξ h Γ init s
                    ctx))
                op →
              @DecrAlmostLinearSSSP.Decremental.Physical.Valid b.input.n
                  (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                  (@DecrAlmostLinearSSSP.Decremental.applyPhysical b.input.n
                    (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                    (@DecrAlmostLinearSSSP.Decremental.CutState.physical b.input.n
                      (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                      (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                        (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m exponent impl K0 ξ h Γ
                          init s ctx)))
                    op)
                  m exponent →
                ∀ (setup : DecrAlmostLinearSSSP.Decremental.Structured.Cmd) (setupCost : Nat),
                  DecrAlmostLinearSSSP.Decremental.CoreHost.Preserves b B K state setup →
                    (∃ u,
                        And (DecrAlmostLinearSSSP.Decremental.Structured.Eval setup s setupCost u)
                          (DecrAlmostLinearSSSP.Decremental.CoreSource.Image B
                            (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N
                            (@DecrAlmostLinearSSSP.Decremental.cutRequest b.input.n
                              (DecrAlmostLinearSSSP.Decremental.logicalCount b) impl.program
                              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m exponent impl K0
                                ξ h Γ init s ctx)
                              op)
                            u)) →
                      ∃ cost t next,
                        And
                          (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                            (setup.seq
                              (DecrAlmostLinearSSSP.Decremental.SourceCall.code N impl.program.update impl.program))
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
                                        (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m
                                            exponent impl K0 ξ h Γ init t next).work
                                        (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m
                                            exponent impl K0 ξ h Γ init s ctx).work)))
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) N))
                                (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))))
                            (And (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state t)
                              (And
                                (DecrAlmostLinearSSSP.Decremental.ShadowDataRep B
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) t
                                  (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m exponent impl
                                    K0 ξ h Γ init t next))
                                (And
                                  (@DecrAlmostLinearSSSP.Decremental.CutTransition b.input.n
                                    (DecrAlmostLinearSSSP.Decremental.logicalCount b) K0 ξ
                                    (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m exponent
                                        impl K0 ξ h Γ init s ctx))
                                    op
                                    (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m exponent
                                      impl K0 ξ h Γ init t next)
                                    (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m exponent
                                        impl K0 ξ h Γ init t next)))
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
                                            op
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
                                        (@LE.le.{0} Nat instLENat
                                          (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m
                                              exponent impl K0 ξ h Γ init s ctx).work
                                          (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m
                                              exponent impl K0 ξ h Γ init t next).work)))))))))) ∧ ((∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {B N m exponent : Nat} {K0 ξ h Γ init : Real}
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
      ξ)) ∧ (∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {B N m exponent : Nat} {K0 ξ h Γ init : Real}
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
                ctx))))))))) ∧ (((∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {B N m exponent : Nat} {K K0 ξ h Γ init : Real}
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
                                                exponent impl K0 ξ h Γ init s ctx)))))))))))) ∧ (∀ (B R N : Nat) (g : DecrAlmostLinearSSSP.Decremental.Machine) {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {cost : Nat} {cmd : DecrAlmostLinearSSSP.Decremental.Structured.Cmd},
  DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N g s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval cmd s cost t →
      DecrAlmostLinearSSSP.Decremental.Structured.NoMemory cmd →
        @Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.Structured.evenRegisters cmd) Bool.true →
          (∀ (k : Nat),
              @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat)
                  (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))
                    (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112)))
                      (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106)))
                        (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50)))
                          (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56)))
                            (@List.nil.{0} Nat))))))
                  k →
                DecrAlmostLinearSSSP.Decremental.Structured.NatFrame cmd k) →
            DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N g t)) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {cost : Nat}
  {cmd : DecrAlmostLinearSSSP.Decremental.Structured.Cmd},
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    @LE.le.{0} Nat instLENat b.input.n B →
      DecrAlmostLinearSSSP.Decremental.Structured.Eval cmd s cost t →
        DecrAlmostLinearSSSP.Decremental.Structured.NoMemory cmd →
          (∀ (k : Nat),
              @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat)
                  DecrAlmostLinearSSSP.Decremental.CoreHost.NatRegisters k →
                DecrAlmostLinearSSSP.Decremental.Structured.NatFrame cmd k) →
            (∀ (k : Nat),
                @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat)
                    DecrAlmostLinearSSSP.Decremental.CoreHost.RealRegisters k →
                  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame cmd k) →
              DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state t) ∧ ((∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {B N m exponent : Nat} {K K0 ξ h Γ init : Real}
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
            ∀ (source dest : Nat),
              @Ne.{1} Nat source (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
                @Ne.{1} Nat source (@OfNat.ofNat.{0} Nat (nat_lit 632) (instOfNatNat (nat_lit 632))) →
                  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 535) (instOfNatNat (nat_lit 535))) dest →
                    @Eq.{1} Nat
                        (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) dest
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                      ∀ (v : Fin b.input.n),
                        @Eq.{1} Nat (s.natReg source)
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val b.input.n v)) →
                          ∃ cost t next,
                            And
                              (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.captureQueryCode N source dest
                                  impl.program)
                                s cost t)
                              (And
                                (@LE.le.{0} Nat instLENat cost
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (DecrAlmostLinearSSSP.Decremental.dispatchCharge impl.program.code)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                                          (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m
                                              exponent impl K0 ξ h Γ init t next).work
                                          (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m
                                              exponent impl K0 ξ h Γ init s ctx).work))
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) N))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 23) (instOfNatNat (nat_lit 23)))))
                                (And (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state t)
                                  (And
                                    (@Eq.{1}
                                      (DecrAlmostLinearSSSP.Decremental.CutState b.input.n
                                        (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                      (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                        (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m
                                          exponent impl K0 ξ h Γ init t next))
                                      (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                        (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m
                                          exponent impl K0 ξ h Γ init s ctx)))
                                    (And
                                      (@Eq.{1} Real (t.realReg dest)
                                        (@DecrAlmostLinearSSSP.Decremental.CutState.y b.input.n
                                          (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                          (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                            (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m
                                              exponent impl K0 ξ h Γ init s ctx))
                                          v))
                                      (And
                                        (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                                          (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.first b B N m
                                            exponent impl K0 ξ h Γ init t next)
                                          (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.first b B N m
                                            exponent impl K0 ξ h Γ init s ctx))
                                        (And
                                          (@Eq.{1}
                                            (List.{0}
                                              (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                            (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N m
                                              exponent impl K0 ξ h Γ init t next)
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
                                              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N m
                                                exponent impl K0 ξ h Γ init s ctx)
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
                                                (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines b B N
                                                  m exponent impl K0 ξ h Γ init s ctx)
                                                (@List.cons.{0} DecrAlmostLinearSSSP.Decremental.Machine
                                                  (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                                    m exponent impl K0 ξ h Γ init t next)
                                                  (@List.nil.{0} DecrAlmostLinearSSSP.Decremental.Machine))))
                                            (And
                                              (@LE.le.{0} Nat instLENat
                                                (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m
                                                    exponent impl K0 ξ h Γ init s ctx).work
                                                (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m
                                                    exponent impl K0 ξ h Γ init t next).work)
                                              (@Eq.{1} Nat
                                                (DecrAlmostLinearSSSP.Decremental.reportVolume
                                                  (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines b B
                                                    N m exponent impl K0 ξ h Γ init t next))
                                                (DecrAlmostLinearSSSP.Decremental.reportVolume
                                                  (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines b B
                                                    N m exponent impl K0 ξ h Γ init s ctx)))))))))))) ∧ (∀ (N source : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program) (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 54) (instOfNatNat (nat_lit 54))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 632) (instOfNatNat (nat_lit 632))) →
              DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
                (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.queryCode N source p) k))))) ∧ ((((∀ (N source : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program) (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
        (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.queryCode N source p) k) ∧ (∀ (N source dest : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program) (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 54) (instOfNatNat (nat_lit 54))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 632) (instOfNatNat (nat_lit 632))) →
              DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
                (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.captureQueryCode N source dest p) k)) ∧ ((∀ (N source dest : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program) (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k dest →
        DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
          (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.captureQueryCode N source dest p) k) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (s : DecrAlmostLinearSSSP.Decremental.State b) {l : Nat}
  (E : Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)) (x : Fin b.input.n → Real),
  @Eq.{1} Real
    (@DecrAlmostLinearSSSP.Decremental.physicalNorm b.input.n l
      (@DecrAlmostLinearSSSP.Decremental.indexedPhysical b s l E) x)
    (DecrAlmostLinearSSSP.Decremental.norm b (@DecrAlmostLinearSSSP.Decremental.State.cache b s) x)) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (s : DecrAlmostLinearSSSP.Decremental.State b) {l : Nat}
  (E : Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)) (C : Finset.{0} (Fin b.input.n)),
  @Eq.{1} Real
    (@DecrAlmostLinearSSSP.Decremental.cutCapacity b.input.n l
      (@DecrAlmostLinearSSSP.Decremental.indexedPhysical b s l E) C)
    (@DecrAlmostLinearSSSP.Decremental.cutCapacity b.input.n
      (@Fintype.card.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)
        (@instFintypeSum.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b)
          (Fin.fintype b.input.k) (DecrAlmostLinearSSSP.Decremental.instFintypeReturnVertex b)))
      (DecrAlmostLinearSSSP.Decremental.cachedPhysical b s) C))))) ∧ (((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (s : DecrAlmostLinearSSSP.Decremental.State b) {l : Nat}
  (E : Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)) (K G U : Real) (C : Finset.{0} (Fin b.input.n)),
  @DecrAlmostLinearSSSP.Decremental.RatioGuarantee b.input.n l
      (@DecrAlmostLinearSSSP.Decremental.indexedPhysical b s l E) K G U C →
    @DecrAlmostLinearSSSP.Decremental.RatioGuarantee b.input.n
      (@Fintype.card.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)
        (@instFintypeSum.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b)
          (Fin.fintype b.input.k) (DecrAlmostLinearSSSP.Decremental.instFintypeReturnVertex b)))
      (DecrAlmostLinearSSSP.Decremental.cachedPhysical b s) K G U C) ∧ (∀ {n k : Nat} {h : DecrAlmostLinearSSSP.Decremental.Physical n k} {K K' G U : Real} {C : Finset.{0} (Fin n)},
  @DecrAlmostLinearSSSP.Decremental.RatioGuarantee n k h K G U C →
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
      @LE.le.{0} Real Real.instLE K K' → @DecrAlmostLinearSSSP.Decremental.RatioGuarantee n k h K' G U C)) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) {l : Nat}
  (E : Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)) (s : DecrAlmostLinearSSSP.Decremental.State b)
  (c t : DecrAlmostLinearSSSP.Decremental.CutState b.input.n l) (K K0 : Real)
  (g : DecrAlmostLinearSSSP.Decremental.Machine) (reports : List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)),
  @DecrAlmostLinearSSSP.Decremental.CutModel b l E s c →
    @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) (@DecrAlmostLinearSSSP.Decremental.State.pending b s)
        (@List.nil.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) →
      @DecrAlmostLinearSSSP.Decremental.CutTransition b.input.n l K0
          (@HPow.hPow.{0, 0, 0} Real Int Real
            (@instHPow.{0, 0} Real Int (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid))) K
            (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
          c
          (@DecrAlmostLinearSSSP.Decremental.CutOp.toggle b.input.n l
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HPow.hPow.{0, 0, 0} Real Nat Real
                  (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) K
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@DecrAlmostLinearSSSP.Decremental.CutState.lastU b.input.n l c))))
          g t →
        (∀ (e : DecrAlmostLinearSSSP.Decremental.Edge b),
            Iff
              (@Membership.mem.{0, 0} (DecrAlmostLinearSSSP.Decremental.Edge b)
                (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
                (@List.instMembership.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) reports e)
              (@DecrAlmostLinearSSSP.Decremental.Reported l g
                (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l))
                  (DecrAlmostLinearSSSP.Decremental.Edge b) (fun x => Fin l)
                  (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l))
                    (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)
                    (@Equiv.instEquivLike.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)))
                  E e))) →
          DecrAlmostLinearSSSP.Decremental.ReportsComplete b K s (@DecrAlmostLinearSSSP.Decremental.modelReply b l c)
            reports) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) {l : Nat}
  (E : Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)) (s : DecrAlmostLinearSSSP.Decremental.State b)
  (c t : DecrAlmostLinearSSSP.Decremental.CutState b.input.n l) (K K0 : Real)
  (g : DecrAlmostLinearSSSP.Decremental.Machine) (reports : List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)),
  @DecrAlmostLinearSSSP.Decremental.CutModel b l E s c →
    @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) (@DecrAlmostLinearSSSP.Decremental.State.pending b s)
        (@List.nil.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) →
      @DecrAlmostLinearSSSP.Decremental.CutTransition b.input.n l K0
          (@HPow.hPow.{0, 0, 0} Real Int Real
            (@instHPow.{0, 0} Real Int (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid))) K
            (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
          c
          (@DecrAlmostLinearSSSP.Decremental.CutOp.toggle b.input.n l
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HPow.hPow.{0, 0, 0} Real Nat Real
                  (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) K
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@DecrAlmostLinearSSSP.Decremental.CutState.lastU b.input.n l c))))
          g t →
        (∀ (e : DecrAlmostLinearSSSP.Decremental.Edge b),
            Iff
              (@Membership.mem.{0, 0} (DecrAlmostLinearSSSP.Decremental.Edge b)
                (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
                (@List.instMembership.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) reports e)
              (@DecrAlmostLinearSSSP.Decremental.Reported l g
                (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l))
                  (DecrAlmostLinearSSSP.Decremental.Edge b) (fun x => Fin l)
                  (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l))
                    (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)
                    (@Equiv.instEquivLike.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)))
                  E e))) →
          @DecrAlmostLinearSSSP.Decremental.CutModel b l E
            (DecrAlmostLinearSSSP.Decremental.reportedToggle b K s (@DecrAlmostLinearSSSP.Decremental.modelReply b l c)
              reports)
            t) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) {l : Nat}
  (E : Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)) (s : DecrAlmostLinearSSSP.Decremental.State b)
  (c t : DecrAlmostLinearSSSP.Decremental.CutState b.input.n l) (K K0 ξ : Real)
  (g : DecrAlmostLinearSSSP.Decremental.Machine),
  @DecrAlmostLinearSSSP.Decremental.CutModel b l E s c →
    @DecrAlmostLinearSSSP.Decremental.CutTransition b.input.n l K0 ξ c
        (@DecrAlmostLinearSSSP.Decremental.CutOp.ratio b.input.n l) g t →
      @Ne.{1} (Fin b.input.n → Real) (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b s)
          (@OfNat.ofNat.{0} (Fin b.input.n → Real) (nat_lit 0)
            (@Zero.toOfNat0.{0} (Fin b.input.n → Real)
              (@Pi.instZero.{0, 0} (Fin b.input.n) (fun a => Real) fun i => Real.instZero))) →
        @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K0 →
          @LE.le.{0} Real Real.instLE K0 K →
            And (@DecrAlmostLinearSSSP.Decremental.CutModel b l E s t)
              (And
                (@DecrAlmostLinearSSSP.Decremental.RatioGuarantee b.input.n
                  (@Fintype.card.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)
                    (@instFintypeSum.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b)
                      (Fin.fintype b.input.k) (DecrAlmostLinearSSSP.Decremental.instFintypeReturnVertex b)))
                  (DecrAlmostLinearSSSP.Decremental.cachedPhysical b s) K
                  (@DecrAlmostLinearSSSP.Decremental.CutState.lastG b.input.n l t)
                  (@DecrAlmostLinearSSSP.Decremental.CutState.lastU b.input.n l t)
                  (@DecrAlmostLinearSSSP.Decremental.CutState.lastCut b.input.n l t))
                (@Eq.{1} Bool (@DecrAlmostLinearSSSP.Decremental.CutState.hasCut b.input.n l t) Bool.true)))))))))) := by
  exact ⟨⟨⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.return_pass_eval,DecrAlmostLinearSSSP.Decremental.CoreInitialize.records_eval⟩,⟨DecrAlmostLinearSSSP.Decremental.CoreInitialize.records_even,DecrAlmostLinearSSSP.Decremental.CoreInitialize.records_head_frame⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.Invariant.final_pending,DecrAlmostLinearSSSP.Decremental.CorePending.token_eq_zero⟩,⟨DecrAlmostLinearSSSP.Decremental.CorePending.View.empty_iff,⟨DecrAlmostLinearSSSP.Decremental.CorePending.popTail_eval,DecrAlmostLinearSSSP.Decremental.CorePending.dequeue⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.CorePending.nat_frame,DecrAlmostLinearSSSP.Decremental.CorePending.real_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.CorePending.pop_nat_frame,DecrAlmostLinearSSSP.Decremental.CorePending.pop_real_frame⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.CorePending.encoded_member,DecrAlmostLinearSSSP.Decremental.CorePending.record_guest_disjoint⟩,⟨DecrAlmostLinearSSSP.Decremental.CorePending.MemoryFrame.refl,⟨DecrAlmostLinearSSSP.Decremental.CorePending.MemoryFrame.trans,DecrAlmostLinearSSSP.Decremental.CorePending.MemoryFrame.guest⟩⟩⟩⟩⟩,⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.CoreHost.initial_image,DecrAlmostLinearSSSP.Decremental.CoreRequest.nat_prefix_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.CoreRequest.real_prefix_frame,DecrAlmostLinearSSSP.Decremental.CoreRequest.tag_prefix_frame⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.CoreRequest.host_nat_frame,DecrAlmostLinearSSSP.Decremental.CoreRequest.host_real_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.CoreRequest.erase_nat_frame,⟨DecrAlmostLinearSSSP.Decremental.CoreRequest.erase_real_frame,DecrAlmostLinearSSSP.Decremental.CoreRequest.query_nat_frame⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.CoreRequest.query_real_frame,DecrAlmostLinearSSSP.Decremental.CoreRequest.endpoint_eval⟩,⟨DecrAlmostLinearSSSP.Decremental.CoreRequest.endpoint_nat_frame,⟨DecrAlmostLinearSSSP.Decremental.CoreRequest.endpoint_real_frame,DecrAlmostLinearSSSP.Decremental.CoreRequest.endpoint_image⟩⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.CoreRequest.toggle_eval,DecrAlmostLinearSSSP.Decremental.CoreHost.Address.below_source⟩,⟨DecrAlmostLinearSSSP.Decremental.CoreHost.Address.guest_disjoint,⟨DecrAlmostLinearSSSP.Decremental.CoreHost.source_frame,DecrAlmostLinearSSSP.Decremental.CoreHost.Image.temp_nat⟩⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.CoreHost.Image.temp_real,DecrAlmostLinearSSSP.Decremental.CoreHost.Image.nat_patch⟩,⟨DecrAlmostLinearSSSP.Decremental.CoreHost.Image.real_patch,DecrAlmostLinearSSSP.Decremental.CoreHost.Image.tagged⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.CoreHost.Image.endpoints,DecrAlmostLinearSSSP.Decremental.CoreHost.Preserves.seq⟩,⟨DecrAlmostLinearSSSP.Decremental.CoreHost.preserves_tag,⟨DecrAlmostLinearSSSP.Decremental.CoreHost.preserves_nat,DecrAlmostLinearSSSP.Decremental.CoreHost.preserves_real⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.CoreHost.preserves_endpoints,DecrAlmostLinearSSSP.Decremental.CoreNativeCut.call⟩,⟨DecrAlmostLinearSSSP.Decremental.CoreHost.preserves_div,⟨DecrAlmostLinearSSSP.Decremental.CoreHost.preserves_ratio,DecrAlmostLinearSSSP.Decremental.CoreHost.preserves_erase⟩⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.CoreHost.preserves_query,DecrAlmostLinearSSSP.Decremental.CoreHost.preserves_insert⟩,⟨DecrAlmostLinearSSSP.Decremental.CoreHost.preserves_paired,⟨DecrAlmostLinearSSSP.Decremental.CoreHost.preserves_toggle,DecrAlmostLinearSSSP.Decremental.CoreRequest.insert_eval⟩⟩⟩⟩⟩,⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.CoreRequest.paired_eval,DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.advance⟩,⟨DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.report_bound,DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.work_bound⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.query,DecrAlmostLinearSSSP.Decremental.CoreSource.Image.command_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.CoreHost.Image.command_frame,⟨DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.capture_query,DecrAlmostLinearSSSP.Decremental.CoreNativeCut.query_nat_frame⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.CoreNativeCut.query_real_frame,DecrAlmostLinearSSSP.Decremental.CoreNativeCut.capture_nat_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.CoreNativeCut.capture_real_frame,⟨DecrAlmostLinearSSSP.Decremental.indexedPhysical_norm_eq,DecrAlmostLinearSSSP.Decremental.indexedPhysical_capacity_eq⟩⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.indexedPhysical_ratio,DecrAlmostLinearSSSP.Decremental.RatioGuarantee.weaken⟩,⟨DecrAlmostLinearSSSP.Decremental.CutModel.toggle_complete,⟨DecrAlmostLinearSSSP.Decremental.CutModel.toggle,DecrAlmostLinearSSSP.Decremental.CutModel.ratio⟩⟩⟩⟩⟩⟩⟩
