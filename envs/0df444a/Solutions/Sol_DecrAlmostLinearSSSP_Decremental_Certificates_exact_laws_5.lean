-- Prove2me | solution 1 for DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T11:14:38.39999+00:00
-- url     : https://prove2.me/submissions/d9751b03-b796-409c-aef5-44f66580f97c

import Definitions.Def_DecrAlmostLinearSSSP_RAMFoundation
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_2
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_3
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_4
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
open scoped ENNReal NNReal
attribute [local instance] Classical.propDecidable
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
theorem DecrAlmostLinearSSSP.Decremental.scale_positive : ∀ (j : Nat),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
    (DecrAlmostLinearSSSP.Decremental.scale j) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.1.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.delta_positive : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (j : Nat),
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (DecrAlmostLinearSSSP.Decremental.delta i j) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.1.1.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.Powers.body_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.Powers.body s
    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
    (DecrAlmostLinearSSSP.Decremental.Exact.Powers.advanced s) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.1.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.Powers.body_nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 248) (instOfNatNat (nat_lit 248))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 250) (instOfNatNat (nat_lit 250))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 252) (instOfNatNat (nat_lit 252))) →
        DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.Powers.body k := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.1.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.Powers.loop_eval : ∀ (bound base remaining done : Nat),
  @Eq.{1} Nat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) done remaining)
      (DecrAlmostLinearSSSP.Decremental.Exact.height bound) →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
      DecrAlmostLinearSSSP.Decremental.Exact.Powers.Prefix bound base done s →
        ∃ t,
          And
            (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.Powers.loop s
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))) remaining)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              t)
            (And
              (DecrAlmostLinearSSSP.Decremental.Exact.Powers.Prefix bound base
                (DecrAlmostLinearSSSP.Decremental.Exact.height bound) t)
              (And (@Eq.{1} (Nat → Real) t.realMem s.realMem)
                (∀ (address : Nat),
                  Or
                      (@LT.lt.{0} Nat instLTNat address
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base done))
                      (@LE.le.{0} Nat instLENat
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                          (DecrAlmostLinearSSSP.Decremental.Exact.height bound))
                        address) →
                    @Eq.{1} Nat (t.natMem address) (s.natMem address)))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.1.2.1.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.guest_bank_ne_host : ∀ (base j a b : Nat),
  @Ne.{1} Nat (DecrAlmostLinearSSSP.Decremental.bankAddress base j a)
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.1.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.scaled_less : ∀ (F a b : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) F →
    Iff
      (@LT.lt.{0} Nat instLTNat (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F a)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F b))
      (@LT.lt.{0} Nat instLTNat a b) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.2.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.shadowReg_ne_meta : ∀ (j k : Nat),
  @LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) →
    @Ne.{1} Nat (DecrAlmostLinearSSSP.Decremental.shadowReg j) k := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.2.1.2.2.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.shadow_scalar : ∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    ∀ (ins tr : DecrAlmostLinearSSSP.Decremental.Instruction),
      @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (DecrAlmostLinearSSSP.Decremental.shadowScalarTranslation ins)
          (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction tr) →
        DecrAlmostLinearSSSP.Decremental.ShadowRep base F (DecrAlmostLinearSSSP.Decremental.instructionEffect tr c)
          (DecrAlmostLinearSSSP.Decremental.instructionEffect ins g) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.2.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.shadow_cast : ∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) F →
      ∀ (d a : Nat),
        @Eq.{1} Real (c.realReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
            (@Nat.cast.{0} Real Real.instNatCast F) →
          DecrAlmostLinearSSSP.Decremental.ShadowRep base F
            (DecrAlmostLinearSSSP.Decremental.instructionEffect
              (DecrAlmostLinearSSSP.Decremental.Instruction.div (DecrAlmostLinearSSSP.Decremental.shadowReg d)
                (DecrAlmostLinearSSSP.Decremental.shadowReg d)
                (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
              (DecrAlmostLinearSSSP.Decremental.instructionEffect
                (DecrAlmostLinearSSSP.Decremental.Instruction.cast (DecrAlmostLinearSSSP.Decremental.shadowReg d)
                  (DecrAlmostLinearSSSP.Decremental.shadowReg a))
                c))
            (DecrAlmostLinearSSSP.Decremental.instructionEffect (DecrAlmostLinearSSSP.Decremental.Instruction.cast d a)
              g) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.2.2.2.2.1
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
lemma shadow_store {base F : ℕ} {c g : Machine} (h : ShadowRep base F c g) (hF : 0 < F) (a d : ℕ)
    (ha : c.natReg 6 = base + F * (2 * g.natReg a + 1)) :
    ShadowRep base F (instructionEffect (.store 6 (shadowReg d)) c) (instructionEffect (.store a d) g) := by
  simp only [instructionEffect, ha, h.realReg]
  exact h.real_memory hF _ _
lemma shadow_storeN {base F : ℕ} {c g : Machine} (h : ShadowRep base F c g) (hF : 0 < F) (a d : ℕ)
    (ha : c.natReg 6 = base + F * (2 * g.natReg a + 1)) :
    ShadowRep base F (instructionEffect (.storeN 6 (shadowReg d)) c) (instructionEffect (.storeN a d) g) := by
  simp only [instructionEffect, ha, h.natReg]
  exact h.nat_memory hF _ _
lemma shadow_address_calculation {base F : ℕ} {c g : Machine} (h : ShadowRep base F c g)
    (hbase : c.natReg 0 = base) (hfactor : c.natReg 7 = F) (a : ℕ) :
    let c1 := instructionEffect (.nadd 6 (shadowReg a) (shadowReg a)) c
    let c2 := instructionEffect (.nadd 6 6 0) c1
    let c3 := instructionEffect (.nadd 6 6 7) c2
    ShadowRep base F c3 g ∧ c3.natReg 6 = base + F * (2 * g.natReg a + 1) := by
  classical
  dsimp only
  let c1 := instructionEffect (.nadd 6 (shadowReg a) (shadowReg a)) c
  let c2 := instructionEffect (.nadd 6 6 0) c1
  let c3 := instructionEffect (.nadd 6 6 7) c2
  have hr1 : ShadowRep base F c1 g := h.scratch _
  have hr2 : ShadowRep base F c2 g := hr1.scratch _
  have hr3 : ShadowRep base F c3 g := hr2.scratch _
  refine ⟨hr3, ?_⟩
  change c3.natReg 6 = _
  simp [c3, c2, c1, instructionEffect, hbase, hfactor, h.natReg]
  ring
end DecrAlmostLinearSSSP.Decremental
end s71
section s72
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma ShadowRep.metadata {base F : ℕ} {c g : Machine} (h : ShadowRep base F c g)
    (pc work : ℕ) :
    ShadowRep base F
      {c with natReg := Function.update (Function.update c.natReg 2 pc) 3 work}
      {g with pc := pc, work := work} := by
  classical
  refine ⟨by simp, by simp, ?_, ?_, h.realReg, ?_, h.realMem, h.natMem⟩
  · simpa only [Function.update_of_ne (by omega : (4 : ℕ) ≠ 3), Function.update_of_ne (by omega : (4 : ℕ) ≠ 2)] using h.halted
  · simpa only [Function.update_of_ne (by omega : (5 : ℕ) ≠ 3), Function.update_of_ne (by omega : (5 : ℕ) ≠ 2)] using h.fault
  · intro j
    simp only [Function.update_of_ne (shadowReg_ne_meta j 3 (by omega)),
      Function.update_of_ne (shadowReg_ne_meta j 2 (by omega))]
    exact h.natReg j
lemma ShadowRep.pc_update {base F : ℕ} {c g : Machine} (h : ShadowRep base F c g)
    (pc : ℕ) :
    ShadowRep base F {c with natReg := Function.update c.natReg 2 pc} {g with pc := pc} := by
  classical
  refine ⟨by simp, ?_, ?_, ?_, h.realReg, ?_, h.realMem, h.natMem⟩
  · simpa only [Function.update_of_ne (by omega : (3 : ℕ) ≠ 2)] using h.work
  · simpa only [Function.update_of_ne (by omega : (4 : ℕ) ≠ 2)] using h.halted
  · simpa only [Function.update_of_ne (by omega : (5 : ℕ) ≠ 2)] using h.fault
  · intro j
    simp only [Function.update_of_ne (shadowReg_ne_meta j 2 (by omega))]
    exact h.natReg j
lemma ShadowRep.halt_update {base F : ℕ} {c g : Machine} (h : ShadowRep base F c g) :
    ShadowRep base F {c with natReg := Function.update c.natReg 4 1} {g with halted := true} := by
  classical
  refine ⟨?_, ?_, by simp, ?_, h.realReg, ?_, h.realMem, h.natMem⟩
  · simpa only [Function.update_of_ne (by omega : (2 : ℕ) ≠ 4)] using h.pc
  · simpa only [Function.update_of_ne (by omega : (3 : ℕ) ≠ 4)] using h.work
  · simpa only [Function.update_of_ne (by omega : (5 : ℕ) ≠ 4)] using h.fault
  · intro j
    simp only [Function.update_of_ne (shadowReg_ne_meta j 4 (by omega))]
    exact h.natReg j
lemma shadow_nat_comparison {base F : ℕ} {c g : Machine} (h : ShadowRep base F c g)
    (hF : 0 < F) (a b : ℕ) : c.natReg (shadowReg a) < c.natReg (shadowReg b) ↔ g.natReg a < g.natReg b := by
  rw [h.natReg, h.natReg]
  exact scaled_less F _ _ hF
lemma shadow_real_comparison {base F : ℕ} {c g : Machine} (h : ShadowRep base F c g)
    (a b : ℕ) : c.realReg (shadowReg a) < c.realReg (shadowReg b) ↔ g.realReg a < g.realReg b := by
  rw [h.realReg, h.realReg]
end DecrAlmostLinearSSSP.Decremental
end s72
section s73
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
lemma ShadowRep.data_machine {B F : ℕ} {c g : Machine} (h : ShadowRep B F c g) :
    ShadowRep B F (Structured.data c).machine g :=
  ⟨h.pc,h.work,h.halted,h.fault,h.realReg,h.natReg,h.realMem,h.natMem⟩
lemma ShadowDataRep.effect {B F : ℕ} {s : Data} {g : Machine} (a : Atom)
    (h : ShadowRep B F (instructionEffect a.instruction s.machine) g) :
    ShadowDataRep B F (a.effect s) g := h.data_machine
lemma ShadowDataRep.header {B F : ℕ} {s : Data} {g : Machine}
    (h : ShadowDataRep B F s g) (hone : s.natReg 1 = 1) :
    ShadowDataRep B F
      {s with natReg := Function.update (Function.update s.natReg 2 (g.pc+1)) 3 (s.natReg 3+1)}
      {g with pc := g.pc+1,work := g.work+1} := by
  have hh := (h.metadata (g.pc+1) (g.work+1)).data_machine
  change ShadowDataRep B F
    {s with natReg := Function.update (Function.update s.natReg 2 (g.pc+1)) 3 (g.work+1)}
    {g with pc := g.pc+1,work := g.work+1} at hh
  have hw : s.natReg 3 = g.work := h.work
  simpa only [hw] using hh
lemma eval_shadow_header (s : Data) (pc : ℕ) :
    Eval (.seq (natural 2 (pc+1)) (nadd 3 3 1)) s 2
      {s with natReg := Function.update (Function.update s.natReg 2 (pc+1)) 3 (s.natReg 3+s.natReg 1)} := by
  simpa only [Function.update_of_ne (by decide : (3 : ℕ) ≠ 2),
    Function.update_of_ne (by decide : (1 : ℕ) ≠ 2)] using
    Eval.seq (eval_natural s 2 (pc+1)) (eval_nadd _ 3 3 1)
lemma eval_shadow_scalar {B F : ℕ} {s : Data} {g : Machine}
    (h : ShadowDataRep B F s g) (ins tr : Instruction) (ht : shadowScalarTranslation ins = some tr) :
    ∃ (a : Atom), a.instruction = tr ∧
      Eval (.atom a) s 1 (a.effect s) ∧ ShadowDataRep B F (a.effect s) (instructionEffect ins g) := by
  have hstraight : Straight tr := by
    cases ins <;> simp only [shadowScalarTranslation] at ht
    all_goals try contradiction
    all_goals cases ht <;> trivial
  let a : Atom := ⟨tr,hstraight⟩
  exact ⟨a,rfl,.atom _ _,(shadow_scalar h ins tr ht).data_machine⟩
lemma eval_shadow_cast {B F : ℕ} {s : Data} {g : Machine}
    (h : ShadowDataRep B F s g) (hF : 0 < F) (d a : ℕ) (hf : s.realReg 7 = (F : ℝ)) :
    ∃ t : Data, Eval (.seq (cast (shadowReg d) (shadowReg a)) (Structured.div (shadowReg d) (shadowReg d) 7)) s 2 t ∧
      ShadowDataRep B F t (instructionEffect (.cast d a) g) := by
  let t := ((⟨.div (shadowReg d) (shadowReg d) 7,trivial⟩ : Atom).effect
    ((⟨.cast (shadowReg d) (shadowReg a),trivial⟩ : Atom).effect s))
  refine ⟨t,Eval.seq (.atom _ _) (.atom _ _),?_⟩
  have hh := (shadow_cast h hF d a hf).data_machine
  exact hh
lemma eval_shadow_address {B F : ℕ} {s : Data} {g : Machine}
    (h : ShadowDataRep B F s g) (hb : s.natReg 0 = B) (hf : s.natReg 7 = F) (a : ℕ) :
    ∃ t : Data, Eval (Structured.sequence [nadd 6 (shadowReg a) (shadowReg a),nadd 6 6 0,nadd 6 6 7]) s 3 t ∧
      ShadowDataRep B F t g ∧ t.natReg 6 = B+F*(2*g.natReg a+1) := by
  let c1 := instructionEffect (.nadd 6 (shadowReg a) (shadowReg a)) s.machine
  let c2 := instructionEffect (.nadd 6 6 0) c1
  let c3 := instructionEffect (.nadd 6 6 7) c2
  refine ⟨Structured.data c3,?_,(shadow_address_calculation h hb hf a).1.data_machine,
    (shadow_address_calculation h hb hf a).2⟩
  have he := Eval.seq (eval_nadd s 6 (shadowReg a) (shadowReg a))
    (Eval.seq (eval_nadd _ 6 6 0) (Eval.seq (eval_nadd _ 6 6 7) (Eval.skip _)))
  exact he
end DecrAlmostLinearSSSP.Decremental
end s73
section s74
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
lemma repeatedAdd_eval (s : Data) (d factor q : ℕ) (hne : factor ≠ d) :
    Eval (repeatedAdd d factor q) s q
      {s with natReg := Function.update s.natReg d (s.natReg d+q*s.natReg factor)} := by
  induction q generalizing s with
  | zero => simpa [repeatedAdd] using Eval.skip s
  | succ q ih =>
    have he := Eval.seq (eval_nadd s d d factor)
      (ih {s with natReg := Function.update s.natReg d (s.natReg d+s.natReg factor)})
    have hh : s.natReg d+s.natReg factor+q*s.natReg factor = s.natReg d+(q+1)*s.natReg factor := by ring
    simpa only [repeatedAdd,Function.update_self,Function.update_of_ne hne,
      Function.update_idem,hh,Nat.add_comm 1 q] using he
lemma structuredConstant_eval (s : Data) (d factor q : ℕ) (hne : factor ≠ d) :
    Eval (structuredConstant d factor q) s (q+1)
      {s with natReg := Function.update s.natReg d (q*s.natReg factor)} := by
  have he := Eval.seq (eval_natural s d 0)
    (repeatedAdd_eval {s with natReg := Function.update s.natReg d 0} d factor q hne)
  simpa only [structuredConstant,Function.update_self,Function.update_of_ne hne,
    Function.update_idem,Nat.zero_add,Nat.add_comm 1 q] using he
lemma eval_shadow_constant {B F : ℕ} {s : Data} {g : Machine} (h : ShadowDataRep B F s g)
    (d q : ℕ) (hf : s.natReg 7 = F) :
    ∃ t : Data, Eval (structuredConstant (shadowReg d) 7 q) s (q+1) t ∧
      ShadowDataRep B F t (instructionEffect (.natural d q) g) := by
  refine ⟨_,structuredConstant_eval s (shadowReg d) 7 q
    (Ne.symm (shadowReg_ne_meta d 7 (by omega))),?_⟩
  have hh := (h.nat_register d q).data_machine
  change ShadowDataRep B F {s with natReg := Function.update s.natReg (shadowReg d) (F*q)}
    (instructionEffect (.natural d q) g) at hh
  simpa only [hf,Nat.mul_comm q F] using hh
lemma repeatedAdd_nat_frame (d factor q k : ℕ) (hd : d ≠ k) : NatFrame (repeatedAdd d factor q) k := by
  induction q with
  | zero => trivial
  | succ q ih => exact ⟨hd,ih⟩
lemma repeatedAdd_real_frame (d factor q k : ℕ) : RealFrame (repeatedAdd d factor q) k := by
  induction q with
  | zero => trivial
  | succ q ih => exact ⟨not_false,ih⟩
end DecrAlmostLinearSSSP.Decremental
end s74
section s75
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
lemma ShadowDataRep.outside_nat_memory {B F : ℕ} {s : Data} {g : Machine}
    (h : ShadowDataRep B F s g) (address value : ℕ)
    (hout : ∀ a, address ≠ B+F*(2*a+1)) :
    ShadowDataRep B F {s with natMem := Function.update s.natMem address value} g := by
  refine ⟨h.pc,h.work,h.halted,h.fault,h.realReg,h.natReg,h.realMem,?_⟩
  intro a
  simpa only [Data.machine,Function.update_of_ne (Ne.symm (hout a))] using h.natMem a
lemma ShadowDataRep.outside_nat_register {B F : ℕ} {s : Data} {g : Machine}
    (h : ShadowDataRep B F s g) (k value : ℕ) (h2 : 2 ≠ k) (h3 : 3 ≠ k)
    (h4 : 4 ≠ k) (h5 : 5 ≠ k) (hs : ∀ j, shadowReg j ≠ k) :
    ShadowDataRep B F {s with natReg := Function.update s.natReg k value} g := by
  refine ⟨?_,?_,?_,?_,h.realReg,?_,h.realMem,h.natMem⟩
  · simpa only [Data.machine,Function.update_of_ne h2] using h.pc
  · simpa only [Data.machine,Function.update_of_ne h3] using h.work
  · simpa only [Data.machine,Function.update_of_ne h4] using h.halted
  · simpa only [Data.machine,Function.update_of_ne h5] using h.fault
  · intro j
    simpa only [Data.machine,Function.update_of_ne (hs j)] using h.natReg j
lemma shadowReg_ne_even (j k : ℕ) : shadowReg j ≠ 2*k := by dsimp [shadowReg];omega
lemma append_report_eval (s : Data) (h1 : s.natReg 1 = 1) (h14 : s.natReg 14 = 2) :
    Eval appendStoreReport s 3 (appendedReport s) := by
  have he := Eval.seq (eval_storeN s 10 6)
    (Eval.seq (eval_nadd _ 10 10 14) (Eval.seq (eval_nadd _ 12 12 1) (Eval.skip _)))
  simpa only [appendStoreReport,Structured.sequence,appendedReport,h1,h14,
    Function.update_of_ne (by decide : (12 : ℕ) ≠ 10),Function.update_of_ne (by decide : (1 : ℕ) ≠ 10)] using he
lemma append_report_rep {B F : ℕ} {s : Data} {g : Machine} (h : ShadowDataRep B F s g)
    (hout : ∀ a, s.natReg 10 ≠ B+F*(2*a+1)) : ShadowDataRep B F (appendedReport s) g := by
  have hm := h.outside_nat_memory (s.natReg 10) (s.natReg 6) hout
  have h10 := hm.outside_nat_register 10 (s.natReg 10+2) (by omega) (by omega) (by omega) (by omega)
    (fun j => shadowReg_ne_even j 5)
  exact h10.outside_nat_register 12 (s.natReg 12+1) (by omega) (by omega) (by omega) (by omega)
    (fun j => shadowReg_ne_even j 6)
lemma append_report_log (start : ℕ) (reports : List ℕ) (s : Data) (h : ReportLog start reports s) :
    ReportLog start (reports++[s.natReg 6]) (appendedReport s) := by
  refine ⟨?_,?_,?_⟩
  · simp only [appendedReport,Function.update_of_ne (by decide : (10 : ℕ) ≠ 12),
      Function.update_self,List.length_append,List.length_singleton,h.1]
    omega
  · simp only [appendedReport,Function.update_self,List.length_append,List.length_singleton,h.2.1]
  · intro j hj
    change Function.update s.natMem (s.natReg 10) (s.natReg 6) (start+2*j) = _
    by_cases hlt : j < reports.length
    · have hne : start+2*j ≠ s.natReg 10 := by rw [h.1];omega
      rw [Function.update_of_ne hne,h.2.2 j hlt,List.getElem_append_left hlt]
    · have heq : j = reports.length := by simp only [List.length_append,List.length_singleton] at hj;omega
      subst j
      rw [← h.1,Function.update_self]
      simp
lemma report_log_outside (B bank start : ℕ) (reports : List ℕ) (s : Data)
    (hstart : ∃ r, start = B+2*r+1) (hlog : ReportLog start reports s) :
    ∀ a, s.natReg 10 ≠ B+bankFactor bank*(2*a+1) := by
  obtain ⟨r,rfl⟩ := hstart
  intro a
  rw [hlog.1]
  have heq : B+2*r+1+2*reports.length = B+(2*(r+reports.length)+1) := by ring
  rw [heq]
  exact Ne.symm (guest_bank_ne_host B bank a (r+reports.length))
end DecrAlmostLinearSSSP.Decremental
end s75
section s76
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.InputCapture
open Structured
lemma eval_code (s : Data) : Eval code s 19 (result s) := eval_sequence_atoms atoms s
lemma no_memory : NoMemory code := by simp [code,atoms,Structured.sequence,NoMemory,NoStore]
lemma captures_initial (p : Program) (i : Input) : Captured i (result (data (initialMachine p i))) := by
  constructor <;> simp [result,atoms,Atom.effect,instructionEffect,data,Data.machine,initialMachine]
  all_goals omega
lemma nat_shadow_frame (j : ℕ) : NatFrame code (shadowReg j) := by
  simp only [code,atoms,List.map_cons,List.map_nil,Structured.sequence,NatFrame,writesNat,shadowReg]
  repeat' (first | apply And.intro | omega | trivial)
lemma real_shadow_frame (j : ℕ) : RealFrame code (shadowReg j) := by
  simp only [code,atoms,List.map_cons,List.map_nil,Structured.sequence,RealFrame,writesReal,shadowReg]
  repeat' (first | apply And.intro | omega | trivial)
lemma initial_shadow_zero (p : Program) (i : Input) :
    ∀ j, (result (data (initialMachine p i))).natReg (shadowReg j) = 0 ∧
      (result (data (initialMachine p i))).realReg (shadowReg j) = 0 := by
  intro j
  have hn := (eval_code (data (initialMachine p i))).nat_frame (nat_shadow_frame j)
  have hr := (eval_code (data (initialMachine p i))).real_frame (real_shadow_frame j)
  rw [hn,hr]
  have hbig : 9 ≤ shadowReg j := by dsimp [shadowReg];omega
  simp [data,initialMachine,show shadowReg j ≠ 0 by omega,show shadowReg j ≠ 1 by omega,
    show shadowReg j ≠ 2 by omega,show shadowReg j ≠ 3 by omega,show shadowReg j ≠ 4 by omega]
lemma input_tape_below_base (i : Input) (e : Fin i.k) (offset : ℕ) (hoff : offset < 3) :
    i.n+3*e.val+offset < i.n+3*i.k+2 := by omega
end DecrAlmostLinearSSSP.Decremental.InputCapture
end s76
section s77
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Powers
open Structured
lemma prepare_eval (s : Data) : Eval prepare s 9 (prepared s) := eval_sequence_atoms prepareAtoms s
lemma prepare_prefix (i : Input) (base : ℕ) (s : Data) (h : InputCapture.Captured i s) (hb : s.natReg 234 = base) :
    Prefix (i.n*i.W) base 0 (prepared s) := by
  constructor
  all_goals first | (intro j hj;omega) | (simp [prepared,prepareAtoms,Atom.effect,instructionEffect,data,Data.machine,h.zeroN,h.unit,h.vertices,h.weightBound,hb])
lemma eval_code (i : Input) (base : ℕ) (s : Data) (h : InputCapture.Captured i s) (hb : s.natReg 234 = base) :
    ∃ t, Eval code s (7*height (i.n*i.W)+11) t ∧ Prefix (i.n*i.W) base (height (i.n*i.W)) t ∧
      t.realMem = s.realMem ∧ (∀ address, address < base ∨ base+height (i.n*i.W) ≤ address → t.natMem address = s.natMem address) := by
  have hp := prepare_prefix i base s h hb
  obtain ⟨t,ht,htp,hr,hframe⟩ := loop_eval (i.n*i.W) base (height (i.n*i.W)) 0 (by omega) (prepared s) hp
  refine ⟨t,?_,htp,hr,?_⟩
  · have he := Eval.seq (prepare_eval s) ht
    have hh : 7*height (i.n*i.W)+11 = 9+(7*height (i.n*i.W)+2) := by omega
    rw [hh];exact he
  · intro address ha
    exact hframe address (by simpa only [Nat.add_zero] using ha)
lemma nat_frame (k : ℕ) (h248 : k ≠ 248) (h250 : k ≠ 250) (h252 : k ≠ 252) : NatFrame code k := by
  refine ⟨?_,body_nat_frame k h248 h250 h252⟩
  simp [prepare,prepareAtoms,Structured.sequence,NatFrame,writesNat,Ne.symm h248,Ne.symm h250,Ne.symm h252]
end DecrAlmostLinearSSSP.Decremental.Exact.Powers
end s77
section s78
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Layout
open Structured
lemma eval_code (s : Data) : Eval code s 8 (result s) := eval_sequence_atoms atoms s
lemma values (i : Input) (s : Data) (h : InputCapture.Captured i s) :
    Image (addresses (i.n+3*i.k+2) i.n i.k) (result s) := by
  constructor
  all_goals simp [result,atoms,Atom.effect,instructionEffect,data,Data.machine,h.base,h.vertices,h.edges,h.unit,addresses]
  all_goals omega
lemma no_memory : NoMemory code := by simp [code,atoms,Structured.sequence,NoMemory,NoStore]
lemma nat_frame (k : ℕ) (h224 : k ≠ 224) (h226 : k ≠ 226) (h228 : k ≠ 228)
    (h230 : k ≠ 230) (h232 : k ≠ 232) (h234 : k ≠ 234) : NatFrame code k := by
  simp [code,atoms,Structured.sequence,NatFrame,writesNat,Ne.symm h224,Ne.symm h226,Ne.symm h228,Ne.symm h230,Ne.symm h232,Ne.symm h234]
lemma real_frame (k : ℕ) : RealFrame code k := by simp [code,atoms,Structured.sequence,RealFrame,writesReal]
end DecrAlmostLinearSSSP.Decremental.Exact.Layout
end s78
section s79
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Clear
open Structured
lemma body_eval (s : Data) : Eval body s 2 (advanced s) := Eval.seq (eval_storeN s 290 56) (eval_nadd _ 290 290 26)
lemma nat_frame (k : ℕ) (hk : k ≠ 290) : NatFrame code k := by
  simp [code,body,NatFrame,storeN,nadd,writesNat,Ne.symm hk]
lemma real_frame (k : ℕ) : RealFrame code k := by simp [code,body,RealFrame,writesReal,storeN,nadd]
lemma eval_code (base length : ℕ) (s : Data)
    (hz : s.natReg 56 = 0) (h1 : s.natReg 26 = 1)
    (hp : s.natReg 290 = base) (he : s.natReg 292 = base+length) :
    ∃ t, Eval code s (4*length+2) t ∧ t.natReg 290 = base+length ∧
      (∀ a, base ≤ a → a<base+length → t.natMem a = 0) ∧ t.realMem = s.realMem ∧
      (∀ a, a<base ∨ base+length≤a → t.natMem a = s.natMem a) := by
  induction length generalizing base s with
  | zero =>
    refine ⟨s,?_,by simpa using hp,?_,rfl,fun _ _ => rfl⟩
    · have ht : ¬(Test.natLess 290 292).holds s := by simp [Test.holds,hp,he]
      exact Eval.loopNo s ht
    · intro a hlow hhigh;omega
  | succ length ih =>
    let u := advanced s
    have huz : u.natReg 56 = 0 := by simp [u,advanced,hz]
    have hu1 : u.natReg 26 = 1 := by simp [u,advanced,h1]
    have hup : u.natReg 290 = base+1 := by simp [u,advanced,hp,h1]
    have hue : u.natReg 292 = (base+1)+length := by simp [u,advanced,he];omega
    obtain ⟨t,ht,htp,htzero,htr,htframe⟩ := ih (base+1) u huz hu1 hup hue
    have htest : (Test.natLess 290 292).holds s := by simp [Test.holds,hp,he]
    refine ⟨t,?_,by omega,?_,htr,?_⟩
    · have hh := Eval.loopYes htest (body_eval s) ht
      convert hh using 1 <;> first | rfl | omega
    · intro a hlow hhigh
      by_cases ha : a=base
      · subst a
        rw [htframe base (Or.inl (by omega))]
        simp [u,advanced,hp,hz]
      · exact htzero a (by omega) (by omega)
    · intro a hout
      rw [htframe a (by omega)]
      change Function.update s.natMem (s.natReg 290) (s.natReg 56) a = s.natMem a
      rw [Function.update_of_ne (by omega)]
end DecrAlmostLinearSSSP.Decremental.Exact.Clear
end s79
section s80
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
lemma Walk.suffix_of_vertex {n k : ℕ} {g : Digraph n k} {active : Finset (Fin k)}
    {u v w : Fin n} {es : List (Fin k)} (h : Walk g active u v es)
    (hw : w ∈ u :: es.map g.head) :
    ∃ fs, Walk g active w v fs ∧ fs.IsSuffix es ∧
      (w :: fs.map g.head).IsSuffix (u :: es.map g.head) := by
  induction h generalizing w with
  | nil v =>
    simp only [List.map_nil, List.mem_singleton] at hw
    subst w
    exact ⟨[], .nil v, List.suffix_refl _, List.suffix_refl _⟩
  | @cons u v es e he h ih =>
    rw [List.map_cons, List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact ⟨e :: es, .cons (u := g.tail e) e he h, List.suffix_refl _, List.suffix_refl _⟩
    · obtain ⟨fs, hf, hs, hv⟩ := ih hw
      exact ⟨fs, hf, hs.trans (List.suffix_cons _ _),
        hv.trans (List.suffix_cons _ _)⟩
lemma Walk.erase_cycles {n k : ℕ} {g : Digraph n k} {active : Finset (Fin k)}
    {u v : Fin n} {es : List (Fin k)} (h : Walk g active u v es) :
    ∃ fs, Walk g active u v fs ∧ fs.Sublist es ∧ (u :: fs.map g.head).Nodup := by
  classical
  induction h with
  | nil v => exact ⟨[], .nil v, List.Sublist.refl [], by simp⟩
  | @cons u v es e he h ih =>
    obtain ⟨fs, hf, hsub, hnodup⟩ := ih
    by_cases hm : g.tail e ∈ g.head e :: fs.map g.head
    · obtain ⟨gs, hg, hs, hv⟩ := hf.suffix_of_vertex hm
      exact ⟨gs, hg, (hs.sublist.trans hsub).trans (List.sublist_cons_self _ _),
        hnodup.sublist hv.sublist⟩
    · refine ⟨e :: fs, .cons (u := g.tail e) e he hf, hsub.cons_cons e, ?_⟩
      simpa only [List.map_cons, List.nodup_cons] using And.intro hm hnodup
lemma Reachable.short_walk {n k : ℕ} {g : Digraph n k} {active : Finset (Fin k)}
    {u v : Fin n} (h : Reachable g active u v) :
    ∃ es, Walk g active u v es ∧ es.length < n := by
  obtain ⟨es, hw⟩ := h
  obtain ⟨fs, hf, _, hn⟩ := hw.erase_cycles
  refine ⟨fs, hf, ?_⟩
  have hc := hn.length_le_card
  simpa only [List.length_cons, List.length_map, Fintype.card_fin, Nat.succ_le_iff] using hc
lemma Walk.cost_telescope {n k : ℕ} {g : Digraph n k} {active : Finset (Fin k)}
    {u v : Fin n} {es : List (Fin k)} (h : Walk g active u v es)
    (p : Fin n → ℝ) :
    (es.map fun e => p (g.tail e) - p (g.head e)).sum = p u - p v := by
  induction h with
  | nil v => simp
  | cons e he h ih => simpa only [List.map_cons, List.sum_cons, ih] using
      (sub_add_sub_cancel (p (g.tail e)) (p (g.head e)) (p _))
end DecrAlmostLinearSSSP.Decremental
end s80
section s81
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
lemma Walk.append {n k : ℕ} {g : Digraph n k} {active : Finset (Fin k)}
    {u v w : Fin n} {es fs : List (Fin k)} (h : Walk g active u v es)
    (h' : Walk g active v w fs) : Walk g active u w (es ++ fs) := by
  induction h with
  | nil v => exact h'
  | cons e he h ih => exact .cons (u := g.tail e) e he (ih h')
lemma Walk.eq_of_empty {n k : ℕ} {g : Digraph n k} {active : Finset (Fin k)}
    {u v : Fin n} {es : List (Fin k)} (h : Walk g active u v es) (hnil : es = []) : u = v := by
  induction h with
  | nil v => rfl
  | cons e he h ih => cases hnil
lemma Reachable.trans {n k : ℕ} {g : Digraph n k} {active : Finset (Fin k)}
    {u v w : Fin n} (h : Reachable g active u v) (h' : Reachable g active v w) :
    Reachable g active u w := by
  obtain ⟨es, he⟩ := h
  obtain ⟨fs, hf⟩ := h'
  exact ⟨es ++ fs, he.append hf⟩
lemma mem_shortEdgeLists {n k : ℕ} (es : List (Fin k)) (hl : es.length < n) :
    es ∈ shortEdgeLists n k := by
  classical
  simp only [shortEdgeLists, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
  refine ⟨⟨es.length, hl⟩, (fun j : Fin es.length => es.get j), ?_⟩
  exact List.ofFn_get es
lemma exists_min_weight_walk {n k : ℕ} (g : Digraph n k) (active : Finset (Fin k))
    (w : Fin k → ℝ) (hw : ∀ e, 0 ≤ w e) (u v : Fin n) (hr : Reachable g active u v) :
    ∃ es, Walk g active u v es ∧ es.length < n ∧
      ∀ fs, Walk g active u v fs → (es.map w).sum ≤ (fs.map w).sum := by
  classical
  let S := (shortEdgeLists n k).filter (Walk g active u v)
  have hs : S.Nonempty := by
    obtain ⟨es, he, hl⟩ := hr.short_walk
    exact ⟨es, Finset.mem_filter.mpr ⟨mem_shortEdgeLists es hl, he⟩⟩
  obtain ⟨es, hes, hmin⟩ := Finset.exists_min_image S (fun es => (es.map w).sum) hs
  have he : Walk g active u v es := (Finset.mem_filter.mp hes).2
  obtain ⟨gs, hg, hsub, hn⟩ := he.erase_cycles
  have hlen : gs.length < n := by
    have hh := hn.length_le_card
    simpa only [List.length_cons, List.length_map, Fintype.card_fin, Nat.succ_le_iff] using hh
  refine ⟨gs, hg, hlen, ?_⟩
  intro fs hf
  obtain ⟨ts, ht, hsubt, hnodup⟩ := hf.erase_cycles
  have hlt : ts.length < n := by
    have hh := hnodup.length_le_card
    simpa only [List.length_cons, List.length_map, Fintype.card_fin, Nat.succ_le_iff] using hh
  have hts : ts ∈ S := Finset.mem_filter.mpr ⟨mem_shortEdgeLists ts hlt, ht⟩
  have hgs : (gs.map w).sum ≤ (es.map w).sum :=
    List.Sublist.sum_le_sum (hsub.map w) (by intro x hx; obtain ⟨e, _, rfl⟩ := List.mem_map.mp hx; exact hw e)
  have hfs : (ts.map w).sum ≤ (fs.map w).sum :=
    List.Sublist.sum_le_sum (hsubt.map w) (by intro x hx; obtain ⟨e, _, rfl⟩ := List.mem_map.mp hx; exact hw e)
  exact hgs.trans ((hmin ts hts).trans hfs)
lemma list_sum_ofReal {k : ℕ} (w : Fin k → ℝ) (hw : ∀ e, 0 ≤ w e) (es : List (Fin k)) :
    (es.map (fun e => ENNReal.ofReal (w e))).sum = ENNReal.ofReal ((es.map w).sum) := by
  induction es with
  | nil => simp
  | cons e es ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    rw [ENNReal.ofReal_add (hw e) (List.sum_nonneg (by intro x hx; obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx; exact hw a))]
lemma distance_le_walk {n k : ℕ} {g : Digraph n k} {active : Finset (Fin k)}
    {u v : Fin n} {es : List (Fin k)} (h : Walk g active u v es) (w : Fin k → ℝ≥0∞) :
    distance g active w u v ≤ (es.map w).sum :=
  iInf_le_of_le es (iInf_le_of_le h le_rfl)
lemma distance_min_weight {n k : ℕ} (g : Digraph n k) (active : Finset (Fin k))
    (w : Fin k → ℝ) (hw : ∀ e, 0 ≤ w e) (u v : Fin n) (hr : Reachable g active u v) :
    ∃ es, Walk g active u v es ∧ es.length < n ∧
      distance g active (fun e => ENNReal.ofReal (w e)) u v = ENNReal.ofReal ((es.map w).sum) := by
  obtain ⟨es, he, hl, hmin⟩ := exists_min_weight_walk g active w hw u v hr
  refine ⟨es, he, hl, le_antisymm ?_ ?_⟩
  · simpa only [list_sum_ofReal w hw] using distance_le_walk he (fun e => ENNReal.ofReal (w e))
  · apply le_iInf
    intro fs
    apply le_iInf
    intro hf
    rw [list_sum_ofReal w hw]
    exact ENNReal.ofReal_le_ofReal (hmin fs hf)
end DecrAlmostLinearSSSP.Decremental
end s81
section s82
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
lemma scaleOriginal_cut (i : Input) (j : ℕ) (e : Fin (roundedInput i j).k) :
    (i.weight (scaleOriginal i j e) : ℝ) ≤ 2 * scale j :=
  ((Fintype.equivFin (ScaleEdge i j)).symm e).property
lemma scaleOriginal_tail (i : Input) (j : ℕ) (e : Fin (roundedInput i j).k) :
    (roundedInput i j).graph.tail e = i.graph.tail (scaleOriginal i j e) := rfl
lemma scaleOriginal_head (i : Input) (j : ℕ) (e : Fin (roundedInput i j).k) :
    (roundedInput i j).graph.head e = i.graph.head (scaleOriginal i j e) := rfl
lemma rounded_walk_project (i : Input) (j : ℕ) (active : Finset (Fin i.k))
    {u v : Fin i.n} {es : List (Fin (roundedInput i j).k)}
    (h : Walk (roundedInput i j).graph (scaleActive i j active) u v es) :
    Walk i.graph active u v (es.map (scaleOriginal i j)) := by
  induction h with
  | nil v => exact .nil v
  | @cons u v es e he h ih =>
    have hea : scaleOriginal i j e ∈ active := (Finset.mem_filter.mp he).2
    exact .cons (u := i.graph.tail (scaleOriginal i j e)) (scaleOriginal i j e) hea ih
lemma rounded_walk_lift (i : Input) (j : ℕ) (active : Finset (Fin i.k))
    {u v : Fin i.n} {es : List (Fin i.k)} (h : Walk i.graph active u v es)
    (hcut : ∀ e ∈ es, (i.weight e : ℝ) ≤ 2 * scale j) :
    ∃ rs, Walk (roundedInput i j).graph (scaleActive i j active) u v rs ∧
      rs.map (scaleOriginal i j) = es := by
  classical
  induction h with
  | nil v => exact ⟨[], .nil v, rfl⟩
  | @cons u v es e he h ih =>
    obtain ⟨rs, hrs, hrmap⟩ := ih (fun f hf => hcut f (List.mem_cons_of_mem e hf))
    let r : Fin (roundedInput i j).k := (Fintype.equivFin (ScaleEdge i j)) ⟨e, hcut e (List.mem_cons_self)⟩
    have hre : scaleOriginal i j r = e := by
      exact congrArg Subtype.val ((Fintype.equivFin (ScaleEdge i j)).symm_apply_apply ⟨e, hcut e List.mem_cons_self⟩)
    have hra : r ∈ scaleActive i j active := by simp [scaleActive, hre, he]
    have hrhead : (roundedInput i j).graph.head r = i.graph.head e := by rw [scaleOriginal_head, hre]
    have hrtail : (roundedInput i j).graph.tail r = i.graph.tail e := by rw [scaleOriginal_tail, hre]
    refine ⟨r :: rs, ?_, ?_⟩
    · rw [← hrtail]
      apply Walk.cons (u := (roundedInput i j).graph.tail r) r hra
      rwa [hrhead]
    · simp only [List.map_cons, hre, hrmap]
lemma rounded_edge_cost (i : Input) (hi : i.Valid) (j : ℕ) (e : Fin (roundedInput i j).k) :
    (i.weight (scaleOriginal i j e) : ℝ) ≤ delta i j * (roundedInput i j).weight e ∧
      delta i j * (roundedInput i j).weight e ≤ (i.weight (scaleOriginal i j e) : ℝ) + delta i j := by
  have hd := delta_positive i hi j
  have hw : (0 : ℝ) ≤ i.weight (scaleOriginal i j e) := Nat.cast_nonneg _
  change (i.weight (scaleOriginal i j e) : ℝ) ≤ delta i j * (⌈(i.weight (scaleOriginal i j e) : ℝ) / delta i j⌉₊ : ℝ) ∧
    delta i j * (⌈(i.weight (scaleOriginal i j e) : ℝ) / delta i j⌉₊ : ℝ) ≤ (i.weight (scaleOriginal i j e) : ℝ) + delta i j
  constructor
  · exact (div_le_iff₀ hd).mp (Nat.le_ceil _ ) |>.trans_eq (mul_comm _ _)
  · have hc := Nat.ceil_lt_add_one (div_nonneg hw hd.le)
    have hh := mul_lt_mul_of_pos_left hc hd
    have hid : delta i j * ((i.weight (scaleOriginal i j e) : ℝ) / delta i j + 1) =
        (i.weight (scaleOriginal i j e) : ℝ) + delta i j := by field_simp
    exact (hh.trans_eq hid).le
lemma rounded_walk_cost (i : Input) (hi : i.Valid) (j : ℕ)
    (rs : List (Fin (roundedInput i j).k)) :
    ((rs.map (fun e => (i.weight (scaleOriginal i j e) : ℝ))).sum ≤
      delta i j * (rs.map (fun e => ((roundedInput i j).weight e : ℝ))).sum) ∧
    delta i j * (rs.map (fun e => ((roundedInput i j).weight e : ℝ))).sum ≤
      (rs.map (fun e => (i.weight (scaleOriginal i j e) : ℝ))).sum + rs.length * delta i j := by
  induction rs with
  | nil => simp
  | cons e rs ih =>
    have he := rounded_edge_cost i hi j e
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    constructor <;> nlinarith only [he.1, he.2, ih.1, ih.2]
end DecrAlmostLinearSSSP.Decremental
end s82
section s83
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
lemma nat_weight_list_real {k : ℕ} (w : Fin k → ℕ) (es : List (Fin k)) :
    (es.map (fun e => (w e : ℝ≥0∞))).sum = ENNReal.ofReal ((es.map (fun e => (w e : ℝ))).sum) := by
  simpa only [ENNReal.ofReal_natCast] using
    list_sum_ofReal (fun e => (w e : ℝ)) (fun e => Nat.cast_nonneg _) es
lemma rounded_distance_lower (i : Input) (hi : i.Valid) (j : ℕ)
    (active : Finset (Fin i.k)) (u v : Fin i.n) :
    distance i.graph active (fun e => (i.weight e : ℝ≥0∞)) u v ≤
      ENNReal.ofReal (delta i j) * distance (roundedInput i j).graph (scaleActive i j active)
        (fun e => ((roundedInput i j).weight e : ℝ≥0∞)) u v := by
  have hd := delta_positive i hi j
  have hd0 : ENNReal.ofReal (delta i j) ≠ 0 := (ENNReal.ofReal_pos.mpr hd).ne'
  conv_rhs => unfold distance
  rw [ENNReal.mul_iInf_of_ne hd0 ENNReal.ofReal_ne_top]
  apply le_iInf
  intro rs
  rw [ENNReal.mul_iInf_of_ne hd0 ENNReal.ofReal_ne_top]
  apply le_iInf
  intro hrs
  have hp := rounded_walk_project i j active hrs
  have hh := distance_le_walk hp (fun e => (i.weight e : ℝ≥0∞))
  rw [nat_weight_list_real, List.map_map] at hh
  apply hh.trans
  rw [nat_weight_list_real, ← ENNReal.ofReal_mul hd.le]
  apply ENNReal.ofReal_le_ofReal
  exact (rounded_walk_cost i hi j rs).1
lemma rounded_distance_upper_of_walk (i : Input) (hi : i.Valid) (j : ℕ)
    (active : Finset (Fin i.k)) {u v : Fin i.n} {es : List (Fin i.k)}
    (hwalk : Walk i.graph active u v es)
    (hcut : ∀ e ∈ es, (i.weight e : ℝ) ≤ 2 * scale j) :
    ENNReal.ofReal (delta i j) * distance (roundedInput i j).graph (scaleActive i j active)
      (fun e => ((roundedInput i j).weight e : ℝ≥0∞)) u v ≤
      ENNReal.ofReal ((es.map (fun e => (i.weight e : ℝ))).sum + es.length * delta i j) := by
  obtain ⟨rs, hrs, hmap⟩ := rounded_walk_lift i j active hwalk hcut
  have hh := mul_le_mul_right (distance_le_walk hrs
    (fun e => ((roundedInput i j).weight e : ℝ≥0∞))) (ENNReal.ofReal (delta i j))
  apply hh.trans
  have hd := delta_positive i hi j
  rw [nat_weight_list_real, ← ENNReal.ofReal_mul hd.le]
  apply ENNReal.ofReal_le_ofReal
  have hc := (rounded_walk_cost i hi j rs).2
  rw [← hmap, List.map_map, List.length_map]
  exact hc
lemma real_weight_le_walk_sum {k : ℕ} (w : Fin k → ℕ) (es : List (Fin k))
    (e : Fin k) (he : e ∈ es) : (w e : ℝ) ≤ (es.map (fun e => (w e : ℝ))).sum := by
  induction es with
  | nil => simp at he
  | cons f es ih =>
    simp only [List.mem_cons] at he
    simp only [List.map_cons, List.sum_cons]
    rcases he with rfl | he
    · have hnon : (0 : ℝ) ≤ (es.map (fun e => (w e : ℝ))).sum := List.sum_nonneg (by
        intro a ha
        obtain ⟨g, _, rfl⟩ := List.mem_map.mp ha
        exact Nat.cast_nonneg _)
      linarith
    · exact (ih he).trans (le_add_of_nonneg_left (Nat.cast_nonneg _))
lemma rounded_shortest_upper (i : Input) (hi : i.Valid) (j : ℕ)
    (active : Finset (Fin i.k)) (u v : Fin i.n)
    (hr : Reachable i.graph active u v)
    (hbound : distance i.graph active (fun e => (i.weight e : ℝ≥0∞)) u v ≤ ENNReal.ofReal (2 * scale j)) :
    ∃ d : ℝ, 0 ≤ d ∧ distance i.graph active (fun e => (i.weight e : ℝ≥0∞)) u v = ENNReal.ofReal d ∧
      ENNReal.ofReal (delta i j) * distance (roundedInput i j).graph (scaleActive i j active)
        (fun e => ((roundedInput i j).weight e : ℝ≥0∞)) u v ≤
        ENNReal.ofReal (d + i.n * delta i j) := by
  obtain ⟨es, hes, hlen, hdist⟩ := distance_min_weight i.graph active (fun e => (i.weight e : ℝ))
    (fun e => Nat.cast_nonneg _) u v hr
  have hdist' : distance i.graph active (fun e => (i.weight e : ℝ≥0∞)) u v =
      ENNReal.ofReal ((es.map (fun e => (i.weight e : ℝ))).sum) := by
    simpa only [ENNReal.ofReal_natCast] using hdist
  let d := (es.map (fun e => (i.weight e : ℝ))).sum
  have hd : 0 ≤ d := List.sum_nonneg (by
    intro a ha
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp ha
    exact Nat.cast_nonneg _)
  have hscale := scale_positive j
  have hdb : d ≤ 2 * scale j := by
    rw [hdist'] at hbound
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ 2 * scale j)).mp hbound
  have hcut : ∀ e ∈ es, (i.weight e : ℝ) ≤ 2 * scale j :=
    fun e he => (real_weight_le_walk_sum i.weight es e he).trans hdb
  have hup := rounded_distance_upper_of_walk i hi j active hes hcut
  refine ⟨d, hd, hdist', hup.trans ?_⟩
  apply ENNReal.ofReal_le_ofReal
  have hlen' : (es.length : ℝ) ≤ i.n := by exact_mod_cast hlen.le
  simpa only [add_comm] using add_le_add_left (mul_le_mul_of_nonneg_right hlen' (delta_positive i hi j).le) d
end DecrAlmostLinearSSSP.Decremental
end s83
section s84
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
lemma distance_top_of_unreachable {n k : ℕ} (g : Digraph n k) (active : Finset (Fin k))
    (w : Fin k → ℝ≥0∞) (u v : Fin n) (hr : ¬ Reachable g active u v) :
    distance g active w u v = ⊤ := by
  apply top_unique
  apply le_iInf
  intro es
  apply le_iInf
  intro hes
  exact False.elim (hr ⟨es,hes⟩)
lemma list_real_weight_upper {k : ℕ} (w : Fin k → ℕ) (W : ℕ)
    (hw : ∀ e, w e ≤ W) (es : List (Fin k)) :
    (es.map (fun e => (w e : ℝ))).sum ≤ es.length * (W : ℝ) := by
  induction es with
  | nil => simp
  | cons e es ih =>
    have he : (w e : ℝ) ≤ W := by exact_mod_cast hw e
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    nlinarith only [he, ih]
lemma input_reachable_distance_bounds (i : Input) (hi : i.Valid) (active : Finset (Fin i.k))
    (v : Fin i.n) (hr : Reachable i.graph active i.source v) (hv : v ≠ i.source) :
    ∃ d : ℝ, 1 ≤ d ∧ d ≤ (i.n : ℝ) * i.W ∧
      distance i.graph active (fun e => (i.weight e : ℝ≥0∞)) i.source v = ENNReal.ofReal d := by
  obtain ⟨es, hes, hlen, hdist⟩ := distance_min_weight i.graph active (fun e => (i.weight e : ℝ))
    (fun e => Nat.cast_nonneg _) i.source v hr
  let d := (es.map (fun e => (i.weight e : ℝ))).sum
  have hdlo : 1 ≤ d := by
    cases heq : es with
    | nil =>
      have he : i.source = v := hes.eq_of_empty heq
      exact False.elim (hv he.symm)
    | cons e rest =>
      have he : (1 : ℝ) ≤ i.weight e := by exact_mod_cast (hi.2.2.2.2.2 e).1
      have hsum := real_weight_le_walk_sum i.weight es e (by rw [heq]; exact List.mem_cons_self)
      exact he.trans hsum
  have hdhi : d ≤ (i.n : ℝ) * i.W := by
    have hh := list_real_weight_upper i.weight i.W (fun e => (hi.2.2.2.2.2 e).2) es
    have hl : (es.length : ℝ) ≤ i.n := by exact_mod_cast hlen.le
    exact hh.trans (mul_le_mul_of_nonneg_right hl (Nat.cast_nonneg _))
  refine ⟨d, hdlo, hdhi, ?_⟩
  simpa only [ENNReal.ofReal_natCast] using hdist
end DecrAlmostLinearSSSP.Decremental
end s84
section s85
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
lemma cappedDistance_bounds {n k : ℕ} (g : Digraph n k) (active : Finset (Fin k))
    (w : Fin k → ℝ) (B : ℝ) (hB : 0 ≤ B) (u v : Fin n) :
    0 ≤ cappedDistance g active w B u v ∧ cappedDistance g active w B u v ≤ B := by
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (min_le_left (ENNReal.ofReal B) (distance g active (fun e => ENNReal.ofReal (w e)) u v))
  simpa only [cappedDistance, ENNReal.toReal_ofReal hB] using hh
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
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s140
section s141
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental.Exact
end s141
section s142
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
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
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s144
section s145
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s145
section s146
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s146
section s147
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s147
section s148
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s148
section s149
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.InputCapture
open Structured
end DecrAlmostLinearSSSP.Decremental.InputCapture
end s149
section s150
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s150
section s151
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s151
section s152
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.InputCapture
open Structured
end DecrAlmostLinearSSSP.Decremental.InputCapture
end s152
section s153
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s153
section s154
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s154
section s155
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s155
section s156
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s156
section s157
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s157
section s158
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s158
section s159
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s159
section s160
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s160
section s161
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s161
section s162
set_option autoImplicit false
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
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s166
section s167
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s167
section s168
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s168
open DecrAlmostLinearSSSP.Decremental
set_option autoImplicit false
theorem solution : (((((((∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
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
              g)) ∧ (∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
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
              (DecrAlmostLinearSSSP.Decremental.Instruction.storeN a d) g))) ∧ ((∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) base →
      @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) F →
        ∀ (a : Nat),
          have c1 :=
            DecrAlmostLinearSSSP.Decremental.instructionEffect
              (DecrAlmostLinearSSSP.Decremental.Instruction.nadd
                (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                (DecrAlmostLinearSSSP.Decremental.shadowReg a) (DecrAlmostLinearSSSP.Decremental.shadowReg a))
              c;
          have c2 :=
            DecrAlmostLinearSSSP.Decremental.instructionEffect
              (DecrAlmostLinearSSSP.Decremental.Instruction.nadd
                (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              c1;
          have c3 :=
            DecrAlmostLinearSSSP.Decremental.instructionEffect
              (DecrAlmostLinearSSSP.Decremental.Instruction.nadd
                (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
              c2;
          And (DecrAlmostLinearSSSP.Decremental.ShadowRep base F c3 g)
            (@Eq.{1} Nat (c3.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (g.natReg a))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))) ∧ (∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    ∀ (pc work : Nat),
      DecrAlmostLinearSSSP.Decremental.ShadowRep base F
        { pc := c.pc, realReg := c.realReg,
          natReg :=
            @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
              (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat c.natReg
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) pc)
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) work,
          realMem := c.realMem, natMem := c.natMem, halted := c.halted, fault := c.fault, work := c.work }
        { pc := pc, realReg := g.realReg, natReg := g.natReg, realMem := g.realMem, natMem := g.natMem,
          halted := g.halted, fault := g.fault, work := work }))) ∧ (((∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    ∀ (pc : Nat),
      DecrAlmostLinearSSSP.Decremental.ShadowRep base F
        { pc := c.pc, realReg := c.realReg,
          natReg :=
            @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat c.natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) pc,
          realMem := c.realMem, natMem := c.natMem, halted := c.halted, fault := c.fault, work := c.work }
        { pc := pc, realReg := g.realReg, natReg := g.natReg, realMem := g.realMem, natMem := g.natMem,
          halted := g.halted, fault := g.fault, work := g.work }) ∧ (∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    DecrAlmostLinearSSSP.Decremental.ShadowRep base F
      { pc := c.pc, realReg := c.realReg,
        natReg :=
          @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat c.natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))),
        realMem := c.realMem, natMem := c.natMem, halted := c.halted, fault := c.fault, work := c.work }
      { pc := g.pc, realReg := g.realReg, natReg := g.natReg, realMem := g.realMem, natMem := g.natMem,
        halted := Bool.true, fault := g.fault, work := g.work })) ∧ ((∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) F →
      ∀ (a b : Nat),
        Iff
          (@LT.lt.{0} Nat instLTNat (c.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg a))
            (c.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg b)))
          (@LT.lt.{0} Nat instLTNat (g.natReg a) (g.natReg b))) ∧ ((∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    ∀ (a b : Nat),
      Iff
        (@LT.lt.{0} Real Real.instLT (c.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg a))
          (c.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg b)))
        (@LT.lt.{0} Real Real.instLT (g.realReg a) (g.realReg b))) ∧ (∀ {B F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep B F c g →
    DecrAlmostLinearSSSP.Decremental.ShadowRep B F (DecrAlmostLinearSSSP.Decremental.Structured.data c).machine g))))) ∧ ((((∀ {B F : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine}
  (a : DecrAlmostLinearSSSP.Decremental.Structured.Atom),
  DecrAlmostLinearSSSP.Decremental.ShadowRep B F
      (DecrAlmostLinearSSSP.Decremental.instructionEffect a.instruction s.machine) g →
    DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F (a.effect s) g) ∧ (∀ {B F : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
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
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) })) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (pc : Nat),
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
      realMem := s.realMem, natMem := s.natMem }) ∧ (∀ {B F : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F s g →
    ∀ (ins tr : DecrAlmostLinearSSSP.Decremental.Instruction),
      @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (DecrAlmostLinearSSSP.Decremental.shadowScalarTranslation ins)
          (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction tr) →
        ∃ a,
          And (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Instruction a.instruction tr)
            (And
              (DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.Cmd.atom a)
                s (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (a.effect s))
              (DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F (a.effect s)
                (DecrAlmostLinearSSSP.Decremental.instructionEffect ins g)))))) ∧ (((∀ {B F : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
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
                  (DecrAlmostLinearSSSP.Decremental.Instruction.cast d a) g))) ∧ (∀ {B F : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
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
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (d factor q : Nat),
  @Ne.{1} Nat factor d →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.repeatedAdd d factor q) s q
      { realReg := s.realReg,
        natReg :=
          @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natReg d
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (s.natReg d)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) q (s.natReg factor))),
        realMem := s.realMem, natMem := s.natMem }) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (d factor q : Nat),
  @Ne.{1} Nat factor d →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.structuredConstant d factor q) s
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) q
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      { realReg := s.realReg,
        natReg :=
          @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natReg d
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) q (s.natReg factor)),
        realMem := s.realMem, natMem := s.natMem }) ∧ (∀ {B F : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
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
                (DecrAlmostLinearSSSP.Decremental.Instruction.natural d q) g)))))))) ∧ (((((∀ (d factor q k : Nat),
  @Ne.{1} Nat d k →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.repeatedAdd d factor q) k) ∧ (∀ (d factor q k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.repeatedAdd d factor q) k)) ∧ ((∀ {B F : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F s g →
    ∀ (address value : Nat),
      (∀ (a : Nat),
          @Ne.{1} Nat address
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) →
        DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F
          { realReg := s.realReg, natReg := s.natReg, realMem := s.realMem,
            natMem := @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natMem address value }
          g) ∧ (∀ {B F : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F s g →
    ∀ (k value : Nat),
      @Ne.{1} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k →
        @Ne.{1} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) k →
          @Ne.{1} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) k →
            @Ne.{1} Nat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) k →
              (∀ (j : Nat), @Ne.{1} Nat (DecrAlmostLinearSSSP.Decremental.shadowReg j) k) →
                DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F
                  { realReg := s.realReg,
                    natReg := @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natReg k value,
                    realMem := s.realMem, natMem := s.natMem }
                  g))) ∧ (((∀ (j k : Nat),
  @Ne.{1} Nat (DecrAlmostLinearSSSP.Decremental.shadowReg j)
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k)) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
      DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.appendStoreReport s
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
        (DecrAlmostLinearSSSP.Decremental.appendedReport s))) ∧ ((∀ {B F : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F s g →
    (∀ (a : Nat),
        @Ne.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) →
      DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F (DecrAlmostLinearSSSP.Decremental.appendedReport s) g) ∧ ((∀ (start : Nat) (reports : List.{0} Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.ReportLog start reports s →
    DecrAlmostLinearSSSP.Decremental.ReportLog start
      (@HAppend.hAppend.{0, 0, 0} (List.{0} Nat) (List.{0} Nat) (List.{0} Nat)
        (@instHAppendOfAppend.{0} (List.{0} Nat) (@List.instAppend.{0} Nat)) reports
        (@List.cons.{0} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
          (@List.nil.{0} Nat)))
      (DecrAlmostLinearSSSP.Decremental.appendedReport s)) ∧ (∀ (B bank start : Nat) (reports : List.{0} Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
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
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))))) ∧ ((((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.InputCapture.code s
    (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19)))
    (DecrAlmostLinearSSSP.Decremental.InputCapture.result s)) ∧ (DecrAlmostLinearSSSP.Decremental.Structured.NoMemory DecrAlmostLinearSSSP.Decremental.InputCapture.code)) ∧ ((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (i : DecrAlmostLinearSSSP.Decremental.Input),
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i
    (DecrAlmostLinearSSSP.Decremental.InputCapture.result
      (DecrAlmostLinearSSSP.Decremental.Structured.data (DecrAlmostLinearSSSP.Decremental.initialMachine p i)))) ∧ ((∀ (j : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.InputCapture.code
    (DecrAlmostLinearSSSP.Decremental.shadowReg j)) ∧ (∀ (j : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.InputCapture.code
    (DecrAlmostLinearSSSP.Decremental.shadowReg j))))) ∧ (((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (i : DecrAlmostLinearSSSP.Decremental.Input) (j : Nat),
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
      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (e : Fin i.k) (offset : Nat),
  @LT.lt.{0} Nat instLTNat offset (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
    @LT.lt.{0} Nat instLTNat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (@Fin.val i.k e)))
        offset)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.Powers.prepare s
    (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))
    (DecrAlmostLinearSSSP.Decremental.Exact.Powers.prepared s)) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (base : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i s →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 234) (instOfNatNat (nat_lit 234)))) base →
      DecrAlmostLinearSSSP.Decremental.Exact.Powers.Prefix
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) i.n i.W) base
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (DecrAlmostLinearSSSP.Decremental.Exact.Powers.prepared s)) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (base : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
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
                  @Eq.{1} Nat (t.natMem address) (s.natMem address))))))))))) ∧ ((((((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 248) (instOfNatNat (nat_lit 248))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 250) (instOfNatNat (nat_lit 250))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 252) (instOfNatNat (nat_lit 252))) →
        DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.Powers.code k) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.Layout.code s
    (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
    (DecrAlmostLinearSSSP.Decremental.Exact.Layout.result s))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i s →
    DecrAlmostLinearSSSP.Decremental.Exact.Layout.Image
      (DecrAlmostLinearSSSP.Decremental.Exact.Layout.addresses
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        i.n i.k)
      (DecrAlmostLinearSSSP.Decremental.Exact.Layout.result s)) ∧ (DecrAlmostLinearSSSP.Decremental.Structured.NoMemory DecrAlmostLinearSSSP.Decremental.Exact.Layout.code))) ∧ (((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 224) (instOfNatNat (nat_lit 224))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 226) (instOfNatNat (nat_lit 226))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 228) (instOfNatNat (nat_lit 228))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 230) (instOfNatNat (nat_lit 230))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 232) (instOfNatNat (nat_lit 232))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 234) (instOfNatNat (nat_lit 234))) →
              DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.Layout.code k) ∧ (∀ (k : Nat), DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Exact.Layout.code k)) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.Clear.body s
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    (DecrAlmostLinearSSSP.Decremental.Exact.Clear.advanced s)) ∧ ((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 290) (instOfNatNat (nat_lit 290))) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.Clear.code k) ∧ (∀ (k : Nat), DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Exact.Clear.code k))))) ∧ ((((∀ (base length : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
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
                        @Eq.{1} Nat (t.natMem a) (s.natMem a)))))) ∧ (∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {u v w : Fin n}
  {es : List.{0} (Fin k)},
  @DecrAlmostLinearSSSP.Decremental.Walk n k g active u v es →
    @Membership.mem.{0, 0} (Fin n) (List.{0} (Fin n)) (@List.instMembership.{0} (Fin n))
        (@List.cons.{0} (Fin n) u
          (@List.map.{0, 0} (Fin k) (Fin n) (@DecrAlmostLinearSSSP.Decremental.Digraph.head n k g) es))
        w →
      ∃ fs,
        And (@DecrAlmostLinearSSSP.Decremental.Walk n k g active w v fs)
          (And (@List.IsSuffix.{0} (Fin k) fs es)
            (@List.IsSuffix.{0} (Fin n)
              (@List.cons.{0} (Fin n) w
                (@List.map.{0, 0} (Fin k) (Fin n) (@DecrAlmostLinearSSSP.Decremental.Digraph.head n k g) fs))
              (@List.cons.{0} (Fin n) u
                (@List.map.{0, 0} (Fin k) (Fin n) (@DecrAlmostLinearSSSP.Decremental.Digraph.head n k g) es)))))) ∧ ((∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {u v : Fin n}
  {es : List.{0} (Fin k)},
  @DecrAlmostLinearSSSP.Decremental.Walk n k g active u v es →
    ∃ fs,
      And (@DecrAlmostLinearSSSP.Decremental.Walk n k g active u v fs)
        (And (@List.Sublist.{0} (Fin k) fs es)
          (@List.Nodup.{0} (Fin n)
            (@List.cons.{0} (Fin n) u
              (@List.map.{0, 0} (Fin k) (Fin n) (@DecrAlmostLinearSSSP.Decremental.Digraph.head n k g) fs))))) ∧ ((∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {u v : Fin n},
  @DecrAlmostLinearSSSP.Decremental.Reachable n k g active u v →
    ∃ es,
      And (@DecrAlmostLinearSSSP.Decremental.Walk n k g active u v es)
        (@LT.lt.{0} Nat instLTNat (@List.length.{0} (Fin k) es) n)) ∧ (∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {u v : Fin n}
  {es : List.{0} (Fin k)},
  @DecrAlmostLinearSSSP.Decremental.Walk n k g active u v es →
    ∀ (p : Fin n → Real),
      @Eq.{1} Real
        (@List.sum.{0} Real Real.instAdd Real.instZero
          (@List.map.{0, 0} (Fin k) Real
            (fun e =>
              @HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                (p (@DecrAlmostLinearSSSP.Decremental.Digraph.tail n k g e))
                (p (@DecrAlmostLinearSSSP.Decremental.Digraph.head n k g e)))
            es))
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (p u) (p v)))))) ∧ (((∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {u v w : Fin n}
  {es fs : List.{0} (Fin k)},
  @DecrAlmostLinearSSSP.Decremental.Walk n k g active u v es →
    @DecrAlmostLinearSSSP.Decremental.Walk n k g active v w fs →
      @DecrAlmostLinearSSSP.Decremental.Walk n k g active u w
        (@HAppend.hAppend.{0, 0, 0} (List.{0} (Fin k)) (List.{0} (Fin k)) (List.{0} (Fin k))
          (@instHAppendOfAppend.{0} (List.{0} (Fin k)) (@List.instAppend.{0} (Fin k))) es fs)) ∧ (∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {u v : Fin n}
  {es : List.{0} (Fin k)},
  @DecrAlmostLinearSSSP.Decremental.Walk n k g active u v es →
    @Eq.{1} (List.{0} (Fin k)) es (@List.nil.{0} (Fin k)) → @Eq.{1} (Fin n) u v)) ∧ ((∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {u v w : Fin n},
  @DecrAlmostLinearSSSP.Decremental.Reachable n k g active u v →
    @DecrAlmostLinearSSSP.Decremental.Reachable n k g active v w →
      @DecrAlmostLinearSSSP.Decremental.Reachable n k g active u w) ∧ ((∀ {n k : Nat} (es : List.{0} (Fin k)),
  @LT.lt.{0} Nat instLTNat (@List.length.{0} (Fin k) es) n →
    @Membership.mem.{0, 0} (List.{0} (Fin k)) (Finset.{0} (List.{0} (Fin k)))
      (@SetLike.instMembership.{0, 0} (Finset.{0} (List.{0} (Fin k))) (List.{0} (Fin k))
        (@Finset.instSetLike.{0} (List.{0} (Fin k))))
      (DecrAlmostLinearSSSP.Decremental.shortEdgeLists n k) es) ∧ (∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (active : Finset.{0} (Fin k)) (w : Fin k → Real),
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
                    (@List.sum.{0} Real Real.instAdd Real.instZero (@List.map.{0, 0} (Fin k) Real w fs)))))))))) ∧ (((((∀ {k : Nat} (w : Fin k → Real),
  (∀ (e : Fin k),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (w e)) →
    ∀ (es : List.{0} (Fin k)),
      @Eq.{1} ENNReal
        (@List.sum.{0} ENNReal ENNReal.instAdd ENNReal.instZero
          (@List.map.{0, 0} (Fin k) ENNReal (fun e => ENNReal.ofReal (w e)) es))
        (ENNReal.ofReal (@List.sum.{0} Real Real.instAdd Real.instZero (@List.map.{0, 0} (Fin k) Real w es)))) ∧ (∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {u v : Fin n}
  {es : List.{0} (Fin k)},
  @DecrAlmostLinearSSSP.Decremental.Walk n k g active u v es →
    ∀ (w : Fin k → ENNReal),
      @LE.le.{0} ENNReal ENNReal.instLE (@DecrAlmostLinearSSSP.Decremental.distance n k g active w u v)
        (@List.sum.{0} ENNReal ENNReal.instAdd ENNReal.instZero (@List.map.{0, 0} (Fin k) ENNReal w es)))) ∧ ((∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (active : Finset.{0} (Fin k)) (w : Fin k → Real),
  (∀ (e : Fin k),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (w e)) →
    ∀ (u v : Fin n),
      @DecrAlmostLinearSSSP.Decremental.Reachable n k g active u v →
        ∃ es,
          And (@DecrAlmostLinearSSSP.Decremental.Walk n k g active u v es)
            (And (@LT.lt.{0} Nat instLTNat (@List.length.{0} (Fin k) es) n)
              (@Eq.{1} ENNReal
                (@DecrAlmostLinearSSSP.Decremental.distance n k g active (fun e => ENNReal.ofReal (w e)) u v)
                (ENNReal.ofReal (@List.sum.{0} Real Real.instAdd Real.instZero (@List.map.{0, 0} (Fin k) Real w es)))))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (j : Nat)
  (e : Fin (DecrAlmostLinearSSSP.Decremental.roundedInput i j).k),
  @LE.le.{0} Real Real.instLE
    (@Nat.cast.{0} Real Real.instNatCast (i.weight (DecrAlmostLinearSSSP.Decremental.scaleOriginal i j e)))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real (nat_lit 2)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
      (DecrAlmostLinearSSSP.Decremental.scale j))))) ∧ (((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (j : Nat)
  (e : Fin (DecrAlmostLinearSSSP.Decremental.roundedInput i j).k),
  @Eq.{1} (Fin (DecrAlmostLinearSSSP.Decremental.roundedInput i j).n)
    (@DecrAlmostLinearSSSP.Decremental.Digraph.tail (DecrAlmostLinearSSSP.Decremental.roundedInput i j).n
      (DecrAlmostLinearSSSP.Decremental.roundedInput i j).k (DecrAlmostLinearSSSP.Decremental.roundedInput i j).graph e)
    (@DecrAlmostLinearSSSP.Decremental.Digraph.tail i.n i.k i.graph
      (DecrAlmostLinearSSSP.Decremental.scaleOriginal i j e))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (j : Nat)
  (e : Fin (DecrAlmostLinearSSSP.Decremental.roundedInput i j).k),
  @Eq.{1} (Fin (DecrAlmostLinearSSSP.Decremental.roundedInput i j).n)
    (@DecrAlmostLinearSSSP.Decremental.Digraph.head (DecrAlmostLinearSSSP.Decremental.roundedInput i j).n
      (DecrAlmostLinearSSSP.Decremental.roundedInput i j).k (DecrAlmostLinearSSSP.Decremental.roundedInput i j).graph e)
    (@DecrAlmostLinearSSSP.Decremental.Digraph.head i.n i.k i.graph
      (DecrAlmostLinearSSSP.Decremental.scaleOriginal i j e)))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (j : Nat) (active : Finset.{0} (Fin i.k)) {u v : Fin i.n}
  {es : List.{0} (Fin (DecrAlmostLinearSSSP.Decremental.roundedInput i j).k)},
  @DecrAlmostLinearSSSP.Decremental.Walk (DecrAlmostLinearSSSP.Decremental.roundedInput i j).n
      (DecrAlmostLinearSSSP.Decremental.roundedInput i j).k (DecrAlmostLinearSSSP.Decremental.roundedInput i j).graph
      (DecrAlmostLinearSSSP.Decremental.scaleActive i j active) u v es →
    @DecrAlmostLinearSSSP.Decremental.Walk i.n i.k i.graph active u v
      (@List.map.{0, 0} (Fin (DecrAlmostLinearSSSP.Decremental.roundedInput i j).k) (Fin i.k)
        (DecrAlmostLinearSSSP.Decremental.scaleOriginal i j) es)) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (j : Nat) (active : Finset.{0} (Fin i.k)) {u v : Fin i.n}
  {es : List.{0} (Fin i.k)},
  @DecrAlmostLinearSSSP.Decremental.Walk i.n i.k i.graph active u v es →
    (∀ (e : Fin i.k),
        @Membership.mem.{0, 0} (Fin i.k) (List.{0} (Fin i.k)) (@List.instMembership.{0} (Fin i.k)) es e →
          @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast (i.weight e))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              (DecrAlmostLinearSSSP.Decremental.scale j))) →
      ∃ rs,
        And
          (@DecrAlmostLinearSSSP.Decremental.Walk (DecrAlmostLinearSSSP.Decremental.roundedInput i j).n
            (DecrAlmostLinearSSSP.Decremental.roundedInput i j).k
            (DecrAlmostLinearSSSP.Decremental.roundedInput i j).graph
            (DecrAlmostLinearSSSP.Decremental.scaleActive i j active) u v rs)
          (@Eq.{1} (List.{0} (Fin i.k))
            (@List.map.{0, 0} (Fin (DecrAlmostLinearSSSP.Decremental.roundedInput i j).k) (Fin i.k)
              (DecrAlmostLinearSSSP.Decremental.scaleOriginal i j) rs)
            es)) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (j : Nat) (e : Fin (DecrAlmostLinearSSSP.Decremental.roundedInput i j).k),
      And
        (@LE.le.{0} Real Real.instLE
          (@Nat.cast.{0} Real Real.instNatCast (i.weight (DecrAlmostLinearSSSP.Decremental.scaleOriginal i j e)))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (DecrAlmostLinearSSSP.Decremental.delta i j)
            (@Nat.cast.{0} Real Real.instNatCast ((DecrAlmostLinearSSSP.Decremental.roundedInput i j).weight e))))
        (@LE.le.{0} Real Real.instLE
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (DecrAlmostLinearSSSP.Decremental.delta i j)
            (@Nat.cast.{0} Real Real.instNatCast ((DecrAlmostLinearSSSP.Decremental.roundedInput i j).weight e)))
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@Nat.cast.{0} Real Real.instNatCast (i.weight (DecrAlmostLinearSSSP.Decremental.scaleOriginal i j e)))
            (DecrAlmostLinearSSSP.Decremental.delta i j)))))))) ∧ ((((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (j : Nat) (rs : List.{0} (Fin (DecrAlmostLinearSSSP.Decremental.roundedInput i j).k)),
      And
        (@LE.le.{0} Real Real.instLE
          (@List.sum.{0} Real Real.instAdd Real.instZero
            (@List.map.{0, 0} (Fin (DecrAlmostLinearSSSP.Decremental.roundedInput i j).k) Real
              (fun e =>
                @Nat.cast.{0} Real Real.instNatCast (i.weight (DecrAlmostLinearSSSP.Decremental.scaleOriginal i j e)))
              rs))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (DecrAlmostLinearSSSP.Decremental.delta i j)
            (@List.sum.{0} Real Real.instAdd Real.instZero
              (@List.map.{0, 0} (Fin (DecrAlmostLinearSSSP.Decremental.roundedInput i j).k) Real
                (fun e =>
                  @Nat.cast.{0} Real Real.instNatCast ((DecrAlmostLinearSSSP.Decremental.roundedInput i j).weight e))
                rs))))
        (@LE.le.{0} Real Real.instLE
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (DecrAlmostLinearSSSP.Decremental.delta i j)
            (@List.sum.{0} Real Real.instAdd Real.instZero
              (@List.map.{0, 0} (Fin (DecrAlmostLinearSSSP.Decremental.roundedInput i j).k) Real
                (fun e =>
                  @Nat.cast.{0} Real Real.instNatCast ((DecrAlmostLinearSSSP.Decremental.roundedInput i j).weight e))
                rs)))
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@List.sum.{0} Real Real.instAdd Real.instZero
              (@List.map.{0, 0} (Fin (DecrAlmostLinearSSSP.Decremental.roundedInput i j).k) Real
                (fun e =>
                  @Nat.cast.{0} Real Real.instNatCast (i.weight (DecrAlmostLinearSSSP.Decremental.scaleOriginal i j e)))
                rs))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@Nat.cast.{0} Real Real.instNatCast
                (@List.length.{0} (Fin (DecrAlmostLinearSSSP.Decremental.roundedInput i j).k) rs))
              (DecrAlmostLinearSSSP.Decremental.delta i j))))) ∧ (∀ {k : Nat} (w : Fin k → Nat) (es : List.{0} (Fin k)),
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
        (@List.map.{0, 0} (Fin k) Real (fun e => @Nat.cast.{0} Real Real.instNatCast (w e)) es))))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (j : Nat) (active : Finset.{0} (Fin i.k)) (u v : Fin i.n),
      @LE.le.{0} ENNReal ENNReal.instLE
        (@DecrAlmostLinearSSSP.Decremental.distance i.n i.k i.graph active
          (fun e =>
            @Nat.cast.{0} ENNReal
              (@AddMonoidWithOne.toNatCast.{0} ENNReal
                (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
              (i.weight e))
          u v)
        (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
          (@instHMul.{0} ENNReal
            (@Distrib.toMul.{0} ENNReal
              (@instDistribOfSemiring.{0} ENNReal (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
          (ENNReal.ofReal (DecrAlmostLinearSSSP.Decremental.delta i j))
          (@DecrAlmostLinearSSSP.Decremental.distance (DecrAlmostLinearSSSP.Decremental.roundedInput i j).n
            (DecrAlmostLinearSSSP.Decremental.roundedInput i j).k
            (DecrAlmostLinearSSSP.Decremental.roundedInput i j).graph
            (DecrAlmostLinearSSSP.Decremental.scaleActive i j active)
            (fun e =>
              @Nat.cast.{0} ENNReal
                (@AddMonoidWithOne.toNatCast.{0} ENNReal
                  (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                ((DecrAlmostLinearSSSP.Decremental.roundedInput i j).weight e))
            u v))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (j : Nat) (active : Finset.{0} (Fin i.k)) {u v : Fin i.n} {es : List.{0} (Fin i.k)},
      @DecrAlmostLinearSSSP.Decremental.Walk i.n i.k i.graph active u v es →
        (∀ (e : Fin i.k),
            @Membership.mem.{0, 0} (Fin i.k) (List.{0} (Fin i.k)) (@List.instMembership.{0} (Fin i.k)) es e →
              @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast (i.weight e))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                  (DecrAlmostLinearSSSP.Decremental.scale j))) →
          @LE.le.{0} ENNReal ENNReal.instLE
            (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
              (@instHMul.{0} ENNReal
                (@Distrib.toMul.{0} ENNReal
                  (@instDistribOfSemiring.{0} ENNReal (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
              (ENNReal.ofReal (DecrAlmostLinearSSSP.Decremental.delta i j))
              (@DecrAlmostLinearSSSP.Decremental.distance (DecrAlmostLinearSSSP.Decremental.roundedInput i j).n
                (DecrAlmostLinearSSSP.Decremental.roundedInput i j).k
                (DecrAlmostLinearSSSP.Decremental.roundedInput i j).graph
                (DecrAlmostLinearSSSP.Decremental.scaleActive i j active)
                (fun e =>
                  @Nat.cast.{0} ENNReal
                    (@AddMonoidWithOne.toNatCast.{0} ENNReal
                      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                    ((DecrAlmostLinearSSSP.Decremental.roundedInput i j).weight e))
                u v))
            (ENNReal.ofReal
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@List.sum.{0} Real Real.instAdd Real.instZero
                  (@List.map.{0, 0} (Fin i.k) Real (fun e => @Nat.cast.{0} Real Real.instNatCast (i.weight e)) es))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@Nat.cast.{0} Real Real.instNatCast (@List.length.{0} (Fin i.k) es))
                  (DecrAlmostLinearSSSP.Decremental.delta i j))))) ∧ (∀ {k : Nat} (w : Fin k → Nat) (es : List.{0} (Fin k)) (e : Fin k),
  @Membership.mem.{0, 0} (Fin k) (List.{0} (Fin k)) (@List.instMembership.{0} (Fin k)) es e →
    @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast (w e))
      (@List.sum.{0} Real Real.instAdd Real.instZero
        (@List.map.{0, 0} (Fin k) Real (fun e => @Nat.cast.{0} Real Real.instNatCast (w e)) es)))))) ∧ (((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (j : Nat) (active : Finset.{0} (Fin i.k)) (u v : Fin i.n),
      @DecrAlmostLinearSSSP.Decremental.Reachable i.n i.k i.graph active u v →
        @LE.le.{0} ENNReal ENNReal.instLE
            (@DecrAlmostLinearSSSP.Decremental.distance i.n i.k i.graph active
              (fun e =>
                @Nat.cast.{0} ENNReal
                  (@AddMonoidWithOne.toNatCast.{0} ENNReal
                    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                  (i.weight e))
              u v)
            (ENNReal.ofReal
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                (DecrAlmostLinearSSSP.Decremental.scale j))) →
          ∃ d,
            And
              (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                d)
              (And
                (@Eq.{1} ENNReal
                  (@DecrAlmostLinearSSSP.Decremental.distance i.n i.k i.graph active
                    (fun e =>
                      @Nat.cast.{0} ENNReal
                        (@AddMonoidWithOne.toNatCast.{0} ENNReal
                          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                        (i.weight e))
                    u v)
                  (ENNReal.ofReal d))
                (@LE.le.{0} ENNReal ENNReal.instLE
                  (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                    (@instHMul.{0} ENNReal
                      (@Distrib.toMul.{0} ENNReal
                        (@instDistribOfSemiring.{0} ENNReal
                          (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                    (ENNReal.ofReal (DecrAlmostLinearSSSP.Decremental.delta i j))
                    (@DecrAlmostLinearSSSP.Decremental.distance (DecrAlmostLinearSSSP.Decremental.roundedInput i j).n
                      (DecrAlmostLinearSSSP.Decremental.roundedInput i j).k
                      (DecrAlmostLinearSSSP.Decremental.roundedInput i j).graph
                      (DecrAlmostLinearSSSP.Decremental.scaleActive i j active)
                      (fun e =>
                        @Nat.cast.{0} ENNReal
                          (@AddMonoidWithOne.toNatCast.{0} ENNReal
                            (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                          ((DecrAlmostLinearSSSP.Decremental.roundedInput i j).weight e))
                      u v))
                  (ENNReal.ofReal
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) d
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@Nat.cast.{0} Real Real.instNatCast i.n) (DecrAlmostLinearSSSP.Decremental.delta i j))))))) ∧ (∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (active : Finset.{0} (Fin k)) (w : Fin k → ENNReal)
  (u v : Fin n),
  Not (@DecrAlmostLinearSSSP.Decremental.Reachable n k g active u v) →
    @Eq.{1} ENNReal (@DecrAlmostLinearSSSP.Decremental.distance n k g active w u v)
      (@Top.top.{0} ENNReal ENNReal.instTop))) ∧ ((∀ {k : Nat} (w : Fin k → Nat) (W : Nat),
  (∀ (e : Fin k), @LE.le.{0} Nat instLENat (w e) W) →
    ∀ (es : List.{0} (Fin k)),
      @LE.le.{0} Real Real.instLE
        (@List.sum.{0} Real Real.instAdd Real.instZero
          (@List.map.{0, 0} (Fin k) Real (fun e => @Nat.cast.{0} Real Real.instNatCast (w e)) es))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@Nat.cast.{0} Real Real.instNatCast (@List.length.{0} (Fin k) es)) (@Nat.cast.{0} Real Real.instNatCast W))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
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
                  (ENNReal.ofReal d)))) ∧ (∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (active : Finset.{0} (Fin k)) (w : Fin k → Real)
  (B : Real),
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) B →
    ∀ (u v : Fin n),
      And
        (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (@DecrAlmostLinearSSSP.Decremental.cappedDistance n k g active w B u v))
        (@LE.le.{0} Real Real.instLE (@DecrAlmostLinearSSSP.Decremental.cappedDistance n k g active w B u v) B))))))))) := by
  exact ⟨⟨⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.shadow_store,DecrAlmostLinearSSSP.Decremental.shadow_storeN⟩,⟨DecrAlmostLinearSSSP.Decremental.shadow_address_calculation,DecrAlmostLinearSSSP.Decremental.ShadowRep.metadata⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.ShadowRep.pc_update,DecrAlmostLinearSSSP.Decremental.ShadowRep.halt_update⟩,⟨DecrAlmostLinearSSSP.Decremental.shadow_nat_comparison,⟨DecrAlmostLinearSSSP.Decremental.shadow_real_comparison,DecrAlmostLinearSSSP.Decremental.ShadowRep.data_machine⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.ShadowDataRep.effect,DecrAlmostLinearSSSP.Decremental.ShadowDataRep.header⟩,⟨DecrAlmostLinearSSSP.Decremental.eval_shadow_header,DecrAlmostLinearSSSP.Decremental.eval_shadow_scalar⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.eval_shadow_cast,DecrAlmostLinearSSSP.Decremental.eval_shadow_address⟩,⟨DecrAlmostLinearSSSP.Decremental.repeatedAdd_eval,⟨DecrAlmostLinearSSSP.Decremental.structuredConstant_eval,DecrAlmostLinearSSSP.Decremental.eval_shadow_constant⟩⟩⟩⟩⟩,⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.repeatedAdd_nat_frame,DecrAlmostLinearSSSP.Decremental.repeatedAdd_real_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.ShadowDataRep.outside_nat_memory,DecrAlmostLinearSSSP.Decremental.ShadowDataRep.outside_nat_register⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.shadowReg_ne_even,DecrAlmostLinearSSSP.Decremental.append_report_eval⟩,⟨DecrAlmostLinearSSSP.Decremental.append_report_rep,⟨DecrAlmostLinearSSSP.Decremental.append_report_log,DecrAlmostLinearSSSP.Decremental.report_log_outside⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.InputCapture.eval_code,DecrAlmostLinearSSSP.Decremental.InputCapture.no_memory⟩,⟨DecrAlmostLinearSSSP.Decremental.InputCapture.captures_initial,⟨DecrAlmostLinearSSSP.Decremental.InputCapture.nat_shadow_frame,DecrAlmostLinearSSSP.Decremental.InputCapture.real_shadow_frame⟩⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.InputCapture.initial_shadow_zero,DecrAlmostLinearSSSP.Decremental.InputCapture.input_tape_below_base⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.Powers.prepare_eval,⟨DecrAlmostLinearSSSP.Decremental.Exact.Powers.prepare_prefix,DecrAlmostLinearSSSP.Decremental.Exact.Powers.eval_code⟩⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.Powers.nat_frame,DecrAlmostLinearSSSP.Decremental.Exact.Layout.eval_code⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.Layout.values,DecrAlmostLinearSSSP.Decremental.Exact.Layout.no_memory⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.Layout.nat_frame,DecrAlmostLinearSSSP.Decremental.Exact.Layout.real_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.Clear.body_eval,⟨DecrAlmostLinearSSSP.Decremental.Exact.Clear.nat_frame,DecrAlmostLinearSSSP.Decremental.Exact.Clear.real_frame⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.Clear.eval_code,DecrAlmostLinearSSSP.Decremental.Walk.suffix_of_vertex⟩,⟨DecrAlmostLinearSSSP.Decremental.Walk.erase_cycles,⟨DecrAlmostLinearSSSP.Decremental.Reachable.short_walk,DecrAlmostLinearSSSP.Decremental.Walk.cost_telescope⟩⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Walk.append,DecrAlmostLinearSSSP.Decremental.Walk.eq_of_empty⟩,⟨DecrAlmostLinearSSSP.Decremental.Reachable.trans,⟨DecrAlmostLinearSSSP.Decremental.mem_shortEdgeLists,DecrAlmostLinearSSSP.Decremental.exists_min_weight_walk⟩⟩⟩⟩⟩,⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.list_sum_ofReal,DecrAlmostLinearSSSP.Decremental.distance_le_walk⟩,⟨DecrAlmostLinearSSSP.Decremental.distance_min_weight,DecrAlmostLinearSSSP.Decremental.scaleOriginal_cut⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.scaleOriginal_tail,DecrAlmostLinearSSSP.Decremental.scaleOriginal_head⟩,⟨DecrAlmostLinearSSSP.Decremental.rounded_walk_project,⟨DecrAlmostLinearSSSP.Decremental.rounded_walk_lift,DecrAlmostLinearSSSP.Decremental.rounded_edge_cost⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.rounded_walk_cost,DecrAlmostLinearSSSP.Decremental.nat_weight_list_real⟩,⟨DecrAlmostLinearSSSP.Decremental.rounded_distance_lower,⟨DecrAlmostLinearSSSP.Decremental.rounded_distance_upper_of_walk,DecrAlmostLinearSSSP.Decremental.real_weight_le_walk_sum⟩⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.rounded_shortest_upper,DecrAlmostLinearSSSP.Decremental.distance_top_of_unreachable⟩,⟨DecrAlmostLinearSSSP.Decremental.list_real_weight_upper,⟨DecrAlmostLinearSSSP.Decremental.input_reachable_distance_bounds,DecrAlmostLinearSSSP.Decremental.cappedDistance_bounds⟩⟩⟩⟩⟩⟩⟩
