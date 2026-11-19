-- Prove2me | solution 1 for DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_5
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T11:22:24.749609+00:00
-- url     : https://prove2.me/submissions/74151a1c-5490-422f-bef5-2434454fe75f

import Definitions.Def_DecrAlmostLinearSSSP_RAMFoundation
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
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
open scoped ENNReal NNReal
attribute [local instance] Classical.propDecidable
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
theorem DecrAlmostLinearSSSP.Decremental.Structured.eval_natural : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (d q : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.natural d q) s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    { realReg := s.realReg, natReg := @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natReg d q,
      realMem := s.realMem, natMem := s.natMem } := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.1.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Structured.eval_mul : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (d a b : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.mul d a b) s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    {
      realReg :=
        @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realReg d
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (s.realReg a) (s.realReg b)),
      natReg := s.natReg, realMem := s.realMem, natMem := s.natMem } := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.1.2.2.1.2
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
theorem DecrAlmostLinearSSSP.Decremental.Exact.Powers.body_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.Powers.body s
    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
    (DecrAlmostLinearSSSP.Decremental.Exact.Powers.advanced s) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.1.1.2.2.2.2
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
theorem DecrAlmostLinearSSSP.Decremental.shadowReg_injective : @Function.Injective.{1, 1} Nat Nat DecrAlmostLinearSSSP.Decremental.shadowReg := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.shadowReg_ne_meta : ∀ (j k : Nat),
  @LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) →
    @Ne.{1} Nat (DecrAlmostLinearSSSP.Decremental.shadowReg j) k := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.2.1.2.2.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.shadowReg_ne_even : ∀ (j k : Nat),
  @Ne.{1} Nat (DecrAlmostLinearSSSP.Decremental.shadowReg j)
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.1.2.1.2.1.1
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
theorem DecrAlmostLinearSSSP.Decremental.Exact.Clear.body_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.Clear.body s
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    (DecrAlmostLinearSSSP.Decremental.Exact.Clear.advanced s) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.2.1.1.2.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.Exact.TentativeImage.stored : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {l : DecrAlmostLinearSSSP.Decremental.Exact.Layout.Addresses}
  {tentative : Fin i.n → Option.{0} Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.TentativeImage i l tentative s →
    ∀ (v : Fin i.n),
      @Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.stored s.machine (@Fin.val i.n v))
        (DecrAlmostLinearSSSP.Decremental.Exact.tentativeValue (tentative v)) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_6.2.2.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.Heap.Image.count : ∀ {n h base slot : Nat} {tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin n))} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  @DecrAlmostLinearSSSP.Decremental.Exact.Heap.Image n h base slot tree queue s →
    @Eq.{1} Nat
      (@DecrAlmostLinearSSSP.Decremental.RadixQueue.count h
        (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.abstract h tree))
      (@Multiset.card.{0} (Prod.{0, 0} Nat (Fin n)) queue) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_7.1.1.1.1.1.2
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
theorem DecrAlmostLinearSSSP.Decremental.Structured.NatFrame.flag : ∀ {cmd : DecrAlmostLinearSSSP.Decremental.Structured.Cmd} {k : Nat},
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame cmd k →
    DecrAlmostLinearSSSP.Decremental.Structured.FlagFrame cmd k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_2.1.1.2.2.1.2
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
theorem DecrAlmostLinearSSSP.Decremental.eval_shadow_call : ∀ (guest : DecrAlmostLinearSSSP.Decremental.Program) (B F : Nat),
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
                                  (@Eq.{1} Nat (u.natMem address) (s.natMem address))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_2.1.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.shadowAction_even_frame : ∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction) (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.shadowAction ins) k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_2.1.2.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.eval_observed_action : ∀ {B bank start : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data}
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
                                t))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_2.2.1.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.shadowAction_real_even_frame : ∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction) (k : Nat),
  @Even.{0} Nat instAddNat k →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.shadowAction ins) k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_2.2.1.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.shadowInterpreter_nat_even_frame : ∀ (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.shadowInterpreter code) k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_2.2.1.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.shadowInterpreter_real_even_frame : ∀ (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (k : Nat),
  @Even.{0} Nat instAddNat k →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.shadowInterpreter code) k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_2.2.1.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.ScaledCeiling.setup_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.ScaledCeiling.setup s
    (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))
    (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.setupData s) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_2.2.1.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.ScaledCeiling.setup_fields : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
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
                        (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58)))))))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_2.2.1.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.ScaledCeiling.setup_nat_frame : ∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.ScaledCeiling.setup k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_2.2.1.2.1.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.ScaledCeiling.setup_real_frame : ∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.ScaledCeiling.setup k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_2.2.1.2.2.1.1
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
theorem DecrAlmostLinearSSSP.Decremental.Fill.body_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Fill.body s
    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (DecrAlmostLinearSSSP.Decremental.Fill.next s) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_3.1.2.1.1.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.SnapshotFill.setup_fields : ∀ (N : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
      And
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.SnapshotFill.setupData N s).natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 116) (instOfNatNat (nat_lit 116))))
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50)))))
        (And
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.SnapshotFill.setupData N s).natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 118) (instOfNatNat (nat_lit 118))))
            N)
          (And
            (@Eq.{1} Nat
              ((DecrAlmostLinearSSSP.Decremental.SnapshotFill.setupData N s).natReg
                (@OfNat.ofNat.{0} Nat (nat_lit 120) (instOfNatNat (nat_lit 120))))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (And
              (@Eq.{1} Nat
                ((DecrAlmostLinearSSSP.Decremental.SnapshotFill.setupData N s).natReg
                  (@OfNat.ofNat.{0} Nat (nat_lit 122) (instOfNatNat (nat_lit 122))))
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (And
                (@Eq.{1} Nat
                  ((DecrAlmostLinearSSSP.Decremental.SnapshotFill.setupData N s).natReg
                    (@OfNat.ofNat.{0} Nat (nat_lit 124) (instOfNatNat (nat_lit 124))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                (And
                  (@Eq.{1} Real
                    ((DecrAlmostLinearSSSP.Decremental.SnapshotFill.setupData N s).realReg
                      (@OfNat.ofNat.{0} Nat (nat_lit 116) (instOfNatNat (nat_lit 116))))
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
                  (@Eq.{1} Nat
                    ((DecrAlmostLinearSSSP.Decremental.SnapshotFill.setupData N s).natReg
                      (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26)))))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_3.1.2.1.2.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.TapeCopy.Env.transfer : ∀ {B bank tail high cost : Nat} {delta cutoff : Real} {cmd : DecrAlmostLinearSSSP.Decremental.Structured.Cmd}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.TapeCopy.Env B bank tail high delta cutoff s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval cmd s cost t →
      DecrAlmostLinearSSSP.Decremental.TapeCopy.Stable cmd →
        DecrAlmostLinearSSSP.Decremental.TapeCopy.Env B bank tail high delta cutoff t := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_4.1.2.1.1.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.shadowReg_ne_of_even : ∀ (j d : Nat), @Even.{0} Nat instAddNat d → @Ne.{1} Nat (DecrAlmostLinearSSSP.Decremental.shadowReg j) d := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_4.1.2.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.TailFrame.seq : ∀ {a b : DecrAlmostLinearSSSP.Decremental.Structured.Cmd},
  DecrAlmostLinearSSSP.Decremental.TailFrame a →
    DecrAlmostLinearSSSP.Decremental.TailFrame b → DecrAlmostLinearSSSP.Decremental.TailFrame (a.seq b) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_4.2.1.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.TailFrame.loop : ∀ (test : DecrAlmostLinearSSSP.Decremental.Structured.Test) {body : DecrAlmostLinearSSSP.Decremental.Structured.Cmd},
  DecrAlmostLinearSSSP.Decremental.TailFrame body →
    DecrAlmostLinearSSSP.Decremental.TailFrame (DecrAlmostLinearSSSP.Decremental.Structured.Cmd.loop test body) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_4.2.1.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.RegisterSave.eval_saveOne : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (j : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.RegisterSave.saveOne j) s
    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
    (DecrAlmostLinearSSSP.Decremental.RegisterSave.savedOne s j) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_4.2.2.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.RegisterSave.eval_restoreOne : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (j : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.RegisterSave.restoreOne j) s
    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
    (DecrAlmostLinearSSSP.Decremental.RegisterSave.restoredOne s j) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_4.2.2.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.RegisterSave.savedOne_base : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (j : Nat),
  @Eq.{1} Nat
    ((DecrAlmostLinearSSSP.Decremental.RegisterSave.savedOne s j).natReg
      (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50)))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_4.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.RegisterSave.savedOne_registers : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (j k : Nat),
  And
    (@Eq.{1} Nat
      ((DecrAlmostLinearSSSP.Decremental.RegisterSave.savedOne s j).natReg
        (DecrAlmostLinearSSSP.Decremental.shadowReg k))
      (s.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg k)))
    (@Eq.{1} Real
      ((DecrAlmostLinearSSSP.Decremental.RegisterSave.savedOne s j).realReg
        (DecrAlmostLinearSSSP.Decremental.shadowReg k))
      (s.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg k))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_4.2.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.RegisterSave.savedOne_value : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (j : Nat),
  And
    (@Eq.{1} Nat
      ((DecrAlmostLinearSSSP.Decremental.RegisterSave.savedOne s j).natMem
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
      (s.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg j)))
    (@Eq.{1} Real
      ((DecrAlmostLinearSSSP.Decremental.RegisterSave.savedOne s j).realMem
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
      (s.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg j))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_4.2.2.2.2.2.2.2
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
end DecrAlmostLinearSSSP.Decremental
end s62
section s63
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s63
section s64
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.ScaledCeiling
open Structured
end DecrAlmostLinearSSSP.Decremental.ScaledCeiling
end s64
section s65
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end s65
section s66
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end s66
section s67
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end s67
section s68
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end s68
section s69
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end s69
section s70
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end s70
section s71
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end s71
section s72
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
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
namespace DecrAlmostLinearSSSP.Decremental.ScaledCeiling
open Structured
end DecrAlmostLinearSSSP.Decremental.ScaledCeiling
end s76
section s77
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.ScaledCeiling
open Structured
end DecrAlmostLinearSSSP.Decremental.ScaledCeiling
end s77
section s78
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.ScaledCeiling
open Structured
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
end DecrAlmostLinearSSSP.Decremental
end s84
section s85
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.ScaledCeiling
open Structured
end DecrAlmostLinearSSSP.Decremental.ScaledCeiling
end s85
section s86
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.ScaledCeiling
open Structured
end DecrAlmostLinearSSSP.Decremental.ScaledCeiling
end s86
section s87
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Layout
open Structured
end DecrAlmostLinearSSSP.Decremental.Layout
end s87
section s88
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
namespace ScaledCeiling
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
lemma savedOne_memory_frame (s : Data) (j address : ℕ) (ha : address ≠ s.natReg 50+2*j) :
    (savedOne s j).natMem address = s.natMem address ∧ (savedOne s j).realMem address = s.realMem address := by
  simp [savedOne,Function.update_of_ne ha]
lemma restoredOne_base (s : Data) (j : ℕ) : (restoredOne s j).natReg 50 = s.natReg 50 := by
  simp [restoredOne,Function.update_of_ne (Ne.symm (shadowReg_ne_even j 25))]
lemma restoredOne_value (s : Data) (j : ℕ) :
    (restoredOne s j).natReg (shadowReg j) = s.natMem (s.natReg 50+2*j) ∧
      (restoredOne s j).realReg (shadowReg j) = s.realMem (s.natReg 50+2*j) := by simp [restoredOne]
lemma restoredOne_register_frame (s : Data) (j k : ℕ) (hk : k ≠ j) :
    (restoredOne s j).natReg (shadowReg k) = s.natReg (shadowReg k) ∧
      (restoredOne s j).realReg (shadowReg k) = s.realReg (shadowReg k) := by
  have hne := shadowReg_injective.ne hk
  simp [restoredOne,Function.update_of_ne hne,Function.update_of_ne (shadowReg_ne_even k 26),
    Function.update_of_ne (shadowReg_ne_even k 27)]
lemma restoredOne_memory (s : Data) (j : ℕ) :
    (restoredOne s j).natMem = s.natMem ∧ (restoredOne s j).realMem = s.realMem := ⟨rfl,rfl⟩
end DecrAlmostLinearSSSP.Decremental.RegisterSave
end s119
section s120
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.RegisterSave
open Structured
lemma eval_saveRegisters (registers : List ℕ) (hnd : registers.Nodup) (s : Data) :
    ∃ t, Eval (saveRegisters registers) s (4*registers.length) t ∧ t.natReg 50 = s.natReg 50 ∧
      (∀ k, t.natReg (shadowReg k) = s.natReg (shadowReg k) ∧ t.realReg (shadowReg k) = s.realReg (shadowReg k)) ∧
      (∀ k ∈ registers, t.natMem (s.natReg 50+2*k) = s.natReg (shadowReg k) ∧
        t.realMem (s.natReg 50+2*k) = s.realReg (shadowReg k)) ∧
      (∀ address, (∀ k ∈ registers, address ≠ s.natReg 50+2*k) →
        t.natMem address = s.natMem address ∧ t.realMem address = s.realMem address) := by
  induction registers generalizing s with
  | nil => exact ⟨s,.skip s,rfl,fun _ => ⟨rfl,rfl⟩,by simp,fun _ _ => ⟨rfl,rfl⟩⟩
  | cons j rest ih =>
    have hnd' := List.nodup_cons.mp hnd
    let u := savedOne s j
    have hu := eval_saveOne s j
    obtain ⟨t,ht,hbase,hregs,hvals,hframe⟩ := ih hnd'.2 u
    have hub : u.natReg 50 = s.natReg 50 := savedOne_base s j
    refine ⟨t,?_,hbase.trans hub,?_,?_,?_⟩
    · simpa only [saveRegisters,List.length_cons,Nat.mul_add,Nat.mul_one,Nat.add_comm 4 _] using Eval.seq hu ht
    · intro k
      exact ⟨(hregs k).1.trans (savedOne_registers s j k).1,(hregs k).2.trans (savedOne_registers s j k).2⟩
    · intro k hk
      rcases List.mem_cons.mp hk with hk|hk
      · subst k
        have hout : ∀ k ∈ rest, s.natReg 50+2*j ≠ u.natReg 50+2*k := by
          intro k hk heq
          rw [hub] at heq
          have heq' : j = k := by omega
          exact hnd'.1 (heq' ▸ hk)
        have hf := hframe (s.natReg 50+2*j) hout
        have hv := savedOne_value s j
        exact ⟨hf.1.trans hv.1,hf.2.trans hv.2⟩
      · have hv := hvals k hk
        rw [hub] at hv
        exact ⟨hv.1.trans (savedOne_registers s j k).1,hv.2.trans (savedOne_registers s j k).2⟩
    · intro address hout
      have htail : ∀ k ∈ rest, address ≠ u.natReg 50+2*k := by
        intro k hk
        rw [hub]
        exact hout k (List.mem_cons_of_mem _ hk)
      have hf := hframe address htail
      have huFrame := savedOne_memory_frame s j address (hout j List.mem_cons_self)
      exact ⟨hf.1.trans huFrame.1,hf.2.trans huFrame.2⟩
lemma eval_restoreRegisters (registers : List ℕ) (hnd : registers.Nodup) (s : Data) :
    ∃ t, Eval (restoreRegisters registers) s (4*registers.length) t ∧ t.natReg 50 = s.natReg 50 ∧
      t.natMem = s.natMem ∧ t.realMem = s.realMem ∧
      (∀ k ∈ registers, t.natReg (shadowReg k) = s.natMem (s.natReg 50+2*k) ∧
        t.realReg (shadowReg k) = s.realMem (s.natReg 50+2*k)) ∧
      (∀ k, k ∉ registers → t.natReg (shadowReg k) = s.natReg (shadowReg k) ∧
        t.realReg (shadowReg k) = s.realReg (shadowReg k)) := by
  induction registers generalizing s with
  | nil => exact ⟨s,.skip s,rfl,rfl,rfl,by simp,fun _ _ => ⟨rfl,rfl⟩⟩
  | cons j rest ih =>
    have hnd' := List.nodup_cons.mp hnd
    let u := restoredOne s j
    have hu := eval_restoreOne s j
    obtain ⟨t,ht,hbase,hn,hr,hvals,hframe⟩ := ih hnd'.2 u
    have hub : u.natReg 50 = s.natReg 50 := restoredOne_base s j
    have hum := restoredOne_memory s j
    refine ⟨t,?_,hbase.trans hub,hn.trans hum.1,hr.trans hum.2,?_,?_⟩
    · simpa only [restoreRegisters,List.length_cons,Nat.mul_add,Nat.mul_one,Nat.add_comm 4 _] using Eval.seq hu ht
    · intro k hk
      rcases List.mem_cons.mp hk with hk|hk
      · subst k
        have hf := hframe j hnd'.1
        have hv := restoredOne_value s j
        exact ⟨hf.1.trans hv.1,hf.2.trans hv.2⟩
      · have hv := hvals k hk
        rw [hub,hum.1,hum.2] at hv
        exact hv
    · intro k hk
      have hkhead : k ≠ j := by intro heq;subst k;exact hk List.mem_cons_self
      have hktail : k ∉ rest := fun hh => hk (List.mem_cons_of_mem j hh)
      have hf := hframe k hktail
      have huFrame := restoredOne_register_frame s j k hkhead
      exact ⟨hf.1.trans huFrame.1,hf.2.trans huFrame.2⟩
end DecrAlmostLinearSSSP.Decremental.RegisterSave
end s120
section s121
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.RegisterSave
open Structured
lemma restoreOne_nat_meta (j k : ℕ) (hk : k < 9) : NatFrame (restoreOne j) k := by
  have hs := shadowReg_ne_meta j k hk
  simp only [restoreOne,Structured.sequence,NatFrame,Structured.natural,nadd,loadN,load,writesNat]
  exact ⟨by omega,by omega,hs,not_false,trivial⟩
lemma restoreOne_real_meta (j k : ℕ) (hk : k < 9) : RealFrame (restoreOne j) k := by
  have hs := shadowReg_ne_meta j k hk
  simp only [restoreOne,Structured.sequence,RealFrame,Structured.natural,nadd,loadN,load,writesReal]
  exact ⟨not_false,not_false,not_false,hs,trivial⟩
lemma restoreRegisters_nat_meta (registers : List ℕ) (k : ℕ) (hk : k < 9) : NatFrame (restoreRegisters registers) k := by
  induction registers with
  | nil => trivial
  | cons j rest ih => exact ⟨restoreOne_nat_meta j k hk,ih⟩
lemma restoreRegisters_real_meta (registers : List ℕ) (k : ℕ) (hk : k < 9) : RealFrame (restoreRegisters registers) k := by
  induction registers with
  | nil => trivial
  | cons j rest ih => exact ⟨restoreOne_real_meta j k hk,ih⟩
lemma restore_saved_image (B F N : ℕ) (s : Data) (g : Machine)
    (hpc : s.natReg 2 = g.pc) (hw : s.natReg 3 = g.work)
    (hh : (s.natReg 4 == 1) = g.halted) (hf : (s.natReg 5 == 1) = g.fault)
    (hmr : ∀ a, s.realMem (B+F*(2*a+1)) = g.realMem a)
    (hmn : ∀ a, s.natMem (B+F*(2*a+1)) = F*g.natMem a)
    (hsaved : ∀ j < N, s.natMem (s.natReg 50+2*j) = F*g.natReg j ∧
      s.realMem (s.natReg 50+2*j) = g.realReg j)
    (htail : ∀ j, N ≤ j → s.natReg (shadowReg j) = 0 ∧ s.realReg (shadowReg j) = 0)
    (hgtail : ZeroRegisterTail N g) :
    ∃ t, Eval (restoreRegisters (List.range N)) s (4*N) t ∧ ShadowDataRep B F t g := by
  obtain ⟨t,he,hbase,hn,hr,hvals,hframe⟩ := eval_restoreRegisters (List.range N) List.nodup_range s
  refine ⟨t,by simpa only [List.length_range] using he,?_⟩
  have hmeta (k : ℕ) (hk : k < 9) : t.natReg k = s.natReg k := he.nat_frame (restoreRegisters_nat_meta _ k hk)
  refine ⟨(hmeta 2 (by omega)).trans hpc,(hmeta 3 (by omega)).trans hw,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Data.machine,hmeta 4 (by omega)] using hh
  · simpa only [Data.machine,hmeta 5 (by omega)] using hf
  · intro j
    change t.realReg (shadowReg j) = g.realReg j
    by_cases hj : j < N
    · exact (hvals j (List.mem_range.mpr hj)).2.trans (hsaved j hj).2
    · have hj' : N ≤ j := by omega
      rw [(hframe j (by simpa only [List.mem_range] using hj)).2,(htail j hj').2,(hgtail j hj').2]
  · intro j
    change t.natReg (shadowReg j) = F*g.natReg j
    by_cases hj : j < N
    · exact (hvals j (List.mem_range.mpr hj)).1.trans (hsaved j hj).1
    · have hj' : N ≤ j := by omega
      rw [(hframe j (by simpa only [List.mem_range] using hj)).1,(htail j hj').1,(hgtail j hj').1,Nat.mul_zero]
  · intro a
    exact (congrFun hr _).trans (hmr a)
  · intro a
    exact (congrFun hn _).trans (hmn a)
end DecrAlmostLinearSSSP.Decremental.RegisterSave
end s121
section s122
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.SourceSetup
open Structured
open RegisterSave
lemma header_eval (entry : ℕ) (s : Data) : Eval (header entry) s 10 (headerData entry s) := eval_sequence_atoms (headerAtoms entry) s
lemma header_memory (entry : ℕ) (s : Data) :
    (headerData entry s).realMem = s.realMem ∧ (headerData entry s).natMem = s.natMem := by
  exact (header_eval entry s).no_memory (by simp [header,headerAtoms,Structured.sequence,NoMemory,NoStore])
lemma header_shadow_nat_frame (entry j : ℕ) : NatFrame (header entry) (shadowReg j) := by
  simp only [header,headerAtoms,List.map_cons,List.map_nil,Structured.sequence,NatFrame,writesNat,shadowReg]
  repeat' (first | apply And.intro | omega | trivial)
lemma header_shadow_real_frame (entry j : ℕ) : RealFrame (header entry) (shadowReg j) := by
  simp only [header,headerAtoms,List.map_cons,List.map_nil,Structured.sequence,RealFrame,writesReal,shadowReg]
  repeat' (first | apply And.intro | omega | trivial)
lemma header_fields (entry B F : ℕ) (s : Data) (hB : s.natReg 74 = B) (hF : s.natReg 112 = F) (hz : s.natReg 56 = 0) :
    (headerData entry s).natReg 0 = B ∧ (headerData entry s).natReg 1 = 1 ∧
    (headerData entry s).natReg 2 = entry ∧ (headerData entry s).natReg 4 = 0 ∧
    (headerData entry s).natReg 5 = 0 ∧ (headerData entry s).natReg 7 = F ∧
    (headerData entry s).realReg 7 = (F : ℝ) ∧
    (headerData entry s).natReg 3 = s.natMem (s.natReg 106+6) ∧
    (headerData entry s).natReg 50 = s.natReg 50 := by
  simp [headerData,headerAtoms,Atom.effect,instructionEffect,data,Data.machine,hB,hF,hz]
lemma restore_no_memory (registers : List ℕ) : NoMemory (restoreRegisters registers) := by
  induction registers with
  | nil => trivial
  | cons j rest ih =>
    refine ⟨?_,ih⟩
    simp [restoreOne,Structured.sequence,NoMemory,Structured.natural,nadd,loadN,load,NoStore]
lemma eval_code (N entry B F : ℕ) (s : Data) (g : Machine)
    (hB : s.natReg 74 = B) (hF : s.natReg 112 = F) (hz : s.natReg 56 = 0)
    (hentry : g.pc = entry) (hwork : s.natMem (s.natReg 106+6) = g.work)
    (hhalt : g.halted = false) (hfault : g.fault = false)
    (hmr : ∀ a, s.realMem (B+F*(2*a+1)) = g.realMem a)
    (hmn : ∀ a, s.natMem (B+F*(2*a+1)) = F*g.natMem a)
    (hsaved : ∀ j < N, s.natMem (s.natReg 50+2*j) = F*g.natReg j ∧ s.realMem (s.natReg 50+2*j) = g.realReg j)
    (htail : ∀ j, N ≤ j → s.natReg (shadowReg j) = 0 ∧ s.realReg (shadowReg j) = 0)
    (hgtail : ZeroRegisterTail N g) :
    ∃ t, Eval (code N entry) s (10+4*N) t ∧ ShadowDataRep B F t g ∧
      t.natReg 0 = B ∧ t.natReg 1 = 1 ∧ t.natReg 7 = F ∧ t.realReg 7 = (F : ℝ) ∧ t.natReg 4 = 0 ∧
      t.realMem = s.realMem ∧ t.natMem = s.natMem := by
  let u := headerData entry s
  have hu := header_eval entry s
  obtain ⟨h0,h1,h2,h4,h5,h7,hr7,h3,h50⟩ := header_fields entry B F s hB hF hz
  have hmem := header_memory entry s
  change u.realMem = s.realMem ∧ u.natMem = s.natMem at hmem
  change u.natReg 50 = s.natReg 50 at h50
  change u.natReg 4 = 0 at h4
  change u.natReg 5 = 0 at h5
  have hregs (j : ℕ) : u.natReg (shadowReg j) = s.natReg (shadowReg j) ∧ u.realReg (shadowReg j) = s.realReg (shadowReg j) :=
    ⟨hu.nat_frame (header_shadow_nat_frame entry j),hu.real_frame (header_shadow_real_frame entry j)⟩
  have hsaved' : ∀ j < N, u.natMem (u.natReg 50+2*j) = F*g.natReg j ∧ u.realMem (u.natReg 50+2*j) = g.realReg j := by
    intro j hj
    simpa only [h50,hmem.1,hmem.2] using hsaved j hj
  have htail' : ∀ j, N ≤ j → u.natReg (shadowReg j) = 0 ∧ u.realReg (shadowReg j) = 0 := by
    intro j hj
    rw [(hregs j).1,(hregs j).2]
    exact htail j hj
  obtain ⟨t,ht,hrep⟩ := restore_saved_image B F N u g (h2.trans hentry.symm) (h3.trans hwork)
    (by simp [h4,hhalt]) (by simp [h5,hfault])
    (fun a => (congrFun hmem.1 _).trans (hmr a)) (fun a => (congrFun hmem.2 _).trans (hmn a)) hsaved' htail' hgtail
  have hmeta (k : ℕ) (hk : k < 9) : t.natReg k = u.natReg k := ht.nat_frame (restoreRegisters_nat_meta _ k hk)
  have hrmeta : t.realReg 7 = u.realReg 7 := ht.real_frame (restoreRegisters_real_meta _ 7 (by omega))
  have hm := ht.no_memory (restore_no_memory _)
  refine ⟨t,Eval.seq hu ht,hrep,(hmeta 0 (by omega)).trans h0,(hmeta 1 (by omega)).trans h1,
    (hmeta 7 (by omega)).trans h7,hrmeta.trans hr7,(hmeta 4 (by omega)).trans h4,
    hm.1.trans hmem.1,hm.2.trans hmem.2⟩
end DecrAlmostLinearSSSP.Decremental.SourceSetup
end s122
section s123
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
lemma eval_observed_instruction {B bank start : ℕ} {s : Data} {g : Machine}
    (h : ShadowDataRep B (bankFactor bank) s g) (hb : s.natReg 0 = B)
    (h1 : s.natReg 1 = 1) (hf : s.natReg 7 = bankFactor bank)
    (hrf : s.realReg 7 = (bankFactor bank : ℝ)) (h14 : s.natReg 14 = 2)
    (reports : List ℕ) (hl : ReportLog start reports s) (hstart : ∃ r, start = B+2*r+1)
    (ins : Instruction) :
    ∃ cost t, Eval (observedInstruction g.pc ins) s cost t ∧ cost ≤ actionBound ins+5 ∧
      ShadowDataRep B (bankFactor bank) t (instructionEffect ins {g with pc := g.pc+1,work := g.work+1}) ∧
      ReportLog start (reports++physicalWrites B bank ins g) t := by
  let t : Data := {s with natReg := Function.update (Function.update s.natReg 2 (g.pc+1)) 3 (s.natReg 3+1)}
  have he : Eval (.seq (natural 2 (g.pc+1)) (nadd 3 3 1)) s 2 t := by
    simpa only [h1] using eval_shadow_header s g.pc
  have ht := h.header h1
  have ht0 : t.natReg 0 = B := by simp [t,hb]
  have ht1 : t.natReg 1 = 1 := by simp [t,h1]
  have ht7 : t.natReg 7 = bankFactor bank := by simp [t,hf]
  have ht14 : t.natReg 14 = 2 := by simp [t,h14]
  have hlog : ReportLog start reports t := by simpa [ReportLog,t] using hl
  obtain ⟨cost,u,hu,hcost,hrep,hrlog⟩ := eval_observed_action ht ht0 ht1 ht7 hrf ht14 reports hlog hstart ins
  refine ⟨2+cost,u,.seq he hu,by omega,hrep,?_⟩
  have hwrites : physicalWrites B bank ins {g with pc := g.pc+1,work := g.work+1} = physicalWrites B bank ins g := by
    cases ins <;> rfl
  rwa [hwrites] at hrlog
lemma eval_observed_dispatch_aux {B bank start : ℕ} (code : List Instruction) (pc : ℕ) (s : Data) (g : Machine)
    (h : ShadowDataRep B (bankFactor bank) s g) (hb : s.natReg 0 = B)
    (h1 : s.natReg 1 = 1) (hf : s.natReg 7 = bankFactor bank)
    (hrf : s.realReg 7 = (bankFactor bank : ℝ)) (h14 : s.natReg 14 = 2)
    (reports : List ℕ) (hl : ReportLog start reports s) (hstart : ∃ r, start = B+2*r+1)
    (hpc : pc ≤ g.pc) (ins : Instruction) (hins : code[g.pc-pc]? = some ins) :
    ∃ cost t, Eval (observedDispatchAux pc code) s cost t ∧ cost ≤ observedDispatchCharge code ∧
      ShadowDataRep B (bankFactor bank) t (instructionEffect ins {g with pc := g.pc+1,work := g.work+1}) ∧
      ReportLog start (reports++physicalWrites B bank ins g) t := by
  induction code generalizing pc s with
  | nil => simp at hins
  | cons head rest ih =>
    let t : Data := {s with natReg := Function.update s.natReg 8 (pc+1)}
    have ht : ShadowDataRep B (bankFactor bank) t g := h.scratch8 (pc+1)
    have ht0 : t.natReg 0 = B := by simp [t,hb]
    have ht1 : t.natReg 1 = 1 := by simp [t,h1]
    have ht7 : t.natReg 7 = bankFactor bank := by simp [t,hf]
    have ht14 : t.natReg 14 = 2 := by simp [t,h14]
    have htlog : ReportLog start reports t := by simpa [ReportLog,t] using hl
    by_cases hp : g.pc = pc
    · have hins' : head = ins := by simpa only [hp,Nat.sub_self,List.getElem?_cons_zero,Option.some.injEq] using hins
      subst ins
      obtain ⟨cost,u,hu,hcost,hrep,hlog⟩ := eval_observed_instruction ht ht0 ht1 ht7 hrf ht14 reports htlog hstart head
      have htest : (Test.natLess 2 8).holds t := by
        change t.natReg 2 < t.natReg 8
        simp only [t,Function.update_self,Function.update_of_ne (by decide : (2 : ℕ) ≠ 8)]
        have hh : s.natReg 2 = g.pc := h.pc
        omega
      have hu' : Eval (observedInstruction pc head) t cost u := by simpa only [hp] using hu
      have he : Eval (observedDispatchAux pc (head::rest)) s (1+(cost+1)) u :=
        Eval.seq (eval_natural s 8 (pc+1)) (Eval.branchYes htest hu')
      refine ⟨1+(cost+1),u,he,?_,hrep,hlog⟩
      simp only [observedDispatchCharge,List.map_cons,List.sum_cons] at hcost ⊢
      omega
    · have hnext : pc+1 ≤ g.pc := by omega
      have hidx : g.pc-pc = (g.pc-(pc+1))+1 := by omega
      have htail : rest[g.pc-(pc+1)]? = some ins := by simpa only [hidx,List.getElem?_cons_succ] using hins
      obtain ⟨cost,u,hu,hcost,hrep,hlog⟩ := ih (pc+1) t ht ht0 ht1 ht7 hrf ht14 htlog hnext htail
      have htest : ¬(Test.natLess 2 8).holds t := by
        change ¬t.natReg 2 < t.natReg 8
        simp only [t,Function.update_self,Function.update_of_ne (by decide : (2 : ℕ) ≠ 8)]
        have hh : s.natReg 2 = g.pc := h.pc
        omega
      refine ⟨1+(cost+2),u,Eval.seq (eval_natural s 8 (pc+1)) (Eval.branchNo htest hu),?_,hrep,hlog⟩
      simp only [observedDispatchCharge,List.map_cons,List.sum_cons] at hcost ⊢
      omega
end DecrAlmostLinearSSSP.Decremental
end s123
section s124
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
lemma appendStoreReport_nat_frame (k : ℕ) (h10 : 10 ≠ k) (h12 : 12 ≠ k) : NatFrame appendStoreReport k := by
  simp [appendStoreReport,Structured.sequence,NatFrame,storeN,nadd,writesNat,h10,h12]
lemma appendStoreReport_real_frame (k : ℕ) : RealFrame appendStoreReport k := by
  simp [appendStoreReport,Structured.sequence,RealFrame,storeN,nadd,writesReal]
lemma observedAction_nat_frame (ins : Instruction) (k : ℕ) (hk : k < 9)
    (h2 : 2 ≠ k) (h4 : 4 ≠ k) (h6 : 6 ≠ k) : NatFrame (observedAction ins) k := by
  have ha := shadowAction_nat_frame ins k hk h2 h4 h6
  have hp := appendStoreReport_nat_frame k (by omega) (by omega)
  cases ins <;> first | exact ha | exact ⟨ha,hp⟩
lemma observedAction_real_frame (ins : Instruction) (k : ℕ) (hk : k < 9) : RealFrame (observedAction ins) k := by
  have ha := shadowAction_real_frame ins k hk
  have hp := appendStoreReport_real_frame k
  cases ins <;> first | exact ha | exact ⟨ha,hp⟩
lemma observedAction_flag_frame (ins : Instruction) : FlagFrame (observedAction ins) 4 := by
  have ha := shadowAction_flag_frame ins
  have hp := (appendStoreReport_nat_frame 4 (by omega) (by omega)).flag
  cases ins <;> first | exact ha | exact ⟨ha,hp⟩
lemma observedAction_nat14_frame (ins : Instruction) : NatFrame (observedAction ins) 14 := by
  have ha := shadowAction_even_frame ins 14 (by omega) (by decide)
  have hp := appendStoreReport_nat_frame 14 (by omega) (by omega)
  cases ins <;> first | exact ha | exact ⟨ha,hp⟩
lemma observedInstruction_nat_frame (pc : ℕ) (ins : Instruction) (k : ℕ)
    (hk : k = 0 ∨ k = 1 ∨ k = 7) : NatFrame (observedInstruction pc ins) k := by
  refine ⟨?_,observedAction_nat_frame ins k (by rcases hk with rfl|rfl|rfl <;> omega)
    (by rcases hk with rfl|rfl|rfl <;> omega) (by rcases hk with rfl|rfl|rfl <;> omega)
    (by rcases hk with rfl|rfl|rfl <;> omega)⟩
  simp only [NatFrame,Structured.natural,nadd,writesNat]
  rcases hk with rfl|rfl|rfl <;> omega
lemma observedInstruction_real_frame (pc : ℕ) (ins : Instruction) : RealFrame (observedInstruction pc ins) 7 :=
  ⟨⟨not_false,not_false⟩,observedAction_real_frame ins 7 (by omega)⟩
lemma observedInstruction_flag_frame (pc : ℕ) (ins : Instruction) : FlagFrame (observedInstruction pc ins) 4 :=
  ⟨(show NatFrame (.seq (natural 2 (pc+1)) (nadd 3 3 1)) 4 from ⟨by norm_num [NatFrame,Structured.natural,nadd,writesNat],by norm_num [NatFrame,Structured.natural,nadd,writesNat]⟩).flag,
    observedAction_flag_frame ins⟩
lemma observedDispatchAux_nat_frame (code : List Instruction) (start k : ℕ)
    (hk : k = 0 ∨ k = 1 ∨ k = 7) : NatFrame (observedDispatchAux start code) k := by
  induction code generalizing start with
  | nil =>
    simp only [observedDispatchAux,NatFrame,Structured.natural,writesNat]
    rcases hk with rfl|rfl|rfl <;> omega
  | cons ins rest ih =>
    refine ⟨?_,observedInstruction_nat_frame start ins k hk,ih (start+1)⟩
    simp only [NatFrame,Structured.natural,writesNat]
    rcases hk with rfl|rfl|rfl <;> omega
lemma observedDispatchAux_real_frame (code : List Instruction) (start : ℕ) : RealFrame (observedDispatchAux start code) 7 := by
  induction code generalizing start with
  | nil => exact ⟨not_false,not_false⟩
  | cons ins rest ih => exact ⟨not_false,observedInstruction_real_frame start ins,ih (start+1)⟩
lemma observedDispatchAux_flag_frame (code : List Instruction) (start : ℕ) : FlagFrame (observedDispatchAux start code) 4 := by
  induction code generalizing start with
  | nil => exact ⟨Or.inl (by norm_num [NatFrame,Structured.natural,nadd,writesNat]),Or.inr ⟨1,le_rfl,rfl⟩⟩
  | cons ins rest ih => exact ⟨Or.inl (by norm_num [NatFrame,Structured.natural,nadd,writesNat]),observedInstruction_flag_frame start ins,ih (start+1)⟩
lemma observedInstruction_nat14_frame (pc : ℕ) (ins : Instruction) : NatFrame (observedInstruction pc ins) 14 :=
  ⟨⟨by norm_num [NatFrame,Structured.natural,writesNat],by norm_num [NatFrame,nadd,writesNat]⟩,
    observedAction_nat14_frame ins⟩
lemma observedDispatchAux_nat14_frame (code : List Instruction) (pc : ℕ) : NatFrame (observedDispatchAux pc code) 14 := by
  induction code generalizing pc with
  | nil => exact ⟨by norm_num [NatFrame,Structured.natural,writesNat],by norm_num [NatFrame,Structured.natural,writesNat]⟩
  | cons ins rest ih => exact ⟨by norm_num [NatFrame,Structured.natural,writesNat],observedInstruction_nat14_frame pc ins,ih (pc+1)⟩
end DecrAlmostLinearSSSP.Decremental
end s124
section s125
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
namespace RegisterSave
lemma saveOne_nat_frame (j k : ℕ) (h52 : k ≠ 52) (h54 : k ≠ 54) : NatFrame (saveOne j) k := by
  simp [saveOne,Structured.sequence,NatFrame,Structured.natural,nadd,storeN,store,writesNat,Ne.symm h52,Ne.symm h54]
lemma saveRegisters_nat_frame (registers : List ℕ) (k : ℕ) (h52 : k ≠ 52) (h54 : k ≠ 54) : NatFrame (saveRegisters registers) k := by
  induction registers with
  | nil => trivial
  | cons j rest ih => exact ⟨saveOne_nat_frame j k h52 h54,ih⟩
lemma restoreOne_nat_even (j k : ℕ) (heven : Even k) (h52 : k ≠ 52) (h54 : k ≠ 54) : NatFrame (restoreOne j) k := by
  have hs : shadowReg j ≠ k := by obtain ⟨q,hq⟩ := heven;dsimp [shadowReg];omega
  simp [restoreOne,Structured.sequence,NatFrame,Structured.natural,nadd,loadN,load,writesNat,Ne.symm h52,Ne.symm h54,hs]
lemma restoreRegisters_nat_even (registers : List ℕ) (k : ℕ) (heven : Even k) (h52 : k ≠ 52) (h54 : k ≠ 54) : NatFrame (restoreRegisters registers) k := by
  induction registers with
  | nil => trivial
  | cons j rest ih => exact ⟨restoreOne_nat_even j k heven h52 h54,ih⟩
lemma restoreRegisters_real_even (registers : List ℕ) (k : ℕ) (heven : Even k) : RealFrame (restoreRegisters registers) k := by
  induction registers with
  | nil => trivial
  | cons j rest ih =>
    refine ⟨?_,ih⟩
    have hs : shadowReg j ≠ k := by obtain ⟨q,hq⟩ := heven;dsimp [shadowReg];omega
    simp [restoreOne,Structured.sequence,RealFrame,Structured.natural,nadd,loadN,load,writesReal,hs]
end RegisterSave
namespace SourceSetup
lemma nat_even_frame (N entry k : ℕ) (hk : 10 ≤ k) (hev : Even k) (h52 : k ≠ 52) (h54 : k ≠ 54) : NatFrame (code N entry) k := by
  refine ⟨?_,RegisterSave.restoreRegisters_nat_even _ k hev h52 h54⟩
  simp only [header,headerAtoms,List.map_cons,List.map_nil,Structured.sequence,NatFrame,writesNat]
  repeat' (first | apply And.intro | omega | trivial)
lemma real_even_frame (N entry k : ℕ) (hk : 10 ≤ k) (hev : Even k) : RealFrame (code N entry) k := by
  refine ⟨?_,RegisterSave.restoreRegisters_real_even _ k hev⟩
  simp only [header,headerAtoms,List.map_cons,List.map_nil,Structured.sequence,RealFrame,writesReal]
  repeat' (first | apply And.intro | omega | trivial)
end SourceSetup
lemma observedAction_nat_even_frame (ins : Instruction) (k : ℕ) (hk : 14 ≤ k) (hev : Even k) : NatFrame (observedAction ins) k := by
  have ha := shadowAction_even_frame ins k (by omega) hev
  have hh := appendStoreReport_nat_frame k (by omega) (by omega)
  cases ins <;> first | exact ha | exact ⟨ha,hh⟩
lemma observedAction_real_even_frame (ins : Instruction) (k : ℕ) (hev : Even k) : RealFrame (observedAction ins) k := by
  have ha := shadowAction_real_even_frame ins k hev
  have hh := appendStoreReport_real_frame k
  cases ins <;> first | exact ha | exact ⟨ha,hh⟩
lemma observedDispatchAux_nat_even_frame (code : List Instruction) (pc k : ℕ) (hk : 14 ≤ k) (hev : Even k) :
    NatFrame (observedDispatchAux pc code) k := by
  induction code generalizing pc with
  | nil => exact ⟨by change 5 ≠ k;omega,by change 4 ≠ k;omega⟩
  | cons ins rest ih =>
    refine ⟨?_,⟨?_,observedAction_nat_even_frame ins k hk hev⟩,ih (pc+1)⟩
    · change 8 ≠ k
      omega
    · change (2 ≠ k) ∧ (3 ≠ k)
      constructor <;> omega
lemma observedDispatchAux_real_even_frame (code : List Instruction) (pc k : ℕ) (hev : Even k) :
    RealFrame (observedDispatchAux pc code) k := by
  induction code generalizing pc with
  | nil => exact ⟨not_false,not_false⟩
  | cons ins rest ih => exact ⟨not_false,⟨⟨not_false,not_false⟩,observedAction_real_even_frame ins k hev⟩,ih (pc+1)⟩
end DecrAlmostLinearSSSP.Decremental
end s125
section s126
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.SourceSnapshot
open Structured
open RegisterSave
lemma work_eval (s : Data) : Eval workCode s 3 (workData s) := eval_sequence_atoms workAtoms s
lemma work_nat_mem (s : Data) :
    (workData s).natMem = Function.update s.natMem (s.natReg 106+6) (s.natReg 3) := by
  simp [workData,workAtoms,Atom.effect,instructionEffect,data,Data.machine]
lemma work_real_mem (s : Data) : (workData s).realMem = s.realMem := rfl
lemma nat_frame (N k : ℕ) (h52 : k ≠ 52) (h54 : k ≠ 54) : NatFrame (code N) k := by
  refine ⟨saveRegisters_nat_frame _ k h52 h54,?_⟩
  simp [workCode,workAtoms,Structured.sequence,NatFrame,writesNat,Ne.symm h52,Ne.symm h54]
lemma eval_code (N : ℕ) (s : Data) (hbase : s.natReg 50 = s.natReg 106+8) :
    ∃ t, Eval (code N) s (4*N+3) t ∧
      t.natMem (s.natReg 106+6) = s.natReg 3 ∧
      (∀ j < N, t.natMem (s.natReg 50+2*j) = s.natReg (shadowReg j) ∧
        t.realMem (s.natReg 50+2*j) = s.realReg (shadowReg j)) ∧
      (∀ address, address ≠ s.natReg 106+6 → (∀ j < N, address ≠ s.natReg 50+2*j) →
        t.natMem address = s.natMem address ∧ t.realMem address = s.realMem address) := by
  obtain ⟨a,ha,haBase,haRegs,haValues,haFrame⟩ := eval_saveRegisters (List.range N) List.nodup_range s
  have ha106 : a.natReg 106 = s.natReg 106 := ha.nat_frame (saveRegisters_nat_frame _ 106 (by omega) (by omega))
  have ha3 : a.natReg 3 = s.natReg 3 := ha.nat_frame (saveRegisters_nat_frame _ 3 (by omega) (by omega))
  refine ⟨workData a,?_,?_,?_,?_⟩
  · simpa only [code,List.length_range] using Eval.seq ha (work_eval a)
  · rw [work_nat_mem,ha106,Function.update_self,ha3]
  · intro j hj
    have hne : s.natReg 50+2*j ≠ a.natReg 106+6 := by rw [ha106,hbase];omega
    have hv := haValues j (List.mem_range.mpr hj)
    rw [work_nat_mem,Function.update_of_ne hne,work_real_mem]
    exact hv
  · intro address hwork hout
    have hne : address ≠ a.natReg 106+6 := by rwa [ha106]
    rw [work_nat_mem,Function.update_of_ne hne,work_real_mem]
    exact haFrame address (fun j hj => hout j (List.mem_range.mp hj))
lemma guest_bank_protected (B bank record a : ℕ) (hrecord : ∃ r, record = B+2*r+1) :
    B+bankFactor bank*(2*a+1) ≠ record+6 ∧ ∀ j, B+bankFactor bank*(2*a+1) ≠ (record+8)+2*j := by
  obtain ⟨r,rfl⟩ := hrecord
  constructor
  · have heq : B+2*r+1+6 = B+(2*(r+3)+1) := by ring
    rw [heq]
    exact guest_bank_ne_host B bank a (r+3)
  · intro j
    have heq : B+2*r+1+8+2*j = B+(2*(r+4+j)+1) := by ring
    rw [heq]
    exact guest_bank_ne_host B bank a (r+4+j)
end DecrAlmostLinearSSSP.Decremental.SourceSnapshot
end s126
section s127
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.SourceCall
open Structured
lemma snapshot_real_frame (N k : ℕ) : RealFrame (SourceSnapshot.code N) k := by
  refine ⟨?_,?_⟩
  · have hh : ∀ registers : List ℕ, RealFrame (RegisterSave.saveRegisters registers) k := by
      intro registers
      induction registers with
      | nil => trivial
      | cons j rest ih =>
        refine ⟨?_,ih⟩
        simp [RegisterSave.saveOne,Structured.sequence,RealFrame,natural,nadd,storeN,store,writesReal]
    exact hh _
  · simp [SourceSnapshot.workCode,SourceSnapshot.workAtoms,Structured.sequence,RealFrame,writesReal]
lemma nat_even_frame (N entry : ℕ) (p : Program) (k : ℕ) (hk : 10 ≤ k) (hev : Even k)
    (h52 : k ≠ 52) (h54 : k ≠ 54) : NatFrame (code N entry p) k :=
  ⟨SourceSetup.nat_even_frame N entry k hk hev h52 h54,
    shadowInterpreter_nat_even_frame _ k hk hev,SourceSnapshot.nat_frame N k h52 h54⟩
lemma real_even_frame (N entry : ℕ) (p : Program) (k : ℕ) (hk : 10 ≤ k) (hev : Even k) : RealFrame (code N entry p) k :=
  ⟨SourceSetup.real_even_frame N entry k hk hev,shadowInterpreter_real_even_frame _ k hev,snapshot_real_frame N k⟩
lemma eval_code (N entry B bank : ℕ) (s : Data) (p : Program) (g final : Machine)
    (hB : s.natReg 74 = B) (hF : s.natReg 112 = bankFactor bank) (hz : s.natReg 56 = 0)
    (hentry : g.pc = entry) (hwork : s.natMem (s.natReg 106+6) = g.work)
    (hhalt : g.halted = false) (hfault : g.fault = false)
    (hmr : ∀ a, s.realMem (B+bankFactor bank*(2*a+1)) = g.realMem a)
    (hmn : ∀ a, s.natMem (B+bankFactor bank*(2*a+1)) = bankFactor bank*g.natMem a)
    (hsaved : ∀ j < N, s.natMem (s.natReg 50+2*j) = bankFactor bank*g.natReg j ∧ s.realMem (s.natReg 50+2*j) = g.realReg j)
    (htail : ∀ j, N ≤ j → s.natReg (shadowReg j) = 0 ∧ s.realReg (shadowReg j) = 0)
    (hgtail : ZeroRegisterTail N g) (he : Ends p g final)
    (hbase : s.natReg 50 = s.natReg 106+8) (hrecord : ∃ r, s.natReg 106 = B+2*r+1) :
    ∃ cost t, Eval (code N entry p) s cost t ∧
      cost ≤ (dispatchCharge p.code+2)*(final.work-g.work)+8*N+15 ∧
      ShadowDataRep B (bankFactor bank) t final ∧
      t.natMem (s.natReg 106+6) = final.work ∧
      (∀ j < N, t.natMem (s.natReg 50+2*j) = bankFactor bank*final.natReg j ∧
        t.realMem (s.natReg 50+2*j) = final.realReg j) ∧
      (∀ address, (∀ a, address ≠ B+bankFactor bank*(2*a+1)) →
        address ≠ s.natReg 106+6 → (∀ j < N, address ≠ s.natReg 50+2*j) →
        t.natMem address = s.natMem address ∧ t.realMem address = s.realMem address) := by
  obtain ⟨a,ha,harep,ha0,ha1,ha7,har7,ha4,hamr,hamn⟩ := SourceSetup.eval_code N entry B (bankFactor bank) s g
    hB hF hz hentry hwork hhalt hfault hmr hmn hsaved htail hgtail
  obtain ⟨c,b,hb,hcost,hbrep,hbframe⟩ := eval_shadow_call p B (bankFactor bank) (bankFactor_positive bank)
    a g final harep ha0 ha1 ha7 har7 (by omega) he
  have ha50 : a.natReg 50 = s.natReg 50 := ha.nat_frame (SourceSetup.nat_even_frame N entry 50 (by omega) (by decide) (by omega) (by omega))
  have ha106 : a.natReg 106 = s.natReg 106 := ha.nat_frame (SourceSetup.nat_even_frame N entry 106 (by omega) (by decide) (by omega) (by omega))
  have hb50 : b.natReg 50 = s.natReg 50 := (hb.nat_frame (shadowInterpreter_nat_even_frame _ 50 (by omega) (by decide))).trans ha50
  have hb106 : b.natReg 106 = s.natReg 106 := (hb.nat_frame (shadowInterpreter_nat_even_frame _ 106 (by omega) (by decide))).trans ha106
  have hbbase : b.natReg 50 = b.natReg 106+8 := by rw [hb50,hb106];exact hbase
  obtain ⟨t,ht,htwork,htsaved,htframe⟩ := SourceSnapshot.eval_code N b hbbase
  have htmeta (k : ℕ) (h52 : k ≠ 52) (h54 : k ≠ 54) : t.natReg k = b.natReg k :=
    ht.nat_frame (SourceSnapshot.nat_frame N k h52 h54)
  have htsourceMem (a : ℕ) : t.natMem (B+bankFactor bank*(2*a+1)) = b.natMem (B+bankFactor bank*(2*a+1)) ∧
      t.realMem (B+bankFactor bank*(2*a+1)) = b.realMem (B+bankFactor bank*(2*a+1)) := by
    have hh := SourceSnapshot.guest_bank_protected B bank (s.natReg 106) a hrecord
    apply htframe
    · simpa only [hb106] using hh.1
    · simpa only [hb50,hbase] using fun j (_ : j < N) => hh.2 j
  have htrep : ShadowDataRep B (bankFactor bank) t final := by
    refine ⟨(htmeta 2 (by omega) (by omega)).trans hbrep.pc,
      (htmeta 3 (by omega) (by omega)).trans hbrep.work,?_,?_,?_,?_,?_,?_⟩
    · change (t.natReg 4 == 1) = final.halted
      rw [htmeta 4 (by omega) (by omega)]
      exact hbrep.halted
    · change (t.natReg 5 == 1) = final.fault
      rw [htmeta 5 (by omega) (by omega)]
      exact hbrep.fault
    · intro j
      exact (ht.real_frame (snapshot_real_frame N (shadowReg j))).trans (hbrep.realReg j)
    · intro j
      have h52 := shadowReg_ne_even j 26
      have h54 := shadowReg_ne_even j 27
      exact (htmeta _ h52 h54).trans (hbrep.natReg j)
    · intro a
      exact (htsourceMem a).2.trans (hbrep.realMem a)
    · intro a
      exact (htsourceMem a).1.trans (hbrep.natMem a)
  refine ⟨(10+4*N)+(c+(4*N+3)),t,Eval.seq ha (Eval.seq hb ht),by omega,htrep,?_,?_,?_⟩
  · have hh : t.natMem (s.natReg 106+6) = b.natReg 3 := by simpa only [hb106] using htwork
    exact hh.trans hbrep.work
  · intro j hj
    have hh := htsaved j hj
    refine ⟨?_,?_⟩
    · have hn : t.natMem (s.natReg 50+2*j) = b.natReg (shadowReg j) := by simpa only [hb50] using hh.1
      exact hn.trans (hbrep.natReg j)
    · have hr : t.realMem (s.natReg 50+2*j) = b.realReg (shadowReg j) := by simpa only [hb50] using hh.2
      exact hr.trans (hbrep.realReg j)
  · intro address hbank hwork' hsaved'
    have hh := htframe address (by simpa only [hb106] using hwork') (by simpa only [hb50] using hsaved')
    have hg := hbframe address hbank
    exact ⟨hh.1.trans (hg.2.trans (congrFun hamn address)),hh.2.trans (hg.1.trans (congrFun hamr address))⟩
end DecrAlmostLinearSSSP.Decremental.SourceCall
end s127
section s128
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.ExtendedMax
open Structured
attribute [local instance] Classical.propDecidable
lemma eval_code (s : Data) (h26 : s.natReg 26 = 1) (hflag : s.natReg 22 ≤ 1)
    (hold : s.natMem (s.natReg 20) ≤ 1)
    (hnew : s.natReg 22 = 0 → 0 ≤ s.realReg 20)
    (hval : s.natMem (s.natReg 20) = 0 → 0 ≤ s.realMem (s.natReg 20)) :
    ∃ cost t, Eval code s cost t ∧ cost ≤ 6 ∧
      t.natMem (s.natReg 20) ≤ 1 ∧
      (t.natMem (s.natReg 20) = 0 → 0 ≤ t.realMem (s.natReg 20)) ∧
      cell t (s.natReg 20) = max (cell s (s.natReg 20)) (incoming s) ∧
      ∀ address, address ≠ s.natReg 20 → t.realMem address = s.realMem address ∧ t.natMem address = s.natMem address := by
  classical
  let a : Data := {s with natReg := Function.update s.natReg 24 (s.natMem (s.natReg 20))}
  have ha : Eval (loadN 24 20) s 1 a := eval_loadN s 24 20
  by_cases ho : s.natMem (s.natReg 20) = 0
  · have htest : (Test.natLess 24 26).holds a := by simp [Test.holds,a,h26,ho]
    by_cases hn : s.natReg 22 = 0
    · have hntest : (Test.natLess 22 26).holds a := by simp [Test.holds,a,h26,hn]
      let b : Data := {a with realReg := Function.update a.realReg 22 (a.realMem (a.natReg 20))}
      have hb : Eval (load 22 20) a 1 b := eval_load a 22 20
      by_cases hlt : s.realMem (s.natReg 20) < s.realReg 20
      · let t : Data := {b with realMem := Function.update b.realMem (b.natReg 20) (b.realReg 20)}
        have ht : (Test.realLess 22 20).holds b := by simpa [Test.holds,b,a] using hlt
        refine ⟨6,t,Eval.seq ha (Eval.branchYes htest (Eval.branchYes hntest
          (Eval.seq hb (Eval.branchYes ht (eval_store b 20 20))))),le_rfl,?_,?_,?_,?_⟩
        · simp [t,b,a,ho]
        · intro hh
          simpa [t,b,a] using hnew hn
        · have hle : ENNReal.ofReal (s.realMem (s.natReg 20)) ≤ ENNReal.ofReal (s.realReg 20) :=
            ENNReal.ofReal_le_ofReal hlt.le
          simp [cell,incoming,t,b,a,ho,hn,max_eq_right hle]
        · intro address had
          simp [t,b,a,Function.update_of_ne had]
      · have ht : ¬(Test.realLess 22 20).holds b := by simpa [Test.holds,b,a] using hlt
        refine ⟨6,b,Eval.seq ha (Eval.branchYes htest (Eval.branchYes hntest
          (Eval.seq hb (Eval.branchNo ht (.skip b))))),le_rfl,?_,?_,?_,?_⟩
        · simpa [b,a] using hold
        · simpa [b,a] using hval
        · have hle : ENNReal.ofReal (s.realReg 20) ≤ ENNReal.ofReal (s.realMem (s.natReg 20)) :=
            ENNReal.ofReal_le_ofReal (le_of_not_gt hlt)
          simp [cell,incoming,b,a,ho,hn,max_eq_left hle]
        · intro address had
          exact ⟨rfl,rfl⟩
    · have hn1 : s.natReg 22 = 1 := by omega
      have hntest : ¬(Test.natLess 22 26).holds a := by simp [Test.holds,a,h26,hn1]
      let t : Data := {a with natMem := Function.update a.natMem (a.natReg 20) (a.natReg 22)}
      refine ⟨5,t,Eval.seq ha (Eval.branchYes htest (Eval.branchNo hntest (eval_storeN a 20 22))),by omega,?_,?_,?_,?_⟩
      · simp [t,a,hn1]
      · simp [t,a,hn1]
      · simp [cell,incoming,t,a,hn1]
      · intro address had
        simp [t,a,Function.update_of_ne had]
  · have ho1 : s.natMem (s.natReg 20) = 1 := by omega
    have htest : ¬(Test.natLess 24 26).holds a := by simp [Test.holds,a,h26,ho1]
    refine ⟨3,a,Eval.seq ha (Eval.branchNo htest (.skip a)),by omega,?_,?_,?_,?_⟩
    · simpa [a] using hold
    · simpa [a] using hval
    · simp [cell,a,ho1]
    · intro address had
      exact ⟨rfl,rfl⟩
end DecrAlmostLinearSSSP.Decremental.ExtendedMax
end s128
section s129
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.ScaledReadout
open Structured
lemma eval_code (s : Data) (F flag : ℕ) (delta r : ℝ) (hF : 0 < F) (hdelta : 0 < delta)
    (hfactor : s.natReg 132 = F) (hd : s.realReg 70 = delta)
    (hflag : flag ≤ 1) (hn : s.natMem (s.natReg 128) = F*flag)
    (hr : s.realMem (s.natReg 128) = r) (hfinite : flag = 0 → 0 ≤ r) :
    ∃ cost t, Eval code s cost t ∧ cost ≤ 6 ∧ t.natReg 22 = flag ∧ t.realReg 20 = delta*r ∧
      (t.natReg 22 = 0 → 0 ≤ t.realReg 20) ∧
      ExtendedMax.incoming t = ENNReal.ofReal delta*(if flag = 1 then ⊤ else ENNReal.ofReal r) ∧
      t.realMem = s.realMem ∧ t.natMem = s.natMem := by
  let a : Data := {s with natReg := Function.update s.natReg 130 (F*flag)}
  let b : Data := {a with realReg := Function.update a.realReg 20 r}
  let c : Data := {b with realReg := Function.update b.realReg 20 (r*delta)}
  have ha : Eval (loadN 130 128) s 1 a := by simpa only [hn,a] using eval_loadN s 130 128
  have hb : Eval (load 20 128) a 1 b := by simpa [a,b,hr] using eval_load a 20 128
  have hc : Eval (mul 20 20 70) b 1 c := by simpa [b,c,a,hd] using eval_mul b 20 20 70
  have hp : Eval (Structured.sequence [loadN 130 128,load 20 128,mul 20 20 70]) s 3 c :=
    Eval.seq ha (Eval.seq hb (Eval.seq hc (Eval.skip c)))
  by_cases hf0 : flag = 0
  · have ht : (Test.natLess 130 132).holds c := by simpa [Test.holds,c,b,a,hfactor,hf0] using hF
    let t : Data := {c with natReg := Function.update c.natReg 22 0}
    refine ⟨5,t,Eval.seq hp (Eval.branchYes ht (eval_natural c 22 0)),by omega,?_,?_,?_,?_,rfl,rfl⟩
    · simp [t,hf0]
    · simp [t,c,mul_comm]
    · intro hzero
      simpa [t,c,mul_comm] using mul_nonneg hdelta.le (hfinite hf0)
    · simp [ExtendedMax.incoming,t,c,hf0,← ENNReal.ofReal_mul hdelta.le,mul_comm]
  · have hf1 : flag = 1 := by omega
    have ht : ¬(Test.natLess 130 132).holds c := by simp [Test.holds,c,b,a,hfactor,hf1]
    let t : Data := {c with natReg := Function.update c.natReg 22 1}
    refine ⟨6,t,Eval.seq hp (Eval.branchNo ht (eval_natural c 22 1)),le_rfl,?_,?_,?_,?_,rfl,rfl⟩
    · simp [t,hf1]
    · simp [t,c,mul_comm]
    · simp [t]
    · have hd0 : ENNReal.ofReal delta ≠ 0 := (ENNReal.ofReal_pos.mpr hdelta).ne'
      simp [ExtendedMax.incoming,t,hf1,ENNReal.mul_top hd0]
lemma no_memory : NoMemory code := by
  simp [code,Structured.sequence,NoMemory,loadN,load,mul,Structured.natural,NoStore]
end DecrAlmostLinearSSSP.Decremental.ScaledReadout
end s129
section s130
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CacheCopy
open Structured
lemma suffix_eval (s : Data) : Eval suffix s 5 (suffixData s) := by
  have hh := Eval.seq (eval_storeN s 20 22) (Eval.seq (eval_store _ 20 20)
    (Eval.seq (eval_nadd _ 20 20 14) (Eval.seq (eval_nadd _ 128 128 170)
      (Eval.seq (eval_nsub _ 176 176 26) (Eval.skip _)))))
  simpa [suffix,Structured.sequence,suffixData] using hh
lemma read_nat_frame (k : ℕ) (h22 : k ≠ 22) (h130 : k ≠ 130) : NatFrame ScaledReadout.code k := by
  simp [ScaledReadout.code,Structured.sequence,NatFrame,writesNat,loadN,load,mul,natural,
    Ne.symm h22,Ne.symm h130]
lemma read_real_frame (k : ℕ) (h20 : k ≠ 20) : RealFrame ScaledReadout.code k := by
  simp [ScaledReadout.code,Structured.sequence,RealFrame,writesReal,loadN,load,mul,natural,Ne.symm h20]
lemma body_eval (s : Data) (F flag : ℕ) (delta r : ℝ) (hF : 0 < F) (hdelta : 0 < delta)
    (hfactor : s.natReg 132 = F) (hd : s.realReg 70 = delta)
    (hflag : flag ≤ 1) (hn : s.natMem (s.natReg 128) = F*flag)
    (hr : s.realMem (s.natReg 128) = r) (hfinite : flag = 0 → 0 ≤ r)
    (h1 : s.natReg 26 = 1) (h2 : s.natReg 14 = 2) :
    ∃ cost t, Eval body s cost t ∧ cost ≤ 11 ∧
      t.natReg 20 = s.natReg 20+2 ∧ t.natReg 128 = s.natReg 128+s.natReg 170 ∧
      t.natReg 176 = s.natReg 176-1 ∧
      t.natMem (s.natReg 20) = flag ∧ t.realMem (s.natReg 20) = delta*r ∧
      (∀ address, address ≠ s.natReg 20 →
        t.natMem address = s.natMem address ∧ t.realMem address = s.realMem address) := by
  obtain ⟨c,u,hu,hc,huf,hur,_,_,hmr,hmn⟩ := ScaledReadout.eval_code s F flag delta r hF hdelta hfactor hd hflag hn hr hfinite
  have hureg (k : ℕ) (h22 : k ≠ 22) (h130 : k ≠ 130) : u.natReg k = s.natReg k :=
    hu.nat_frame (read_nat_frame k h22 h130)
  have hu20 : u.natReg 20 = s.natReg 20 := hureg 20 (by omega) (by omega)
  have hu14 : u.natReg 14 = 2 := (hureg 14 (by omega) (by omega)).trans h2
  have hu26 : u.natReg 26 = 1 := (hureg 26 (by omega) (by omega)).trans h1
  have hu128 : u.natReg 128 = s.natReg 128 := hureg 128 (by omega) (by omega)
  have hu170 : u.natReg 170 = s.natReg 170 := hureg 170 (by omega) (by omega)
  have hu176 : u.natReg 176 = s.natReg 176 := hureg 176 (by omega) (by omega)
  let t := suffixData u
  refine ⟨c+5,t,Eval.seq hu (suffix_eval u),by omega,?_,?_,?_,?_,?_,?_⟩
  · simp [t,suffixData,hu20,hu14]
  · simp [t,suffixData,hu128,hu170]
  · simp [t,suffixData,hu176,hu26]
  · simp [t,suffixData,hu20,huf]
  · simp [t,suffixData,hu20,hur]
  · intro address ha
    simp [t,suffixData,hu20,Function.update_of_ne ha,hmn,hmr]
lemma nat_frame (k : ℕ) (h20 : k ≠ 20) (h22 : k ≠ 22) (h128 : k ≠ 128)
    (h130 : k ≠ 130) (h176 : k ≠ 176) : NatFrame body k := by
  simp [body,suffix,Structured.sequence,NatFrame,read_nat_frame k h22 h130,
    writesNat,storeN,store,nadd,nsub,Ne.symm h20,Ne.symm h128,Ne.symm h176]
lemma real_frame (k : ℕ) (h20 : k ≠ 20) : RealFrame body k := by
  simp [body,suffix,Structured.sequence,RealFrame,read_real_frame k h20,
    writesReal,storeN,store,nadd,nsub]
end DecrAlmostLinearSSSP.Decremental.CacheCopy
end s130
section s131
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CacheCopy
open Structured
lemma eval_code (count sourceBase cacheBase stride F : ℕ) (delta : ℝ)
    (flags : ℕ → ℕ) (values : ℕ → ℝ) (s : Data)
    (hF : 0 < F) (hdelta : 0 < delta)
    (hfactor : s.natReg 132 = F) (hd : s.realReg 70 = delta)
    (hs : s.natReg 128 = sourceBase) (hc : s.natReg 20 = cacheBase)
    (hst : s.natReg 170 = stride) (hcount : s.natReg 176 = count)
    (hz : s.natReg 56 = 0) (h1 : s.natReg 26 = 1) (h2 : s.natReg 14 = 2)
    (hflags : ∀ j < count, flags j ≤ 1)
    (hfinite : ∀ j < count, flags j = 0 → 0 ≤ values j)
    (hn : ∀ j < count, s.natMem (sourceBase+stride*j) = F*flags j)
    (hr : ∀ j < count, s.realMem (sourceBase+stride*j) = values j)
    (hseparate : ∀ j < count, ∀ k < count, sourceBase+stride*j ≠ cacheBase+2*k) :
    ∃ cost t, Eval code s cost t ∧ cost ≤ 13*count+2 ∧
      t.natReg 128 = sourceBase+stride*count ∧ t.natReg 20 = cacheBase+2*count ∧
      t.natReg 176 = 0 ∧
      (∀ j < count, t.natMem (cacheBase+2*j) = flags j ∧
        t.realMem (cacheBase+2*j) = delta*values j) ∧
      (∀ address, (∀ j < count, address ≠ cacheBase+2*j) →
        t.natMem address = s.natMem address ∧ t.realMem address = s.realMem address) := by
  induction count generalizing sourceBase cacheBase flags values s with
  | zero =>
    have ht : ¬(Test.natLess 56 176).holds s := by simp [Test.holds,hz,hcount]
    exact ⟨2,s,Eval.loopNo s ht,by simp,by simpa using hs,by simpa using hc,hcount,by simp,fun _ _ => ⟨rfl,rfl⟩⟩
  | succ count ih =>
    have hn0 : s.natMem (s.natReg 128) = F*flags 0 := by simpa only [hs,Nat.mul_zero,Nat.add_zero] using hn 0 (by omega)
    have hr0 : s.realMem (s.natReg 128) = values 0 := by simpa only [hs,Nat.mul_zero,Nat.add_zero] using hr 0 (by omega)
    obtain ⟨c,u,hu,hcost,hu20,hu128,hu176,hun,hur,huframe⟩ := body_eval s F (flags 0) delta (values 0)
      hF hdelta hfactor hd (hflags 0 (by omega)) hn0 hr0 (hfinite 0 (by omega)) h1 h2
    have hnat (k : ℕ) (h20 : k ≠ 20) (h22 : k ≠ 22) (h128 : k ≠ 128)
        (h130 : k ≠ 130) (h176 : k ≠ 176) : u.natReg k = s.natReg k :=
      hu.nat_frame (nat_frame k h20 h22 h128 h130 h176)
    have hreal (k : ℕ) (h20 : k ≠ 20) : u.realReg k = s.realReg k := hu.real_frame (real_frame k h20)
    have hufactor : u.natReg 132 = F := (hnat 132 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hfactor
    have hud : u.realReg 70 = delta := (hreal 70 (by omega)).trans hd
    have hust : u.natReg 170 = stride := (hnat 170 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hst
    have huz : u.natReg 56 = 0 := (hnat 56 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hz
    have hu1 : u.natReg 26 = 1 := (hnat 26 (by omega) (by omega) (by omega) (by omega) (by omega)).trans h1
    have hu2 : u.natReg 14 = 2 := (hnat 14 (by omega) (by omega) (by omega) (by omega) (by omega)).trans h2
    have hus : u.natReg 128 = sourceBase+stride := by simpa only [hs,hst] using hu128
    have huc : u.natReg 20 = cacheBase+2 := by simpa only [hc] using hu20
    have hucount : u.natReg 176 = count := by simpa only [hcount,Nat.succ_sub_one] using hu176
    have htailNat : ∀ j < count, u.natMem (sourceBase+stride+stride*j) = F*flags (j+1) := by
      intro j hj
      have heq : sourceBase+stride+stride*j = sourceBase+stride*(j+1) := by ring
      have hne : sourceBase+stride+stride*j ≠ s.natReg 20 := by
        rw [hc,heq]
        simpa only [Nat.mul_zero,Nat.add_zero] using hseparate (j+1) (by omega) 0 (by omega)
      rw [(huframe _ hne).1,heq]
      exact hn (j+1) (by omega)
    have htailReal : ∀ j < count, u.realMem (sourceBase+stride+stride*j) = values (j+1) := by
      intro j hj
      have heq : sourceBase+stride+stride*j = sourceBase+stride*(j+1) := by ring
      have hne : sourceBase+stride+stride*j ≠ s.natReg 20 := by
        rw [hc,heq]
        simpa only [Nat.mul_zero,Nat.add_zero] using hseparate (j+1) (by omega) 0 (by omega)
      rw [(huframe _ hne).2,heq]
      exact hr (j+1) (by omega)
    have htailSeparate : ∀ j < count, ∀ k < count,
        sourceBase+stride+stride*j ≠ cacheBase+2+2*k := by
      intro j hj k hk
      have heq1 : sourceBase+stride+stride*j = sourceBase+stride*(j+1) := by ring
      have heq2 : cacheBase+2+2*k = cacheBase+2*(k+1) := by omega
      rw [heq1,heq2]
      exact hseparate (j+1) (by omega) (k+1) (by omega)
    obtain ⟨rest,t,ht,htcost,hts,htc,htcount,htcells,htframe⟩ :=
      ih (sourceBase+stride) (cacheBase+2) (fun j => flags (j+1)) (fun j => values (j+1)) u
        hufactor hud hus huc hust hucount huz hu1 hu2
        (fun j hj => hflags (j+1) (by omega)) (fun j hj => hfinite (j+1) (by omega))
        htailNat htailReal htailSeparate
    have htest : (Test.natLess 56 176).holds s := by simp [Test.holds,hz,hcount]
    refine ⟨c+rest+2,t,Eval.loopYes htest hu ht,by omega,?_,?_,htcount,?_,?_⟩
    · rw [hts]
      ring
    · omega
    · intro j hj
      by_cases hj0 : j = 0
      · subst j
        have hout : ∀ k < count, cacheBase+2*0 ≠ cacheBase+2+2*k := by intro k hk;omega
        have hh := htframe (cacheBase+2*0) hout
        simpa only [hc,Nat.mul_zero,Nat.add_zero] using And.intro (hh.1.trans (by simpa only [hc,Nat.mul_zero,Nat.add_zero] using hun)) (hh.2.trans (by simpa only [hc,Nat.mul_zero,Nat.add_zero] using hur))
      · obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
        have hk : k < count := by omega
        have heq : cacheBase+2+2*k = cacheBase+2*(k+1) := by omega
        simpa only [heq] using htcells k hk
    · intro address hout
      have htail : ∀ j < count, address ≠ cacheBase+2+2*j := by
        intro j hj
        have heq : cacheBase+2+2*j = cacheBase+2*(j+1) := by omega
        rw [heq]
        exact hout (j+1) (by omega)
      have hh := htframe address htail
      have hhead : address ≠ s.natReg 20 := by rw [hc];simpa only [Nat.mul_zero,Nat.add_zero] using hout 0 (by omega)
      have hheadFrame := huframe address hhead
      exact ⟨hh.1.trans hheadFrame.1,hh.2.trans hheadFrame.2⟩
end DecrAlmostLinearSSSP.Decremental.CacheCopy
end s131
section s132
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.CacheCopy
open Structured
lemma eval_source (B bank cacheOffset count : ℕ) (delta : ℝ) (s : Data) (g : Machine)
    (hrep : ShadowDataRep B (bankFactor bank) s g) (hdpos : 0 < delta)
    (hfactor : s.natReg 132 = bankFactor bank) (hd : s.realReg 70 = delta)
    (hs : s.natReg 128 = B+bankFactor bank) (hc : s.natReg 20 = B+2*cacheOffset+1)
    (hst : s.natReg 170 = 2*bankFactor bank) (hcount : s.natReg 176 = count)
    (hz : s.natReg 56 = 0) (h1 : s.natReg 26 = 1) (h2 : s.natReg 14 = 2)
    (hflags : ∀ v : Fin count, g.natMem v.val ≤ 1)
    (hfinite : ∀ v : Fin count, g.natMem v.val = 0 → 0 ≤ g.realMem v.val) :
    ∃ cost t, Eval code s cost t ∧ cost ≤ 13*count+2 ∧
      (∀ v : Fin count,
        t.natMem (B+2*cacheOffset+1+2*v.val) = g.natMem v.val ∧
        t.realMem (B+2*cacheOffset+1+2*v.val) = delta*g.realMem v.val ∧
        ExtendedMax.cell t (B+2*cacheOffset+1+2*v.val) = ENNReal.ofReal delta*stored g v.val) ∧
      (∀ address, (∀ j < count, address ≠ B+2*cacheOffset+1+2*j) →
        t.natMem address = s.natMem address ∧ t.realMem address = s.realMem address) ∧
      (∀ a, t.natMem (B+bankFactor bank*(2*a+1)) = s.natMem (B+bankFactor bank*(2*a+1)) ∧
        t.realMem (B+bankFactor bank*(2*a+1)) = s.realMem (B+bankFactor bank*(2*a+1))) := by
  have haddr (j : ℕ) : B+bankFactor bank+(2*bankFactor bank)*j = B+bankFactor bank*(2*j+1) := by ring
  have hsep (j k : ℕ) : B+bankFactor bank+(2*bankFactor bank)*j ≠ B+2*cacheOffset+1+2*k := by
    rw [haddr]
    have heq : B+2*cacheOffset+1+2*k = B+(2*(cacheOffset+k)+1) := by ring
    rw [heq]
    exact guest_bank_ne_host B bank j (cacheOffset+k)
  obtain ⟨cost,t,he,hcost,_,_,_,hcells,hframe⟩ := eval_code count (B+bankFactor bank)
    (B+2*cacheOffset+1) (2*bankFactor bank) (bankFactor bank) delta g.natMem g.realMem s
      (bankFactor_positive bank) hdpos hfactor hd hs hc hst hcount hz h1 h2
      (fun j hj => hflags ⟨j,hj⟩) (fun j hj => hfinite ⟨j,hj⟩)
      (by intro j hj;rw [haddr];exact hrep.natMem j)
      (by intro j hj;rw [haddr];exact hrep.realMem j)
      (fun j _ k _ => hsep j k)
  refine ⟨cost,t,he,hcost,?_,hframe,?_⟩
  · intro v
    obtain ⟨hn,hr⟩ := hcells v.val v.isLt
    refine ⟨hn,hr,?_⟩
    by_cases hf0 : g.natMem v.val = 0
    · simp [ExtendedMax.cell,stored,hn,hr,hf0,← ENNReal.ofReal_mul hdpos.le]
    · have hf1 : g.natMem v.val = 1 := by have hh := hflags v;omega
      have hd0 : ENNReal.ofReal delta ≠ 0 := (ENNReal.ofReal_pos.mpr hdpos).ne'
      simp [ExtendedMax.cell,stored,hn,hf1,ENNReal.mul_top hd0]
  · intro a
    apply hframe
    intro j hj
    have heq : B+bankFactor bank*(2*a+1) = B+bankFactor bank+(2*bankFactor bank)*a := (haddr a).symm
    rw [heq]
    exact hsep a j
end DecrAlmostLinearSSSP.Decremental.CacheCopy
end s132
section s133
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CacheCopy
open Structured
lemma setup_eval (s : Data) : Eval setup s 5 (setupData s) := eval_sequence_atoms setupAtoms s
lemma setup_fields (s : Data) (hz : s.natReg 56 = 0) :
    (setupData s).natReg 128 = s.natReg 74+s.natReg 112 ∧
    (setupData s).natReg 132 = s.natReg 112 ∧ (setupData s).natReg 170 = 2*s.natReg 112 ∧
    (setupData s).natReg 20 = s.natReg 108 ∧ (setupData s).natReg 176 = s.natReg 66 := by
  simp [setupData,setupAtoms,Atom.effect,instructionEffect,data,Data.machine,hz,two_mul]
lemma setup_nat_frame (k : ℕ) (h128 : k ≠ 128) (h132 : k ≠ 132) (h170 : k ≠ 170)
    (h20 : k ≠ 20) (h176 : k ≠ 176) : NatFrame setup k := by
  simp [setup,setupAtoms,Structured.sequence,NatFrame,writesNat,Ne.symm h128,Ne.symm h132,Ne.symm h170,Ne.symm h20,Ne.symm h176]
lemma setup_real_frame (k : ℕ) : RealFrame setup k := by
  simp [setup,setupAtoms,Structured.sequence,RealFrame,writesReal]
lemma call_source (B bank cacheOffset count : ℕ) (delta : ℝ) (s : Data) (g : Machine)
    (hrep : ShadowDataRep B (bankFactor bank) s g) (hdpos : 0 < delta)
    (hB : s.natReg 74 = B) (hF : s.natReg 112 = bankFactor bank)
    (hc : s.natReg 108 = B+2*cacheOffset+1) (hn : s.natReg 66 = count)
    (hd : s.realReg 70 = delta) (hz : s.natReg 56 = 0) (h1 : s.natReg 26 = 1) (h2 : s.natReg 14 = 2)
    (hflags : ∀ v : Fin count, g.natMem v.val ≤ 1)
    (hfinite : ∀ v : Fin count, g.natMem v.val = 0 → 0 ≤ g.realMem v.val) :
    ∃ cost t, Eval call s cost t ∧ cost ≤ 13*count+7 ∧
      (∀ v : Fin count, t.natMem (B+2*cacheOffset+1+2*v.val) = g.natMem v.val ∧
        t.realMem (B+2*cacheOffset+1+2*v.val) = delta*g.realMem v.val ∧
        ExtendedMax.cell t (B+2*cacheOffset+1+2*v.val) = ENNReal.ofReal delta*stored g v.val) ∧
      (∀ address, (∀ j < count, address ≠ B+2*cacheOffset+1+2*j) →
        t.natMem address = s.natMem address ∧ t.realMem address = s.realMem address) ∧
      (∀ a, t.natMem (B+bankFactor bank*(2*a+1)) = s.natMem (B+bankFactor bank*(2*a+1)) ∧
        t.realMem (B+bankFactor bank*(2*a+1)) = s.realMem (B+bankFactor bank*(2*a+1))) := by
  let a := setupData s
  have ha := setup_eval s
  have harep : ShadowDataRep B (bankFactor bank) a g := by
    have hnmeta (k : ℕ) (hk : k < 9) : a.natReg k = s.natReg k :=
      ha.nat_frame (setup_nat_frame k (by omega) (by omega) (by omega) (by omega) (by omega))
    refine ⟨(hnmeta 2 (by omega)).trans hrep.pc,(hnmeta 3 (by omega)).trans hrep.work,?_,?_,?_,?_,hrep.realMem,hrep.natMem⟩
    · change (a.natReg 4 == 1) = g.halted
      rw [hnmeta 4 (by omega)]
      exact hrep.halted
    · change (a.natReg 5 == 1) = g.fault
      rw [hnmeta 5 (by omega)]
      exact hrep.fault
    · intro j
      exact (ha.real_frame (setup_real_frame _)).trans (hrep.realReg j)
    · intro j
      exact (ha.nat_frame (setup_nat_frame _ (shadowReg_ne_of_even j 128 (by decide))
        (shadowReg_ne_of_even j 132 (by decide)) (shadowReg_ne_of_even j 170 (by decide))
        (shadowReg_ne_of_even j 20 (by decide)) (shadowReg_ne_of_even j 176 (by decide)))).trans (hrep.natReg j)
  obtain ⟨h128,h132,h170,h20,h176⟩ := setup_fields s hz
  have ha56 : a.natReg 56 = 0 := (ha.nat_frame (setup_nat_frame 56 (by omega) (by omega) (by omega) (by omega) (by omega))).trans hz
  have ha26 : a.natReg 26 = 1 := (ha.nat_frame (setup_nat_frame 26 (by omega) (by omega) (by omega) (by omega) (by omega))).trans h1
  have ha14 : a.natReg 14 = 2 := (ha.nat_frame (setup_nat_frame 14 (by omega) (by omega) (by omega) (by omega) (by omega))).trans h2
  have ha70 : a.realReg 70 = delta := hd
  obtain ⟨c,t,ht,hcost,hvalues,hframe,hbanks⟩ := eval_source B bank cacheOffset count delta a g harep hdpos
    (by simpa only [hF] using h132) ha70 (by simpa only [hB,hF] using h128)
    (by simpa only [hc] using h20) (by simpa only [hF] using h170) (by simpa only [hn] using h176)
    ha56 ha26 ha14 hflags hfinite
  exact ⟨5+c,t,Eval.seq ha ht,by omega,hvalues,hframe,hbanks⟩
end DecrAlmostLinearSSSP.Decremental.CacheCopy
end s133
section s134
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
lemma GlobalFrame.seq {a b : Cmd} (ha : GlobalFrame a) (hb : GlobalFrame b) : GlobalFrame (.seq a b) :=
  ⟨fun k hk => ⟨ha.1 k hk,hb.1 k hk⟩,fun k hk => ⟨ha.2 k hk,hb.2 k hk⟩⟩
lemma GlobalFrame.loop (test : Test) {body : Cmd} (h : GlobalFrame body) : GlobalFrame (.loop test body) := h
lemma Globals.transfer {i : Input} {B utility cost : ℕ} {cmd : Cmd} {s t : Data}
    (h : Globals i B utility s) (he : Eval cmd s cost t) (hf : GlobalFrame cmd) : Globals i B utility t := by
  have hn (k : ℕ) (hk : k ∈ globalNat) : t.natReg k = s.natReg k := he.nat_frame (hf.1 k hk)
  have hr (k : ℕ) (hk : k ∈ globalReal) : t.realReg k = s.realReg k := he.real_frame (hf.2 k hk)
  rcases h with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_⟩
  constructor
  all_goals first | (rw [hn _ (by decide)];assumption) | (rw [hr _ (by decide)];assumption)
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
theorem solution : (((((((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (j address : Nat),
  @Ne.{1} Nat address
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)) →
    And (@Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.RegisterSave.savedOne s j).natMem address) (s.natMem address))
      (@Eq.{1} Real ((DecrAlmostLinearSSSP.Decremental.RegisterSave.savedOne s j).realMem address) (s.realMem address))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (j : Nat),
  @Eq.{1} Nat
    ((DecrAlmostLinearSSSP.Decremental.RegisterSave.restoredOne s j).natReg
      (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50)))))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (j : Nat),
  And
    (@Eq.{1} Nat
      ((DecrAlmostLinearSSSP.Decremental.RegisterSave.restoredOne s j).natReg
        (DecrAlmostLinearSSSP.Decremental.shadowReg j))
      (s.natMem
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j))))
    (@Eq.{1} Real
      ((DecrAlmostLinearSSSP.Decremental.RegisterSave.restoredOne s j).realReg
        (DecrAlmostLinearSSSP.Decremental.shadowReg j))
      (s.realMem
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j))))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (j k : Nat),
  @Ne.{1} Nat k j →
    And
      (@Eq.{1} Nat
        ((DecrAlmostLinearSSSP.Decremental.RegisterSave.restoredOne s j).natReg
          (DecrAlmostLinearSSSP.Decremental.shadowReg k))
        (s.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg k)))
      (@Eq.{1} Real
        ((DecrAlmostLinearSSSP.Decremental.RegisterSave.restoredOne s j).realReg
          (DecrAlmostLinearSSSP.Decremental.shadowReg k))
        (s.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg k)))))) ∧ (((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (j : Nat),
  And (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.RegisterSave.restoredOne s j).natMem s.natMem)
    (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.RegisterSave.restoredOne s j).realMem s.realMem)) ∧ (∀ (registers : List.{0} Nat),
  @List.Nodup.{0} Nat registers →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
      ∃ t,
        And
          (DecrAlmostLinearSSSP.Decremental.Structured.Eval
            (DecrAlmostLinearSSSP.Decremental.RegisterSave.saveRegisters registers) s
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (@List.length.{0} Nat registers))
            t)
          (And
            (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50)))))
            (And
              (∀ (k : Nat),
                And
                  (@Eq.{1} Nat (t.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg k))
                    (s.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg k)))
                  (@Eq.{1} Real (t.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg k))
                    (s.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg k))))
              (And
                (∀ (k : Nat),
                  @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat) registers k →
                    And
                      (@Eq.{1} Nat
                        (t.natMem
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k)))
                        (s.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg k)))
                      (@Eq.{1} Real
                        (t.realMem
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k)))
                        (s.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg k))))
                (∀ (address : Nat),
                  (∀ (k : Nat),
                      @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat) registers k →
                        @Ne.{1} Nat address
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k))) →
                    And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                      (@Eq.{1} Real (t.realMem address) (s.realMem address)))))))) ∧ ((∀ (registers : List.{0} Nat),
  @List.Nodup.{0} Nat registers →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
      ∃ t,
        And
          (DecrAlmostLinearSSSP.Decremental.Structured.Eval
            (DecrAlmostLinearSSSP.Decremental.RegisterSave.restoreRegisters registers) s
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (@List.length.{0} Nat registers))
            t)
          (And
            (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50)))))
            (And (@Eq.{1} (Nat → Nat) t.natMem s.natMem)
              (And (@Eq.{1} (Nat → Real) t.realMem s.realMem)
                (And
                  (∀ (k : Nat),
                    @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat) registers k →
                      And
                        (@Eq.{1} Nat (t.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg k))
                          (s.natMem
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k))))
                        (@Eq.{1} Real (t.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg k))
                          (s.realMem
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k)))))
                  (∀ k ∉ registers,
                    And
                      (@Eq.{1} Nat (t.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg k))
                        (s.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg k)))
                      (@Eq.{1} Real (t.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg k))
                        (s.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg k))))))))) ∧ ((∀ (j k : Nat),
  @LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.RegisterSave.restoreOne j) k) ∧ (∀ (j k : Nat),
  @LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.RegisterSave.restoreOne j) k))))) ∧ ((((∀ (registers : List.{0} Nat) (k : Nat),
  @LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
      (DecrAlmostLinearSSSP.Decremental.RegisterSave.restoreRegisters registers) k) ∧ (∀ (registers : List.{0} Nat) (k : Nat),
  @LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
      (DecrAlmostLinearSSSP.Decremental.RegisterSave.restoreRegisters registers) k)) ∧ ((∀ (B F N : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (g : DecrAlmostLinearSSSP.Decremental.Machine),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) g.pc →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) g.work →
      @Eq.{1} Bool
          (@BEq.beq.{0} Nat (@instBEqOfDecidableEq.{0} Nat instDecidableEqNat)
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          g.halted →
        @Eq.{1} Bool
            (@BEq.beq.{0} Nat (@instBEqOfDecidableEq.{0} Nat instDecidableEqNat)
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            g.fault →
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
                          (DecrAlmostLinearSSSP.Decremental.RegisterSave.restoreRegisters (List.range N)) s
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) N)
                          t)
                        (DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F t g)) ∧ (∀ (entry : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.SourceSetup.header entry) s
    (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))
    (DecrAlmostLinearSSSP.Decremental.SourceSetup.headerData entry s)))) ∧ (((∀ (entry : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  And (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.SourceSetup.headerData entry s).realMem s.realMem)
    (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.SourceSetup.headerData entry s).natMem s.natMem)) ∧ (∀ (entry j : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.SourceSetup.header entry)
    (DecrAlmostLinearSSSP.Decremental.shadowReg j))) ∧ ((∀ (entry j : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.SourceSetup.header entry)
    (DecrAlmostLinearSSSP.Decremental.shadowReg j)) ∧ ((∀ (entry B F : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))) B →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112)))) F →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
        And
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.SourceSetup.headerData entry s).natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
            B)
          (And
            (@Eq.{1} Nat
              ((DecrAlmostLinearSSSP.Decremental.SourceSetup.headerData entry s).natReg
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (And
              (@Eq.{1} Nat
                ((DecrAlmostLinearSSSP.Decremental.SourceSetup.headerData entry s).natReg
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                entry)
              (And
                (@Eq.{1} Nat
                  ((DecrAlmostLinearSSSP.Decremental.SourceSetup.headerData entry s).natReg
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                (And
                  (@Eq.{1} Nat
                    ((DecrAlmostLinearSSSP.Decremental.SourceSetup.headerData entry s).natReg
                      (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (And
                    (@Eq.{1} Nat
                      ((DecrAlmostLinearSSSP.Decremental.SourceSetup.headerData entry s).natReg
                        (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                      F)
                    (And
                      (@Eq.{1} Real
                        ((DecrAlmostLinearSSSP.Decremental.SourceSetup.headerData entry s).realReg
                          (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                        (@Nat.cast.{0} Real Real.instNatCast F))
                      (And
                        (@Eq.{1} Nat
                          ((DecrAlmostLinearSSSP.Decremental.SourceSetup.headerData entry s).natReg
                            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                          (s.natMem
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
                              (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))))
                        (@Eq.{1} Nat
                          ((DecrAlmostLinearSSSP.Decremental.SourceSetup.headerData entry s).natReg
                            (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))))))))))) ∧ (∀ (registers : List.{0} Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.NoMemory
    (DecrAlmostLinearSSSP.Decremental.RegisterSave.restoreRegisters registers))))))) ∧ (((((∀ (N entry B F : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data)
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
                                            (@Eq.{1} (Nat → Nat) t.natMem s.natMem))))))))) ∧ (∀ {B bank start : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data}
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
                            (DecrAlmostLinearSSSP.Decremental.observedInstruction g.pc ins) s cost t)
                          (And
                            (@LE.le.{0} Nat instLENat cost
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (DecrAlmostLinearSSSP.Decremental.actionBound ins)
                                (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))
                            (And
                              (DecrAlmostLinearSSSP.Decremental.ShadowDataRep B
                                (DecrAlmostLinearSSSP.Decremental.bankFactor bank) t
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
                              (DecrAlmostLinearSSSP.Decremental.ReportLog start
                                (@HAppend.hAppend.{0, 0, 0} (List.{0} Nat) (List.{0} Nat) (List.{0} Nat)
                                  (@instHAppendOfAppend.{0} (List.{0} Nat) (@List.instAppend.{0} Nat)) reports
                                  (DecrAlmostLinearSSSP.Decremental.physicalWrites B bank ins g))
                                t))))) ∧ ((∀ {B bank start : Nat} (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (pc : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (g : DecrAlmostLinearSSSP.Decremental.Machine),
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
                    @LE.le.{0} Nat instLENat pc g.pc →
                      ∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
                        @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                            (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                              DecrAlmostLinearSSSP.Decremental.Instruction
                              (fun as i =>
                                @LT.lt.{0} Nat instLTNat i
                                  (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                              (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) code
                              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) g.pc pc))
                            (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins) →
                          ∃ cost t,
                            And
                              (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                (DecrAlmostLinearSSSP.Decremental.observedDispatchAux pc code) s cost t)
                              (And
                                (@LE.le.{0} Nat instLENat cost
                                  (DecrAlmostLinearSSSP.Decremental.observedDispatchCharge code))
                                (And
                                  (DecrAlmostLinearSSSP.Decremental.ShadowDataRep B
                                    (DecrAlmostLinearSSSP.Decremental.bankFactor bank) t
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
                                  (DecrAlmostLinearSSSP.Decremental.ReportLog start
                                    (@HAppend.hAppend.{0, 0, 0} (List.{0} Nat) (List.{0} Nat) (List.{0} Nat)
                                      (@instHAppendOfAppend.{0} (List.{0} Nat) (@List.instAppend.{0} Nat)) reports
                                      (DecrAlmostLinearSSSP.Decremental.physicalWrites B bank ins g))
                                    t)))) ∧ (∀ (k : Nat),
  @Ne.{1} Nat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Ne.{1} Nat (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) k →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.appendStoreReport k))) ∧ (((∀ (k : Nat), DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.appendStoreReport k) ∧ (∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction) (k : Nat),
  @LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) →
    @Ne.{1} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k →
      @Ne.{1} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) k →
        @Ne.{1} Nat (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) k →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.observedAction ins) k)) ∧ ((∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction) (k : Nat),
  @LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.observedAction ins) k) ∧ ((∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
  DecrAlmostLinearSSSP.Decremental.Structured.FlagFrame (DecrAlmostLinearSSSP.Decremental.observedAction ins)
    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) ∧ (∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.observedAction ins)
    (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))))))) ∧ ((((∀ (pc : Nat) (ins : DecrAlmostLinearSSSP.Decremental.Instruction) (k : Nat),
  Or (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (Or (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.observedInstruction pc ins) k) ∧ (∀ (pc : Nat) (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.observedInstruction pc ins)
    (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))) ∧ ((∀ (pc : Nat) (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
  DecrAlmostLinearSSSP.Decremental.Structured.FlagFrame (DecrAlmostLinearSSSP.Decremental.observedInstruction pc ins)
    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) ∧ ((∀ (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (start k : Nat),
  Or (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (Or (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
      (DecrAlmostLinearSSSP.Decremental.observedDispatchAux start code) k) ∧ (∀ (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (start : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
    (DecrAlmostLinearSSSP.Decremental.observedDispatchAux start code)
    (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))))) ∧ (((∀ (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (start : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.FlagFrame
    (DecrAlmostLinearSSSP.Decremental.observedDispatchAux start code)
    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) ∧ (∀ (pc : Nat) (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.observedInstruction pc ins)
    (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))) ∧ ((∀ (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (pc : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.observedDispatchAux pc code)
    (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))) ∧ ((∀ (j k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 54) (instOfNatNat (nat_lit 54))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.RegisterSave.saveOne j) k) ∧ (∀ (registers : List.{0} Nat) (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 54) (instOfNatNat (nat_lit 54))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
        (DecrAlmostLinearSSSP.Decremental.RegisterSave.saveRegisters registers) k))))))) ∧ ((((((∀ (j k : Nat),
  @Even.{0} Nat instAddNat k →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 54) (instOfNatNat (nat_lit 54))) →
        DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
          (DecrAlmostLinearSSSP.Decremental.RegisterSave.restoreOne j) k) ∧ (∀ (registers : List.{0} Nat) (k : Nat),
  @Even.{0} Nat instAddNat k →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 54) (instOfNatNat (nat_lit 54))) →
        DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
          (DecrAlmostLinearSSSP.Decremental.RegisterSave.restoreRegisters registers) k)) ∧ ((∀ (registers : List.{0} Nat) (k : Nat),
  @Even.{0} Nat instAddNat k →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
      (DecrAlmostLinearSSSP.Decremental.RegisterSave.restoreRegisters registers) k) ∧ (∀ (N entry k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 54) (instOfNatNat (nat_lit 54))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
            (DecrAlmostLinearSSSP.Decremental.SourceSetup.code N entry) k))) ∧ (((∀ (N entry k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.SourceSetup.code N entry)
        k) ∧ (∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction) (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))) k →
    @Even.{0} Nat instAddNat k →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.observedAction ins) k)) ∧ ((∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction) (k : Nat),
  @Even.{0} Nat instAddNat k →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.observedAction ins) k) ∧ ((∀ (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (pc k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))) k →
    @Even.{0} Nat instAddNat k →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
        (DecrAlmostLinearSSSP.Decremental.observedDispatchAux pc code) k) ∧ (∀ (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (pc k : Nat),
  @Even.{0} Nat instAddNat k →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.observedDispatchAux pc code)
      k))))) ∧ ((((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.SourceSnapshot.workCode s
    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
    (DecrAlmostLinearSSSP.Decremental.SourceSnapshot.workData s)) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.SourceSnapshot.workData s).natMem
    (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natMem
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
        (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.SourceSnapshot.workData s).realMem s.realMem) ∧ ((∀ (N k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 54) (instOfNatNat (nat_lit 54))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.SourceSnapshot.code N) k) ∧ (∀ (N : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
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
                    (@Eq.{1} Real (t.realMem address) (s.realMem address))))))))) ∧ (((∀ (B bank record a : Nat),
  (∃ r,
      @Eq.{1} Nat record
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
    And
      (@Ne.{1} Nat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record
          (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
      (∀ (j : Nat),
        @Ne.{1} Nat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record
              (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))) ∧ (∀ (N k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.SourceSnapshot.code N) k)) ∧ ((∀ (N entry : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program) (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 54) (instOfNatNat (nat_lit 54))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
            (DecrAlmostLinearSSSP.Decremental.SourceCall.code N entry p) k) ∧ ((∀ (N entry : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program) (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.SourceCall.code N entry p)
        k) ∧ (∀ (N entry B bank : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data)
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
                                                      (@Eq.{1} Real (t.realMem address) (s.realMem address))))))))))))) ∧ (((((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
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
                              (@Eq.{1} Nat (t.natMem address) (s.natMem address)))))))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (F flag : Nat) (delta r : Real),
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
                                  (@Eq.{1} (Nat → Nat) t.natMem s.natMem))))))))) ∧ ((DecrAlmostLinearSSSP.Decremental.Structured.NoMemory DecrAlmostLinearSSSP.Decremental.ScaledReadout.code) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CacheCopy.suffix s
    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
    (DecrAlmostLinearSSSP.Decremental.CacheCopy.suffixData s)))) ∧ (((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 130) (instOfNatNat (nat_lit 130))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.ScaledReadout.code k) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.ScaledReadout.code k)) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (F flag : Nat) (delta r : Real),
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
                  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                      ∃ cost t,
                        And
                          (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                            DecrAlmostLinearSSSP.Decremental.CacheCopy.body s cost t)
                          (And
                            (@LE.le.{0} Nat instLENat cost
                              (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11))))
                            (And
                              (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))))
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                              (And
                                (@Eq.{1} Nat
                                  (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 128) (instOfNatNat (nat_lit 128))))
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 128) (instOfNatNat (nat_lit 128))))
                                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 170) (instOfNatNat (nat_lit 170))))))
                                (And
                                  (@Eq.{1} Nat
                                    (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 176) (instOfNatNat (nat_lit 176))))
                                    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 176) (instOfNatNat (nat_lit 176))))
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                  (And
                                    (@Eq.{1} Nat
                                      (t.natMem
                                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
                                      flag)
                                    (And
                                      (@Eq.{1} Real
                                        (t.realMem
                                          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
                                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) delta r))
                                      (∀ (address : Nat),
                                        @Ne.{1} Nat address
                                            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))) →
                                          And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                            (@Eq.{1} Real (t.realMem address) (s.realMem address)))))))))) ∧ ((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 128) (instOfNatNat (nat_lit 128))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 130) (instOfNatNat (nat_lit 130))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 176) (instOfNatNat (nat_lit 176))) →
            DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CacheCopy.body k) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CacheCopy.body k))))) ∧ ((((∀ (count sourceBase cacheBase stride F : Nat) (delta : Real) (flags : Nat → Nat) (values : Nat → Real)
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
                                                      (@Eq.{1} Real (t.realMem address) (s.realMem address))))))))) ∧ (∀ (B bank cacheOffset count : Nat) (delta : Real) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data)
  (g : DecrAlmostLinearSSSP.Decremental.Machine),
  DecrAlmostLinearSSSP.Decremental.ShadowDataRep B (DecrAlmostLinearSSSP.Decremental.bankFactor bank) s g →
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) delta →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 132) (instOfNatNat (nat_lit 132))))
          (DecrAlmostLinearSSSP.Decremental.bankFactor bank) →
        @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 70) (instOfNatNat (nat_lit 70)))) delta →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 128) (instOfNatNat (nat_lit 128))))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                (DecrAlmostLinearSSSP.Decremental.bankFactor bank)) →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) cacheOffset))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
              @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 170) (instOfNatNat (nat_lit 170))))
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (DecrAlmostLinearSSSP.Decremental.bankFactor bank)) →
                @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 176) (instOfNatNat (nat_lit 176)))) count →
                  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                        (∀ (v : Fin count),
                            @LE.le.{0} Nat instLENat (g.natMem (@Fin.val count v))
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                          (∀ (v : Fin count),
                              @Eq.{1} Nat (g.natMem (@Fin.val count v))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                                @LE.le.{0} Real Real.instLE
                                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                  (g.realMem (@Fin.val count v))) →
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
                                    (∀ (v : Fin count),
                                      And
                                        (@Eq.{1} Nat
                                          (t.natMem
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                    cacheOffset))
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                (@Fin.val count v))))
                                          (g.natMem (@Fin.val count v)))
                                        (And
                                          (@Eq.{1} Real
                                            (t.realMem
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                      cacheOffset))
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                  (@Fin.val count v))))
                                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) delta
                                              (g.realMem (@Fin.val count v))))
                                          (@Eq.{1} ENNReal
                                            (DecrAlmostLinearSSSP.Decremental.ExtendedMax.cell t
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                      cacheOffset))
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                  (@Fin.val count v))))
                                            (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                                              (@instHMul.{0} ENNReal
                                                (@Distrib.toMul.{0} ENNReal
                                                  (@instDistribOfSemiring.{0} ENNReal
                                                    (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                                              (ENNReal.ofReal delta)
                                              (DecrAlmostLinearSSSP.Decremental.stored g (@Fin.val count v))))))
                                    (And
                                      (∀ (address : Nat),
                                        (∀ (j : Nat),
                                            @LT.lt.{0} Nat instLTNat j count →
                                              @Ne.{1} Nat address
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                        cacheOffset))
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j))) →
                                          And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                            (@Eq.{1} Real (t.realMem address) (s.realMem address)))
                                      (∀ (a : Nat),
                                        And
                                          (@Eq.{1} Nat
                                            (t.natMem
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                                            (s.natMem
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))
                                          (@Eq.{1} Real
                                            (t.realMem
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                                            (s.realMem
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                      (instOfNatNat (nat_lit 1)))))))))))))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CacheCopy.setup s
    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
    (DecrAlmostLinearSSSP.Decremental.CacheCopy.setupData s)) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    And
      (@Eq.{1} Nat
        ((DecrAlmostLinearSSSP.Decremental.CacheCopy.setupData s).natReg
          (@OfNat.ofNat.{0} Nat (nat_lit 128) (instOfNatNat (nat_lit 128))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74))))
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))))))
      (And
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.CacheCopy.setupData s).natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 132) (instOfNatNat (nat_lit 132))))
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112)))))
        (And
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.CacheCopy.setupData s).natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 170) (instOfNatNat (nat_lit 170))))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))))))
          (And
            (@Eq.{1} Nat
              ((DecrAlmostLinearSSSP.Decremental.CacheCopy.setupData s).natReg
                (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 108) (instOfNatNat (nat_lit 108)))))
            (@Eq.{1} Nat
              ((DecrAlmostLinearSSSP.Decremental.CacheCopy.setupData s).natReg
                (@OfNat.ofNat.{0} Nat (nat_lit 176) (instOfNatNat (nat_lit 176))))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 66) (instOfNatNat (nat_lit 66))))))))) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 128) (instOfNatNat (nat_lit 128))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 132) (instOfNatNat (nat_lit 132))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 170) (instOfNatNat (nat_lit 170))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 176) (instOfNatNat (nat_lit 176))) →
            DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CacheCopy.setup k)))) ∧ (((∀ (k : Nat), DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CacheCopy.setup k) ∧ (∀ (B bank cacheOffset count : Nat) (delta : Real) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data)
  (g : DecrAlmostLinearSSSP.Decremental.Machine),
  DecrAlmostLinearSSSP.Decremental.ShadowDataRep B (DecrAlmostLinearSSSP.Decremental.bankFactor bank) s g →
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) delta →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))) B →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))))
            (DecrAlmostLinearSSSP.Decremental.bankFactor bank) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 108) (instOfNatNat (nat_lit 108))))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) cacheOffset))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 66) (instOfNatNat (nat_lit 66)))) count →
              @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 70) (instOfNatNat (nat_lit 70)))) delta →
                @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                      (∀ (v : Fin count),
                          @LE.le.{0} Nat instLENat (g.natMem (@Fin.val count v))
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                        (∀ (v : Fin count),
                            @Eq.{1} Nat (g.natMem (@Fin.val count v))
                                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                              @LE.le.{0} Real Real.instLE
                                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                (g.realMem (@Fin.val count v))) →
                          ∃ cost t,
                            And
                              (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                DecrAlmostLinearSSSP.Decremental.CacheCopy.call s cost t)
                              (And
                                (@LE.le.{0} Nat instLENat cost
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13))) count)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                                (And
                                  (∀ (v : Fin count),
                                    And
                                      (@Eq.{1} Nat
                                        (t.natMem
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                  cacheOffset))
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                              (@Fin.val count v))))
                                        (g.natMem (@Fin.val count v)))
                                      (And
                                        (@Eq.{1} Real
                                          (t.realMem
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                    cacheOffset))
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                (@Fin.val count v))))
                                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) delta
                                            (g.realMem (@Fin.val count v))))
                                        (@Eq.{1} ENNReal
                                          (DecrAlmostLinearSSSP.Decremental.ExtendedMax.cell t
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                    cacheOffset))
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                (@Fin.val count v))))
                                          (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                                            (@instHMul.{0} ENNReal
                                              (@Distrib.toMul.{0} ENNReal
                                                (@instDistribOfSemiring.{0} ENNReal
                                                  (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                                            (ENNReal.ofReal delta)
                                            (DecrAlmostLinearSSSP.Decremental.stored g (@Fin.val count v))))))
                                  (And
                                    (∀ (address : Nat),
                                      (∀ (j : Nat),
                                          @LT.lt.{0} Nat instLTNat j count →
                                            @Ne.{1} Nat address
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                      cacheOffset))
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j))) →
                                        And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                          (@Eq.{1} Real (t.realMem address) (s.realMem address)))
                                    (∀ (a : Nat),
                                      And
                                        (@Eq.{1} Nat
                                          (t.natMem
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                                          (s.natMem
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))
                                        (@Eq.{1} Real
                                          (t.realMem
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                                          (s.realMem
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))))))) ∧ ((∀ {a b : DecrAlmostLinearSSSP.Decremental.Structured.Cmd},
  DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame a →
    DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame b →
      DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame (a.seq b)) ∧ ((∀ (test : DecrAlmostLinearSSSP.Decremental.Structured.Test) {body : DecrAlmostLinearSSSP.Decremental.Structured.Cmd},
  DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame body →
    DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame (DecrAlmostLinearSSSP.Decremental.Structured.Cmd.loop test body)) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B utility cost : Nat}
  {cmd : DecrAlmostLinearSSSP.Decremental.Structured.Cmd} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.Globals i B utility s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval cmd s cost t →
      DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame cmd →
        DecrAlmostLinearSSSP.Decremental.Native.Globals i B utility t)))))))) := by
  exact ⟨⟨⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.RegisterSave.savedOne_memory_frame,DecrAlmostLinearSSSP.Decremental.RegisterSave.restoredOne_base⟩,⟨DecrAlmostLinearSSSP.Decremental.RegisterSave.restoredOne_value,DecrAlmostLinearSSSP.Decremental.RegisterSave.restoredOne_register_frame⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.RegisterSave.restoredOne_memory,DecrAlmostLinearSSSP.Decremental.RegisterSave.eval_saveRegisters⟩,⟨DecrAlmostLinearSSSP.Decremental.RegisterSave.eval_restoreRegisters,⟨DecrAlmostLinearSSSP.Decremental.RegisterSave.restoreOne_nat_meta,DecrAlmostLinearSSSP.Decremental.RegisterSave.restoreOne_real_meta⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.RegisterSave.restoreRegisters_nat_meta,DecrAlmostLinearSSSP.Decremental.RegisterSave.restoreRegisters_real_meta⟩,⟨DecrAlmostLinearSSSP.Decremental.RegisterSave.restore_saved_image,DecrAlmostLinearSSSP.Decremental.SourceSetup.header_eval⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.SourceSetup.header_memory,DecrAlmostLinearSSSP.Decremental.SourceSetup.header_shadow_nat_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.SourceSetup.header_shadow_real_frame,⟨DecrAlmostLinearSSSP.Decremental.SourceSetup.header_fields,DecrAlmostLinearSSSP.Decremental.SourceSetup.restore_no_memory⟩⟩⟩⟩⟩,⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.SourceSetup.eval_code,DecrAlmostLinearSSSP.Decremental.eval_observed_instruction⟩,⟨DecrAlmostLinearSSSP.Decremental.eval_observed_dispatch_aux,DecrAlmostLinearSSSP.Decremental.appendStoreReport_nat_frame⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.appendStoreReport_real_frame,DecrAlmostLinearSSSP.Decremental.observedAction_nat_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.observedAction_real_frame,⟨DecrAlmostLinearSSSP.Decremental.observedAction_flag_frame,DecrAlmostLinearSSSP.Decremental.observedAction_nat14_frame⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.observedInstruction_nat_frame,DecrAlmostLinearSSSP.Decremental.observedInstruction_real_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.observedInstruction_flag_frame,⟨DecrAlmostLinearSSSP.Decremental.observedDispatchAux_nat_frame,DecrAlmostLinearSSSP.Decremental.observedDispatchAux_real_frame⟩⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.observedDispatchAux_flag_frame,DecrAlmostLinearSSSP.Decremental.observedInstruction_nat14_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.observedDispatchAux_nat14_frame,⟨DecrAlmostLinearSSSP.Decremental.RegisterSave.saveOne_nat_frame,DecrAlmostLinearSSSP.Decremental.RegisterSave.saveRegisters_nat_frame⟩⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.RegisterSave.restoreOne_nat_even,DecrAlmostLinearSSSP.Decremental.RegisterSave.restoreRegisters_nat_even⟩,⟨DecrAlmostLinearSSSP.Decremental.RegisterSave.restoreRegisters_real_even,DecrAlmostLinearSSSP.Decremental.SourceSetup.nat_even_frame⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.SourceSetup.real_even_frame,DecrAlmostLinearSSSP.Decremental.observedAction_nat_even_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.observedAction_real_even_frame,⟨DecrAlmostLinearSSSP.Decremental.observedDispatchAux_nat_even_frame,DecrAlmostLinearSSSP.Decremental.observedDispatchAux_real_even_frame⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.SourceSnapshot.work_eval,DecrAlmostLinearSSSP.Decremental.SourceSnapshot.work_nat_mem⟩,⟨DecrAlmostLinearSSSP.Decremental.SourceSnapshot.work_real_mem,⟨DecrAlmostLinearSSSP.Decremental.SourceSnapshot.nat_frame,DecrAlmostLinearSSSP.Decremental.SourceSnapshot.eval_code⟩⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.SourceSnapshot.guest_bank_protected,DecrAlmostLinearSSSP.Decremental.SourceCall.snapshot_real_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.SourceCall.nat_even_frame,⟨DecrAlmostLinearSSSP.Decremental.SourceCall.real_even_frame,DecrAlmostLinearSSSP.Decremental.SourceCall.eval_code⟩⟩⟩⟩⟩,⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.ExtendedMax.eval_code,DecrAlmostLinearSSSP.Decremental.ScaledReadout.eval_code⟩,⟨DecrAlmostLinearSSSP.Decremental.ScaledReadout.no_memory,DecrAlmostLinearSSSP.Decremental.CacheCopy.suffix_eval⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.CacheCopy.read_nat_frame,DecrAlmostLinearSSSP.Decremental.CacheCopy.read_real_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.CacheCopy.body_eval,⟨DecrAlmostLinearSSSP.Decremental.CacheCopy.nat_frame,DecrAlmostLinearSSSP.Decremental.CacheCopy.real_frame⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.CacheCopy.eval_code,DecrAlmostLinearSSSP.Decremental.CacheCopy.eval_source⟩,⟨DecrAlmostLinearSSSP.Decremental.CacheCopy.setup_eval,⟨DecrAlmostLinearSSSP.Decremental.CacheCopy.setup_fields,DecrAlmostLinearSSSP.Decremental.CacheCopy.setup_nat_frame⟩⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.CacheCopy.setup_real_frame,DecrAlmostLinearSSSP.Decremental.CacheCopy.call_source⟩,⟨DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame.seq,⟨DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame.loop,DecrAlmostLinearSSSP.Decremental.Native.Globals.transfer⟩⟩⟩⟩⟩⟩⟩
