-- Prove2me | solution 1 for DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_10
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T17:36:31.445018+00:00
-- url     : https://prove2.me/submissions/2f0cd5c6-8723-45fc-a1f7-14c015de782b

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
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_core_laws_1
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_core_laws_2
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_core_laws_3
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_core_laws_4
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_core_laws_5
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_core_laws_6
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_core_laws_7
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_core_laws_8
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_core_laws_9
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
theorem DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Bounded.root : ∀ {height : Nat} {tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie height} {low high : Nat},
  @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Bounded height tree low high →
    @Ne.{1} Nat (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root height tree)
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
      And (@LE.le.{0} Nat instLENat low (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root height tree))
        (@LT.lt.{0} Nat instLTNat (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root height tree) high) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.1.1.2.2.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.Structured.eval_add : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (d a b : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.add d a b) s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    {
      realReg :=
        @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realReg d
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (s.realReg a) (s.realReg b)),
      natReg := s.natReg, realMem := s.realMem, natMem := s.natMem } := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.1.2.1.2.2.2
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
theorem DecrAlmostLinearSSSP.Decremental.Structured.eval_store : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (a d : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.store a d) s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    { realReg := s.realReg, natReg := s.natReg,
      realMem := @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realMem (s.natReg a) (s.realReg d),
      natMem := s.natMem } := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.2.1.1.1.2
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
theorem DecrAlmostLinearSSSP.Decremental.Exact.TriePush.code_nat_frame : ∀ k ∉ DecrAlmostLinearSSSP.Decremental.Exact.TriePush.registers,
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.TriePush.code k := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_3.2.2.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.TriePush.code_real_frame : ∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Exact.TriePush.code k := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_3.2.2.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.TriePop.Result.nat_frame : ∀ {h : Nat} {tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  (r : @DecrAlmostLinearSSSP.Decremental.Exact.TriePop.Result h tree s),
  ∀ k ∉ DecrAlmostLinearSSSP.Decremental.Exact.TriePop.registers,
    @Eq.{1} Nat ((@DecrAlmostLinearSSSP.Decremental.Exact.TriePop.Result.final h tree s r).natReg k) (s.natReg k) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.1.1.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.TriePop.body_nat_frame : ∀ k ∉ DecrAlmostLinearSSSP.Decremental.Exact.TriePop.registers,
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.TriePop.body k := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.1.1.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.TriePop.code_nat_frame : ∀ k ∉ DecrAlmostLinearSSSP.Decremental.Exact.TriePop.registers,
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.TriePop.code k := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.1.1.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.TriePop.code_real_frame : ∀ (k : Nat), DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Exact.TriePop.code k := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.1.1.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.Powers.body_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.Powers.body s
    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
    (DecrAlmostLinearSSSP.Decremental.Exact.Powers.advanced s) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.1.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.Powers.body_nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 248) (instOfNatNat (nat_lit 248))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 250) (instOfNatNat (nat_lit 250))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 252) (instOfNatNat (nat_lit 252))) →
        DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.Powers.body k := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.1.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.Powers.body_real_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 250) (instOfNatNat (nat_lit 250))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Exact.Powers.body k := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.1.2.1.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.code_real_frame : ∀ (j : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.code j := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_6.1.2.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.loop_eval : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (remaining upto : Nat),
  @Eq.{1} Nat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) upto remaining) i.k →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
      DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.Prefix i upto s →
        ∃ t,
          And
            (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.loop
              s
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) remaining)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
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
                    @Eq.{1} Nat (t.natMem a) (s.natMem a)))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_6.2.1.2.1.2.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.OnlineRun.length : ∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {i : DecrAlmostLinearSSSP.Decremental.Input} {ds : List.{0} (Fin i.k)}
  {cs : List.{0} DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.OnlineRun p i ds cs →
    @Eq.{1} Nat (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Machine cs)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_8.2.2.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.PreservesOutside.refl : ∀ (base F : Nat) (c : DecrAlmostLinearSSSP.Decremental.Machine),
  DecrAlmostLinearSSSP.Decremental.PreservesOutside base F c c := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_2.1.1.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.PreservesOutside.trans : ∀ {base F : Nat} {c d e : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.PreservesOutside base F c d →
    DecrAlmostLinearSSSP.Decremental.PreservesOutside base F d e →
      DecrAlmostLinearSSSP.Decremental.PreservesOutside base F c e := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_2.1.1.1.1.2.2
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
theorem DecrAlmostLinearSSSP.Decremental.SourceMemory.Image.frame : ∀ {B bank : Nat} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {natural : Nat → Nat} {real : Nat → Real},
  DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B bank s natural real →
    (∀ (a : Nat),
        And
          (@Eq.{1} Nat (t.natMem (DecrAlmostLinearSSSP.Decremental.bankAddress B bank a))
            (s.natMem (DecrAlmostLinearSSSP.Decremental.bankAddress B bank a)))
          (@Eq.{1} Real (t.realMem (DecrAlmostLinearSSSP.Decremental.bankAddress B bank a))
            (s.realMem (DecrAlmostLinearSSSP.Decremental.bankAddress B bank a)))) →
      DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B bank t natural real := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_4.1.1.2.2.1.2
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
theorem DecrAlmostLinearSSSP.Decremental.CacheCopy.body_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (F flag : Nat) (delta r : Real),
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
                                            (@Eq.{1} Real (t.realMem address) (s.realMem address))))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_5.2.2.1.2.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.CacheCopy.setup_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CacheCopy.setup s
    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
    (DecrAlmostLinearSSSP.Decremental.CacheCopy.setupData s) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_5.2.2.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.CacheCopy.setup_fields : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
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
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 66) (instOfNatNat (nat_lit 66)))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_5.2.2.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CacheCopy.setup_nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 128) (instOfNatNat (nat_lit 128))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 132) (instOfNatNat (nat_lit 132))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 170) (instOfNatNat (nat_lit 170))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 176) (instOfNatNat (nat_lit 176))) →
            DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CacheCopy.setup k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_5.2.2.2.1.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame.seq : ∀ {a b : DecrAlmostLinearSSSP.Decremental.Structured.Cmd},
  DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame a →
    DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame b →
      DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame (a.seq b) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_5.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame.loop : ∀ (test : DecrAlmostLinearSSSP.Decremental.Structured.Test) {body : DecrAlmostLinearSSSP.Decremental.Structured.Cmd},
  DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame body →
    DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame (DecrAlmostLinearSSSP.Decremental.Structured.Cmd.loop test body) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_5.2.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.Globals.transfer : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B utility cost : Nat}
  {cmd : DecrAlmostLinearSSSP.Decremental.Structured.Cmd} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.Globals i B utility s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval cmd s cost t →
      DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame cmd →
        DecrAlmostLinearSSSP.Decremental.Native.Globals i B utility t := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_5.2.2.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Native.BankFrame.seq : ∀ {a b : DecrAlmostLinearSSSP.Decremental.Structured.Cmd},
  DecrAlmostLinearSSSP.Decremental.Native.BankFrame a →
    DecrAlmostLinearSSSP.Decremental.Native.BankFrame b → DecrAlmostLinearSSSP.Decremental.Native.BankFrame (a.seq b) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_6.1.1.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.Native.BankFrame.loop : ∀ (test : DecrAlmostLinearSSSP.Decremental.Structured.Test) {body : DecrAlmostLinearSSSP.Decremental.Structured.Cmd},
  DecrAlmostLinearSSSP.Decremental.Native.BankFrame body →
    DecrAlmostLinearSSSP.Decremental.Native.BankFrame (DecrAlmostLinearSSSP.Decremental.Structured.Cmd.loop test body) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_6.1.1.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.Native.BankEnv.transfer : ∀ {j record cache stride cost : Nat} {cmd : DecrAlmostLinearSSSP.Decremental.Structured.Cmd}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.BankEnv j record cache stride s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval cmd s cost t →
      DecrAlmostLinearSSSP.Decremental.Native.BankFrame cmd →
        DecrAlmostLinearSSSP.Decremental.Native.BankEnv j record cache stride t := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_6.1.1.2.2.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.LinkedScan.body_nat_frame : ∀ (k : Nat),
  Or (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 34) (instOfNatNat (nat_lit 34))))
      (Or (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 36) (instOfNatNat (nat_lit 36))))
        (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 38) (instOfNatNat (nat_lit 38))))) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.LinkedScan.body k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_8.1.1.1.1.1.2
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
theorem DecrAlmostLinearSSSP.Decremental.LinkedScan.code_nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 42) (instOfNatNat (nat_lit 42))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 44) (instOfNatNat (nat_lit 44))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 46) (instOfNatNat (nat_lit 46))) →
              DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.LinkedScan.code k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_8.1.2.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.LinkedScan.code_real_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))) →
      DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.LinkedScan.code k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_8.1.2.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.Native.ScanTable.frame_above : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {recordBase cacheBase stride : Nat}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal},
  DecrAlmostLinearSSSP.Decremental.Native.ScanTable i recordBase cacheBase stride b s →
    @LE.le.{0} Nat instLENat recordBase cacheBase →
      (∀ (address : Nat),
          @LE.le.{0} Nat instLENat recordBase address →
            And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
              (@Eq.{1} Real (t.realMem address) (s.realMem address))) →
        DecrAlmostLinearSSSP.Decremental.Native.ScanTable i recordBase cacheBase stride b t := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_8.1.2.2.2.2.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.Native.PublicFrame.refl : ∀ (l : DecrAlmostLinearSSSP.Decremental.Native.PointerLayout) (n : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data), DecrAlmostLinearSSSP.Decremental.Native.PublicFrame l n s s := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_8.2.2.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Native.PublicFrame.trans : ∀ {l : DecrAlmostLinearSSSP.Decremental.Native.PointerLayout} {n : Nat}
  {s t u : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.PublicFrame l n s t →
    DecrAlmostLinearSSSP.Decremental.Native.PublicFrame l n t u →
      DecrAlmostLinearSSSP.Decremental.Native.PublicFrame l n s u := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_8.2.2.2.1.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.DirtyCommit.body_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
        @Ne.{1} Nat (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 192) (instOfNatNat (nat_lit 192)))))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 98) (instOfNatNat (nat_lit 98))))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 192) (instOfNatNat (nat_lit 192))))))) →
          ∃ cost t,
            And
              (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.DirtyCommit.body s cost
                t)
              (And (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18))))
                (And
                  (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 192) (instOfNatNat (nat_lit 192))))
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 192) (instOfNatNat (nat_lit 192))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (And
                    (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 194) (instOfNatNat (nat_lit 194))))
                      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 194) (instOfNatNat (nat_lit 194))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (And
                      (@Eq.{1} Nat
                        (t.natMem
                          (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 192) (instOfNatNat (nat_lit 192))))))
                        (DecrAlmostLinearSSSP.Decremental.SelectedRead.flag
                          (DecrAlmostLinearSSSP.Decremental.DirtyCommit.loaded s)))
                      (And
                        (@Eq.{1} Real
                          (t.realMem
                            (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 192) (instOfNatNat (nat_lit 192))))))
                          (DecrAlmostLinearSSSP.Decremental.SelectedRead.realValue
                            (DecrAlmostLinearSSSP.Decremental.DirtyCommit.loaded s)))
                        (And
                          (@Eq.{1} Nat
                            (t.natMem
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 98) (instOfNatNat (nat_lit 98))))
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                  (s.natMem
                                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 192) (instOfNatNat (nat_lit 192))))))))
                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                          (∀ (address : Nat),
                            @Ne.{1} Nat address
                                (s.natMem
                                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 192) (instOfNatNat (nat_lit 192))))) →
                              @Ne.{1} Nat address
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 98) (instOfNatNat (nat_lit 98))))
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                      (s.natMem
                                        (s.natReg
                                          (@OfNat.ofNat.{0} Nat (nat_lit 192) (instOfNatNat (nat_lit 192))))))) →
                                And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                  (@Eq.{1} Real (t.realMem address) (s.realMem address))))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_9.1.2.2.1.2.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.DirtyCommit.code_nat_frame : ∀ (k : Nat),
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
                      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 182) (instOfNatNat (nat_lit 182))) →
                        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 180) (instOfNatNat (nat_lit 180))) →
                          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
                            DecrAlmostLinearSSSP.Decremental.DirtyCommit.code k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_9.2.1.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.DirtyCommit.code_real_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.DirtyCommit.code k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_9.2.1.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.Native.PublicControlFrame.seq : ∀ {a b : DecrAlmostLinearSSSP.Decremental.Structured.Cmd},
  DecrAlmostLinearSSSP.Decremental.Native.PublicControlFrame a →
    DecrAlmostLinearSSSP.Decremental.Native.PublicControlFrame b →
      DecrAlmostLinearSSSP.Decremental.Native.PublicControlFrame (a.seq b) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_10.1.1.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Native.Controls.transfer : ∀ {B n S reserve N cost : Nat} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {cmd : DecrAlmostLinearSSSP.Decremental.Structured.Cmd},
  DecrAlmostLinearSSSP.Decremental.Native.Controls B n S reserve N s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval cmd s cost t →
      DecrAlmostLinearSSSP.Decremental.Native.PublicControlFrame cmd →
        DecrAlmostLinearSSSP.Decremental.Native.Controls B n S reserve N t := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_10.1.1.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Native.NormalMemory.source : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program} {B reserve : Nat}
  {g : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → DecrAlmostLinearSSSP.Decremental.Machine}
  {b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal} {ptr : Fin i.n → Nat}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.NormalMemory i p B reserve g b ptr s →
    @Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.stored s.machine (@Fin.val i.n i.source))
      (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero)) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_10.1.1.2.1.2.2
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
theorem DecrAlmostLinearSSSP.Decremental.Native.ScanTable.refresh : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B reserve N : Nat}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal},
  DecrAlmostLinearSSSP.Decremental.Native.ScanTable i
      (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve
          N).records
      (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve
          N).caches
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) N)
        (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
      b s →
    ∀ (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n) (bnew : Fin i.n → ENNReal),
      DecrAlmostLinearSSSP.Decremental.Native.CacheImage i (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)
          (DecrAlmostLinearSSSP.Decremental.Native.cacheAt
            (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i)
                reserve N).caches
            i.n (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j))
          bnew t →
        (∀ (address : Nat),
            @Ne.{1} Nat address
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (DecrAlmostLinearSSSP.Decremental.Native.cacheAt
                    (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n
                        (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).caches
                    i.n (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j))
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val i.n v))) →
              And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                (@Eq.{1} Real (t.realMem address) (s.realMem address))) →
          DecrAlmostLinearSSSP.Decremental.Native.ScanTable i
            (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i)
                reserve N).records
            (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i)
                reserve N).caches
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) N)
              (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
            (@Function.update.{1, 1} (Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (fun a => Fin i.n → ENNReal)
              (instDecidableEqFin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) b j bnew)
            t := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_10.1.2.1.2.2.2.2
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
theorem DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.setup_eval : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (B j start count : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))) B →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))))
            (DecrAlmostLinearSSSP.Decremental.bankFactor j) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 66) (instOfNatNat (nat_lit 66)))) i.n →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 92) (instOfNatNat (nat_lit 92)))) start →
              @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))) count →
                @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                  @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
                    ∃ cost t,
                      And
                        (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                          DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.setup s cost t)
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
                                    (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))
                                    (DecrAlmostLinearSSSP.Decremental.utilityDepth i.size))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))))
                              (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))))
                          (And
                            (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 212) (instOfNatNat (nat_lit 212))))
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (DecrAlmostLinearSSSP.Decremental.bankFactor j)
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) i.n)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                            (And
                              (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 210) (instOfNatNat (nat_lit 210))))
                                start)
                              (And
                                (@Eq.{1} Nat
                                  (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 214) (instOfNatNat (nat_lit 214)))) count)
                                (∀ (address : Nat),
                                  (∀ (a : Nat),
                                      @Ne.{1} Nat address
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 48) (instOfNatNat (nat_lit 48))))
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a))
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                                    And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                      (@Eq.{1} Real (t.realMem address) (s.realMem address))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_11.1.1.1.2.1.2
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
theorem DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.Environment.transfer : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B reserve N cost : Nat}
  {j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)} {g : DecrAlmostLinearSSSP.Decremental.Machine}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.Environment i B reserve N j g s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.body s cost
        t →
      DecrAlmostLinearSSSP.Decremental.Native.ReportFrame i B reserve N
          (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) s t →
        DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.Environment i B reserve N j g t := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_11.2.1.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.Queue.head : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B reserve N offset address : Nat} {rest : List.{0} Nat}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.Queue i B reserve N offset (@List.cons.{0} Nat address rest) s →
    @Eq.{1} Nat (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 210) (instOfNatNat (nat_lit 210))))) address := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_11.2.1.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.body_eval : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (B reserve N offset : Nat),
      @LE.le.{0} Nat instLENat i.n B →
        ∀ (a : DecrAlmostLinearSSSP.Decremental.AdapterState i) (xs : List.{0} (Fin i.n))
          (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
          DecrAlmostLinearSSSP.Decremental.Native.AdapterMemory i B reserve N a xs s →
            ∀ (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (g : DecrAlmostLinearSSSP.Decremental.Machine),
              DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.Environment i B reserve N j g s →
                (∀ (z : Fin i.n),
                    DecrAlmostLinearSSSP.Decremental.PointerValid i
                      (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i a) z
                      (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i a z)) →
                  (∀ (z : Fin i.n),
                      And
                        (@LE.le.{0} Nat instLENat (g.natMem (@Fin.val i.n z))
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        (@Eq.{1} Nat (g.natMem (@Fin.val i.n z))
                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                          @LE.le.{0} Real Real.instLE
                            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                            (g.realMem (@Fin.val i.n z)))) →
                    ∀ (logical : Nat) (rest : List.{0} Nat),
                      DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.Queue i B reserve N offset
                          (@List.cons.{0} Nat
                            (DecrAlmostLinearSSSP.Decremental.bankAddress B
                              (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) logical)
                            rest)
                          s →
                        ∃ cost t ys,
                          And
                            (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                              DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.body s cost t)
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
                                        (DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.events i B j g
                                          (DecrAlmostLinearSSSP.Decremental.bankAddress B
                                            (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) logical)))))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 59) (instOfNatNat (nat_lit 59)))))
                              (And
                                (DecrAlmostLinearSSSP.Decremental.Native.AdapterMemory i B reserve N
                                  (DecrAlmostLinearSSSP.Decremental.adapterTrace i a
                                    (DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.events i B j g
                                      (DecrAlmostLinearSSSP.Decremental.bankAddress B
                                        (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) logical)))
                                  ys t)
                                (And
                                  (@LE.le.{0} Nat instLENat (@List.length.{0} (Fin i.n) ys)
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@List.length.{0} (Fin i.n) xs)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                  (And
                                    (DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.Environment i B reserve N j g
                                      t)
                                    (And
                                      (DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.Queue i B reserve N
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                        rest t)
                                      (DecrAlmostLinearSSSP.Decremental.Native.ReportFrame i B reserve N
                                        (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) s t)))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_11.2.1.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.loop_eval : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (B reserve N : Nat),
      @LE.le.{0} Nat instLENat i.n B →
        ∀ (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (g : DecrAlmostLinearSSSP.Decremental.Machine),
          (∀ (z : Fin i.n),
              And
                (@LE.le.{0} Nat instLENat (g.natMem (@Fin.val i.n z))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (@Eq.{1} Nat (g.natMem (@Fin.val i.n z)) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                  @LE.le.{0} Real Real.instLE
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                    (g.realMem (@Fin.val i.n z)))) →
            ∀ (reports : List.{0} Nat),
              (∀ (address : Nat),
                  @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat) reports address →
                    ∃ logical,
                      @Eq.{1} Nat address
                        (DecrAlmostLinearSSSP.Decremental.bankAddress B
                          (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) logical)) →
                ∀ (a : DecrAlmostLinearSSSP.Decremental.AdapterState i) (xs : List.{0} (Fin i.n))
                  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (offset : Nat),
                  DecrAlmostLinearSSSP.Decremental.Native.AdapterMemory i B reserve N a xs s →
                    DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.Environment i B reserve N j g s →
                      (∀ (z : Fin i.n),
                          DecrAlmostLinearSSSP.Decremental.PointerValid i
                            (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i a) z
                            (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i a z)) →
                        DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.Queue i B reserve N offset reports s →
                          ∃ cost t ys,
                            And
                              (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.loop s cost t)
                              (And
                                (@LE.le.{0} Nat instLENat cost
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
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
                                          (@OfNat.ofNat.{0} Nat (nat_lit 61) (instOfNatNat (nat_lit 61))))
                                        (@List.length.{0} Nat reports))
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
                                        (DecrAlmostLinearSSSP.Decremental.pointerTravel i a
                                          (DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.allEvents i B j g
                                            reports))))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                (And
                                  (DecrAlmostLinearSSSP.Decremental.Native.AdapterMemory i B reserve N
                                    (DecrAlmostLinearSSSP.Decremental.adapterTrace i a
                                      (DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.allEvents i B j g reports))
                                    ys t)
                                  (And
                                    (@LE.le.{0} Nat instLENat (@List.length.{0} (Fin i.n) ys)
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@List.length.{0} (Fin i.n) xs) (@List.length.{0} Nat reports)))
                                    (And
                                      (DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.Environment i B reserve N j
                                        g t)
                                      (And
                                        (DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.Queue i B reserve N
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset
                                            (@List.length.{0} Nat reports))
                                          (@List.nil.{0} Nat) t)
                                        (DecrAlmostLinearSSSP.Decremental.Native.ReportFrame i B reserve N
                                          (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) s t)))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_11.2.1.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.setup_nat_frame : ∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 154) (instOfNatNat (nat_lit 154))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 210) (instOfNatNat (nat_lit 210))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 212) (instOfNatNat (nat_lit 212))) →
              @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 214) (instOfNatNat (nat_lit 214))) →
                DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
                  DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.setup k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_11.2.1.1.2.2.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.ObservedSourceCall.code_nat_frame : ∀ (N entry : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program) (k : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 54) (instOfNatNat (nat_lit 54))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
            (DecrAlmostLinearSSSP.Decremental.ObservedSourceCall.code N entry p) k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_12.1.1.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.ObservedSourceCall.code_real_frame : ∀ (N entry : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program) (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
        (DecrAlmostLinearSSSP.Decremental.ObservedSourceCall.code N entry p) k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_12.1.1.1.1.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.Native.ReportFrame.record : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B reserve N j : Nat}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.ReportFrame i B reserve N j s t →
    ∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (r : Nat),
      @LT.lt.{0} Nat instLTNat r
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) N
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) →
        And
          (@Eq.{1} Nat
            (t.natMem
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (DecrAlmostLinearSSSP.Decremental.Native.sourceRecord i B reserve N
                  (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)))
            (s.natMem
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (DecrAlmostLinearSSSP.Decremental.Native.sourceRecord i B reserve N
                  (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))))
          (@Eq.{1} Real
            (t.realMem
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (DecrAlmostLinearSSSP.Decremental.Native.sourceRecord i B reserve N
                  (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)))
            (s.realMem
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (DecrAlmostLinearSSSP.Decremental.Native.sourceRecord i B reserve N
                  (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_12.1.2.2.1.2.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.code_nat_frame : ∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      (∀ (r : Nat),
          @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat)
              DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.forbiddenNat r →
            @Ne.{1} Nat k r) →
        DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.code
          k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_12.2.1.1.1.2.2
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
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.head_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  ∃ cost,
    And
      (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Normalize.Native.headCode s
        cost (DecrAlmostLinearSSSP.Decremental.Normalize.Native.headData s))
      (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_1.2.2.1.2.1.1
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
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.SentinelInvariant.loop : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program} {B : Nat}
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
            (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 90) (instOfNatNat (nat_lit 90)))) i.n))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_2.1.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Normalize.Native.Boundary.correct : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  i.Valid →
    ∀ (ds : List.{0} (Fin i.k)),
      DecrAlmostLinearSSSP.Decremental.Normalize.Native.Boundary i c g →
        DecrAlmostLinearSSSP.Decremental.Normalize.Native.Correct (DecrAlmostLinearSSSP.Decremental.Normalize.input i)
            (@List.map.{0, 0} (Fin i.k) (Fin (DecrAlmostLinearSSSP.Decremental.Normalize.input i).k)
              (DecrAlmostLinearSSSP.Decremental.Normalize.oldEdge i) ds)
            g →
          DecrAlmostLinearSSSP.Decremental.Normalize.Native.Correct i ds c := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_2.2.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.RuntimeInvariant.initial : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
    DecrAlmostLinearSSSP.Decremental.RuntimeInvariant b K (DecrAlmostLinearSSSP.Decremental.initializeState b) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_3.2.1.2.1.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.RuntimeInvariant.refresh : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.State b),
      DecrAlmostLinearSSSP.Decremental.RuntimeInvariant b K s →
        ∀ (e : DecrAlmostLinearSSSP.Decremental.Edge b),
          DecrAlmostLinearSSSP.Decremental.RuntimeInvariant b K (DecrAlmostLinearSSSP.Decremental.refresh b s e) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_3.2.1.2.2.1.1
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
theorem DecrAlmostLinearSSSP.Decremental.CoreRequest.nat_frame : ∀ (slot source k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
      (DecrAlmostLinearSSSP.Decremental.CoreRequest.natCode slot source) k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.1.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreRequest.real_frame : ∀ (slot source k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
    (DecrAlmostLinearSSSP.Decremental.CoreRequest.realCode slot source) k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.1.2.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreRequest.ratio_eval : ∀ {n k : Nat} (B R N : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program)
  (g : DecrAlmostLinearSSSP.Decremental.Machine) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N g s →
    (∃ r,
        @Eq.{1} Nat R
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
      ∃ t,
        And
          (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreRequest.ratioCode s
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) t)
          (DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N
            (@DecrAlmostLinearSSSP.Decremental.cutRequest n k p g (@DecrAlmostLinearSSSP.Decremental.CutOp.ratio n k))
            t) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.2.1.2.2.2.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.CorePending.enqueue : ∀ {l : Nat} (B : Nat) (xs : List.{0} (Fin l)) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (e : Fin l),
  @DecrAlmostLinearSSSP.Decremental.CorePending.View l B xs s →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 552) (instOfNatNat (nat_lit 552))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val l e)) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
            ∃ cost t ys,
              And
                (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CorePending.code s
                  cost t)
                (And (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))))
                  (And
                    (@Eq.{1} (List.{0} (Fin l)) ys
                      (@ite.{1} (List.{0} (Fin l))
                        (@Membership.mem.{0, 0} (Fin l) (List.{0} (Fin l)) (@List.instMembership.{0} (Fin l)) xs e)
                        (@List.instDecidableMemOfLawfulBEq.{0} (Fin l)
                          (@instBEqOfDecidableEq.{0} (Fin l) (instDecidableEqFin l))
                          (@Std.LawfulBEqOrd.lawfulBEq.{0} (Fin l)
                            (@instBEqOfDecidableEq.{0} (Fin l) (instDecidableEqFin l)) (instOrdFin l)
                            (@Std.LawfulBCmp.toLawfulBEqCmp.{0} (Fin l)
                              (@Preorder.toLE.{0} (Fin l)
                                (@PartialOrder.toPreorder.{0} (Fin l)
                                  (@LinearOrder.toPartialOrder.{0} (Fin l) (@Fin.instLinearOrder l))))
                              (@Preorder.toLT.{0} (Fin l)
                                (@PartialOrder.toPreorder.{0} (Fin l)
                                  (@LinearOrder.toPartialOrder.{0} (Fin l) (@Fin.instLinearOrder l))))
                              (@instBEqOfDecidableEq.{0} (Fin l) (instDecidableEqFin l))
                              (@Ord.compare.{0} (Fin l) (instOrdFin l))
                              (@instLawfulBCmpCompare_mathlib.{0} (Fin l) (@Fin.instLinearOrder l)))
                            (Fin.instLawfulEqOrd l))
                          e xs)
                        xs (@List.cons.{0} (Fin l) e xs)))
                    (And (@DecrAlmostLinearSSSP.Decremental.CorePending.View l B ys t)
                      (And (@LE.le.{0} Nat instLENat (@List.length.{0} (Fin l) ys) l)
                        (And (@Eq.{1} (Nat → Real) t.realMem s.realMem)
                          (∀ (a : Nat),
                            @Ne.{1} Nat a
                                (@DecrAlmostLinearSSSP.Decremental.CorePending.address l B e
                                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
                              @Ne.{1} Nat a
                                  (@DecrAlmostLinearSSSP.Decremental.CorePending.address l B e
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                @Eq.{1} Nat (t.natMem a) (s.natMem a))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.2.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.logicalCount_le : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core),
  @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.logicalCount b)
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.2.2.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreMemory.field_injective : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (e f : DecrAlmostLinearSSSP.Decremental.Edge b) (a c : Nat),
  @LT.lt.{0} Nat instLTNat a (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
    @LT.lt.{0} Nat instLTNat c (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
      @Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.CoreMemory.field b B e a)
          (DecrAlmostLinearSSSP.Decremental.CoreMemory.field b B f c) →
        And (@Eq.{1} (DecrAlmostLinearSSSP.Decremental.Edge b) e f) (@Eq.{1} Nat a c) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.2.2.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreMemory.field_above_base : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (e : DecrAlmostLinearSSSP.Decremental.Edge b) (a : Nat),
  @LT.lt.{0} Nat instLTNat B (DecrAlmostLinearSSSP.Decremental.CoreMemory.field b B e a) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreMemory.gradient_above_base : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (v : Fin b.input.n),
  @LT.lt.{0} Nat instLTNat B (DecrAlmostLinearSSSP.Decremental.CoreMemory.gradientCell b B v) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4.2.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreGeometry.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreGeometry.code s
    (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))
    (DecrAlmostLinearSSSP.Decremental.CoreGeometry.result s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.1.1.1.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.CoreDegree.nat_frame : ∀ (vertex k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 620) (instOfNatNat (nat_lit 620))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 662) (instOfNatNat (nat_lit 662))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.CoreDegree.code vertex) k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.2.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreDegree.real_frame : ∀ (vertex k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.CoreDegree.code vertex) k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.2.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreTape.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreTape.code s
    (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (DecrAlmostLinearSSSP.Decremental.CoreTape.result s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5.1.2.2.2.1.1
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
theorem DecrAlmostLinearSSSP.Decremental.CoreRefresh.result_values : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  And
    (@Eq.{1} Real
      ((DecrAlmostLinearSSSP.Decremental.CoreRefresh.result s).realReg
        (@OfNat.ofNat.{0} Nat (nat_lit 616) (instOfNatNat (nat_lit 616))))
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 606) (instOfNatNat (nat_lit 606))))
          (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 608) (instOfNatNat (nat_lit 608)))))
        (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 610) (instOfNatNat (nat_lit 610))))))
    (And
      (@Eq.{1} Real
        ((DecrAlmostLinearSSSP.Decremental.CoreRefresh.result s).realReg
          (@OfNat.ofNat.{0} Nat (nat_lit 612) (instOfNatNat (nat_lit 612))))
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 602) (instOfNatNat (nat_lit 602))))
          (@Max.max.{0} Real Real.instMax
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 604) (instOfNatNat (nat_lit 604))))
              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 606) (instOfNatNat (nat_lit 606))))
                  (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 608) (instOfNatNat (nat_lit 608)))))
                (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 610) (instOfNatNat (nat_lit 610))))))
            (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 506) (instOfNatNat (nat_lit 506)))))))
      (@Eq.{1} Real
        ((DecrAlmostLinearSSSP.Decremental.CoreRefresh.result s).realReg
          (@OfNat.ofNat.{0} Nat (nat_lit 614) (instOfNatNat (nat_lit 614))))
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          ((DecrAlmostLinearSSSP.Decremental.CoreRefresh.result s).realReg
            (@OfNat.ofNat.{0} Nat (nat_lit 612) (instOfNatNat (nat_lit 612))))
          (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 600) (instOfNatNat (nat_lit 600))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.1.2.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreRefresh.no_memory : DecrAlmostLinearSSSP.Decremental.Structured.NoMemory DecrAlmostLinearSSSP.Decremental.CoreRefresh.code := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.1.2.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreRefresh.nat_frame : ∀ (k : Nat), DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreRefresh.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.1.2.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreRefresh.real_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 612) (instOfNatNat (nat_lit 612))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 614) (instOfNatNat (nat_lit 614))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 616) (instOfNatNat (nat_lit 616))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 618) (instOfNatNat (nat_lit 618))) →
          DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreRefresh.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.1.2.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreRefresh.result_capacity : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (e : DecrAlmostLinearSSSP.Decremental.Edge b) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 602) (instOfNatNat (nat_lit 602))))
      (DecrAlmostLinearSSSP.Decremental.coefficient b e) →
    @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 604) (instOfNatNat (nat_lit 604))))
        (DecrAlmostLinearSSSP.Decremental.cost b (@DecrAlmostLinearSSSP.Decremental.State.active b state) e) →
      @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 606) (instOfNatNat (nat_lit 606))))
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (DecrAlmostLinearSSSP.Decremental.initialLabel b (DecrAlmostLinearSSSP.Decremental.tail b e))
            (DecrAlmostLinearSSSP.Decremental.initialLabel b (DecrAlmostLinearSSSP.Decremental.head b e))) →
        @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 608) (instOfNatNat (nat_lit 608))))
            (@DecrAlmostLinearSSSP.Decremental.State.y b state (DecrAlmostLinearSSSP.Decremental.tail b e)) →
          @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 610) (instOfNatNat (nat_lit 610))))
              (@DecrAlmostLinearSSSP.Decremental.State.y b state (DecrAlmostLinearSSSP.Decremental.head b e)) →
            @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 506) (instOfNatNat (nat_lit 506))))
                (DecrAlmostLinearSSSP.Decremental.kappa b) →
              @Eq.{1} Real
                ((DecrAlmostLinearSSSP.Decremental.CoreRefresh.result s).realReg
                  (@OfNat.ofNat.{0} Nat (nat_lit 612) (instOfNatNat (nat_lit 612))))
                (DecrAlmostLinearSSSP.Decremental.capacity b (@DecrAlmostLinearSSSP.Decremental.State.active b state)
                  (DecrAlmostLinearSSSP.Decremental.labels b state) e) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.1.2.1.2.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.CoreGradient.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 550) (instOfNatNat (nat_lit 550))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 632) (instOfNatNat (nat_lit 632))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 634) (instOfNatNat (nat_lit 634))) →
        DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreGradient.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.2.1.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreGradient.real_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 628) (instOfNatNat (nat_lit 628))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
      DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreGradient.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreGradientEndpoints.head_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreGradientEndpoints.headCode s
    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
    (DecrAlmostLinearSSSP.Decremental.CoreGradientEndpoints.headPrepared s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_6.2.2.1.1.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.body_nat_frame : ∀ (k : Nat),
  Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 550) (instOfNatNat (nat_lit 550))))
      (Or (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 552) (instOfNatNat (nat_lit 552))))
        (Or (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 554) (instOfNatNat (nat_lit 554))))
          (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 662) (instOfNatNat (nat_lit 662))) k))) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.body k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_7.1.1.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.body_real_frame : ∀ (k : Nat),
  Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 602) (instOfNatNat (nat_lit 602))))
      (Or (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 608) (instOfNatNat (nat_lit 608))))
        (Or (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 610) (instOfNatNat (nat_lit 610))))
          (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) k))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.body k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_7.1.1.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.even_registers : @Eq.{1} Bool
  (DecrAlmostLinearSSSP.Decremental.Structured.evenRegisters DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.code)
  Bool.true := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_7.1.1.1.2.1.1
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
theorem DecrAlmostLinearSSSP.Decremental.CorePending.dequeue : ∀ {l : Nat} (B : Nat) (xs : List.{0} (Fin l)) (e : Fin l) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
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
                        @Eq.{1} Nat (t.natMem j) (s.natMem j))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_8.1.1.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.CorePending.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 546) (instOfNatNat (nat_lit 546))) →
    Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 562) (instOfNatNat (nat_lit 562))))
        (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 572) (instOfNatNat (nat_lit 572))) k) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CorePending.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_8.1.1.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.CorePending.real_frame : ∀ (k : Nat), DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CorePending.code k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_8.1.1.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.CorePending.pop_nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 546) (instOfNatNat (nat_lit 546))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))) →
      Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 562) (instOfNatNat (nat_lit 562))))
          (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 572) (instOfNatNat (nat_lit 572))) k) →
        DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CorePending.popCode k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_8.1.1.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.CorePending.pop_real_frame : ∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CorePending.popCode k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_8.1.1.2.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.CorePending.MemoryFrame.refl : ∀ (B l : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CorePending.MemoryFrame B l s s := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_8.1.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CorePending.MemoryFrame.trans : ∀ {B l : Nat} {s t u : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.CorePending.MemoryFrame B l s t →
    DecrAlmostLinearSSSP.Decremental.CorePending.MemoryFrame B l t u →
      DecrAlmostLinearSSSP.Decremental.CorePending.MemoryFrame B l s u := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_8.1.1.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CorePending.MemoryFrame.guest : ∀ {B l : Nat} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
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
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_8.1.1.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreRequest.endpoint_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreRequest.endpointCode s
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    (DecrAlmostLinearSSSP.Decremental.CoreRequest.endpoints s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_8.1.2.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreRequest.endpoint_nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 636) (instOfNatNat (nat_lit 636))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 638) (instOfNatNat (nat_lit 638))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreRequest.endpointCode k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_8.1.2.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreRequest.endpoint_real_frame : ∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreRequest.endpointCode k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_8.1.2.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreRequest.toggle_eval : ∀ {n k : Nat} (B R N : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program)
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
              t) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_8.1.2.2.2.1.1
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
theorem DecrAlmostLinearSSSP.Decremental.CoreHost.preserves_ratio : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b),
  @LE.le.{0} Nat instLENat b.input.n B →
    DecrAlmostLinearSSSP.Decremental.CoreHost.Preserves b B K state
      DecrAlmostLinearSSSP.Decremental.CoreRequest.ratioCode := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_8.2.1.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreHost.preserves_toggle : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b),
  @LE.le.{0} Nat instLENat b.input.n B →
    DecrAlmostLinearSSSP.Decremental.CoreHost.Preserves b B K state
      DecrAlmostLinearSSSP.Decremental.CoreRequest.toggleCode := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_8.2.1.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.advance : ∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {B N m exponent : Nat} {K K0 ξ h Γ init : Real}
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
                                              exponent impl K0 ξ h Γ init t next).work)))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_8.2.2.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreSource.Image.command_frame : ∀ (B R N : Nat) (g : DecrAlmostLinearSSSP.Decremental.Machine) {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data}
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
            DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N g t := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_8.2.2.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreHost.Image.command_frame : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
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
              DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state t := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_8.2.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CutModel.toggle_complete : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) {l : Nat}
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
            reports := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_8.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CutModel.toggle : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) {l : Nat}
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
            t := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_8.2.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CutModel.ratio : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) {l : Nat}
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
                (@Eq.{1} Bool (@DecrAlmostLinearSSSP.Decremental.CutState.hasCut b.input.n l t) Bool.true)) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_8.2.2.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.labels : ∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {B N m exponent : Nat} {K K0 ξ h Γ init : Real}
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
            @DecrAlmostLinearSSSP.Decremental.CutModel b (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b) state
                (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                  (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m exponent impl K0 ξ h Γ init s
                    ctx)) →
              ∀ (a z : Fin b.input.n),
                @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 636) (instOfNatNat (nat_lit 636))))
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val b.input.n a)) →
                  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 638) (instOfNatNat (nat_lit 638))))
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val b.input.n z)) →
                    ∃ cost t next,
                      And
                        (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                          (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.labelsCode N impl.program) s cost t)
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
                                  (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16))) N))
                              (@OfNat.ofNat.{0} Nat (nat_lit 46) (instOfNatNat (nat_lit 46)))))
                          (And (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state t)
                            (And
                              (@DecrAlmostLinearSSSP.Decremental.CutModel b
                                (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b) state
                                (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                  (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m exponent impl
                                    K0 ξ h Γ init t next)))
                              (And
                                (@Eq.{1} Real
                                  (t.realReg (@OfNat.ofNat.{0} Nat (nat_lit 608) (instOfNatNat (nat_lit 608))))
                                  (@DecrAlmostLinearSSSP.Decremental.State.y b state a))
                                (And
                                  (@Eq.{1} Real
                                    (t.realReg (@OfNat.ofNat.{0} Nat (nat_lit 610) (instOfNatNat (nat_lit 610))))
                                    (@DecrAlmostLinearSSSP.Decremental.State.y b state z))
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
                                              (DecrAlmostLinearSSSP.Decremental.logicalCount b) a)
                                            (@List.cons.{0}
                                              (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                              (@DecrAlmostLinearSSSP.Decremental.CutOp.queryY b.input.n
                                                (DecrAlmostLinearSSSP.Decremental.logicalCount b) z)
                                              (@List.nil.{0}
                                                (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                  (DecrAlmostLinearSSSP.Decremental.logicalCount b)))))))
                                      (And
                                        (∃ middle,
                                          @Eq.{1} (List.{0} DecrAlmostLinearSSSP.Decremental.Machine)
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
                                              (@List.cons.{0} DecrAlmostLinearSSSP.Decremental.Machine middle
                                                (@List.cons.{0} DecrAlmostLinearSSSP.Decremental.Machine
                                                  (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                                    m exponent impl K0 ξ h Γ init t next)
                                                  (@List.nil.{0} DecrAlmostLinearSSSP.Decremental.Machine)))))
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
                                                exponent impl K0 ξ h Γ init s ctx)))))))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_9.1.1.1.1.1.1
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
theorem DecrAlmostLinearSSSP.Decremental.RuntimeBounds.refresh : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.State b),
      DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K s →
        ∀ (e : DecrAlmostLinearSSSP.Decremental.Edge b),
          DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K (DecrAlmostLinearSSSP.Decremental.refresh b s e) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_9.1.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.RuntimeBounds.toggle : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LE.le.{0} Real Real.instLE
      (@OfNat.ofNat.{0} Real (nat_lit 32)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
      K →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.State b),
      DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K s →
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
                    DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K
                      (DecrAlmostLinearSSSP.Decremental.reportedToggle b K s r reports) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_9.1.2.2.2.2.2.2
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
theorem DecrAlmostLinearSSSP.Decremental.CutModel.refresh : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) {l : Nat}
  (E : Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)) (s : DecrAlmostLinearSSSP.Decremental.State b)
  (e : DecrAlmostLinearSSSP.Decremental.Edge b) (c c1 c2 c3 : DecrAlmostLinearSSSP.Decremental.CutState b.input.n l)
  (K ξ : Real) (g1 g2 g3 : DecrAlmostLinearSSSP.Decremental.Machine),
  @DecrAlmostLinearSSSP.Decremental.CutModel b l E s c →
    @DecrAlmostLinearSSSP.Decremental.CutTransition b.input.n l K ξ c
        (@DecrAlmostLinearSSSP.Decremental.CutOp.erase b.input.n l
          (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l))
            (DecrAlmostLinearSSSP.Decremental.Edge b) (fun x => Fin l)
            (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l))
              (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)
              (@Equiv.instEquivLike.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)))
            E e))
        g1 c1 →
      @DecrAlmostLinearSSSP.Decremental.CutTransition b.input.n l K ξ c1
          (@DecrAlmostLinearSSSP.Decremental.CutOp.insert b.input.n l
            (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l))
              (DecrAlmostLinearSSSP.Decremental.Edge b) (fun x => Fin l)
              (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l))
                (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)
                (@Equiv.instEquivLike.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)))
              E e)
            (DecrAlmostLinearSSSP.Decremental.tail b e) (DecrAlmostLinearSSSP.Decremental.head b e)
            (DecrAlmostLinearSSSP.Decremental.capacity b (@DecrAlmostLinearSSSP.Decremental.State.active b s)
              (DecrAlmostLinearSSSP.Decremental.labels b s) e))
          g2 c2 →
        @DecrAlmostLinearSSSP.Decremental.CutTransition b.input.n l K ξ c2
            (@DecrAlmostLinearSSSP.Decremental.CutOp.paired b.input.n l (DecrAlmostLinearSSSP.Decremental.head b e)
              (DecrAlmostLinearSSSP.Decremental.tail b e)
              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                (DecrAlmostLinearSSSP.Decremental.capacity b (@DecrAlmostLinearSSSP.Decremental.State.active b s)
                  (DecrAlmostLinearSSSP.Decremental.labels b s) e)
                (@DecrAlmostLinearSSSP.Decremental.State.cache b s e)))
            g3 c3 →
          @DecrAlmostLinearSSSP.Decremental.CutModel b l E (DecrAlmostLinearSSSP.Decremental.refresh b s e) c3 := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_9.2.1.2.2.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.CutModel.toggle_valid : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) {l : Nat}
  (E : Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)) (s : DecrAlmostLinearSSSP.Decremental.State b)
  (c : DecrAlmostLinearSSSP.Decremental.CutState b.input.n l) (K : Real),
  @DecrAlmostLinearSSSP.Decremental.CutModel b l E s c →
    @Eq.{1} Bool (@DecrAlmostLinearSSSP.Decremental.CutState.hasCut b.input.n l c) Bool.true →
      @Ne.{1} (Fin b.input.n → Real) (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b s)
          (@OfNat.ofNat.{0} (Fin b.input.n → Real) (nat_lit 0)
            (@Zero.toOfNat0.{0} (Fin b.input.n → Real)
              (@Pi.instZero.{0, 0} (Fin b.input.n) (fun a => Real) fun i => Real.instZero))) →
        @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (@DecrAlmostLinearSSSP.Decremental.CutState.lastU b.input.n l c) →
          @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) K →
            @DecrAlmostLinearSSSP.Decremental.CutOp.Valid b.input.n l c
              (@DecrAlmostLinearSSSP.Decremental.CutOp.toggle b.input.n l
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@HPow.hPow.{0, 0, 0} Real Nat Real
                      (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) K
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@DecrAlmostLinearSSSP.Decremental.CutState.lastU b.input.n l c)))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_9.2.2.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.RuntimeBounds.refresh_validity : ∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.State b),
      DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K s →
        ∀ (e : DecrAlmostLinearSSSP.Decremental.Edge b), DecrAlmostLinearSSSP.Decremental.RefreshValidity b s e := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_9.2.2.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.physical_refresh_validated : ∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {B N : Nat} {K K0 ξ h Γ init : Real}
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
      impl K0 ξ h Γ init s),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    @LE.le.{0} Nat instLENat b.input.n B →
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) N →
        @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.registerBound impl.program.code) N →
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
                  impl K0 ξ h Γ init s ctx)) →
            ∀ (e : DecrAlmostLinearSSSP.Decremental.Edge b),
              DecrAlmostLinearSSSP.Decremental.RefreshValidity b state e →
                @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
                    (DecrAlmostLinearSSSP.Decremental.CoreMemory.encodedEdge b e) →
                  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626))))
                      (@Fin.val b.input.n (DecrAlmostLinearSSSP.Decremental.tail b e)) →
                    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 628) (instOfNatNat (nat_lit 628))))
                        (@Fin.val b.input.n (DecrAlmostLinearSSSP.Decremental.head b e)) →
                      @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 612) (instOfNatNat (nat_lit 612))))
                          (DecrAlmostLinearSSSP.Decremental.capacity b
                            (@DecrAlmostLinearSSSP.Decremental.State.active b state)
                            (DecrAlmostLinearSSSP.Decremental.labels b state) e) →
                        @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 614) (instOfNatNat (nat_lit 614))))
                            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                              (DecrAlmostLinearSSSP.Decremental.capacity b
                                (@DecrAlmostLinearSSSP.Decremental.State.active b state)
                                (DecrAlmostLinearSSSP.Decremental.labels b state) e)
                              (@DecrAlmostLinearSSSP.Decremental.State.cache b state e)) →
                          ∃ cost t next,
                            And
                              (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.physicalRefreshCode N impl.program) s
                                cost t)
                              (And
                                (@LE.le.{0} Nat instLENat cost
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (DecrAlmostLinearSSSP.Decremental.dispatchCharge impl.program.code)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                                          (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                b.input.size)
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                  b.weightExponent)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                              impl K0 ξ h Γ init t next).work
                                          (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                b.input.size)
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                  b.weightExponent)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                              impl K0 ξ h Γ init s ctx).work))
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 24) (instOfNatNat (nat_lit 24))) N))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 85) (instOfNatNat (nat_lit 85)))))
                                (And (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state t)
                                  (And
                                    (@DecrAlmostLinearSSSP.Decremental.CutModel b
                                      (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                      (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b)
                                      (DecrAlmostLinearSSSP.Decremental.refresh b state e)
                                      (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                        (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                              b.weightExponent)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                          impl K0 ξ h Γ init t next)))
                                    (And
                                      (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                                        (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.first b B N
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                              b.weightExponent)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                          impl K0 ξ h Γ init t next)
                                        (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.first b B N
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                              b.weightExponent)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                          impl K0 ξ h Γ init s ctx))
                                      (And
                                        (@Eq.{1}
                                          (List.{0}
                                            (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                              (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                          (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                              b.input.size)
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                b.weightExponent)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
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
                                            (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                b.input.size)
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                  b.weightExponent)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                              impl K0 ξ h Γ init s ctx)
                                            (@List.cons.{0}
                                              (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                              (@DecrAlmostLinearSSSP.Decremental.CutOp.erase b.input.n
                                                (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                                (@DFunLike.coe.{1, 1, 1}
                                                  (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                    (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                                  (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                  (fun x => Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                                  (@EquivLike.toFunLike.{1, 1, 1}
                                                    (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                      (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                                    (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                    (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                                    (@Equiv.instEquivLike.{1, 1}
                                                      (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                      (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))))
                                                  (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b) e))
                                              (@List.cons.{0}
                                                (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                  (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                                (@DecrAlmostLinearSSSP.Decremental.CutOp.insert b.input.n
                                                  (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                                  (@DFunLike.coe.{1, 1, 1}
                                                    (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                      (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                                    (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                    (fun x => Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                                    (@EquivLike.toFunLike.{1, 1, 1}
                                                      (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                        (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                                      (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                      (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                                      (@Equiv.instEquivLike.{1, 1}
                                                        (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                        (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))))
                                                    (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b) e)
                                                  (DecrAlmostLinearSSSP.Decremental.tail b e)
                                                  (DecrAlmostLinearSSSP.Decremental.head b e)
                                                  (DecrAlmostLinearSSSP.Decremental.capacity b
                                                    (@DecrAlmostLinearSSSP.Decremental.State.active b state)
                                                    (DecrAlmostLinearSSSP.Decremental.labels b state) e))
                                                (@List.cons.{0}
                                                  (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                    (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                                  (@DecrAlmostLinearSSSP.Decremental.CutOp.paired b.input.n
                                                    (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                                    (DecrAlmostLinearSSSP.Decremental.head b e)
                                                    (DecrAlmostLinearSSSP.Decremental.tail b e)
                                                    (@HSub.hSub.{0, 0, 0} Real Real Real
                                                      (@instHSub.{0} Real Real.instSub)
                                                      (DecrAlmostLinearSSSP.Decremental.capacity b
                                                        (@DecrAlmostLinearSSSP.Decremental.State.active b state)
                                                        (DecrAlmostLinearSSSP.Decremental.labels b state) e)
                                                      (@DecrAlmostLinearSSSP.Decremental.State.cache b state e)))
                                                  (@List.nil.{0}
                                                    (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                      (DecrAlmostLinearSSSP.Decremental.logicalCount b))))))))
                                        (And
                                          (@LE.le.{0} Nat instLENat
                                            (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                  b.input.size)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                    b.weightExponent)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                impl K0 ξ h Γ init s ctx).work
                                            (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                  b.input.size)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                    b.weightExponent)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                impl K0 ξ h Γ init t next).work)
                                          (@Eq.{1} Nat
                                            (DecrAlmostLinearSSSP.Decremental.reportVolume
                                              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines b B N
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                  b.input.size)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                    b.weightExponent)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                impl K0 ξ h Γ init t next))
                                            (DecrAlmostLinearSSSP.Decremental.reportVolume
                                              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines b B N
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                  b.input.size)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                    b.weightExponent)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                impl K0 ξ h Γ init s ctx))))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_9.2.2.1.2.2.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.CoreGeometry.result_addresses : ∀ (root : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 568) (instOfNatNat (nat_lit 568)))) root →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
      DecrAlmostLinearSSSP.Decremental.CoreRecord.Addresses root
        (DecrAlmostLinearSSSP.Decremental.CoreGeometry.result s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_9.2.2.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreNativeCut.labels_nat_frame : ∀ (N : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program) (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 54) (instOfNatNat (nat_lit 54))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 632) (instOfNatNat (nat_lit 632))) →
              DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
                (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.labelsCode N p) k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_9.2.2.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreNativeCut.physical_refresh_nat_frame : ∀ (N : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program) (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 54) (instOfNatNat (nat_lit 54))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 632) (instOfNatNat (nat_lit 632))) →
              @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 636) (instOfNatNat (nat_lit 636))) →
                @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 638) (instOfNatNat (nat_lit 638))) →
                  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
                    (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.physicalRefreshCode N p) k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_9.2.2.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.CoreNativeCut.physical_refresh_real_frame : ∀ (N : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program) (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
        (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.physicalRefreshCode N p) k := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_9.2.2.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.CoreNativeCut.labels_loaded : ∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {state : DecrAlmostLinearSSSP.Decremental.State b}
  {e : DecrAlmostLinearSSSP.Decremental.Edge b} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {cost N : Nat}
  {p : DecrAlmostLinearSSSP.Decremental.Program},
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.labelsCode N p) s
      cost t →
    DecrAlmostLinearSSSP.Decremental.CoreGeometry.Loaded b state e s →
      DecrAlmostLinearSSSP.Decremental.CoreGeometry.Loaded b state e t := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_9.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreNativeCut.labels_addresses : ∀ {base : Nat} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {cost N : Nat}
  {p : DecrAlmostLinearSSSP.Decremental.Program},
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.labelsCode N p) s
      cost t →
    DecrAlmostLinearSSSP.Decremental.CoreRecord.Addresses base s →
      DecrAlmostLinearSSSP.Decremental.CoreRecord.Addresses base t := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_9.2.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.CoreRefreshRead.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreRefreshRead.code s
    (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19)))
    (DecrAlmostLinearSSSP.Decremental.CoreRefreshRead.result s) := DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_9.2.2.2.2.2.2.2
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
lemma no_memory : NoMemory code := by
  simp [code,CorePending.prefixCode,CorePending.prefixAtoms,CoreGeometry.code,CoreGeometry.addressCode,
    CoreGeometry.addressAtoms,CoreGeometry.loadCode,CoreGeometry.loadAtoms,CoreRequest.endpointCode,
    Structured.sequence,NoMemory,NoStore,nadd]
lemma even_registers : evenRegisters code = true := by decide
lemma nat_frame (k : ℕ) (hk : k < 562 ∨ 648 < k) : NatFrame code k := by
  simp [code,CorePending.prefixCode,CorePending.prefixAtoms,CoreGeometry.code,CoreGeometry.addressCode,
    CoreGeometry.addressAtoms,CoreGeometry.loadCode,CoreGeometry.loadAtoms,CoreRequest.endpointCode,
    Structured.sequence,NatFrame,writesNat,nadd]
  omega
lemma real_frame (k : ℕ) (hk : k < 600 ∨ 606 < k) : RealFrame code k := by
  simp [code,CorePending.prefixCode,CorePending.prefixAtoms,CoreGeometry.code,CoreGeometry.addressCode,
    CoreGeometry.addressAtoms,CoreGeometry.loadCode,CoreGeometry.loadAtoms,CoreRequest.endpointCode,
    Structured.sequence,RealFrame,writesReal,nadd]
  omega
lemma correct (b : Core) (B : ℕ) (K : ℝ) (state : State b) (e : Edge b) (s : Data)
    (h : CoreHost.Image b B K state s) (hB : b.input.n ≤ B)
    (he : s.natReg 560 = CoreMemory.encodedEdge b e) :
    CoreHost.Image b B K state (result s) ∧ CoreGeometry.Loaded b state e (result s) ∧
      CoreRecord.Addresses (CoreMemory.field b B e 0) (result s) ∧
      (result s).natReg 636 = 2*(tail b e).val ∧ (result s).natReg 638 = 2*(head b e).val := by
  let p := CorePending.prefixData s
  let q := CoreGeometry.result p
  have hp := CorePending.prefix_eval s
  have hq := CoreGeometry.eval_code p
  have hr := CoreRequest.endpoint_eval q
  have hpm := hp.no_memory (show NoMemory CorePending.prefixCode by
    simp [CorePending.prefixCode,CorePending.prefixAtoms,Structured.sequence,NoMemory,NoStore])
  have hpn (k : ℕ) (hk : k < 562 ∨ 572 < k) : p.natReg k = s.natReg k := hp.nat_frame (by
    simp [CorePending.prefixCode,CorePending.prefixAtoms,Structured.sequence,NatFrame,writesNat];omega)
  have hp2 : p.natReg 14 = 2 := (hpn 14 (by omega)).trans h.captured.two
  have hpbase : p.natReg 568 = CoreMemory.field b B e 0 := by
    rw [(CorePending.prefix_fields s).1,h.layout.recordBase,he]
    dsimp [CoreMemory.encodedEdge,CoreMemory.field]
    omega
  have hpgeom := h.geometry.frame b B state (fun _ _ _ => congrFun hpm.1 _) (fun _ _ _ => congrFun hpm.2 _)
  have hload : CoreGeometry.Loaded b state e q := CoreGeometry.loaded_image b B state e p hpgeom hpbase hp2
  have hadd : CoreRecord.Addresses (CoreMemory.field b B e 0) q := CoreGeometry.result_addresses _ p hpbase hp2
  have hhost := h.command_frame b B K state hB (eval_code s) no_memory
    (fun k hk => nat_frame k (Or.inl (by simp only [CoreHost.NatRegisters,List.mem_cons,List.not_mem_nil,or_false] at hk;omega)))
    (fun k hk => real_frame k (Or.inl (by simp only [CoreHost.RealRegisters,List.mem_cons,List.not_mem_nil,or_false] at hk;omega)))
  refine ⟨hhost,hload.frame b state e
    (fun k hk => hr.nat_frame (CoreRequest.endpoint_nat_frame k
      (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk;omega)
      (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk;omega)))
    (fun k _ => hr.real_frame (CoreRequest.endpoint_real_frame k)),
    hadd.frame _ (fun k hk => hr.nat_frame (CoreRequest.endpoint_nat_frame k
      (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk;omega)
      (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk;omega))),?_,?_⟩
  · change Function.update (Function.update q.natReg 636 (q.natReg 626+q.natReg 626)) 638 (q.natReg 628+q.natReg 628) 636 = _
    rw [Function.update_of_ne (by decide : (636:ℕ) ≠ 638),Function.update_self,hload.tail]
    omega
  · change Function.update (Function.update q.natReg 636 (q.natReg 626+q.natReg 626)) 638 (q.natReg 628+q.natReg 628) 638 = _
    rw [Function.update_self,hload.head]
    omega
lemma source_frame (b : Core) (B N : ℕ) (g : Machine) (s : Data) (h : CoreSource.Image B (CoreMemory.sourceRecord b B) N g s) :
    CoreSource.Image B (CoreMemory.sourceRecord b B) N g (result s) :=
  h.command_frame B _ N g (eval_code s) no_memory even_registers
    (fun k hk => nat_frame k (Or.inl (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk;omega)))
end DecrAlmostLinearSSSP.Decremental.CoreRefreshRead
end s324
section s325
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreRefresh
open Structured
lemma computed (b : Core) (B N : ℕ) (K : ℝ) (state : State b) (e : Edge b) (g : Machine) (s : Data)
    (h : CoreHost.Image b B K state s) (hs : CoreSource.Image B (CoreMemory.sourceRecord b B) N g s)
    (hB : b.input.n ≤ B) (hl : CoreGeometry.Loaded b state e s)
    (htail : s.realReg 608 = state.y (tail b e)) (hhead : s.realReg 610 = state.y (head b e)) :
    CoreHost.Image b B K state (result s) ∧
      CoreSource.Image B (CoreMemory.sourceRecord b B) N g (result s) ∧
      (result s).realReg 612 = capacity b state.active (labels b state) e ∧
      (result s).realReg 614 = capacity b state.active (labels b state) e-state.cache e ∧
      ∀ v : ReturnVertex b, e = .inr v → (result s).realReg 616 = labels b state v.val := by
  have he := eval_code s h.captured.zeroR
  have hhost := h.command_frame b B K state hB he no_memory
    (fun k _ => nat_frame k)
    (fun k hk => real_frame k
      (by simp only [CoreHost.RealRegisters,List.mem_cons,List.not_mem_nil,or_false] at hk;omega)
      (by simp only [CoreHost.RealRegisters,List.mem_cons,List.not_mem_nil,or_false] at hk;omega)
      (by simp only [CoreHost.RealRegisters,List.mem_cons,List.not_mem_nil,or_false] at hk;omega)
      (by simp only [CoreHost.RealRegisters,List.mem_cons,List.not_mem_nil,or_false] at hk;omega))
  have hsource := hs.command_frame B _ N g he no_memory (by decide) (fun k _ => nat_frame k)
  have hf := result_capacity b state e s hl.coefficient hl.cost hl.initial htail hhead h.parameters.kappaValue
  refine ⟨hhost,hsource,hf,?_,?_⟩
  · rw [(result_values s).2.2,hf,hl.oldCache]
  · intro v hv
    subst e
    rw [(result_values s).1,hl.initial,htail,hhead]
    simp [tail,head,labels,initialLabel]
end DecrAlmostLinearSSSP.Decremental.CoreRefresh
end s325
section s326
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGeometry
open Structured
lemma Image.write_cache (b : Core) (B : ℕ) (state : State b) (e : Edge b) (f : ℝ) (s : Data)
    (h : Image b B state s) :
    Image b B {state with cache := Function.update state.cache e f}
      {s with realMem := Function.update s.realMem (CoreMemory.field b B e 0) f} := by
  have hdiff (d : Edge b) (offset : ℕ) (ho : offset < 5) (hne : offset ≠ 0) :
      CoreMemory.field b B d offset ≠ CoreMemory.field b B e 0 := by
    intro hh
    exact hne (CoreMemory.field_injective b B d e offset 0 ho (by omega) hh).2
  refine ⟨?_,?_,?_,?_,h.tail,h.head,h.returnFlag,?_⟩
  · intro d
    change Function.update s.realMem (CoreMemory.field b B e 0) f (CoreMemory.field b B d 0) = Function.update state.cache e f d
    by_cases hd : d = e
    · subst d;simp
    · rw [Function.update_of_ne (fun hh => hd (CoreMemory.field_injective b B d e 0 0 (by omega) (by omega) hh).1),
        Function.update_of_ne hd,h.cache d]
  · intro d
    exact (Function.update_of_ne (hdiff d 1 (by omega) (by omega)) _ _).trans (h.coefficient d)
  · intro d
    exact (Function.update_of_ne (hdiff d 2 (by omega) (by omega)) _ _).trans (h.cost d)
  · intro d
    exact (Function.update_of_ne (hdiff d 4 (by omega) (by omega)) _ _).trans (h.initial d)
  · intro v
    exact (Function.update_of_ne (hdiff (.inr v) 3 (by omega) (by omega)) _ _).trans (h.samples v)
end DecrAlmostLinearSSSP.Decremental.CoreGeometry
end s326
section s327
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreHost
open Structured
lemma Image.write_cache (b : Core) (B : ℕ) (K : ℝ) (state : State b) (e : Edge b) (f : ℝ) (s : Data)
    (h : Image b B K state s) (hB : b.input.n ≤ B) :
    Image b B K {state with cache := Function.update state.cache e f}
      {s with realMem := Function.update s.realMem (CoreMemory.field b B e 0) f} := by
  let t : Data := {s with realMem := Function.update s.realMem (CoreMemory.field b B e 0) f}
  have hpublic (v : Fin b.input.n) : t.realMem v.val = s.realMem v.val := by
    apply Function.update_of_ne
    have hh := CoreMemory.field_above_base b B e 0
    have hv := v.isLt
    omega
  have hg (v : Fin b.input.n) : t.realMem (CoreMemory.gradientBase b B+2*v.val) = s.realMem (CoreMemory.gradientBase b B+2*v.val) := by
    apply Function.update_of_ne
    have hh := CoreMemory.field_below_gradient b B e 0 (by omega)
    omega
  refine ⟨h.captured.named_frame b.input (fun _ _ => rfl) (fun _ _ => rfl),
    h.parameters.frame b K (fun _ _ => rfl) (fun _ _ => rfl),
    h.layout.frame b B (fun _ _ => rfl),h.base,h.geometry.write_cache b B state e f s,
    h.gradient.frame _ _ hg rfl,h.pending.frame rfl (fun _ _ _ => rfl),?_,?_⟩
  · intro v
    exact (stored_memory_congr s t v.val rfl (hpublic v)).trans (h.answers v)
  · intro v
    change t.natMem v.val ≤ 1 ∧ (t.natMem v.val = 0 → 0 ≤ t.realMem v.val)
    rw [hpublic v]
    exact h.normal v
end DecrAlmostLinearSSSP.Decremental.CoreHost
end s327
section s328
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGradientDelta
open Structured
lemma even_registers : evenRegisters code = true := by decide
lemma nat_frame (k : ℕ) (h550 : k ≠ 550) (h620 : k ≠ 620) (h632 : k ≠ 632) (h634 : k ≠ 634) : NatFrame code k :=
  ⟨by simp [NatFrame,add,writesNat],by simp [NatFrame,add,writesNat],
    CoreGradientEndpoints.nat_frame k h550 h620 h632 h634,by simp [NatFrame,add,writesNat]⟩
lemma real_frame (k : ℕ) (h612 : k ≠ 612) (h698 : k ≠ 698) (h626 : k ≠ 626) (h628 : k ≠ 628) (h630 : k ≠ 630) : RealFrame code k :=
  ⟨by simp [RealFrame,add,writesReal,Ne.symm h698],by simp [RealFrame,add,writesReal,Ne.symm h612],
    CoreGradientEndpoints.real_frame k h626 h628 h630,by simp [RealFrame,add,writesReal,Ne.symm h612]⟩
lemma eval_code {n : ℕ} (base : ℕ) (g : Fin n → ℝ) (a z : Fin n) (delta f : ℝ) (s : Data)
    (h : CoreGradient.Image base g s) (hb : s.natReg 554 = base)
    (ha : s.natReg 626 = a.val) (hz : s.natReg 628 = z.val)
    (hdelta : s.realReg 614 = delta) (hf : s.realReg 612 = f) (hzero : s.realReg 56 = 0) :
    ∃ cost t, Eval code s cost t ∧ cost ≤ 39 ∧
      CoreGradient.Image base (fun v => g v-(if v = a then delta else 0)+(if v = z then delta else 0)) t ∧
      t.realReg 612 = f ∧ t.natMem = s.natMem ∧
      (∀ j, j ≠ base+2*a.val → j ≠ base+2*z.val → t.realMem j = s.realMem j) := by
  let p : Data := {s with realReg := Function.update s.realReg 698 (s.realReg 612+s.realReg 56)}
  let u : Data := {p with realReg := Function.update p.realReg 612 (p.realReg 614+p.realReg 56)}
  have hp : Eval (add 698 612 56) s 1 p := eval_add s 698 612 56
  have hu : Eval (add 612 614 56) p 1 u := eval_add p 612 614 56
  have huimage : CoreGradient.Image base g u := ⟨h.entries,h.count⟩
  have hudelta : u.realReg 612 = delta := by simp [u,p,hdelta,hzero]
  have hu0 : u.realReg 56 = 0 := by simp [u,p,hzero]
  obtain ⟨cq,q,hq,hcq,hqimage,hqn,hqr⟩ := CoreGradientEndpoints.eval_code base g a z delta u huimage hb ha hz hudelta hu0
  have hq698 : q.realReg 698 = f := by
    rw [hq.real_frame (CoreGradientEndpoints.real_frame 698 (by omega) (by omega) (by omega))]
    simp [u,p,hf,hzero]
  have hq0 : q.realReg 56 = 0 := (hq.real_frame (CoreGradientEndpoints.real_frame 56 (by omega) (by omega) (by omega))).trans hu0
  let t : Data := {q with realReg := Function.update q.realReg 612 (q.realReg 698+q.realReg 56)}
  have ht : Eval (add 612 698 56) q 1 t := eval_add q 612 698 56
  refine ⟨1+(1+(cq+1)),t,Eval.seq hp (Eval.seq hu (Eval.seq hq ht)),by omega,
    ⟨hqimage.entries,hqimage.count⟩,?_,hqn,hqr⟩
  simp [t,hq698,hq0]
end DecrAlmostLinearSSSP.Decremental.CoreGradientDelta
end s328
section s329
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGeometry
open Structured
lemma Image.state_congr (b : Core) (B : ℕ) {before after : State b} {s : Data} (h : Image b B before s)
    (ha : after.active = before.active) (hc : after.cache = before.cache) (hs : after.sample = before.sample) :
    Image b B after s := by
  refine ⟨?_,h.coefficient,?_,h.initial,h.tail,h.head,h.returnFlag,?_⟩
  · intro e;rw [hc];exact h.cache e
  · intro e;rw [ha];exact h.cost e
  · intro v;rw [hs];exact h.samples v
end DecrAlmostLinearSSSP.Decremental.CoreGeometry
namespace DecrAlmostLinearSSSP.Decremental.CoreHost
open Structured
lemma Image.state_congr (b : Core) (B : ℕ) (K : ℝ) {before after : State b} {s : Data} (h : Image b B K before s)
    (ha : after.active = before.active) (hc : after.cache = before.cache)
    (hg : after.cachedGradient = before.cachedGradient) (hp : after.pending = before.pending)
    (hs : after.sample = before.sample) (ho : after.output = before.output) : Image b B K after s := by
  refine ⟨h.captured,h.parameters,h.layout,h.base,h.geometry.state_congr b B ha hc hs,?_,?_,?_,h.normal⟩
  · rw [hg];exact h.gradient
  · rw [hp];exact h.pending
  · intro v;rw [ho];exact h.answers v
end DecrAlmostLinearSSSP.Decremental.CoreHost
end s329
section s330
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreSource
open Structured
lemma Image.host_frame (b : Core) (B N : ℕ) (g : Machine) {s t : Data}
    (h : Image B (CoreMemory.sourceRecord b B) N g s)
    (hn : ∀ k, k ∈ ([74,112,106,50,56] : List ℕ) → t.natReg k = s.natReg k)
    (htail : ∀ j, N ≤ j → t.natReg (shadowReg j) = s.natReg (shadowReg j) ∧ t.realReg (shadowReg j) = s.realReg (shadowReg j))
    (hm : ∀ address, ¬CoreHost.Address b B address → t.natMem address = s.natMem address ∧ t.realMem address = s.realMem address) :
    Image B (CoreMemory.sourceRecord b B) N g t := by
  apply h.frame B _ N g hn htail
  · intro a
    apply hm
    intro ha
    exact ha.guest_disjoint b B _ a rfl
  · exact (hm _ (by intro ha;have hh := ha.below_source b B _;omega)).1
  · intro j hj
    exact hm _ (by intro ha;have hh := ha.below_source b B _;omega)
end DecrAlmostLinearSSSP.Decremental.CoreSource
end s330
section s331
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreHost
open Structured
lemma gradient_delta_image (b : Core) (B : ℕ) (K : ℝ) (state : State b) (a z : Fin b.input.n) (delta : ℝ)
    (s t : Data) (cost : ℕ) (h : Image b B K state s) (hB : b.input.n ≤ B)
    (he : Eval CoreGradientDelta.code s cost t)
    (hg : CoreGradient.Image (CoreMemory.gradientBase b B)
      (fun v => state.cachedGradient v-(if v = a then delta else 0)+(if v = z then delta else 0)) t)
    (hn : t.natMem = s.natMem)
    (hr : ∀ j, j ≠ CoreMemory.gradientCell b B a → j ≠ CoreMemory.gradientCell b B z → t.realMem j = s.realMem j) :
    Image b B K {state with cachedGradient := fun v => state.cachedGradient v-(if v = a then delta else 0)+(if v = z then delta else 0)} t := by
  have hnreg (k : ℕ) (h550 : k ≠ 550) (hk : k < 620) : t.natReg k = s.natReg k :=
    he.nat_frame (CoreGradientDelta.nat_frame k h550 (by omega) (by omega) (by omega))
  have hrreg (k : ℕ) (hk : k ≤ 534) : t.realReg k = s.realReg k :=
    he.real_frame (CoreGradientDelta.real_frame k (by omega) (by omega) (by omega) (by omega) (by omega))
  have hrecords (e : Edge b) (j : ℕ) (hj : j < 5) : t.realMem (CoreMemory.field b B e j) = s.realMem (CoreMemory.field b B e j) := by
    have hh := CoreMemory.field_below_gradient b B e j hj
    apply hr <;> dsimp [CoreMemory.gradientCell] <;> omega
  have hpublic (v : Fin b.input.n) : t.realMem v.val = s.realMem v.val := by
    have ha := CoreMemory.gradient_above_base b B a
    have hz := CoreMemory.gradient_above_base b B z
    have hv := v.isLt
    apply hr <;> omega
  refine ⟨h.captured.named_frame b.input
      (fun k hk => hnreg k (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk;omega)
        (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk;omega))
      (fun k hk => hrreg k (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk;omega)),
    h.parameters.frame b K
      (fun k hk => hnreg k (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk;omega)
        (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk;omega))
      (fun k hk => hrreg k (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk;omega)),
    h.layout.frame b B
      (fun k hk => hnreg k (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk;omega)
        (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk;omega)),
    (hnreg 74 (by omega) (by omega)).trans h.base,
    (h.geometry.frame b B state hrecords (fun _ _ _ => congrFun hn _)).state_congr b B rfl rfl rfl,hg,
    h.pending.frame (hnreg 546 (by omega) (by omega)) (fun _ _ _ => congrFun hn _),?_,?_⟩
  · intro v
    exact (stored_memory_congr s t v.val (congrFun hn _) (hpublic v)).trans (h.answers v)
  · intro v
    simpa only [hn,hpublic v] using h.normal v
lemma gradient_delta_source (b : Core) (B N : ℕ) (g : Machine) (a z : Fin b.input.n)
    (s t : Data) (cost : ℕ) (h : CoreSource.Image B (CoreMemory.sourceRecord b B) N g s)
    (he : Eval CoreGradientDelta.code s cost t) (hn : t.natMem = s.natMem)
    (hr : ∀ j, j ≠ CoreMemory.gradientCell b B a → j ≠ CoreMemory.gradientCell b B z → t.realMem j = s.realMem j) :
    CoreSource.Image B (CoreMemory.sourceRecord b B) N g t := by
  apply h.host_frame b B N g
  · intro k hk
    exact he.nat_frame (CoreGradientDelta.nat_frame k
      (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk;omega)
      (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk;omega)
      (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk;omega)
      (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk;omega))
  · intro j hj
    have hf := evenRegisters_frames _ CoreGradientDelta.even_registers (shadowReg j) (by simp [shadowReg])
    exact ⟨he.nat_frame hf.1,he.real_frame hf.2⟩
  · intro address ha
    refine ⟨congrFun hn _,hr address ?_ ?_⟩
    · intro hh;apply ha;rw [hh];exact address_gradient b B a
    · intro hh;apply ha;rw [hh];exact address_gradient b B z
end DecrAlmostLinearSSSP.Decremental.CoreHost
end s331
section s332
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreHost
open Structured
lemma pop_pending_eval (b : Core) (B : ℕ) (K : ℝ) (state : State b) (e : Edge b) (xs : List (Edge b)) (s : Data)
    (h : Image b B K state s) (hB : b.input.n ≤ B) (hxs : state.pending = e::xs) :
    ∃ t, Eval CorePending.popCode s 9 t ∧ Image b B K {state with pending := xs} t ∧
      t.natReg 560 = CoreMemory.encodedEdge b e ∧ t.realMem = s.realMem ∧
      (∀ j, j ≠ CoreMemory.field b B e 0 → t.natMem j = s.natMem j) := by
  have hv : CorePending.View B ((logicalIndexEquiv b e)::xs.map (logicalIndexEquiv b)) s := by
    simpa only [hxs,List.map_cons] using h.pending
  obtain ⟨t,he,htview,htedge,htr,htn⟩ := CorePending.dequeue B (xs.map (logicalIndexEquiv b)) (logicalIndexEquiv b e) s hv
    h.layout.recordBase h.captured.two h.captured.zeroN
  have hn : ∀ j, j ≠ CoreMemory.field b B e 0 → t.natMem j = s.natMem j := by
    simpa only [CorePending.address,CoreMemory.field] using htn
  have hnreg (k : ℕ) (h546 : k ≠ 546) (hk : k < 560) : t.natReg k = s.natReg k :=
    he.nat_frame (CorePending.pop_nat_frame k h546 (by omega) (by omega))
  have hrreg (k : ℕ) : t.realReg k = s.realReg k := he.real_frame (CorePending.pop_real_frame k)
  have hnatfield (d : Edge b) (offset : ℕ) (ho : offset < 5) (h0 : offset ≠ 0) :
      t.natMem (CoreMemory.field b B d offset) = s.natMem (CoreMemory.field b B d offset) := by
    apply hn
    intro hh
    exact h0 (CoreMemory.field_injective b B d e offset 0 ho (by omega) hh).2
  have hgeom' : CoreGeometry.Image b B {state with pending := xs} t := by
    refine ⟨fun d => (congrFun htr _).trans (h.geometry.cache d),
      fun d => (congrFun htr _).trans (h.geometry.coefficient d),
      fun d => (congrFun htr _).trans (h.geometry.cost d),
      fun d => (congrFun htr _).trans (h.geometry.initial d),
      fun d => (hnatfield d 2 (by omega) (by omega)).trans (h.geometry.tail d),
      fun d => (hnatfield d 3 (by omega) (by omega)).trans (h.geometry.head d),
      fun d => (hnatfield d 4 (by omega) (by omega)).trans (h.geometry.returnFlag d),
      fun v => (congrFun htr _).trans (h.geometry.samples v)⟩
  have hpublic (v : Fin b.input.n) : t.natMem v.val = s.natMem v.val := by
    apply hn
    have hh := CoreMemory.field_above_base b B e 0
    have hv := v.isLt
    omega
  have hnew : Image b B K {state with pending := xs} t := by
    refine ⟨h.captured.named_frame b.input
        (fun k hk => hnreg k (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk;omega)
          (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk;omega)) (fun k _ => hrreg k),
      h.parameters.frame b K
        (fun k hk => hnreg k (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk;omega)
          (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk;omega)) (fun k _ => hrreg k),
      h.layout.frame b B
        (fun k hk => hnreg k (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk;omega)
          (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk;omega)),
      (hnreg 74 (by omega) (by omega)).trans h.base,hgeom',
      h.gradient.frame _ _ (fun _ => congrFun htr _) (hnreg 550 (by omega) (by omega)),htview,?_,?_⟩
    · intro v
      exact (stored_memory_congr s t v.val (hpublic v) (congrFun htr _)).trans (h.answers v)
    · intro v
      simpa only [hpublic v,htr] using h.normal v
  exact ⟨t,he,hnew,htedge,htr,hn⟩
end DecrAlmostLinearSSSP.Decremental.CoreHost
end s332
section s333
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreSource
open Structured
lemma Image.host_real_memory (b : Core) (B N : ℕ) (g : Machine) (s : Data)
    (h : Image B (CoreMemory.sourceRecord b B) N g s) (address : ℕ) (value : ℝ)
    (ha : CoreHost.Address b B address) :
    Image B (CoreMemory.sourceRecord b B) N g {s with realMem := Function.update s.realMem address value} := by
  apply h.host_frame b B N g
  · intro k hk;rfl
  · intro j hj;exact ⟨rfl,rfl⟩
  · intro j hj
    exact ⟨rfl,Function.update_of_ne (by intro hh;apply hj;rw [hh];exact ha) _ _⟩
lemma Image.host_nat_memory (b : Core) (B N : ℕ) (g : Machine) (s : Data)
    (h : Image B (CoreMemory.sourceRecord b B) N g s) (address value : ℕ)
    (ha : CoreHost.Address b B address) :
    Image B (CoreMemory.sourceRecord b B) N g {s with natMem := Function.update s.natMem address value} := by
  apply h.host_frame b B N g
  · intro k hk;rfl
  · intro j hj;exact ⟨rfl,rfl⟩
  · intro j hj
    exact ⟨Function.update_of_ne (by intro hh;apply hj;rw [hh];exact ha) _ _,rfl⟩
lemma Image.pending_pop (b : Core) (B N : ℕ) (g : Machine) (s t : Data) (cost : ℕ) (e : Edge b)
    (h : Image B (CoreMemory.sourceRecord b B) N g s) (he : Eval CorePending.popCode s cost t)
    (hr : t.realMem = s.realMem) (hn : ∀ j, j ≠ CoreMemory.field b B e 0 → t.natMem j = s.natMem j) :
    Image B (CoreMemory.sourceRecord b B) N g t := by
  apply h.host_frame b B N g
  · intro k hk
    exact he.nat_frame (CorePending.pop_nat_frame k
      (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk;omega)
      (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk;omega)
      (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk;omega))
  · intro j hj
    have heven : evenRegisters CorePending.popCode = true := by decide
    have hf := evenRegisters_frames _ heven (shadowReg j) (by simp [shadowReg])
    exact ⟨he.nat_frame hf.1,he.real_frame hf.2⟩
  · intro address ha
    exact ⟨hn address (by intro hh;apply ha;rw [hh];exact CoreHost.address_field b B e 0 (by omega)),congrFun hr _⟩
end DecrAlmostLinearSSSP.Decremental.CoreSource
end s333
section s334
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreCommit
open Structured
lemma prefix_nat_frame (k : ℕ) (h550 : k ≠ 550) (h620 : k ≠ 620) (h632 : k ≠ 632) (h634 : k ≠ 634) : NatFrame prefixCode k :=
  ⟨by simp [NatFrame,store,writesNat],CoreGradientDelta.nat_frame k h550 h620 h632 h634⟩
lemma prefix_real_frame (k : ℕ) (h612 : k ≠ 612) (h698 : k ≠ 698) (h626 : k ≠ 626) (h628 : k ≠ 628) (h630 : k ≠ 630) : RealFrame prefixCode k :=
  ⟨by simp [RealFrame,store,writesReal],CoreGradientDelta.real_frame k h612 h698 h626 h628 h630⟩
lemma prefix_eval (b : Core) (B N : ℕ) (K : ℝ) (state : State b) (e : Edge b) (f delta : ℝ) (g : Machine) (s : Data)
    (h : CoreHost.Image b B K state s) (hs : CoreSource.Image B (CoreMemory.sourceRecord b B) N g s)
    (hB : b.input.n ≤ B) (hptr : s.natReg 568 = CoreMemory.field b B e 0)
    (ha : s.natReg 626 = (tail b e).val) (hz : s.natReg 628 = (head b e).val)
    (hf : s.realReg 612 = f) (hdelta : s.realReg 614 = delta) :
    ∃ cost t, Eval prefixCode s cost t ∧ cost ≤ 40 ∧
      CoreHost.Image b B K (cacheGradientState b state e f delta) t ∧
      CoreSource.Image B (CoreMemory.sourceRecord b B) N g t ∧ t.realReg 612 = f := by
  let p : Data := {s with realMem := Function.update s.realMem (CoreMemory.field b B e 0) f}
  let st : State b := {state with cache := Function.update state.cache e f}
  have hp : Eval (store 568 612) s 1 p := by simpa only [hptr,hf] using eval_store s 568 612
  have hpm : CoreHost.Image b B K st p := h.write_cache b B K state e f s hB
  have hps : CoreSource.Image B (CoreMemory.sourceRecord b B) N g p :=
    hs.host_real_memory b B N g s (CoreMemory.field b B e 0) f (CoreHost.address_field b B e 0 (by omega))
  obtain ⟨cost,t,he,hcost,htg,htf,htn,htr⟩ := CoreGradientDelta.eval_code (CoreMemory.gradientBase b B)
    state.cachedGradient (tail b e) (head b e) delta f p hpm.gradient hpm.layout.gradientBase ha hz hdelta hf hpm.captured.zeroR
  have htr' : ∀ j, j ≠ CoreMemory.gradientCell b B (tail b e) → j ≠ CoreMemory.gradientCell b B (head b e) → t.realMem j = p.realMem j := htr
  have htm := CoreHost.gradient_delta_image b B K st (tail b e) (head b e) delta p t cost hpm hB he htg htn htr'
  have hts := CoreHost.gradient_delta_source b B N g (tail b e) (head b e) p t cost hps he htn htr'
  refine ⟨1+cost,t,Eval.seq hp he,by omega,?_,hts,htf⟩
  exact htm.state_congr b B K rfl rfl rfl rfl rfl rfl
end DecrAlmostLinearSSSP.Decremental.CoreCommit
end s334
section s335
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreGeometry
open Structured
lemma Image.write_return (b : Core) (B : ℕ) (state : State b) (v : ReturnVertex b) (r : ℝ)
    (s t : Data) (h : Image b B state s) (hB : b.input.n ≤ B)
    (hsample : t.realMem (CoreMemory.field b B (.inr v) 3) = r)
    (hn : ∀ j, j ≠ v.val.val → t.natMem j = s.natMem j)
    (hr : ∀ j, j ≠ v.val.val → j ≠ CoreMemory.field b B (.inr v) 3 → t.realMem j = s.realMem j) :
    Image b B {state with sample := Function.update state.sample v.val r} t := by
  have hprivate (e : Edge b) (j : ℕ) : CoreMemory.field b B e j ≠ v.val.val := by
    have hh := CoreMemory.field_above_base b B e j
    have hv := v.val.isLt
    omega
  have hother (e : Edge b) (j : ℕ) (hj : j < 5) (hne : j ≠ 3) :
      t.realMem (CoreMemory.field b B e j) = s.realMem (CoreMemory.field b B e j) := by
    apply hr _ (hprivate e j)
    intro hh
    exact hne (CoreMemory.field_injective b B e (.inr v) j 3 hj (by omega) hh).2
  refine ⟨fun e => (hother e 0 (by omega) (by omega)).trans (h.cache e),
    fun e => (hother e 1 (by omega) (by omega)).trans (h.coefficient e),
    fun e => (hother e 2 (by omega) (by omega)).trans (h.cost e),
    fun e => (hother e 4 (by omega) (by omega)).trans (h.initial e),
    fun e => (hn _ (hprivate e 2)).trans (h.tail e),
    fun e => (hn _ (hprivate e 3)).trans (h.head e),
    fun e => (hn _ (hprivate e 4)).trans (h.returnFlag e),?_⟩
  intro w
  change t.realMem (CoreMemory.field b B (.inr w) 3) = Function.update state.sample v.val r w.val
  by_cases hw : w.val = v.val
  · have hwv : w = v := Subtype.ext hw
    subst w
    simpa only [Function.update_self] using hsample
  · rw [Function.update_of_ne hw]
    apply Eq.trans (hr _ (hprivate (.inr w) 3) _ ) (h.samples w)
    intro hh
    have heq := (CoreMemory.field_injective b B (.inr w) (.inr v) 3 3 (by omega) (by omega) hh).1
    exact hw (congrArg (fun e : Edge b => match e with | .inl _ => b.input.source | .inr u => u.val) heq)
end DecrAlmostLinearSSSP.Decremental.CoreGeometry
end s335
section s336
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreHost
open Structured
lemma return_write_eval (b : Core) (B : ℕ) (K : ℝ) (state : State b) (v : ReturnVertex b) (r : ℝ) (s : Data)
    (h : Image b B K state s) (hB : b.input.n ≤ B) (hv : s.natReg 626 = v.val.val)
    (haddr : s.natReg 578 = CoreMemory.field b B (.inr v) 3) (hr : s.realReg 616 = r) :
    ∃ cost t, Eval CoreReturn.code s cost t ∧ cost ≤ 11 ∧
      Image b B K {state with sample := Function.update state.sample v.val r, output := Function.update state.output v.val (readout b r)} t ∧
      (∀ j, j ≠ v.val.val → t.natMem j = s.natMem j) ∧
      (∀ j, j ≠ v.val.val → j ≠ CoreMemory.field b B (.inr v) 3 → t.realMem j = s.realMem j) := by
  have hprivate : CoreMemory.field b B (.inr v) 3 ≠ v.val.val := by
    have hh := CoreMemory.field_above_base b B (.inr v) 3
    have hv := v.val.isLt
    omega
  obtain ⟨cost,t,he,hcost,hout,hsample,hnormal,hpositive,hn,hm⟩ :=
    CoreReturn.eval_code b s v.val.val (CoreMemory.field b B (.inr v) 3) r hv haddr hprivate hr
      h.captured.zeroN h.captured.zeroR h.parameters.Qvalue h.parameters.infinityThreshold h.parameters.readoutFactor
  have hnreg (k : ℕ) (hk : k ≤ 554) : t.natReg k = s.natReg k :=
    he.nat_frame (CoreReturn.nat_frame k (by omega) (by omega))
  have hrreg (k : ℕ) (hk : k ≤ 534) : t.realReg k = s.realReg k :=
    he.real_frame (CoreReturn.real_frame k (by omega) (by omega))
  have hpoint (j : ℕ) (hj : j < b.input.n) (hne : j ≠ v.val.val) :
      t.natMem j = s.natMem j ∧ t.realMem j = s.realMem j := by
    refine ⟨hn j hne,hm j hne ?_⟩
    have hh := CoreMemory.field_above_base b B (.inr v) 3
    omega
  have hnewGeom : CoreGeometry.Image b B
      {state with sample := Function.update state.sample v.val r,output := Function.update state.output v.val (readout b r)} t :=
    (h.geometry.write_return b B state v r s t hB hsample hn hm).state_congr b B rfl rfl rfl
  have hgrad : CoreGradient.Image (CoreMemory.gradientBase b B) state.cachedGradient t := by
    apply h.gradient.frame _ _ _ (hnreg 550 (by omega))
    intro w
    apply hm
    · have hh := CoreMemory.gradient_above_base b B w
      have hv := v.val.isLt
      change CoreMemory.gradientCell b B w ≠ v.val.val
      omega
    · have hh := CoreMemory.field_below_gradient b B (.inr v) 3 (by omega)
      dsimp [CoreMemory.gradientCell]
      omega
  have hpending : CorePending.View B (state.pending.map (logicalIndexEquiv b)) t := by
    apply h.pending.frame (hnreg 546 (by omega))
    intro e offset ho
    apply hn
    have hh : B < CorePending.address B e offset := by dsimp [CorePending.address];omega
    have hv := v.val.isLt
    omega
  have hnew : Image b B K {state with sample := Function.update state.sample v.val r, output := Function.update state.output v.val (readout b r)} t := by
    refine ⟨h.captured.named_frame b.input
        (fun k hk => hnreg k (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk;omega))
        (fun k hk => hrreg k (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk;omega)),
      h.parameters.frame b K
        (fun k hk => hnreg k (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk;omega))
        (fun k hk => hrreg k (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk;omega)),
      h.layout.frame b B (fun k hk => hnreg k (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk;omega)),
      (hnreg 74 (by omega)).trans h.base,hnewGeom,hgrad,hpending,?_,?_⟩
    · intro w
      change stored t.machine w.val = Function.update state.output v.val (readout b r) w
      by_cases hw : w = v.val
      · subst w;simpa only [Function.update_self] using hout
      · rw [Function.update_of_ne hw]
        have hwm := hpoint w.val w.isLt (fun hh => hw (Fin.ext hh))
        exact (stored_memory_congr s t w.val hwm.1 hwm.2).trans (h.answers w)
    · intro w
      by_cases hw : w = v.val
      · subst w;exact ⟨hnormal,hpositive⟩
      · have hwm := hpoint w.val w.isLt (fun hh => hw (Fin.ext hh))
        simpa only [hwm.1,hwm.2] using h.normal w
  exact ⟨cost,t,he,hcost,hnew,hn,hm⟩
lemma return_source_frame (b : Core) (B N : ℕ) (g : Machine) (v : ReturnVertex b)
    (s t : Data) (cost : ℕ) (h : CoreSource.Image B (CoreMemory.sourceRecord b B) N g s)
    (hB : b.input.n ≤ B) (he : Eval CoreReturn.code s cost t)
    (hn : ∀ j, j ≠ v.val.val → t.natMem j = s.natMem j)
    (hr : ∀ j, j ≠ v.val.val → j ≠ CoreMemory.field b B (.inr v) 3 → t.realMem j = s.realMem j) :
    CoreSource.Image B (CoreMemory.sourceRecord b B) N g t := by
  apply h.host_frame b B N g
  · intro k hk
    exact he.nat_frame (CoreReturn.nat_frame k
      (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk;omega)
      (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk;omega))
  · intro j hj
    have heven : evenRegisters CoreReturn.code = true := by decide
    have hf := evenRegisters_frames _ heven (shadowReg j) (by simp [shadowReg])
    exact ⟨he.nat_frame hf.1,he.real_frame hf.2⟩
  · intro address ha
    have hpublic : address ≠ v.val.val := by
      intro hh
      apply ha
      rw [hh]
      exact Or.inl (by have hv := v.val.isLt;omega)
    exact ⟨hn address hpublic,hr address hpublic (by intro hh;apply ha;rw [hh];exact address_field b B (.inr v) 3 (by omega))⟩
end DecrAlmostLinearSSSP.Decremental.CoreHost
end s336
section s337
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreCommit
open Structured
lemma return_eval (b : Core) (B N : ℕ) (K : ℝ) (state : State b) (e : Edge b) (g : Machine) (s : Data)
    (h : CoreHost.Image b B K state s) (hs : CoreSource.Image B (CoreMemory.sourceRecord b B) N g s)
    (hB : b.input.n ≤ B) (hflag : s.natReg 648 = CoreGeometry.returnBit b e)
    (htail : s.natReg 626 = (tail b e).val) (haddr : s.natReg 578 = CoreMemory.field b B e 3)
    (hsample : ∀ v : ReturnVertex b, e = .inr v → s.realReg 616 = labels b state v.val) :
    ∃ cost t, Eval returnCode s cost t ∧ cost ≤ 12 ∧
      CoreHost.Image b B K (returnState b state e) t ∧
      CoreSource.Image B (CoreMemory.sourceRecord b B) N g t := by
  cases e with
  | inl e =>
    have ht : ¬(Test.natLess 56 648).holds s := by simp [Test.holds,h.captured.zeroN,hflag,CoreGeometry.returnBit]
    exact ⟨2,s,Eval.branchNo ht (Eval.skip s),by omega,h,hs⟩
  | inr v =>
    have ht : (Test.natLess 56 648).holds s := by simp [Test.holds,h.captured.zeroN,hflag,CoreGeometry.returnBit]
    have htail' : s.natReg 626 = v.val.val := by simpa only [tail] using htail
    obtain ⟨cost,t,he,hcost,htm,htn,htr⟩ := CoreHost.return_write_eval b B K state v (labels b state v.val) s h hB htail' haddr (hsample v rfl)
    have hts := CoreHost.return_source_frame b B N g v s t cost hs hB he htn htr
    exact ⟨cost+1,t,Eval.branchYes ht he,by omega,htm,hts⟩
end DecrAlmostLinearSSSP.Decremental.CoreCommit
end s337
section s338
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreCommit
open Structured
lemma head_eval (b : Core) (B N : ℕ) (K : ℝ) (state : State b) (e : Edge b) (xs : List (Edge b))
    (g : Machine) (s : Data) (h : CoreHost.Image b B K state s)
    (hs : CoreSource.Image B (CoreMemory.sourceRecord b B) N g s) (hB : b.input.n ≤ B)
    (hpend : state.pending = e::xs) (hptr : s.natReg 568 = CoreMemory.field b B e 0)
    (ha : s.natReg 626 = (tail b e).val) (hz : s.natReg 628 = (head b e).val)
    (hflag : s.natReg 648 = CoreGeometry.returnBit b e) (haddr : s.natReg 578 = CoreMemory.field b B e 3)
    (hf : s.realReg 612 = capacity b state.active (labels b state) e)
    (hd : s.realReg 614 = capacity b state.active (labels b state) e-state.cache e)
    (hsample : ∀ v : ReturnVertex b, e = .inr v → s.realReg 616 = labels b state v.val) :
    ∃ cost t, Eval headCode s cost t ∧ cost ≤ 61 ∧
      CoreHost.Image b B K (refresh b state e) t ∧
      CoreSource.Image B (CoreMemory.sourceRecord b B) N g t := by
  let f := capacity b state.active (labels b state) e
  let delta := f-state.cache e
  let st := cacheGradientState b state e f delta
  obtain ⟨cp,p,hp,hcp,hpm,hps,hpf⟩ := prefix_eval b B N K state e f delta g s h hs hB hptr ha hz hf hd
  have hpn (k : ℕ) (h550 : k ≠ 550) (h620 : k ≠ 620) (h632 : k ≠ 632) (h634 : k ≠ 634) : p.natReg k = s.natReg k :=
    hp.nat_frame (prefix_nat_frame k h550 h620 h632 h634)
  have hpflag : p.natReg 648 = CoreGeometry.returnBit b e := (hpn 648 (by omega) (by omega) (by omega) (by omega)).trans hflag
  have hptail : p.natReg 626 = (tail b e).val := (hpn 626 (by omega) (by omega) (by omega) (by omega)).trans ha
  have hpaddr : p.natReg 578 = CoreMemory.field b B e 3 := (hpn 578 (by omega) (by omega) (by omega) (by omega)).trans haddr
  have hpsample : ∀ v : ReturnVertex b, e = .inr v → p.realReg 616 = labels b st v.val := by
    intro v hv
    rw [hp.real_frame (prefix_real_frame 616 (by omega) (by omega) (by omega) (by omega) (by omega)),hsample v hv]
    rfl
  obtain ⟨cr,r,hr,hcr,hrm,hrs⟩ := return_eval b B N K st e g p hpm hps hB hpflag hptail hpaddr hpsample
  have hrpend : (returnState b st e).pending = e::xs := by
    cases e <;> simpa only [returnState,st,cacheGradientState] using hpend
  obtain ⟨t,ht,htm,htedge,htr,htn⟩ := CoreHost.pop_pending_eval b B K (returnState b st e) e xs r hrm hB hrpend
  have hts := hrs.pending_pop b B N g r t 9 e ht htr htn
  have hmap : ((logicalIndexEquiv b e)::xs.map (logicalIndexEquiv b)).Nodup := by
    simpa only [hpend,List.map_cons] using h.pending.nodup
  have hne : ∀ w ∈ xs, w ≠ e := by
    intro w hw heq
    subst w
    exact (List.nodup_cons.mp hmap).1 (List.mem_map.mpr ⟨e,hw,rfl⟩)
  have hfilter : state.pending.filter (fun w => w ≠ e) = xs := by
    rw [hpend]
    simp only [List.filter_cons,ne_self_iff_false,decide_false,Bool.false_eq_true,if_false]
    apply List.filter_eq_self.mpr
    intro w hw
    simpa only [decide_eq_true_eq] using hne w hw
  have htfinal : CoreHost.Image b B K (refresh b state e) t := by
    apply htm.state_congr b B K
    · cases e <;> rfl
    · cases e <;> rfl
    · cases e <;> rfl
    · exact hfilter
    · cases e <;> rfl
    · cases e <;> rfl
  exact ⟨cp+(cr+9),t,Eval.seq hp (Eval.seq hr ht),by omega,htfinal,hts⟩
end DecrAlmostLinearSSSP.Decremental.CoreCommit
end s338
section s339
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
lemma Context.refresh_head_validated {b : Core} {B N : ℕ} {K K0 ξ h Γ init : ℝ}
    {impl : CutImplementation} {state : State b} {s : Data}
    (ctx : Context b B N (2*b.input.size) (4*b.weightExponent+68) impl K0 ξ h Γ init s)
    (host : CoreHost.Image b B K state s) (hB : b.input.n ≤ B) (hN : 10 ≤ N)
    (hBound : registerBound impl.program.code ≤ N)
    (model : CutModel b (logicalIndexEquiv b) state (impl.view b.input.n (logicalCount b) ctx.current))
    (e : Edge b) (xs : List (Edge b)) (hpend : state.pending = e::xs)
    (beforeValid : (indexedPhysical b state (logicalIndexEquiv b)).Valid (2*b.input.size) (4*b.weightExponent+68))
    (refreshValid : RefreshValidity b state e) (afterBounds : RuntimeBounds b K (refresh b state e))
    (he : s.natReg 560 = CoreMemory.encodedEdge b e) :
    ∃ cost t, ∃ next : Context b B N (2*b.input.size) (4*b.weightExponent+68) impl K0 ξ h Γ init t,
      Eval (refreshCode N impl.program) s cost t ∧
      cost ≤ (dispatchCharge impl.program.code+2)*(next.current.work-ctx.current.work)+40*N+218 ∧
      CoreHost.Image b B K (refresh b state e) t ∧ RuntimeBounds b K (refresh b state e) ∧
      CutModel b (logicalIndexEquiv b) (refresh b state e) (impl.view b.input.n (logicalCount b) next.current) ∧
      next.first = ctx.first ∧
      next.ops = ctx.ops++[.queryY (tail b e),.queryY (head b e),.erase (logicalIndexEquiv b e),
        .insert (logicalIndexEquiv b e) (tail b e) (head b e) (capacity b state.active (DecrAlmostLinearSSSP.Decremental.labels b state) e),
        .paired (head b e) (tail b e) (capacity b state.active (DecrAlmostLinearSSSP.Decremental.labels b state) e-state.cache e)] ∧
      ctx.current.work ≤ next.current.work ∧ reportVolume next.machines = reportVolume ctx.machines := by
  let r := CoreRefreshRead.result s
  have hr : Eval CoreRefreshRead.code s 19 r := CoreRefreshRead.eval_code s
  obtain ⟨hrm,hrload,hraddr,hrtail,hrhead⟩ := CoreRefreshRead.correct b B K state e s host hB he
  have hrs := CoreRefreshRead.source_frame b B N ctx.current s ctx.image
  let rctx := ctx.of_image hrs
  have hrmodel : CutModel b (logicalIndexEquiv b) state (impl.view b.input.n (logicalCount b) rctx.current) := model
  have hrvalid : (impl.view b.input.n (logicalCount b) rctx.current).physical.Valid (2*b.input.size) (4*b.weightExponent+68) := by
    rw [hrmodel.physical]
    exact beforeValid
  obtain ⟨cl,l,lctx,hl,hcl,hlm,hlmodel,hltail,hlhead,hlfirst,hlops,hlcs,hlmono,hlR⟩ :=
    rctx.labels hrm hB hN hBound hrvalid hrmodel (tail b e) (head b e) hrtail hrhead
  have hlload := labels_loaded hl hrload
  have hladdr := labels_addresses hl hraddr
  let c := CoreRefresh.result l
  have hc : Eval CoreRefresh.code l 7 c := CoreRefresh.eval_code l hlm.captured.zeroR
  obtain ⟨hcm,hcs,hcf,hcd,hcsample⟩ := CoreRefresh.computed b B N K state e lctx.current l hlm lctx.image hB hlload hltail hlhead
  let cctx := lctx.of_image hcs
  have hce : c.natReg 560 = CoreMemory.encodedEdge b e := by
    rw [hc.nat_frame (CoreRefresh.nat_frame 560),hl.nat_frame (labels_nat_frame N impl.program 560
      (by omega) (by decide) (by omega) (by omega) (by omega) (by omega)),hr.nat_frame (CoreRefreshRead.nat_frame 560 (Or.inl (by omega)))]
    exact he
  have hca : c.natReg 626 = (tail b e).val := (hc.nat_frame (CoreRefresh.nat_frame 626)).trans hlload.tail
  have hcz : c.natReg 628 = (head b e).val := (hc.nat_frame (CoreRefresh.nat_frame 628)).trans hlload.head
  obtain ⟨cp,p,pctx,hp,hcp,hpm,hpmodel,hpfirst,hpops,hpmono,hpR⟩ :=
    cctx.physical_refresh_validated hcm hB hN hBound hlmodel e refreshValid hce hca hcz hcf hcd
  have hpn (k : ℕ) (hk : k ∈ ([568,578,626,648] : List ℕ)) : p.natReg k = l.natReg k := by
    have hframe : NatFrame (physicalRefreshCode N impl.program) k := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl|rfl|rfl|rfl
      all_goals exact physical_refresh_nat_frame N impl.program _ (by omega) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    exact (hp.nat_frame hframe).trans (hc.nat_frame (CoreRefresh.nat_frame k))
  have hpr (k : ℕ) (hk : k ∈ ([612,614,616] : List ℕ)) : p.realReg k = c.realReg k := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl
    all_goals exact hp.real_frame (physical_refresh_real_frame N impl.program _ (by omega) (by decide))
  have hpptr : p.natReg 568 = CoreMemory.field b B e 0 := (hpn 568 (by simp)).trans hladdr.root
  have hpa : p.natReg 626 = (tail b e).val := (hpn 626 (by simp)).trans hlload.tail
  have hpz : p.natReg 628 = (head b e).val :=
    (hp.nat_frame (physical_refresh_nat_frame N impl.program 628 (by omega) (by decide) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega))).trans hcz
  have hpflag : p.natReg 648 = CoreGeometry.returnBit b e := (hpn 648 (by simp)).trans hlload.returnFlag
  have hpaddr : p.natReg 578 = CoreMemory.field b B e 3 := by
    rw [hpn 578 (by simp),hladdr.head]
    dsimp [CoreMemory.field]
  have hpf : p.realReg 612 = capacity b state.active (DecrAlmostLinearSSSP.Decremental.labels b state) e := (hpr 612 (by simp)).trans hcf
  have hpd : p.realReg 614 = capacity b state.active (DecrAlmostLinearSSSP.Decremental.labels b state) e-state.cache e := (hpr 614 (by simp)).trans hcd
  have hpsample : ∀ v : ReturnVertex b, e = .inr v → p.realReg 616 = DecrAlmostLinearSSSP.Decremental.labels b state v.val :=
    fun v hv => (hpr 616 (by simp)).trans (hcsample v hv)
  obtain ⟨cc,t,ht,hcc,htm,hts⟩ := CoreCommit.head_eval b B N K state e xs pctx.current p hpm pctx.image hB hpend
    hpptr hpa hpz hpflag hpaddr hpf hpd hpsample
  let next := pctx.of_image hts
  have hmono1 : ctx.current.work ≤ lctx.current.work := hlmono
  have hmono2 : lctx.current.work ≤ pctx.current.work := hpmono
  have hsum : pctx.current.work-ctx.current.work = (lctx.current.work-ctx.current.work)+
      (pctx.current.work-lctx.current.work) := by omega
  change cl ≤ (dispatchCharge impl.program.code+2)*(lctx.current.work-ctx.current.work)+16*N+46 at hcl
  change cp ≤ (dispatchCharge impl.program.code+2)*(pctx.current.work-lctx.current.work)+24*N+85 at hcp
  have hcost : 19+(cl+(7+(cp+cc))) ≤ (dispatchCharge impl.program.code+2)*(pctx.current.work-ctx.current.work)+40*N+218 := by
    rw [hsum,Nat.mul_add]
    omega
  refine ⟨19+(cl+(7+(cp+cc))),t,next,Eval.seq hr (Eval.seq hl (Eval.seq hc (Eval.seq hp ht))),hcost,
    htm,afterBounds,hpmodel,hpfirst.trans hlfirst,?_,hmono1.trans hmono2,hpR.trans hlR⟩
  change pctx.ops = ctx.ops++_
  rw [hpops]
  change lctx.ops++_ = ctx.ops++_
  rw [hlops]
  simp only [rctx,Context.of_image,List.append_assoc,List.cons_append,List.nil_append]
lemma Context.refresh_head {b : Core} {B N : ℕ} {K K0 ξ h Γ init : ℝ}
    {impl : CutImplementation} {state : State b} {s : Data}
    (ctx : Context b B N (2*b.input.size) (4*b.weightExponent+68) impl K0 ξ h Γ init s)
    (host : CoreHost.Image b B K state s) (hB : b.input.n ≤ B) (hN : 10 ≤ N)
    (hBound : registerBound impl.program.code ≤ N) (hK : 0 < K) (bounds : RuntimeBounds b K state)
    (model : CutModel b (logicalIndexEquiv b) state (impl.view b.input.n (logicalCount b) ctx.current))
    (e : Edge b) (xs : List (Edge b)) (hpend : state.pending = e::xs)
    (he : s.natReg 560 = CoreMemory.encodedEdge b e) :
    ∃ cost t, ∃ next : Context b B N (2*b.input.size) (4*b.weightExponent+68) impl K0 ξ h Γ init t,
      Eval (refreshCode N impl.program) s cost t ∧
      cost ≤ (dispatchCharge impl.program.code+2)*(next.current.work-ctx.current.work)+40*N+218 ∧
      CoreHost.Image b B K (refresh b state e) t ∧ RuntimeBounds b K (refresh b state e) ∧
      CutModel b (logicalIndexEquiv b) (refresh b state e) (impl.view b.input.n (logicalCount b) next.current) ∧
      next.first = ctx.first ∧
      next.ops = ctx.ops++[.queryY (tail b e),.queryY (head b e),.erase (logicalIndexEquiv b e),
        .insert (logicalIndexEquiv b e) (tail b e) (head b e) (capacity b state.active (DecrAlmostLinearSSSP.Decremental.labels b state) e),
        .paired (head b e) (tail b e) (capacity b state.active (DecrAlmostLinearSSSP.Decremental.labels b state) e-state.cache e)] ∧
      ctx.current.work ≤ next.current.work ∧ reportVolume next.machines = reportVolume ctx.machines := by
  exact ctx.refresh_head_validated host hB hN hBound model e xs hpend
    (runtime_indexed_physical_valid b K state bounds (logicalIndexEquiv b) (logicalCount_le b))
    (bounds.refresh_validity b K hK state e) (bounds.refresh b K hK state e) he
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s339
section s340
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreHeadSelect
open Structured
lemma eval_code (s : Data) : Eval code s 1 (result s) := eval_nsub s 560 546 14
lemma nat_frame (k : ℕ) (hk : k ≠ 560) : NatFrame code k := by simp [code,NatFrame,nsub,writesNat,Ne.symm hk]
lemma real_frame (k : ℕ) : RealFrame code k := by simp [code,RealFrame,nsub,writesReal]
lemma no_memory : NoMemory code := by simp [code,NoMemory,nsub,NoStore]
lemma even_registers : evenRegisters code = true := by decide
lemma correct (b : Core) (B N : ℕ) (K : ℝ) (state : State b) (e : Edge b) (xs : List (Edge b)) (g : Machine) (s : Data)
    (h : CoreHost.Image b B K state s) (hs : CoreSource.Image B (CoreMemory.sourceRecord b B) N g s)
    (hB : b.input.n ≤ B) (hpend : state.pending = e::xs) :
    CoreHost.Image b B K state (result s) ∧
      CoreSource.Image B (CoreMemory.sourceRecord b B) N g (result s) ∧
      (result s).natReg 560 = CoreMemory.encodedEdge b e := by
  have he := eval_code s
  have hhm := h.command_frame b B K state hB he no_memory
    (fun k hk => nat_frame k (by simp only [CoreHost.NatRegisters,List.mem_cons,List.not_mem_nil,or_false] at hk;omega))
    (fun k _ => real_frame k)
  have hsm := hs.command_frame B _ N g he no_memory even_registers
    (fun k hk => nat_frame k (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk;omega))
  refine ⟨hhm,hsm,?_⟩
  have hhead : s.natReg 546 = 2*(logicalIndexEquiv b e).val+2 := by
    simpa only [hpend,List.map_cons,CorePending.token] using h.pending.head
  simp only [result,Function.update_self,hhead,h.captured.two,CoreMemory.encodedEdge]
  omega
end DecrAlmostLinearSSSP.Decremental.CoreHeadSelect
end s340
section s341
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
lemma Context.drain_one {b : Core} {B N : ℕ} {K K0 ξ h Γ init : ℝ}
    {impl : CutImplementation} {state : State b} {s : Data}
    (ctx : Context b B N (2*b.input.size) (4*b.weightExponent+68) impl K0 ξ h Γ init s)
    (host : CoreHost.Image b B K state s) (hB : b.input.n ≤ B) (hN : 10 ≤ N)
    (hBound : registerBound impl.program.code ≤ N) (hK : 0 < K) (bounds : RuntimeBounds b K state)
    (model : CutModel b (logicalIndexEquiv b) state (impl.view b.input.n (logicalCount b) ctx.current))
    (e : Edge b) (xs : List (Edge b)) (hpend : state.pending = e::xs) (hrunning : state.stopped = false) :
    ∃ cost t, ∃ next : Context b B N (2*b.input.size) (4*b.weightExponent+68) impl K0 ξ h Γ init t,
      Eval (drainOneCode N impl.program) s cost t ∧
      cost ≤ (dispatchCharge impl.program.code+2)*(next.current.work-ctx.current.work)+40*N+219 ∧
      CoreHost.Image b B K (refresh b state e) t ∧ RuntimeBounds b K (refresh b state e) ∧
      CutModel b (logicalIndexEquiv b) (refresh b state e) (impl.view b.input.n (logicalCount b) next.current) ∧
      RuntimeRepairStep b K state (refresh b state e) ∧
      next.first = ctx.first ∧ next.ops.length = ctx.ops.length+5 ∧
      toggleVolume next.ops = toggleVolume ctx.ops ∧ ctx.current.work ≤ next.current.work ∧ reportVolume next.machines = reportVolume ctx.machines := by
  let u := CoreHeadSelect.result s
  have hu : Eval CoreHeadSelect.code s 1 u := CoreHeadSelect.eval_code s
  obtain ⟨hum,hus,hue⟩ := CoreHeadSelect.correct b B N K state e xs ctx.current s host ctx.image hB hpend
  let uctx := ctx.of_image hus
  obtain ⟨cost,t,next,he,hcost,htm,htbounds,htmodel,htfirst,htops,htmono,htR⟩ :=
    uctx.refresh_head hum hB hN hBound hK bounds model e xs hpend hue
  have hl : next.ops.length = ctx.ops.length+5 := by
    rw [htops]
    simp only [uctx,Context.of_image,List.length_append,List.length_cons,List.length_nil]
  have hvol : toggleVolume next.ops = toggleVolume ctx.ops := by
    rw [htops]
    simp [toggleVolume,List.filter_append,uctx,Context.of_image]
  exact ⟨1+cost,t,next,Eval.seq hu he,by change cost ≤ (dispatchCharge impl.program.code+2)*(next.current.work-ctx.current.work)+40*N+218 at hcost;omega,
    htm,htbounds,htmodel,RuntimeRepairStep.refresh state e xs hrunning hpend,htfirst,hl,hvol,htmono,htR⟩
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s341
section s342
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreCommit
open Structured
lemma head_running_frame : NatFrame headCode 650 := by
  exact ⟨prefix_nat_frame 650 (by omega) (by omega) (by omega) (by omega),
    ⟨CoreReturn.nat_frame 650 (by omega) (by omega),True.intro⟩,
    CorePending.pop_nat_frame 650 (by omega) (by omega) (by omega)⟩
end DecrAlmostLinearSSSP.Decremental.CoreCommit
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
lemma refresh_running_frame (N : ℕ) (p : Program) : NatFrame (refreshCode N p) 650 :=
  ⟨CoreRefreshRead.nat_frame 650 (by omega),
    labels_nat_frame N p 650 (by omega) (by decide) (by omega) (by omega) (by omega) (by omega),
    CoreRefresh.nat_frame 650,
    physical_refresh_nat_frame N p 650 (by omega) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
    CoreCommit.head_running_frame⟩
lemma drain_running_frame (N : ℕ) (p : Program) : NatFrame (drainOneCode N p) 650 :=
  ⟨CoreHeadSelect.nat_frame 650 (by omega),refresh_running_frame N p⟩
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s342
section s343
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreReports
open Structured
attribute [local instance] Classical.propDecidable
lemma push_membership {l : ℕ} (xs : List (Fin l)) (v : ℕ) (e : Fin l) :
    e ∈ push l xs v ↔ e ∈ xs ∨ e.val = v := by
  unfold push
  split_ifs with hv hx
  · constructor
    · exact fun hh => Or.inl hh
    · rintro (hh|hh)
      · exact hh
      · have he : e = ⟨v,hv⟩ := Fin.ext hh
        simpa only [he] using hx
  · simp only [List.mem_cons]
    constructor
    · rintro (hh|hh)
      · exact Or.inr (congrArg Fin.val hh)
      · exact Or.inl hh
    · rintro (hh|hh)
      · exact Or.inr hh
      · exact Or.inl (Fin.ext hh)
  · have hne : e.val ≠ v := by have hh := e.isLt;omega
    simp [hne]
lemma fetch_eval (s : Data) : Eval fetchCode s 4 (fetched s) := eval_sequence_atoms fetchAtoms s
lemma fetch_nat_frame (k : ℕ) (h560 : k ≠ 560) (h584 : k ≠ 584) : NatFrame fetchCode k := by
  simp [fetchCode,fetchAtoms,Structured.sequence,NatFrame,writesNat,h560,h584,Ne.symm h560,Ne.symm h584]
lemma fetch_real_frame (k : ℕ) : RealFrame fetchCode k := by
  simp [fetchCode,fetchAtoms,Structured.sequence,RealFrame,writesReal]
lemma fetch_mem (s : Data) : (fetched s).natMem = s.natMem ∧ (fetched s).realMem = s.realMem := ⟨rfl,rfl⟩
lemma fetch_value (B offset v : ℕ) (s : Data) (hb : s.natReg 74 = B) (h2 : s.natReg 14 = 2)
    (hp : s.natReg 580 = 2*offset) (hm : s.natMem (B+4*offset+2) = 2*v) :
    (fetched s).natReg 560 = 2*v := by
  simp only [fetched,fetchAtoms,List.foldl_cons,List.foldl_nil,Atom.effect,instructionEffect,data,Data.machine]
  simp only [Function.update_self,Function.update_of_ne (by decide : (14 : ℕ) ≠ 584),
    Function.update_of_ne (by decide : (74 : ℕ) ≠ 584),hb,h2,hp]
  convert hm using 1 <;> congr 1 <;> omega
lemma Environment.transfer {B l : ℕ} {s t : Data} (h : Environment B l s)
    (hf : ∀ k, k ∈ ([74,552,14,26,542] : List ℕ) → t.natReg k = s.natReg k) : Environment B l t :=
  ⟨(hf 74 (by simp)).trans h.base,(hf 552 (by simp)).trans h.geometry,
   (hf 14 (by simp)).trans h.two,(hf 26 (by simp)).trans h.one,(hf 542 (by simp)).trans h.limit⟩
lemma body_nat_frame (k : ℕ) (h546 : k ≠ 546) (h560 : k ≠ 560) (h580 : k ≠ 580) (h584 : k ≠ 584)
    (hk : k < 562 ∨ 572 < k) : NatFrame body k := by
  exact ⟨fetch_nat_frame k h560 h584,⟨CorePending.nat_frame k h546 hk,trivial⟩,
    by simp [NatFrame,nadd,writesNat,Ne.symm h580]⟩
lemma body_real_frame (k : ℕ) : RealFrame body k := by
  exact ⟨fetch_real_frame k,⟨CorePending.real_frame k,trivial⟩,by simp [RealFrame,nadd,writesReal]⟩
end DecrAlmostLinearSSSP.Decremental.CoreReports
end s343
section s344
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreReports
open Structured
attribute [local instance] Classical.propDecidable
lemma body_eval (B l offset v : ℕ) (xs : List (Fin l)) (s : Data)
    (henv : Environment B l s) (hv : CorePending.View B xs s)
    (hp : s.natReg 580 = 2*offset) (hm : s.natMem (B+4*offset+2) = 2*v) :
    ∃ cost t, Eval body s cost t ∧ cost ≤ 16 ∧
      CorePending.View B (push l xs v) t ∧ Environment B l t ∧
      t.natReg 580 = 2*(offset+1) ∧ t.realMem = s.realMem ∧
      (∀ j, t.natMem (B+4*j+2) = s.natMem (B+4*j+2)) ∧ CorePending.MemoryFrame B l s t := by
  let a := fetched s
  have heval := fetch_eval s
  have ham : a.natMem = s.natMem := (fetch_mem s).1
  have har : a.realMem = s.realMem := (fetch_mem s).2
  have ha560 : a.natReg 560 = 2*v := fetch_value B offset v s henv.base henv.two hp hm
  have ha580 : a.natReg 580 = 2*offset := (heval.nat_frame (fetch_nat_frame 580 (by omega) (by omega))).trans hp
  have hav : CorePending.View B xs a := hv.frame
    (heval.nat_frame (fetch_nat_frame 546 (by omega) (by omega))) (fun _ _ _ => congrFun ham _)
  have hae : Environment B l a := henv.transfer (fun k hk => heval.nat_frame (fetch_nat_frame k (by simp at hk;omega) (by simp at hk;omega)))
  have branchResult : ∃ cb u, Eval (.branch (.natLess 560 542) CorePending.code .skip) a cb u ∧ cb ≤ 11 ∧
      CorePending.View B (push l xs v) u ∧ u.realMem = s.realMem ∧
      CorePending.MemoryFrame B l s u := by
    by_cases hvl : v < l
    · let e : Fin l := ⟨v,hvl⟩
      obtain ⟨c,u,ys,hu,hc,hys,huv,hlen,hur,huf⟩ := CorePending.enqueue B xs a e hav hae.geometry ha560 hae.one hae.two
      have ht : (Test.natLess 560 542).holds a := by simp only [Test.holds,ha560,hae.limit];omega
      have hys' : ys = push l xs v := by simpa only [push,dif_pos hvl] using hys
      refine ⟨c+1,u,Eval.branchYes ht hu,by omega,by simpa only [hys'] using huv,hur.trans har,?_⟩
      intro j hj
      exact (huf j (hj e).1 (hj e).2).trans (congrFun ham j)
    · have ht : ¬ (Test.natLess 560 542).holds a := by simp only [Test.holds,ha560,hae.limit];omega
      exact ⟨2,a,Eval.branchNo ht (.skip a),by omega,by simpa only [push,dif_neg hvl] using hav,har,
        fun j _ => congrFun ham j⟩
  obtain ⟨cb,u,hub,hcb,huv,hur,huf⟩ := branchResult
  have hu580 : u.natReg 580 = 2*offset := (hub.nat_frame
    ⟨CorePending.nat_frame 580 (by omega) (by omega),trivial⟩).trans ha580
  have hu14 : u.natReg 14 = 2 := (hub.nat_frame
    ⟨CorePending.nat_frame 14 (by omega) (by omega),trivial⟩).trans hae.two
  let t : Data := {u with natReg := Function.update u.natReg 580 (u.natReg 580+u.natReg 14)}
  have ht := eval_nadd u 580 580 14
  have hall : Eval body s (4+(cb+1)) t := Eval.seq heval (Eval.seq hub ht)
  refine ⟨4+(cb+1),t,hall,by omega,?_,?_,?_,hur,fun j => huf.guest j,huf⟩
  · exact huv.frame (by simp [t]) (fun _ _ _ => rfl)
  · exact henv.transfer (fun k hk => hall.nat_frame (body_nat_frame k
      (by simp at hk;omega) (by simp at hk;omega) (by simp at hk;omega)
      (by simp at hk;omega) (by simp at hk;omega)))
  · simp only [t,Function.update_self,hu580,hu14]
    omega
end DecrAlmostLinearSSSP.Decremental.CoreReports
end s344
section s345
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreReports
open Structured
attribute [local instance] Classical.propDecidable
lemma consume_membership {l : ℕ} (xs : List (Fin l)) (reports : List ℕ) (e : Fin l) :
    e ∈ consume l xs reports ↔ e ∈ xs ∨ e.val ∈ reports := by
  induction reports generalizing xs with
  | nil => simp [consume]
  | cons v rest ih =>
    change e ∈ consume l (push l xs v) rest ↔ _
    rw [ih,push_membership]
    simp only [List.mem_cons]
    tauto
lemma loop_eval (B l : ℕ) (reports : List ℕ) (xs : List (Fin l)) (offset : ℕ) (s : Data)
    (henv : Environment B l s) (hv : CorePending.View B xs s)
    (hp : s.natReg 580 = 2*offset) (hc : s.natReg 582 = 2*(offset+reports.length))
    (hm : ∀ j (hj : j < reports.length), s.natMem (B+4*(offset+j)+2) = 2*reports[j]) :
    ∃ cost t, Eval loop s cost t ∧ cost ≤ 18*reports.length+2 ∧
      CorePending.View B (consume l xs reports) t ∧ Environment B l t ∧
      t.natReg 580 = 2*(offset+reports.length) ∧ t.realMem = s.realMem ∧
      (∀ j, t.natMem (B+4*j+2) = s.natMem (B+4*j+2)) ∧ CorePending.MemoryFrame B l s t := by
  induction reports generalizing xs offset s with
  | nil =>
    have htest : ¬ (Test.natLess 580 582).holds s := by simp only [Test.holds,hp,hc,List.length_nil,Nat.add_zero,lt_self_iff_false,not_false_eq_true]
    exact ⟨2,s,Eval.loopNo s htest,by simp,hv,henv,by simpa using hp,rfl,fun _ => rfl,CorePending.MemoryFrame.refl B l s⟩
  | cons v rest ih =>
    have hh : s.natMem (B+4*offset+2) = 2*v := by
      have hh := hm 0 (by simp)
      change s.natMem (B+4*(offset+0)+2) = 2*v at hh
      simpa only [Nat.add_zero] using hh
    obtain ⟨cb,u,hu,hcb,huv,hue,hup,hur,huf,huframe⟩ := body_eval B l offset v xs s henv hv hp hh
    have huc : u.natReg 582 = 2*(offset+1+rest.length) := by
      rw [hu.nat_frame (body_nat_frame 582 (by omega) (by omega) (by omega) (by omega) (by omega)),hc,List.length_cons]
      omega
    have hum : ∀ j (hj : j < rest.length), u.natMem (B+4*(offset+1+j)+2) = 2*rest[j] := by
      intro j hj
      rw [huf]
      have hh := hm (j+1) (by simp only [List.length_cons];omega)
      simp only [List.getElem_cons_succ] at hh
      convert hh using 1 <;> congr 1 <;> omega
    obtain ⟨cr,t,ht,hcr,htv,hte,htp,htr,htf,htframe⟩ := ih (push l xs v) (offset+1) u hue huv hup huc hum
    have htest : (Test.natLess 580 582).holds s := by simp only [Test.holds,hp,hc,List.length_cons];omega
    refine ⟨cb+cr+2,t,Eval.loopYes htest hu ht,?_,htv,hte,?_,htr.trans hur,fun j => (htf j).trans (huf j),huframe.trans htframe⟩
    · simp only [List.length_cons]
      omega
    · simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm 1 rest.length] using htp
end DecrAlmostLinearSSSP.Decremental.CoreReports
end s345
section s346
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreReports
open Structured
attribute [local instance] Classical.propDecidable
lemma reportList_membership {l : ℕ} (g : Machine) (e : Fin l) :
    e.val ∈ reportList g ↔ Reported g e := by
  simp only [reportList,List.mem_ofFn,Reported]
  constructor
  · rintro ⟨j,hj⟩
    exact ⟨j.val,j.isLt,hj⟩
  · rintro ⟨j,hj,hv⟩
    exact ⟨⟨j,hj⟩,hv⟩
lemma setup_eval (s : Data) : Eval setup s 2 (setupData s) := eval_sequence_atoms setupAtoms s
lemma setup_nat_frame (k : ℕ) (h580 : k ≠ 580) (h582 : k ≠ 582) : NatFrame setup k := by
  simp [setup,setupAtoms,Structured.sequence,NatFrame,writesNat,Ne.symm h580,Ne.symm h582]
lemma setup_fields (s : Data) (hz : s.natReg 56 = 0) :
    (setupData s).natReg 580 = 0 ∧ (setupData s).natReg 582 = s.natReg 23 := by
  simp [setupData,setupAtoms,Atom.effect,instructionEffect,data,Data.machine,hz]
lemma setup_mem (s : Data) : (setupData s).natMem = s.natMem ∧ (setupData s).realMem = s.realMem := ⟨rfl,rfl⟩
lemma eval_code (B l : ℕ) (g : Machine) (xs : List (Fin l)) (s : Data)
    (henv : Environment B l s) (hv : CorePending.View B xs s) (hz : s.natReg 56 = 0)
    (hrep : ShadowDataRep B 2 s g) :
    ∃ cost t, Eval code s cost t ∧ cost ≤ 18*reportCount g+4 ∧
      CorePending.View B (consume l xs (reportList g)) t ∧ Environment B l t ∧
      t.realMem = s.realMem ∧ (∀ j, t.natMem (B+4*j+2) = s.natMem (B+4*j+2)) ∧
      (∀ e : Fin l, e ∈ consume l xs (reportList g) ↔ e ∈ xs ∨ Reported g e) ∧ CorePending.MemoryFrame B l s t := by
  let a := setupData s
  have he := setup_eval s
  have ham : a.natMem = s.natMem := (setup_mem s).1
  have har : a.realMem = s.realMem := (setup_mem s).2
  have hae : Environment B l a := henv.transfer (fun k hk => he.nat_frame
    (setup_nat_frame k (by simp at hk;omega) (by simp at hk;omega)))
  have hav : CorePending.View B xs a := hv.frame
    (he.nat_frame (setup_nat_frame 546 (by omega) (by omega))) (fun _ _ _ => congrFun ham _)
  have ha580 : a.natReg 580 = 2*0 := (setup_fields s hz).1
  have ha582 : a.natReg 582 = 2*(0+(reportList g).length) := by
    rw [(setup_fields s hz).2]
    have hh := hrep.natReg 7
    change s.natReg 23 = 2*g.natReg 7 at hh
    simpa only [reportList,List.length_ofFn,Nat.zero_add,reportCount] using hh
  have hentries : ∀ j (hj : j < (reportList g).length), a.natMem (B+4*(0+j)+2) = 2*(reportList g)[j] := by
    intro j hj
    rw [ham]
    have hh := hrep.natMem j
    change s.natMem (B+2*(2*j+1)) = 2*g.natMem j at hh
    simp only [reportList,List.getElem_ofFn,Nat.zero_add]
    convert hh using 1 <;> congr 1 <;> omega
  obtain ⟨cl,t,ht,hcl,htv,hte,htp,htr,htf,htframe⟩ := loop_eval B l (reportList g) xs 0 a hae hav ha580 ha582 hentries
  refine ⟨2+cl,t,Eval.seq he ht,?_,htv,hte,htr.trans har,fun j => (htf j).trans (congrFun ham _),?_,?_⟩
  · simp only [reportList,List.length_ofFn] at hcl
    omega
  · intro e
    rw [consume_membership,reportList_membership]
  · exact (show CorePending.MemoryFrame B l s a from fun j _ => congrFun ham j).trans htframe
end DecrAlmostLinearSSSP.Decremental.CoreReports
end s346
section s347
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreReports
lemma push_length (l : ℕ) (xs : List (Fin l)) (v : ℕ) : (push l xs v).length ≤ xs.length+1 := by
  unfold push
  split_ifs <;> simp <;> omega
lemma consume_length (l : ℕ) (xs : List (Fin l)) (reports : List ℕ) :
    (consume l xs reports).length ≤ xs.length+reports.length := by
  induction reports generalizing xs with
  | nil => simp [consume]
  | cons v reports ih =>
    have hi := ih (push l xs v)
    have hp := push_length l xs v
    change (consume l (push l xs v) reports).length ≤ _
    simp only [List.length_cons]
    omega
lemma initial_reports_length (l : ℕ) (g : Machine) :
    (consume l [] (reportList g)).length ≤ reportCount g := by
  simpa only [List.length_nil,Nat.zero_add,reportList,List.length_ofFn] using consume_length l [] (reportList g)
end DecrAlmostLinearSSSP.Decremental.CoreReports
end s347
section s348
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
lemma Context.ratio {b : Core} {B N m exponent : ℕ} {K K0 ξ h Γ init : ℝ}
    {impl : CutImplementation} {state : State b} {s : Data}
    (ctx : Context b B N m exponent impl K0 ξ h Γ init s) (host : CoreHost.Image b B K state s)
    (hB : b.input.n ≤ B) (hN : 10 ≤ N) (hBound : registerBound impl.program.code ≤ N)
    (hb : (impl.view b.input.n (logicalCount b) ctx.current).physical.Valid m exponent)
    (model : CutModel b (logicalIndexEquiv b) state (impl.view b.input.n (logicalCount b) ctx.current))
    (hn : state.cachedGradient ≠ 0) (hK0 : 0 < K0) (hKK : K0 ≤ K) :
    ∃ cost t, ∃ next : Context b B N m exponent impl K0 ξ h Γ init t,
      Eval (ratioCode N impl.program) s cost t ∧
      cost ≤ (dispatchCharge impl.program.code+2)*(next.current.work-ctx.current.work)+8*N+19 ∧
      CoreHost.Image b B K state t ∧
      CutModel b (logicalIndexEquiv b) state (impl.view b.input.n (logicalCount b) next.current) ∧
      RatioGuarantee (cachedPhysical b state) K
        (impl.view b.input.n (logicalCount b) next.current).lastG
        (impl.view b.input.n (logicalCount b) next.current).lastU
        (impl.view b.input.n (logicalCount b) next.current).lastCut ∧
      (impl.view b.input.n (logicalCount b) next.current).hasCut = true ∧
      t.realReg 29 = (impl.view b.input.n (logicalCount b) next.current).lastG ∧
      t.realReg 31 = (impl.view b.input.n (logicalCount b) next.current).lastU ∧
      next.first = ctx.first ∧ next.ops = ctx.ops++[.ratio] ∧ ctx.current.work ≤ next.current.work ∧ reportVolume next.machines = reportVolume ctx.machines := by
  have hodd : ∃ r, CoreMemory.sourceRecord b B = B+2*r+1 := by
    exact ⟨5*logicalCount b+b.input.n,by dsimp [CoreMemory.sourceRecord,CoreMemory.gradientBase];omega⟩
  have hs := CoreRequest.ratio_eval (n := b.input.n) (k := logicalCount b) B (CoreMemory.sourceRecord b B) N impl.program ctx.current s ctx.image hodd
  obtain ⟨cost,t,next,he,hcost,htm,hrep,htrans,hfirst,hops,hcs,hmono⟩ := ctx.advance host hB hN hBound .ratio
    trivial hb CoreRequest.ratioCode 4 (CoreHost.preserves_ratio b B K state hB) hs
  obtain ⟨htmodel,htqual,hthas⟩ := model.ratio b (logicalIndexEquiv b) state _ _ K K0 ξ next.current htrans hn hK0 hKK
  have htn : (impl.view b.input.n (logicalCount b) next.current).physical.gamma ≠ 0 := by
    simpa only [htmodel.physical,indexedPhysical] using hn
  obtain ⟨hq,hhas,hG,hU⟩ := htrans.2.2.2.2 htn
  have hnG : t.realReg 29 = (impl.view b.input.n (logicalCount b) next.current).lastG := by
    have hh : t.realReg 29 = next.current.realReg 10 := by simpa only [shadowReg,Data.machine] using hrep.realReg 10
    exact hh.trans hG.symm
  have hnU : t.realReg 31 = (impl.view b.input.n (logicalCount b) next.current).lastU := by
    have hh : t.realReg 31 = next.current.realReg 11 := by simpa only [shadowReg,Data.machine] using hrep.realReg 11
    exact hh.trans hU.symm
  have hR : reportVolume next.machines = reportVolume ctx.machines := by
    rw [hcs,reportVolume_append ctx.machines ctx.current next.current ctx.last,htrans.2.2.1,Nat.add_zero]
  exact ⟨cost,t,next,he,by omega,htm,htmodel,htqual,hthas,hnG,hnU,hfirst,hops,hmono,hR⟩
end DecrAlmostLinearSSSP.Decremental.CoreNativeCut
end s348
section s349
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreReports
open Structured
lemma code_nat_frame (k : ℕ) (h546 : k ≠ 546) (h560 : k ≠ 560) (h580 : k ≠ 580)
    (h582 : k ≠ 582) (h584 : k ≠ 584) (hk : k < 562 ∨ 572 < k) : NatFrame code k :=
  ⟨setup_nat_frame k h580 h582,body_nat_frame k h546 h560 h580 h584 hk⟩
lemma code_nat_shadow_frame (j : ℕ) : NatFrame code (shadowReg j) := by
  simp [code,setup,setupAtoms,loop,body,fetchCode,fetchAtoms,CorePending.code,
    CorePending.prefixCode,CorePending.prefixAtoms,CorePending.insertCode,
    Structured.sequence,NatFrame,writesNat,nadd,storeN,shadowReg] <;> omega
lemma code_real_frame (j : ℕ) : RealFrame code j := by
  exact ⟨by simp [setup,setupAtoms,Structured.sequence,RealFrame,writesReal],body_real_frame j⟩
lemma frame_above {B l : ℕ} {s t : Data} (h : CorePending.MemoryFrame B l s t)
    (j : ℕ) (hj : B+10*l ≤ j) : t.natMem j = s.natMem j := by
  apply h
  intro e
  have he := e.isLt
  constructor <;> dsimp [CorePending.address] <;> omega
lemma frame_below {B l : ℕ} {s t : Data} (h : CorePending.MemoryFrame B l s t)
    (j : ℕ) (hj : j ≤ B) : t.natMem j = s.natMem j := by
  apply h
  intro e
  constructor <;> dsimp [CorePending.address] <;> omega
lemma frame_geometry {B : ℕ} (b : Core) {s t : Data}
    (h : CorePending.MemoryFrame B (logicalCount b) s t) (e : Edge b) (offset : ℕ)
    (hlo : 2 ≤ offset) (hhi : offset < 5) :
    t.natMem (CoreMemory.field b B e offset) = s.natMem (CoreMemory.field b B e offset) := by
  apply h
  intro f
  have heq : CoreMemory.field b B e offset = CorePending.address B (logicalIndexEquiv b e) offset := rfl
  rw [heq]
  constructor
  · intro hh
    have hx := CorePending.address_injective B (logicalIndexEquiv b e) f offset 0 hhi (by omega) hh
    omega
  · intro hh
    have hx := CorePending.address_injective B (logicalIndexEquiv b e) f offset 1 hhi (by omega) hh
    omega
end DecrAlmostLinearSSSP.Decremental.CoreReports
end s349
section s350
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreSource
open Structured
lemma Image.report_scan (B R N l : ℕ) (g : Machine) (s t : Data) (cost : ℕ)
    (h : Image B R N g s) (hR : B+10*l ≤ R)
    (he : Eval CoreReports.code s cost t) (hr : t.realMem = s.realMem)
    (hm : CorePending.MemoryFrame B l s t) : Image B R N g t := by
  have hn (k : ℕ) (hk : k < 500) : t.natReg k = s.natReg k := he.nat_frame
    (CoreReports.code_nat_frame k (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
  refine ⟨(hn 74 (by omega)).trans h.base,(hn 112 (by omega)).trans h.factor,
    (hn 106 (by omega)).trans h.record,(hn 50 (by omega)).trans h.savedBase,
    (hn 56 (by omega)).trans h.zero,?_,?_,?_,?_,?_⟩
  · intro a
    rw [hr]
    exact h.realMem a
  · intro a
    have haddr : B+2*(2*a+1) = B+4*a+2 := by omega
    rw [haddr,hm.guest]
    simpa only [haddr] using h.natMem a
  · rw [CoreReports.frame_above hm (R+6) (by omega)]
    exact h.work
  · constructor
    · intro j hj
      rw [hn 50 (by omega),h.savedBase,CoreReports.frame_above hm (R+8+2*j) (by omega)]
      simpa only [h.savedBase] using h.saved.nat j hj
    · intro j hj
      rw [hn 50 (by omega),hr]
      exact h.saved.real j hj
  · intro j hj
    rw [he.nat_frame (CoreReports.code_nat_shadow_frame j),he.real_frame (CoreReports.code_real_frame (shadowReg j))]
    exact h.tail j hj
end DecrAlmostLinearSSSP.Decremental.CoreSource
end s350
section s351
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreHost
open Structured
lemma reports_image (b : Core) (B : ℕ) (K : ℝ) (state : State b) (ys : List (Fin (logicalCount b)))
    (s t : Data) (cost : ℕ) (h : Image b B K state s) (hB : b.input.n ≤ B)
    (he : Eval CoreReports.code s cost t) (hv : CorePending.View B ys t)
    (hr : t.realMem = s.realMem) (hn : CorePending.MemoryFrame B (logicalCount b) s t) :
    Image b B K {state with pending := ys.map (logicalIndexEquiv b).symm} t := by
  have hnreg (k : ℕ) (h546 : k ≠ 546) (hk : k < 560 ∨ 584 < k) : t.natReg k = s.natReg k :=
    he.nat_frame (CoreReports.code_nat_frame k h546 (by omega) (by omega) (by omega) (by omega) (by omega))
  have hrreg (k : ℕ) : t.realReg k = s.realReg k := he.real_frame (CoreReports.code_real_frame k)
  have hgeom : CoreGeometry.Image b B {state with pending := ys.map (logicalIndexEquiv b).symm} t := by
    refine ⟨fun e => (congrFun hr _).trans (h.geometry.cache e),
      fun e => (congrFun hr _).trans (h.geometry.coefficient e),
      fun e => (congrFun hr _).trans (h.geometry.cost e),
      fun e => (congrFun hr _).trans (h.geometry.initial e),
      fun e => (CoreReports.frame_geometry b hn e 2 (by omega) (by omega)).trans (h.geometry.tail e),
      fun e => (CoreReports.frame_geometry b hn e 3 (by omega) (by omega)).trans (h.geometry.head e),
      fun e => (CoreReports.frame_geometry b hn e 4 (by omega) (by omega)).trans (h.geometry.returnFlag e),
      fun v => (congrFun hr _).trans (h.geometry.samples v)⟩
  have hpending : CorePending.View B (((ys.map (logicalIndexEquiv b).symm).map (logicalIndexEquiv b))) t := by
    simpa [List.map_map,Function.comp_def] using hv
  have hpublic (v : Fin b.input.n) : t.natMem v.val = s.natMem v.val := CoreReports.frame_below hn _ (by have hv := v.isLt;omega)
  refine ⟨h.captured.named_frame b.input
      (fun k hk => hnreg k (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk;omega)
        (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk;omega)) (fun k _ => hrreg k),
    h.parameters.frame b K
      (fun k hk => hnreg k (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk;omega)
        (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk;omega)) (fun k _ => hrreg k),
    h.layout.frame b B
      (fun k hk => hnreg k (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk;omega)
        (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk;omega)),
    (hnreg 74 (by omega) (by omega)).trans h.base,hgeom,
    h.gradient.frame _ _ (fun _ => congrFun hr _) (hnreg 550 (by omega) (by omega)),hpending,?_,?_⟩
  · intro v
    exact (stored_memory_congr s t v.val (hpublic v) (congrFun hr _)).trans (h.answers v)
  · intro v
    simpa only [hpublic v,hr] using h.normal v
lemma reports_environment (b : Core) (B : ℕ) (K : ℝ) (state : State b) (s : Data) (h : Image b B K state s) :
    CoreReports.Environment B (logicalCount b) s :=
  ⟨h.base,h.layout.recordBase,h.captured.two,h.captured.unit,h.layout.edgeLimit⟩
end DecrAlmostLinearSSSP.Decremental.CoreHost
end s351
section s352
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.CoreReports
lemma logical_membership (b : Core) (g : Machine) (ys : List (Fin (logicalCount b)))
    (h : ∀ d, d ∈ ys ↔ Reported g d) :
    ∀ e, e ∈ ys.map (logicalIndexEquiv b).symm ↔ Reported g (logicalIndexEquiv b e) := by
  intro e
  constructor
  · intro he
    obtain ⟨d,hd,hde⟩ := List.mem_map.mp he
    have heq : logicalIndexEquiv b e = d := by rw [← hde];simp
    rw [heq]
    exact (h d).mp hd
  · intro he
    exact List.mem_map.mpr ⟨logicalIndexEquiv b e,(h _).mpr he,(logicalIndexEquiv b).symm_apply_apply e⟩
end DecrAlmostLinearSSSP.Decremental.CoreReports
end s352
section s353
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.CoreNativeCut
open Structured
lemma Context.toggle {b : Core} {B N : ℕ} {K K0 h Γ init : ℝ}
    {impl : CutImplementation} {state : State b} {s : Data}
    (ctx : Context b B N (2*b.input.size) (4*b.weightExponent+68) impl K0 (K^(-2 : ℤ)) h Γ init s)
    (host : CoreHost.Image b B K state s) (hB : b.input.n ≤ B) (hN : 10 ≤ N)
    (hBound : registerBound impl.program.code ≤ N) (hK : 32 ≤ K) (bounds : RuntimeBounds b K state)
    (model : CutModel b (logicalIndexEquiv b) state (impl.view b.input.n (logicalCount b) ctx.current))
    (hrunning : state.stopped = false) (hdrained : state.pending = []) (hn : state.cachedGradient ≠ 0)
    (hhas : (impl.view b.input.n (logicalCount b) ctx.current).hasCut = true)
    (hq : RatioGuarantee (cachedPhysical b state) K
      (impl.view b.input.n (logicalCount b) ctx.current).lastG
      (impl.view b.input.n (logicalCount b) ctx.current).lastU
      (impl.view b.input.n (logicalCount b) ctx.current).lastCut)
    (hfailed : (impl.view b.input.n (logicalCount b) ctx.current).lastG/
      (impl.view b.input.n (logicalCount b) ctx.current).lastU < -1/(4*K))
    (hNativeU : s.realReg 31 = (impl.view b.input.n (logicalCount b) ctx.current).lastU) :
    ∃ cost t, ∃ next : Context b B N (2*b.input.size) (4*b.weightExponent+68) impl K0 (K^(-2 : ℤ)) h Γ init t,
    ∃ reports : List (Edge b),
      Eval (toggleCode N impl.program) s cost t ∧
      cost ≤ (dispatchCharge impl.program.code+2)*(next.current.work-ctx.current.work)+8*N+27+18*reportCount next.current ∧
      CoreHost.Image b B K (reportedToggle b K state
        (modelReply b (impl.view b.input.n (logicalCount b) ctx.current)) reports) t ∧
      RuntimeBounds b K (reportedToggle b K state (modelReply b (impl.view b.input.n (logicalCount b) ctx.current)) reports) ∧
      CutModel b (logicalIndexEquiv b)
        (reportedToggle b K state (modelReply b (impl.view b.input.n (logicalCount b) ctx.current)) reports)
        (impl.view b.input.n (logicalCount b) next.current) ∧
      RuntimeRepairStep b K state
        (reportedToggle b K state (modelReply b (impl.view b.input.n (logicalCount b) ctx.current)) reports) ∧
      next.first = ctx.first ∧ next.ops.length = ctx.ops.length+1 ∧
      toggleVolume next.ops = toggleVolume ctx.ops+1 ∧ ctx.current.work ≤ next.current.work ∧
      reportVolume next.machines = reportVolume ctx.machines+reportCount next.current ∧
      reports.length ≤ reportCount next.current := by
  have hodd : ∃ r, CoreMemory.sourceRecord b B = B+2*r+1 := by
    exact ⟨5*logicalCount b+b.input.n,by dsimp [CoreMemory.sourceRecord,CoreMemory.gradientBase];omega⟩
  let c := impl.view b.input.n (logicalCount b) ctx.current
  let tau := 1/(K^2*c.lastU)
  have htau : s.realReg 510/s.realReg 31 = tau := by
    rw [host.parameters.threshold,hNativeU]
    dsimp only [tau,c]
    simp only [zpow_neg,zpow_ofNat,div_eq_mul_inv,one_div,mul_inv_rev]
    ring
  have hv := model.toggle_valid b (logicalIndexEquiv b) state _ K hhas hn hq.2.1 (by linarith)
  have hb : (applyPhysical c.physical (.toggle tau)).Valid (2*b.input.size) (4*b.weightExponent+68) := by
    change c.physical.Valid _ _
    rw [model.physical]
    exact runtime_indexed_physical_valid b K state bounds (logicalIndexEquiv b) (logicalCount_le b)
  have hs := CoreRequest.toggle_eval (n := b.input.n) (k := logicalCount b) B (CoreMemory.sourceRecord b B) N
    impl.program ctx.current s tau ctx.image hodd htau
  obtain ⟨cu,u,uctx,hu,hcu,hum,hrep,htrans,hfirst,hops,hcs,hmono⟩ :=
    ctx.advance host hB hN hBound (.toggle tau) hv hb CoreRequest.toggleCode 8
      (CoreHost.preserves_toggle b B K state hB) hs
  have hupending : CorePending.View B ([] : List (Fin (logicalCount b))) u := by
    simpa only [hdrained,List.map_nil] using hum.pending
  obtain ⟨cr,t,ht,hcr,htview,htenv,htr,htguest,htmembership,htmemory⟩ :=
    CoreReports.eval_code B (logicalCount b) uctx.current [] u
      (CoreHost.reports_environment b B K state u hum) hupending hum.captured.zeroN hrep
  let ys := CoreReports.consume (logicalCount b) [] (CoreReports.reportList uctx.current)
  let reports := ys.map (logicalIndexEquiv b).symm
  have hMember : ∀ e, e ∈ reports ↔ Reported uctx.current (logicalIndexEquiv b e) := by
    apply CoreReports.logical_membership b uctx.current ys
    intro d
    simpa only [List.not_mem_nil,false_or] using htmembership d
  have hComplete := model.toggle_complete b (logicalIndexEquiv b) state _ _ K K0 uctx.current reports hdrained htrans hMember
  have htmodel := model.toggle b (logicalIndexEquiv b) state _ _ K K0 uctx.current reports hdrained htrans hMember
  have htm0 := CoreHost.reports_image b B K state ys u t cr hum hB ht htview htr htmemory
  have htm : CoreHost.Image b B K (reportedToggle b K state (modelReply b c) reports) t :=
    htm0.state_congr b B K rfl rfl rfl rfl rfl rfl
  have hts := uctx.image.report_scan B (CoreMemory.sourceRecord b B) N (logicalCount b) uctx.current u t cr
    (by dsimp [CoreMemory.sourceRecord,CoreMemory.gradientBase];omega) ht htr htmemory
  let next := uctx.of_image hts
  have hBounds := bounds.toggle b K hK state hdrained (modelReply b c) hq hfailed reports hComplete
  have hStep := RuntimeRepairStep.toggle state (modelReply b c) reports hrunning hdrained hq hfailed hComplete
  have hlength : next.ops.length = ctx.ops.length+1 := by change uctx.ops.length = _;rw [hops];simp
  have hvol : toggleVolume next.ops = toggleVolume ctx.ops+1 := by
    change toggleVolume uctx.ops = _
    rw [hops]
    simp [toggleVolume,List.filter_append]
  have hR : reportVolume next.machines = reportVolume ctx.machines+reportCount next.current := by
    change reportVolume uctx.machines = reportVolume ctx.machines+reportCount uctx.current
    rw [hcs,reportVolume_append ctx.machines ctx.current uctx.current ctx.last]
  have hlen : reports.length ≤ reportCount next.current := by
    change (ys.map (logicalIndexEquiv b).symm).length ≤ reportCount uctx.current
    rw [List.length_map]
    exact CoreReports.initial_reports_length (logicalCount b) uctx.current
  exact ⟨cu+cr,t,next,reports,Eval.seq hu ht,by change cu+cr ≤ (dispatchCharge impl.program.code+2)*(uctx.current.work-ctx.current.work)+8*N+27+18*reportCount uctx.current;omega,
    htm,hBounds,htmodel,hStep,hfirst,hlength,hvol,hmono,hR,hlen⟩
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
theorem solution : (((((((DecrAlmostLinearSSSP.Decremental.Structured.NoMemory DecrAlmostLinearSSSP.Decremental.CoreRefreshRead.code) ∧ (@Eq.{1} Bool
  (DecrAlmostLinearSSSP.Decremental.Structured.evenRegisters DecrAlmostLinearSSSP.Decremental.CoreRefreshRead.code)
  Bool.true)) ∧ ((∀ (k : Nat),
  Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 562) (instOfNatNat (nat_lit 562))))
      (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 648) (instOfNatNat (nat_lit 648))) k) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreRefreshRead.code k) ∧ (∀ (k : Nat),
  Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 600) (instOfNatNat (nat_lit 600))))
      (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 606) (instOfNatNat (nat_lit 606))) k) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreRefreshRead.code k))) ∧ (((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
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
                    (@Fin.val b.input.n (DecrAlmostLinearSSSP.Decremental.head b e)))))))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B N : Nat) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreSource.Image B (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N g
      s →
    DecrAlmostLinearSSSP.Decremental.CoreSource.Image B (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N
      g (DecrAlmostLinearSSSP.Decremental.CoreRefreshRead.result s))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B N : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (e : DecrAlmostLinearSSSP.Decremental.Edge b) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    DecrAlmostLinearSSSP.Decremental.CoreSource.Image B (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N
        g s →
      @LE.le.{0} Nat instLENat b.input.n B →
        DecrAlmostLinearSSSP.Decremental.CoreGeometry.Loaded b state e s →
          @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 608) (instOfNatNat (nat_lit 608))))
              (@DecrAlmostLinearSSSP.Decremental.State.y b state (DecrAlmostLinearSSSP.Decremental.tail b e)) →
            @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 610) (instOfNatNat (nat_lit 610))))
                (@DecrAlmostLinearSSSP.Decremental.State.y b state (DecrAlmostLinearSSSP.Decremental.head b e)) →
              And
                (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state
                  (DecrAlmostLinearSSSP.Decremental.CoreRefresh.result s))
                (And
                  (DecrAlmostLinearSSSP.Decremental.CoreSource.Image B
                    (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N g
                    (DecrAlmostLinearSSSP.Decremental.CoreRefresh.result s))
                  (And
                    (@Eq.{1} Real
                      ((DecrAlmostLinearSSSP.Decremental.CoreRefresh.result s).realReg
                        (@OfNat.ofNat.{0} Nat (nat_lit 612) (instOfNatNat (nat_lit 612))))
                      (DecrAlmostLinearSSSP.Decremental.capacity b
                        (@DecrAlmostLinearSSSP.Decremental.State.active b state)
                        (DecrAlmostLinearSSSP.Decremental.labels b state) e))
                    (And
                      (@Eq.{1} Real
                        ((DecrAlmostLinearSSSP.Decremental.CoreRefresh.result s).realReg
                          (@OfNat.ofNat.{0} Nat (nat_lit 614) (instOfNatNat (nat_lit 614))))
                        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                          (DecrAlmostLinearSSSP.Decremental.capacity b
                            (@DecrAlmostLinearSSSP.Decremental.State.active b state)
                            (DecrAlmostLinearSSSP.Decremental.labels b state) e)
                          (@DecrAlmostLinearSSSP.Decremental.State.cache b state e)))
                      (∀ (v : DecrAlmostLinearSSSP.Decremental.ReturnVertex b),
                        @Eq.{1} (DecrAlmostLinearSSSP.Decremental.Edge b) e
                            (@Sum.inr.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) v) →
                          @Eq.{1} Real
                            ((DecrAlmostLinearSSSP.Decremental.CoreRefresh.result s).realReg
                              (@OfNat.ofNat.{0} Nat (nat_lit 616) (instOfNatNat (nat_lit 616))))
                            (DecrAlmostLinearSSSP.Decremental.labels b state
                              (@Subtype.val.{1} (Fin b.input.n) (fun v => @Ne.{1} (Fin b.input.n) v b.input.source)
                                v))))))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (e : DecrAlmostLinearSSSP.Decremental.Edge b) (f : Real) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreGeometry.Image b B state s →
    DecrAlmostLinearSSSP.Decremental.CoreGeometry.Image b B
      (@DecrAlmostLinearSSSP.Decremental.State.mk b (@DecrAlmostLinearSSSP.Decremental.State.active b state)
        (@DecrAlmostLinearSSSP.Decremental.State.y b state)
        (@Function.update.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (fun a => Real)
          (fun a b_1 =>
            @instDecidableEqSum.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b)
              (instDecidableEqFin b.input.k) (DecrAlmostLinearSSSP.Decremental.instDecidableEqReturnVertex b) a b_1)
          (@DecrAlmostLinearSSSP.Decremental.State.cache b state) e f)
        (@DecrAlmostLinearSSSP.Decremental.State.baseline b state)
        (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b state)
        (@DecrAlmostLinearSSSP.Decremental.State.nonzeroEntries b state)
        (@DecrAlmostLinearSSSP.Decremental.State.sample b state)
        (@DecrAlmostLinearSSSP.Decremental.State.output b state)
        (@DecrAlmostLinearSSSP.Decremental.State.pending b state)
        (@DecrAlmostLinearSSSP.Decremental.State.stopped b state)
        (@DecrAlmostLinearSSSP.Decremental.State.toggles b state)
        (@DecrAlmostLinearSSSP.Decremental.State.history b state))
      { realReg := s.realReg, natReg := s.natReg,
        realMem :=
          @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realMem
            (DecrAlmostLinearSSSP.Decremental.CoreMemory.field b B e
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
            f,
        natMem := s.natMem }) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (e : DecrAlmostLinearSSSP.Decremental.Edge b) (f : Real) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    @LE.le.{0} Nat instLENat b.input.n B →
      DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K
        (@DecrAlmostLinearSSSP.Decremental.State.mk b (@DecrAlmostLinearSSSP.Decremental.State.active b state)
          (@DecrAlmostLinearSSSP.Decremental.State.y b state)
          (@Function.update.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (fun a => Real)
            (fun a b_1 =>
              @instDecidableEqSum.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b)
                (instDecidableEqFin b.input.k) (DecrAlmostLinearSSSP.Decremental.instDecidableEqReturnVertex b) a b_1)
            (@DecrAlmostLinearSSSP.Decremental.State.cache b state) e f)
          (@DecrAlmostLinearSSSP.Decremental.State.baseline b state)
          (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b state)
          (@DecrAlmostLinearSSSP.Decremental.State.nonzeroEntries b state)
          (@DecrAlmostLinearSSSP.Decremental.State.sample b state)
          (@DecrAlmostLinearSSSP.Decremental.State.output b state)
          (@DecrAlmostLinearSSSP.Decremental.State.pending b state)
          (@DecrAlmostLinearSSSP.Decremental.State.stopped b state)
          (@DecrAlmostLinearSSSP.Decremental.State.toggles b state)
          (@DecrAlmostLinearSSSP.Decremental.State.history b state))
        { realReg := s.realReg, natReg := s.natReg,
          realMem :=
            @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realMem
              (DecrAlmostLinearSSSP.Decremental.CoreMemory.field b B e
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              f,
          natMem := s.natMem }))))) ∧ ((((@Eq.{1} Bool
  (DecrAlmostLinearSSSP.Decremental.Structured.evenRegisters DecrAlmostLinearSSSP.Decremental.CoreGradientDelta.code)
  Bool.true) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 550) (instOfNatNat (nat_lit 550))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 620) (instOfNatNat (nat_lit 620))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 632) (instOfNatNat (nat_lit 632))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 634) (instOfNatNat (nat_lit 634))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreGradientDelta.code k)) ∧ ((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 612) (instOfNatNat (nat_lit 612))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 698) (instOfNatNat (nat_lit 698))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 628) (instOfNatNat (nat_lit 628))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
            DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
              DecrAlmostLinearSSSP.Decremental.CoreGradientDelta.code k) ∧ (∀ {n : Nat} (base : Nat) (g : Fin n → Real) (a z : Fin n) (delta f : Real)
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
                                  @Eq.{1} Real (t.realMem j) (s.realMem j))))))))) ∧ (((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) {before after : DecrAlmostLinearSSSP.Decremental.State b}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.CoreGeometry.Image b B before s →
    @Eq.{1} (Finset.{0} (Fin b.input.k)) (@DecrAlmostLinearSSSP.Decremental.State.active b after)
        (@DecrAlmostLinearSSSP.Decremental.State.active b before) →
      @Eq.{1} (DecrAlmostLinearSSSP.Decremental.Edge b → Real) (@DecrAlmostLinearSSSP.Decremental.State.cache b after)
          (@DecrAlmostLinearSSSP.Decremental.State.cache b before) →
        @Eq.{1} (Fin b.input.n → Real) (@DecrAlmostLinearSSSP.Decremental.State.sample b after)
            (@DecrAlmostLinearSSSP.Decremental.State.sample b before) →
          DecrAlmostLinearSSSP.Decremental.CoreGeometry.Image b B after s) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real)
  {before after : DecrAlmostLinearSSSP.Decremental.State b} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K before s →
    @Eq.{1} (Finset.{0} (Fin b.input.k)) (@DecrAlmostLinearSSSP.Decremental.State.active b after)
        (@DecrAlmostLinearSSSP.Decremental.State.active b before) →
      @Eq.{1} (DecrAlmostLinearSSSP.Decremental.Edge b → Real) (@DecrAlmostLinearSSSP.Decremental.State.cache b after)
          (@DecrAlmostLinearSSSP.Decremental.State.cache b before) →
        @Eq.{1} (Fin b.input.n → Real) (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b after)
            (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b before) →
          @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
              (@DecrAlmostLinearSSSP.Decremental.State.pending b after)
              (@DecrAlmostLinearSSSP.Decremental.State.pending b before) →
            @Eq.{1} (Fin b.input.n → Real) (@DecrAlmostLinearSSSP.Decremental.State.sample b after)
                (@DecrAlmostLinearSSSP.Decremental.State.sample b before) →
              @Eq.{1} (Fin b.input.n → ENNReal) (@DecrAlmostLinearSSSP.Decremental.State.output b after)
                  (@DecrAlmostLinearSSSP.Decremental.State.output b before) →
                DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K after s)) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B N : Nat) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.CoreSource.Image B (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N g
      s →
    (∀ (k : Nat),
        @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat)
            (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))
              (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112)))
                (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106)))
                  (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50)))
                    (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56)))
                      (@List.nil.{0} Nat))))))
            k →
          @Eq.{1} Nat (t.natReg k) (s.natReg k)) →
      (∀ (j : Nat),
          @LE.le.{0} Nat instLENat N j →
            And
              (@Eq.{1} Nat (t.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg j))
                (s.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg j)))
              (@Eq.{1} Real (t.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg j))
                (s.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg j)))) →
        (∀ (address : Nat),
            Not (DecrAlmostLinearSSSP.Decremental.CoreHost.Address b B address) →
              And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                (@Eq.{1} Real (t.realMem address) (s.realMem address))) →
          DecrAlmostLinearSSSP.Decremental.CoreSource.Image B
            (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N g t) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (a z : Fin b.input.n) (delta : Real) (s t : DecrAlmostLinearSSSP.Decremental.Structured.Data) (cost : Nat),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    @LE.le.{0} Nat instLENat b.input.n B →
      DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreGradientDelta.code s cost
          t →
        @DecrAlmostLinearSSSP.Decremental.CoreGradient.Image b.input.n
            (DecrAlmostLinearSSSP.Decremental.CoreMemory.gradientBase b B)
            (fun v =>
              @HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                  (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b state v)
                  (@ite.{1} Real (@Eq.{1} (Fin b.input.n) v a) (instDecidableEqFin b.input.n v a) delta
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
                (@ite.{1} Real (@Eq.{1} (Fin b.input.n) v z) (instDecidableEqFin b.input.n v z) delta
                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
            t →
          @Eq.{1} (Nat → Nat) t.natMem s.natMem →
            (∀ (j : Nat),
                @Ne.{1} Nat j (DecrAlmostLinearSSSP.Decremental.CoreMemory.gradientCell b B a) →
                  @Ne.{1} Nat j (DecrAlmostLinearSSSP.Decremental.CoreMemory.gradientCell b B z) →
                    @Eq.{1} Real (t.realMem j) (s.realMem j)) →
              DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K
                (@DecrAlmostLinearSSSP.Decremental.State.mk b (@DecrAlmostLinearSSSP.Decremental.State.active b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.y b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.cache b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.baseline b state)
                  (fun v =>
                    @HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                        (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b state v)
                        (@ite.{1} Real (@Eq.{1} (Fin b.input.n) v a) (instDecidableEqFin b.input.n v a) delta
                          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
                      (@ite.{1} Real (@Eq.{1} (Fin b.input.n) v z) (instDecidableEqFin b.input.n v z) delta
                        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
                  (@DecrAlmostLinearSSSP.Decremental.State.nonzeroEntries b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.sample b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.output b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.pending b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.stopped b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.toggles b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.history b state))
                t) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B N : Nat) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  (a z : Fin b.input.n) (s t : DecrAlmostLinearSSSP.Decremental.Structured.Data) (cost : Nat),
  DecrAlmostLinearSSSP.Decremental.CoreSource.Image B (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N g
      s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreGradientDelta.code s cost t →
      @Eq.{1} (Nat → Nat) t.natMem s.natMem →
        (∀ (j : Nat),
            @Ne.{1} Nat j (DecrAlmostLinearSSSP.Decremental.CoreMemory.gradientCell b B a) →
              @Ne.{1} Nat j (DecrAlmostLinearSSSP.Decremental.CoreMemory.gradientCell b B z) →
                @Eq.{1} Real (t.realMem j) (s.realMem j)) →
          DecrAlmostLinearSSSP.Decremental.CoreSource.Image B
            (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N g t)))))) ∧ (((((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (e : DecrAlmostLinearSSSP.Decremental.Edge b) (xs : List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    @LE.le.{0} Nat instLENat b.input.n B →
      @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
          (@DecrAlmostLinearSSSP.Decremental.State.pending b state)
          (@List.cons.{0} (DecrAlmostLinearSSSP.Decremental.Edge b) e xs) →
        ∃ t,
          And
            (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CorePending.popCode s
              (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) t)
            (And
              (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K
                (@DecrAlmostLinearSSSP.Decremental.State.mk b (@DecrAlmostLinearSSSP.Decremental.State.active b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.y b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.cache b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.baseline b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.nonzeroEntries b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.sample b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.output b state) xs
                  (@DecrAlmostLinearSSSP.Decremental.State.stopped b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.toggles b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.history b state))
                t)
              (And
                (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
                  (DecrAlmostLinearSSSP.Decremental.CoreMemory.encodedEdge b e))
                (And (@Eq.{1} (Nat → Real) t.realMem s.realMem)
                  (∀ (j : Nat),
                    @Ne.{1} Nat j
                        (DecrAlmostLinearSSSP.Decremental.CoreMemory.field b B e
                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
                      @Eq.{1} Nat (t.natMem j) (s.natMem j)))))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B N : Nat) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreSource.Image B (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N g
      s →
    ∀ (address : Nat) (value : Real),
      DecrAlmostLinearSSSP.Decremental.CoreHost.Address b B address →
        DecrAlmostLinearSSSP.Decremental.CoreSource.Image B
          (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N g
          { realReg := s.realReg, natReg := s.natReg,
            realMem := @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realMem address value,
            natMem := s.natMem })) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B N : Nat) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreSource.Image B (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N g
      s →
    ∀ (address value : Nat),
      DecrAlmostLinearSSSP.Decremental.CoreHost.Address b B address →
        DecrAlmostLinearSSSP.Decremental.CoreSource.Image B
          (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N g
          { realReg := s.realReg, natReg := s.natReg, realMem := s.realMem,
            natMem := @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natMem address value }) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B N : Nat) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  (s t : DecrAlmostLinearSSSP.Decremental.Structured.Data) (cost : Nat) (e : DecrAlmostLinearSSSP.Decremental.Edge b),
  DecrAlmostLinearSSSP.Decremental.CoreSource.Image B (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N g
      s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CorePending.popCode s cost t →
      @Eq.{1} (Nat → Real) t.realMem s.realMem →
        (∀ (j : Nat),
            @Ne.{1} Nat j
                (DecrAlmostLinearSSSP.Decremental.CoreMemory.field b B e
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
              @Eq.{1} Nat (t.natMem j) (s.natMem j)) →
          DecrAlmostLinearSSSP.Decremental.CoreSource.Image B
            (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N g t))) ∧ (((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 550) (instOfNatNat (nat_lit 550))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 620) (instOfNatNat (nat_lit 620))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 632) (instOfNatNat (nat_lit 632))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 634) (instOfNatNat (nat_lit 634))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreCommit.prefixCode k) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 612) (instOfNatNat (nat_lit 612))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 698) (instOfNatNat (nat_lit 698))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 628) (instOfNatNat (nat_lit 628))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
            DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreCommit.prefixCode
              k)) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B N : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
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
                              f))))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (v : DecrAlmostLinearSSSP.Decremental.ReturnVertex b) (r : Real)
  (s t : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreGeometry.Image b B state s →
    @LE.le.{0} Nat instLENat b.input.n B →
      @Eq.{1} Real
          (t.realMem
            (DecrAlmostLinearSSSP.Decremental.CoreMemory.field b B
              (@Sum.inr.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) v)
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
          r →
        (∀ (j : Nat),
            @Ne.{1} Nat j
                (@Fin.val b.input.n
                  (@Subtype.val.{1} (Fin b.input.n) (fun v => @Ne.{1} (Fin b.input.n) v b.input.source) v)) →
              @Eq.{1} Nat (t.natMem j) (s.natMem j)) →
          (∀ (j : Nat),
              @Ne.{1} Nat j
                  (@Fin.val b.input.n
                    (@Subtype.val.{1} (Fin b.input.n) (fun v => @Ne.{1} (Fin b.input.n) v b.input.source) v)) →
                @Ne.{1} Nat j
                    (DecrAlmostLinearSSSP.Decremental.CoreMemory.field b B
                      (@Sum.inr.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) v)
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) →
                  @Eq.{1} Real (t.realMem j) (s.realMem j)) →
            DecrAlmostLinearSSSP.Decremental.CoreGeometry.Image b B
              (@DecrAlmostLinearSSSP.Decremental.State.mk b (@DecrAlmostLinearSSSP.Decremental.State.active b state)
                (@DecrAlmostLinearSSSP.Decremental.State.y b state)
                (@DecrAlmostLinearSSSP.Decremental.State.cache b state)
                (@DecrAlmostLinearSSSP.Decremental.State.baseline b state)
                (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b state)
                (@DecrAlmostLinearSSSP.Decremental.State.nonzeroEntries b state)
                (@Function.update.{1, 1} (Fin b.input.n) (fun a => Real) (instDecidableEqFin b.input.n)
                  (@DecrAlmostLinearSSSP.Decremental.State.sample b state)
                  (@Subtype.val.{1} (Fin b.input.n) (fun v => @Ne.{1} (Fin b.input.n) v b.input.source) v) r)
                (@DecrAlmostLinearSSSP.Decremental.State.output b state)
                (@DecrAlmostLinearSSSP.Decremental.State.pending b state)
                (@DecrAlmostLinearSSSP.Decremental.State.stopped b state)
                (@DecrAlmostLinearSSSP.Decremental.State.toggles b state)
                (@DecrAlmostLinearSSSP.Decremental.State.history b state))
              t) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (v : DecrAlmostLinearSSSP.Decremental.ReturnVertex b) (r : Real)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    @LE.le.{0} Nat instLENat b.input.n B →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626))))
          (@Fin.val b.input.n
            (@Subtype.val.{1} (Fin b.input.n) (fun v => @Ne.{1} (Fin b.input.n) v b.input.source) v)) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 578) (instOfNatNat (nat_lit 578))))
            (DecrAlmostLinearSSSP.Decremental.CoreMemory.field b B
              (@Sum.inr.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) v)
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) →
          @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 616) (instOfNatNat (nat_lit 616)))) r →
            ∃ cost t,
              And
                (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreReturn.code s
                  cost t)
                (And (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11))))
                  (And
                    (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K
                      (@DecrAlmostLinearSSSP.Decremental.State.mk b
                        (@DecrAlmostLinearSSSP.Decremental.State.active b state)
                        (@DecrAlmostLinearSSSP.Decremental.State.y b state)
                        (@DecrAlmostLinearSSSP.Decremental.State.cache b state)
                        (@DecrAlmostLinearSSSP.Decremental.State.baseline b state)
                        (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b state)
                        (@DecrAlmostLinearSSSP.Decremental.State.nonzeroEntries b state)
                        (@Function.update.{1, 1} (Fin b.input.n) (fun a => Real) (instDecidableEqFin b.input.n)
                          (@DecrAlmostLinearSSSP.Decremental.State.sample b state)
                          (@Subtype.val.{1} (Fin b.input.n) (fun v => @Ne.{1} (Fin b.input.n) v b.input.source) v) r)
                        (@Function.update.{1, 1} (Fin b.input.n) (fun a => ENNReal) (instDecidableEqFin b.input.n)
                          (@DecrAlmostLinearSSSP.Decremental.State.output b state)
                          (@Subtype.val.{1} (Fin b.input.n) (fun v => @Ne.{1} (Fin b.input.n) v b.input.source) v)
                          (DecrAlmostLinearSSSP.Decremental.readout b r))
                        (@DecrAlmostLinearSSSP.Decremental.State.pending b state)
                        (@DecrAlmostLinearSSSP.Decremental.State.stopped b state)
                        (@DecrAlmostLinearSSSP.Decremental.State.toggles b state)
                        (@DecrAlmostLinearSSSP.Decremental.State.history b state))
                      t)
                    (And
                      (∀ (j : Nat),
                        @Ne.{1} Nat j
                            (@Fin.val b.input.n
                              (@Subtype.val.{1} (Fin b.input.n) (fun v => @Ne.{1} (Fin b.input.n) v b.input.source)
                                v)) →
                          @Eq.{1} Nat (t.natMem j) (s.natMem j))
                      (∀ (j : Nat),
                        @Ne.{1} Nat j
                            (@Fin.val b.input.n
                              (@Subtype.val.{1} (Fin b.input.n) (fun v => @Ne.{1} (Fin b.input.n) v b.input.source)
                                v)) →
                          @Ne.{1} Nat j
                              (DecrAlmostLinearSSSP.Decremental.CoreMemory.field b B
                                (@Sum.inr.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) v)
                                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) →
                            @Eq.{1} Real (t.realMem j) (s.realMem j)))))))))) ∧ ((((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B N : Nat) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  (v : DecrAlmostLinearSSSP.Decremental.ReturnVertex b) (s t : DecrAlmostLinearSSSP.Decremental.Structured.Data)
  (cost : Nat),
  DecrAlmostLinearSSSP.Decremental.CoreSource.Image B (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N g
      s →
    @LE.le.{0} Nat instLENat b.input.n B →
      DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreReturn.code s cost t →
        (∀ (j : Nat),
            @Ne.{1} Nat j
                (@Fin.val b.input.n
                  (@Subtype.val.{1} (Fin b.input.n) (fun v => @Ne.{1} (Fin b.input.n) v b.input.source) v)) →
              @Eq.{1} Nat (t.natMem j) (s.natMem j)) →
          (∀ (j : Nat),
              @Ne.{1} Nat j
                  (@Fin.val b.input.n
                    (@Subtype.val.{1} (Fin b.input.n) (fun v => @Ne.{1} (Fin b.input.n) v b.input.source) v)) →
                @Ne.{1} Nat j
                    (DecrAlmostLinearSSSP.Decremental.CoreMemory.field b B
                      (@Sum.inr.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) v)
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) →
                  @Eq.{1} Real (t.realMem j) (s.realMem j)) →
            DecrAlmostLinearSSSP.Decremental.CoreSource.Image B
              (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N g t) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B N : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (e : DecrAlmostLinearSSSP.Decremental.Edge b) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    DecrAlmostLinearSSSP.Decremental.CoreSource.Image B (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N
        g s →
      @LE.le.{0} Nat instLENat b.input.n B →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 648) (instOfNatNat (nat_lit 648))))
            (DecrAlmostLinearSSSP.Decremental.CoreGeometry.returnBit b e) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626))))
              (@Fin.val b.input.n (DecrAlmostLinearSSSP.Decremental.tail b e)) →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 578) (instOfNatNat (nat_lit 578))))
                (DecrAlmostLinearSSSP.Decremental.CoreMemory.field b B e
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) →
              (∀ (v : DecrAlmostLinearSSSP.Decremental.ReturnVertex b),
                  @Eq.{1} (DecrAlmostLinearSSSP.Decremental.Edge b) e
                      (@Sum.inr.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) v) →
                    @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 616) (instOfNatNat (nat_lit 616))))
                      (DecrAlmostLinearSSSP.Decremental.labels b state
                        (@Subtype.val.{1} (Fin b.input.n) (fun v => @Ne.{1} (Fin b.input.n) v b.input.source) v))) →
                ∃ cost t,
                  And
                    (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                      DecrAlmostLinearSSSP.Decremental.CoreCommit.returnCode s cost t)
                    (And (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))
                      (And
                        (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K
                          (DecrAlmostLinearSSSP.Decremental.CoreCommit.returnState b state e) t)
                        (DecrAlmostLinearSSSP.Decremental.CoreSource.Image B
                          (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N g t))))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B N : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (e : DecrAlmostLinearSSSP.Decremental.Edge b) (xs : List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
  (g : DecrAlmostLinearSSSP.Decremental.Machine) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    DecrAlmostLinearSSSP.Decremental.CoreSource.Image B (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N
        g s →
      @LE.le.{0} Nat instLENat b.input.n B →
        @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
            (@DecrAlmostLinearSSSP.Decremental.State.pending b state)
            (@List.cons.{0} (DecrAlmostLinearSSSP.Decremental.Edge b) e xs) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 568) (instOfNatNat (nat_lit 568))))
              (DecrAlmostLinearSSSP.Decremental.CoreMemory.field b B e
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626))))
                (@Fin.val b.input.n (DecrAlmostLinearSSSP.Decremental.tail b e)) →
              @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 628) (instOfNatNat (nat_lit 628))))
                  (@Fin.val b.input.n (DecrAlmostLinearSSSP.Decremental.head b e)) →
                @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 648) (instOfNatNat (nat_lit 648))))
                    (DecrAlmostLinearSSSP.Decremental.CoreGeometry.returnBit b e) →
                  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 578) (instOfNatNat (nat_lit 578))))
                      (DecrAlmostLinearSSSP.Decremental.CoreMemory.field b B e
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) →
                    @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 612) (instOfNatNat (nat_lit 612))))
                        (DecrAlmostLinearSSSP.Decremental.capacity b
                          (@DecrAlmostLinearSSSP.Decremental.State.active b state)
                          (DecrAlmostLinearSSSP.Decremental.labels b state) e) →
                      @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 614) (instOfNatNat (nat_lit 614))))
                          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                            (DecrAlmostLinearSSSP.Decremental.capacity b
                              (@DecrAlmostLinearSSSP.Decremental.State.active b state)
                              (DecrAlmostLinearSSSP.Decremental.labels b state) e)
                            (@DecrAlmostLinearSSSP.Decremental.State.cache b state e)) →
                        (∀ (v : DecrAlmostLinearSSSP.Decremental.ReturnVertex b),
                            @Eq.{1} (DecrAlmostLinearSSSP.Decremental.Edge b) e
                                (@Sum.inr.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) v) →
                              @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 616) (instOfNatNat (nat_lit 616))))
                                (DecrAlmostLinearSSSP.Decremental.labels b state
                                  (@Subtype.val.{1} (Fin b.input.n) (fun v => @Ne.{1} (Fin b.input.n) v b.input.source)
                                    v))) →
                          ∃ cost t,
                            And
                              (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                DecrAlmostLinearSSSP.Decremental.CoreCommit.headCode s cost t)
                              (And
                                (@LE.le.{0} Nat instLENat cost
                                  (@OfNat.ofNat.{0} Nat (nat_lit 61) (instOfNatNat (nat_lit 61))))
                                (And
                                  (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K
                                    (DecrAlmostLinearSSSP.Decremental.refresh b state e) t)
                                  (DecrAlmostLinearSSSP.Decremental.CoreSource.Image B
                                    (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N g t)))) ∧ ((∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {B N : Nat} {K K0 ξ h Γ init : Real}
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
      impl K0 ξ h Γ init s),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    @LE.le.{0} Nat instLENat b.input.n B →
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) N →
        @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.registerBound impl.program.code) N →
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
                  impl K0 ξ h Γ init s ctx)) →
            ∀ (e : DecrAlmostLinearSSSP.Decremental.Edge b) (xs : List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)),
              @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
                  (@DecrAlmostLinearSSSP.Decremental.State.pending b state)
                  (@List.cons.{0} (DecrAlmostLinearSSSP.Decremental.Edge b) e xs) →
                @DecrAlmostLinearSSSP.Decremental.Physical.Valid b.input.n
                    (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                    (@DecrAlmostLinearSSSP.Decremental.indexedPhysical b state
                      (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                      (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b))
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                      (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68)))) →
                  DecrAlmostLinearSSSP.Decremental.RefreshValidity b state e →
                    DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K
                        (DecrAlmostLinearSSSP.Decremental.refresh b state e) →
                      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
                          (DecrAlmostLinearSSSP.Decremental.CoreMemory.encodedEdge b e) →
                        ∃ cost t next,
                          And
                            (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                              (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.refreshCode N impl.program) s cost t)
                            (And
                              (@LE.le.{0} Nat instLENat cost
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (DecrAlmostLinearSSSP.Decremental.dispatchCharge impl.program.code)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                                        (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                              b.input.size)
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                b.weightExponent)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                            impl K0 ξ h Γ init t next).work
                                        (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                              b.input.size)
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                b.weightExponent)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                            impl K0 ξ h Γ init s ctx).work))
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40))) N))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 218) (instOfNatNat (nat_lit 218)))))
                              (And
                                (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K
                                  (DecrAlmostLinearSSSP.Decremental.refresh b state e) t)
                                (And
                                  (DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K
                                    (DecrAlmostLinearSSSP.Decremental.refresh b state e))
                                  (And
                                    (@DecrAlmostLinearSSSP.Decremental.CutModel b
                                      (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                      (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b)
                                      (DecrAlmostLinearSSSP.Decremental.refresh b state e)
                                      (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                        (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                              b.weightExponent)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                          impl K0 ξ h Γ init t next)))
                                    (And
                                      (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                                        (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.first b B N
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                              b.weightExponent)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                          impl K0 ξ h Γ init t next)
                                        (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.first b B N
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                              b.weightExponent)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                          impl K0 ξ h Γ init s ctx))
                                      (And
                                        (@Eq.{1}
                                          (List.{0}
                                            (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                              (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                          (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                              b.input.size)
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                b.weightExponent)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
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
                                            (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                b.input.size)
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                  b.weightExponent)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                              impl K0 ξ h Γ init s ctx)
                                            (@List.cons.{0}
                                              (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                              (@DecrAlmostLinearSSSP.Decremental.CutOp.queryY b.input.n
                                                (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                                (DecrAlmostLinearSSSP.Decremental.tail b e))
                                              (@List.cons.{0}
                                                (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                  (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                                (@DecrAlmostLinearSSSP.Decremental.CutOp.queryY b.input.n
                                                  (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                                  (DecrAlmostLinearSSSP.Decremental.head b e))
                                                (@List.cons.{0}
                                                  (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                    (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                                  (@DecrAlmostLinearSSSP.Decremental.CutOp.erase b.input.n
                                                    (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                                    (@DFunLike.coe.{1, 1, 1}
                                                      (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                        (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                                      (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                      (fun x => Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                                      (@EquivLike.toFunLike.{1, 1, 1}
                                                        (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                          (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                                        (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                        (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                                        (@Equiv.instEquivLike.{1, 1}
                                                          (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                          (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))))
                                                      (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b) e))
                                                  (@List.cons.{0}
                                                    (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                      (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                                    (@DecrAlmostLinearSSSP.Decremental.CutOp.insert b.input.n
                                                      (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                                      (@DFunLike.coe.{1, 1, 1}
                                                        (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                          (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                                        (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                        (fun x => Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                                        (@EquivLike.toFunLike.{1, 1, 1}
                                                          (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                            (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                                          (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                          (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                                          (@Equiv.instEquivLike.{1, 1}
                                                            (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                            (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))))
                                                        (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b) e)
                                                      (DecrAlmostLinearSSSP.Decremental.tail b e)
                                                      (DecrAlmostLinearSSSP.Decremental.head b e)
                                                      (DecrAlmostLinearSSSP.Decremental.capacity b
                                                        (@DecrAlmostLinearSSSP.Decremental.State.active b state)
                                                        (DecrAlmostLinearSSSP.Decremental.labels b state) e))
                                                    (@List.cons.{0}
                                                      (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                        (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                                      (@DecrAlmostLinearSSSP.Decremental.CutOp.paired b.input.n
                                                        (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                                        (DecrAlmostLinearSSSP.Decremental.head b e)
                                                        (DecrAlmostLinearSSSP.Decremental.tail b e)
                                                        (@HSub.hSub.{0, 0, 0} Real Real Real
                                                          (@instHSub.{0} Real Real.instSub)
                                                          (DecrAlmostLinearSSSP.Decremental.capacity b
                                                            (@DecrAlmostLinearSSSP.Decremental.State.active b state)
                                                            (DecrAlmostLinearSSSP.Decremental.labels b state) e)
                                                          (@DecrAlmostLinearSSSP.Decremental.State.cache b state e)))
                                                      (@List.nil.{0}
                                                        (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                          (DecrAlmostLinearSSSP.Decremental.logicalCount b))))))))))
                                        (And
                                          (@LE.le.{0} Nat instLENat
                                            (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                  b.input.size)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                    b.weightExponent)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                impl K0 ξ h Γ init s ctx).work
                                            (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                  b.input.size)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                    b.weightExponent)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                impl K0 ξ h Γ init t next).work)
                                          (@Eq.{1} Nat
                                            (DecrAlmostLinearSSSP.Decremental.reportVolume
                                              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines b B N
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                  b.input.size)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                    b.weightExponent)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                impl K0 ξ h Γ init t next))
                                            (DecrAlmostLinearSSSP.Decremental.reportVolume
                                              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines b B N
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                  b.input.size)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                    b.weightExponent)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                impl K0 ξ h Γ init s ctx))))))))))) ∧ (∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {B N : Nat} {K K0 ξ h Γ init : Real}
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
      impl K0 ξ h Γ init s),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    @LE.le.{0} Nat instLENat b.input.n B →
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) N →
        @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.registerBound impl.program.code) N →
          @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
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
                      impl K0 ξ h Γ init s ctx)) →
                ∀ (e : DecrAlmostLinearSSSP.Decremental.Edge b)
                  (xs : List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)),
                  @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
                      (@DecrAlmostLinearSSSP.Decremental.State.pending b state)
                      (@List.cons.{0} (DecrAlmostLinearSSSP.Decremental.Edge b) e xs) →
                    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
                        (DecrAlmostLinearSSSP.Decremental.CoreMemory.encodedEdge b e) →
                      ∃ cost t next,
                        And
                          (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                            (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.refreshCode N impl.program) s cost t)
                          (And
                            (@LE.le.{0} Nat instLENat cost
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (DecrAlmostLinearSSSP.Decremental.dispatchCharge impl.program.code)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                                      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                              b.weightExponent)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                          impl K0 ξ h Γ init t next).work
                                      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                              b.weightExponent)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                          impl K0 ξ h Γ init s ctx).work))
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40))) N))
                                (@OfNat.ofNat.{0} Nat (nat_lit 218) (instOfNatNat (nat_lit 218)))))
                            (And
                              (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K
                                (DecrAlmostLinearSSSP.Decremental.refresh b state e) t)
                              (And
                                (DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K
                                  (DecrAlmostLinearSSSP.Decremental.refresh b state e))
                                (And
                                  (@DecrAlmostLinearSSSP.Decremental.CutModel b
                                    (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                    (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b)
                                    (DecrAlmostLinearSSSP.Decremental.refresh b state e)
                                    (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                            b.weightExponent)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                        impl K0 ξ h Γ init t next)))
                                  (And
                                    (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                                      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.first b B N
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                            b.weightExponent)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                        impl K0 ξ h Γ init t next)
                                      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.first b B N
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                            b.weightExponent)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                        impl K0 ξ h Γ init s ctx))
                                    (And
                                      (@Eq.{1}
                                        (List.{0}
                                          (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                            (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                        (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                              b.weightExponent)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
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
                                          (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                              b.input.size)
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                b.weightExponent)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                            impl K0 ξ h Γ init s ctx)
                                          (@List.cons.{0}
                                            (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                              (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                            (@DecrAlmostLinearSSSP.Decremental.CutOp.queryY b.input.n
                                              (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                              (DecrAlmostLinearSSSP.Decremental.tail b e))
                                            (@List.cons.{0}
                                              (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                              (@DecrAlmostLinearSSSP.Decremental.CutOp.queryY b.input.n
                                                (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                                (DecrAlmostLinearSSSP.Decremental.head b e))
                                              (@List.cons.{0}
                                                (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                  (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                                (@DecrAlmostLinearSSSP.Decremental.CutOp.erase b.input.n
                                                  (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                                  (@DFunLike.coe.{1, 1, 1}
                                                    (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                      (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                                    (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                    (fun x => Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                                    (@EquivLike.toFunLike.{1, 1, 1}
                                                      (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                        (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                                      (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                      (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                                      (@Equiv.instEquivLike.{1, 1}
                                                        (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                        (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))))
                                                    (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b) e))
                                                (@List.cons.{0}
                                                  (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                    (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                                  (@DecrAlmostLinearSSSP.Decremental.CutOp.insert b.input.n
                                                    (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                                    (@DFunLike.coe.{1, 1, 1}
                                                      (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                        (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                                      (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                      (fun x => Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                                      (@EquivLike.toFunLike.{1, 1, 1}
                                                        (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                          (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                                        (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                        (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                                        (@Equiv.instEquivLike.{1, 1}
                                                          (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                          (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))))
                                                      (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b) e)
                                                    (DecrAlmostLinearSSSP.Decremental.tail b e)
                                                    (DecrAlmostLinearSSSP.Decremental.head b e)
                                                    (DecrAlmostLinearSSSP.Decremental.capacity b
                                                      (@DecrAlmostLinearSSSP.Decremental.State.active b state)
                                                      (DecrAlmostLinearSSSP.Decremental.labels b state) e))
                                                  (@List.cons.{0}
                                                    (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                      (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                                    (@DecrAlmostLinearSSSP.Decremental.CutOp.paired b.input.n
                                                      (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                                      (DecrAlmostLinearSSSP.Decremental.head b e)
                                                      (DecrAlmostLinearSSSP.Decremental.tail b e)
                                                      (@HSub.hSub.{0, 0, 0} Real Real Real
                                                        (@instHSub.{0} Real Real.instSub)
                                                        (DecrAlmostLinearSSSP.Decremental.capacity b
                                                          (@DecrAlmostLinearSSSP.Decremental.State.active b state)
                                                          (DecrAlmostLinearSSSP.Decremental.labels b state) e)
                                                        (@DecrAlmostLinearSSSP.Decremental.State.cache b state e)))
                                                    (@List.nil.{0}
                                                      (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                        (DecrAlmostLinearSSSP.Decremental.logicalCount b))))))))))
                                      (And
                                        (@LE.le.{0} Nat instLENat
                                          (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                b.input.size)
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                  b.weightExponent)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                              impl K0 ξ h Γ init s ctx).work
                                          (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                b.input.size)
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                  b.weightExponent)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                              impl K0 ξ h Γ init t next).work)
                                        (@Eq.{1} Nat
                                          (DecrAlmostLinearSSSP.Decremental.reportVolume
                                            (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines b B N
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                b.input.size)
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                  b.weightExponent)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                              impl K0 ξ h Γ init t next))
                                          (DecrAlmostLinearSSSP.Decremental.reportVolume
                                            (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines b B N
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                b.input.size)
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                  b.weightExponent)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                              impl K0 ξ h Γ init s ctx)))))))))))))) ∧ (((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreHeadSelect.code s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    (DecrAlmostLinearSSSP.Decremental.CoreHeadSelect.result s)) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreHeadSelect.code k)) ∧ ((∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreHeadSelect.code k) ∧ ((DecrAlmostLinearSSSP.Decremental.Structured.NoMemory DecrAlmostLinearSSSP.Decremental.CoreHeadSelect.code) ∧ (@Eq.{1} Bool
  (DecrAlmostLinearSSSP.Decremental.Structured.evenRegisters DecrAlmostLinearSSSP.Decremental.CoreHeadSelect.code)
  Bool.true))))))) ∧ ((((((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B N : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
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
                (DecrAlmostLinearSSSP.Decremental.CoreMemory.encodedEdge b e)))) ∧ (∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {B N : Nat} {K K0 ξ h Γ init : Real}
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
      impl K0 ξ h Γ init s),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    @LE.le.{0} Nat instLENat b.input.n B →
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) N →
        @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.registerBound impl.program.code) N →
          @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
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
                      impl K0 ξ h Γ init s ctx)) →
                ∀ (e : DecrAlmostLinearSSSP.Decremental.Edge b)
                  (xs : List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)),
                  @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
                      (@DecrAlmostLinearSSSP.Decremental.State.pending b state)
                      (@List.cons.{0} (DecrAlmostLinearSSSP.Decremental.Edge b) e xs) →
                    @Eq.{1} Bool (@DecrAlmostLinearSSSP.Decremental.State.stopped b state) Bool.false →
                      ∃ cost t next,
                        And
                          (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                            (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.drainOneCode N impl.program) s cost t)
                          (And
                            (@LE.le.{0} Nat instLENat cost
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (DecrAlmostLinearSSSP.Decremental.dispatchCharge impl.program.code)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                                      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                              b.weightExponent)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                          impl K0 ξ h Γ init t next).work
                                      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                              b.weightExponent)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                          impl K0 ξ h Γ init s ctx).work))
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40))) N))
                                (@OfNat.ofNat.{0} Nat (nat_lit 219) (instOfNatNat (nat_lit 219)))))
                            (And
                              (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K
                                (DecrAlmostLinearSSSP.Decremental.refresh b state e) t)
                              (And
                                (DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K
                                  (DecrAlmostLinearSSSP.Decremental.refresh b state e))
                                (And
                                  (@DecrAlmostLinearSSSP.Decremental.CutModel b
                                    (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                    (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b)
                                    (DecrAlmostLinearSSSP.Decremental.refresh b state e)
                                    (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                            b.weightExponent)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                        impl K0 ξ h Γ init t next)))
                                  (And
                                    (DecrAlmostLinearSSSP.Decremental.RuntimeRepairStep b K state
                                      (DecrAlmostLinearSSSP.Decremental.refresh b state e))
                                    (And
                                      (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                                        (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.first b B N
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                              b.weightExponent)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                          impl K0 ξ h Γ init t next)
                                        (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.first b B N
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                              b.weightExponent)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                          impl K0 ξ h Γ init s ctx))
                                      (And
                                        (@Eq.{1} Nat
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
                                              impl K0 ξ h Γ init t next))
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
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
                                                impl K0 ξ h Γ init s ctx))
                                            (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))
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
                                                impl K0 ξ h Γ init t next))
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
                                                impl K0 ξ h Γ init s ctx)))
                                          (And
                                            (@LE.le.{0} Nat instLENat
                                              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                    b.input.size)
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                      b.weightExponent)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                  impl K0 ξ h Γ init s ctx).work
                                              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                    b.input.size)
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                      b.weightExponent)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                  impl K0 ξ h Γ init t next).work)
                                            (@Eq.{1} Nat
                                              (DecrAlmostLinearSSSP.Decremental.reportVolume
                                                (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines b B N
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                    b.input.size)
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                      b.weightExponent)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                  impl K0 ξ h Γ init t next))
                                              (DecrAlmostLinearSSSP.Decremental.reportVolume
                                                (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines b B N
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                    b.input.size)
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                      b.weightExponent)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                  impl K0 ξ h Γ init s ctx)))))))))))))) ∧ ((DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreCommit.headCode
  (@OfNat.ofNat.{0} Nat (nat_lit 650) (instOfNatNat (nat_lit 650)))) ∧ (∀ (N : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program),
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.refreshCode N p)
    (@OfNat.ofNat.{0} Nat (nat_lit 650) (instOfNatNat (nat_lit 650)))))) ∧ (((∀ (N : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program),
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.drainOneCode N p)
    (@OfNat.ofNat.{0} Nat (nat_lit 650) (instOfNatNat (nat_lit 650)))) ∧ (∀ {l : Nat} (xs : List.{0} (Fin l)) (v : Nat) (e : Fin l),
  Iff
    (@Membership.mem.{0, 0} (Fin l) (List.{0} (Fin l)) (@List.instMembership.{0} (Fin l))
      (DecrAlmostLinearSSSP.Decremental.CoreReports.push l xs v) e)
    (Or (@Membership.mem.{0, 0} (Fin l) (List.{0} (Fin l)) (@List.instMembership.{0} (Fin l)) xs e)
      (@Eq.{1} Nat (@Fin.val l e) v)))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreReports.fetchCode s
    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
    (DecrAlmostLinearSSSP.Decremental.CoreReports.fetched s)) ∧ ((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 584) (instOfNatNat (nat_lit 584))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreReports.fetchCode k) ∧ (∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreReports.fetchCode k))))) ∧ ((((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  And (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.CoreReports.fetched s).natMem s.natMem)
    (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.CoreReports.fetched s).realMem s.realMem)) ∧ (∀ (B offset v : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))) B →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 580) (instOfNatNat (nat_lit 580))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) offset) →
        @Eq.{1} Nat
            (s.natMem
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) offset))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) v) →
          @Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.CoreReports.fetched s).natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) v))) ∧ ((∀ {B l : Nat} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.CoreReports.Environment B l s →
    (∀ (k : Nat),
        @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat)
            (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))
              (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 552) (instOfNatNat (nat_lit 552)))
                (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))
                  (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26)))
                    (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 542) (instOfNatNat (nat_lit 542)))
                      (@List.nil.{0} Nat))))))
            k →
          @Eq.{1} Nat (t.natReg k) (s.natReg k)) →
      DecrAlmostLinearSSSP.Decremental.CoreReports.Environment B l t) ∧ ((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 546) (instOfNatNat (nat_lit 546))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 580) (instOfNatNat (nat_lit 580))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 584) (instOfNatNat (nat_lit 584))) →
          Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 562) (instOfNatNat (nat_lit 562))))
              (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 572) (instOfNatNat (nat_lit 572))) k) →
            DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreReports.body k) ∧ (∀ (k : Nat), DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreReports.body k)))) ∧ (((∀ (B l offset v : Nat) (xs : List.{0} (Fin l)) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreReports.Environment B l s →
    @DecrAlmostLinearSSSP.Decremental.CorePending.View l B xs s →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 580) (instOfNatNat (nat_lit 580))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) offset) →
        @Eq.{1} Nat
            (s.natMem
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) offset))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) v) →
          ∃ cost t,
            And
              (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreReports.body s cost
                t)
              (And (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16))))
                (And
                  (@DecrAlmostLinearSSSP.Decremental.CorePending.View l B
                    (DecrAlmostLinearSSSP.Decremental.CoreReports.push l xs v) t)
                  (And (DecrAlmostLinearSSSP.Decremental.CoreReports.Environment B l t)
                    (And
                      (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 580) (instOfNatNat (nat_lit 580))))
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
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
                          (DecrAlmostLinearSSSP.Decremental.CorePending.MemoryFrame B l s t)))))))) ∧ (∀ {l : Nat} (xs : List.{0} (Fin l)) (reports : List.{0} Nat) (e : Fin l),
  Iff
    (@Membership.mem.{0, 0} (Fin l) (List.{0} (Fin l)) (@List.instMembership.{0} (Fin l))
      (DecrAlmostLinearSSSP.Decremental.CoreReports.consume l xs reports) e)
    (Or (@Membership.mem.{0, 0} (Fin l) (List.{0} (Fin l)) (@List.instMembership.{0} (Fin l)) xs e)
      (@Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat) reports (@Fin.val l e))))) ∧ ((∀ (B l : Nat) (reports : List.{0} Nat) (xs : List.{0} (Fin l)) (offset : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreReports.Environment B l s →
    @DecrAlmostLinearSSSP.Decremental.CorePending.View l B xs s →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 580) (instOfNatNat (nat_lit 580))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) offset) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 582) (instOfNatNat (nat_lit 582))))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset (@List.length.{0} Nat reports))) →
          (∀ (j : Nat) (hj : @LT.lt.{0} Nat instLTNat j (@List.length.{0} Nat reports)),
              @Eq.{1} Nat
                (s.natMem
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset j)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (@GetElem.getElem.{0, 0, 0} (List.{0} Nat) Nat Nat
                    (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Nat as))
                    (@List.instGetElemNatLtLength.{0} Nat) reports j hj))) →
            ∃ cost t,
              And
                (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreReports.loop s
                  cost t)
                (And
                  (@LE.le.{0} Nat instLENat cost
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18))) (@List.length.{0} Nat reports))
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (And
                    (@DecrAlmostLinearSSSP.Decremental.CorePending.View l B
                      (DecrAlmostLinearSSSP.Decremental.CoreReports.consume l xs reports) t)
                    (And (DecrAlmostLinearSSSP.Decremental.CoreReports.Environment B l t)
                      (And
                        (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 580) (instOfNatNat (nat_lit 580))))
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset
                              (@List.length.{0} Nat reports))))
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
                            (DecrAlmostLinearSSSP.Decremental.CorePending.MemoryFrame B l s t)))))))) ∧ ((∀ {l : Nat} (g : DecrAlmostLinearSSSP.Decremental.Machine) (e : Fin l),
  Iff
    (@Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat)
      (DecrAlmostLinearSSSP.Decremental.CoreReports.reportList g) (@Fin.val l e))
    (@DecrAlmostLinearSSSP.Decremental.Reported l g e)) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreReports.setup s
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    (DecrAlmostLinearSSSP.Decremental.CoreReports.setupData s))))))) ∧ (((((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 580) (instOfNatNat (nat_lit 580))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 582) (instOfNatNat (nat_lit 582))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreReports.setup k) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    And
      (@Eq.{1} Nat
        ((DecrAlmostLinearSSSP.Decremental.CoreReports.setupData s).natReg
          (@OfNat.ofNat.{0} Nat (nat_lit 580) (instOfNatNat (nat_lit 580))))
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@Eq.{1} Nat
        ((DecrAlmostLinearSSSP.Decremental.CoreReports.setupData s).natReg
          (@OfNat.ofNat.{0} Nat (nat_lit 582) (instOfNatNat (nat_lit 582))))
        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 23) (instOfNatNat (nat_lit 23))))))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  And (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.CoreReports.setupData s).natMem s.natMem)
    (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.CoreReports.setupData s).realMem s.realMem)) ∧ (∀ (B l : Nat) (g : DecrAlmostLinearSSSP.Decremental.Machine) (xs : List.{0} (Fin l))
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
                          (DecrAlmostLinearSSSP.Decremental.CorePending.MemoryFrame B l s t)))))))))) ∧ (((∀ (l : Nat) (xs : List.{0} (Fin l)) (v : Nat),
  @LE.le.{0} Nat instLENat (@List.length.{0} (Fin l) (DecrAlmostLinearSSSP.Decremental.CoreReports.push l xs v))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin l) xs)
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) ∧ (∀ (l : Nat) (xs : List.{0} (Fin l)) (reports : List.{0} Nat),
  @LE.le.{0} Nat instLENat
    (@List.length.{0} (Fin l) (DecrAlmostLinearSSSP.Decremental.CoreReports.consume l xs reports))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin l) xs)
      (@List.length.{0} Nat reports)))) ∧ ((∀ (l : Nat) (g : DecrAlmostLinearSSSP.Decremental.Machine),
  @LE.le.{0} Nat instLENat
    (@List.length.{0} (Fin l)
      (DecrAlmostLinearSSSP.Decremental.CoreReports.consume l (@List.nil.{0} (Fin l))
        (DecrAlmostLinearSSSP.Decremental.CoreReports.reportList g)))
    (DecrAlmostLinearSSSP.Decremental.reportCount g)) ∧ ((∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {B N m exponent : Nat} {K K0 ξ h Γ init : Real}
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
            @DecrAlmostLinearSSSP.Decremental.CutModel b (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b) state
                (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                  (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m exponent impl K0 ξ h Γ init s
                    ctx)) →
              @Ne.{1} (Fin b.input.n → Real) (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b state)
                  (@OfNat.ofNat.{0} (Fin b.input.n → Real) (nat_lit 0)
                    (@Zero.toOfNat0.{0} (Fin b.input.n → Real)
                      (@Pi.instZero.{0, 0} (Fin b.input.n) (fun a => Real) fun i => Real.instZero))) →
                @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                    K0 →
                  @LE.le.{0} Real Real.instLE K0 K →
                    ∃ cost t next,
                      And
                        (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                          (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.ratioCode N impl.program) s cost t)
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
                              (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19)))))
                          (And (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state t)
                            (And
                              (@DecrAlmostLinearSSSP.Decremental.CutModel b
                                (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b) state
                                (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                  (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m exponent impl
                                    K0 ξ h Γ init t next)))
                              (And
                                (@DecrAlmostLinearSSSP.Decremental.RatioGuarantee b.input.n
                                  (@Fintype.card.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)
                                    (@instFintypeSum.{0, 0} (Fin b.input.k)
                                      (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) (Fin.fintype b.input.k)
                                      (DecrAlmostLinearSSSP.Decremental.instFintypeReturnVertex b)))
                                  (DecrAlmostLinearSSSP.Decremental.cachedPhysical b state) K
                                  (@DecrAlmostLinearSSSP.Decremental.CutState.lastG b.input.n
                                    (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                    (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m exponent
                                        impl K0 ξ h Γ init t next)))
                                  (@DecrAlmostLinearSSSP.Decremental.CutState.lastU b.input.n
                                    (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                    (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m exponent
                                        impl K0 ξ h Γ init t next)))
                                  (@DecrAlmostLinearSSSP.Decremental.CutState.lastCut b.input.n
                                    (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                    (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m exponent
                                        impl K0 ξ h Γ init t next))))
                                (And
                                  (@Eq.{1} Bool
                                    (@DecrAlmostLinearSSSP.Decremental.CutState.hasCut b.input.n
                                      (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                      (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                        (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m
                                          exponent impl K0 ξ h Γ init t next)))
                                    Bool.true)
                                  (And
                                    (@Eq.{1} Real
                                      (t.realReg (@OfNat.ofNat.{0} Nat (nat_lit 29) (instOfNatNat (nat_lit 29))))
                                      (@DecrAlmostLinearSSSP.Decremental.CutState.lastG b.input.n
                                        (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                        (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                          (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m
                                            exponent impl K0 ξ h Γ init t next))))
                                    (And
                                      (@Eq.{1} Real
                                        (t.realReg (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31))))
                                        (@DecrAlmostLinearSSSP.Decremental.CutState.lastU b.input.n
                                          (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                          (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                            (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m
                                              exponent impl K0 ξ h Γ init t next))))
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
                                                (@DecrAlmostLinearSSSP.Decremental.CutOp.ratio b.input.n
                                                  (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                                (@List.nil.{0}
                                                  (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                    (DecrAlmostLinearSSSP.Decremental.logicalCount b))))))
                                          (And
                                            (@LE.le.{0} Nat instLENat
                                              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m
                                                  exponent impl K0 ξ h Γ init s ctx).work
                                              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m
                                                  exponent impl K0 ξ h Γ init t next).work)
                                            (@Eq.{1} Nat
                                              (DecrAlmostLinearSSSP.Decremental.reportVolume
                                                (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines b B N
                                                  m exponent impl K0 ξ h Γ init t next))
                                              (DecrAlmostLinearSSSP.Decremental.reportVolume
                                                (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines b B N
                                                  m exponent impl K0 ξ h Γ init s ctx)))))))))))))) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 546) (instOfNatNat (nat_lit 546))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 580) (instOfNatNat (nat_lit 580))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 582) (instOfNatNat (nat_lit 582))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 584) (instOfNatNat (nat_lit 584))) →
            Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 562) (instOfNatNat (nat_lit 562))))
                (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 572) (instOfNatNat (nat_lit 572))) k) →
              DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreReports.code k))))) ∧ ((((∀ (j : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreReports.code
    (DecrAlmostLinearSSSP.Decremental.shadowReg j)) ∧ (∀ (j : Nat), DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreReports.code j)) ∧ ((∀ {B l : Nat} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.CorePending.MemoryFrame B l s t →
    ∀ (j : Nat),
      @LE.le.{0} Nat instLENat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) l))
          j →
        @Eq.{1} Nat (t.natMem j) (s.natMem j)) ∧ ((∀ {B l : Nat} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.CorePending.MemoryFrame B l s t →
    ∀ (j : Nat), @LE.le.{0} Nat instLENat j B → @Eq.{1} Nat (t.natMem j) (s.natMem j)) ∧ (∀ {B : Nat} (b : DecrAlmostLinearSSSP.Decremental.Core) {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.CorePending.MemoryFrame B (DecrAlmostLinearSSSP.Decremental.logicalCount b) s t →
    ∀ (e : DecrAlmostLinearSSSP.Decremental.Edge b) (offset : Nat),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) offset →
        @LT.lt.{0} Nat instLTNat offset (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
          @Eq.{1} Nat (t.natMem (DecrAlmostLinearSSSP.Decremental.CoreMemory.field b B e offset))
            (s.natMem (DecrAlmostLinearSSSP.Decremental.CoreMemory.field b B e offset)))))) ∧ (((∀ (B R N l : Nat) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  (s t : DecrAlmostLinearSSSP.Decremental.Structured.Data) (cost : Nat),
  DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N g s →
    @LE.le.{0} Nat instLENat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) l))
        R →
      DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreReports.code s cost t →
        @Eq.{1} (Nat → Real) t.realMem s.realMem →
          DecrAlmostLinearSSSP.Decremental.CorePending.MemoryFrame B l s t →
            DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N g t) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (ys : List.{0} (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
  (s t : DecrAlmostLinearSSSP.Decremental.Structured.Data) (cost : Nat),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    @LE.le.{0} Nat instLENat b.input.n B →
      DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreReports.code s cost t →
        @DecrAlmostLinearSSSP.Decremental.CorePending.View (DecrAlmostLinearSSSP.Decremental.logicalCount b) B ys t →
          @Eq.{1} (Nat → Real) t.realMem s.realMem →
            DecrAlmostLinearSSSP.Decremental.CorePending.MemoryFrame B (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                s t →
              DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K
                (@DecrAlmostLinearSSSP.Decremental.State.mk b (@DecrAlmostLinearSSSP.Decremental.State.active b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.y b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.cache b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.baseline b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.nonzeroEntries b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.sample b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.output b state)
                  (@List.map.{0, 0} (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                    (DecrAlmostLinearSSSP.Decremental.Edge b)
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
                        (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b)))
                    ys)
                  (@DecrAlmostLinearSSSP.Decremental.State.stopped b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.toggles b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.history b state))
                t)) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    DecrAlmostLinearSSSP.Decremental.CoreReports.Environment B (DecrAlmostLinearSSSP.Decremental.logicalCount b) s) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  (ys : List.{0} (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))),
  (∀ (d : Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)),
      Iff
        (@Membership.mem.{0, 0} (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
          (List.{0} (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
          (@List.instMembership.{0} (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))) ys d)
        (@DecrAlmostLinearSSSP.Decremental.Reported (DecrAlmostLinearSSSP.Decremental.logicalCount b) g d)) →
    ∀ (e : DecrAlmostLinearSSSP.Decremental.Edge b),
      Iff
        (@Membership.mem.{0, 0} (DecrAlmostLinearSSSP.Decremental.Edge b)
          (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
          (@List.instMembership.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
          (@List.map.{0, 0} (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
            (DecrAlmostLinearSSSP.Decremental.Edge b)
            (@DFunLike.coe.{1, 1, 1}
              (Equiv.{1, 1} (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                (DecrAlmostLinearSSSP.Decremental.Edge b))
              (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)) (fun x => DecrAlmostLinearSSSP.Decremental.Edge b)
              (@EquivLike.toFunLike.{1, 1, 1}
                (Equiv.{1, 1} (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                  (DecrAlmostLinearSSSP.Decremental.Edge b))
                (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)) (DecrAlmostLinearSSSP.Decremental.Edge b)
                (@Equiv.instEquivLike.{1, 1} (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                  (DecrAlmostLinearSSSP.Decremental.Edge b)))
              (@Equiv.symm.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
                (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b)))
            ys)
          e)
        (@DecrAlmostLinearSSSP.Decremental.Reported (DecrAlmostLinearSSSP.Decremental.logicalCount b) g
          (@DFunLike.coe.{1, 1, 1}
            (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
              (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
            (DecrAlmostLinearSSSP.Decremental.Edge b) (fun x => Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
            (@EquivLike.toFunLike.{1, 1, 1}
              (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
                (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
              (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
              (@Equiv.instEquivLike.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
                (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))))
            (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b) e))) ∧ (∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {B N : Nat} {K K0 h Γ init : Real}
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
                        K (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                      h Γ init s ctx)) →
                @Eq.{1} Bool (@DecrAlmostLinearSSSP.Decremental.State.stopped b state) Bool.false →
                  @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
                      (@DecrAlmostLinearSSSP.Decremental.State.pending b state)
                      (@List.nil.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) →
                    @Ne.{1} (Fin b.input.n → Real) (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b state)
                        (@OfNat.ofNat.{0} (Fin b.input.n → Real) (nat_lit 0)
                          (@Zero.toOfNat0.{0} (Fin b.input.n → Real)
                            (@Pi.instZero.{0, 0} (Fin b.input.n) (fun a => Real) fun i => Real.instZero))) →
                      @Eq.{1} Bool
                          (@DecrAlmostLinearSSSP.Decremental.CutState.hasCut b.input.n
                            (DecrAlmostLinearSSSP.Decremental.logicalCount b)
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
                                h Γ init s ctx)))
                          Bool.true →
                        @DecrAlmostLinearSSSP.Decremental.RatioGuarantee b.input.n
                            (@Fintype.card.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)
                              (@instFintypeSum.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b)
                                (Fin.fintype b.input.k) (DecrAlmostLinearSSSP.Decremental.instFintypeReturnVertex b)))
                            (DecrAlmostLinearSSSP.Decremental.cachedPhysical b state) K
                            (@DecrAlmostLinearSSSP.Decremental.CutState.lastG b.input.n
                              (DecrAlmostLinearSSSP.Decremental.logicalCount b)
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
                                  h Γ init s ctx)))
                            (@DecrAlmostLinearSSSP.Decremental.CutState.lastU b.input.n
                              (DecrAlmostLinearSSSP.Decremental.logicalCount b)
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
                                  h Γ init s ctx)))
                            (@DecrAlmostLinearSSSP.Decremental.CutState.lastCut b.input.n
                              (DecrAlmostLinearSSSP.Decremental.logicalCount b)
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
                                  h Γ init s ctx))) →
                          @LT.lt.{0} Real Real.instLT
                              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                (@DecrAlmostLinearSSSP.Decremental.CutState.lastG b.input.n
                                  (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                  (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                    (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
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
                                      h Γ init s ctx)))
                                (@DecrAlmostLinearSSSP.Decremental.CutState.lastU b.input.n
                                  (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                  (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                    (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
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
                                      h Γ init s ctx))))
                              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                (@Neg.neg.{0} Real Real.instNeg
                                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                  (@OfNat.ofNat.{0} Real (nat_lit 4)
                                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                                      (@Nat.instAtLeastTwoHAddOfNat
                                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                        (@Nat.instNeZeroSucc
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                                  K)) →
                            @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31))))
                                (@DecrAlmostLinearSSSP.Decremental.CutState.lastU b.input.n
                                  (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                  (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                    (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
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
                                      h Γ init s ctx))) →
                              ∃ cost t next reports,
                                And
                                  (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                    (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.toggleCode N impl.program) s cost t)
                                  (And
                                    (@LE.le.{0} Nat instLENat cost
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (DecrAlmostLinearSSSP.Decremental.dispatchCharge impl.program.code)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
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
                                                    h Γ init t next).work
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
                                                    h Γ init s ctx).work))
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) N))
                                          (@OfNat.ofNat.{0} Nat (nat_lit 27) (instOfNatNat (nat_lit 27))))
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))
                                          (DecrAlmostLinearSSSP.Decremental.reportCount
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
                                              h Γ init t next)))))
                                    (And
                                      (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K
                                        (DecrAlmostLinearSSSP.Decremental.reportedToggle b K state
                                          (@DecrAlmostLinearSSSP.Decremental.modelReply b
                                            (DecrAlmostLinearSSSP.Decremental.logicalCount b)
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
                                                h Γ init s ctx)))
                                          reports)
                                        t)
                                      (And
                                        (DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K
                                          (DecrAlmostLinearSSSP.Decremental.reportedToggle b K state
                                            (@DecrAlmostLinearSSSP.Decremental.modelReply b
                                              (DecrAlmostLinearSSSP.Decremental.logicalCount b)
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
                                                  h Γ init s ctx)))
                                            reports))
                                        (And
                                          (@DecrAlmostLinearSSSP.Decremental.CutModel b
                                            (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                            (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b)
                                            (DecrAlmostLinearSSSP.Decremental.reportedToggle b K state
                                              (@DecrAlmostLinearSSSP.Decremental.modelReply b
                                                (DecrAlmostLinearSSSP.Decremental.logicalCount b)
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
                                                    h Γ init s ctx)))
                                              reports)
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
                                            (DecrAlmostLinearSSSP.Decremental.RuntimeRepairStep b K state
                                              (DecrAlmostLinearSSSP.Decremental.reportedToggle b K state
                                                (@DecrAlmostLinearSSSP.Decremental.modelReply b
                                                  (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                                  (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                                    (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B
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
                                                      h Γ init s ctx)))
                                                reports))
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
                                                (@Eq.{1} Nat
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
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@List.length.{0}
                                                      (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                        (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                                      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N
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
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                (And
                                                  (@Eq.{1} Nat
                                                    (@DecrAlmostLinearSSSP.Decremental.toggleVolume b.input.n
                                                      (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                                      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N
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
                                                        h Γ init t next))
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@DecrAlmostLinearSSSP.Decremental.toggleVolume b.input.n
                                                        (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                                        (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B
                                                          N
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
                                                                (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                            K
                                                            (@Neg.neg.{0} Int Int.instNegInt
                                                              (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                                (@instOfNat (nat_lit 2)))))
                                                          h Γ init s ctx))
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                  (And
                                                    (@LE.le.{0} Nat instLENat
                                                      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b
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
                                                                (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                            K
                                                            (@Neg.neg.{0} Int Int.instNegInt
                                                              (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                                (@instOfNat (nat_lit 2)))))
                                                          h Γ init s ctx).work
                                                      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b
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
                                                                (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                            K
                                                            (@Neg.neg.{0} Int Int.instNegInt
                                                              (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                                (@instOfNat (nat_lit 2)))))
                                                          h Γ init t next).work)
                                                    (And
                                                      (@Eq.{1} Nat
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
                                                              h Γ init s ctx))
                                                          (DecrAlmostLinearSSSP.Decremental.reportCount
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
                                                              h Γ init t next))))
                                                      (@LE.le.{0} Nat instLENat
                                                        (@List.length.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                          reports)
                                                        (DecrAlmostLinearSSSP.Decremental.reportCount
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
                                                            h Γ init t next))))))))))))))))))))) := by
  exact ⟨⟨⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.CoreRefreshRead.no_memory,DecrAlmostLinearSSSP.Decremental.CoreRefreshRead.even_registers⟩,⟨DecrAlmostLinearSSSP.Decremental.CoreRefreshRead.nat_frame,DecrAlmostLinearSSSP.Decremental.CoreRefreshRead.real_frame⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.CoreRefreshRead.correct,DecrAlmostLinearSSSP.Decremental.CoreRefreshRead.source_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.CoreRefresh.computed,⟨DecrAlmostLinearSSSP.Decremental.CoreGeometry.Image.write_cache,DecrAlmostLinearSSSP.Decremental.CoreHost.Image.write_cache⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.CoreGradientDelta.even_registers,DecrAlmostLinearSSSP.Decremental.CoreGradientDelta.nat_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.CoreGradientDelta.real_frame,DecrAlmostLinearSSSP.Decremental.CoreGradientDelta.eval_code⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.CoreGeometry.Image.state_congr,DecrAlmostLinearSSSP.Decremental.CoreHost.Image.state_congr⟩,⟨DecrAlmostLinearSSSP.Decremental.CoreSource.Image.host_frame,⟨DecrAlmostLinearSSSP.Decremental.CoreHost.gradient_delta_image,DecrAlmostLinearSSSP.Decremental.CoreHost.gradient_delta_source⟩⟩⟩⟩⟩,⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.CoreHost.pop_pending_eval,DecrAlmostLinearSSSP.Decremental.CoreSource.Image.host_real_memory⟩,⟨DecrAlmostLinearSSSP.Decremental.CoreSource.Image.host_nat_memory,DecrAlmostLinearSSSP.Decremental.CoreSource.Image.pending_pop⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.CoreCommit.prefix_nat_frame,DecrAlmostLinearSSSP.Decremental.CoreCommit.prefix_real_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.CoreCommit.prefix_eval,⟨DecrAlmostLinearSSSP.Decremental.CoreGeometry.Image.write_return,DecrAlmostLinearSSSP.Decremental.CoreHost.return_write_eval⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.CoreHost.return_source_frame,DecrAlmostLinearSSSP.Decremental.CoreCommit.return_eval⟩,⟨DecrAlmostLinearSSSP.Decremental.CoreCommit.head_eval,⟨DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.refresh_head_validated,DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.refresh_head⟩⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.CoreHeadSelect.eval_code,DecrAlmostLinearSSSP.Decremental.CoreHeadSelect.nat_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.CoreHeadSelect.real_frame,⟨DecrAlmostLinearSSSP.Decremental.CoreHeadSelect.no_memory,DecrAlmostLinearSSSP.Decremental.CoreHeadSelect.even_registers⟩⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.CoreHeadSelect.correct,DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.drain_one⟩,⟨DecrAlmostLinearSSSP.Decremental.CoreCommit.head_running_frame,DecrAlmostLinearSSSP.Decremental.CoreNativeCut.refresh_running_frame⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.CoreNativeCut.drain_running_frame,DecrAlmostLinearSSSP.Decremental.CoreReports.push_membership⟩,⟨DecrAlmostLinearSSSP.Decremental.CoreReports.fetch_eval,⟨DecrAlmostLinearSSSP.Decremental.CoreReports.fetch_nat_frame,DecrAlmostLinearSSSP.Decremental.CoreReports.fetch_real_frame⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.CoreReports.fetch_mem,DecrAlmostLinearSSSP.Decremental.CoreReports.fetch_value⟩,⟨DecrAlmostLinearSSSP.Decremental.CoreReports.Environment.transfer,⟨DecrAlmostLinearSSSP.Decremental.CoreReports.body_nat_frame,DecrAlmostLinearSSSP.Decremental.CoreReports.body_real_frame⟩⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.CoreReports.body_eval,DecrAlmostLinearSSSP.Decremental.CoreReports.consume_membership⟩,⟨DecrAlmostLinearSSSP.Decremental.CoreReports.loop_eval,⟨DecrAlmostLinearSSSP.Decremental.CoreReports.reportList_membership,DecrAlmostLinearSSSP.Decremental.CoreReports.setup_eval⟩⟩⟩⟩⟩,⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.CoreReports.setup_nat_frame,DecrAlmostLinearSSSP.Decremental.CoreReports.setup_fields⟩,⟨DecrAlmostLinearSSSP.Decremental.CoreReports.setup_mem,DecrAlmostLinearSSSP.Decremental.CoreReports.eval_code⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.CoreReports.push_length,DecrAlmostLinearSSSP.Decremental.CoreReports.consume_length⟩,⟨DecrAlmostLinearSSSP.Decremental.CoreReports.initial_reports_length,⟨DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ratio,DecrAlmostLinearSSSP.Decremental.CoreReports.code_nat_frame⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.CoreReports.code_nat_shadow_frame,DecrAlmostLinearSSSP.Decremental.CoreReports.code_real_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.CoreReports.frame_above,⟨DecrAlmostLinearSSSP.Decremental.CoreReports.frame_below,DecrAlmostLinearSSSP.Decremental.CoreReports.frame_geometry⟩⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.CoreSource.Image.report_scan,DecrAlmostLinearSSSP.Decremental.CoreHost.reports_image⟩,⟨DecrAlmostLinearSSSP.Decremental.CoreHost.reports_environment,⟨DecrAlmostLinearSSSP.Decremental.CoreReports.logical_membership,DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.toggle⟩⟩⟩⟩⟩⟩⟩
