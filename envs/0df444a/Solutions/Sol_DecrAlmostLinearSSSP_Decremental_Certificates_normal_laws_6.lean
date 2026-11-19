-- Prove2me | solution 1 for DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_6
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T11:22:25.283949+00:00
-- url     : https://prove2.me/submissions/7cf96e2c-b675-4b78-a8db-b912065b195e

import Definitions.Def_DecrAlmostLinearSSSP_RAMFoundation
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
theorem DecrAlmostLinearSSSP.Decremental.Structured.Eval.nat_frame : ∀ {cmd : DecrAlmostLinearSSSP.Decremental.Structured.Cmd} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {cost k : Nat},
  DecrAlmostLinearSSSP.Decremental.Structured.Eval cmd s cost t →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame cmd k → @Eq.{1} Nat (t.natReg k) (s.natReg k) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.2.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.Structured.Eval.real_frame : ∀ {cmd : DecrAlmostLinearSSSP.Decremental.Structured.Cmd} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {cost k : Nat},
  DecrAlmostLinearSSSP.Decremental.Structured.Eval cmd s cost t →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame cmd k → @Eq.{1} Real (t.realReg k) (s.realReg k) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.2.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.TriePush.start_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePush.start s
    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
    (DecrAlmostLinearSSSP.Decremental.Exact.TriePush.started s) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_3.1.1.2.2.2.2.2
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
theorem DecrAlmostLinearSSSP.Decremental.Exact.TriePop.start_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePop.start s
    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
    (DecrAlmostLinearSSSP.Decremental.Exact.TriePop.started s) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_3.2.2.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.TriePop.Result.nat_frame : ∀ {h : Nat} {tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  (r : @DecrAlmostLinearSSSP.Decremental.Exact.TriePop.Result h tree s),
  ∀ k ∉ DecrAlmostLinearSSSP.Decremental.Exact.TriePop.registers,
    @Eq.{1} Nat ((@DecrAlmostLinearSSSP.Decremental.Exact.TriePop.Result.final h tree s r).natReg k) (s.natReg k) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.1.1.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.input_vertex_positive : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) i.n := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.1.1.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.scale_positive : ∀ (j : Nat),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
    (DecrAlmostLinearSSSP.Decremental.scale j) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.1.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.delta_positive : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (j : Nat),
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (DecrAlmostLinearSSSP.Decremental.delta i j) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.1.1.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.guest_bank_ne_host : ∀ (base j a b : Nat),
  @Ne.{1} Nat (DecrAlmostLinearSSSP.Decremental.bankAddress base j a)
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.1.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.InputCapture.eval_code : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.InputCapture.code s
    (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19)))
    (DecrAlmostLinearSSSP.Decremental.InputCapture.result s) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.1.2.2.1.1.1
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
theorem DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.tape_frame : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (s t : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.Tape i s →
    (∀ (a : Nat),
        @LT.lt.{0} Nat instLTNat a
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k)) →
          @Eq.{1} Nat (t.natMem a) (s.natMem a)) →
      DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.Tape i t := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_6.2.1.1.1.1.1
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
theorem DecrAlmostLinearSSSP.Decremental.PreservesOutside.trans : ∀ {base F : Nat} {c d e : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.PreservesOutside base F c d →
    DecrAlmostLinearSSSP.Decremental.PreservesOutside base F d e →
      DecrAlmostLinearSSSP.Decremental.PreservesOutside base F c e := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_2.1.1.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.ScaledCeiling.setup_nat_frame : ∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.ScaledCeiling.setup k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_2.2.1.2.1.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.ScaledCeiling.setup_real_frame : ∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.ScaledCeiling.setup k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_2.2.1.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.ScaledCeiling.guest_bank_outside_utility_tail : ∀ (B bank tail a u : Nat),
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
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_2.2.1.2.2.2.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.ScaledCeiling.reserve_nat_frame : ∀ (B k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 60) (instOfNatNat (nat_lit 60))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
            (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.polynomialReserve B) k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_2.2.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.ScaledCeiling.count_nat_frame : ∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
            DecrAlmostLinearSSSP.Decremental.ScaledCeiling.countScales k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_3.1.1.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.ScaledCeiling.area_nat_frame : ∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.ScaledCeiling.scaleArea
            k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_3.1.1.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.Layout.real_frame : ∀ (stride k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.Layout.code stride) k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_3.1.1.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.utilityDepth_power : ∀ (m : Nat),
  @LE.le.{0} Real Real.instLE
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real (nat_lit 512)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 512) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 511) (instOfNatNat (nat_lit 511)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 510) (instOfNatNat (nat_lit 510)))))))
      (@HPow.hPow.{0, 0, 0} Real Nat Real
        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
        (@Nat.cast.{0} Real Real.instNatCast m) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@HPow.hPow.{0, 0, 0} Real Nat Real
      (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
      (@OfNat.ofNat.{0} Real (nat_lit 2)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
      (DecrAlmostLinearSSSP.Decremental.utilityDepth m)) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_3.1.1.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.normal_barrier_argument_bound : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    @LT.lt.{0} Real Real.instLT
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@Nat.cast.{0} Real Real.instNatCast i.size))
        i.accuracy →
      And
        (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 512)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 512) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 511) (instOfNatNat (nat_lit 511)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 510) (instOfNatNat (nat_lit 510)))))))
              (@Nat.cast.{0} Real Real.instNatCast i.n))
            i.accuracy))
        (@LE.le.{0} Real Real.instLE
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 512)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 512) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 511) (instOfNatNat (nat_lit 511)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 510) (instOfNatNat (nat_lit 510)))))))
              (@Nat.cast.{0} Real Real.instNatCast i.n))
            i.accuracy)
          (@HPow.hPow.{0, 0, 0} Real Nat Real
            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
            (DecrAlmostLinearSSSP.Decremental.utilityDepth i.size))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_3.1.1.2.2.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.ScaleParameters.prepare_nat_frame : ∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 204) (instOfNatNat (nat_lit 204))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 154) (instOfNatNat (nat_lit 154))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 156) (instOfNatNat (nat_lit 156))) →
              @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 158) (instOfNatNat (nat_lit 158))) →
                @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 160) (instOfNatNat (nat_lit 160))) →
                  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 152) (instOfNatNat (nat_lit 152))) →
                    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
                      DecrAlmostLinearSSSP.Decremental.ScaleParameters.prepare k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_3.2.1.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.ScaleParameters.prepare_real_frame : ∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 200) (instOfNatNat (nat_lit 200))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 202) (instOfNatNat (nat_lit 202))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 204) (instOfNatNat (nat_lit 204))) →
              DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
                DecrAlmostLinearSSSP.Decremental.ScaleParameters.prepare k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_3.2.1.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.ScaleParameters.fields_real_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 208) (instOfNatNat (nat_lit 208))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.ScaleParameters.writeFields k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_3.2.1.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.ScaleParameters.fields_nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 206) (instOfNatNat (nat_lit 206))) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.ScaleParameters.writeFields k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_3.2.1.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.ScaleParameters.initializeSnapshot_eval : ∀ (N : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (p : DecrAlmostLinearSSSP.Decremental.Program)
  (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    @LT.lt.{0} Real Real.instLT
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@Nat.cast.{0} Real Real.instNatCast i.size))
        i.accuracy →
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) N →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64)))) i.size →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 66) (instOfNatNat (nat_lit 66)))) i.n →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68)))) i.k →
              @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72))))
                  (@Fin.val i.n i.source) →
                @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64)))) i.accuracy →
                  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))))
                      (DecrAlmostLinearSSSP.Decremental.bankFactor
                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 110) (instOfNatNat (nat_lit 110))))) →
                    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                      @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
                          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
                        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                            (∀ (j : Nat),
                                @LT.lt.{0} Nat instLTNat j N →
                                  @LT.lt.{0} Nat instLTNat
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j))
                                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 48) (instOfNatNat (nat_lit 48))))) →
                              ∃ cost t,
                                And
                                  (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                    (DecrAlmostLinearSSSP.Decremental.ScaleParameters.initializeSnapshot N) s cost t)
                                  (And
                                    (@LE.le.{0} Nat instLENat cost
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) N)
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (DecrAlmostLinearSSSP.Decremental.dispatchCharge
                                                  DecrAlmostLinearSSSP.Decremental.ScaledCeiling.ceilingProgram.code)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))
                                                  (DecrAlmostLinearSSSP.Decremental.utilityDepth i.size))
                                                (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))))))
                                        (@OfNat.ofNat.{0} Nat (nat_lit 109) (instOfNatNat (nat_lit 109)))))
                                    (And
                                      (@Eq.{1} Nat
                                        (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50)))))
                                      (And
                                        (@Eq.{1} Nat
                                          (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 154) (instOfNatNat (nat_lit 154))))
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (DecrAlmostLinearSSSP.Decremental.bankFactor
                                              (s.natReg
                                                (@OfNat.ofNat.{0} Nat (nat_lit 110) (instOfNatNat (nat_lit 110)))))
                                            i.n))
                                        (And
                                          (@Eq.{1} Nat
                                            (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 152) (instOfNatNat (nat_lit 152))))
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (DecrAlmostLinearSSSP.Decremental.bankFactor
                                                (s.natReg
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 110) (instOfNatNat (nat_lit 110)))))
                                              (DecrAlmostLinearSSSP.Decremental.barrierHigh i)))
                                          (And
                                            (∀ (j : Nat),
                                              @LT.lt.{0} Nat instLTNat j N →
                                                And
                                                  (@Eq.{1} Nat
                                                    (t.natMem
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (t.natReg
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 50)
                                                            (instOfNatNat (nat_lit 50))))
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                          j)))
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (DecrAlmostLinearSSSP.Decremental.bankFactor
                                                        (s.natReg
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 110)
                                                            (instOfNatNat (nat_lit 110)))))
                                                      ((DecrAlmostLinearSSSP.Decremental.initialMachine p
                                                            (DecrAlmostLinearSSSP.Decremental.barrierInput i
                                                              (s.natReg
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 110)
                                                                  (instOfNatNat (nat_lit 110)))))).natReg
                                                        j)))
                                                  (@Eq.{1} Real
                                                    (t.realMem
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (t.natReg
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 50)
                                                            (instOfNatNat (nat_lit 50))))
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                          j)))
                                                    ((DecrAlmostLinearSSSP.Decremental.initialMachine p
                                                          (DecrAlmostLinearSSSP.Decremental.barrierInput i
                                                            (s.natReg
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 110)
                                                                (instOfNatNat (nat_lit 110)))))).realReg
                                                      j)))
                                            (∀ (address : Nat),
                                              (∀ (j : Nat),
                                                  @LT.lt.{0} Nat instLTNat j N →
                                                    @Ne.{1} Nat address
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (s.natReg
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 50)
                                                            (instOfNatNat (nat_lit 50))))
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                          j))) →
                                                (∀ (a : Nat),
                                                    @Ne.{1} Nat address
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (s.natReg
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 48)
                                                              (instOfNatNat (nat_lit 48))))
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                              (instOfNatNat (nat_lit 2)))
                                                            a))
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                          (instOfNatNat (nat_lit 1))))) →
                                                  And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                                    (@Eq.{1} Real (t.realMem address) (s.realMem address)))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_3.2.1.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.registerBound_ge : ∀ (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
    (DecrAlmostLinearSSSP.Decremental.registerBound code) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_3.2.2.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail.ends : ∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {c d : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail (DecrAlmostLinearSSSP.Decremental.registerBound p.code) c →
    DecrAlmostLinearSSSP.Decremental.Ends p c d →
      DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail (DecrAlmostLinearSSSP.Decremental.registerBound p.code) d := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_3.2.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.initialMachine_zero_tail : ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (i : DecrAlmostLinearSSSP.Decremental.Input),
  DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail (DecrAlmostLinearSSSP.Decremental.registerBound p.code)
    (DecrAlmostLinearSSSP.Decremental.initialMachine p i) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_3.2.2.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.TapeCopy.naturalField_nat_frame : ∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 172) (instOfNatNat (nat_lit 172))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 174) (instOfNatNat (nat_lit 174))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 162) (instOfNatNat (nat_lit 162))) →
              @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 164) (instOfNatNat (nat_lit 164))) →
                DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
                  DecrAlmostLinearSSSP.Decremental.TapeCopy.naturalField k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_4.1.1.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.TapeCopy.naturalField_real_frame : ∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 200) (instOfNatNat (nat_lit 200))) →
          DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.TapeCopy.naturalField k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_4.1.1.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.TapeCopy.weightField_nat_frame : ∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 172) (instOfNatNat (nat_lit 172))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 174) (instOfNatNat (nat_lit 174))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 162) (instOfNatNat (nat_lit 162))) →
              @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 164) (instOfNatNat (nat_lit 164))) →
                DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
                  DecrAlmostLinearSSSP.Decremental.TapeCopy.weightField k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_4.1.1.2.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.TapeCopy.weightField_real_frame : ∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 202) (instOfNatNat (nat_lit 202))) →
          DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.TapeCopy.weightField k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_4.1.1.2.2.1.1
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
theorem DecrAlmostLinearSSSP.Decremental.RecordHeader.memory_frame : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
      ∀ (address : Nat),
        @Ne.{1} Nat address (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106)))) →
          @Ne.{1} Nat address
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
            @Ne.{1} Nat address
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) →
              @Ne.{1} Nat address
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))) →
                And
                  (@Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.RecordHeader.result s).natMem address)
                    (s.natMem address))
                  (@Eq.{1} Real ((DecrAlmostLinearSSSP.Decremental.RecordHeader.result s).realMem address)
                    (s.realMem address)) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_4.1.2.2.2.1.2
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
theorem DecrAlmostLinearSSSP.Decremental.tailFrame_call : DecrAlmostLinearSSSP.Decremental.TailFrame DecrAlmostLinearSSSP.Decremental.ScaledCeiling.call := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_4.2.1.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.tailFrame_productReal : ∀ (d p x : Nat),
  @Even.{0} Nat instAddNat d →
    DecrAlmostLinearSSSP.Decremental.TailFrame (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.productReal d p x) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_4.2.1.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.tailFrame_productNat : ∀ (d p x : Nat),
  @Even.{0} Nat instAddNat d →
    DecrAlmostLinearSSSP.Decremental.TailFrame (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.productNat d p x) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_4.2.1.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.tailFrame_initializeSnapshot : ∀ (N : Nat),
  DecrAlmostLinearSSSP.Decremental.TailFrame (DecrAlmostLinearSSSP.Decremental.ScaleParameters.initializeSnapshot N) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_4.2.1.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.TailFrame.preserves : ∀ {cmd : DecrAlmostLinearSSSP.Decremental.Structured.Cmd},
  DecrAlmostLinearSSSP.Decremental.TailFrame cmd →
    ∀ {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {cost N : Nat},
      DecrAlmostLinearSSSP.Decremental.Structured.Eval cmd s cost t →
        @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) N →
          (∀ (j : Nat),
              @LE.le.{0} Nat instLENat N j →
                And
                  (@Eq.{1} Nat (s.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg j))
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (@Eq.{1} Real (s.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg j))
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))) →
            ∀ (j : Nat),
              @LE.le.{0} Nat instLENat N j →
                And
                  (@Eq.{1} Nat (t.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg j))
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (@Eq.{1} Real (t.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg j))
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_4.2.1.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.tailFrame_atom : ∀ (a : DecrAlmostLinearSSSP.Decremental.Structured.Atom),
  DecrAlmostLinearSSSP.Decremental.EvenRegisterWrites a.instruction →
    DecrAlmostLinearSSSP.Decremental.TailFrame (DecrAlmostLinearSSSP.Decremental.Structured.Cmd.atom a) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_4.2.1.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.TailFrame.branch : ∀ (test : DecrAlmostLinearSSSP.Decremental.Structured.Test) {a b : DecrAlmostLinearSSSP.Decremental.Structured.Cmd},
  DecrAlmostLinearSSSP.Decremental.TailFrame a →
    DecrAlmostLinearSSSP.Decremental.TailFrame b →
      DecrAlmostLinearSSSP.Decremental.TailFrame (DecrAlmostLinearSSSP.Decremental.Structured.Cmd.branch test a b) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_4.2.1.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.TailFrame.loop : ∀ (test : DecrAlmostLinearSSSP.Decremental.Structured.Test) {body : DecrAlmostLinearSSSP.Decremental.Structured.Cmd},
  DecrAlmostLinearSSSP.Decremental.TailFrame body →
    DecrAlmostLinearSSSP.Decremental.TailFrame (DecrAlmostLinearSSSP.Decremental.Structured.Cmd.loop test body) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_4.2.1.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.tailFrame_recordHeader : DecrAlmostLinearSSSP.Decremental.TailFrame DecrAlmostLinearSSSP.Decremental.RecordHeader.code := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_4.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Layout.code_vertex_stride : ∀ {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {stride cost : Nat},
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Layout.code stride) s cost t →
    @Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 100) (instOfNatNat (nat_lit 100))))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 66) (instOfNatNat (nat_lit 66))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_4.2.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.TapeCopy.start_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.TapeCopy.start s
    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
    (DecrAlmostLinearSSSP.Decremental.TapeCopy.startData s) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_4.2.2.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.TapeCopy.start_values : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (B bank n k : Nat),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))) B →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))))
          (DecrAlmostLinearSSSP.Decremental.bankFactor bank) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 66) (instOfNatNat (nat_lit 66)))) n →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68)))) k →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 154) (instOfNatNat (nat_lit 154))))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (DecrAlmostLinearSSSP.Decremental.bankFactor bank) n) →
              And
                (@Eq.{1} Nat
                  ((DecrAlmostLinearSSSP.Decremental.TapeCopy.startData s).natReg
                    (@OfNat.ofNat.{0} Nat (nat_lit 162) (instOfNatNat (nat_lit 162))))
                  n)
                (And
                  (@Eq.{1} Nat
                    ((DecrAlmostLinearSSSP.Decremental.TapeCopy.startData s).natReg
                      (@OfNat.ofNat.{0} Nat (nat_lit 164) (instOfNatNat (nat_lit 164))))
                    (DecrAlmostLinearSSSP.Decremental.bankAddress B bank n))
                  (And
                    (@Eq.{1} Nat
                      ((DecrAlmostLinearSSSP.Decremental.TapeCopy.startData s).natReg
                        (@OfNat.ofNat.{0} Nat (nat_lit 170) (instOfNatNat (nat_lit 170))))
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                        (DecrAlmostLinearSSSP.Decremental.bankFactor bank)))
                    (@Eq.{1} Nat
                      ((DecrAlmostLinearSSSP.Decremental.TapeCopy.startData s).natReg
                        (@OfNat.ofNat.{0} Nat (nat_lit 166) (instOfNatNat (nat_lit 166))))
                      k))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_4.2.2.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.TapeCopy.start_nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 162) (instOfNatNat (nat_lit 162))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 164) (instOfNatNat (nat_lit 164))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 170) (instOfNatNat (nat_lit 170))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 166) (instOfNatNat (nat_lit 166))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.TapeCopy.start k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_4.2.2.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.TapeCopy.start_real_frame : ∀ (k : Nat), DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.TapeCopy.start k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_4.2.2.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.TapeCopy.tailFrame_start : DecrAlmostLinearSSSP.Decremental.TailFrame DecrAlmostLinearSSSP.Decremental.TapeCopy.start := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_4.2.2.2.1.2.2.2
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
theorem DecrAlmostLinearSSSP.Decremental.SourceSnapshot.guest_bank_protected : ∀ (B bank record a : Nat),
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
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_5.2.1.2.2.1.1
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
theorem DecrAlmostLinearSSSP.Decremental.CacheCopy.setup_nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 128) (instOfNatNat (nat_lit 128))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 132) (instOfNatNat (nat_lit 132))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 170) (instOfNatNat (nat_lit 170))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 176) (instOfNatNat (nat_lit 176))) →
            DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CacheCopy.setup k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_5.2.2.2.1.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.CacheCopy.setup_real_frame : ∀ (k : Nat), DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CacheCopy.setup k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_5.2.2.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.CacheCopy.call_source : ∀ (B bank cacheOffset count : Nat) (delta : Real) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data)
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
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_5.2.2.2.2.1.2
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
lemma globalFrame_header : GlobalFrame RecordHeader.code := by
  constructor
  · intro k hk
    simp only [globalNat,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals apply RecordHeader.nat_frame <;> norm_num
  · intro k hk
    simp only [globalReal,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl
    all_goals apply RecordHeader.real_frame <;> norm_num
lemma globalFrame_snapshotFill (N : ℕ) : GlobalFrame (SnapshotFill.code N) := by
  constructor
  · intro k hk
    simp only [globalNat,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals apply SnapshotFill.nat_frame <;> norm_num
  · intro k hk
    simp only [globalReal,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl
    all_goals apply SnapshotFill.real_frame <;> norm_num
lemma globalFrame_prepare : GlobalFrame ScaleParameters.prepare := by
  constructor
  · intro k hk
    simp only [globalNat,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals apply ScaleParameters.prepare_nat_frame <;> norm_num
  · intro k hk
    simp only [globalReal,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl
    all_goals apply ScaleParameters.prepare_real_frame <;> norm_num
lemma globalFrame_fields : GlobalFrame ScaleParameters.writeFields := by
  constructor
  · intro k hk
    simp only [globalNat,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals apply ScaleParameters.fields_nat_frame <;> norm_num
  · intro k hk
    simp only [globalReal,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl
    all_goals apply ScaleParameters.fields_real_frame <;> norm_num
lemma globalFrame_initializeSnapshot (N : ℕ) : GlobalFrame (ScaleParameters.initializeSnapshot N) :=
  (globalFrame_snapshotFill N).seq (globalFrame_prepare.seq globalFrame_fields)
lemma globalFrame_tapeStart : GlobalFrame TapeCopy.start := by
  constructor
  · intro k hk
    simp only [globalNat,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals apply TapeCopy.start_nat_frame <;> norm_num
  · intro k hk
    exact TapeCopy.start_real_frame k
lemma globalFrame_naturalField : GlobalFrame TapeCopy.naturalField := by
  constructor
  · intro k hk
    simp only [globalNat,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals apply TapeCopy.naturalField_nat_frame <;> norm_num
  · intro k hk
    simp only [globalReal,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl
    all_goals apply TapeCopy.naturalField_real_frame <;> norm_num
lemma globalFrame_weightField : GlobalFrame TapeCopy.weightField := by
  constructor
  · intro k hk
    simp only [globalNat,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals apply TapeCopy.weightField_nat_frame <;> norm_num
  · intro k hk
    simp only [globalReal,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl
    all_goals apply TapeCopy.weightField_real_frame <;> norm_num
lemma globalFrame_tapeEdge : GlobalFrame TapeCopy.edge := by
  have hd : GlobalFrame (nsub 166 166 26) := by
    constructor
    · intro k hk
      simp only [globalNat,List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        norm_num [NatFrame,nsub,writesNat]
    · intro k hk
      simp [RealFrame,nsub,writesReal]
  exact globalFrame_naturalField.seq (globalFrame_naturalField.seq (globalFrame_weightField.seq hd))
lemma globalFrame_tapeLoop : GlobalFrame TapeCopy.code := globalFrame_tapeEdge.loop _
lemma globalFrame_sourceCall (N entry : ℕ) (p : Program) : GlobalFrame (SourceCall.code N entry p) := by
  constructor
  · intro k hk
    simp only [globalNat,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals apply SourceCall.nat_even_frame <;> norm_num
  · intro k hk
    simp only [globalReal,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl
    all_goals apply SourceCall.real_even_frame <;> norm_num
end DecrAlmostLinearSSSP.Decremental.Native
end s134
section s135
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Prepass
open Structured ScaledCeiling
lemma code_vertex_stride {s t : Data} {coefficient stride cost : ℕ} (he : Eval (code coefficient stride) s cost t) :
    t.natReg 100 = 2*s.natReg 66 := by
  unfold code at he
  cases he with
  | seq hreserve hrest =>
    cases hrest with
    | seq hcount hrest =>
      cases hrest with
      | seq harea hlayout =>
        have hr := hreserve.nat_frame (reserve_nat_frame coefficient 66 (by omega) (by decide) (by omega) (by omega))
        have hc := hcount.nat_frame (count_nat_frame 66 (by omega) (by decide) (by omega) (by omega))
        have ha := harea.nat_frame (area_nat_frame 66 (by omega) (by decide) (by omega) (by omega))
        exact (Layout.code_vertex_stride hlayout).trans (congrArg (fun n : ℕ => 2*n) (ha.trans (hc.trans hr)))
lemma globals_after {s t : Data} {i : Input} {coefficient stride cost : ℕ}
    (hc : InputCapture.Captured i s) (he : Eval (code coefficient stride) s cost t)
    (hrep : Layout.Represents t (Layout.addresses (i.n+3*i.k+2) i.n (scaleCount i) (coefficient*i.size^3+1) stride)) :
    Native.Globals i (i.n+3*i.k+2)
      (Layout.addresses (i.n+3*i.k+2) i.n (scaleCount i) (coefficient*i.size^3+1) stride).utility t := by
  have hn (k : ℕ) (hk : 10 ≤ k) (hk' : k < 84) (hev : Even k) (h48 : k ≠ 48)
      (h58 : k ≠ 58) (h60 : k ≠ 60) (h80 : k ≠ 80) (h82 : k ≠ 82) : t.natReg k = s.natReg k :=
    he.nat_frame (nat_frame coefficient stride k hk hk' hev h48 h58 h60 h80 h82)
  have hr (k : ℕ) (hk : 10 ≤ k) (hev : Even k) (h58 : k ≠ 58) (h80 : k ≠ 80) (h82 : k ≠ 82) (h84 : k ≠ 84) :
      t.realReg k = s.realReg k := he.real_frame (real_frame coefficient stride k hk hev h58 h80 h82 h84)
  constructor
  · exact (hn 56 (by omega) (by omega) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hc.zeroN
  · exact (hr 56 (by omega) (by decide) (by omega) (by omega) (by omega) (by omega)).trans hc.zeroR
  · exact (hn 26 (by omega) (by omega) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hc.unit
  · exact (hn 14 (by omega) (by omega) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hc.two
  · exact (hn 34 (by omega) (by omega) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hc.scanZero
  · exact (hn 36 (by omega) (by omega) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hc.scanUnit
  · exact (hn 64 (by omega) (by omega) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hc.size
  · exact (hn 66 (by omega) (by omega) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hc.vertices
  · exact (hn 68 (by omega) (by omega) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hc.edges
  · exact (hn 70 (by omega) (by omega) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hc.weightBound
  · exact (hn 72 (by omega) (by omega) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hc.source
  · exact (hr 64 (by omega) (by decide) (by omega) (by omega) (by omega) (by omega)).trans hc.accuracy
  · exact (hn 74 (by omega) (by omega) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hc.base
  · exact hrep.2.2.2.2.2.2
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
lemma BankFrame.seq {a b : Cmd} (ha : BankFrame a) (hb : BankFrame b) : BankFrame (.seq a b) :=
  ⟨fun k hk => ⟨ha.1 k hk,hb.1 k hk⟩,ha.2,hb.2⟩
lemma BankFrame.loop (test : Test) {body : Cmd} (h : BankFrame body) : BankFrame (.loop test body) := h
lemma BankEnv.transfer {j record cache stride cost : ℕ} {cmd : Cmd} {s t : Data}
    (h : BankEnv j record cache stride s) (he : Eval cmd s cost t) (hf : BankFrame cmd) : BankEnv j record cache stride t := by
  have hn (k : ℕ) (hk : k ∈ bankNat) : t.natReg k = s.natReg k := he.nat_frame (hf.1 k hk)
  have hr : t.realReg 146 = s.realReg 146 := he.real_frame hf.2
  rcases h with ⟨_,_,_,_,_,_⟩
  constructor
  all_goals first | (rw [hn _ (by decide)];assumption) | (rw [hr];assumption)
lemma bankFrame_header : BankFrame RecordHeader.code := by
  constructor
  · intro k hk
    simp only [bankNat,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl
    all_goals apply RecordHeader.nat_frame <;> norm_num
  · apply RecordHeader.real_frame <;> norm_num
lemma bankFrame_snapshotFill (N : ℕ) : BankFrame (SnapshotFill.code N) := by
  constructor
  · intro k hk
    simp only [bankNat,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl
    all_goals apply SnapshotFill.nat_frame <;> norm_num
  · apply SnapshotFill.real_frame <;> norm_num
lemma bankFrame_prepare : BankFrame ScaleParameters.prepare := by
  constructor
  · intro k hk
    simp only [bankNat,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl
    all_goals apply ScaleParameters.prepare_nat_frame <;> norm_num
  · apply ScaleParameters.prepare_real_frame <;> norm_num
lemma bankFrame_fields : BankFrame ScaleParameters.writeFields := by
  constructor
  · intro k hk
    simp only [bankNat,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl
    all_goals apply ScaleParameters.fields_nat_frame <;> norm_num
  · apply ScaleParameters.fields_real_frame <;> norm_num
lemma bankFrame_tapeStart : BankFrame TapeCopy.start := by
  constructor
  · intro k hk
    simp only [bankNat,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl
    all_goals apply TapeCopy.start_nat_frame <;> norm_num
  · apply TapeCopy.start_real_frame <;> norm_num
lemma bankFrame_naturalField : BankFrame TapeCopy.naturalField := by
  constructor
  · intro k hk
    simp only [bankNat,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl
    all_goals apply TapeCopy.naturalField_nat_frame <;> norm_num
  · apply TapeCopy.naturalField_real_frame <;> norm_num
lemma bankFrame_weightField : BankFrame TapeCopy.weightField := by
  constructor
  · intro k hk
    simp only [bankNat,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl
    all_goals apply TapeCopy.weightField_nat_frame <;> norm_num
  · apply TapeCopy.weightField_real_frame <;> norm_num
lemma bankFrame_sourceCall (N entry : ℕ) (p : Program) : BankFrame (SourceCall.code N entry p) := by
  constructor
  · intro k hk
    simp only [bankNat,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl
    all_goals apply SourceCall.nat_even_frame <;> norm_num
  · apply SourceCall.real_even_frame <;> norm_num
lemma bankFrame_initializeSnapshot (N : ℕ) : BankFrame (ScaleParameters.initializeSnapshot N) :=
  (bankFrame_snapshotFill N).seq (bankFrame_prepare.seq bankFrame_fields)
lemma bankFrame_tapeEdge : BankFrame TapeCopy.edge := by
  have hd : BankFrame (nsub 166 166 26) := by
    constructor
    · intro k hk
      simp only [bankNat,List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> norm_num [NatFrame,nsub,writesNat]
    · simp [RealFrame,nsub,writesReal]
  exact bankFrame_naturalField.seq (bankFrame_naturalField.seq (bankFrame_weightField.seq hd))
lemma bankFrame_tapeLoop : BankFrame TapeCopy.code := bankFrame_tapeEdge.loop _
end DecrAlmostLinearSSSP.Decremental.Native
end s137
section s138
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
lemma header_ready (i : Input) (j B utility record cache stride N : ℕ) (s : Data)
    (hg : Globals i B utility s) (hb : BankEnv j record cache stride s)
    (hrecord : ∃ r, record = B+2*r+1) (hN : 8 ≤ N)
    (himage : SourceMemory.Image B j s (fun _ => 0) (fun _ => 0))
    (raw : ℕ → ℕ) (hprefix : ∀ address, address ≤ B → s.natMem address = raw address)
    (htail : ∀ r, N ≤ r → s.natReg (shadowReg r) = 0 ∧ s.realReg (shadowReg r) = 0) :
    ∃ t, Eval RecordHeader.code s 19 t ∧ Ready i j B utility record cache stride t ∧
      SourceMemory.Image B j t (fun _ => 0) (fun _ => 0) ∧
      (∀ address, address ≤ B → t.natMem address = raw address) ∧
      (∀ r, N ≤ r → t.natReg (shadowReg r) = 0 ∧ t.realReg (shadowReg r) = 0) ∧
      (∀ address, address ≠ record → address ≠ record+2 → address ≠ record+4 → address ≠ record+6 →
        t.natMem address = s.natMem address ∧ t.realMem address = s.realMem address) := by
  let t := RecordHeader.result s
  have he := RecordHeader.eval_code s
  have hgt : Globals i B utility t := hg.transfer he globalFrame_header
  have hbt : BankEnv j record cache stride t := hb.transfer he bankFrame_header
  obtain ⟨_,_,_,hwork,_,_,h50,h148,h70⟩ := RecordHeader.values s hg.zeroN hg.two
  have ht50 : t.natReg 50 = record+8 := by simpa only [hb.record] using h50
  have ht148 : t.realReg 148 = 2*scale j := by simpa only [hb.scale] using h148
  have ht70 : t.realReg 70 = delta i j := by simpa only [delta,hg.accuracy,hb.scale,hg.vertices] using h70
  have htwork : t.natMem (record+6) = 0 := by simpa only [hb.record] using hwork
  have hframe (address : ℕ) (h0 : address ≠ record) (h2 : address ≠ record+2)
      (h4 : address ≠ record+4) (h6 : address ≠ record+6) :
      t.natMem address = s.natMem address ∧ t.realMem address = s.realMem address :=
    RecordHeader.memory_frame s hg.zeroN hg.two address (by simpa only [hb.record] using h0)
      (by simpa only [hb.record] using h2) (by simpa only [hb.record] using h4) (by simpa only [hb.record] using h6)
  obtain ⟨r,hr⟩ := hrecord
  have hbank (a offset : ℕ) (hoff : Even offset) : bankAddress B j a ≠ record+offset := by
    obtain ⟨q,hq⟩ := hoff
    have heq : record+offset = B+(2*(r+q)+1) := by rw [hr,hq];ring
    rw [heq]
    exact guest_bank_ne_host B j a (r+q)
  have htimage : SourceMemory.Image B j t (fun _ => 0) (fun _ => 0) := himage.frame (fun a =>
    hframe _ (by simpa using hbank a 0 (by decide)) (hbank a 2 (by decide)) (hbank a 4 (by decide)) (hbank a 6 (by decide)))
  refine ⟨t,he,⟨hgt,hbt,ht50,ht70,ht148,htwork⟩,htimage,?_,?_,hframe⟩
  · intro address ha
    have hh := hframe address (by omega) (by omega) (by omega) (by omega)
    exact hh.1.trans (hprefix address ha)
  · exact tailFrame_recordHeader.preserves he hN htail
end DecrAlmostLinearSSSP.Decremental.Native
end s138
section s139
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
lemma snapshot_extra_real_frame (N k : ℕ) (hk : 10 ≤ k) (hev : Even k)
    (h116 : k ≠ 116) (h58 : k ≠ 58) (h200 : k ≠ 200) (h202 : k ≠ 202)
    (h204 : k ≠ 204) (h208 : k ≠ 208) : RealFrame (ScaleParameters.initializeSnapshot N) k :=
  ⟨SnapshotFill.real_frame N k h116,ScaleParameters.prepare_real_frame k hk hev h58 h200 h202 h204,
    ScaleParameters.fields_real_frame k h208⟩
lemma snapshot_ready (i : Input) (hi : i.Valid) (p : Program)
    (heps : 1/(i.size : ℝ) < i.accuracy) (j B utility record cache stride N : ℕ) (s : Data)
    (hready : Ready i j B utility record cache stride s) (hN : 8 ≤ N)
    (hrecord : ∃ r, record = B+2*r+1) (hutility : ∃ u, utility = B+2*u)
    (hbefore : ∀ r < N, record+8+2*r < utility)
    (himage : SourceMemory.Image B j s (fun _ => 0) (fun _ => 0))
    (raw : ℕ → ℕ) (hprefix : ∀ address, address ≤ B → s.natMem address = raw address)
    (htail : ∀ r, N ≤ r → s.natReg (shadowReg r) = 0 ∧ s.realReg (shadowReg r) = 0) :
    ∃ cost t, Eval (ScaleParameters.initializeSnapshot N) s cost t ∧
      cost ≤ 6*N+5*((dispatchCharge ScaledCeiling.ceilingProgram.code+3)*(16*utilityDepth i.size+32))+109 ∧
      Ready i j B utility record cache stride t ∧ SourceMemory.Image B j t (fun _ => 0) (fun _ => 0) ∧
      t.natReg 154 = bankFactor j*i.n ∧ t.natReg 152 = bankFactor j*barrierHigh i ∧
      (∀ r < N, t.natMem (record+8+2*r) = bankFactor j*(initialMachine p (barrierInput i j)).natReg r ∧
        t.realMem (record+8+2*r) = (initialMachine p (barrierInput i j)).realReg r) ∧
      (∀ address, address ≤ B → t.natMem address = raw address) ∧
      (∀ r, N ≤ r → t.natReg (shadowReg r) = 0 ∧ t.realReg (shadowReg r) = 0) ∧
      (∀ address, (∀ r < N, address ≠ record+8+2*r) →
        (∀ a, address ≠ utility+2*a+1) →
        t.natMem address = s.natMem address ∧ t.realMem address = s.realMem address) := by
  have hg := hready.globals
  have hb := hready.bank
  have hF : s.natReg 112 = bankFactor (s.natReg 110) := by rw [hb.index];exact hb.factor
  obtain ⟨cost,t,he,hcost,ht50,htFn,htHigh,htsaved,htframe⟩ := ScaleParameters.initializeSnapshot_eval N s p i hi heps
    (by omega) hg.size hg.vertices hg.edges hg.source hg.accuracy hF hg.zeroN hg.zeroR hg.two hg.unit
    (by simpa only [hready.savebase,hg.utilityBase] using hbefore)
  have hgt := hg.transfer he (globalFrame_initializeSnapshot N)
  have hbt := hb.transfer he (bankFrame_initializeSnapshot N)
  have h50 : t.natReg 50 = record+8 := ht50.trans hready.savebase
  have hf : ∀ address, (∀ r < N, address ≠ record+8+2*r) → (∀ a, address ≠ utility+2*a+1) →
      t.natMem address = s.natMem address ∧ t.realMem address = s.realMem address := by
    simpa only [hready.savebase,hg.utilityBase] using htframe
  have hwork : t.natMem (record+6) = 0 := by
    have hh := hf (record+6) (by intro r hr;omega) (by intro a;have h0 := hbefore 0 (by omega);omega)
    exact hh.1.trans hready.work
  have hd : t.realReg 70 = delta i j := (he.real_frame (snapshot_extra_real_frame N 70 (by omega) (by decide)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))).trans hready.delta
  have hcut : t.realReg 148 = 2*scale j := (he.real_frame (snapshot_extra_real_frame N 148 (by omega) (by decide)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))).trans hready.cutoff
  obtain ⟨r,hr⟩ := hrecord
  obtain ⟨u,hu⟩ := hutility
  have himg : SourceMemory.Image B j t (fun _ => 0) (fun _ => 0) := himage.frame (by
    intro a
    apply hf
    · have hh := (SourceSnapshot.guest_bank_protected B j record a ⟨r,hr⟩).2
      intro v hv
      exact hh v
    · rw [hu]
      exact ScaledCeiling.guest_bank_outside_utility_tail B j u a)
  refine ⟨cost,t,he,hcost,⟨hgt,hbt,h50,hd,hcut,hwork⟩,himg,?_,?_,?_,?_,?_,hf⟩
  · simpa only [hb.index] using htFn
  · simpa only [hb.index] using htHigh
  · intro r hr'
    simpa only [h50,hb.index] using htsaved r hr'
  · intro address ha
    have hh := hf address (by intro v hv;omega) (by intro a;rw [hu];omega)
    exact hh.1.trans (hprefix address ha)
  · exact (tailFrame_initializeSnapshot N).preserves he hN htail
end DecrAlmostLinearSSSP.Decremental.Native
end s139
section s140
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.TapeCopy
lemma edgeImage_outside (raw : ℕ → ℕ) (delta cutoff : ℝ) (high : ℕ)
    (natural : ℕ → ℕ) (origin logical address : ℕ)
    (h0 : address ≠ logical) (h1 : address ≠ logical+1) (h2 : address ≠ logical+2) :
    edgeImage raw delta cutoff high natural origin logical address = natural address := by
  simp only [edgeImage,Function.update_of_ne h2,Function.update_of_ne h1,Function.update_of_ne h0]
lemma tapeImage_outside (raw : ℕ → ℕ) (delta cutoff : ℝ) (high count : ℕ)
    (natural : ℕ → ℕ) (origin logical address : ℕ)
    (hout : address < logical ∨ logical+3*count ≤ address) :
    tapeImage raw delta cutoff high count natural origin logical address = natural address := by
  induction count generalizing natural origin logical with
  | zero => rfl
  | succ count ih =>
    rw [tapeImage,ih _ (origin+3) (logical+3) (by omega)]
    exact edgeImage_outside _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega)
lemma tapeImage_fields (raw : ℕ → ℕ) (delta cutoff : ℝ) (high count : ℕ)
    (natural : ℕ → ℕ) (origin logical : ℕ) :
    ∀ j < count,
      tapeImage raw delta cutoff high count natural origin logical (logical+3*j) = raw (origin+3*j) ∧
      tapeImage raw delta cutoff high count natural origin logical (logical+3*j+1) = raw (origin+3*j+1) ∧
      tapeImage raw delta cutoff high count natural origin logical (logical+3*j+2) = roundedWeight delta cutoff high (raw (origin+3*j+2)) := by
  induction count generalizing natural origin logical with
  | zero => simp
  | succ count ih =>
    intro j hj
    by_cases hj0 : j = 0
    · subst j
      simp only [Nat.mul_zero,Nat.add_zero,tapeImage]
      have h0 := tapeImage_outside raw delta cutoff high count (edgeImage raw delta cutoff high natural origin logical) (origin+3) (logical+3) logical (Or.inl (by omega))
      have h1 := tapeImage_outside raw delta cutoff high count (edgeImage raw delta cutoff high natural origin logical) (origin+3) (logical+3) (logical+1) (Or.inl (by omega))
      have h2 := tapeImage_outside raw delta cutoff high count (edgeImage raw delta cutoff high natural origin logical) (origin+3) (logical+3) (logical+2) (Or.inl (by omega))
      rw [h0,h1,h2]
      simp [edgeImage]
    · obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
      have hk : k < count := by omega
      have hh := ih (edgeImage raw delta cutoff high natural origin logical) (origin+3) (logical+3) k hk
      have heq0 : logical+3+3*k = logical+3*(k+1) := by omega
      have heq1 : origin+3+3*k = origin+3*(k+1) := by omega
      simpa only [tapeImage,heq0,heq1] using hh
end DecrAlmostLinearSSSP.Decremental.TapeCopy
end s140
section s141
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.TapeCopy
lemma roundedWeight_barrier (i : Input) (j : ℕ) (e : Fin i.k) :
    roundedWeight (delta i j) (2*scale j) (barrierHigh i) (i.weight e) = barrierWeight i j e := by
  unfold roundedWeight barrierWeight
  by_cases hc : (i.weight e : ℝ) ≤ 2*scale j
  · simp [hc,not_lt_of_ge hc]
  · simp [hc,lt_of_not_ge hc]
lemma tapeImage_barrier (p : Program) (i : Input) (j : ℕ) :
    tapeImage (initialMachine p i).natMem (delta i j) (2*scale j) (barrierHigh i) i.k
      (fun _ => 0) i.n i.n = (initialMachine p (barrierInput i j)).natMem := by
  funext address
  by_cases htape : i.n ≤ address ∧ (address-i.n)/3 < i.k
  · let e : Fin i.k := ⟨(address-i.n)/3,htape.2⟩
    let offset := (address-i.n)%3
    have hoffset : offset < 3 := Nat.mod_lt _ (by omega)
    have haddress : address = i.n+3*e.val+offset := by dsimp [e,offset];omega
    rw [haddress]
    have hfields := tapeImage_fields (initialMachine p i).natMem (delta i j) (2*scale j)
      (barrierHigh i) i.k (fun _ => 0) i.n i.n e.val e.isLt
    have hright := initial_nat_tape p (barrierInput i j) e offset hoffset
    change (initialMachine p (barrierInput i j)).natMem (i.n+3*e.val+offset) =
      (if offset = 0 then (i.graph.tail e).val else if offset = 1 then (i.graph.head e).val else barrierWeight i j e) at hright
    rw [hright]
    have hraw0 : (initialMachine p i).natMem (i.n+3*e.val) = (i.graph.tail e).val := by
      simpa using initial_nat_tape p i e 0 (by omega)
    have hraw1 : (initialMachine p i).natMem (i.n+3*e.val+1) = (i.graph.head e).val := by
      simpa using initial_nat_tape p i e 1 (by omega)
    have hraw2 : (initialMachine p i).natMem (i.n+3*e.val+2) = i.weight e := by
      simpa using initial_nat_tape p i e 2 (by omega)
    have hoffcases : offset = 0 ∨ offset = 1 ∨ offset = 2 := by omega
    rcases hoffcases with ho | ho | ho
    · simpa only [ho,Nat.add_zero,ite_true] using hfields.1.trans hraw0
    · simpa only [ho,show (1 : ℕ) ≠ 0 by omega,ite_false,ite_true] using hfields.2.1.trans hraw1
    · simpa only [ho,show (2 : ℕ) ≠ 0 by omega,show (2 : ℕ) ≠ 1 by omega,ite_false,hraw2,roundedWeight_barrier] using hfields.2.2
  · have hout : address < i.n ∨ i.n+3*i.k ≤ address := by omega
    rw [tapeImage_outside _ _ _ _ _ _ _ _ _ hout]
    change 0 = (initialMachine p (barrierInput i j)).natMem address
    simp [initialMachine,barrierInput,htape]
end DecrAlmostLinearSSSP.Decremental.TapeCopy
end s141
section s142
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.TapeCopy
open Structured
lemma ordinary_argument_bound (i : Input) (hi : i.Valid) (x : ℕ) (hx : x ≤ i.size) :
    (x : ℝ) ≤ (2 : ℝ)^utilityDepth i.size := by
  have hm : 1 ≤ i.size := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (lt_of_lt_of_le (input_vertex_positive i) hi.1))
  have hx' : x ≤ 512*i.size^2 := by nlinarith
  exact (show (x : ℝ) ≤ 512*(i.size : ℝ)^2 by exact_mod_cast hx').trans (utilityDepth_power i.size)
lemma low_weight_argument_bound (i : Input) (hi : i.Valid) (heps : 1/(i.size : ℝ) < i.accuracy)
    (j : ℕ) (w : ℝ) (hcut : w ≤ 2*scale j) : w/delta i j ≤ (2 : ℝ)^utilityDepth i.size := by
  have hd := delta_positive i hi j
  have hsmall := div_le_div_of_nonneg_right hcut hd.le
  have he := hi.2.2.2.1
  have hs := scale_positive j
  have hn : (0 : ℝ) < i.n := by exact_mod_cast input_vertex_positive i
  have hratio : (2*scale j)/delta i j = 256*(i.n : ℝ)/i.accuracy := by
    dsimp [delta]
    field_simp
    <;> ring
  rw [hratio] at hsmall
  have hmid : 256*(i.n : ℝ)/i.accuracy ≤ 512*(i.n : ℝ)/i.accuracy := by
    exact div_le_div_of_nonneg_right (by nlinarith) he.le
  exact hsmall.trans (hmid.trans (normal_barrier_argument_bound i hi heps).2)
lemma barrier_eval (s : Data) (p : Program) (i : Input) (hi : i.Valid)
    (heps : 1/(i.size : ℝ) < i.accuracy) (j B bank tail : ℕ)
    (henv : Env B bank tail (barrierHigh i) (delta i j) (2*scale j) s)
    (himage : SourceMemory.Image B bank s (fun _ => 0) (fun _ => 0))
    (hsource : s.natReg 162 = i.n) (hdest : s.natReg 164 = bankAddress B bank i.n)
    (hcount : s.natReg 166 = i.k) (htape : i.n+3*i.k ≤ B)
    (hprefix : ∀ address, address ≤ B → s.natMem address = (initialMachine p i).natMem address) :
    ∃ cost t, Eval code s cost t ∧
      cost ≤ i.k*(3*((dispatchCharge ScaledCeiling.ceilingProgram.code+3)*(16*utilityDepth i.size+32))+30)+2 ∧
      SourceMemory.Image B bank t (initialMachine p (barrierInput i j)).natMem
        (initialMachine p (barrierInput i j)).realMem ∧
      Env B bank tail (barrierHigh i) (delta i j) (2*scale j) t ∧
      t.natReg 162 = i.n+3*i.k ∧ t.natReg 164 = bankAddress B bank (i.n+3*i.k) ∧ t.natReg 166 = 0 ∧
      (∀ address, address ≤ B → t.natMem address = (initialMachine p i).natMem address) ∧
      (∀ address, (∀ a < 3*i.k, address ≠ bankAddress B bank (i.n+a)) →
        (∀ a, address ≠ s.natReg 48+2*a+1) →
        t.natMem address = s.natMem address ∧ t.realMem address = s.realMem address) := by
  have htail : ∀ e < i.k, ((initialMachine p i).natMem (i.n+3*e) : ℝ) ≤ (2 : ℝ)^utilityDepth i.size := by
    intro e he
    have ht : (initialMachine p i).natMem (i.n+3*e) = (i.graph.tail ⟨e,he⟩).val := by
      simpa using initial_nat_tape p i ⟨e,he⟩ 0 (by omega)
    rw [ht]
    apply ordinary_argument_bound i hi
    have hh := (i.graph.tail ⟨e,he⟩).isLt
    have hn := hi.1
    omega
  have hhead : ∀ e < i.k, ((initialMachine p i).natMem (i.n+3*e+1) : ℝ) ≤ (2 : ℝ)^utilityDepth i.size := by
    intro e he
    have ht : (initialMachine p i).natMem (i.n+3*e+1) = (i.graph.head ⟨e,he⟩).val := by
      simpa using initial_nat_tape p i ⟨e,he⟩ 1 (by omega)
    rw [ht]
    apply ordinary_argument_bound i hi
    have hh := (i.graph.head ⟨e,he⟩).isLt
    have hn := hi.1
    omega
  have hweight : ∀ e < i.k, ((initialMachine p i).natMem (i.n+3*e+2) : ℝ) ≤ 2*scale j →
      ((initialMachine p i).natMem (i.n+3*e+2) : ℝ)/delta i j ≤ (2 : ℝ)^utilityDepth i.size := by
    intro e he hc
    exact low_weight_argument_bound i hi heps j _ hc
  obtain ⟨cost,t,he,hcost,himg,htenv,h162,h164,h166,hpref,hframe⟩ := eval_code s i.k (utilityDepth i.size)
    B bank tail i.n i.n (barrierHigh i) (delta i j) (2*scale j) (initialMachine p i).natMem
    (fun _ => 0) (fun _ => 0) henv himage hsource hdest hcount htape (delta_positive i hi j)
    hprefix htail hhead hweight
  rw [tapeImage_barrier] at himg
  exact ⟨cost,t,he,hcost,himg,htenv,h162,h164,h166,hpref,hframe⟩
end DecrAlmostLinearSSSP.Decremental.TapeCopy
end s142
section s143
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.TapeCopy
open Structured
lemma ConstantFrame.seq {a b : Cmd} (ha : ConstantFrame a) (hb : ConstantFrame b) : ConstantFrame (.seq a b) :=
  ⟨fun k hk => ⟨ha.1 k hk,hb.1 k hk⟩,fun k hk => ⟨ha.2 k hk,hb.2 k hk⟩⟩
lemma constantFrame_start : ConstantFrame start := by
  constructor
  · intro k hk
    simp only [constantsNat,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl
    all_goals apply start_nat_frame <;> norm_num
  · intro k hk
    exact start_real_frame k
lemma constantFrame_natural : ConstantFrame naturalField := by
  constructor
  · intro k hk
    simp only [constantsNat,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl
    all_goals apply naturalField_nat_frame <;> norm_num
  · intro k hk
    simp only [constantsReal,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl
    all_goals apply naturalField_real_frame <;> norm_num
lemma constantFrame_weight : ConstantFrame weightField := by
  constructor
  · intro k hk
    simp only [constantsNat,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl
    all_goals apply weightField_nat_frame <;> norm_num
  · intro k hk
    simp only [constantsReal,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl
    all_goals apply weightField_real_frame <;> norm_num
lemma constantFrame_edge : ConstantFrame edge := by
  have hd : ConstantFrame (nsub 166 166 26) := by
    constructor
    · intro k hk
      simp only [constantsNat,List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl <;> norm_num [NatFrame,nsub,writesNat]
    · intro k hk
      simp [RealFrame,nsub,writesReal]
  exact constantFrame_natural.seq (constantFrame_natural.seq (constantFrame_weight.seq hd))
lemma constantFrame_loop : ConstantFrame code := constantFrame_edge
end DecrAlmostLinearSSSP.Decremental.TapeCopy
end s143
section s144
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
lemma tailFrame_skip : TailFrame Cmd.skip := fun _ _ => ⟨trivial,trivial⟩
lemma tailFrame_tapeFinish : TailFrame (Structured.sequence [storeN 164 174,nadd 162 162 26,nadd 164 164 170]) :=
  (tailFrame_atom ⟨.storeN 164 174,trivial⟩ trivial).seq
    ((tailFrame_atom ⟨.nadd 162 162 26,trivial⟩ (by norm_num [EvenRegisterWrites])).seq
      ((tailFrame_atom ⟨.nadd 164 164 170,trivial⟩ (by norm_num [EvenRegisterWrites])).seq tailFrame_skip))
lemma tailFrame_naturalField : TailFrame TapeCopy.naturalField :=
  (tailFrame_atom ⟨.loadN 172 162,trivial⟩ (by norm_num [EvenRegisterWrites])).seq
    ((tailFrame_productNat 174 112 172 (by norm_num [EvenRegisterWrites])).seq tailFrame_tapeFinish)
lemma tailFrame_weightChoice : TailFrame TapeCopy.chooseWeight :=
  (tailFrame_atom ⟨.nadd 174 152 56,trivial⟩ (by norm_num [EvenRegisterWrites])).branch _
    ((tailFrame_atom ⟨.div 202 202 70,trivial⟩ (by norm_num [EvenRegisterWrites])).seq (tailFrame_productReal 174 112 202 (by norm_num [EvenRegisterWrites])))
lemma tailFrame_weightField : TailFrame TapeCopy.weightField :=
  (tailFrame_atom ⟨.loadN 172 162,trivial⟩ (by norm_num [EvenRegisterWrites])).seq
    ((tailFrame_atom ⟨.cast 202 172,trivial⟩ (by norm_num [EvenRegisterWrites])).seq
      (tailFrame_weightChoice.seq tailFrame_tapeFinish))
lemma tailFrame_tapeEdge : TailFrame TapeCopy.edge :=
  tailFrame_naturalField.seq (tailFrame_naturalField.seq (tailFrame_weightField.seq
    (tailFrame_atom ⟨.nsub 166 166 26,trivial⟩ (by norm_num [EvenRegisterWrites]))))
lemma tailFrame_tapeLoop : TailFrame TapeCopy.code := tailFrame_tapeEdge.loop _
end DecrAlmostLinearSSSP.Decremental
end s144
section s145
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
lemma host_record_ne_bank (B bank record offset : ℕ) (hr : ∃ r, record = B+2*r+1) (ho : Even offset) :
    ∀ a, record+offset ≠ bankAddress B bank a := by
  obtain ⟨r,rfl⟩ := hr
  obtain ⟨q,rfl⟩ := ho
  intro a
  have heq : B+2*r+1+(q+q) = B+(2*(r+q)+1) := by ring
  rw [heq]
  exact Ne.symm (guest_bank_ne_host B bank a (r+q))
lemma tape_ready (i : Input) (hi : i.Valid) (p : Program)
    (heps : 1/(i.size : ℝ) < i.accuracy) (j B utility record cache stride N : ℕ) (s : Data)
    (hready : Ready i j B utility record cache stride s) (hN : 8 ≤ N)
    (hrecord : ∃ r, record = B+2*r+1) (hutility : ∃ u, utility = B+2*u)
    (hbefore : ∀ r < N, record+8+2*r < utility) (hB : i.n+3*i.k ≤ B)
    (hFn : s.natReg 154 = bankFactor j*i.n) (hHigh : s.natReg 152 = bankFactor j*barrierHigh i)
    (himage : SourceMemory.Image B j s (fun _ => 0) (fun _ => 0))
    (hsaved : ∀ r < N, s.natMem (record+8+2*r) = bankFactor j*(initialMachine p (barrierInput i j)).natReg r ∧
      s.realMem (record+8+2*r) = (initialMachine p (barrierInput i j)).realReg r)
    (hprefix : ∀ address, address ≤ B → s.natMem address = (initialMachine p i).natMem address)
    (htail : ∀ r, N ≤ r → s.natReg (shadowReg r) = 0 ∧ s.realReg (shadowReg r) = 0) :
    ∃ cost t, Eval prepareTape s cost t ∧
      cost ≤ i.k*(3*((dispatchCharge ScaledCeiling.ceilingProgram.code+3)*(16*utilityDepth i.size+32))+30)+8 ∧
      Ready i j B utility record cache stride t ∧
      SourceMemory.Image B j t (initialMachine p (barrierInput i j)).natMem (initialMachine p (barrierInput i j)).realMem ∧
      (∀ r < N, t.natMem (record+8+2*r) = bankFactor j*(initialMachine p (barrierInput i j)).natReg r ∧
        t.realMem (record+8+2*r) = (initialMachine p (barrierInput i j)).realReg r) ∧
      (∀ address, address ≤ B → t.natMem address = (initialMachine p i).natMem address) ∧
      (∀ r, N ≤ r → t.natReg (shadowReg r) = 0 ∧ t.realReg (shadowReg r) = 0) ∧
      (∀ address, (∀ a < 3*i.k, address ≠ bankAddress B j (i.n+a)) →
        (∀ a, address ≠ utility+2*a+1) →
        t.natMem address = s.natMem address ∧ t.realMem address = s.realMem address) := by
  let a := TapeCopy.startData s
  have ha := TapeCopy.start_eval s
  have hg := hready.globals
  have hb := hready.bank
  have hag : Globals i B utility a := hg.transfer ha globalFrame_tapeStart
  have hab : BankEnv j record cache stride a := hb.transfer ha bankFrame_tapeStart
  have haimage : SourceMemory.Image B j a (fun _ => 0) (fun _ => 0) := ⟨himage.natMem,himage.realMem⟩
  have haprefix : ∀ address, address ≤ B → a.natMem address = (initialMachine p i).natMem address := hprefix
  obtain ⟨hu,hutilityEq⟩ := hutility
  have haHigh : a.natReg 152 = bankFactor j*barrierHigh i :=
    (ha.nat_frame (TapeCopy.constantFrame_start.1 152 (by decide))).trans hHigh
  have hadelta : a.realReg 70 = delta i j := (ha.real_frame (TapeCopy.start_real_frame 70)).trans hready.delta
  have hacut : a.realReg 148 = 2*scale j := (ha.real_frame (TapeCopy.start_real_frame 148)).trans hready.cutoff
  obtain ⟨h162,h164,h170,h166⟩ := TapeCopy.start_values s B j i.n i.k hg.zeroN hg.base hb.factor hg.vertices hg.edges hFn
  have haenv : TapeCopy.Env B j hu (barrierHigh i) (delta i j) (2*scale j) a :=
    ⟨hag.utilityBase.trans hutilityEq,hab.factor,haHigh,h170,hag.unit,hag.zeroN,hag.zeroR,hadelta,hacut⟩
  obtain ⟨c,t,he,hcost,himg,_,_,_,_,htprefix,htframe⟩ := TapeCopy.barrier_eval a p i hi heps j B j hu
    haenv haimage h162 h164 h166 hB haprefix
  have hgt := hag.transfer he globalFrame_tapeLoop
  have hbt := hab.transfer he bankFrame_tapeLoop
  have ht50 : t.natReg 50 = record+8 :=
    (he.nat_frame (TapeCopy.constantFrame_loop.1 50 (by decide))).trans
      ((ha.nat_frame (TapeCopy.constantFrame_start.1 50 (by decide))).trans hready.savebase)
  have htdelta : t.realReg 70 = delta i j :=
    (he.real_frame (TapeCopy.constantFrame_loop.2 70 (by decide))).trans hadelta
  have htcut : t.realReg 148 = 2*scale j :=
    (he.real_frame (TapeCopy.constantFrame_loop.2 148 (by decide))).trans hacut
  have hmN : a.natMem = s.natMem := rfl
  have hmR : a.realMem = s.realMem := rfl
  have hf : ∀ address, (∀ v < 3*i.k, address ≠ bankAddress B j (i.n+v)) →
      (∀ v, address ≠ utility+2*v+1) →
      t.natMem address = s.natMem address ∧ t.realMem address = s.realMem address := by
    simpa only [hag.utilityBase,hmN,hmR] using htframe
  have hwork : t.natMem (record+6) = 0 := by
    have hh := hf (record+6) (by intro v hv;exact host_record_ne_bank B j record 6 hrecord (by decide) _)
      (by intro v;have h0 := hbefore 0 (by omega);omega)
    exact hh.1.trans hready.work
  refine ⟨6+c,t,Eval.seq ha he,by omega,⟨hgt,hbt,ht50,htdelta,htcut,hwork⟩,himg,?_,htprefix,?_,hf⟩
  · intro r hr
    have hhost : record+8+2*r = record+(8+2*r) := by omega
    have hh := hf (record+8+2*r) (by
      intro v hv
      rw [hhost]
      exact host_record_ne_bank B j record (8+2*r) hrecord (by exact ⟨4+r,by omega⟩) _)
      (by intro v;have hlt := hbefore r hr;omega)
    exact ⟨hh.1.trans (hsaved r hr).1,hh.2.trans (hsaved r hr).2⟩
  · have hazero := TapeCopy.tailFrame_start.preserves ha hN htail
    exact tailFrame_tapeLoop.preserves he hN hazero
end DecrAlmostLinearSSSP.Decremental.Native
end s145
section s146
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
lemma RecordImage.frame {i : Input} {j record cache next : ℕ} {s t : Data}
    (h : RecordImage i j record cache next s)
    (hf : ∀ offset ∈ ([0,2,4] : List ℕ), t.natMem (record+offset) = s.natMem (record+offset) ∧
      t.realMem (record+offset) = s.realMem (record+offset)) : RecordImage i j record cache next t := by
  have h0 := hf 0 (by simp)
  simp only [Nat.add_zero] at h0
  have h2 := hf 2 (by simp)
  have h4 := hf 4 (by simp)
  exact ⟨h0.1.trans h.cachebase,h2.1.trans h.next,h4.1.trans h.factor,h0.2.trans h.cutoff,h2.2.trans h.delta⟩
lemma recordImage_header {i : Input} {j B utility record cache stride cost : ℕ} {s t : Data}
    (hg : Globals i B utility s) (hb : BankEnv j record cache stride s)
    (he : Eval RecordHeader.code s cost t) : RecordImage i j record cache (record+stride) t := by
  obtain ⟨_,rfl⟩ := he.deterministic (RecordHeader.eval_code s)
  obtain ⟨hcache,hnext,hfactor,_,hcut,hdelta,_,_,_⟩ := RecordHeader.values s hg.zeroN hg.two
  refine ⟨?_,?_,?_,?_,?_⟩
  · simpa only [hb.record,hb.cache] using hcache
  · simpa only [hb.record,hb.stride] using hnext
  · simpa only [hb.record,hb.factor] using hfactor
  · simpa only [hb.record,hb.scale] using hcut
  · simpa only [hb.record,hg.accuracy,hb.scale,hg.vertices,delta] using hdelta
lemma RecordImage.snapshot_frame {i : Input} {j record cache next utility N : ℕ} {s t : Data}
    (h : RecordImage i j record cache next s) (hN : 0 < N)
    (hbefore : ∀ r < N, record+8+2*r < utility)
    (hf : ∀ address, (∀ r < N, address ≠ record+8+2*r) →
      (∀ a, address ≠ utility+2*a+1) →
      t.natMem address = s.natMem address ∧ t.realMem address = s.realMem address) : RecordImage i j record cache next t := by
  apply h.frame
  intro offset hoff
  have ho : offset ≤ 4 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hoff;omega
  apply hf
  · intro r hr;omega
  · intro a
    have hh := hbefore 0 hN
    omega
lemma RecordImage.tape_frame {i : Input} {j B record cache next utility N : ℕ} {s t : Data}
    (h : RecordImage i j record cache next s) (hN : 0 < N)
    (hrecord : ∃ r, record = B+2*r+1) (hbefore : ∀ r < N, record+8+2*r < utility)
    (hf : ∀ address, (∀ a < 3*i.k, address ≠ bankAddress B j (i.n+a)) →
      (∀ a, address ≠ utility+2*a+1) →
      t.natMem address = s.natMem address ∧ t.realMem address = s.realMem address) : RecordImage i j record cache next t := by
  apply h.frame
  intro offset hoff
  have ho : offset ≤ 4 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hoff;omega
  have heven : Even offset := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hoff
    rcases hoff with rfl | rfl | rfl <;> decide
  apply hf
  · intro a ha
    exact host_record_ne_bank B j record offset hrecord heven _
  · intro a
    have hh := hbefore 0 hN
    omega
end DecrAlmostLinearSSSP.Decremental.Native
end s146
section s147
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
lemma prepareBank_eval (i : Input) (hi : i.Valid) (p : Program) (heps : 1/(i.size : ℝ) < i.accuracy)
    (j B utility record cache stride N : ℕ) (s : Data)
    (hg : Globals i B utility s) (hb : BankEnv j record cache stride s) (hN : 8 ≤ N)
    (hrecord : ∃ r, record = B+2*r+1) (hutility : ∃ u, utility = B+2*u)
    (hbefore : ∀ r < N, record+8+2*r < utility) (hB : i.n+3*i.k ≤ B)
    (himage : SourceMemory.Image B j s (fun _ => 0) (fun _ => 0))
    (hprefix : ∀ address, address ≤ B → s.natMem address = (initialMachine p i).natMem address)
    (htail : ∀ r, N ≤ r → s.natReg (shadowReg r) = 0 ∧ s.realReg (shadowReg r) = 0) :
    ∃ cost t, Eval (prepareBank N) s cost t ∧
      cost ≤ 6*N+5*((dispatchCharge ScaledCeiling.ceilingProgram.code+3)*(16*utilityDepth i.size+32))+
        i.k*(3*((dispatchCharge ScaledCeiling.ceilingProgram.code+3)*(16*utilityDepth i.size+32))+30)+136 ∧
      Ready i j B utility record cache stride t ∧ RecordImage i j record cache (record+stride) t ∧
      SourceMemory.Image B j t (initialMachine p (barrierInput i j)).natMem (initialMachine p (barrierInput i j)).realMem ∧
      (∀ r < N, t.natMem (record+8+2*r) = bankFactor j*(initialMachine p (barrierInput i j)).natReg r ∧
        t.realMem (record+8+2*r) = (initialMachine p (barrierInput i j)).realReg r) ∧
      (∀ address, address ≤ B → t.natMem address = (initialMachine p i).natMem address) ∧
      (∀ r, N ≤ r → t.natReg (shadowReg r) = 0 ∧ t.realReg (shadowReg r) = 0) ∧
      (∀ address, (∀ r < N+4, address ≠ record+2*r) →
        (∀ v < 3*i.k, address ≠ bankAddress B j (i.n+v)) →
        (∀ a, address ≠ utility+2*a+1) →
        t.natMem address = s.natMem address ∧ t.realMem address = s.realMem address) := by
  obtain ⟨a,ha,haready,haimage,haprefix,hatail,haframe⟩ := header_ready i j B utility record cache stride N s
    hg hb hrecord hN himage (initialMachine p i).natMem hprefix htail
  have hameta := recordImage_header hg hb ha
  obtain ⟨cs,b,hs,hscost,hbready,hbimage,hFn,hHigh,hbsaved,hbprefix,hbtail,hbframe⟩ := snapshot_ready i hi p heps
    j B utility record cache stride N a haready hN hrecord hutility hbefore haimage
    (initialMachine p i).natMem haprefix hatail
  have hbmeta := hameta.snapshot_frame (by omega : 0 < N) hbefore hbframe
  obtain ⟨ct,t,ht,htcost,htready,htimage,htsaved,htprefix,httail,htframe⟩ := tape_ready i hi p heps
    j B utility record cache stride N b hbready hN hrecord hutility hbefore hB hFn hHigh hbimage hbsaved hbprefix hbtail
  have htmeta := hbmeta.tape_frame (by omega : 0 < N) hrecord hbefore htframe
  refine ⟨19+(cs+ct),t,Eval.seq ha (Eval.seq hs ht),by omega,htready,htmeta,htimage,htsaved,htprefix,httail,?_⟩
  intro address hout hsource hutil
  have hheader := haframe address
    (by simpa using hout 0 (by omega)) (by simpa using hout 1 (by omega))
    (by simpa using hout 2 (by omega)) (by simpa using hout 3 (by omega))
  have hsnapshot := hbframe address (by
    intro r hr
    have hh : record+8+2*r = record+2*(r+4) := by omega
    rw [hh]
    exact hout (r+4) (by omega)) hutil
  have htape := htframe address hsource hutil
  exact ⟨htape.1.trans (hsnapshot.1.trans hheader.1),htape.2.trans (hsnapshot.2.trans hheader.2)⟩
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
lemma initialize_from_maintains (p : Program) (C : ℝ) (a : ℕ → ℝ) (queryBound : ℕ)
    (i : Input) (hmaintains : Maintains p C a queryBound false i)
    (B bank : ℕ) (s : Data)
    (hB : s.natReg 74 = B) (hF : s.natReg 112 = bankFactor bank) (hz : s.natReg 56 = 0)
    (hwork : s.natMem (s.natReg 106+6) = 0)
    (hmr : ∀ addr, s.realMem (B+bankFactor bank*(2*addr+1)) = (initialMachine p i).realMem addr)
    (hmn : ∀ addr, s.natMem (B+bankFactor bank*(2*addr+1)) = bankFactor bank*(initialMachine p i).natMem addr)
    (hsaved : ∀ j < registerBound p.code,
      s.natMem (s.natReg 50+2*j) = bankFactor bank*(initialMachine p i).natReg j ∧
      s.realMem (s.natReg 50+2*j) = (initialMachine p i).realReg j)
    (htail : ∀ j, registerBound p.code ≤ j → s.natReg (shadowReg j) = 0 ∧ s.realReg (shadowReg j) = 0)
    (hbase : s.natReg 50 = s.natReg 106+8) (hrecord : ∃ r, s.natReg 106 = B+2*r+1) :
    ∃ final cost t, Ends p (initialMachine p i) final ∧
      Eval (code (registerBound p.code) p.initPC p) s cost t ∧
      cost ≤ (dispatchCharge p.code+2)*final.work+8*registerBound p.code+15 ∧
      ShadowDataRep B (bankFactor bank) t final ∧
      ZeroRegisterTail (registerBound p.code) final ∧
      stored final i.source.val = 0 ∧
      (∀ v : Fin i.n, final.natMem v.val ≤ 1 ∧ (final.natMem v.val = 0 → 0 ≤ final.realMem v.val)) ∧
      (∀ v : Fin i.n, i.dist [] v ≤ stored final v.val ∧
        stored final v.val ≤ ENNReal.ofReal (1+i.accuracy)*i.dist [] v ∧
        (stored final v.val = ⊤ ↔ ¬Reachable i.graph (live []) i.source v)) ∧
      (final.work : ℝ) ≤ C*i.size*a i.size/i.accuracy ∧
      t.natMem (s.natReg 106+6) = final.work ∧
      (∀ j < registerBound p.code, t.natMem (s.natReg 50+2*j) = bankFactor bank*final.natReg j ∧
        t.realMem (s.natReg 50+2*j) = final.realReg j) ∧
      (∀ address, (∀ addr, address ≠ B+bankFactor bank*(2*addr+1)) →
        address ≠ s.natReg 106+6 → (∀ j < registerBound p.code, address ≠ s.natReg 50+2*j) →
        t.natMem address = s.natMem address ∧ t.realMem address = s.realMem address) := by
  obtain ⟨final,hend,hsource,hnormal,haccurate,hcost⟩ := hmaintains.initialization
  have hinitzero := initialMachine_zero_tail p i
  obtain ⟨cost,t,he,hccost,hrep,htwork,htsaved,hframe⟩ := eval_code (registerBound p.code) p.initPC B bank s p
    (initialMachine p i) final hB hF hz rfl hwork rfl rfl hmr hmn hsaved htail hinitzero hend hbase hrecord
  refine ⟨final,cost,t,hend,he,?_,hrep,hinitzero.ends hend,hsource,hnormal,haccurate,?_,htwork,htsaved,hframe⟩
  · simpa only [initialMachine,Nat.sub_zero] using hccost
  · simpa using hcost
end DecrAlmostLinearSSSP.Decremental.SourceCall
end s150
section s151
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
namespace CacheCopy
lemma call_nat_frame (k : ℕ) (h20 : k ≠ 20) (h22 : k ≠ 22) (h128 : k ≠ 128)
    (h130 : k ≠ 130) (h132 : k ≠ 132) (h170 : k ≠ 170) (h176 : k ≠ 176) : NatFrame call k :=
  ⟨setup_nat_frame k h128 h132 h170 h20 h176,nat_frame k h20 h22 h128 h130 h176⟩
lemma call_real_frame (k : ℕ) (h20 : k ≠ 20) : RealFrame call k :=
  ⟨setup_real_frame k,real_frame k h20⟩
lemma tailFrame_call : TailFrame call := by
  intro j hj
  exact ⟨call_nat_frame _ (shadowReg_ne_of_even j 20 (by decide)) (shadowReg_ne_of_even j 22 (by decide))
    (shadowReg_ne_of_even j 128 (by decide)) (shadowReg_ne_of_even j 130 (by decide))
    (shadowReg_ne_of_even j 132 (by decide)) (shadowReg_ne_of_even j 170 (by decide))
    (shadowReg_ne_of_even j 176 (by decide)),call_real_frame _ (shadowReg_ne_of_even j 20 (by decide))⟩
end CacheCopy
namespace Native
lemma globalFrame_cacheCall : GlobalFrame CacheCopy.call := by
  constructor
  · intro k hk
    simp only [globalNat,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals apply CacheCopy.call_nat_frame <;> norm_num
  · intro k hk
    simp only [globalReal,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl
    all_goals apply CacheCopy.call_real_frame <;> norm_num
lemma bankFrame_cacheCall : BankFrame CacheCopy.call := by
  constructor
  · intro k hk
    simp only [bankNat,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl
    all_goals apply CacheCopy.call_nat_frame <;> norm_num
  · apply CacheCopy.call_real_frame
    omega
end Native
end DecrAlmostLinearSSSP.Decremental
end s151
section s152
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Native
lemma RecordImage.source_frame {i : Input} {j B record cache next N : ℕ} {s t : Structured.Data}
    (h : RecordImage i j record cache next s) (hrecord : ∃ r, record = B+2*r+1)
    (hf : ∀ address, (∀ a, address ≠ B+bankFactor j*(2*a+1)) → address ≠ record+6 →
      (∀ r < N, address ≠ record+8+2*r) →
      t.natMem address = s.natMem address ∧ t.realMem address = s.realMem address) : RecordImage i j record cache next t := by
  apply h.frame
  intro offset hoff
  have ho : offset ≤ 4 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hoff;omega
  have heven : Even offset := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hoff
    rcases hoff with rfl | rfl | rfl <;> decide
  apply hf
  · exact host_record_ne_bank B j record offset hrecord heven
  · omega
  · intro r hr;omega
lemma RecordImage.cache_frame {i : Input} {j record cache next count : ℕ} {s t : Structured.Data}
    (h : RecordImage i j record cache next s) (hbefore : record+4 < cache)
    (hf : ∀ address, (∀ v < count, address ≠ cache+2*v) →
      t.natMem address = s.natMem address ∧ t.realMem address = s.realMem address) : RecordImage i j record cache next t := by
  apply h.frame
  intro offset hoff
  have ho : offset ≤ 4 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hoff;omega
  apply hf
  intro v hv
  omega
end DecrAlmostLinearSSSP.Decremental.Native
end s152
section s153
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
lemma initializeScale_eval (i : Input) (hi : i.Valid) (p : Program) (C : ℝ) (a : ℕ → ℝ) (queryBound : ℕ)
    (heps : 1/(i.size : ℝ) < i.accuracy) (j B utility record cache stride : ℕ) (s : Data)
    (hmaintains : Maintains p C a queryBound false (barrierInput i j))
    (hg : Globals i B utility s) (hb : BankEnv j record cache stride s)
    (hrecord : ∃ r, record = B+2*r+1) (hcache : ∃ c, cache = B+2*c+1) (hutility : ∃ u, utility = B+2*u)
    (hbefore : ∀ r < registerBound p.code, record+8+2*r < utility)
    (hrecordCache : record+2*(registerBound p.code+3) < cache) (hB : i.n+3*i.k ≤ B)
    (himage : SourceMemory.Image B j s (fun _ => 0) (fun _ => 0))
    (hprefix : ∀ address, address ≤ B → s.natMem address = (initialMachine p i).natMem address)
    (htail : ∀ r, registerBound p.code ≤ r → s.natReg (shadowReg r) = 0 ∧ s.realReg (shadowReg r) = 0) :
    ∃ final cost t, Ends p (initialMachine p (barrierInput i j)) final ∧
      Eval (initializeScale p) s cost t ∧
      cost ≤ (dispatchCharge p.code+2)*final.work+14*registerBound p.code+
        5*((dispatchCharge ScaledCeiling.ceilingProgram.code+3)*(16*utilityDepth i.size+32))+
        i.k*(3*((dispatchCharge ScaledCeiling.ceilingProgram.code+3)*(16*utilityDepth i.size+32))+30)+13*i.n+158 ∧
      Globals i B utility t ∧ BankEnv j record cache stride t ∧ RecordImage i j record cache (record+stride) t ∧
      SourceMemory.Image B j t final.natMem final.realMem ∧
      t.natMem (record+6) = final.work ∧
      (∀ r < registerBound p.code, t.natMem (record+8+2*r) = bankFactor j*final.natReg r ∧
        t.realMem (record+8+2*r) = final.realReg r) ∧
      (∀ v : Fin i.n, t.natMem (cache+2*v.val) = final.natMem v.val ∧
        t.realMem (cache+2*v.val) = delta i j*final.realMem v.val ∧
        ExtendedMax.cell t (cache+2*v.val) = ENNReal.ofReal (delta i j)*stored final v.val) ∧
      (∀ v : Fin i.n, final.natMem v.val ≤ 1 ∧ (final.natMem v.val = 0 → 0 ≤ final.realMem v.val)) ∧
      (∀ v : Fin i.n, (barrierInput i j).dist [] v ≤ stored final v.val ∧
        stored final v.val ≤ ENNReal.ofReal (1+(barrierInput i j).accuracy)*(barrierInput i j).dist [] v ∧
        (stored final v.val = ⊤ ↔ ¬Reachable i.graph (live []) i.source v)) ∧
      (final.work : ℝ) ≤ C*(barrierInput i j).size*a (barrierInput i j).size/(barrierInput i j).accuracy ∧
      (∀ r, registerBound p.code ≤ r → t.natReg (shadowReg r) = 0 ∧ t.realReg (shadowReg r) = 0) ∧
      (∀ address, (∀ r < registerBound p.code+4, address ≠ record+2*r) →
        (∀ v, address ≠ bankAddress B j v) → (∀ v < i.n, address ≠ cache+2*v) →
        (∀ v, address ≠ utility+2*v+1) →
        t.natMem address = s.natMem address ∧ t.realMem address = s.realMem address) := by
  let N := registerBound p.code
  have hN : 8 ≤ N := registerBound_ge p.code
  obtain ⟨cp,u,hu,hcp,huready,humeta,huimage,husaved,huprefix,hutail,huprepframe⟩ := prepareBank_eval i hi p heps
    j B utility record cache stride N s hg hb hN hrecord hutility hbefore hB himage hprefix htail
  have hug := huready.globals
  have hub := huready.bank
  have huwork : u.natMem (u.natReg 106+6) = 0 := by rw [hub.record];exact huready.work
  have hubase : u.natReg 50 = u.natReg 106+8 := by rw [hub.record];exact huready.savebase
  have husaved' : ∀ r < N, u.natMem (u.natReg 50+2*r) = bankFactor j*(initialMachine p (barrierInput i j)).natReg r ∧
      u.realMem (u.natReg 50+2*r) = (initialMachine p (barrierInput i j)).realReg r := by simpa only [huready.savebase] using husaved
  obtain ⟨final,cc,v,hend,hv,hcc,hvrep,hfinaltail,hsource,hnormal,haccuracy,hwork,hvwork,hvsaved,hvframe⟩ :=
    SourceCall.initialize_from_maintains p C a queryBound (barrierInput i j) hmaintains B j u hug.base hub.factor hug.zeroN
      huwork huimage.realMem huimage.natMem husaved' hutail hubase (by simpa only [hub.record] using hrecord)
  have hvg := hug.transfer hv (globalFrame_sourceCall N p.initPC p)
  have hvb := hub.transfer hv (bankFrame_sourceCall N p.initPC p)
  have hvdelta : v.realReg 70 = delta i j := (hv.real_frame (SourceCall.real_even_frame N p.initPC p 70 (by omega) (by decide))).trans huready.delta
  obtain ⟨cacheOffset,hcacheEq⟩ := hcache
  obtain ⟨ccopy,t,ht,hcopy,htcache,htcacheframe,htbanks⟩ := CacheCopy.call_source B j cacheOffset i.n (delta i j) v final hvrep
    (delta_positive i hi j) hvg.base hvb.factor (hvb.cache.trans hcacheEq) hvg.vertices hvdelta hvg.zeroN hvg.unit hvg.two
    (fun v => (hnormal v).1) (fun v hv => (hnormal v).2 hv)
  have htg := hvg.transfer ht globalFrame_cacheCall
  have htb := hvb.transfer ht bankFrame_cacheCall
  have hsourceframe : ∀ address, (∀ addr, address ≠ B+bankFactor j*(2*addr+1)) → address ≠ record+6 →
      (∀ r < N, address ≠ record+8+2*r) →
      v.natMem address = u.natMem address ∧ v.realMem address = u.realMem address := by
    simpa only [hub.record,huready.savebase] using hvframe
  have hvmeta := humeta.source_frame hrecord hsourceframe
  have hcacheframe : ∀ address, (∀ r < i.n, address ≠ cache+2*r) →
      t.natMem address = v.natMem address ∧ t.realMem address = v.realMem address := by
    simpa only [hcacheEq] using htcacheframe
  have htmeta := hvmeta.cache_frame (by omega : record+4 < cache) hcacheframe
  have htimage : SourceMemory.Image B j t final.natMem final.realMem := by
    constructor
    · intro r
      exact (htbanks r).1.trans (hvrep.natMem r)
    · intro r
      exact (htbanks r).2.trans (hvrep.realMem r)
  have hvtail : ∀ r, N ≤ r → v.natReg (shadowReg r) = 0 ∧ v.realReg (shadowReg r) = 0 := by
    intro r hr
    obtain ⟨hn,hr'⟩ := hfinaltail r hr
    exact ⟨(hvrep.natReg r).trans (by rw [hn];simp),(hvrep.realReg r).trans hr'⟩
  have httail := CacheCopy.tailFrame_call.preserves ht hN hvtail
  have hsavedFinal : ∀ r < N, t.natMem (record+8+2*r) = bankFactor j*final.natReg r ∧
      t.realMem (record+8+2*r) = final.realReg r := by
    intro r hr
    have hh := hcacheframe (record+8+2*r) (by intro v hv;omega)
    have hs := hvsaved r hr
    rw [huready.savebase] at hs
    exact ⟨hh.1.trans hs.1,hh.2.trans hs.2⟩
  have htwork : t.natMem (record+6) = final.work := by
    have hh := hcacheframe (record+6) (by intro v hv;omega)
    have hw : v.natMem (record+6) = final.work := by simpa only [hub.record] using hvwork
    exact hh.1.trans hw
  refine ⟨final,cp+(cc+ccopy),t,hend,Eval.seq hu (Eval.seq hv ht),by omega,htg,htb,htmeta,htimage,htwork,hsavedFinal,?_,hnormal,haccuracy,hwork,httail,?_⟩
  · simpa only [hcacheEq] using htcache
  · intro address hrecordOut hbankOut hcacheOut hutilOut
    have hp := huprepframe address hrecordOut (fun r hr => hbankOut _) hutilOut
    have hs := hsourceframe address hbankOut
      (by simpa using hrecordOut 3 (by omega)) (by
        intro r hr
        have heq : record+8+2*r = record+2*(r+4) := by omega
        rw [heq]
        exact hrecordOut (r+4) (by omega))
    have hc := hcacheframe address hcacheOut
    exact ⟨hc.1.trans (hs.1.trans hp.1),hc.2.trans (hs.2.trans hp.2)⟩
end DecrAlmostLinearSSSP.Decremental.Native
end s153
section s154
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
lemma ControlFrame.seq {a b : Cmd} (ha : ControlFrame a) (hb : ControlFrame b) : ControlFrame (.seq a b) :=
  fun k hlow hhigh heven => ⟨ha k hlow hhigh heven,hb k hlow hhigh heven⟩
lemma controlFrame_header : ControlFrame RecordHeader.code := by
  intro k hlo hhi hev
  apply RecordHeader.nat_frame <;> omega
lemma controlFrame_snapshotFill (N : ℕ) : ControlFrame (SnapshotFill.code N) := by
  intro k hlo hhi hev
  apply SnapshotFill.nat_frame <;> omega
lemma controlFrame_prepare : ControlFrame ScaleParameters.prepare := by
  intro k hlo hhi hev
  apply ScaleParameters.prepare_nat_frame
  all_goals first | omega | exact hev
lemma controlFrame_fields : ControlFrame ScaleParameters.writeFields := by
  intro k hlo hhi hev
  apply ScaleParameters.fields_nat_frame
  omega
lemma controlFrame_initializeSnapshot (N : ℕ) : ControlFrame (ScaleParameters.initializeSnapshot N) :=
  (controlFrame_snapshotFill N).seq (controlFrame_prepare.seq controlFrame_fields)
lemma controlFrame_tapeStart : ControlFrame TapeCopy.start := by
  intro k hlo hhi hev
  apply TapeCopy.start_nat_frame <;> omega
lemma controlFrame_naturalField : ControlFrame TapeCopy.naturalField := by
  intro k hlo hhi hev
  apply TapeCopy.naturalField_nat_frame
  all_goals first | omega | exact hev
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
theorem solution : (((((((DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame DecrAlmostLinearSSSP.Decremental.RecordHeader.code) ∧ (∀ (N : Nat), DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame (DecrAlmostLinearSSSP.Decremental.SnapshotFill.code N))) ∧ ((DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame DecrAlmostLinearSSSP.Decremental.ScaleParameters.prepare) ∧ (DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame DecrAlmostLinearSSSP.Decremental.ScaleParameters.writeFields))) ∧ (((∀ (N : Nat),
  DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame
    (DecrAlmostLinearSSSP.Decremental.ScaleParameters.initializeSnapshot N)) ∧ (DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame DecrAlmostLinearSSSP.Decremental.TapeCopy.start)) ∧ ((DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame DecrAlmostLinearSSSP.Decremental.TapeCopy.naturalField) ∧ ((DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame DecrAlmostLinearSSSP.Decremental.TapeCopy.weightField) ∧ (DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame DecrAlmostLinearSSSP.Decremental.TapeCopy.edge))))) ∧ ((((DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame DecrAlmostLinearSSSP.Decremental.TapeCopy.code) ∧ (∀ (N entry : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program),
  DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame (DecrAlmostLinearSSSP.Decremental.SourceCall.code N entry p))) ∧ ((∀ {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {coefficient stride cost : Nat},
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Prepass.code coefficient stride) s
      cost t →
    @Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 100) (instOfNatNat (nat_lit 100))))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 66) (instOfNatNat (nat_lit 66)))))) ∧ (∀ {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {i : DecrAlmostLinearSSSP.Decremental.Input}
  {coefficient stride cost : Nat},
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Prepass.code coefficient stride)
        s cost t →
      DecrAlmostLinearSSSP.Decremental.Layout.Represents t
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
            stride) →
        DecrAlmostLinearSSSP.Decremental.Native.Globals i
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
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
              stride).utility
          t))) ∧ (((∀ {a b : DecrAlmostLinearSSSP.Decremental.Structured.Cmd},
  DecrAlmostLinearSSSP.Decremental.Native.BankFrame a →
    DecrAlmostLinearSSSP.Decremental.Native.BankFrame b → DecrAlmostLinearSSSP.Decremental.Native.BankFrame (a.seq b)) ∧ (∀ (test : DecrAlmostLinearSSSP.Decremental.Structured.Test) {body : DecrAlmostLinearSSSP.Decremental.Structured.Cmd},
  DecrAlmostLinearSSSP.Decremental.Native.BankFrame body →
    DecrAlmostLinearSSSP.Decremental.Native.BankFrame (DecrAlmostLinearSSSP.Decremental.Structured.Cmd.loop test body))) ∧ ((∀ {j record cache stride cost : Nat} {cmd : DecrAlmostLinearSSSP.Decremental.Structured.Cmd}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.BankEnv j record cache stride s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval cmd s cost t →
      DecrAlmostLinearSSSP.Decremental.Native.BankFrame cmd →
        DecrAlmostLinearSSSP.Decremental.Native.BankEnv j record cache stride t) ∧ ((DecrAlmostLinearSSSP.Decremental.Native.BankFrame DecrAlmostLinearSSSP.Decremental.RecordHeader.code) ∧ (∀ (N : Nat), DecrAlmostLinearSSSP.Decremental.Native.BankFrame (DecrAlmostLinearSSSP.Decremental.SnapshotFill.code N))))))) ∧ (((((DecrAlmostLinearSSSP.Decremental.Native.BankFrame DecrAlmostLinearSSSP.Decremental.ScaleParameters.prepare) ∧ (DecrAlmostLinearSSSP.Decremental.Native.BankFrame DecrAlmostLinearSSSP.Decremental.ScaleParameters.writeFields)) ∧ ((DecrAlmostLinearSSSP.Decremental.Native.BankFrame DecrAlmostLinearSSSP.Decremental.TapeCopy.start) ∧ (DecrAlmostLinearSSSP.Decremental.Native.BankFrame DecrAlmostLinearSSSP.Decremental.TapeCopy.naturalField))) ∧ (((DecrAlmostLinearSSSP.Decremental.Native.BankFrame DecrAlmostLinearSSSP.Decremental.TapeCopy.weightField) ∧ (∀ (N entry : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program),
  DecrAlmostLinearSSSP.Decremental.Native.BankFrame (DecrAlmostLinearSSSP.Decremental.SourceCall.code N entry p))) ∧ ((∀ (N : Nat),
  DecrAlmostLinearSSSP.Decremental.Native.BankFrame
    (DecrAlmostLinearSSSP.Decremental.ScaleParameters.initializeSnapshot N)) ∧ ((DecrAlmostLinearSSSP.Decremental.Native.BankFrame DecrAlmostLinearSSSP.Decremental.TapeCopy.edge) ∧ (DecrAlmostLinearSSSP.Decremental.Native.BankFrame DecrAlmostLinearSSSP.Decremental.TapeCopy.code))))) ∧ ((((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (j B utility record cache stride N : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Native.Globals i B utility s →
    DecrAlmostLinearSSSP.Decremental.Native.BankEnv j record cache stride s →
      (∃ r,
          @Eq.{1} Nat record
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
        @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) N →
          (DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B j s
              (fun x => @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) fun x =>
              @OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
            ∀ (raw : Nat → Nat),
              (∀ (address : Nat), @LE.le.{0} Nat instLENat address B → @Eq.{1} Nat (s.natMem address) (raw address)) →
                (∀ (r : Nat),
                    @LE.le.{0} Nat instLENat N r →
                      And
                        (@Eq.{1} Nat (s.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg r))
                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                        (@Eq.{1} Real (s.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg r))
                          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))) →
                  ∃ t,
                    And
                      (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                        DecrAlmostLinearSSSP.Decremental.RecordHeader.code s
                        (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19))) t)
                      (And (DecrAlmostLinearSSSP.Decremental.Native.Ready i j B utility record cache stride t)
                        (And
                          (DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B j t
                            (fun x => @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) fun x =>
                            @OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                          (And
                            (∀ (address : Nat),
                              @LE.le.{0} Nat instLENat address B → @Eq.{1} Nat (t.natMem address) (raw address))
                            (And
                              (∀ (r : Nat),
                                @LE.le.{0} Nat instLENat N r →
                                  And
                                    (@Eq.{1} Nat (t.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg r))
                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                    (@Eq.{1} Real (t.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg r))
                                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
                              (∀ (address : Nat),
                                @Ne.{1} Nat address record →
                                  @Ne.{1} Nat address
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
                                    @Ne.{1} Nat address
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record
                                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) →
                                      @Ne.{1} Nat address
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record
                                            (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))) →
                                        And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                          (@Eq.{1} Real (t.realMem address) (s.realMem address)))))))) ∧ (∀ (N k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 116) (instOfNatNat (nat_lit 116))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 200) (instOfNatNat (nat_lit 200))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 202) (instOfNatNat (nat_lit 202))) →
              @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 204) (instOfNatNat (nat_lit 204))) →
                @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 208) (instOfNatNat (nat_lit 208))) →
                  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
                    (DecrAlmostLinearSSSP.Decremental.ScaleParameters.initializeSnapshot N) k)) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (p : DecrAlmostLinearSSSP.Decremental.Program),
      @LT.lt.{0} Real Real.instLT
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@Nat.cast.{0} Real Real.instNatCast i.size))
          i.accuracy →
        ∀ (j B utility record cache stride N : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
          DecrAlmostLinearSSSP.Decremental.Native.Ready i j B utility record cache stride s →
            @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) N →
              (∃ r,
                  @Eq.{1} Nat record
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                (∃ u,
                    @Eq.{1} Nat utility
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) u))) →
                  (∀ (r : Nat),
                      @LT.lt.{0} Nat instLTNat r N →
                        @LT.lt.{0} Nat instLTNat
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record
                              (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
                          utility) →
                    (DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B j s
                        (fun x => @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) fun x =>
                        @OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
                      ∀ (raw : Nat → Nat),
                        (∀ (address : Nat),
                            @LE.le.{0} Nat instLENat address B → @Eq.{1} Nat (s.natMem address) (raw address)) →
                          (∀ (r : Nat),
                              @LE.le.{0} Nat instLENat N r →
                                And
                                  (@Eq.{1} Nat (s.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg r))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                  (@Eq.{1} Real (s.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg r))
                                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))) →
                            ∃ cost t,
                              And
                                (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                  (DecrAlmostLinearSSSP.Decremental.ScaleParameters.initializeSnapshot N) s cost t)
                                (And
                                  (@LE.le.{0} Nat instLENat cost
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) N)
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (DecrAlmostLinearSSSP.Decremental.dispatchCharge
                                                DecrAlmostLinearSSSP.Decremental.ScaledCeiling.ceilingProgram.code)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))
                                                (DecrAlmostLinearSSSP.Decremental.utilityDepth i.size))
                                              (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))))))
                                      (@OfNat.ofNat.{0} Nat (nat_lit 109) (instOfNatNat (nat_lit 109)))))
                                  (And
                                    (DecrAlmostLinearSSSP.Decremental.Native.Ready i j B utility record cache stride t)
                                    (And
                                      (DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B j t
                                        (fun x => @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) fun x =>
                                        @OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                      (And
                                        (@Eq.{1} Nat
                                          (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 154) (instOfNatNat (nat_lit 154))))
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (DecrAlmostLinearSSSP.Decremental.bankFactor j) i.n))
                                        (And
                                          (@Eq.{1} Nat
                                            (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 152) (instOfNatNat (nat_lit 152))))
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (DecrAlmostLinearSSSP.Decremental.bankFactor j)
                                              (DecrAlmostLinearSSSP.Decremental.barrierHigh i)))
                                          (And
                                            (∀ (r : Nat),
                                              @LT.lt.{0} Nat instLTNat r N →
                                                And
                                                  (@Eq.{1} Nat
                                                    (t.natMem
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          record
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                          r)))
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (DecrAlmostLinearSSSP.Decremental.bankFactor j)
                                                      ((DecrAlmostLinearSSSP.Decremental.initialMachine p
                                                            (DecrAlmostLinearSSSP.Decremental.barrierInput i j)).natReg
                                                        r)))
                                                  (@Eq.{1} Real
                                                    (t.realMem
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          record
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                          r)))
                                                    ((DecrAlmostLinearSSSP.Decremental.initialMachine p
                                                          (DecrAlmostLinearSSSP.Decremental.barrierInput i j)).realReg
                                                      r)))
                                            (And
                                              (∀ (address : Nat),
                                                @LE.le.{0} Nat instLENat address B →
                                                  @Eq.{1} Nat (t.natMem address) (raw address))
                                              (And
                                                (∀ (r : Nat),
                                                  @LE.le.{0} Nat instLENat N r →
                                                    And
                                                      (@Eq.{1} Nat
                                                        (t.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg r))
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                      (@Eq.{1} Real
                                                        (t.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg r))
                                                        (@OfNat.ofNat.{0} Real (nat_lit 0)
                                                          (@Zero.toOfNat0.{0} Real Real.instZero))))
                                                (∀ (address : Nat),
                                                  (∀ (r : Nat),
                                                      @LT.lt.{0} Nat instLTNat r N →
                                                        @Ne.{1} Nat address
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat)
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat) record
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 8)
                                                                (instOfNatNat (nat_lit 8))))
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                (instOfNatNat (nat_lit 2)))
                                                              r))) →
                                                    (∀ (a : Nat),
                                                        @Ne.{1} Nat address
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat)
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat) utility
                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                (@instHMul.{0} Nat instMulNat)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                  (instOfNatNat (nat_lit 2)))
                                                                a))
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                              (instOfNatNat (nat_lit 1))))) →
                                                      And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                                        (@Eq.{1} Real (t.realMem address) (s.realMem address)))))))))))) ∧ ((∀ (raw : Nat → Nat) (delta cutoff : Real) (high : Nat) (natural : Nat → Nat) (origin logical address : Nat),
  @Ne.{1} Nat address logical →
    @Ne.{1} Nat address
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) logical
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
      @Ne.{1} Nat address
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) logical
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
        @Eq.{1} Nat
          (DecrAlmostLinearSSSP.Decremental.TapeCopy.edgeImage raw delta cutoff high natural origin logical address)
          (natural address)) ∧ (∀ (raw : Nat → Nat) (delta cutoff : Real) (high count : Nat) (natural : Nat → Nat) (origin logical address : Nat),
  Or (@LT.lt.{0} Nat instLTNat address logical)
      (@LE.le.{0} Nat instLENat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) logical
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) count))
        address) →
    @Eq.{1} Nat
      (DecrAlmostLinearSSSP.Decremental.TapeCopy.tapeImage raw delta cutoff high count natural origin logical address)
      (natural address))))) ∧ (((∀ (raw : Nat → Nat) (delta cutoff : Real) (high count : Nat) (natural : Nat → Nat) (origin logical j : Nat),
  @LT.lt.{0} Nat instLTNat j count →
    And
      (@Eq.{1} Nat
        (DecrAlmostLinearSSSP.Decremental.TapeCopy.tapeImage raw delta cutoff high count natural origin logical
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) logical
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j)))
        (raw
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) origin
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j))))
      (And
        (@Eq.{1} Nat
          (DecrAlmostLinearSSSP.Decremental.TapeCopy.tapeImage raw delta cutoff high count natural origin logical
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) logical
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (raw
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) origin
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (@Eq.{1} Nat
          (DecrAlmostLinearSSSP.Decremental.TapeCopy.tapeImage raw delta cutoff high count natural origin logical
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) logical
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (DecrAlmostLinearSSSP.Decremental.TapeCopy.roundedWeight delta cutoff high
            (raw
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) origin
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (j : Nat) (e : Fin i.k),
  @Eq.{1} Nat
    (DecrAlmostLinearSSSP.Decremental.TapeCopy.roundedWeight (DecrAlmostLinearSSSP.Decremental.delta i j)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (DecrAlmostLinearSSSP.Decremental.scale j))
      (DecrAlmostLinearSSSP.Decremental.barrierHigh i) (i.weight e))
    (DecrAlmostLinearSSSP.Decremental.barrierWeight i j e))) ∧ ((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (i : DecrAlmostLinearSSSP.Decremental.Input) (j : Nat),
  @Eq.{1} (Nat → Nat)
    (DecrAlmostLinearSSSP.Decremental.TapeCopy.tapeImage (DecrAlmostLinearSSSP.Decremental.initialMachine p i).natMem
      (DecrAlmostLinearSSSP.Decremental.delta i j)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (DecrAlmostLinearSSSP.Decremental.scale j))
      (DecrAlmostLinearSSSP.Decremental.barrierHigh i) i.k
      (fun x => @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) i.n i.n)
    (DecrAlmostLinearSSSP.Decremental.initialMachine p (DecrAlmostLinearSSSP.Decremental.barrierInput i j)).natMem) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (x : Nat),
      @LE.le.{0} Nat instLENat x i.size →
        @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast x)
          (@HPow.hPow.{0, 0, 0} Real Nat Real
            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
            (DecrAlmostLinearSSSP.Decremental.utilityDepth i.size))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    @LT.lt.{0} Real Real.instLT
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@Nat.cast.{0} Real Real.instNatCast i.size))
        i.accuracy →
      ∀ (j : Nat) (w : Real),
        @LE.le.{0} Real Real.instLE w
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              (DecrAlmostLinearSSSP.Decremental.scale j)) →
          @LE.le.{0} Real Real.instLE
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) w
              (DecrAlmostLinearSSSP.Decremental.delta i j))
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              (DecrAlmostLinearSSSP.Decremental.utilityDepth i.size))))))))) ∧ ((((((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (p : DecrAlmostLinearSSSP.Decremental.Program)
  (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    @LT.lt.{0} Real Real.instLT
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@Nat.cast.{0} Real Real.instNatCast i.size))
        i.accuracy →
      ∀ (j B bank tail : Nat),
        DecrAlmostLinearSSSP.Decremental.TapeCopy.Env B bank tail (DecrAlmostLinearSSSP.Decremental.barrierHigh i)
            (DecrAlmostLinearSSSP.Decremental.delta i j)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              (DecrAlmostLinearSSSP.Decremental.scale j))
            s →
          (DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B bank s
              (fun x => @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) fun x =>
              @OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 162) (instOfNatNat (nat_lit 162)))) i.n →
              @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 164) (instOfNatNat (nat_lit 164))))
                  (DecrAlmostLinearSSSP.Decremental.bankAddress B bank i.n) →
                @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 166) (instOfNatNat (nat_lit 166)))) i.k →
                  @LE.le.{0} Nat instLENat
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
                      B →
                    (∀ (address : Nat),
                        @LE.le.{0} Nat instLENat address B →
                          @Eq.{1} Nat (s.natMem address)
                            ((DecrAlmostLinearSSSP.Decremental.initialMachine p i).natMem address)) →
                      ∃ cost t,
                        And
                          (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                            DecrAlmostLinearSSSP.Decremental.TapeCopy.code s cost t)
                          (And
                            (@LE.le.{0} Nat instLENat cost
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) i.k
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
                                            (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))
                                            (DecrAlmostLinearSSSP.Decremental.utilityDepth i.size))
                                          (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                            (And
                              (DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B bank t
                                (DecrAlmostLinearSSSP.Decremental.initialMachine p
                                    (DecrAlmostLinearSSSP.Decremental.barrierInput i j)).natMem
                                (DecrAlmostLinearSSSP.Decremental.initialMachine p
                                    (DecrAlmostLinearSSSP.Decremental.barrierInput i j)).realMem)
                              (And
                                (DecrAlmostLinearSSSP.Decremental.TapeCopy.Env B bank tail
                                  (DecrAlmostLinearSSSP.Decremental.barrierHigh i)
                                  (DecrAlmostLinearSSSP.Decremental.delta i j)
                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                    (@OfNat.ofNat.{0} Real (nat_lit 2)
                                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                        (@Nat.instAtLeastTwoHAddOfNat
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                          (@Nat.instNeZeroSucc
                                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                                    (DecrAlmostLinearSSSP.Decremental.scale j))
                                  t)
                                (And
                                  (@Eq.{1} Nat
                                    (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 162) (instOfNatNat (nat_lit 162))))
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k)))
                                  (And
                                    (@Eq.{1} Nat
                                      (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 164) (instOfNatNat (nat_lit 164))))
                                      (DecrAlmostLinearSSSP.Decremental.bankAddress B bank
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))))
                                    (And
                                      (@Eq.{1} Nat
                                        (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 166) (instOfNatNat (nat_lit 166))))
                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                      (And
                                        (∀ (address : Nat),
                                          @LE.le.{0} Nat instLENat address B →
                                            @Eq.{1} Nat (t.natMem address)
                                              ((DecrAlmostLinearSSSP.Decremental.initialMachine p i).natMem address))
                                        (∀ (address : Nat),
                                          (∀ (a : Nat),
                                              @LT.lt.{0} Nat instLTNat a
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k) →
                                                @Ne.{1} Nat address
                                                  (DecrAlmostLinearSSSP.Decremental.bankAddress B bank
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                                                      a))) →
                                            (∀ (a : Nat),
                                                @Ne.{1} Nat address
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (s.natReg
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 48) (instOfNatNat (nat_lit 48))))
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                        a))
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                                              And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                                (@Eq.{1} Real (t.realMem address) (s.realMem address))))))))))) ∧ (∀ {a b : DecrAlmostLinearSSSP.Decremental.Structured.Cmd},
  DecrAlmostLinearSSSP.Decremental.TapeCopy.ConstantFrame a →
    DecrAlmostLinearSSSP.Decremental.TapeCopy.ConstantFrame b →
      DecrAlmostLinearSSSP.Decremental.TapeCopy.ConstantFrame (a.seq b))) ∧ ((DecrAlmostLinearSSSP.Decremental.TapeCopy.ConstantFrame DecrAlmostLinearSSSP.Decremental.TapeCopy.start) ∧ (DecrAlmostLinearSSSP.Decremental.TapeCopy.ConstantFrame DecrAlmostLinearSSSP.Decremental.TapeCopy.naturalField))) ∧ (((DecrAlmostLinearSSSP.Decremental.TapeCopy.ConstantFrame DecrAlmostLinearSSSP.Decremental.TapeCopy.weightField) ∧ (DecrAlmostLinearSSSP.Decremental.TapeCopy.ConstantFrame DecrAlmostLinearSSSP.Decremental.TapeCopy.edge)) ∧ ((DecrAlmostLinearSSSP.Decremental.TapeCopy.ConstantFrame DecrAlmostLinearSSSP.Decremental.TapeCopy.code) ∧ ((DecrAlmostLinearSSSP.Decremental.TailFrame DecrAlmostLinearSSSP.Decremental.Structured.Cmd.skip) ∧ (DecrAlmostLinearSSSP.Decremental.TailFrame
  (DecrAlmostLinearSSSP.Decremental.Structured.sequence
    (@List.cons.{0} DecrAlmostLinearSSSP.Decremental.Structured.Cmd
      (DecrAlmostLinearSSSP.Decremental.Structured.storeN
        (@OfNat.ofNat.{0} Nat (nat_lit 164) (instOfNatNat (nat_lit 164)))
        (@OfNat.ofNat.{0} Nat (nat_lit 174) (instOfNatNat (nat_lit 174))))
      (@List.cons.{0} DecrAlmostLinearSSSP.Decremental.Structured.Cmd
        (DecrAlmostLinearSSSP.Decremental.Structured.nadd
          (@OfNat.ofNat.{0} Nat (nat_lit 162) (instOfNatNat (nat_lit 162)))
          (@OfNat.ofNat.{0} Nat (nat_lit 162) (instOfNatNat (nat_lit 162)))
          (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
        (@List.cons.{0} DecrAlmostLinearSSSP.Decremental.Structured.Cmd
          (DecrAlmostLinearSSSP.Decremental.Structured.nadd
            (@OfNat.ofNat.{0} Nat (nat_lit 164) (instOfNatNat (nat_lit 164)))
            (@OfNat.ofNat.{0} Nat (nat_lit 164) (instOfNatNat (nat_lit 164)))
            (@OfNat.ofNat.{0} Nat (nat_lit 170) (instOfNatNat (nat_lit 170))))
          (@List.nil.{0} DecrAlmostLinearSSSP.Decremental.Structured.Cmd)))))))))) ∧ ((((DecrAlmostLinearSSSP.Decremental.TailFrame DecrAlmostLinearSSSP.Decremental.TapeCopy.naturalField) ∧ (DecrAlmostLinearSSSP.Decremental.TailFrame DecrAlmostLinearSSSP.Decremental.TapeCopy.chooseWeight)) ∧ ((DecrAlmostLinearSSSP.Decremental.TailFrame DecrAlmostLinearSSSP.Decremental.TapeCopy.weightField) ∧ ((DecrAlmostLinearSSSP.Decremental.TailFrame DecrAlmostLinearSSSP.Decremental.TapeCopy.edge) ∧ (DecrAlmostLinearSSSP.Decremental.TailFrame DecrAlmostLinearSSSP.Decremental.TapeCopy.code)))) ∧ (((∀ (B bank record offset : Nat),
  (∃ r,
      @Eq.{1} Nat record
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
    @Even.{0} Nat instAddNat offset →
      ∀ (a : Nat),
        @Ne.{1} Nat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record offset)
          (DecrAlmostLinearSSSP.Decremental.bankAddress B bank a)) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (p : DecrAlmostLinearSSSP.Decremental.Program),
      @LT.lt.{0} Real Real.instLT
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@Nat.cast.{0} Real Real.instNatCast i.size))
          i.accuracy →
        ∀ (j B utility record cache stride N : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
          DecrAlmostLinearSSSP.Decremental.Native.Ready i j B utility record cache stride s →
            @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) N →
              (∃ r,
                  @Eq.{1} Nat record
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                (∃ u,
                    @Eq.{1} Nat utility
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) u))) →
                  (∀ (r : Nat),
                      @LT.lt.{0} Nat instLTNat r N →
                        @LT.lt.{0} Nat instLTNat
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record
                              (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
                          utility) →
                    @LE.le.{0} Nat instLENat
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
                        B →
                      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 154) (instOfNatNat (nat_lit 154))))
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (DecrAlmostLinearSSSP.Decremental.bankFactor j) i.n) →
                        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 152) (instOfNatNat (nat_lit 152))))
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (DecrAlmostLinearSSSP.Decremental.bankFactor j)
                              (DecrAlmostLinearSSSP.Decremental.barrierHigh i)) →
                          (DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B j s
                              (fun x => @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) fun x =>
                              @OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
                            (∀ (r : Nat),
                                @LT.lt.{0} Nat instLTNat r N →
                                  And
                                    (@Eq.{1} Nat
                                      (s.natMem
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record
                                            (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)))
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (DecrAlmostLinearSSSP.Decremental.bankFactor j)
                                        ((DecrAlmostLinearSSSP.Decremental.initialMachine p
                                              (DecrAlmostLinearSSSP.Decremental.barrierInput i j)).natReg
                                          r)))
                                    (@Eq.{1} Real
                                      (s.realMem
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record
                                            (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)))
                                      ((DecrAlmostLinearSSSP.Decremental.initialMachine p
                                            (DecrAlmostLinearSSSP.Decremental.barrierInput i j)).realReg
                                        r))) →
                              (∀ (address : Nat),
                                  @LE.le.{0} Nat instLENat address B →
                                    @Eq.{1} Nat (s.natMem address)
                                      ((DecrAlmostLinearSSSP.Decremental.initialMachine p i).natMem address)) →
                                (∀ (r : Nat),
                                    @LE.le.{0} Nat instLENat N r →
                                      And
                                        (@Eq.{1} Nat (s.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg r))
                                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                        (@Eq.{1} Real (s.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg r))
                                          (@OfNat.ofNat.{0} Real (nat_lit 0)
                                            (@Zero.toOfNat0.{0} Real Real.instZero)))) →
                                  ∃ cost t,
                                    And
                                      (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                        DecrAlmostLinearSSSP.Decremental.Native.prepareTape s cost t)
                                      (And
                                        (@LE.le.{0} Nat instLENat cost
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) i.k
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
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))
                                                        (DecrAlmostLinearSSSP.Decremental.utilityDepth i.size))
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))))
                                                (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))
                                            (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))
                                        (And
                                          (DecrAlmostLinearSSSP.Decremental.Native.Ready i j B utility record cache
                                            stride t)
                                          (And
                                            (DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B j t
                                              (DecrAlmostLinearSSSP.Decremental.initialMachine p
                                                  (DecrAlmostLinearSSSP.Decremental.barrierInput i j)).natMem
                                              (DecrAlmostLinearSSSP.Decremental.initialMachine p
                                                  (DecrAlmostLinearSSSP.Decremental.barrierInput i j)).realMem)
                                            (And
                                              (∀ (r : Nat),
                                                @LT.lt.{0} Nat instLTNat r N →
                                                  And
                                                    (@Eq.{1} Nat
                                                      (t.natMem
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat) record
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 8)
                                                              (instOfNatNat (nat_lit 8))))
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                              (instOfNatNat (nat_lit 2)))
                                                            r)))
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (DecrAlmostLinearSSSP.Decremental.bankFactor j)
                                                        ((DecrAlmostLinearSSSP.Decremental.initialMachine p
                                                              (DecrAlmostLinearSSSP.Decremental.barrierInput i
                                                                j)).natReg
                                                          r)))
                                                    (@Eq.{1} Real
                                                      (t.realMem
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat) record
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 8)
                                                              (instOfNatNat (nat_lit 8))))
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                              (instOfNatNat (nat_lit 2)))
                                                            r)))
                                                      ((DecrAlmostLinearSSSP.Decremental.initialMachine p
                                                            (DecrAlmostLinearSSSP.Decremental.barrierInput i j)).realReg
                                                        r)))
                                              (And
                                                (∀ (address : Nat),
                                                  @LE.le.{0} Nat instLENat address B →
                                                    @Eq.{1} Nat (t.natMem address)
                                                      ((DecrAlmostLinearSSSP.Decremental.initialMachine p i).natMem
                                                        address))
                                                (And
                                                  (∀ (r : Nat),
                                                    @LE.le.{0} Nat instLENat N r →
                                                      And
                                                        (@Eq.{1} Nat
                                                          (t.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg r))
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                        (@Eq.{1} Real
                                                          (t.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg r))
                                                          (@OfNat.ofNat.{0} Real (nat_lit 0)
                                                            (@Zero.toOfNat0.{0} Real Real.instZero))))
                                                  (∀ (address : Nat),
                                                    (∀ (a : Nat),
                                                        @LT.lt.{0} Nat instLTNat a
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 3)
                                                                (instOfNatNat (nat_lit 3)))
                                                              i.k) →
                                                          @Ne.{1} Nat address
                                                            (DecrAlmostLinearSSSP.Decremental.bankAddress B j
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat) i.n a))) →
                                                      (∀ (a : Nat),
                                                          @Ne.{1} Nat address
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat) utility
                                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                  (@instHMul.{0} Nat instMulNat)
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                    (instOfNatNat (nat_lit 2)))
                                                                  a))
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                (instOfNatNat (nat_lit 1))))) →
                                                        And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                                          (@Eq.{1} Real (t.realMem address) (s.realMem address))))))))))) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {j record cache next : Nat}
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
      DecrAlmostLinearSSSP.Decremental.Native.RecordImage i j record cache next t) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {j B utility record cache stride cost : Nat}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.Globals i B utility s →
    DecrAlmostLinearSSSP.Decremental.Native.BankEnv j record cache stride s →
      DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.RecordHeader.code s cost t →
        DecrAlmostLinearSSSP.Decremental.Native.RecordImage i j record cache
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record stride) t) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {j record cache next utility N : Nat}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.RecordImage i j record cache next s →
    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) N →
      (∀ (r : Nat),
          @LT.lt.{0} Nat instLTNat r N →
            @LT.lt.{0} Nat instLTNat
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record
                  (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
              utility) →
        (∀ (address : Nat),
            (∀ (r : Nat),
                @LT.lt.{0} Nat instLTNat r N →
                  @Ne.{1} Nat address
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record
                        (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))) →
              (∀ (a : Nat),
                  @Ne.{1} Nat address
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) utility
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a))
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                  (@Eq.{1} Real (t.realMem address) (s.realMem address))) →
          DecrAlmostLinearSSSP.Decremental.Native.RecordImage i j record cache next t)))))) ∧ (((((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {j B record cache next utility N : Nat}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.RecordImage i j record cache next s →
    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) N →
      (∃ r,
          @Eq.{1} Nat record
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
        (∀ (r : Nat),
            @LT.lt.{0} Nat instLTNat r N →
              @LT.lt.{0} Nat instLTNat
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record
                    (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
                utility) →
          (∀ (address : Nat),
              (∀ (a : Nat),
                  @LT.lt.{0} Nat instLTNat a
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k) →
                    @Ne.{1} Nat address
                      (DecrAlmostLinearSSSP.Decremental.bankAddress B j
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n a))) →
                (∀ (a : Nat),
                    @Ne.{1} Nat address
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) utility
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a))
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                  And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                    (@Eq.{1} Real (t.realMem address) (s.realMem address))) →
            DecrAlmostLinearSSSP.Decremental.Native.RecordImage i j record cache next t) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (p : DecrAlmostLinearSSSP.Decremental.Program),
      @LT.lt.{0} Real Real.instLT
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@Nat.cast.{0} Real Real.instNatCast i.size))
          i.accuracy →
        ∀ (j B utility record cache stride N : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
          DecrAlmostLinearSSSP.Decremental.Native.Globals i B utility s →
            DecrAlmostLinearSSSP.Decremental.Native.BankEnv j record cache stride s →
              @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) N →
                (∃ r,
                    @Eq.{1} Nat record
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                  (∃ u,
                      @Eq.{1} Nat utility
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) u))) →
                    (∀ (r : Nat),
                        @LT.lt.{0} Nat instLTNat r N →
                          @LT.lt.{0} Nat instLTNat
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record
                                (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
                            utility) →
                      @LE.le.{0} Nat instLENat
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
                          B →
                        (DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B j s
                            (fun x => @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) fun x =>
                            @OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
                          (∀ (address : Nat),
                              @LE.le.{0} Nat instLENat address B →
                                @Eq.{1} Nat (s.natMem address)
                                  ((DecrAlmostLinearSSSP.Decremental.initialMachine p i).natMem address)) →
                            (∀ (r : Nat),
                                @LE.le.{0} Nat instLENat N r →
                                  And
                                    (@Eq.{1} Nat (s.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg r))
                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                    (@Eq.{1} Real (s.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg r))
                                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))) →
                              ∃ cost t,
                                And
                                  (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                    (DecrAlmostLinearSSSP.Decremental.Native.prepareBank N) s cost t)
                                  (And
                                    (@LE.le.{0} Nat instLENat cost
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) N)
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (DecrAlmostLinearSSSP.Decremental.dispatchCharge
                                                    DecrAlmostLinearSSSP.Decremental.ScaledCeiling.ceilingProgram.code)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))
                                                    (DecrAlmostLinearSSSP.Decremental.utilityDepth i.size))
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))))))
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) i.k
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
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))
                                                      (DecrAlmostLinearSSSP.Decremental.utilityDepth i.size))
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))))
                                              (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))))
                                        (@OfNat.ofNat.{0} Nat (nat_lit 136) (instOfNatNat (nat_lit 136)))))
                                    (And
                                      (DecrAlmostLinearSSSP.Decremental.Native.Ready i j B utility record cache stride
                                        t)
                                      (And
                                        (DecrAlmostLinearSSSP.Decremental.Native.RecordImage i j record cache
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record
                                            stride)
                                          t)
                                        (And
                                          (DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B j t
                                            (DecrAlmostLinearSSSP.Decremental.initialMachine p
                                                (DecrAlmostLinearSSSP.Decremental.barrierInput i j)).natMem
                                            (DecrAlmostLinearSSSP.Decremental.initialMachine p
                                                (DecrAlmostLinearSSSP.Decremental.barrierInput i j)).realMem)
                                          (And
                                            (∀ (r : Nat),
                                              @LT.lt.{0} Nat instLTNat r N →
                                                And
                                                  (@Eq.{1} Nat
                                                    (t.natMem
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          record
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                          r)))
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (DecrAlmostLinearSSSP.Decremental.bankFactor j)
                                                      ((DecrAlmostLinearSSSP.Decremental.initialMachine p
                                                            (DecrAlmostLinearSSSP.Decremental.barrierInput i j)).natReg
                                                        r)))
                                                  (@Eq.{1} Real
                                                    (t.realMem
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          record
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                          r)))
                                                    ((DecrAlmostLinearSSSP.Decremental.initialMachine p
                                                          (DecrAlmostLinearSSSP.Decremental.barrierInput i j)).realReg
                                                      r)))
                                            (And
                                              (∀ (address : Nat),
                                                @LE.le.{0} Nat instLENat address B →
                                                  @Eq.{1} Nat (t.natMem address)
                                                    ((DecrAlmostLinearSSSP.Decremental.initialMachine p i).natMem
                                                      address))
                                              (And
                                                (∀ (r : Nat),
                                                  @LE.le.{0} Nat instLENat N r →
                                                    And
                                                      (@Eq.{1} Nat
                                                        (t.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg r))
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                      (@Eq.{1} Real
                                                        (t.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg r))
                                                        (@OfNat.ofNat.{0} Real (nat_lit 0)
                                                          (@Zero.toOfNat0.{0} Real Real.instZero))))
                                                (∀ (address : Nat),
                                                  (∀ (r : Nat),
                                                      @LT.lt.{0} Nat instLTNat r
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat) N
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                              (instOfNatNat (nat_lit 4)))) →
                                                        @Ne.{1} Nat address
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat) record
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                (instOfNatNat (nat_lit 2)))
                                                              r))) →
                                                    (∀ (v : Nat),
                                                        @LT.lt.{0} Nat instLTNat v
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 3)
                                                                (instOfNatNat (nat_lit 3)))
                                                              i.k) →
                                                          @Ne.{1} Nat address
                                                            (DecrAlmostLinearSSSP.Decremental.bankAddress B j
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat) i.n v))) →
                                                      (∀ (a : Nat),
                                                          @Ne.{1} Nat address
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat) utility
                                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                  (@instHMul.{0} Nat instMulNat)
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                    (instOfNatNat (nat_lit 2)))
                                                                  a))
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                (instOfNatNat (nat_lit 1))))) →
                                                        And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                                          (@Eq.{1} Real (t.realMem address) (s.realMem address)))))))))))) ∧ ((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (C : Real) (a : Nat → Real) (queryBound : Nat)
  (i : DecrAlmostLinearSSSP.Decremental.Input),
  DecrAlmostLinearSSSP.Decremental.Maintains p C a queryBound Bool.false i →
    ∀ (B bank : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))) B →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))))
            (DecrAlmostLinearSSSP.Decremental.bankFactor bank) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
            @Eq.{1} Nat
                (s.natMem
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
              (∀ (addr : Nat),
                  @Eq.{1} Real
                    (s.realMem
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) addr)
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                    ((DecrAlmostLinearSSSP.Decremental.initialMachine p i).realMem addr)) →
                (∀ (addr : Nat),
                    @Eq.{1} Nat
                      (s.natMem
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) addr)
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
                        ((DecrAlmostLinearSSSP.Decremental.initialMachine p i).natMem addr))) →
                  (∀ (j : Nat),
                      @LT.lt.{0} Nat instLTNat j (DecrAlmostLinearSSSP.Decremental.registerBound p.code) →
                        And
                          (@Eq.{1} Nat
                            (s.natMem
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
                              ((DecrAlmostLinearSSSP.Decremental.initialMachine p i).natReg j)))
                          (@Eq.{1} Real
                            (s.realMem
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
                            ((DecrAlmostLinearSSSP.Decremental.initialMachine p i).realReg j))) →
                    (∀ (j : Nat),
                        @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.registerBound p.code) j →
                          And
                            (@Eq.{1} Nat (s.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg j))
                              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                            (@Eq.{1} Real (s.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg j))
                              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))) →
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
                          ∃ final cost t,
                            And
                              (DecrAlmostLinearSSSP.Decremental.Ends p
                                (DecrAlmostLinearSSSP.Decremental.initialMachine p i) final)
                              (And
                                (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                  (DecrAlmostLinearSSSP.Decremental.SourceCall.code
                                    (DecrAlmostLinearSSSP.Decremental.registerBound p.code) p.initPC p)
                                  s cost t)
                                (And
                                  (@LE.le.{0} Nat instLENat cost
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (DecrAlmostLinearSSSP.Decremental.dispatchCharge p.code)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                          final.work)
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                                          (DecrAlmostLinearSSSP.Decremental.registerBound p.code)))
                                      (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))))
                                  (And
                                    (DecrAlmostLinearSSSP.Decremental.ShadowDataRep B
                                      (DecrAlmostLinearSSSP.Decremental.bankFactor bank) t final)
                                    (And
                                      (DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail
                                        (DecrAlmostLinearSSSP.Decremental.registerBound p.code) final)
                                      (And
                                        (@Eq.{1} ENNReal
                                          (DecrAlmostLinearSSSP.Decremental.stored final (@Fin.val i.n i.source))
                                          (@OfNat.ofNat.{0} ENNReal (nat_lit 0)
                                            (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero)))
                                        (And
                                          (∀ (v : Fin i.n),
                                            And
                                              (@LE.le.{0} Nat instLENat (final.natMem (@Fin.val i.n v))
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                              (@Eq.{1} Nat (final.natMem (@Fin.val i.n v))
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                                                @LE.le.{0} Real Real.instLE
                                                  (@OfNat.ofNat.{0} Real (nat_lit 0)
                                                    (@Zero.toOfNat0.{0} Real Real.instZero))
                                                  (final.realMem (@Fin.val i.n v))))
                                          (And
                                            (∀ (v : Fin i.n),
                                              And
                                                (@LE.le.{0} ENNReal ENNReal.instLE (i.dist (@List.nil.{0} (Fin i.k)) v)
                                                  (DecrAlmostLinearSSSP.Decremental.stored final (@Fin.val i.n v)))
                                                (And
                                                  (@LE.le.{0} ENNReal ENNReal.instLE
                                                    (DecrAlmostLinearSSSP.Decremental.stored final (@Fin.val i.n v))
                                                    (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                                                      (@instHMul.{0} ENNReal
                                                        (@Distrib.toMul.{0} ENNReal
                                                          (@instDistribOfSemiring.{0} ENNReal
                                                            (@CommSemiring.toSemiring.{0} ENNReal
                                                              ENNReal.instCommSemiring))))
                                                      (ENNReal.ofReal
                                                        (@HAdd.hAdd.{0, 0, 0} Real Real Real
                                                          (@instHAdd.{0} Real Real.instAdd)
                                                          (@OfNat.ofNat.{0} Real (nat_lit 1)
                                                            (@One.toOfNat1.{0} Real Real.instOne))
                                                          i.accuracy))
                                                      (i.dist (@List.nil.{0} (Fin i.k)) v)))
                                                  (Iff
                                                    (@Eq.{1} ENNReal
                                                      (DecrAlmostLinearSSSP.Decremental.stored final (@Fin.val i.n v))
                                                      (@Top.top.{0} ENNReal ENNReal.instTop))
                                                    (Not
                                                      (@DecrAlmostLinearSSSP.Decremental.Reachable i.n i.k i.graph
                                                        (@DecrAlmostLinearSSSP.Decremental.live i.k
                                                          (@List.nil.{0} (Fin i.k)))
                                                        i.source v)))))
                                            (And
                                              (@LE.le.{0} Real Real.instLE
                                                (@Nat.cast.{0} Real Real.instNatCast final.work)
                                                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                                  (@instHDiv.{0} Real
                                                    (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                    (@HMul.hMul.{0, 0, 0} Real Real Real
                                                      (@instHMul.{0} Real Real.instMul) C
                                                      (@Nat.cast.{0} Real Real.instNatCast i.size))
                                                    (a i.size))
                                                  i.accuracy))
                                              (And
                                                (@Eq.{1} Nat
                                                  (t.natMem
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (s.natReg
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 106)
                                                          (instOfNatNat (nat_lit 106))))
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
                                                  final.work)
                                                (And
                                                  (∀ (j : Nat),
                                                    @LT.lt.{0} Nat instLTNat j
                                                        (DecrAlmostLinearSSSP.Decremental.registerBound p.code) →
                                                      And
                                                        (@Eq.{1} Nat
                                                          (t.natMem
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (s.natReg
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 50)
                                                                  (instOfNatNat (nat_lit 50))))
                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                (@instHMul.{0} Nat instMulNat)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                  (instOfNatNat (nat_lit 2)))
                                                                j)))
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
                                                            (final.natReg j)))
                                                        (@Eq.{1} Real
                                                          (t.realMem
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (s.natReg
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 50)
                                                                  (instOfNatNat (nat_lit 50))))
                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                (@instHMul.{0} Nat instMulNat)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                  (instOfNatNat (nat_lit 2)))
                                                                j)))
                                                          (final.realReg j)))
                                                  (∀ (address : Nat),
                                                    (∀ (addr : Nat),
                                                        @Ne.{1} Nat address
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat) B
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat)
                                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                  (@instHMul.{0} Nat instMulNat)
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                    (instOfNatNat (nat_lit 2)))
                                                                  addr)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                  (instOfNatNat (nat_lit 1))))))) →
                                                      @Ne.{1} Nat address
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat)
                                                            (s.natReg
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 106)
                                                                (instOfNatNat (nat_lit 106))))
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 6)
                                                              (instOfNatNat (nat_lit 6)))) →
                                                        (∀ (j : Nat),
                                                            @LT.lt.{0} Nat instLTNat j
                                                                (DecrAlmostLinearSSSP.Decremental.registerBound
                                                                  p.code) →
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
                                                            (@Eq.{1} Real (t.realMem address)
                                                              (s.realMem address)))))))))))))) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 128) (instOfNatNat (nat_lit 128))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 130) (instOfNatNat (nat_lit 130))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 132) (instOfNatNat (nat_lit 132))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 170) (instOfNatNat (nat_lit 170))) →
              @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 176) (instOfNatNat (nat_lit 176))) →
                DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CacheCopy.call k))) ∧ (((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CacheCopy.call k) ∧ (DecrAlmostLinearSSSP.Decremental.TailFrame DecrAlmostLinearSSSP.Decremental.CacheCopy.call)) ∧ ((DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame DecrAlmostLinearSSSP.Decremental.CacheCopy.call) ∧ ((DecrAlmostLinearSSSP.Decremental.Native.BankFrame DecrAlmostLinearSSSP.Decremental.CacheCopy.call) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {j B record cache next N : Nat}
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
        DecrAlmostLinearSSSP.Decremental.Native.RecordImage i j record cache next t))))) ∧ ((((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {j record cache next count : Nat}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.RecordImage i j record cache next s →
    @LT.lt.{0} Nat instLTNat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        cache →
      (∀ (address : Nat),
          (∀ (v : Nat),
              @LT.lt.{0} Nat instLTNat v count →
                @Ne.{1} Nat address
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cache
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) v))) →
            And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
              (@Eq.{1} Real (t.realMem address) (s.realMem address))) →
        DecrAlmostLinearSSSP.Decremental.Native.RecordImage i j record cache next t) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (C : Real) (a : Nat → Real) (queryBound : Nat),
      @LT.lt.{0} Real Real.instLT
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@Nat.cast.{0} Real Real.instNatCast i.size))
          i.accuracy →
        ∀ (j B utility record cache stride : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
          DecrAlmostLinearSSSP.Decremental.Maintains p C a queryBound Bool.false
              (DecrAlmostLinearSSSP.Decremental.barrierInput i j) →
            DecrAlmostLinearSSSP.Decremental.Native.Globals i B utility s →
              DecrAlmostLinearSSSP.Decremental.Native.BankEnv j record cache stride s →
                (∃ r,
                    @Eq.{1} Nat record
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                  (∃ c,
                      @Eq.{1} Nat cache
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) c))
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                    (∃ u,
                        @Eq.{1} Nat utility
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) u))) →
                      (∀ (r : Nat),
                          @LT.lt.{0} Nat instLTNat r (DecrAlmostLinearSSSP.Decremental.registerBound p.code) →
                            @LT.lt.{0} Nat instLTNat
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record
                                  (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
                              utility) →
                        @LT.lt.{0} Nat instLTNat
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (DecrAlmostLinearSSSP.Decremental.registerBound p.code)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                            cache →
                          @LE.le.{0} Nat instLENat
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
                              B →
                            (DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B j s
                                (fun x => @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) fun x =>
                                @OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
                              (∀ (address : Nat),
                                  @LE.le.{0} Nat instLENat address B →
                                    @Eq.{1} Nat (s.natMem address)
                                      ((DecrAlmostLinearSSSP.Decremental.initialMachine p i).natMem address)) →
                                (∀ (r : Nat),
                                    @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.registerBound p.code) r →
                                      And
                                        (@Eq.{1} Nat (s.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg r))
                                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                        (@Eq.{1} Real (s.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg r))
                                          (@OfNat.ofNat.{0} Real (nat_lit 0)
                                            (@Zero.toOfNat0.{0} Real Real.instZero)))) →
                                  ∃ final cost t,
                                    And
                                      (DecrAlmostLinearSSSP.Decremental.Ends p
                                        (DecrAlmostLinearSSSP.Decremental.initialMachine p
                                          (DecrAlmostLinearSSSP.Decremental.barrierInput i j))
                                        final)
                                      (And
                                        (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                          (DecrAlmostLinearSSSP.Decremental.Native.initializeScale p) s cost t)
                                        (And
                                          (@LE.le.{0} Nat instLENat cost
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (DecrAlmostLinearSSSP.Decremental.dispatchCharge p.code)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                        final.work)
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))
                                                        (DecrAlmostLinearSSSP.Decremental.registerBound p.code)))
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (DecrAlmostLinearSSSP.Decremental.dispatchCharge
                                                            DecrAlmostLinearSSSP.Decremental.ScaledCeiling.ceilingProgram.code)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 16)
                                                              (instOfNatNat (nat_lit 16)))
                                                            (DecrAlmostLinearSSSP.Decremental.utilityDepth i.size))
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 32)
                                                            (instOfNatNat (nat_lit 32)))))))
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) i.k
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
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
                                                              (instOfNatNat (nat_lit 32))))))
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))))
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13))) i.n))
                                              (@OfNat.ofNat.{0} Nat (nat_lit 158) (instOfNatNat (nat_lit 158)))))
                                          (And (DecrAlmostLinearSSSP.Decremental.Native.Globals i B utility t)
                                            (And
                                              (DecrAlmostLinearSSSP.Decremental.Native.BankEnv j record cache stride t)
                                              (And
                                                (DecrAlmostLinearSSSP.Decremental.Native.RecordImage i j record cache
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    record stride)
                                                  t)
                                                (And
                                                  (DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B j t
                                                    final.natMem final.realMem)
                                                  (And
                                                    (@Eq.{1} Nat
                                                      (t.natMem
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          record
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 6)
                                                            (instOfNatNat (nat_lit 6)))))
                                                      final.work)
                                                    (And
                                                      (∀ (r : Nat),
                                                        @LT.lt.{0} Nat instLTNat r
                                                            (DecrAlmostLinearSSSP.Decremental.registerBound p.code) →
                                                          And
                                                            (@Eq.{1} Nat
                                                              (t.natMem
                                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                  (@instHAdd.{0} Nat instAddNat)
                                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                    (@instHAdd.{0} Nat instAddNat) record
                                                                    (@OfNat.ofNat.{0} Nat (nat_lit 8)
                                                                      (instOfNatNat (nat_lit 8))))
                                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                    (@instHMul.{0} Nat instMulNat)
                                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                      (instOfNatNat (nat_lit 2)))
                                                                    r)))
                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                (@instHMul.{0} Nat instMulNat)
                                                                (DecrAlmostLinearSSSP.Decremental.bankFactor j)
                                                                (final.natReg r)))
                                                            (@Eq.{1} Real
                                                              (t.realMem
                                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                  (@instHAdd.{0} Nat instAddNat)
                                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                    (@instHAdd.{0} Nat instAddNat) record
                                                                    (@OfNat.ofNat.{0} Nat (nat_lit 8)
                                                                      (instOfNatNat (nat_lit 8))))
                                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                    (@instHMul.{0} Nat instMulNat)
                                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                      (instOfNatNat (nat_lit 2)))
                                                                    r)))
                                                              (final.realReg r)))
                                                      (And
                                                        (∀ (v : Fin i.n),
                                                          And
                                                            (@Eq.{1} Nat
                                                              (t.natMem
                                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                  (@instHAdd.{0} Nat instAddNat) cache
                                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                    (@instHMul.{0} Nat instMulNat)
                                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                      (instOfNatNat (nat_lit 2)))
                                                                    (@Fin.val i.n v))))
                                                              (final.natMem (@Fin.val i.n v)))
                                                            (And
                                                              (@Eq.{1} Real
                                                                (t.realMem
                                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                    (@instHAdd.{0} Nat instAddNat) cache
                                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                      (@instHMul.{0} Nat instMulNat)
                                                                      (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                        (instOfNatNat (nat_lit 2)))
                                                                      (@Fin.val i.n v))))
                                                                (@HMul.hMul.{0, 0, 0} Real Real Real
                                                                  (@instHMul.{0} Real Real.instMul)
                                                                  (DecrAlmostLinearSSSP.Decremental.delta i j)
                                                                  (final.realMem (@Fin.val i.n v))))
                                                              (@Eq.{1} ENNReal
                                                                (DecrAlmostLinearSSSP.Decremental.ExtendedMax.cell t
                                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                    (@instHAdd.{0} Nat instAddNat) cache
                                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                      (@instHMul.{0} Nat instMulNat)
                                                                      (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                        (instOfNatNat (nat_lit 2)))
                                                                      (@Fin.val i.n v))))
                                                                (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                                                                  (@instHMul.{0} ENNReal
                                                                    (@Distrib.toMul.{0} ENNReal
                                                                      (@instDistribOfSemiring.{0} ENNReal
                                                                        (@CommSemiring.toSemiring.{0} ENNReal
                                                                          ENNReal.instCommSemiring))))
                                                                  (ENNReal.ofReal
                                                                    (DecrAlmostLinearSSSP.Decremental.delta i j))
                                                                  (DecrAlmostLinearSSSP.Decremental.stored final
                                                                    (@Fin.val i.n v))))))
                                                        (And
                                                          (∀ (v : Fin i.n),
                                                            And
                                                              (@LE.le.{0} Nat instLENat (final.natMem (@Fin.val i.n v))
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                  (instOfNatNat (nat_lit 1))))
                                                              (@Eq.{1} Nat (final.natMem (@Fin.val i.n v))
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 0)
                                                                    (instOfNatNat (nat_lit 0))) →
                                                                @LE.le.{0} Real Real.instLE
                                                                  (@OfNat.ofNat.{0} Real (nat_lit 0)
                                                                    (@Zero.toOfNat0.{0} Real Real.instZero))
                                                                  (final.realMem (@Fin.val i.n v))))
                                                          (And
                                                            (∀ (v : Fin i.n),
                                                              And
                                                                (@LE.le.{0} ENNReal ENNReal.instLE
                                                                  ((DecrAlmostLinearSSSP.Decremental.barrierInput i
                                                                        j).dist
                                                                    (@List.nil.{0}
                                                                      (Fin
                                                                        (DecrAlmostLinearSSSP.Decremental.barrierInput i
                                                                            j).k))
                                                                    v)
                                                                  (DecrAlmostLinearSSSP.Decremental.stored final
                                                                    (@Fin.val i.n v)))
                                                                (And
                                                                  (@LE.le.{0} ENNReal ENNReal.instLE
                                                                    (DecrAlmostLinearSSSP.Decremental.stored final
                                                                      (@Fin.val i.n v))
                                                                    (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                                                                      (@instHMul.{0} ENNReal
                                                                        (@Distrib.toMul.{0} ENNReal
                                                                          (@instDistribOfSemiring.{0} ENNReal
                                                                            (@CommSemiring.toSemiring.{0} ENNReal
                                                                              ENNReal.instCommSemiring))))
                                                                      (ENNReal.ofReal
                                                                        (@HAdd.hAdd.{0, 0, 0} Real Real Real
                                                                          (@instHAdd.{0} Real Real.instAdd)
                                                                          (@OfNat.ofNat.{0} Real (nat_lit 1)
                                                                            (@One.toOfNat1.{0} Real Real.instOne))
                                                                          (DecrAlmostLinearSSSP.Decremental.barrierInput
                                                                              i j).accuracy))
                                                                      ((DecrAlmostLinearSSSP.Decremental.barrierInput i
                                                                            j).dist
                                                                        (@List.nil.{0}
                                                                          (Fin
                                                                            (DecrAlmostLinearSSSP.Decremental.barrierInput
                                                                                i j).k))
                                                                        v)))
                                                                  (Iff
                                                                    (@Eq.{1} ENNReal
                                                                      (DecrAlmostLinearSSSP.Decremental.stored final
                                                                        (@Fin.val i.n v))
                                                                      (@Top.top.{0} ENNReal ENNReal.instTop))
                                                                    (Not
                                                                      (@DecrAlmostLinearSSSP.Decremental.Reachable i.n
                                                                        i.k i.graph
                                                                        (@DecrAlmostLinearSSSP.Decremental.live i.k
                                                                          (@List.nil.{0} (Fin i.k)))
                                                                        i.source v)))))
                                                            (And
                                                              (@LE.le.{0} Real Real.instLE
                                                                (@Nat.cast.{0} Real Real.instNatCast final.work)
                                                                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                                                  (@instHDiv.{0} Real
                                                                    (@DivInvMonoid.toDiv.{0} Real
                                                                      Real.instDivInvMonoid))
                                                                  (@HMul.hMul.{0, 0, 0} Real Real Real
                                                                    (@instHMul.{0} Real Real.instMul)
                                                                    (@HMul.hMul.{0, 0, 0} Real Real Real
                                                                      (@instHMul.{0} Real Real.instMul) C
                                                                      (@Nat.cast.{0} Real Real.instNatCast
                                                                        (DecrAlmostLinearSSSP.Decremental.barrierInput i
                                                                            j).size))
                                                                    (a
                                                                      (DecrAlmostLinearSSSP.Decremental.barrierInput i
                                                                          j).size))
                                                                  (DecrAlmostLinearSSSP.Decremental.barrierInput i
                                                                      j).accuracy))
                                                              (And
                                                                (∀ (r : Nat),
                                                                  @LE.le.{0} Nat instLENat
                                                                      (DecrAlmostLinearSSSP.Decremental.registerBound
                                                                        p.code)
                                                                      r →
                                                                    And
                                                                      (@Eq.{1} Nat
                                                                        (t.natReg
                                                                          (DecrAlmostLinearSSSP.Decremental.shadowReg
                                                                            r))
                                                                        (@OfNat.ofNat.{0} Nat (nat_lit 0)
                                                                          (instOfNatNat (nat_lit 0))))
                                                                      (@Eq.{1} Real
                                                                        (t.realReg
                                                                          (DecrAlmostLinearSSSP.Decremental.shadowReg
                                                                            r))
                                                                        (@OfNat.ofNat.{0} Real (nat_lit 0)
                                                                          (@Zero.toOfNat0.{0} Real Real.instZero))))
                                                                (∀ (address : Nat),
                                                                  (∀ (r : Nat),
                                                                      @LT.lt.{0} Nat instLTNat r
                                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                            (@instHAdd.{0} Nat instAddNat)
                                                                            (DecrAlmostLinearSSSP.Decremental.registerBound
                                                                              p.code)
                                                                            (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                              (instOfNatNat (nat_lit 4)))) →
                                                                        @Ne.{1} Nat address
                                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                            (@instHAdd.{0} Nat instAddNat) record
                                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                              (@instHMul.{0} Nat instMulNat)
                                                                              (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                                (instOfNatNat (nat_lit 2)))
                                                                              r))) →
                                                                    (∀ (v : Nat),
                                                                        @Ne.{1} Nat address
                                                                          (DecrAlmostLinearSSSP.Decremental.bankAddress
                                                                            B j v)) →
                                                                      (∀ (v : Nat),
                                                                          @LT.lt.{0} Nat instLTNat v i.n →
                                                                            @Ne.{1} Nat address
                                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                                (@instHAdd.{0} Nat instAddNat) cache
                                                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                                  (@instHMul.{0} Nat instMulNat)
                                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                                    (instOfNatNat (nat_lit 2)))
                                                                                  v))) →
                                                                        (∀ (v : Nat),
                                                                            @Ne.{1} Nat address
                                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                                (@instHAdd.{0} Nat instAddNat)
                                                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                                  (@instHAdd.{0} Nat instAddNat) utility
                                                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                                    (@instHMul.{0} Nat instMulNat)
                                                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                                      (instOfNatNat (nat_lit 2)))
                                                                                    v))
                                                                                (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                                  (instOfNatNat (nat_lit 1))))) →
                                                                          And
                                                                            (@Eq.{1} Nat (t.natMem address)
                                                                              (s.natMem address))
                                                                            (@Eq.{1} Real (t.realMem address)
                                                                              (s.realMem address)))))))))))))))))) ∧ ((∀ {a b : DecrAlmostLinearSSSP.Decremental.Structured.Cmd},
  DecrAlmostLinearSSSP.Decremental.Native.ControlFrame a →
    DecrAlmostLinearSSSP.Decremental.Native.ControlFrame b →
      DecrAlmostLinearSSSP.Decremental.Native.ControlFrame (a.seq b)) ∧ ((DecrAlmostLinearSSSP.Decremental.Native.ControlFrame DecrAlmostLinearSSSP.Decremental.RecordHeader.code) ∧ (∀ (N : Nat), DecrAlmostLinearSSSP.Decremental.Native.ControlFrame (DecrAlmostLinearSSSP.Decremental.SnapshotFill.code N))))) ∧ (((DecrAlmostLinearSSSP.Decremental.Native.ControlFrame DecrAlmostLinearSSSP.Decremental.ScaleParameters.prepare) ∧ (DecrAlmostLinearSSSP.Decremental.Native.ControlFrame DecrAlmostLinearSSSP.Decremental.ScaleParameters.writeFields)) ∧ ((∀ (N : Nat),
  DecrAlmostLinearSSSP.Decremental.Native.ControlFrame
    (DecrAlmostLinearSSSP.Decremental.ScaleParameters.initializeSnapshot N)) ∧ ((DecrAlmostLinearSSSP.Decremental.Native.ControlFrame DecrAlmostLinearSSSP.Decremental.TapeCopy.start) ∧ (DecrAlmostLinearSSSP.Decremental.Native.ControlFrame DecrAlmostLinearSSSP.Decremental.TapeCopy.naturalField)))))))) := by
  exact ⟨⟨⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Native.globalFrame_header,DecrAlmostLinearSSSP.Decremental.Native.globalFrame_snapshotFill⟩,⟨DecrAlmostLinearSSSP.Decremental.Native.globalFrame_prepare,DecrAlmostLinearSSSP.Decremental.Native.globalFrame_fields⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Native.globalFrame_initializeSnapshot,DecrAlmostLinearSSSP.Decremental.Native.globalFrame_tapeStart⟩,⟨DecrAlmostLinearSSSP.Decremental.Native.globalFrame_naturalField,⟨DecrAlmostLinearSSSP.Decremental.Native.globalFrame_weightField,DecrAlmostLinearSSSP.Decremental.Native.globalFrame_tapeEdge⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Native.globalFrame_tapeLoop,DecrAlmostLinearSSSP.Decremental.Native.globalFrame_sourceCall⟩,⟨DecrAlmostLinearSSSP.Decremental.Prepass.code_vertex_stride,DecrAlmostLinearSSSP.Decremental.Prepass.globals_after⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Native.BankFrame.seq,DecrAlmostLinearSSSP.Decremental.Native.BankFrame.loop⟩,⟨DecrAlmostLinearSSSP.Decremental.Native.BankEnv.transfer,⟨DecrAlmostLinearSSSP.Decremental.Native.bankFrame_header,DecrAlmostLinearSSSP.Decremental.Native.bankFrame_snapshotFill⟩⟩⟩⟩⟩,⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Native.bankFrame_prepare,DecrAlmostLinearSSSP.Decremental.Native.bankFrame_fields⟩,⟨DecrAlmostLinearSSSP.Decremental.Native.bankFrame_tapeStart,DecrAlmostLinearSSSP.Decremental.Native.bankFrame_naturalField⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Native.bankFrame_weightField,DecrAlmostLinearSSSP.Decremental.Native.bankFrame_sourceCall⟩,⟨DecrAlmostLinearSSSP.Decremental.Native.bankFrame_initializeSnapshot,⟨DecrAlmostLinearSSSP.Decremental.Native.bankFrame_tapeEdge,DecrAlmostLinearSSSP.Decremental.Native.bankFrame_tapeLoop⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Native.header_ready,DecrAlmostLinearSSSP.Decremental.Native.snapshot_extra_real_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.Native.snapshot_ready,⟨DecrAlmostLinearSSSP.Decremental.TapeCopy.edgeImage_outside,DecrAlmostLinearSSSP.Decremental.TapeCopy.tapeImage_outside⟩⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.TapeCopy.tapeImage_fields,DecrAlmostLinearSSSP.Decremental.TapeCopy.roundedWeight_barrier⟩,⟨DecrAlmostLinearSSSP.Decremental.TapeCopy.tapeImage_barrier,⟨DecrAlmostLinearSSSP.Decremental.TapeCopy.ordinary_argument_bound,DecrAlmostLinearSSSP.Decremental.TapeCopy.low_weight_argument_bound⟩⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.TapeCopy.barrier_eval,DecrAlmostLinearSSSP.Decremental.TapeCopy.ConstantFrame.seq⟩,⟨DecrAlmostLinearSSSP.Decremental.TapeCopy.constantFrame_start,DecrAlmostLinearSSSP.Decremental.TapeCopy.constantFrame_natural⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.TapeCopy.constantFrame_weight,DecrAlmostLinearSSSP.Decremental.TapeCopy.constantFrame_edge⟩,⟨DecrAlmostLinearSSSP.Decremental.TapeCopy.constantFrame_loop,⟨DecrAlmostLinearSSSP.Decremental.tailFrame_skip,DecrAlmostLinearSSSP.Decremental.tailFrame_tapeFinish⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.tailFrame_naturalField,DecrAlmostLinearSSSP.Decremental.tailFrame_weightChoice⟩,⟨DecrAlmostLinearSSSP.Decremental.tailFrame_weightField,⟨DecrAlmostLinearSSSP.Decremental.tailFrame_tapeEdge,DecrAlmostLinearSSSP.Decremental.tailFrame_tapeLoop⟩⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Native.host_record_ne_bank,DecrAlmostLinearSSSP.Decremental.Native.tape_ready⟩,⟨DecrAlmostLinearSSSP.Decremental.Native.RecordImage.frame,⟨DecrAlmostLinearSSSP.Decremental.Native.recordImage_header,DecrAlmostLinearSSSP.Decremental.Native.RecordImage.snapshot_frame⟩⟩⟩⟩⟩,⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Native.RecordImage.tape_frame,DecrAlmostLinearSSSP.Decremental.Native.prepareBank_eval⟩,⟨DecrAlmostLinearSSSP.Decremental.SourceCall.initialize_from_maintains,DecrAlmostLinearSSSP.Decremental.CacheCopy.call_nat_frame⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.CacheCopy.call_real_frame,DecrAlmostLinearSSSP.Decremental.CacheCopy.tailFrame_call⟩,⟨DecrAlmostLinearSSSP.Decremental.Native.globalFrame_cacheCall,⟨DecrAlmostLinearSSSP.Decremental.Native.bankFrame_cacheCall,DecrAlmostLinearSSSP.Decremental.Native.RecordImage.source_frame⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Native.RecordImage.cache_frame,DecrAlmostLinearSSSP.Decremental.Native.initializeScale_eval⟩,⟨DecrAlmostLinearSSSP.Decremental.Native.ControlFrame.seq,⟨DecrAlmostLinearSSSP.Decremental.Native.controlFrame_header,DecrAlmostLinearSSSP.Decremental.Native.controlFrame_snapshotFill⟩⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Native.controlFrame_prepare,DecrAlmostLinearSSSP.Decremental.Native.controlFrame_fields⟩,⟨DecrAlmostLinearSSSP.Decremental.Native.controlFrame_initializeSnapshot,⟨DecrAlmostLinearSSSP.Decremental.Native.controlFrame_tapeStart,DecrAlmostLinearSSSP.Decremental.Native.controlFrame_naturalField⟩⟩⟩⟩⟩⟩⟩
