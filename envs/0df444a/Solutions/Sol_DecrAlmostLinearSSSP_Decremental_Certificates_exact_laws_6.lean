-- Prove2me | solution 1 for DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_6
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T11:14:38.919533+00:00
-- url     : https://prove2.me/submissions/3ad4f5d3-0294-4916-885e-4c0296023d19

import Definitions.Def_DecrAlmostLinearSSSP_RAMFoundation
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_1
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_2
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_3
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_4
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_5
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
open scoped ENNReal NNReal
attribute [local instance] Classical.propDecidable
theorem DecrAlmostLinearSSSP.Decremental.RadixQueue.entries_card : ∀ {height : Nat} (t : DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height) (low : Nat),
  @Eq.{1} Nat
    (@Multiset.card.{0} (Prod.{0, 0} Nat Nat) (@DecrAlmostLinearSSSP.Decremental.RadixQueue.entries height t low))
    (@DecrAlmostLinearSSSP.Decremental.RadixQueue.count height t) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_1.1.1.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.RadixQueue.entries_insert : ∀ (height key value : Nat) (t : DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height) (low : Nat),
  @LT.lt.{0} Nat instLTNat key
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) height) →
    @Eq.{1} (Multiset.{0} (Prod.{0, 0} Nat Nat))
      (@DecrAlmostLinearSSSP.Decremental.RadixQueue.entries height
        (DecrAlmostLinearSSSP.Decremental.RadixQueue.insert height key value t) low)
      (@Multiset.cons.{0} (Prod.{0, 0} Nat Nat)
        (@Prod.mk.{0, 0} Nat Nat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) low key) value)
        (@DecrAlmostLinearSSSP.Decremental.RadixQueue.entries height t low)) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_1.1.1.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.RadixQueue.pop_spec : ∀ {height : Nat} (t : DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height) (low key value : Nat)
  (next : DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height),
  @Eq.{1} (Option.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height))))
      (@DecrAlmostLinearSSSP.Decremental.RadixQueue.pop height t)
      (@Option.some.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height)))
        (@Prod.mk.{0, 0} Nat (Prod.{0, 0} Nat (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height)) key
          (@Prod.mk.{0, 0} Nat (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height) value next))) →
    And
      (@Eq.{1} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (@DecrAlmostLinearSSSP.Decremental.RadixQueue.entries height t low)
        (@Multiset.cons.{0} (Prod.{0, 0} Nat Nat)
          (@Prod.mk.{0, 0} Nat Nat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) low key) value)
          (@DecrAlmostLinearSSSP.Decremental.RadixQueue.entries height next low)))
      (∀ (item : Prod.{0, 0} Nat Nat),
        @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Multiset.{0} (Prod.{0, 0} Nat Nat))
            (@Multiset.instMembership.{0} (Prod.{0, 0} Nat Nat))
            (@DecrAlmostLinearSSSP.Decremental.RadixQueue.entries height t low) item →
          @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) low key)
            (@Prod.fst.{0, 0} Nat Nat item)) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_1.1.1.1.2.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.Exact.Powers.prepare_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.Powers.prepare s
    (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))
    (DecrAlmostLinearSSSP.Decremental.Exact.Powers.prepared s) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.1.2.2.2.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.Walk.append : ∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {u v w : Fin n}
  {es fs : List.{0} (Fin k)},
  @DecrAlmostLinearSSSP.Decremental.Walk n k g active u v es →
    @DecrAlmostLinearSSSP.Decremental.Walk n k g active v w fs →
      @DecrAlmostLinearSSSP.Decremental.Walk n k g active u w
        (@HAppend.hAppend.{0, 0, 0} (List.{0} (Fin k)) (List.{0} (Fin k)) (List.{0} (Fin k))
          (@instHAppendOfAppend.{0} (List.{0} (Fin k)) (@List.instAppend.{0} (Fin k))) es fs) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.2.1.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.Reachable.trans : ∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {u v w : Fin n},
  @DecrAlmostLinearSSSP.Decremental.Reachable n k g active u v →
    @DecrAlmostLinearSSSP.Decremental.Reachable n k g active v w →
      @DecrAlmostLinearSSSP.Decremental.Reachable n k g active u w := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.2.1.2.2.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.distance_top_of_unreachable : ∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (active : Finset.{0} (Fin k)) (w : Fin k → ENNReal)
  (u v : Fin n),
  Not (@DecrAlmostLinearSSSP.Decremental.Reachable n k g active u v) →
    @Eq.{1} ENNReal (@DecrAlmostLinearSSSP.Decremental.distance n k g active w u v)
      (@Top.top.{0} ENNReal ENNReal.instTop) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.2.2.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.cappedDistance_bounds : ∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (active : Finset.{0} (Fin k)) (w : Fin k → Real)
  (B : Real),
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) B →
    ∀ (u v : Fin n),
      And
        (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (@DecrAlmostLinearSSSP.Decremental.cappedDistance n k g active w B u v))
        (@LE.le.{0} Real Real.instLE (@DecrAlmostLinearSSSP.Decremental.cappedDistance n k g active w B u v) B) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.2.2.2.2.2.2.2
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
lemma distance_unreachable {n k : ℕ} (g : Digraph n k) (active : Finset (Fin k))
    (w : Fin k → ℝ≥0∞) (u v : Fin n) (hr : ¬ Reachable g active u v) :
    distance g active w u v = ⊤ := by
  apply le_antisymm le_top
  apply le_iInf
  intro es
  apply le_iInf
  intro he
  exact False.elim (hr ⟨es, he⟩)
lemma cappedDistance_unreachable {n k : ℕ} (g : Digraph n k) (active : Finset (Fin k))
    (w : Fin k → ℝ) (B : ℝ) (hB : 0 ≤ B) (u v : Fin n) (hr : ¬ Reachable g active u v) :
    cappedDistance g active w B u v = B := by
  rw [cappedDistance, distance_unreachable g active _ u v hr, min_eq_left le_top, ENNReal.toReal_ofReal hB]
lemma cappedDistance_of_distance {n k : ℕ} (g : Digraph n k) (active : Finset (Fin k))
    (w : Fin k → ℝ) (B c : ℝ) (hB : 0 ≤ B) (hc : 0 ≤ c) (u v : Fin n)
    (hd : distance g active (fun e => ENNReal.ofReal (w e)) u v = ENNReal.ofReal c) :
    cappedDistance g active w B u v = min B c := by
  rw [cappedDistance, hd, ← ENNReal.ofReal_min, ENNReal.toReal_ofReal (le_min hB hc)]
lemma cappedDistance_self {n k : ℕ} (g : Digraph n k) (active : Finset (Fin k))
    (w : Fin k → ℝ) (B : ℝ) (hB : 0 ≤ B) (u : Fin n) :
    cappedDistance g active w B u u = 0 := by
  have hd : distance g active (fun e => ENNReal.ofReal (w e)) u u = 0 := by
    apply le_antisymm
    · simpa only [List.map_nil, List.sum_nil] using
        distance_le_walk (Walk.nil u : Walk g active u u []) (fun e => ENNReal.ofReal (w e))
    · exact zero_le
  rw [cappedDistance, hd, min_eq_right (show (0 : ℝ≥0∞) ≤ ENNReal.ofReal B from zero_le), ENNReal.toReal_zero]
lemma cappedDistance_lt_walk {n k : ℕ} (g : Digraph n k) (active : Finset (Fin k))
    (w : Fin k → ℝ) (hw : ∀ e, 0 ≤ w e) (B : ℝ) (hB : 0 ≤ B) (u v : Fin n)
    (hcap : cappedDistance g active w B u v < B) :
    ∃ es, Walk g active u v es ∧ (es.map w).sum = cappedDistance g active w B u v := by
  classical
  have hr : Reachable g active u v := by
    by_contra hn
    rw [cappedDistance_unreachable g active w B hB u v hn] at hcap
    exact (lt_irrefl B) hcap
  obtain ⟨es, he, hl, hd⟩ := distance_min_weight g active w hw u v hr
  have hc : 0 ≤ (es.map w).sum := List.sum_nonneg (by
    intro x hx
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp hx
    exact hw e)
  have hmin := cappedDistance_of_distance g active w B _ hB hc u v hd
  have hh : (es.map w).sum < B := by
    by_contra hn
    rw [hmin, min_eq_left (not_lt.mp hn)] at hcap
    exact (lt_irrefl B) hcap
  exact ⟨es, he, by simpa only [min_eq_right hh.le] using hmin.symm⟩
lemma cappedDistance_edge {n k : ℕ} (g : Digraph n k) (active : Finset (Fin k))
    (w : Fin k → ℝ) (hw : ∀ e, 0 ≤ w e) (B : ℝ) (hB : 0 ≤ B) (t : Fin n)
    (e : Fin k) (he : e ∈ active) :
    cappedDistance g active w B (g.tail e) t ≤ w e + cappedDistance g active w B (g.head e) t := by
  classical
  by_cases hr : Reachable g active (g.head e) t
  · obtain ⟨es, hes, _, hd⟩ := distance_min_weight g active w hw (g.head e) t hr
    have hwalk : Walk g active (g.tail e) t (e :: es) := Walk.cons (u := g.tail e) e he hes
    have hru : Reachable g active (g.tail e) t := ⟨e :: es, hwalk⟩
    obtain ⟨fs, hfs, _, hdu⟩ := distance_min_weight g active w hw (g.tail e) t hru
    have he0 : 0 ≤ (es.map w).sum := List.sum_nonneg (by
      intro x hx; obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx; exact hw a)
    have hf0 : 0 ≤ (fs.map w).sum := List.sum_nonneg (by
      intro x hx; obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx; exact hw a)
    rw [cappedDistance_of_distance g active w B _ hB hf0 _ _ hdu,
      cappedDistance_of_distance g active w B _ hB he0 _ _ hd]
    have hle := distance_le_walk hwalk (fun e => ENNReal.ofReal (w e))
    rw [hdu, list_sum_ofReal w hw] at hle
    simp only [List.map_cons, List.sum_cons] at hle
    have hr0 : 0 ≤ w e + (es.map w).sum := add_nonneg (hw e) he0
    have hreal := (ENNReal.ofReal_le_ofReal_iff hr0).mp hle
    by_cases hsmall : (es.map w).sum ≤ B
    · rw [min_eq_right hsmall]
      exact (min_le_right _ _).trans hreal
    · rw [min_eq_left (le_of_not_ge hsmall)]
      exact (min_le_left _ _).trans (by linarith [hw e])
  · rw [cappedDistance_unreachable g active w B hB _ _ hr]
    exact (cappedDistance_bounds g active w B hB _ _).2.trans (by linarith [hw e])
lemma Walk.label_le_weight {n k : ℕ} {g : Digraph n k} {active : Finset (Fin k)}
    {u v : Fin n} {es : List (Fin k)} (h : Walk g active u v es)
    (p : Fin n → ℝ) (w : Fin k → ℝ)
    (he : ∀ e ∈ active, p (g.tail e) - p (g.head e) ≤ w e) :
    p u - p v ≤ (es.map w).sum := by
  induction h with
  | nil v => simp
  | cons e hm h ih =>
    simp only [List.map_cons, List.sum_cons]
    linarith [he e hm]
lemma cappedDistance_label_bound {n k : ℕ} (g : Digraph n k) (active : Finset (Fin k))
    (w : Fin k → ℝ) (hw : ∀ e, 0 ≤ w e) (B : ℝ) (hB : 0 ≤ B) (u v : Fin n)
    (p : Fin n → ℝ) (he : ∀ e ∈ active, p (g.tail e) - p (g.head e) ≤ w e)
    (hcap : cappedDistance g active w B u v < B) :
    p u ≤ p v + cappedDistance g active w B u v := by
  obtain ⟨es, hes, hd⟩ := cappedDistance_lt_walk g active w hw B hB u v hcap
  have hh := hes.label_le_weight p w he
  rw [hd] at hh
  linarith
end DecrAlmostLinearSSSP.Decremental
end s85
section s86
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact
lemma nat_weight_real_sum {k : ℕ} (w : Fin k → ℕ) (es : List (Fin k)) :
    (((es.map w).sum : ℕ) : ℝ) = (es.map (fun e => (w e : ℝ))).sum := by
  induction es with
  | nil => simp
  | cons e es ih => simp [ih]
lemma nat_weight_upper {k : ℕ} (w : Fin k → ℕ) (W : ℕ) (hw : ∀ e, w e ≤ W) (es : List (Fin k)) :
    (es.map w).sum ≤ es.length*W := by
  induction es with
  | nil => simp
  | cons e es ih =>
    have he := hw e
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega
lemma reachable_nat_distance (i : Input) (hi : i.Valid) (active : Finset (Fin i.k)) (v : Fin i.n)
    (hr : Reachable i.graph active i.source v) :
    ∃ d : ℕ, d ≤ (i.n-1)*i.W ∧ distance i.graph active (fun e => (i.weight e : ℝ≥0∞)) i.source v = d := by
  obtain ⟨es,hes,hlen,hdist⟩ := distance_min_weight i.graph active (fun e => (i.weight e : ℝ))
    (fun e => Nat.cast_nonneg _) i.source v hr
  let d := (es.map i.weight).sum
  have hd : d ≤ (i.n-1)*i.W := by
    have hsum := nat_weight_upper i.weight i.W (fun e => (hi.2.2.2.2.2 e).2) es
    have hlength : es.length ≤ i.n-1 := by omega
    exact hsum.trans (Nat.mul_le_mul_right i.W hlength)
  refine ⟨d,hd,?_⟩
  rw [← nat_weight_real_sum i.weight es,ENNReal.ofReal_natCast] at hdist
  simpa only [ENNReal.ofReal_natCast] using hdist
lemma candidate_key_bound (i : Input) (hi : i.Valid) (active : Finset (Fin i.k)) (u : Fin i.n)
    (d : ℕ) (hd : distance i.graph active (fun e => (i.weight e : ℝ≥0∞)) i.source u = d)
    (hr : Reachable i.graph active i.source u) (e : Fin i.k) : d+i.weight e ≤ i.n*i.W := by
  obtain ⟨d',hd',hdeq⟩ := reachable_nat_distance i hi active u hr
  have heq : d = d' := by exact_mod_cast hd.symm.trans hdeq
  rw [heq]
  have hw := (hi.2.2.2.2.2 e).2
  have hn : 1 ≤ i.n := input_vertex_positive i
  calc
    d'+i.weight e ≤ (i.n-1)*i.W+i.W := Nat.add_le_add hd' hw
    _ = i.n*i.W := by rw [← Nat.add_one_mul,Nat.sub_add_cancel hn]
lemma nat_feasible_distance {n k : ℕ} (g : Digraph n k) (active : Finset (Fin k))
    (w : Fin k → ℕ) (s : Fin n) (z : Fin n → ℕ) (hs : z s = 0)
    (he : ∀ e ∈ active, z (g.head e) ≤ z (g.tail e)+w e) (v : Fin n) :
    (z v : ℝ≥0∞) ≤ distance g active (fun e => (w e : ℝ≥0∞)) s v := by
  simp only [← ENNReal.ofReal_natCast]
  unfold distance
  apply le_iInf
  intro es
  apply le_iInf
  intro hwalk
  rw [list_sum_ofReal _ (fun e => Nat.cast_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have hh := hwalk.label_le_weight (fun v => -(z v : ℝ)) (fun e => (w e : ℝ)) (by
    intro e he'
    have hNat := he e he'
    have hReal : (z (g.head e) : ℝ) ≤ (z (g.tail e) : ℝ)+(w e : ℝ) := by exact_mod_cast hNat
    linarith)
  simpa only [hs,Nat.cast_zero,neg_zero,zero_sub,neg_neg] using hh
end DecrAlmostLinearSSSP.Decremental.Exact
end s86
section s87
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact
lemma LabelInvariant.pop_exact {n k : ℕ} {g : Digraph n k} {active : Finset (Fin k)} {w : Fin k → ℕ}
    {source : Fin n} {tentative : Fin n → Option ℕ} {settled : Finset (Fin n)} {queue : Multiset (ℕ × Fin n)}
    (h : LabelInvariant g active w source tentative settled queue) (key : ℕ) (v : Fin n)
    (hitem : (key,v) ∈ queue) (hmin : ∀ item ∈ queue, key ≤ item.1) (hv : v ∉ settled) :
    tentative v = some key ∧ distance g active (fun e => (w e : ℝ≥0∞)) source v = key := by
  classical
  obtain ⟨d,hd,hdk⟩ := h.queueValid (key,v) hitem
  have hkd : key ≤ d := hmin (d,v) (h.covered v hv d hd)
  have hdeq : d = key := by omega
  subst d
  refine ⟨hd,le_antisymm (h.pathBound v key hd) ?_⟩
  let z := frontierPotential tentative settled key
  have hzSource : z source = 0 := by
    by_cases hs : source ∈ settled
    · simp [z,frontierPotential,hs,h.sourceZero]
    · have hk0 := hmin (0,source) (h.covered source hs 0 h.sourceZero)
      have hk : key = 0 := by omega
      simp [z,frontierPotential,hs,hk]
  have hzEdge : ∀ e ∈ active, z (g.head e) ≤ z (g.tail e)+w e := by
    intro e he
    by_cases ht : g.tail e ∈ settled
    · obtain ⟨dt,dh,hdt,hdh,hrelax⟩ := h.frontier e he ht
      by_cases hh : g.head e ∈ settled
      · simpa [z,frontierPotential,ht,hh,hdt,hdh] using hrelax
      · have hk := hmin (dh,g.head e) (h.covered (g.head e) hh dh hdh)
        simp only [z,frontierPotential,if_pos ht,if_neg hh,hdt,Option.getD_some]
        omega
    · by_cases hh : g.head e ∈ settled
      · obtain ⟨dh,hdh,_⟩ := h.exactSettled (g.head e) hh
        have hk := h.belowQueue (g.head e) hh dh hdh (key,v) hitem
        simp only [z,frontierPotential,if_neg ht,if_pos hh,hdh,Option.getD_some]
        omega
      · simp [z,frontierPotential,ht,hh]
  have hz := nat_feasible_distance g active w source z hzSource hzEdge v
  simpa only [z,frontierPotential,if_neg hv] using hz
end DecrAlmostLinearSSSP.Decremental.Exact
end s87
section s88
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact
lemma distance_self_zero {n k : ℕ} (g : Digraph n k) (active : Finset (Fin k)) (w : Fin k → ℝ≥0∞) (s : Fin n) :
    distance g active w s s = 0 := by
  apply le_antisymm
  · have hh := distance_le_walk (Walk.nil (g := g) (active := active) s) w
    simpa only [List.map_nil,List.sum_nil] using hh
  · exact bot_le
lemma reachable_of_nat_bound {n k : ℕ} (g : Digraph n k) (active : Finset (Fin k)) (w : Fin k → ℝ≥0∞)
    (s v : Fin n) (d : ℕ) (hd : distance g active w s v ≤ d) : Reachable g active s v := by
  by_contra hn
  rw [distance_top_of_unreachable g active w s v hn] at hd
  exact (show (d : ℝ≥0∞) ≠ ⊤ by simp) (top_le_iff.mp hd)
lemma distance_edge_bound {n k : ℕ} (g : Digraph n k) (active : Finset (Fin k)) (w : Fin k → ℕ)
    (s : Fin n) (e : Fin k) (he : e ∈ active) (d : ℕ)
    (hd : distance g active (fun a => (w a : ℝ≥0∞)) s (g.tail e) ≤ d) :
    distance g active (fun a => (w a : ℝ≥0∞)) s (g.head e) ≤ (d+w e : ℕ) := by
  have hr := reachable_of_nat_bound g active (fun a => (w a : ℝ≥0∞)) s (g.tail e) d hd
  obtain ⟨es,hes,_,hdist⟩ := distance_min_weight g active (fun a => (w a : ℝ)) (fun _ => Nat.cast_nonneg _) s (g.tail e) hr
  have hsum : (es.map (fun a => (w a : ℝ≥0∞))).sum = ENNReal.ofReal ((es.map (fun a => (w a : ℝ))).sum) := by
    simpa only [ENNReal.ofReal_natCast] using list_sum_ofReal (fun a => (w a : ℝ)) (fun _ => Nat.cast_nonneg _) es
  have htailCost : distance g active (fun a => (w a : ℝ≥0∞)) s (g.tail e) = (es.map (fun a => (w a : ℝ≥0∞))).sum := by
    rw [hsum]
    simpa only [ENNReal.ofReal_natCast] using hdist
  have hedge : Walk g active (g.tail e) (g.head e) [e] := .cons (u := g.tail e) e he (.nil _)
  have hbound := distance_le_walk (hes.append hedge) (fun a => (w a : ℝ≥0∞))
  simp only [List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] at hbound
  rw [← htailCost] at hbound
  apply hbound.trans
  simpa only [Nat.cast_add] using add_le_add hd (le_rfl : (w e : ℝ≥0∞) ≤ w e)
end DecrAlmostLinearSSSP.Decremental.Exact
end s88
section s89
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact
lemma labelInvariant_initial {n k : ℕ} (g : Digraph n k) (active : Finset (Fin k)) (w : Fin k → ℕ) (source : Fin n) :
    LabelInvariant g active w source (initialTentative source) ∅ ({(0,source)} : Multiset (ℕ × Fin n)) := by
  classical
  constructor
  · simp [initialTentative]
  · intro v d hd
    by_cases hv : v = source
    · subst v
      have hd0 : d = 0 := by simpa [initialTentative] using hd.symm
      subst d
      simp [distance_self_zero]
    · simp [initialTentative,hv] at hd
  · simp
  · simp
  · simp
  · intro v hv d hd
    by_cases heq : v = source
    · subst v
      have hd0 : d = 0 := by simpa [initialTentative] using hd.symm
      subst d
      simp
    · simp [initialTentative,heq] at hd
  · intro item hitem
    have heq : item = (0,source) := by simpa using hitem
    subst item
    exact ⟨0,by simp [initialTentative],le_rfl⟩
lemma Walk.closed_predicate {n k : ℕ} {g : Digraph n k} {active : Finset (Fin k)}
    {u v : Fin n} {es : List (Fin k)} (h : Walk g active u v es) (P : Fin n → Prop)
    (hedge : ∀ e ∈ active, P (g.tail e) → P (g.head e)) (hu : P u) : P v := by
  induction h with
  | nil v => exact hu
  | cons e he hw ih => exact ih (hedge e he hu)
lemma LabelInvariant.finished {n k : ℕ} {g : Digraph n k} {active : Finset (Fin k)} {w : Fin k → ℕ}
    {source : Fin n} {tentative : Fin n → Option ℕ} {settled : Finset (Fin n)}
    (h : LabelInvariant g active w source tentative settled 0) :
    ∀ v, distance g active (fun e => (w e : ℝ≥0∞)) source v = tentativeValue (tentative v) ∧
      (tentative v = none ↔ ¬Reachable g active source v) := by
  classical
  have hfiniteSettled (v : Fin n) (d : ℕ) (hd : tentative v = some d) : v ∈ settled := by
    by_contra hv
    have hh := h.covered v hv d hd
    simp at hh
  have hclosed : ∀ e ∈ active, (∃ d, tentative (g.tail e) = some d) → ∃ d, tentative (g.head e) = some d := by
    intro e he ht
    obtain ⟨dt,hdt⟩ := ht
    obtain ⟨_,dh,_,hdh,_⟩ := h.frontier e he (hfiniteSettled (g.tail e) dt hdt)
    exact ⟨dh,hdh⟩
  have hreachable (v : Fin n) (hr : Reachable g active source v) : ∃ d, tentative v = some d := by
    obtain ⟨es,hes⟩ := hr
    exact Walk.closed_predicate hes (fun z => ∃ d, tentative z = some d) hclosed ⟨0,h.sourceZero⟩
  intro v
  cases ht : tentative v with
  | none =>
    have hn : ¬Reachable g active source v := by
      intro hr
      obtain ⟨d,hd⟩ := hreachable v hr
      rw [ht] at hd
      contradiction
    exact ⟨distance_top_of_unreachable g active _ source v hn,by simp [ht,hn]⟩
  | some d =>
    obtain ⟨d',hd',heq⟩ := h.exactSettled v (hfiniteSettled v d ht)
    have hdd : d' = d := Option.some.inj (hd'.symm.trans ht)
    have hr := reachable_of_nat_bound g active (fun e => (w e : ℝ≥0∞)) source v d (h.pathBound v d ht)
    exact ⟨by simpa only [tentativeValue,hdd] using heq,by simp [ht,hr]⟩
end DecrAlmostLinearSSSP.Decremental.Exact
end s89
section s90
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact
lemma LabelInvariant.decrease {n k : ℕ} {g : Digraph n k} {active : Finset (Fin k)} {w : Fin k → ℕ}
    {source : Fin n} {tentative : Fin n → Option ℕ} {settled : Finset (Fin n)} {queue : Multiset (ℕ × Fin n)}
    (h : LabelInvariant g active w source tentative settled queue) (target : Fin n) (candidate : ℕ)
    (hn : target ∉ settled) (hsmaller : ∀ d, tentative target = some d → candidate < d)
    (hpath : distance g active (fun e => (w e : ℝ≥0∞)) source target ≤ candidate)
    (hbelow : ∀ v ∈ settled, ∀ d, tentative v = some d → d ≤ candidate) :
    LabelInvariant g active w source (Function.update tentative target (some candidate)) settled ((candidate,target)::ₘqueue) := by
  classical
  have hsource : source ≠ target := by
    intro hh
    have hz := hsmaller 0 (hh ▸ h.sourceZero)
    omega
  have hsettled (v : Fin n) (hv : v ∈ settled) : v ≠ target := by intro hh;subst v;exact hn hv
  constructor
  · rw [Function.update_of_ne hsource];exact h.sourceZero
  · intro v d hd
    by_cases hv : v = target
    · subst v
      rw [Function.update_self] at hd
      have hh := Option.some.inj hd
      subst d
      exact hpath
    · rw [Function.update_of_ne hv] at hd
      exact h.pathBound v d hd
  · intro v hv
    rw [Function.update_of_ne (hsettled v hv)]
    exact h.exactSettled v hv
  · intro v hv d hd item hitem
    rw [Function.update_of_ne (hsettled v hv)] at hd
    rcases Multiset.mem_cons.mp hitem with hh | hh
    · subst item;exact hbelow v hv d hd
    · exact h.belowQueue v hv d hd item hh
  · intro e he ht
    obtain ⟨dt,dh,hdt,hdh,hle⟩ := h.frontier e he ht
    refine ⟨dt,if g.head e = target then candidate else dh,?_,?_,?_⟩
    · rw [Function.update_of_ne (hsettled _ ht)];exact hdt
    · by_cases hh : g.head e = target
      · simp [hh]
      · simp only [if_neg hh,Function.update_of_ne hh,hdh]
    · by_cases hh : g.head e = target
      · have hh' := hsmaller dh (hh ▸ hdh)
        simp only [if_pos hh];omega
      · simpa only [if_neg hh] using hle
  · intro v hv d hd
    by_cases heq : v = target
    · subst v
      rw [Function.update_self] at hd
      have hh := Option.some.inj hd
      subst d
      exact Multiset.mem_cons_self _ _
    · rw [Function.update_of_ne heq] at hd
      exact Multiset.mem_cons_of_mem (h.covered v hv d hd)
  · intro item hitem
    rcases Multiset.mem_cons.mp hitem with hh | hh
    · subst item;exact ⟨candidate,Function.update_self _ _ _,le_rfl⟩
    · obtain ⟨d,hd,hle⟩ := h.queueValid item hh
      by_cases heq : item.2 = target
      · refine ⟨candidate,?_,?_⟩
        · rw [heq,Function.update_self]
        · have hh' := hsmaller d (heq ▸ hd);omega
      · exact ⟨d,by rwa [Function.update_of_ne heq],hle⟩
end DecrAlmostLinearSSSP.Decremental.Exact
end s90
section s91
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact
lemma LabelInvariant.settle {n k : ℕ} {g : Digraph n k} {active : Finset (Fin k)} {w : Fin k → ℕ}
    {source : Fin n} {tentative : Fin n → Option ℕ} {settled : Finset (Fin n)} {remaining : Multiset (ℕ × Fin n)}
    (key : ℕ) (v : Fin n)
    (h : LabelInvariant g active w source tentative settled ((key,v)::ₘremaining))
    (hv : v ∉ settled) (ht : tentative v = some key)
    (hd : distance g active (fun e => (w e : ℝ≥0∞)) source v = key)
    (hmin : ∀ item ∈ remaining, key ≤ item.1)
    (hrelaxed : ∀ e ∈ active, g.tail e = v → ∃ dh, tentative (g.head e) = some dh ∧ dh ≤ key+w e) :
    LabelInvariant g active w source tentative (insert v settled) remaining := by
  classical
  constructor
  · exact h.sourceZero
  · exact h.pathBound
  · intro u hu
    rcases Finset.mem_insert.mp hu with hh | hh
    · subst u;exact ⟨key,ht,hd⟩
    · exact h.exactSettled u hh
  · intro u hu d huTent item hitem
    rcases Finset.mem_insert.mp hu with hh | hh
    · subst u
      have hdk : d = key := Option.some.inj (huTent.symm.trans ht)
      subst d
      exact hmin item hitem
    · exact h.belowQueue u hh d huTent item (Multiset.mem_cons_of_mem hitem)
  · intro e he htail
    rcases Finset.mem_insert.mp htail with hh | hh
    · obtain ⟨dh,hdh,hbound⟩ := hrelaxed e he hh
      exact ⟨key,dh,hh ▸ ht,hdh,hbound⟩
    · exact h.frontier e he hh
  · intro u hu d hud
    have hun : u ∉ settled := fun hh => hu (Finset.mem_insert_of_mem hh)
    have hune : u ≠ v := by intro hh;subst u;exact hu (Finset.mem_insert_self _ _)
    rcases Multiset.mem_cons.mp (h.covered u hun d hud) with hh | hh
    · have huv := congrArg Prod.snd hh
      exact False.elim (hune huv)
    · exact hh
  · intro item hitem
    exact h.queueValid item (Multiset.mem_cons_of_mem hitem)
end DecrAlmostLinearSSSP.Decremental.Exact
end s91
section s92
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact
lemma adjacency_step {n k : ℕ} (g : Digraph n k) (t : ℕ) (ht : t<k) (v : Fin n) :
    adjacency g (t+1) v = if g.tail ⟨t,ht⟩ = v then ⟨t,ht⟩::adjacency g t v else adjacency g t v := by
  simp only [adjacency,dif_pos ht]
lemma adjacency_mem {n k : ℕ} (g : Digraph n k) (t : ℕ) (v : Fin n) (e : Fin k) :
    e ∈ adjacency g t v ↔ e.val<t ∧ g.tail e=v := by
  induction t with
  | zero => simp [adjacency]
  | succ t ih =>
    by_cases ht : t<k
    · rw [adjacency_step g t ht v]
      by_cases he : g.tail ⟨t,ht⟩ = v
      · rw [if_pos he,List.mem_cons,ih]
        constructor
        · rintro (hh | ⟨h1,h2⟩)
          · subst e;exact ⟨Nat.lt_succ_self t,he⟩
          · exact ⟨by omega,h2⟩
        · rintro ⟨h1,h2⟩
          by_cases hv : e.val=t
          · exact Or.inl (Fin.ext hv)
          · exact Or.inr ⟨by omega,h2⟩
      · rw [if_neg he,ih]
        constructor
        · rintro ⟨h1,h2⟩;exact ⟨by omega,h2⟩
        · rintro ⟨h1,h2⟩
          have hne : e.val ≠ t := by intro hh;apply he;have heq : e=⟨t,ht⟩ := Fin.ext hh;simpa only [← heq] using h2
          exact ⟨by omega,h2⟩
    · have hek := e.isLt
      simp only [adjacency,dif_neg ht,ih]
      constructor <;> rintro ⟨h1,h2⟩ <;> exact ⟨by omega,h2⟩
lemma adjacency_nodup {n k : ℕ} (g : Digraph n k) (t : ℕ) (v : Fin n) : (adjacency g t v).Nodup := by
  induction t with
  | zero => simp [adjacency]
  | succ t ih =>
    by_cases ht : t<k
    · rw [adjacency_step g t ht v]
      split_ifs
      · exact List.nodup_cons.mpr ⟨by simp [adjacency_mem],ih⟩
      · exact ih
    · simpa only [adjacency,dif_neg ht] using ih
lemma adjacency_total {n k : ℕ} (g : Digraph n k) (t : ℕ) (ht : t≤k) :
    ∑ v : Fin n, (adjacency g t v).length = t := by
  classical
  induction t with
  | zero => simp [adjacency]
  | succ t ih =>
    have htt : t<k := by omega
    have hi := ih (by omega)
    have hl (v : Fin n) : (adjacency g (t+1) v).length =
        (adjacency g t v).length+(if v=g.tail ⟨t,htt⟩ then 1 else 0) := by
      rw [adjacency_step g t htt v]
      by_cases heq : g.tail ⟨t,htt⟩ = v
      · rw [if_pos heq,if_pos heq.symm,List.length_cons]
      · rw [if_neg heq,if_neg (Ne.symm heq),Nat.add_zero]
    simp only [hl,Finset.sum_add_distrib,hi]
    simp
end DecrAlmostLinearSSSP.Decremental.Exact
end s92
section s93
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild
open Structured
lemma clearPrepare_eval (s : Data) : Eval clearPrepare s 2 (clearPrepared s) := eval_sequence_atoms clearPrepareAtoms s
lemma prepare_eval (s : Data) : Eval prepare s 4 (prepared s) := eval_sequence_atoms prepareAtoms s
lemma edge_eval (s : Data) : Eval edge s 20 (advanced s) := eval_sequence_atoms edgeAtoms s
lemma edge_nat_frame (j : ℕ) (hj : j ∉ ({294,296,298,300,304,306,308,310,312,314} : Finset ℕ)) : NatFrame edge j := by
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hj
  simp [edge,edgeAtoms,Structured.sequence,NatFrame,writesNat] <;> tauto
lemma code_real_frame (j : ℕ) : RealFrame code j := by
  refine ⟨?_,Clear.real_frame j,?_,?_⟩
  all_goals simp [clearPrepare,clearPrepareAtoms,prepare,prepareAtoms,loop,edge,edgeAtoms,Structured.sequence,RealFrame,writesReal]
end DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild
end s93
section s94
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild
open Structured
lemma edge_fields (s : Data) (h1 : s.natReg 26 = 1) :
    let tail := s.natMem (s.natReg 298)
    let head := s.natMem (s.natReg 298+1)
    let weight := s.natMem (s.natReg 298+2)
    let headSlot := s.natReg 224+tail
    let next := s.natMem headSlot
    let node := s.natReg 296
    (advanced s).natMem = Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update s.natMem node head) (node+1) (s.natReg 294))
      (node+2) next) (node+3) weight) (s.natReg 294) 1) headSlot node ∧
      (advanced s).natReg 294 = s.natReg 294+1 ∧
      (advanced s).natReg 296 = s.natReg 296+4 ∧
      (advanced s).natReg 298 = s.natReg 298+3 ∧
      (advanced s).natReg 300 = s.natReg 300+1 ∧
      (advanced s).realMem = s.realMem := by
  simp [advanced,edgeAtoms,Atom.effect,instructionEffect,data,Data.machine,h1,Nat.add_assoc]
end DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild
end s94
section s95
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma initial_nat_tape (p : Program) (i : Input) (e : Fin i.k) (offset : ℕ) (hoff : offset < 3) :
    (initialMachine p i).natMem (i.n+3*e.val+offset) =
      if offset = 0 then (i.graph.tail e).val else if offset = 1 then (i.graph.head e).val else i.weight e := by
  obtain ⟨e,he⟩ := e
  have hsub : i.n+3*e+offset-i.n = 3*e+offset := by omega
  have hdiv : (3*e+offset)/3 = e := by omega
  have hmod : (3*e+offset)%3 = offset := by omega
  have hlow : i.n ≤ i.n+3*e+offset := by omega
  simp [initialMachine,hsub,hdiv,hmod,he,hlow]
lemma initial_nat_above_tape (p : Program) (i : Input) (address : ℕ) (ha : i.n+3*i.k ≤ address) :
    (initialMachine p i).natMem address = 0 := by
  have hnot : ¬(i.n ≤ address ∧ (address-i.n)/3 < i.k) := by omega
  simp only [initialMachine,dif_neg hnot]
lemma initial_real_zero (p : Program) (i : Input) (address : ℕ) :
    (initialMachine p i).realMem address = 0 := rfl
lemma initial_source_bank_zero (p : Program) (i : Input) (B F : ℕ) (hB : i.n+3*i.k ≤ B) (hF : 0 < F) :
    ∀ address, (initialMachine p i).natMem (B+F*(2*address+1)) = 0 ∧
      (initialMachine p i).realMem (B+F*(2*address+1)) = 0 := by
  intro address
  refine ⟨initial_nat_above_tape p i _ ?_,rfl⟩
  omega
end DecrAlmostLinearSSSP.Decremental
end s95
section s96
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact
open Structured
namespace Adjacency
lemma tape_initial (p : Program) (i : Input) : Tape i (data (initialMachine p i)) := by
  intro e
  refine ⟨?_,?_,?_⟩
  · simpa [data] using initial_nat_tape p i e 0 (by omega)
  · simpa [data] using initial_nat_tape p i e 1 (by omega)
  · simpa [data] using initial_nat_tape p i e 2 (by omega)
lemma tape_frame (i : Input) (s t : Data) (h : Tape i s)
    (hf : ∀ a : ℕ, a < i.n+3*i.k → t.natMem a=s.natMem a) : Tape i t := by
  intro e
  have he := e.isLt
  exact ⟨(hf _ (by omega)).trans (h e).1,(hf _ (by omega)).trans (h e).2.1,(hf _ (by omega)).trans (h e).2.2⟩
lemma root_cons (l : Layout.Addresses) {k : ℕ} (e : Fin k) (es : List (Fin k)) : root l (e::es)=nodeAddress l e := rfl
lemma node_positive (i : Input) (e : Fin i.k) : 0<nodeAddress (Layout.addresses (i.n+3*i.k+2) i.n i.k) e := by
  simp [nodeAddress,Layout.addresses]
end Adjacency
end DecrAlmostLinearSSSP.Decremental.Exact
end s96
section s97
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Adjacency
lemma insert_heads (i : Input) (e : Fin i.k) (memory : ℕ → ℕ) (v : Fin i.n) :
    let l := Layout.addresses (i.n+3*i.k+2) i.n i.k
    insertMemory i l e memory (l.heads+v.val) =
      if v=i.graph.tail e then nodeAddress l e else memory (l.heads+v.val) := by
  let l := Layout.addresses (i.n+3*i.k+2) i.n i.k
  have hv := v.isLt
  have he := e.isLt
  have ht := (i.graph.tail e).isLt
  change insertMemory i l e memory (l.heads+v.val) = _
  unfold insertMemory
  by_cases h : v=i.graph.tail e
  · rw [h,Function.update_self,if_pos rfl]
  · rw [if_neg h,Function.update_of_ne (by intro hh;apply h;apply Fin.ext;omega)]
    dsimp [l,Layout.addresses,nodeAddress]
    repeat' rw [Function.update_of_ne (by omega)]
lemma insert_active (i : Input) (e f : Fin i.k) (memory : ℕ → ℕ) :
    let l := Layout.addresses (i.n+3*i.k+2) i.n i.k
    insertMemory i l e memory (l.active+f.val) = if f=e then 1 else memory (l.active+f.val) := by
  let l := Layout.addresses (i.n+3*i.k+2) i.n i.k
  have hf := f.isLt
  have he := e.isLt
  have ht := (i.graph.tail e).isLt
  change insertMemory i l e memory (l.active+f.val) = _
  unfold insertMemory
  rw [Function.update_of_ne (by dsimp [l,Layout.addresses];omega)]
  by_cases h : f=e
  · rw [h,Function.update_self,if_pos rfl]
  · rw [if_neg h,Function.update_of_ne (by intro hh;apply h;apply Fin.ext;omega)]
    dsimp [l,Layout.addresses,nodeAddress]
    repeat' rw [Function.update_of_ne (by omega)]
lemma insert_old_node (i : Input) (e f : Fin i.k) (hne : f ≠ e) (r : ℕ) (hr : r<4) (memory : ℕ → ℕ) :
    let l := Layout.addresses (i.n+3*i.k+2) i.n i.k
    insertMemory i l e memory (nodeAddress l f+r) = memory (nodeAddress l f+r) := by
  let l := Layout.addresses (i.n+3*i.k+2) i.n i.k
  have hf := f.isLt
  have he := e.isLt
  have ht := (i.graph.tail e).isLt
  have hval : f.val ≠ e.val := fun hh => hne (Fin.ext hh)
  change insertMemory i l e memory (nodeAddress l f+r) = _
  unfold insertMemory
  dsimp [l,Layout.addresses,nodeAddress]
  repeat' rw [Function.update_of_ne (by omega)]
lemma insert_new_node (i : Input) (e : Fin i.k) (memory : ℕ → ℕ) :
    let l := Layout.addresses (i.n+3*i.k+2) i.n i.k
    let updated := insertMemory i l e memory
    updated (nodeAddress l e) = (i.graph.head e).val ∧
      updated (nodeAddress l e+1) = l.active+e.val ∧
      updated (nodeAddress l e+2) = memory (l.heads+(i.graph.tail e).val) ∧
      updated (nodeAddress l e+3) = i.weight e := by
  let l := Layout.addresses (i.n+3*i.k+2) i.n i.k
  have he := e.isLt
  have ht := (i.graph.tail e).isLt
  change insertMemory i l e memory _ = _ ∧ _ = _ ∧ _ = _ ∧ _ = _
  unfold insertMemory
  dsimp [l,Layout.addresses,nodeAddress]
  constructor
  · simp (disch := omega) only [Function.update_of_ne,Function.update_self]
  · constructor
    · simp (disch := omega) only [Function.update_of_ne,Function.update_self]
    · constructor
      · simp (disch := omega) only [Function.update_of_ne,Function.update_self]
      · simp (disch := omega) only [Function.update_of_ne,Function.update_self]
lemma insert_frame (i : Input) (e : Fin i.k) (memory : ℕ → ℕ) (a : ℕ)
    (ha : a < (Layout.addresses (i.n+3*i.k+2) i.n i.k).heads ∨
      (Layout.addresses (i.n+3*i.k+2) i.n i.k).powers ≤ a) :
    insertMemory i (Layout.addresses (i.n+3*i.k+2) i.n i.k) e memory a = memory a := by
  have he := e.isLt
  have ht := (i.graph.tail e).isLt
  unfold insertMemory
  dsimp [Layout.addresses,nodeAddress] at ha ⊢
  repeat' rw [Function.update_of_ne (by omega)]
end DecrAlmostLinearSSSP.Decremental.Exact.Adjacency
end s97
section s98
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Adjacency
open Structured
lemma image_insert (i : Input) (t : ℕ) (ht : t < i.k) (s u : Data)
    (hi : Image i (Layout.addresses (i.n+3*i.k+2) i.n i.k) t s)
    (hm : u.natMem = insertMemory i (Layout.addresses (i.n+3*i.k+2) i.n i.k) ⟨t,ht⟩ s.natMem) :
    Image i (Layout.addresses (i.n+3*i.k+2) i.n i.k) (t+1) u := by
  let l := Layout.addresses (i.n+3*i.k+2) i.n i.k
  let e : Fin i.k := ⟨t,ht⟩
  have hold (f : Fin i.k) (hne : f ≠ e) (r : ℕ) (hr : r<4) :
      u.natMem (nodeAddress l f+r) = s.natMem (nodeAddress l f+r) := by
    rw [hm];exact insert_old_node i e f hne r hr s.natMem
  have hnew := insert_new_node i e s.natMem
  change insertMemory i l e s.natMem (nodeAddress l e) = _ ∧ _ ∧ _ ∧ _ at hnew
  rw [← hm] at hnew
  have hnodes (f : Fin i.k) (hf : f.val<t+1) :
      u.natMem (nodeAddress l f) = (i.graph.head f).val ∧
      u.natMem (nodeAddress l f+1) = l.active+f.val ∧
      u.natMem (nodeAddress l f+2) = root l (adjacency i.graph f.val (i.graph.tail f)) ∧
      u.natMem (nodeAddress l f+3) = i.weight f := by
    by_cases hfe : f=e
    · subst f
      refine ⟨hnew.1,hnew.2.1,?_,hnew.2.2.2⟩
      exact hnew.2.2.1.trans (hi.heads (i.graph.tail e))
    · have hval : f.val ≠ t := fun hh => hfe (Fin.ext hh)
      have hft : f.val<t := by omega
      refine ⟨?_,(hold f hfe 1 (by omega)).trans (hi.flagAddress f hft),
        (hold f hfe 2 (by omega)).trans (hi.next f hft),(hold f hfe 3 (by omega)).trans (hi.weight f hft)⟩
      simpa only [Nat.add_zero] using (hold f hfe 0 (by omega)).trans (by simpa only [Nat.add_zero] using hi.head f hft)
  constructor
  · intro v
    rw [hm,insert_heads i e s.natMem v,adjacency_step i.graph t ht v]
    change (if v=i.graph.tail e then nodeAddress l e else s.natMem (l.heads+v.val)) =
      root l (if i.graph.tail e=v then e::adjacency i.graph t v else adjacency i.graph t v)
    by_cases hv : v=i.graph.tail e
    · simp only [if_pos hv,if_pos hv.symm,root]
    · simp only [if_neg hv,if_neg (Ne.symm hv)]
      exact hi.heads v
  · intro f hf;exact (hnodes f hf).1
  · intro f hf;exact (hnodes f hf).2.1
  · intro f hf;exact (hnodes f hf).2.2.1
  · intro f hf;exact (hnodes f hf).2.2.2
  · intro f hf
    rw [hm,insert_active i e f s.natMem]
    by_cases hfe : f=e
    · rw [if_pos hfe]
    · rw [if_neg hfe]
      have hval : f.val ≠ t := fun hh => hfe (Fin.ext hh)
      exact hi.active f (by omega)
end DecrAlmostLinearSSSP.Decremental.Exact.Adjacency
end s98
section s99
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild
open Structured
lemma step_memory (i : Input) (upto : ℕ) (ht : upto < i.k) (s : Data) (h : Prefix i upto s) :
    (advanced s).natMem = Adjacency.insertMemory i (Layout.addresses (i.n+3*i.k+2) i.n i.k) ⟨upto,ht⟩ s.natMem := by
  have hm := (edge_fields s h.unit).1
  rw [hm]
  unfold Adjacency.insertMemory Adjacency.nodeAddress
  simp only [h.tapeCursor,h.nodeCursor,h.activeCursor,h.layout.heads,Fin.val_mk,
    (h.tape ⟨upto,ht⟩).1,(h.tape ⟨upto,ht⟩).2.1,(h.tape ⟨upto,ht⟩).2.2]
lemma step_prefix (i : Input) (upto : ℕ) (ht : upto < i.k) (s : Data) (h : Prefix i upto s) : Prefix i (upto+1) (advanced s) := by
  have he := edge_eval s
  have hn (j : ℕ) (hj : j ∉ ({294,296,298,300,304,306,308,310,312,314} : Finset ℕ)) := he.nat_frame (edge_nat_frame j hj)
  have hm := step_memory i upto ht s h
  have hv := edge_fields s h.unit
  refine ⟨(hn 56 (by norm_num)).trans h.zero,(hn 26 (by norm_num)).trans h.unit,
    (hn 66 (by norm_num)).trans h.vertices,(hn 68 (by norm_num)).trans h.edges,?_,?_,
    Adjacency.image_insert i upto ht s (advanced s) h.image hm,?_,?_,?_,?_⟩
  · constructor
    · exact (hn 224 (by norm_num)).trans h.layout.heads
    · exact (hn 226 (by norm_num)).trans h.layout.settled
    · exact (hn 228 (by norm_num)).trans h.layout.active
    · exact (hn 230 (by norm_num)).trans h.layout.distances
    · exact (hn 232 (by norm_num)).trans h.layout.nodes
    · exact (hn 234 (by norm_num)).trans h.layout.powers
  · apply Adjacency.tape_frame i s (advanced s) h.tape
    intro a ha
    rw [hm]
    apply Adjacency.insert_frame i ⟨upto,ht⟩ s.natMem a
    exact Or.inl (by dsimp [Layout.addresses];omega)
  · rw [hv.2.1,h.activeCursor];omega
  · rw [hv.2.2.1,h.nodeCursor];omega
  · rw [hv.2.2.2.1,h.tapeCursor];omega
  · rw [hv.2.2.2.2.1,h.index]
end DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild
end s99
section s100
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild
open Structured
attribute [local irreducible] advanced
lemma loop_nat_frame (j : ℕ) (hj : j ∉ ({294,296,298,300,304,306,308,310,312,314} : Finset ℕ)) : NatFrame loop j := edge_nat_frame j hj
lemma loop_eval (i : Input) (remaining upto : ℕ) (hend : upto+remaining=i.k) (s : Data) (h : Prefix i upto s) :
    ∃ t, Eval loop s (22*remaining+2) t ∧ Prefix i i.k t ∧ t.realMem = s.realMem ∧
      (∀ a, a < (Layout.addresses (i.n+3*i.k+2) i.n i.k).heads ∨
        (Layout.addresses (i.n+3*i.k+2) i.n i.k).powers ≤ a → t.natMem a = s.natMem a) := by
  induction remaining generalizing upto s with
  | zero =>
    have hu : upto=i.k := by omega
    refine ⟨s,?_,hu ▸ h,rfl,fun _ _ => rfl⟩
    have ht : ¬(Test.natLess 300 68).holds s := by simp [Test.holds,h.index,h.edges,hu]
    exact Eval.loopNo s ht
  | succ remaining ih =>
    have hu : upto < i.k := by omega
    have hstep := step_prefix i upto hu s h
    obtain ⟨t,ht,hp,hr,hf⟩ := ih (upto+1) (by omega) (advanced s) hstep
    have htest : (Test.natLess 300 68).holds s := by
      change s.natReg 300 < s.natReg 68
      rw [h.index,h.edges]
      exact hu
    refine ⟨t,?_,hp,hr.trans (edge_fields s h.unit).2.2.2.2.2,?_⟩
    · have he := Eval.loopYes htest (edge_eval s) ht
      convert he using 1 <;> first | rfl | omega
    · intro a ha
      rw [hf a ha,step_memory i upto hu s h]
      exact Adjacency.insert_frame i ⟨upto,hu⟩ s.natMem a ha
end DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild
end s100
section s101
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
namespace DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild
open Structured
lemma setup_nat_frame (j : ℕ) (hj : j ∉ ({290,292,294,296,298,300} : Finset ℕ)) : NatFrame setup j := by
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hj
  refine ⟨?_,Clear.nat_frame j (by tauto),?_⟩
  all_goals simp [clearPrepare,clearPrepareAtoms,prepare,prepareAtoms,Structured.sequence,NatFrame,writesNat] <;> tauto
lemma setup_eval (i : Input) (s : Data) (hz : s.natReg 56 = 0) (h1 : s.natReg 26 = 1)
    (hn : s.natReg 66 = i.n) (hk : s.natReg 68 = i.k)
    (hl : Layout.Image (Layout.addresses (i.n+3*i.k+2) i.n i.k) s) (htape : Adjacency.Tape i s) :
    ∃ t, Eval setup s (4*i.n+8) t ∧ Prefix i 0 t ∧ t.realMem = s.realMem ∧
      (∀ a, a < (Layout.addresses (i.n+3*i.k+2) i.n i.k).heads ∨
        (Layout.addresses (i.n+3*i.k+2) i.n i.k).heads+i.n ≤ a → t.natMem a=s.natMem a) := by
  let l := Layout.addresses (i.n+3*i.k+2) i.n i.k
  let u := clearPrepared s
  have heu := clearPrepare_eval s
  have huNat (j : ℕ) (h290 : j ≠ 290) (h292 : j ≠ 292) : u.natReg j = s.natReg j := by
    apply heu.nat_frame
    simp [clearPrepare,clearPrepareAtoms,Structured.sequence,NatFrame,writesNat,Ne.symm h290,Ne.symm h292]
  have huz : u.natReg 56 = 0 := (huNat 56 (by omega) (by omega)).trans hz
  have hu1 : u.natReg 26 = 1 := (huNat 26 (by omega) (by omega)).trans h1
  have hu290 : u.natReg 290 = l.heads := by
    simp [u,clearPrepared,clearPrepareAtoms,Atom.effect,instructionEffect,data,Data.machine,hz,hl.heads,l]
  have hu292 : u.natReg 292 = l.heads+i.n := by
    simp [u,clearPrepared,clearPrepareAtoms,Atom.effect,instructionEffect,data,Data.machine,hn,hl.heads,l]
  obtain ⟨v,hev,hv290,hvMem,hvReal,hvFrame⟩ := Clear.eval_code l.heads i.n u huz hu1 hu290 hu292
  let t := prepared v
  have het := prepare_eval v
  have he := Eval.seq heu (Eval.seq hev het)
  have he' : Eval setup s (4*i.n+8) t := by convert he using 1 <;> first | rfl | omega
  have htf (j : ℕ) (hj : j ∉ ({290,292,294,296,298,300} : Finset ℕ)) : t.natReg j = s.natReg j :=
    he'.nat_frame (setup_nat_frame j hj)
  have hvf (j : ℕ) (h290 : j ≠ 290) : v.natReg j = u.natReg j := hev.nat_frame (Clear.nat_frame j h290)
  have hmem : t.natMem = v.natMem := by rfl
  have htFrame (a : ℕ) (ha : a<l.heads ∨ l.heads+i.n≤a) : t.natMem a=s.natMem a := by
    exact hvFrame a ha
  have htLayout : Layout.Image l t := by
    constructor
    · exact (htf 224 (by norm_num)).trans hl.heads
    · exact (htf 226 (by norm_num)).trans hl.settled
    · exact (htf 228 (by norm_num)).trans hl.active
    · exact (htf 230 (by norm_num)).trans hl.distances
    · exact (htf 232 (by norm_num)).trans hl.nodes
    · exact (htf 234 (by norm_num)).trans hl.powers
  refine ⟨t,he',?_,hvReal,htFrame⟩
  refine ⟨(htf 56 (by norm_num)).trans hz,(htf 26 (by norm_num)).trans h1,
    (htf 66 (by norm_num)).trans hn,(htf 68 (by norm_num)).trans hk,htLayout,?_,?_,?_,?_,?_,?_⟩
  · apply Adjacency.tape_frame i s t htape
    intro a ha
    exact htFrame a (Or.inl (by dsimp [l,Layout.addresses];omega))
  · constructor
    · intro x
      change v.natMem (l.heads+x.val) = 0
      exact hvMem _ (Nat.le_add_right _ _) (Nat.add_lt_add_left x.isLt _)
    all_goals intro e he;have ee := e.isLt;simp at he
  · have hu228 := (hvf 228 (by omega)).trans (huNat 228 (by omega) (by omega))
    simp [t,prepared,prepareAtoms,Atom.effect,instructionEffect,data,Data.machine,
      (hvf 56 (by omega)).trans huz,hu228,hl.active]
  · have hu232 := (hvf 232 (by omega)).trans (huNat 232 (by omega) (by omega))
    simp [t,prepared,prepareAtoms,Atom.effect,instructionEffect,data,Data.machine,
      (hvf 56 (by omega)).trans huz,hu232,hl.nodes]
  · have hu66 := (hvf 66 (by omega)).trans (huNat 66 (by omega) (by omega))
    simp [t,prepared,prepareAtoms,Atom.effect,instructionEffect,data,Data.machine,
      (hvf 56 (by omega)).trans huz,hu66,hn]
  · simp [t,prepared,prepareAtoms,Atom.effect,instructionEffect,data,Data.machine]
end DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild
end s101
section s102
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild
open Structured
lemma append_loop {s u t : Data} {c d : ℕ} (hi : Eval setup s c u) (hl : Eval loop u d t) :
    Eval code s (c+d) t := by
  cases hi with
  | seq hp hs =>
    cases hs with
    | seq hc hprep =>
      have he := Eval.seq hp (Eval.seq hc (Eval.seq hprep hl))
      convert he using 1 <;> first | rfl | omega
lemma code_nat_frame (j : ℕ) (hj : j ∉ ({290,292,294,296,298,300,304,306,308,310,312,314} : Finset ℕ)) : NatFrame code j := by
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hj
  refine ⟨?_,Clear.nat_frame j (by tauto),?_,loop_nat_frame j ?_⟩
  · simp [clearPrepare,clearPrepareAtoms,Structured.sequence,NatFrame,writesNat] <;> tauto
  · simp [prepare,prepareAtoms,Structured.sequence,NatFrame,writesNat] <;> tauto
  · simp only [Finset.mem_insert,Finset.mem_singleton,not_or];tauto
lemma code_eval (i : Input) (s : Data) (hz : s.natReg 56 = 0) (h1 : s.natReg 26 = 1)
    (hn : s.natReg 66 = i.n) (hk : s.natReg 68 = i.k)
    (hl : Layout.Image (Layout.addresses (i.n+3*i.k+2) i.n i.k) s) (htape : Adjacency.Tape i s) :
    ∃ t, Eval code s (4*i.n+22*i.k+10) t ∧ Prefix i i.k t ∧ t.realMem = s.realMem ∧
      (∀ a, a < (Layout.addresses (i.n+3*i.k+2) i.n i.k).heads ∨
        (Layout.addresses (i.n+3*i.k+2) i.n i.k).powers ≤ a → t.natMem a=s.natMem a) := by
  obtain ⟨u,heu,hu,hur,huf⟩ := setup_eval i s hz h1 hn hk hl htape
  obtain ⟨t,het,ht,htr,htf⟩ := loop_eval i i.k 0 (by omega) u hu
  refine ⟨t,?_,ht,htr.trans hur,?_⟩
  · have he := append_loop heu het
    convert he using 1 <;> first | rfl | omega
  · intro a ha
    rw [htf a ha,huf a (by
      rcases ha with ha | ha
      · exact Or.inl ha
      · exact Or.inr (by dsimp [Layout.addresses] at ha ⊢;omega))]
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
lemma adjacency_head {n k : ℕ} (g : Digraph n k) (upto : ℕ) (v : Fin n) (e : Fin k) (es : List (Fin k))
    (heq : adjacency g upto v=e::es) : es=adjacency g e.val v ∧ g.tail e=v ∧ e.val<upto := by
  induction upto with
  | zero => simp [adjacency] at heq
  | succ upto ih =>
    by_cases ht : upto<k
    · rw [adjacency_step g upto ht v] at heq
      by_cases hv : g.tail ⟨upto,ht⟩=v
      · rw [if_pos hv] at heq
        have hh := List.cons.inj heq
        have he : e=⟨upto,ht⟩ := hh.1.symm
        subst e
        exact ⟨hh.2.symm,hv,Nat.lt_succ_self upto⟩
      · rw [if_neg hv] at heq
        obtain ⟨h1,h2,h3⟩ := ih heq
        exact ⟨h1,h2,by omega⟩
    · simp only [adjacency,dif_neg ht] at heq
      obtain ⟨h1,h2,h3⟩ := ih heq
      exact ⟨h1,h2,by omega⟩
namespace Adjacency
lemma image_chain (i : Input) (l : Layout.Addresses) (s : Structured.Data) (upto : ℕ)
    (hi : Image i l upto s) (v : Fin i.n) : Chain l s (adjacency i.graph upto v) := by
  have aux : ∀ bound, bound≤upto → Chain l s (adjacency i.graph bound v) := by
    intro bound
    induction bound using Nat.strong_induction_on with
    | h bound ih =>
      intro hb
      cases he : adjacency i.graph bound v with
      | nil => trivial
      | cons e es =>
        obtain ⟨hrest,htail,helt⟩ := adjacency_head i.graph bound v e es he
        refine ⟨?_,?_⟩
        · rw [hi.next e (by omega),htail,hrest]
        · rw [hrest];exact ih e.val helt (by omega)
  exact aux upto le_rfl
end Adjacency
end DecrAlmostLinearSSSP.Decremental.Exact
end s104
section s105
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Adjacency
open Structured
lemma Image.static {i : Input} {l : Layout.Addresses} {s : Data} (h : Image i l i.k s) : StaticImage i l s :=
  ⟨h.heads,fun e => h.head e e.isLt,fun e => h.flagAddress e e.isLt,fun e => h.next e e.isLt,fun e => h.weight e e.isLt⟩
lemma Image.active_initial {i : Input} {l : Layout.Addresses} {s : Data} (h : Image i l i.k s) : ActiveImage i l [] s := by
  intro e
  simpa [live] using h.active e e.isLt
lemma StaticImage.frame {i : Input} {l : Layout.Addresses} {s t : Data} (h : StaticImage i l s)
    (hf : ∀ a∈staticFootprint i l, t.natMem a=s.natMem a) : StaticImage i l t := by
  have hn (e : Fin i.k) (r : ℕ) (hr : r<4) : t.natMem (nodeAddress l e+r)=s.natMem (nodeAddress l e+r) := by
    apply hf
    apply Finset.mem_union_right
    have he := e.isLt
    exact Finset.mem_Ico.mpr ⟨by dsimp [nodeAddress];omega,by dsimp [nodeAddress];omega⟩
  constructor
  · intro v
    rw [hf _ (Finset.mem_union_left _ (Finset.mem_Ico.mpr ⟨by omega,by have hv := v.isLt;omega⟩))]
    exact h.heads v
  · intro e;simpa only [Nat.add_zero] using (hn e 0 (by omega)).trans (by simpa only [Nat.add_zero] using h.head e)
  · intro e;exact (hn e 1 (by omega)).trans (h.flagAddress e)
  · intro e;exact (hn e 2 (by omega)).trans (h.next e)
  · intro e;exact (hn e 3 (by omega)).trans (h.weight e)
lemma StaticImage.chain {i : Input} {l : Layout.Addresses} {s : Data} (h : StaticImage i l s) (v : Fin i.n) :
    Chain l s (adjacency i.graph i.k v) := by
  have aux : ∀ bound, Chain l s (adjacency i.graph bound v) := by
    intro bound
    induction bound using Nat.strong_induction_on with
    | h bound ih =>
      cases he : adjacency i.graph bound v with
      | nil => trivial
      | cons e es =>
        obtain ⟨hrest,htail,helt⟩ := adjacency_head i.graph bound v e es he
        refine ⟨?_,?_⟩
        · rw [h.next e,htail,hrest]
        · rw [hrest];exact ih e.val helt
  exact aux i.k
end DecrAlmostLinearSSSP.Decremental.Exact.Adjacency
end s105
section s106
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact
open Structured
lemma TentativeImage.finite {i : Input} {l : Layout.Addresses} {tentative : Fin i.n → Option ℕ} {s : Data}
    (h : TentativeImage i l tentative s) (v : Fin i.n) (d : ℕ) (hv : tentative v=some d) :
    s.natMem v.val=0 ∧ s.natMem (l.distances+v.val)=d ∧ s.realMem v.val=(d : ℝ) := by
  simpa only [TentativeImage,hv] using h v
lemma TentativeImage.infinite {i : Input} {l : Layout.Addresses} {tentative : Fin i.n → Option ℕ} {s : Data}
    (h : TentativeImage i l tentative s) (v : Fin i.n) (hv : tentative v=none) : s.natMem v.val=1 := by
  simpa only [TentativeImage,hv] using h v
lemma TentativeImage.flag_one {i : Input} {l : Layout.Addresses} {tentative : Fin i.n → Option ℕ} {s : Data}
    (h : TentativeImage i l tentative s) (v : Fin i.n) : s.natMem v.val=1 ↔ tentative v=none := by
  cases hv : tentative v with
  | none => simp [h.infinite v hv,hv]
  | some d => simp [ (h.finite v d hv).1,hv]
lemma TentativeImage.stored {i : Input} {l : Layout.Addresses} {tentative : Fin i.n → Option ℕ} {s : Data}
    (h : TentativeImage i l tentative s) (v : Fin i.n) :
    stored s.machine v.val = tentativeValue (tentative v) := by
  cases hv : tentative v with
  | none => simp [DecrAlmostLinearSSSP.Decremental.stored,Data.machine,h.infinite v hv,hv,tentativeValue]
  | some d => simp [DecrAlmostLinearSSSP.Decremental.stored,Data.machine,(h.finite v d hv).1,(h.finite v d hv).2.2,hv,tentativeValue]
lemma TentativeImage.frame {i : Input} {l : Layout.Addresses} {tentative : Fin i.n → Option ℕ} {s t : Data}
    (h : TentativeImage i l tentative s)
    (hflag : ∀ v : Fin i.n, t.natMem v.val=s.natMem v.val)
    (hdist : ∀ v : Fin i.n, t.natMem (l.distances+v.val)=s.natMem (l.distances+v.val))
    (hreal : ∀ v : Fin i.n, t.realMem v.val=s.realMem v.val) : TentativeImage i l tentative t := by
  intro v
  cases hv : tentative v with
  | none => exact (hflag v).trans (h.infinite v hv)
  | some d => exact ⟨(hflag v).trans (h.finite v d hv).1,(hdist v).trans (h.finite v d hv).2.1,(hreal v).trans (h.finite v d hv).2.2⟩
end DecrAlmostLinearSSSP.Decremental.Exact
end s106
section s107
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Layout
lemma vertex_bounds (i : Input) (v : Fin i.n) :
    let l := addresses (i.n+3*i.k+2) i.n i.k
    v.val < l.heads ∧ l.heads+v.val<l.powers ∧ l.settled+v.val<l.powers ∧ l.distances+v.val<l.powers := by
  have hv := v.isLt
  dsimp [addresses]
  constructor <;> omega
lemma edge_bounds (i : Input) (e : Fin i.k) (r : ℕ) (hr : r<4) :
    let l := addresses (i.n+3*i.k+2) i.n i.k
    l.active+e.val<l.powers ∧ Adjacency.nodeAddress l e+r<l.powers := by
  have he := e.isLt
  dsimp [addresses,Adjacency.nodeAddress]
  constructor <;> omega
lemma static_bounds (i : Input) (a : ℕ) (ha : a∈Adjacency.staticFootprint i (addresses (i.n+3*i.k+2) i.n i.k)) :
    a < (addresses (i.n+3*i.k+2) i.n i.k).powers := by
  simp only [Adjacency.staticFootprint,Finset.mem_union,Finset.mem_Ico] at ha
  dsimp [addresses] at ha ⊢
  rcases ha with ha | ha <;> omega
end DecrAlmostLinearSSSP.Decremental.Exact.Layout
end s107
section s108
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact
lemma queueMap_card {n : ℕ} (q : Multiset (ℕ × Fin n)) : (queueMap q).card=q.card := Multiset.card_map _ _
lemma queueMap_cons {n : ℕ} (key : ℕ) (v : Fin n) (q : Multiset (ℕ × Fin n)) :
    queueMap ((key,v)::ₘq)=(key,v.val)::ₘqueueMap q := Multiset.map_cons _ _ _
lemma queueMap_count {n h : ℕ} (tree : RadixQueue.Trie h) (q : Multiset (ℕ × Fin n))
    (hm : queueMap q=RadixQueue.entries tree 0) : RadixQueue.count tree=q.card := by
  have hh := congrArg Multiset.card hm
  simpa only [queueMap_card,RadixQueue.entries_card] using hh.symm
lemma queueMap_pop {n h : ℕ} (tree next : RadixQueue.Trie h) (q : Multiset (ℕ × Fin n))
    (key value : ℕ) (hm : queueMap q=RadixQueue.entries tree 0)
    (hp : RadixQueue.pop tree=some (key,value,next)) :
    ∃ (v : Fin n) (remaining : Multiset (ℕ × Fin n)), v.val=value ∧ q=(key,v)::ₘremaining ∧
      queueMap remaining=RadixQueue.entries next 0 ∧ (∀ item∈q, key ≤ item.1) := by
  classical
  obtain ⟨hbag,hmin⟩ := RadixQueue.pop_spec tree 0 key value next hp
  simp only [Nat.zero_add] at hbag hmin
  have hmapped : (key,value)∈queueMap q := by rw [hm,hbag];exact Multiset.mem_cons_self _ _
  obtain ⟨item,hitem,heq⟩ := Multiset.mem_map.mp hmapped
  rcases item with ⟨d,v⟩
  have hd : d=key := congrArg Prod.fst heq
  have hv : v.val=value := congrArg Prod.snd heq
  subst d
  let remaining := q.erase (key,v)
  have hcons : (key,v)::ₘremaining=q := Multiset.cons_erase hitem
  refine ⟨v,remaining,hv,hcons.symm,?_,?_⟩
  · apply (Multiset.cons_inj_right (key,value)).mp
    calc
      (key,value)::ₘqueueMap remaining = queueMap ((key,v)::ₘremaining) := by rw [queueMap_cons,hv]
      _ = queueMap q := congrArg queueMap hcons
      _ = RadixQueue.entries tree 0 := hm
      _ = (key,value)::ₘRadixQueue.entries next 0 := hbag
  · intro item hi
    have hmi : (item.1,item.2.val)∈RadixQueue.entries tree 0 := by
      rw [←hm]
      exact Multiset.mem_map.mpr ⟨item,hi,rfl⟩
    exact hmin _ hmi
lemma queueMap_insert {n h : ℕ} (tree : RadixQueue.Trie h) (q : Multiset (ℕ × Fin n))
    (key : ℕ) (v : Fin n) (hm : queueMap q=RadixQueue.entries tree 0) (hk : key<2^h) :
    queueMap ((key,v)::ₘq)=RadixQueue.entries (RadixQueue.insert h key v.val tree) 0 := by
  rw [queueMap_cons,RadixQueue.entries_insert h key v.val tree 0 hk]
  simp only [Nat.zero_add,hm]
end DecrAlmostLinearSSSP.Decremental.Exact
end s108
section s109
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Heap
open Structured
lemma Image.slot_not {n h : ℕ} {base slot : ℕ} {tree : LocatedTrie h} {queue : Multiset (ℕ × Fin n)} {s : Data}
    (h : Image base slot tree queue s) : slot ∉ tree.footprint := by
  intro hh
  have hh' := (h.bounded slot hh).1
  omega
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
theorem solution : (((((((∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (active : Finset.{0} (Fin k)) (w : Fin k → ENNReal)
  (u v : Fin n),
  Not (@DecrAlmostLinearSSSP.Decremental.Reachable n k g active u v) →
    @Eq.{1} ENNReal (@DecrAlmostLinearSSSP.Decremental.distance n k g active w u v)
      (@Top.top.{0} ENNReal ENNReal.instTop)) ∧ (∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (active : Finset.{0} (Fin k)) (w : Fin k → Real)
  (B : Real),
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) B →
    ∀ (u v : Fin n),
      Not (@DecrAlmostLinearSSSP.Decremental.Reachable n k g active u v) →
        @Eq.{1} Real (@DecrAlmostLinearSSSP.Decremental.cappedDistance n k g active w B u v) B)) ∧ ((∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (active : Finset.{0} (Fin k)) (w : Fin k → Real)
  (B c : Real),
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) B →
    @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) c →
      ∀ (u v : Fin n),
        @Eq.{1} ENNReal (@DecrAlmostLinearSSSP.Decremental.distance n k g active (fun e => ENNReal.ofReal (w e)) u v)
            (ENNReal.ofReal c) →
          @Eq.{1} Real (@DecrAlmostLinearSSSP.Decremental.cappedDistance n k g active w B u v)
            (@Min.min.{0} Real Real.instMin B c)) ∧ (∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (active : Finset.{0} (Fin k)) (w : Fin k → Real)
  (B : Real),
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) B →
    ∀ (u : Fin n),
      @Eq.{1} Real (@DecrAlmostLinearSSSP.Decremental.cappedDistance n k g active w B u u)
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))) ∧ (((∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (active : Finset.{0} (Fin k)) (w : Fin k → Real),
  (∀ (e : Fin k),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (w e)) →
    ∀ (B : Real),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) B →
        ∀ (u v : Fin n),
          @LT.lt.{0} Real Real.instLT (@DecrAlmostLinearSSSP.Decremental.cappedDistance n k g active w B u v) B →
            ∃ es,
              And (@DecrAlmostLinearSSSP.Decremental.Walk n k g active u v es)
                (@Eq.{1} Real (@List.sum.{0} Real Real.instAdd Real.instZero (@List.map.{0, 0} (Fin k) Real w es))
                  (@DecrAlmostLinearSSSP.Decremental.cappedDistance n k g active w B u v))) ∧ (∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (active : Finset.{0} (Fin k)) (w : Fin k → Real),
  (∀ (e : Fin k),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (w e)) →
    ∀ (B : Real),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) B →
        ∀ (t : Fin n) (e : Fin k),
          @Membership.mem.{0, 0} (Fin k) (Finset.{0} (Fin k))
              (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin k)) (Fin k) (@Finset.instSetLike.{0} (Fin k))) active e →
            @LE.le.{0} Real Real.instLE
              (@DecrAlmostLinearSSSP.Decremental.cappedDistance n k g active w B
                (@DecrAlmostLinearSSSP.Decremental.Digraph.tail n k g e) t)
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (w e)
                (@DecrAlmostLinearSSSP.Decremental.cappedDistance n k g active w B
                  (@DecrAlmostLinearSSSP.Decremental.Digraph.head n k g e) t)))) ∧ ((∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {u v : Fin n}
  {es : List.{0} (Fin k)},
  @DecrAlmostLinearSSSP.Decremental.Walk n k g active u v es →
    ∀ (p : Fin n → Real) (w : Fin k → Real),
      (∀ (e : Fin k),
          @Membership.mem.{0, 0} (Fin k) (Finset.{0} (Fin k))
              (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin k)) (Fin k) (@Finset.instSetLike.{0} (Fin k))) active e →
            @LE.le.{0} Real Real.instLE
              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                (p (@DecrAlmostLinearSSSP.Decremental.Digraph.tail n k g e))
                (p (@DecrAlmostLinearSSSP.Decremental.Digraph.head n k g e)))
              (w e)) →
        @LE.le.{0} Real Real.instLE (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (p u) (p v))
          (@List.sum.{0} Real Real.instAdd Real.instZero (@List.map.{0, 0} (Fin k) Real w es))) ∧ ((∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (active : Finset.{0} (Fin k)) (w : Fin k → Real),
  (∀ (e : Fin k),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (w e)) →
    ∀ (B : Real),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) B →
        ∀ (u v : Fin n) (p : Fin n → Real),
          (∀ (e : Fin k),
              @Membership.mem.{0, 0} (Fin k) (Finset.{0} (Fin k))
                  (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin k)) (Fin k) (@Finset.instSetLike.{0} (Fin k))) active
                  e →
                @LE.le.{0} Real Real.instLE
                  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                    (p (@DecrAlmostLinearSSSP.Decremental.Digraph.tail n k g e))
                    (p (@DecrAlmostLinearSSSP.Decremental.Digraph.head n k g e)))
                  (w e)) →
            @LT.lt.{0} Real Real.instLT (@DecrAlmostLinearSSSP.Decremental.cappedDistance n k g active w B u v) B →
              @LE.le.{0} Real Real.instLE (p u)
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (p v)
                  (@DecrAlmostLinearSSSP.Decremental.cappedDistance n k g active w B u v))) ∧ (∀ {k : Nat} (w : Fin k → Nat) (es : List.{0} (Fin k)),
  @Eq.{1} Real
    (@Nat.cast.{0} Real Real.instNatCast
      (@List.sum.{0} Nat instAddNat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)
        (@List.map.{0, 0} (Fin k) Nat w es)))
    (@List.sum.{0} Real Real.instAdd Real.instZero
      (@List.map.{0, 0} (Fin k) Real (fun e => @Nat.cast.{0} Real Real.instNatCast (w e)) es))))))) ∧ ((((∀ {k : Nat} (w : Fin k → Nat) (W : Nat),
  (∀ (e : Fin k), @LE.le.{0} Nat instLENat (w e) W) →
    ∀ (es : List.{0} (Fin k)),
      @LE.le.{0} Nat instLENat
        (@List.sum.{0} Nat instAddNat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)
          (@List.map.{0, 0} (Fin k) Nat w es))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@List.length.{0} (Fin k) es) W)) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (active : Finset.{0} (Fin i.k)) (v : Fin i.n),
      @DecrAlmostLinearSSSP.Decremental.Reachable i.n i.k i.graph active i.source v →
        ∃ d,
          And
            (@LE.le.{0} Nat instLENat d
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) i.n
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                i.W))
            (@Eq.{1} ENNReal
              (@DecrAlmostLinearSSSP.Decremental.distance i.n i.k i.graph active
                (fun e =>
                  @Nat.cast.{0} ENNReal
                    (@AddMonoidWithOne.toNatCast.{0} ENNReal
                      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                    (i.weight e))
                i.source v)
              (@Nat.cast.{0} ENNReal
                (@AddMonoidWithOne.toNatCast.{0} ENNReal
                  (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                d)))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
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
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) i.n i.W)) ∧ (∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (active : Finset.{0} (Fin k)) (w : Fin k → Nat)
  (s : Fin n) (z : Fin n → Nat),
  @Eq.{1} Nat (z s) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    (∀ (e : Fin k),
        @Membership.mem.{0, 0} (Fin k) (Finset.{0} (Fin k))
            (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin k)) (Fin k) (@Finset.instSetLike.{0} (Fin k))) active e →
          @LE.le.{0} Nat instLENat (z (@DecrAlmostLinearSSSP.Decremental.Digraph.head n k g e))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (z (@DecrAlmostLinearSSSP.Decremental.Digraph.tail n k g e)) (w e))) →
      ∀ (v : Fin n),
        @LE.le.{0} ENNReal ENNReal.instLE
          (@Nat.cast.{0} ENNReal
            (@AddMonoidWithOne.toNatCast.{0} ENNReal
              (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
            (z v))
          (@DecrAlmostLinearSSSP.Decremental.distance n k g active
            (fun e =>
              @Nat.cast.{0} ENNReal
                (@AddMonoidWithOne.toNatCast.{0} ENNReal
                  (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                (w e))
            s v)))) ∧ (((∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {w : Fin k → Nat}
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
                  key))) ∧ (∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (active : Finset.{0} (Fin k)) (w : Fin k → ENNReal)
  (s : Fin n),
  @Eq.{1} ENNReal (@DecrAlmostLinearSSSP.Decremental.distance n k g active w s s)
    (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero)))) ∧ ((∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (active : Finset.{0} (Fin k)) (w : Fin k → ENNReal)
  (s v : Fin n) (d : Nat),
  @LE.le.{0} ENNReal ENNReal.instLE (@DecrAlmostLinearSSSP.Decremental.distance n k g active w s v)
      (@Nat.cast.{0} ENNReal
        (@AddMonoidWithOne.toNatCast.{0} ENNReal
          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
        d) →
    @DecrAlmostLinearSSSP.Decremental.Reachable n k g active s v) ∧ ((∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (active : Finset.{0} (Fin k)) (w : Fin k → Nat)
  (s : Fin n) (e : Fin k),
  @Membership.mem.{0, 0} (Fin k) (Finset.{0} (Fin k))
      (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin k)) (Fin k) (@Finset.instSetLike.{0} (Fin k))) active e →
    ∀ (d : Nat),
      @LE.le.{0} ENNReal ENNReal.instLE
          (@DecrAlmostLinearSSSP.Decremental.distance n k g active
            (fun a =>
              @Nat.cast.{0} ENNReal
                (@AddMonoidWithOne.toNatCast.{0} ENNReal
                  (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                (w a))
            s (@DecrAlmostLinearSSSP.Decremental.Digraph.tail n k g e))
          (@Nat.cast.{0} ENNReal
            (@AddMonoidWithOne.toNatCast.{0} ENNReal
              (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
            d) →
        @LE.le.{0} ENNReal ENNReal.instLE
          (@DecrAlmostLinearSSSP.Decremental.distance n k g active
            (fun a =>
              @Nat.cast.{0} ENNReal
                (@AddMonoidWithOne.toNatCast.{0} ENNReal
                  (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                (w a))
            s (@DecrAlmostLinearSSSP.Decremental.Digraph.head n k g e))
          (@Nat.cast.{0} ENNReal
            (@AddMonoidWithOne.toNatCast.{0} ENNReal
              (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d (w e)))) ∧ (∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (active : Finset.{0} (Fin k)) (w : Fin k → Nat)
  (source : Fin n),
  @DecrAlmostLinearSSSP.Decremental.Exact.LabelInvariant n k g active w source
    (@DecrAlmostLinearSSSP.Decremental.Exact.initialTentative n source)
    (@EmptyCollection.emptyCollection.{0} (Finset.{0} (Fin n)) (@Finset.instEmptyCollection.{0} (Fin n)))
    (@Singleton.singleton.{0, 0} (Prod.{0, 0} Nat (Fin n)) (Multiset.{0} (Prod.{0, 0} Nat (Fin n)))
      (@Multiset.instSingleton.{0} (Prod.{0, 0} Nat (Fin n)))
      (@Prod.mk.{0, 0} Nat (Fin n) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) source)))))))) ∧ (((((∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {u v : Fin n}
  {es : List.{0} (Fin k)},
  @DecrAlmostLinearSSSP.Decremental.Walk n k g active u v es →
    ∀ (P : Fin n → Prop),
      (∀ (e : Fin k),
          @Membership.mem.{0, 0} (Fin k) (Finset.{0} (Fin k))
              (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin k)) (Fin k) (@Finset.instSetLike.{0} (Fin k))) active e →
            P (@DecrAlmostLinearSSSP.Decremental.Digraph.tail n k g e) →
              P (@DecrAlmostLinearSSSP.Decremental.Digraph.head n k g e)) →
        P u → P v) ∧ (∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {w : Fin k → Nat}
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
          (Not (@DecrAlmostLinearSSSP.Decremental.Reachable n k g active source v))))) ∧ ((∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {w : Fin k → Nat}
  {source : Fin n} {tentative : Fin n → Option.{0} Nat} {settled : Finset.{0} (Fin n)}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin n))},
  @DecrAlmostLinearSSSP.Decremental.Exact.LabelInvariant n k g active w source tentative settled queue →
    ∀ (target : Fin n) (candidate : Nat),
      target ∉ settled →
        (∀ (d : Nat),
            @Eq.{1} (Option.{0} Nat) (tentative target) (@Option.some.{0} Nat d) →
              @LT.lt.{0} Nat instLTNat candidate d) →
          @LE.le.{0} ENNReal ENNReal.instLE
              (@DecrAlmostLinearSSSP.Decremental.distance n k g active
                (fun e =>
                  @Nat.cast.{0} ENNReal
                    (@AddMonoidWithOne.toNatCast.{0} ENNReal
                      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                    (w e))
                source target)
              (@Nat.cast.{0} ENNReal
                (@AddMonoidWithOne.toNatCast.{0} ENNReal
                  (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                candidate) →
            (∀ (v : Fin n),
                @Membership.mem.{0, 0} (Fin n) (Finset.{0} (Fin n))
                    (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin n)) (Fin n) (@Finset.instSetLike.{0} (Fin n)))
                    settled v →
                  ∀ (d : Nat),
                    @Eq.{1} (Option.{0} Nat) (tentative v) (@Option.some.{0} Nat d) →
                      @LE.le.{0} Nat instLENat d candidate) →
              @DecrAlmostLinearSSSP.Decremental.Exact.LabelInvariant n k g active w source
                (@Function.update.{1, 1} (Fin n) (fun a => Option.{0} Nat) (instDecidableEqFin n) tentative target
                  (@Option.some.{0} Nat candidate))
                settled
                (@Multiset.cons.{0} (Prod.{0, 0} Nat (Fin n)) (@Prod.mk.{0, 0} Nat (Fin n) candidate target) queue)) ∧ (∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {w : Fin k → Nat}
  {source : Fin n} {tentative : Fin n → Option.{0} Nat} {settled : Finset.{0} (Fin n)}
  {remaining : Multiset.{0} (Prod.{0, 0} Nat (Fin n))} (key : Nat) (v : Fin n),
  @DecrAlmostLinearSSSP.Decremental.Exact.LabelInvariant n k g active w source tentative settled
      (@Multiset.cons.{0} (Prod.{0, 0} Nat (Fin n)) (@Prod.mk.{0, 0} Nat (Fin n) key v) remaining) →
    v ∉ settled →
      @Eq.{1} (Option.{0} Nat) (tentative v) (@Option.some.{0} Nat key) →
        @Eq.{1} ENNReal
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
              key) →
          (∀ (item : Prod.{0, 0} Nat (Fin n)),
              @Membership.mem.{0, 0} (Prod.{0, 0} Nat (Fin n)) (Multiset.{0} (Prod.{0, 0} Nat (Fin n)))
                  (@Multiset.instMembership.{0} (Prod.{0, 0} Nat (Fin n))) remaining item →
                @LE.le.{0} Nat instLENat key (@Prod.fst.{0, 0} Nat (Fin n) item)) →
            (∀ (e : Fin k),
                @Membership.mem.{0, 0} (Fin k) (Finset.{0} (Fin k))
                    (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin k)) (Fin k) (@Finset.instSetLike.{0} (Fin k)))
                    active e →
                  @Eq.{1} (Fin n) (@DecrAlmostLinearSSSP.Decremental.Digraph.tail n k g e) v →
                    ∃ dh,
                      And
                        (@Eq.{1} (Option.{0} Nat) (tentative (@DecrAlmostLinearSSSP.Decremental.Digraph.head n k g e))
                          (@Option.some.{0} Nat dh))
                        (@LE.le.{0} Nat instLENat dh
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) key (w e)))) →
              @DecrAlmostLinearSSSP.Decremental.Exact.LabelInvariant n k g active w source tentative
                (@Insert.insert.{0, 0} (Fin n) (Finset.{0} (Fin n))
                  (@Finset.instInsert.{0} (Fin n) (instDecidableEqFin n)) v settled)
                remaining))) ∧ (((∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (t : Nat) (ht : @LT.lt.{0} Nat instLTNat t k)
  (v : Fin n),
  @Eq.{1} (List.{0} (Fin k))
    (@DecrAlmostLinearSSSP.Decremental.Exact.adjacency n k g
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      v)
    (@ite.{1} (List.{0} (Fin k))
      (@Eq.{1} (Fin n) (@DecrAlmostLinearSSSP.Decremental.Digraph.tail n k g (@Fin.mk k t ht)) v)
      (instDecidableEqFin n (@DecrAlmostLinearSSSP.Decremental.Digraph.tail n k g (@Fin.mk k t ht)) v)
      (@List.cons.{0} (Fin k) (@Fin.mk k t ht) (@DecrAlmostLinearSSSP.Decremental.Exact.adjacency n k g t v))
      (@DecrAlmostLinearSSSP.Decremental.Exact.adjacency n k g t v))) ∧ (∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (t : Nat) (v : Fin n) (e : Fin k),
  Iff
    (@Membership.mem.{0, 0} (Fin k) (List.{0} (Fin k)) (@List.instMembership.{0} (Fin k))
      (@DecrAlmostLinearSSSP.Decremental.Exact.adjacency n k g t v) e)
    (And (@LT.lt.{0} Nat instLTNat (@Fin.val k e) t)
      (@Eq.{1} (Fin n) (@DecrAlmostLinearSSSP.Decremental.Digraph.tail n k g e) v)))) ∧ ((∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (t : Nat) (v : Fin n),
  @List.Nodup.{0} (Fin k) (@DecrAlmostLinearSSSP.Decremental.Exact.adjacency n k g t v)) ∧ ((∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (t : Nat),
  @LE.le.{0} Nat instLENat t k →
    @Eq.{1} Nat (∑ v, @List.length.{0} (Fin k) (@DecrAlmostLinearSSSP.Decremental.Exact.adjacency n k g t v)) t) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.clearPrepare s
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    (DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.clearPrepared s)))))) ∧ ((((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.prepare s
    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
    (DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.prepared s)) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.edge s
    (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))
    (DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.advanced s))) ∧ ((∀
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
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.edge j) ∧ ((∀ (j : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.code j) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
    have tail := s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 298) (instOfNatNat (nat_lit 298))));
    have head :=
      s.natMem
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 298) (instOfNatNat (nat_lit 298))))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))));
    have weight :=
      s.natMem
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 298) (instOfNatNat (nat_lit 298))))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))));
    have headSlot :=
      @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 224) (instOfNatNat (nat_lit 224)))) tail;
    have next := s.natMem headSlot;
    have node := s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 296) (instOfNatNat (nat_lit 296)));
    And
      (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.advanced s).natMem
        (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
          (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
            (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
              (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
                (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
                  (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natMem node head)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) node
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 294) (instOfNatNat (nat_lit 294)))))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) node
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                next)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) node
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              weight)
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 294) (instOfNatNat (nat_lit 294))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          headSlot node))
      (And
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.advanced s).natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 294) (instOfNatNat (nat_lit 294))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 294) (instOfNatNat (nat_lit 294))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (And
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.advanced s).natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 296) (instOfNatNat (nat_lit 296))))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 296) (instOfNatNat (nat_lit 296))))
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
          (And
            (@Eq.{1} Nat
              ((DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.advanced s).natReg
                (@OfNat.ofNat.{0} Nat (nat_lit 298) (instOfNatNat (nat_lit 298))))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 298) (instOfNatNat (nat_lit 298))))
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
            (And
              (@Eq.{1} Nat
                ((DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.advanced s).natReg
                  (@OfNat.ofNat.{0} Nat (nat_lit 300) (instOfNatNat (nat_lit 300))))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 300) (instOfNatNat (nat_lit 300))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.advanced s).realMem
                s.realMem))))))))) ∧ (((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (i : DecrAlmostLinearSSSP.Decremental.Input) (e : Fin i.k)
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
          (@Fin.val i.n (@DecrAlmostLinearSSSP.Decremental.Digraph.head i.n i.k i.graph e)) (i.weight e)))) ∧ (∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (i : DecrAlmostLinearSSSP.Decremental.Input) (address : Nat),
  @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
      address →
    @Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.initialMachine p i).natMem address)
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) ∧ ((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (i : DecrAlmostLinearSSSP.Decremental.Input) (address : Nat),
  @Eq.{1} Real ((DecrAlmostLinearSSSP.Decremental.initialMachine p i).realMem address)
    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) ∧ ((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (i : DecrAlmostLinearSSSP.Decremental.Input) (B F : Nat),
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
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))) ∧ (∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (i : DecrAlmostLinearSSSP.Decremental.Input),
  DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.Tape i
    (DecrAlmostLinearSSSP.Decremental.Structured.data (DecrAlmostLinearSSSP.Decremental.initialMachine p i))))))))) ∧ ((((((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (s t : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.Tape i s →
    (∀ (a : Nat),
        @LT.lt.{0} Nat instLTNat a
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k)) →
          @Eq.{1} Nat (t.natMem a) (s.natMem a)) →
      DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.Tape i t) ∧ (∀ (l : DecrAlmostLinearSSSP.Decremental.Exact.Layout.Addresses) {k : Nat} (e : Fin k) (es : List.{0} (Fin k)),
  @Eq.{1} Nat (@DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.root l k (@List.cons.{0} (Fin k) e es))
    (@DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.nodeAddress l k e))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (e : Fin i.k),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
    (@DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.nodeAddress
      (DecrAlmostLinearSSSP.Decremental.Exact.Layout.addresses
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        i.n i.k)
      i.k e)) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (e : Fin i.k) (memory : Nat → Nat) (v : Fin i.n),
  have l :=
    DecrAlmostLinearSSSP.Decremental.Exact.Layout.addresses
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      i.n i.k;
  @Eq.{1} Nat
    (DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.insertMemory i l e memory
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) l.heads (@Fin.val i.n v)))
    (@ite.{1} Nat (@Eq.{1} (Fin i.n) v (@DecrAlmostLinearSSSP.Decremental.Digraph.tail i.n i.k i.graph e))
      (instDecidableEqFin i.n v (@DecrAlmostLinearSSSP.Decremental.Digraph.tail i.n i.k i.graph e))
      (@DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.nodeAddress l i.k e)
      (memory (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) l.heads (@Fin.val i.n v))))))) ∧ (((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (e f : Fin i.k) (memory : Nat → Nat),
  have l :=
    DecrAlmostLinearSSSP.Decremental.Exact.Layout.addresses
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      i.n i.k;
  @Eq.{1} Nat
    (DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.insertMemory i l e memory
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) l.active (@Fin.val i.k f)))
    (@ite.{1} Nat (@Eq.{1} (Fin i.k) f e) (instDecidableEqFin i.k f e)
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (memory (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) l.active (@Fin.val i.k f))))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (e f : Fin i.k),
  @Ne.{1} (Fin i.k) f e →
    ∀ (r : Nat),
      @LT.lt.{0} Nat instLTNat r (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
        ∀ (memory : Nat → Nat),
          have l :=
            DecrAlmostLinearSSSP.Decremental.Exact.Layout.addresses
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              i.n i.k;
          @Eq.{1} Nat
            (DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.insertMemory i l e memory
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.nodeAddress l i.k f) r))
            (memory
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.nodeAddress l i.k f) r)))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (e : Fin i.k) (memory : Nat → Nat),
  have l :=
    DecrAlmostLinearSSSP.Decremental.Exact.Layout.addresses
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      i.n i.k;
  have updated := DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.insertMemory i l e memory;
  And
    (@Eq.{1} Nat (updated (@DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.nodeAddress l i.k e))
      (@Fin.val i.n (@DecrAlmostLinearSSSP.Decremental.Digraph.head i.n i.k i.graph e)))
    (And
      (@Eq.{1} Nat
        (updated
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.nodeAddress l i.k e)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) l.active (@Fin.val i.k e)))
      (And
        (@Eq.{1} Nat
          (updated
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.nodeAddress l i.k e)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (memory
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) l.heads
              (@Fin.val i.n (@DecrAlmostLinearSSSP.Decremental.Digraph.tail i.n i.k i.graph e)))))
        (@Eq.{1} Nat
          (updated
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.nodeAddress l i.k e)
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
          (i.weight e))))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (e : Fin i.k) (memory : Nat → Nat) (a : Nat),
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
    @Eq.{1} Nat
      (DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.insertMemory i
        (DecrAlmostLinearSSSP.Decremental.Exact.Layout.addresses
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          i.n i.k)
        e memory a)
      (memory a)) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (t : Nat) (ht : @LT.lt.{0} Nat instLTNat t i.k)
  (s u : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.Image i
      (DecrAlmostLinearSSSP.Decremental.Exact.Layout.addresses
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        i.n i.k)
      t s →
    @Eq.{1} (Nat → Nat) u.natMem
        (DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.insertMemory i
          (DecrAlmostLinearSSSP.Decremental.Exact.Layout.addresses
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            i.n i.k)
          (@Fin.mk i.k t ht) s.natMem) →
      DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.Image i
        (DecrAlmostLinearSSSP.Decremental.Exact.Layout.addresses
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          i.n i.k)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        u))))) ∧ ((((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (upto : Nat) (ht : @LT.lt.{0} Nat instLTNat upto i.k)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.Prefix i upto s →
    @Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.advanced s).natMem
      (DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.insertMemory i
        (DecrAlmostLinearSSSP.Decremental.Exact.Layout.addresses
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          i.n i.k)
        (@Fin.mk i.k upto ht) s.natMem)) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (upto : Nat),
  @LT.lt.{0} Nat instLTNat upto i.k →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
      DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.Prefix i upto s →
        DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.Prefix i
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) upto
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.advanced s))) ∧ ((∀
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
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.loop j) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (remaining upto : Nat),
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
                    @Eq.{1} Nat (t.natMem a) (s.natMem a))))) ∧ (∀
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
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.setup j)))) ∧ (((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
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
                          @Eq.{1} Nat (t.natMem a) (s.natMem a))))) ∧ (∀ {s u t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {c d : Nat},
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.setup s c u →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.loop u d t →
      DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.code s
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c d) t)) ∧ ((∀
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
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.code j) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
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
                          @Eq.{1} Nat (t.natMem a) (s.natMem a))))) ∧ (∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (upto : Nat) (v : Fin n) (e : Fin k)
  (es : List.{0} (Fin k)),
  @Eq.{1} (List.{0} (Fin k)) (@DecrAlmostLinearSSSP.Decremental.Exact.adjacency n k g upto v)
      (@List.cons.{0} (Fin k) e es) →
    And (@Eq.{1} (List.{0} (Fin k)) es (@DecrAlmostLinearSSSP.Decremental.Exact.adjacency n k g (@Fin.val k e) v))
      (And (@Eq.{1} (Fin n) (@DecrAlmostLinearSSSP.Decremental.Digraph.tail n k g e) v)
        (@LT.lt.{0} Nat instLTNat (@Fin.val k e) upto)))))))) ∧ (((((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (l : DecrAlmostLinearSSSP.Decremental.Exact.Layout.Addresses)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (upto : Nat),
  DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.Image i l upto s →
    ∀ (v : Fin i.n),
      @DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.Chain i.k l s
        (@DecrAlmostLinearSSSP.Decremental.Exact.adjacency i.n i.k i.graph upto v)) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {l : DecrAlmostLinearSSSP.Decremental.Exact.Layout.Addresses}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.Image i l i.k s →
    DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.StaticImage i l s)) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {l : DecrAlmostLinearSSSP.Decremental.Exact.Layout.Addresses}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.Image i l i.k s →
    DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.ActiveImage i l (@List.nil.{0} (Fin i.k)) s) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {l : DecrAlmostLinearSSSP.Decremental.Exact.Layout.Addresses}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.StaticImage i l s →
    (∀ (a : Nat),
        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
            (DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.staticFootprint i l) a →
          @Eq.{1} Nat (t.natMem a) (s.natMem a)) →
      DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.StaticImage i l t))) ∧ (((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {l : DecrAlmostLinearSSSP.Decremental.Exact.Layout.Addresses}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.StaticImage i l s →
    ∀ (v : Fin i.n),
      @DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.Chain i.k l s
        (@DecrAlmostLinearSSSP.Decremental.Exact.adjacency i.n i.k i.graph i.k v)) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {l : DecrAlmostLinearSSSP.Decremental.Exact.Layout.Addresses}
  {tentative : Fin i.n → Option.{0} Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.TentativeImage i l tentative s →
    ∀ (v : Fin i.n) (d : Nat),
      @Eq.{1} (Option.{0} Nat) (tentative v) (@Option.some.{0} Nat d) →
        And (@Eq.{1} Nat (s.natMem (@Fin.val i.n v)) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (And
            (@Eq.{1} Nat
              (s.natMem (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) l.distances (@Fin.val i.n v)))
              d)
            (@Eq.{1} Real (s.realMem (@Fin.val i.n v)) (@Nat.cast.{0} Real Real.instNatCast d))))) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {l : DecrAlmostLinearSSSP.Decremental.Exact.Layout.Addresses}
  {tentative : Fin i.n → Option.{0} Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.TentativeImage i l tentative s →
    ∀ (v : Fin i.n),
      @Eq.{1} (Option.{0} Nat) (tentative v) (@Option.none.{0} Nat) →
        @Eq.{1} Nat (s.natMem (@Fin.val i.n v)) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {l : DecrAlmostLinearSSSP.Decremental.Exact.Layout.Addresses}
  {tentative : Fin i.n → Option.{0} Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.TentativeImage i l tentative s →
    ∀ (v : Fin i.n),
      Iff (@Eq.{1} Nat (s.natMem (@Fin.val i.n v)) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@Eq.{1} (Option.{0} Nat) (tentative v) (@Option.none.{0} Nat))) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {l : DecrAlmostLinearSSSP.Decremental.Exact.Layout.Addresses}
  {tentative : Fin i.n → Option.{0} Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.TentativeImage i l tentative s →
    ∀ (v : Fin i.n),
      @Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.stored s.machine (@Fin.val i.n v))
        (DecrAlmostLinearSSSP.Decremental.Exact.tentativeValue (tentative v))))))) ∧ ((((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {l : DecrAlmostLinearSSSP.Decremental.Exact.Layout.Addresses}
  {tentative : Fin i.n → Option.{0} Nat} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.TentativeImage i l tentative s →
    (∀ (v : Fin i.n), @Eq.{1} Nat (t.natMem (@Fin.val i.n v)) (s.natMem (@Fin.val i.n v))) →
      (∀ (v : Fin i.n),
          @Eq.{1} Nat
            (t.natMem (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) l.distances (@Fin.val i.n v)))
            (s.natMem (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) l.distances (@Fin.val i.n v)))) →
        (∀ (v : Fin i.n), @Eq.{1} Real (t.realMem (@Fin.val i.n v)) (s.realMem (@Fin.val i.n v))) →
          DecrAlmostLinearSSSP.Decremental.Exact.TentativeImage i l tentative t) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (v : Fin i.n),
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
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) l.distances (@Fin.val i.n v)) l.powers))))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (e : Fin i.k) (r : Nat),
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
        l.powers)) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (a : Nat),
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
          i.n i.k).powers) ∧ (∀ {n : Nat} (q : Multiset.{0} (Prod.{0, 0} Nat (Fin n))),
  @Eq.{1} Nat (@Multiset.card.{0} (Prod.{0, 0} Nat Nat) (@DecrAlmostLinearSSSP.Decremental.Exact.queueMap n q))
    (@Multiset.card.{0} (Prod.{0, 0} Nat (Fin n)) q))))) ∧ (((∀ {n : Nat} (key : Nat) (v : Fin n) (q : Multiset.{0} (Prod.{0, 0} Nat (Fin n))),
  @Eq.{1} (Multiset.{0} (Prod.{0, 0} Nat Nat))
    (@DecrAlmostLinearSSSP.Decremental.Exact.queueMap n
      (@Multiset.cons.{0} (Prod.{0, 0} Nat (Fin n)) (@Prod.mk.{0, 0} Nat (Fin n) key v) q))
    (@Multiset.cons.{0} (Prod.{0, 0} Nat Nat) (@Prod.mk.{0, 0} Nat Nat key (@Fin.val n v))
      (@DecrAlmostLinearSSSP.Decremental.Exact.queueMap n q))) ∧ (∀ {n h : Nat} (tree : DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie h) (q : Multiset.{0} (Prod.{0, 0} Nat (Fin n))),
  @Eq.{1} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (@DecrAlmostLinearSSSP.Decremental.Exact.queueMap n q)
      (@DecrAlmostLinearSSSP.Decremental.RadixQueue.entries h tree
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
    @Eq.{1} Nat (@DecrAlmostLinearSSSP.Decremental.RadixQueue.count h tree)
      (@Multiset.card.{0} (Prod.{0, 0} Nat (Fin n)) q))) ∧ ((∀ {n h : Nat} (tree next : DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie h)
  (q : Multiset.{0} (Prod.{0, 0} Nat (Fin n))) (key value : Nat),
  @Eq.{1} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (@DecrAlmostLinearSSSP.Decremental.Exact.queueMap n q)
      (@DecrAlmostLinearSSSP.Decremental.RadixQueue.entries h tree
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
    @Eq.{1} (Option.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie h))))
        (@DecrAlmostLinearSSSP.Decremental.RadixQueue.pop h tree)
        (@Option.some.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie h)))
          (@Prod.mk.{0, 0} Nat (Prod.{0, 0} Nat (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie h)) key
            (@Prod.mk.{0, 0} Nat (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie h) value next))) →
      ∃ v remaining,
        And (@Eq.{1} Nat (@Fin.val n v) value)
          (And
            (@Eq.{1} (Multiset.{0} (Prod.{0, 0} Nat (Fin n))) q
              (@Multiset.cons.{0} (Prod.{0, 0} Nat (Fin n)) (@Prod.mk.{0, 0} Nat (Fin n) key v) remaining))
            (And
              (@Eq.{1} (Multiset.{0} (Prod.{0, 0} Nat Nat))
                (@DecrAlmostLinearSSSP.Decremental.Exact.queueMap n remaining)
                (@DecrAlmostLinearSSSP.Decremental.RadixQueue.entries h next
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (∀ (item : Prod.{0, 0} Nat (Fin n)),
                @Membership.mem.{0, 0} (Prod.{0, 0} Nat (Fin n)) (Multiset.{0} (Prod.{0, 0} Nat (Fin n)))
                    (@Multiset.instMembership.{0} (Prod.{0, 0} Nat (Fin n))) q item →
                  @LE.le.{0} Nat instLENat key (@Prod.fst.{0, 0} Nat (Fin n) item))))) ∧ ((∀ {n h : Nat} (tree : DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie h) (q : Multiset.{0} (Prod.{0, 0} Nat (Fin n)))
  (key : Nat) (v : Fin n),
  @Eq.{1} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (@DecrAlmostLinearSSSP.Decremental.Exact.queueMap n q)
      (@DecrAlmostLinearSSSP.Decremental.RadixQueue.entries h tree
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
    @LT.lt.{0} Nat instLTNat key
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h) →
      @Eq.{1} (Multiset.{0} (Prod.{0, 0} Nat Nat))
        (@DecrAlmostLinearSSSP.Decremental.Exact.queueMap n
          (@Multiset.cons.{0} (Prod.{0, 0} Nat (Fin n)) (@Prod.mk.{0, 0} Nat (Fin n) key v) q))
        (@DecrAlmostLinearSSSP.Decremental.RadixQueue.entries h
          (DecrAlmostLinearSSSP.Decremental.RadixQueue.insert h key (@Fin.val n v) tree)
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) ∧ (∀ {n h base slot : Nat} {tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin n))} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  @DecrAlmostLinearSSSP.Decremental.Exact.Heap.Image n h base slot tree queue s →
    slot ∉ @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint h tree)))))))) := by
  exact ⟨⟨⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.distance_unreachable,DecrAlmostLinearSSSP.Decremental.cappedDistance_unreachable⟩,⟨DecrAlmostLinearSSSP.Decremental.cappedDistance_of_distance,DecrAlmostLinearSSSP.Decremental.cappedDistance_self⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.cappedDistance_lt_walk,DecrAlmostLinearSSSP.Decremental.cappedDistance_edge⟩,⟨DecrAlmostLinearSSSP.Decremental.Walk.label_le_weight,⟨DecrAlmostLinearSSSP.Decremental.cappedDistance_label_bound,DecrAlmostLinearSSSP.Decremental.Exact.nat_weight_real_sum⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.nat_weight_upper,DecrAlmostLinearSSSP.Decremental.Exact.reachable_nat_distance⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.candidate_key_bound,DecrAlmostLinearSSSP.Decremental.Exact.nat_feasible_distance⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.LabelInvariant.pop_exact,DecrAlmostLinearSSSP.Decremental.Exact.distance_self_zero⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.reachable_of_nat_bound,⟨DecrAlmostLinearSSSP.Decremental.Exact.distance_edge_bound,DecrAlmostLinearSSSP.Decremental.Exact.labelInvariant_initial⟩⟩⟩⟩⟩,⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.Walk.closed_predicate,DecrAlmostLinearSSSP.Decremental.Exact.LabelInvariant.finished⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.LabelInvariant.decrease,DecrAlmostLinearSSSP.Decremental.Exact.LabelInvariant.settle⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.adjacency_step,DecrAlmostLinearSSSP.Decremental.Exact.adjacency_mem⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.adjacency_nodup,⟨DecrAlmostLinearSSSP.Decremental.Exact.adjacency_total,DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.clearPrepare_eval⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.prepare_eval,DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.edge_eval⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.edge_nat_frame,⟨DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.code_real_frame,DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.edge_fields⟩⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.initial_nat_tape,DecrAlmostLinearSSSP.Decremental.initial_nat_above_tape⟩,⟨DecrAlmostLinearSSSP.Decremental.initial_real_zero,⟨DecrAlmostLinearSSSP.Decremental.initial_source_bank_zero,DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.tape_initial⟩⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.tape_frame,DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.root_cons⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.node_positive,DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.insert_heads⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.insert_active,DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.insert_old_node⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.insert_new_node,⟨DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.insert_frame,DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.image_insert⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.step_memory,DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.step_prefix⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.loop_nat_frame,⟨DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.loop_eval,DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.setup_nat_frame⟩⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.setup_eval,DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.append_loop⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.code_nat_frame,⟨DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.code_eval,DecrAlmostLinearSSSP.Decremental.Exact.adjacency_head⟩⟩⟩⟩⟩,⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.image_chain,DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.Image.static⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.Image.active_initial,DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.StaticImage.frame⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.StaticImage.chain,DecrAlmostLinearSSSP.Decremental.Exact.TentativeImage.finite⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.TentativeImage.infinite,⟨DecrAlmostLinearSSSP.Decremental.Exact.TentativeImage.flag_one,DecrAlmostLinearSSSP.Decremental.Exact.TentativeImage.stored⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.TentativeImage.frame,DecrAlmostLinearSSSP.Decremental.Exact.Layout.vertex_bounds⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.Layout.edge_bounds,⟨DecrAlmostLinearSSSP.Decremental.Exact.Layout.static_bounds,DecrAlmostLinearSSSP.Decremental.Exact.queueMap_card⟩⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.queueMap_cons,DecrAlmostLinearSSSP.Decremental.Exact.queueMap_count⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.queueMap_pop,⟨DecrAlmostLinearSSSP.Decremental.Exact.queueMap_insert,DecrAlmostLinearSSSP.Decremental.Exact.Heap.Image.slot_not⟩⟩⟩⟩⟩⟩⟩
