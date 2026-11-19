-- Prove2me | solution 1 for DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_7
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T11:14:39.572212+00:00
-- url     : https://prove2.me/submissions/8954c274-0306-4246-9021-8f2caf0b4ff4

import Definitions.Def_DecrAlmostLinearSSSP_RAMFoundation
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_2
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_3
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_4
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_5
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_6
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
theorem DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Bounded.mono : ∀ {height : Nat} {tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie height} {low high low' high' : Nat},
  @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Bounded height tree low high →
    @LE.le.{0} Nat instLENat low' low →
      @LE.le.{0} Nat instLENat high high' →
        @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Bounded height tree low' high' := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.1.1.2.2.2.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.Structured.eval_loadN : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (d a : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.loadN d a) s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    { realReg := s.realReg,
      natReg := @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natReg d (s.natMem (s.natReg a)),
      realMem := s.realMem, natMem := s.natMem } := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.2.1.1.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.Exact.TriePush.code_result : ∀ (h : Nat) (tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h) (low base : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 236) (instOfNatNat (nat_lit 236)))) h →
        @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image s h tree →
          @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Separated h tree →
            @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Bounded h tree low
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))) →
              @Eq.{1} Nat (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 246) (instOfNatNat (nat_lit 246)))))
                  (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root h tree) →
                @LE.le.{0} Nat instLENat low
                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 246) (instOfNatNat (nat_lit 246)))) →
                  @LT.lt.{0} Nat instLTNat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 246) (instOfNatNat (nat_lit 246))))
                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))) →
                    s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 246) (instOfNatNat (nat_lit 246))) ∉
                        @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint h tree →
                      (∀ (j : Nat),
                          @LT.lt.{0} Nat instLTNat j h →
                            @Eq.{1} Nat
                              (s.natMem (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base j))
                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)) →
                        @LE.le.{0} Nat instLENat
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base h) low →
                          (@Ne.{1} Nat h (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                              @Eq.{1} Nat
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 238) (instOfNatNat (nat_lit 238))))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base h)) →
                            ∃ cost t next,
                              And
                                (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                  DecrAlmostLinearSSSP.Decremental.Exact.TriePush.code s cost t)
                                (And
                                  (@LE.le.{0} Nat instLENat cost
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 43) (instOfNatNat (nat_lit 43)))
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                  (And
                                    (@Eq.{1} Nat
                                      (t.natMem
                                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 246) (instOfNatNat (nat_lit 246)))))
                                      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root h next))
                                    (And (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image t h next)
                                      (And (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Separated h next)
                                        (And
                                          (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Bounded h next low
                                            (t.natReg
                                              (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))))
                                          (And
                                            (@Eq.{1} (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie h)
                                              (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.abstract h next)
                                              (DecrAlmostLinearSSSP.Decremental.RadixQueue.insert h
                                                (s.natReg
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260))))
                                                (s.natReg
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 262) (instOfNatNat (nat_lit 262))))
                                                (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.abstract h tree)))
                                            (And
                                              (@LE.le.{0} Nat instLENat
                                                (s.natReg
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))
                                                (t.natReg
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))))
                                              (And
                                                (@LE.le.{0} (Finset.{0} Nat)
                                                  (@Preorder.toLE.{0} (Finset.{0} Nat)
                                                    (@PartialOrder.toPreorder.{0} (Finset.{0} Nat)
                                                      (@Finset.instPartialOrder.{0} Nat)))
                                                  (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint h next)
                                                  (@Union.union.{0} (Finset.{0} Nat)
                                                    (@Finset.instUnion.{0} Nat instDecidableEqNat)
                                                    (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint h
                                                      tree)
                                                    (@Finset.Ico.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                                                      (s.natReg
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 244)
                                                          (instOfNatNat (nat_lit 244))))
                                                      (t.natReg
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 244)
                                                          (instOfNatNat (nat_lit 244)))))))
                                                (And (@Eq.{1} (Nat → Real) t.realMem s.realMem)
                                                  (∀ (address : Nat),
                                                    @Ne.{1} Nat address
                                                        (s.natReg
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 246)
                                                            (instOfNatNat (nat_lit 246)))) →
                                                      address ∉
                                                          @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint
                                                            h tree →
                                                        Or
                                                            (@LT.lt.{0} Nat instLTNat address
                                                              (s.natReg
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 244)
                                                                  (instOfNatNat (nat_lit 244)))))
                                                            (@LE.le.{0} Nat instLENat
                                                              (t.natReg
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 244)
                                                                  (instOfNatNat (nat_lit 244))))
                                                              address) →
                                                          @Eq.{1} Nat (t.natMem address) (s.natMem address))))))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_3.2.2.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.TriePop.Result.nat_frame : ∀ {h : Nat} {tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  (r : @DecrAlmostLinearSSSP.Decremental.Exact.TriePop.Result h tree s),
  ∀ k ∉ DecrAlmostLinearSSSP.Decremental.Exact.TriePop.registers,
    @Eq.{1} Nat ((@DecrAlmostLinearSSSP.Decremental.Exact.TriePop.Result.final h tree s r).natReg k) (s.natReg k) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.1.1.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image.read_count : ∀ {h : Nat} (tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image s h tree →
    @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Separated h tree →
      @Eq.{1} Nat
        (@ite.{1} Nat
          (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root h tree))
          (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root h tree))
          (s.natMem (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root h tree))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@DecrAlmostLinearSSSP.Decremental.RadixQueue.count h
          (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.abstract h tree)) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.1.1.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.TriePop.code_nat_frame : ∀ k ∉ DecrAlmostLinearSSSP.Decremental.Exact.TriePop.registers,
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.TriePop.code k := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.1.1.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.TriePop.code_real_frame : ∀ (k : Nat), DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Exact.TriePop.code k := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.1.1.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.TriePop.code_result : ∀ (h : Nat) (tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h) (low base : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 236) (instOfNatNat (nat_lit 236)))) h →
        @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image s h tree →
          @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Separated h tree →
            @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Bounded h tree low
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))) →
              @Eq.{1} Nat (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 246) (instOfNatNat (nat_lit 246)))))
                  (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root h tree) →
                @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                    (@DecrAlmostLinearSSSP.Decremental.RadixQueue.count h
                      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.abstract h tree)) →
                  (∀ (j : Nat),
                      @LT.lt.{0} Nat instLTNat j h →
                        @Eq.{1} Nat (s.natMem (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base j))
                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)) →
                    @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base h)
                        low →
                      (@Ne.{1} Nat h (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                          @Eq.{1} Nat
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 238) (instOfNatNat (nat_lit 238))))
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base h)) →
                        ∃ cost t next key,
                          And
                            (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                              DecrAlmostLinearSSSP.Decremental.Exact.TriePop.code s cost t)
                            (And
                              (@LE.le.{0} Nat instLENat cost
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 34) (instOfNatNat (nat_lit 34)))
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                              (And
                                (@Eq.{1}
                                  (Option.{0}
                                    (Prod.{0, 0} Nat
                                      (Prod.{0, 0} Nat (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie h))))
                                  (@DecrAlmostLinearSSSP.Decremental.RadixQueue.pop h
                                    (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.abstract h tree))
                                  (@Option.some.{0}
                                    (Prod.{0, 0} Nat
                                      (Prod.{0, 0} Nat (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie h)))
                                    (@Prod.mk.{0, 0} Nat
                                      (Prod.{0, 0} Nat (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie h)) key
                                      (@Prod.mk.{0, 0} Nat (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie h)
                                        (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 262) (instOfNatNat (nat_lit 262))))
                                        (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.abstract h next)))))
                                (And
                                  (@Eq.{1} Nat
                                    (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260)))) key)
                                  (And (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image t h next)
                                    (And (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Separated h next)
                                      (And
                                        (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Bounded h next low
                                          (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))))
                                        (And
                                          (@Eq.{1} Nat (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root h next)
                                            (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root h tree))
                                          (And
                                            (@LE.le.{0} (Finset.{0} Nat)
                                              (@Preorder.toLE.{0} (Finset.{0} Nat)
                                                (@PartialOrder.toPreorder.{0} (Finset.{0} Nat)
                                                  (@Finset.instPartialOrder.{0} Nat)))
                                              (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint h next)
                                              (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint h tree))
                                            (And (@Eq.{1} (Nat → Real) t.realMem s.realMem)
                                              (∀
                                                a ∉
                                                  @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint h tree,
                                                @Eq.{1} Nat (t.natMem a) (s.natMem a))))))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.1.1.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.ShadowDataRep.effect : ∀ {B F : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine}
  (a : DecrAlmostLinearSSSP.Decremental.Structured.Atom),
  DecrAlmostLinearSSSP.Decremental.ShadowRep B F
      (DecrAlmostLinearSSSP.Decremental.instructionEffect a.instruction s.machine) g →
    DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F (a.effect s) g := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.1.1.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.Powers.nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 248) (instOfNatNat (nat_lit 248))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 250) (instOfNatNat (nat_lit 250))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 252) (instOfNatNat (nat_lit 252))) →
        DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.Powers.code k := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.2.1.1.1.1.1
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
theorem DecrAlmostLinearSSSP.Decremental.Exact.distance_edge_bound : ∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (active : Finset.{0} (Fin k)) (w : Fin k → Nat)
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
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d (w e))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_6.1.1.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.LabelInvariant.decrease : ∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {w : Fin k → Nat}
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
                (@Multiset.cons.{0} (Prod.{0, 0} Nat (Fin n)) (@Prod.mk.{0, 0} Nat (Fin n) candidate target) queue) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_6.1.2.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.LabelInvariant.settle : ∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {w : Fin k → Nat}
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
                remaining := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_6.1.2.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.adjacency_mem : ∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (t : Nat) (v : Fin n) (e : Fin k),
  Iff
    (@Membership.mem.{0, 0} (Fin k) (List.{0} (Fin k)) (@List.instMembership.{0} (Fin k))
      (@DecrAlmostLinearSSSP.Decremental.Exact.adjacency n k g t v) e)
    (And (@LT.lt.{0} Nat instLTNat (@Fin.val k e) t)
      (@Eq.{1} (Fin n) (@DecrAlmostLinearSSSP.Decremental.Digraph.tail n k g e) v)) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_6.1.2.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.code_real_frame : ∀ (j : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.code j := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_6.1.2.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.node_positive : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (e : Fin i.k),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
    (@DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.nodeAddress
      (DecrAlmostLinearSSSP.Decremental.Exact.Layout.addresses
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        i.n i.k)
      i.k e) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_6.2.1.1.1.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.StaticImage.chain : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {l : DecrAlmostLinearSSSP.Decremental.Exact.Layout.Addresses}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.StaticImage i l s →
    ∀ (v : Fin i.n),
      @DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.Chain i.k l s
        (@DecrAlmostLinearSSSP.Decremental.Exact.adjacency i.n i.k i.graph i.k v) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_6.2.2.1.2.1.1
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
theorem DecrAlmostLinearSSSP.Decremental.Exact.queueMap_count : ∀ {n h : Nat} (tree : DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie h) (q : Multiset.{0} (Prod.{0, 0} Nat (Fin n))),
  @Eq.{1} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (@DecrAlmostLinearSSSP.Decremental.Exact.queueMap n q)
      (@DecrAlmostLinearSSSP.Decremental.RadixQueue.entries h tree
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
    @Eq.{1} Nat (@DecrAlmostLinearSSSP.Decremental.RadixQueue.count h tree)
      (@Multiset.card.{0} (Prod.{0, 0} Nat (Fin n)) q) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_6.2.2.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.queueMap_pop : ∀ {n h : Nat} (tree next : DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie h)
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
                  @LE.le.{0} Nat instLENat key (@Prod.fst.{0, 0} Nat (Fin n) item)))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_6.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.queueMap_insert : ∀ {n h : Nat} (tree : DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie h) (q : Multiset.{0} (Prod.{0, 0} Nat (Fin n)))
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
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_6.2.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.Heap.Image.slot_not : ∀ {n h base slot : Nat} {tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin n))} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  @DecrAlmostLinearSSSP.Decremental.Exact.Heap.Image n h base slot tree queue s →
    slot ∉ @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint h tree := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_6.2.2.2.2.2.2.2
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
lemma Image.powers_not {n h : ℕ} {base slot : ℕ} {tree : LocatedTrie h} {queue : Multiset (ℕ × Fin n)} {s : Data}
    (hi : Image base slot tree queue s) (j : ℕ) (hj : j<h) : base+j ∉ tree.footprint := by
  intro hh
  have hh' := (hi.bounded (base+j) hh).1
  have hh'' := hi.powersHigh
  omega
lemma Image.count {n h : ℕ} {base slot : ℕ} {tree : LocatedTrie h} {queue : Multiset (ℕ × Fin n)} {s : Data}
    (hi : Image base slot tree queue s) : RadixQueue.count tree.abstract=queue.card := queueMap_count tree.abstract queue hi.entries
end DecrAlmostLinearSSSP.Decremental.Exact.Heap
end s109
section s110
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Heap
open Structured
lemma Image.push {n h : ℕ} {base slot : ℕ} {tree : LocatedTrie h} {queue : Multiset (ℕ × Fin n)} {s : Data}
    (hi : Image base slot tree queue s) (key : ℕ) (v : Fin n)
    (hkey : s.natReg 260 = key) (hvertex : s.natReg 262 = v.val) (hbound : key<2^h) :
    ∃ (cost : ℕ) (t : Data) (next : LocatedTrie h), Eval TriePush.code s cost t ∧ cost ≤ 43*(h+1) ∧
      Image base slot next ((key,v)::ₘqueue) t ∧ t.realMem=s.realMem ∧
      (∀ a, a<slot → t.natMem a=s.natMem a) := by
  have hroot : s.natMem (s.natReg 246)=tree.root := by rw [hi.slotReg];exact hi.root
  have hnot : s.natReg 246 ∉ tree.footprint := by rw [hi.slotReg];exact hi.slot_not
  obtain ⟨cost,t,next,he,hc,hslot,htImage,htSep,htBound,habstract,halloc,hfoot,hreal,hframe⟩ :=
    TriePush.code_result h tree slot base s hi.zero hi.unit hi.height hi.treeImage hi.separated
      (hi.bounded.mono (by omega) le_rfl) hroot (by rw [hi.slotReg]) (by rw [hi.slotReg];exact hi.allocator)
      hnot hi.powers hi.powersHigh hi.powerPtr
  have hn (k : ℕ) (hk : k ∉ TriePush.registers) := he.nat_frame (TriePush.code_nat_frame k hk)
  have hmeta (k : ℕ) (hk : k ∉ TriePush.registers) : t.natReg k=s.natReg k := hn k hk
  have htbound : next.Bounded (slot+1) (t.natReg 244) := by
    intro a ha
    rcases Finset.mem_union.mp (hfoot ha) with ho | hf
    · have hh := hi.bounded a ho
      exact ⟨hh.1,hh.2.trans_le halloc⟩
    · have hh := Finset.mem_Ico.mp hf
      exact ⟨by have := hi.allocator;omega,hh.2⟩
  have htBelow (a : ℕ) (ha : a<slot) : t.natMem a=s.natMem a := by
    apply hframe a
    · rw [hi.slotReg];omega
    · intro hh;have := (hi.bounded a hh).1;omega
    · exact Or.inl (ha.trans hi.allocator)
  refine ⟨cost,t,next,he,hc,?_,hreal,htBelow⟩
  refine ⟨(hmeta 56 (by norm_num [TriePush.registers])).trans hi.zero,
    (hmeta 26 (by norm_num [TriePush.registers])).trans hi.unit,
    (hmeta 236 (by norm_num [TriePush.registers])).trans hi.height,?_,
    (hmeta 246 (by norm_num [TriePush.registers])).trans hi.slotReg,
    hi.allocator.trans_le halloc,htImage,htSep,htbound,?_,?_,hi.powersHigh,?_⟩
  · intro hh;rw [hmeta 238 (by norm_num [TriePush.registers])];exact hi.powerPtr hh
  · rwa [hi.slotReg] at hslot
  · intro j hj
    rw [htBelow (base+j) (by have := hi.powersHigh;omega)]
    exact hi.powers j hj
  · rw [habstract,hkey,hvertex]
    exact queueMap_insert tree.abstract queue key v hi.entries hbound
end DecrAlmostLinearSSSP.Decremental.Exact.Heap
end s110
section s111
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Heap
open Structured
lemma Image.pop {n h : ℕ} {base slot : ℕ} {tree : LocatedTrie h} {queue : Multiset (ℕ × Fin n)} {s : Data}
    (hi : Image base slot tree queue s) (hpositive : 0<queue.card) :
    ∃ (cost : ℕ) (t : Data) (next : LocatedTrie h) (key : ℕ) (v : Fin n) (remaining : Multiset (ℕ × Fin n)),
      Eval TriePop.code s cost t ∧ cost ≤ 34*(h+1) ∧ Image base slot next remaining t ∧
      t.natReg 260=key ∧ t.natReg 262=v.val ∧ queue=(key,v)::ₘremaining ∧
      (∀ item∈queue, key ≤ item.1) ∧ t.realMem=s.realMem ∧
      (∀ a, a<slot → t.natMem a=s.natMem a) := by
  have hroot : s.natMem (s.natReg 246)=tree.root := by rw [hi.slotReg];exact hi.root
  obtain ⟨cost,t,next,key,he,hc,hpop,hkey,htImage,htSep,htBound,htRoot,htFoot,hreal,hframe⟩ :=
    TriePop.code_result h tree (slot+1) base s hi.zero hi.unit hi.height hi.treeImage hi.separated hi.bounded
      hroot (by rw [hi.count];exact hpositive) hi.powers (by have := hi.powersHigh;omega) hi.powerPtr
  obtain ⟨v,remaining,hv,hqueue,hentries,hmin⟩ := queueMap_pop tree.abstract next.abstract queue key (t.natReg 262) hi.entries hpop
  have hn (k : ℕ) (hk : k ∉ TriePop.registers) := he.nat_frame (TriePop.code_nat_frame k hk)
  have halloc : t.natReg 244=s.natReg 244 := hn 244 (by norm_num [TriePop.registers])
  have htBelow (a : ℕ) (ha : a<slot) : t.natMem a=s.natMem a := by
    apply hframe a
    intro hh;have := (hi.bounded a hh).1;omega
  refine ⟨cost,t,next,key,v,remaining,he,hc,?_,hkey,hv.symm,hqueue,hmin,hreal,htBelow⟩
  refine ⟨(hn 56 (by norm_num [TriePop.registers])).trans hi.zero,
    (hn 26 (by norm_num [TriePop.registers])).trans hi.unit,
    (hn 236 (by norm_num [TriePop.registers])).trans hi.height,?_,
    (hn 246 (by norm_num [TriePop.registers])).trans hi.slotReg,
    ?_,htImage,htSep,htBound,?_,?_,hi.powersHigh,hentries⟩
  · intro hh;rw [hn 238 (by norm_num [TriePop.registers])];exact hi.powerPtr hh
  · rw [halloc];exact hi.allocator
  · rw [hframe slot hi.slot_not,hi.root,htRoot]
  · intro j hj
    rw [hframe (base+j) (hi.powers_not j hj)]
    exact hi.powers j hj
end DecrAlmostLinearSSSP.Decremental.Exact.Heap
end s111
section s112
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
lemma public_below (i : Input) (v : Fin i.n) : v.val<heapSlot i := by
  have hv := v.isLt
  dsimp [heapSlot,heapBase,layout,Layout.addresses]
  omega
lemma settled_below (i : Input) (v : Fin i.n) : (layout i).settled+v.val<heapSlot i := by
  have hb := (Layout.vertex_bounds i v).2.2.1
  dsimp [heapSlot,heapBase,layout]
  exact hb.trans_le (Nat.le_add_right _ _)
lemma distance_below (i : Input) (v : Fin i.n) : (layout i).distances+v.val<heapSlot i := by
  have hb := (Layout.vertex_bounds i v).2.2.2
  dsimp [heapSlot,heapBase,layout]
  exact hb.trans_le (Nat.le_add_right _ _)
lemma active_below (i : Input) (e : Fin i.k) : (layout i).active+e.val<heapSlot i := by
  have hb := (Layout.edge_bounds i e 0 (by omega)).1
  dsimp [heapSlot,heapBase,layout]
  exact hb.trans_le (Nat.le_add_right _ _)
lemma graph_below (i : Input) (a : ℕ) (ha : a∈Adjacency.staticFootprint i (layout i)) : a<heapSlot i := by
  have hb := Layout.static_bounds i a ha
  dsimp [heapSlot,heapBase,layout]
  exact hb.trans_le (Nat.le_add_right _ _)
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s112
section s113
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
lemma Memory.heap_replace {i : Input} {deleted : List (Fin i.k)} {tentative : Fin i.n → Option ℕ}
    {settled : Finset (Fin i.n)} {tree next : LocatedTrie (heapHeight i)}
    {queue remaining : Multiset (ℕ × Fin i.n)} {s t : Data}
    (h : Memory i deleted tentative settled tree queue s)
    (hheap : Heap.Image (heapBase i) (heapSlot i) next remaining t)
    (hn : ∀ j, j<244 → t.natReg j=s.natReg j) (hr56 : t.realReg 56=s.realReg 56)
    (hr : t.realMem=s.realMem) (hm : ∀ a, a<heapSlot i → t.natMem a=s.natMem a) :
    Memory i deleted tentative settled next remaining t := by
  refine ⟨(hn 66 (by omega)).trans h.vertices,(hn 68 (by omega)).trans h.edges,
    (hn 72 (by omega)).trans h.source,hr56.trans h.zeroR,?_,?_,?_,?_,?_,hheap⟩
  · constructor
    · exact (hn 224 (by omega)).trans h.layoutRegs.heads
    · exact (hn 226 (by omega)).trans h.layoutRegs.settled
    · exact (hn 228 (by omega)).trans h.layoutRegs.active
    · exact (hn 230 (by omega)).trans h.layoutRegs.distances
    · exact (hn 232 (by omega)).trans h.layoutRegs.nodes
    · exact (hn 234 (by omega)).trans h.layoutRegs.powers
  · exact h.graph.frame (fun a ha => hm a (graph_below i a ha))
  · intro e
    rw [hm _ (active_below i e)]
    exact h.active e
  · exact h.tentative.frame (fun v => hm _ (public_below i v))
      (fun v => hm _ (distance_below i v)) (fun v => congrFun hr v.val)
  · intro v
    rw [hm _ (settled_below i v)]
    exact h.settled v
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s113
section s114
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Heap
open Structured
lemma Image.frame {n h : ℕ} {base slot : ℕ} {tree : LocatedTrie h} {queue : Multiset (ℕ × Fin n)} {s t : Data}
    (hi : Image base slot tree queue s)
    (hn : ∀ j∈({56,26,236,238,244,246} : Finset ℕ), t.natReg j=s.natReg j)
    (hm : t.natMem=s.natMem) : Image base slot tree queue t := by
  refine ⟨(hn 56 (by norm_num)).trans hi.zero,(hn 26 (by norm_num)).trans hi.unit,
    (hn 236 (by norm_num)).trans hi.height,?_,(hn 246 (by norm_num)).trans hi.slotReg,?_,
    hi.treeImage.frame (fun a _ => congrFun hm a),hi.separated,?_,?_,?_,hi.powersHigh,hi.entries⟩
  · intro hh;rw [hn 238 (by norm_num)];exact hi.powerPtr hh
  · rw [hn 244 (by norm_num)];exact hi.allocator
  · rw [hn 244 (by norm_num)];exact hi.bounded
  · rw [hm];exact hi.root
  · intro j hj;rw [hm];exact hi.powers j hj
end DecrAlmostLinearSSSP.Decremental.Exact.Heap
end s114
section s115
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
lemma Memory.register_frame {i : Input} {deleted : List (Fin i.k)} {tentative : Fin i.n → Option ℕ}
    {settled : Finset (Fin i.n)} {tree : LocatedTrie (heapHeight i)} {queue : Multiset (ℕ × Fin i.n)} {s t : Data}
    (h : Memory i deleted tentative settled tree queue s)
    (hn : ∀ j, j≤246 → t.natReg j=s.natReg j) (hr56 : t.realReg 56=s.realReg 56)
    (hm : t.natMem=s.natMem) (hr : t.realMem=s.realMem) :
    Memory i deleted tentative settled tree queue t := by
  apply h.heap_replace (h.heap.frame (fun j hj => hn j (by simp only [Finset.mem_insert,Finset.mem_singleton] at hj;omega)) hm)
  · intro j hj;exact hn j (by omega)
  · exact hr56
  · exact hr
  · intro a _;exact congrFun hm a
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s115
section s116
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
lemma queueCount_eval (s : Data) (hz : s.natReg 56=0) :
    ∃ c, Eval queueCount s c (counted s) ∧ c≤4 := by
  let u : Data := {s with natReg := Function.update s.natReg 346 (s.natMem (s.natReg 246))}
  have hu : Eval (loadN 346 246) s 1 u := eval_loadN s 346 246
  by_cases hp : 0<s.natMem (s.natReg 246)
  · have ht : (Test.natLess 56 346).holds u := by simpa [Test.holds,u,hz] using hp
    refine ⟨3,?_,by omega⟩
    have he := Eval.seq hu (Eval.branchYes (no := natural 348 0) ht (eval_loadN u 348 346))
    simpa only [queueCount,counted,if_pos hp,u,Function.update_self] using he
  · have ht : ¬(Test.natLess 56 346).holds u := by simpa [Test.holds,u,hz] using hp
    refine ⟨4,?_,by omega⟩
    have he := Eval.seq hu (Eval.branchNo (yes := loadN 348 346) ht (eval_natural u 348 0))
    simpa only [queueCount,counted,if_neg hp,u] using he
lemma queueCount_nat_frame (j : ℕ) (h346 : j≠346) (h348 : j≠348) : NatFrame queueCount j := by
  simp [queueCount,NatFrame,writesNat,loadN,natural,Ne.symm h346,Ne.symm h348]
lemma queueCount_real_frame (j : ℕ) : RealFrame queueCount j := by simp [queueCount,RealFrame,writesReal,loadN,natural]
lemma Memory.queueCount {i : Input} {deleted : List (Fin i.k)} {tentative : Fin i.n → Option ℕ}
    {settled : Finset (Fin i.n)} {tree : LocatedTrie (heapHeight i)} {queue : Multiset (ℕ × Fin i.n)} {s : Data}
    (h : Memory i deleted tentative settled tree queue s) :
    ∃ c, Eval queueCount s c (counted s) ∧ c≤4 ∧
      Memory i deleted tentative settled tree queue (counted s) ∧ (counted s).natReg 348=queue.card := by
  obtain ⟨c,he,hc⟩ := queueCount_eval s h.heap.zero
  refine ⟨c,he,hc,?_,?_⟩
  · exact h.register_frame (fun j hj => he.nat_frame (queueCount_nat_frame j (by omega) (by omega)))
      (he.real_frame (queueCount_real_frame 56)) rfl rfl
  · have hroot : s.natMem (s.natReg 246)=tree.root := by rw [h.heap.slotReg];exact h.heap.root
    have hcount := LocatedTrie.Image.read_count tree s h.heap.treeImage h.heap.separated
    simpa only [counted,Function.update_self,hroot,h.heap.count] using hcount
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s116
section s117
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
lemma candidatePrefix_eval (s : Data) : Eval (Structured.sequence (candidateAtoms.map Cmd.atom)) s 7 (candidateData s) :=
  eval_sequence_atoms candidateAtoms s
lemma candidatePrefix_nat_frame (j : ℕ) (hj : j ∉ ({312,316,322,324,326,336} : Finset ℕ)) : NatFrame (Structured.sequence (candidateAtoms.map Cmd.atom)) j := by
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hj
  simp [candidateAtoms,Structured.sequence,NatFrame,writesNat] <;> tauto
lemma candidatePrefix_real_frame (j : ℕ) : RealFrame (Structured.sequence (candidateAtoms.map Cmd.atom)) j := by
  simp [candidateAtoms,Structured.sequence,RealFrame,writesReal]
lemma Memory.candidatePrefix {i : Input} {deleted : List (Fin i.k)} {tentative : Fin i.n → Option ℕ}
    {settled : Finset (Fin i.n)} {tree : LocatedTrie (heapHeight i)} {queue : Multiset (ℕ × Fin i.n)} {s : Data}
    (h : Memory i deleted tentative settled tree queue s) (e : Fin i.k) (key : ℕ)
    (h308 : s.natReg 308=Adjacency.nodeAddress (layout i) e) (h310 : s.natReg 310=(i.graph.head e).val)
    (h304 : s.natReg 304=key) :
    Memory i deleted tentative settled tree queue (candidateData s) ∧
      (candidateData s).natReg 310=(i.graph.head e).val ∧
      (candidateData s).natReg 326=key+i.weight e ∧
      (candidateData s).natReg 316=s.natMem (i.graph.head e).val ∧
      (candidateData s).natReg 322=(layout i).distances+(i.graph.head e).val ∧
      (candidateData s).natReg 324=s.natMem ((layout i).distances+(i.graph.head e).val) := by
  have he := candidatePrefix_eval s
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · exact h.register_frame (fun j hj => he.nat_frame (candidatePrefix_nat_frame j (by
      simp only [Finset.mem_insert,Finset.mem_singleton,not_or];omega)))
      (he.real_frame (candidatePrefix_real_frame 56)) rfl rfl
  · exact (he.nat_frame (candidatePrefix_nat_frame 310 (by norm_num))).trans h310
  all_goals simp [candidateData,candidateAtoms,Atom.effect,instructionEffect,data,Data.machine,
    h308,h310,h304,h.graph.weight e,h.layoutRegs.distances]
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s117
section s118
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Heap
open Structured
lemma Image.below_frame {n h : ℕ} {base slot : ℕ} {tree : LocatedTrie h} {queue : Multiset (ℕ × Fin n)} {s t : Data}
    (hi : Image base slot tree queue s)
    (hn : ∀ j∈({56,26,236,238,244,246} : Finset ℕ), t.natReg j=s.natReg j)
    (hm : ∀ a, base≤a → t.natMem a=s.natMem a) : Image base slot tree queue t := by
  have hbs : base ≤ slot := by have := hi.powersHigh;omega
  refine ⟨(hn 56 (by norm_num)).trans hi.zero,(hn 26 (by norm_num)).trans hi.unit,
    (hn 236 (by norm_num)).trans hi.height,?_,(hn 246 (by norm_num)).trans hi.slotReg,?_,
    hi.treeImage.frame (fun a ha => hm a (hbs.trans (by have := (hi.bounded a ha).1;omega))),hi.separated,?_,?_,?_,hi.powersHigh,hi.entries⟩
  · intro hh;rw [hn 238 (by norm_num)];exact hi.powerPtr hh
  · rw [hn 244 (by norm_num)];exact hi.allocator
  · rw [hn 244 (by norm_num)];exact hi.bounded
  · rw [hm slot hbs];exact hi.root
  · intro j hj;rw [hm (base+j) (Nat.le_add_right _ _)];exact hi.powers j hj
end DecrAlmostLinearSSSP.Decremental.Exact.Heap
end s118
section s119
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
lemma improvePrefix_eval (s : Data) : Eval (Structured.sequence (improveAtoms.map Cmd.atom)) s 6 (improved s) :=
  eval_sequence_atoms improveAtoms s
lemma improvePrefix_fields (s : Data) (hz : s.natReg 56=0) :
    (improved s).natMem = Function.update (Function.update s.natMem (s.natReg 310) 0) (s.natReg 322) (s.natReg 326) ∧
      (improved s).realMem = Function.update s.realMem (s.natReg 310) (s.natReg 326 : ℝ) ∧
      (improved s).natReg 260 = s.natReg 326 ∧ (improved s).natReg 262 = s.natReg 310 := by
  simp [improved,improveAtoms,Atom.effect,instructionEffect,data,Data.machine,hz]
lemma improvePrefix_nat_frame (j : ℕ) (h260 : j≠260) (h262 : j≠262) : NatFrame (Structured.sequence (improveAtoms.map Cmd.atom)) j := by
  simp [improveAtoms,Structured.sequence,NatFrame,writesNat,Ne.symm h260,Ne.symm h262]
lemma improvePrefix_real_frame (j : ℕ) (h332 : j≠332) : RealFrame (Structured.sequence (improveAtoms.map Cmd.atom)) j := by
  simp [improveAtoms,Structured.sequence,RealFrame,writesReal,Ne.symm h332]
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s119
section s120
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact
open Structured
lemma TentativeImage.update {i : Input} {l : Layout.Addresses} {tentative : Fin i.n → Option ℕ} {s t : Data}
    (hi : TentativeImage i l tentative s) (target : Fin i.n) (candidate : ℕ)
    (hsep : ∀ v u : Fin i.n, v.val≠l.distances+u.val)
    (hm : t.natMem=Function.update (Function.update s.natMem target.val 0) (l.distances+target.val) candidate)
    (hr : t.realMem=Function.update s.realMem target.val (candidate : ℝ)) :
    TentativeImage i l (Function.update tentative target (some candidate)) t := by
  intro v
  by_cases hv : v=target
  · subst v
    simp only [Function.update_self]
    refine ⟨?_,?_,?_⟩
    · rw [hm,Function.update_of_ne (hsep target target),Function.update_self]
    · rw [hm,Function.update_self]
    · rw [hr,Function.update_self]
  · have hvval : v.val≠target.val := fun hh => hv (Fin.ext hh)
    have hf : t.natMem v.val=s.natMem v.val := by
      rw [hm,Function.update_of_ne (hsep v target),Function.update_of_ne hvval]
    have hd : t.natMem (l.distances+v.val)=s.natMem (l.distances+v.val) := by
      rw [hm,Function.update_of_ne (by omega),Function.update_of_ne (Ne.symm (hsep target v))]
    have hreal : t.realMem v.val=s.realMem v.val := by rw [hr,Function.update_of_ne hvval]
    simp only [Function.update_of_ne hv]
    cases ht : tentative v with
    | none => exact hf.trans (hi.infinite v ht)
    | some d => exact ⟨hf.trans (hi.finite v d ht).1,hd.trans (hi.finite v d ht).2.1,hreal.trans (hi.finite v d ht).2.2⟩
end DecrAlmostLinearSSSP.Decremental.Exact
end s120
section s121
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
lemma Memory.improvePrefix {i : Input} {deleted : List (Fin i.k)} {tentative : Fin i.n → Option ℕ}
    {settled : Finset (Fin i.n)} {tree : LocatedTrie (heapHeight i)} {queue : Multiset (ℕ × Fin i.n)} {s : Data}
    (h : Memory i deleted tentative settled tree queue s) (target : Fin i.n) (candidate : ℕ)
    (h310 : s.natReg 310=target.val) (h322 : s.natReg 322=(layout i).distances+target.val)
    (h326 : s.natReg 326=candidate) :
    Memory i deleted (Function.update tentative target (some candidate)) settled tree queue (improved s) ∧
      (improved s).natReg 260=candidate ∧ (improved s).natReg 262=target.val := by
  let t := improved s
  have he := improvePrefix_eval s
  have hv := improvePrefix_fields s h.heap.zero
  have hm : t.natMem=Function.update (Function.update s.natMem target.val 0) ((layout i).distances+target.val) candidate := by
    simpa only [h310,h322,h326] using hv.1
  have hr : t.realMem=Function.update s.realMem target.val (candidate : ℝ) := by simpa only [h310,h326] using hv.2.1
  have hn (j : ℕ) (hj : j ≤ 246) : t.natReg j=s.natReg j := he.nat_frame (improvePrefix_nat_frame j (by omega) (by omega))
  have hframe (a : ℕ) (hp : a≠target.val) (hd : a≠(layout i).distances+target.val) : t.natMem a=s.natMem a := by
    rw [hm,Function.update_of_ne hd,Function.update_of_ne hp]
  have htarget := target.isLt
  have hsep (v u : Fin i.n) : v.val≠(layout i).distances+u.val := by
    have hv := v.isLt
    dsimp [layout,Layout.addresses]
    omega
  have hheap := h.heap.below_frame (fun j hj => hn j (by simp only [Finset.mem_insert,Finset.mem_singleton] at hj;omega)) (by
    intro a ha
    apply hframe a
    · have hb := (Layout.vertex_bounds i target).1
      dsimp [heapBase,layout,Layout.addresses] at ha ⊢;omega
    · have hb := (Layout.vertex_bounds i target).2.2.2
      change (layout i).distances+target.val < heapBase i at hb
      omega)
  refine ⟨?_,by simpa only [h326] using hv.2.2.1,by simpa only [h310] using hv.2.2.2⟩
  refine ⟨(hn 66 (by omega)).trans h.vertices,(hn 68 (by omega)).trans h.edges,
    (hn 72 (by omega)).trans h.source,(he.real_frame (improvePrefix_real_frame 56 (by omega))).trans h.zeroR,
    ?_,?_,?_,h.tentative.update target candidate hsep hm hr,?_,hheap⟩
  · constructor
    · exact (hn 224 (by omega)).trans h.layoutRegs.heads
    · exact (hn 226 (by omega)).trans h.layoutRegs.settled
    · exact (hn 228 (by omega)).trans h.layoutRegs.active
    · exact (hn 230 (by omega)).trans h.layoutRegs.distances
    · exact (hn 232 (by omega)).trans h.layoutRegs.nodes
    · exact (hn 234 (by omega)).trans h.layoutRegs.powers
  · apply h.graph.frame
    intro a ha
    apply hframe a
    · simp only [Adjacency.staticFootprint,Finset.mem_union,Finset.mem_Ico] at ha
      dsimp [layout,Layout.addresses] at ha
      rcases ha with ha | ha <;> omega
    · simp only [Adjacency.staticFootprint,Finset.mem_union,Finset.mem_Ico] at ha
      dsimp [layout,Layout.addresses] at ha ⊢
      rcases ha with ha | ha <;> omega
  · intro e
    rw [hframe _ (by have he := e.isLt;dsimp [layout,Layout.addresses];omega)
      (by have he := e.isLt;dsimp [layout,Layout.addresses];omega)]
    exact h.active e
  · intro v
    rw [hframe _ (by have hv := v.isLt;dsimp [layout,Layout.addresses];omega)
      (by have hv := v.isLt;dsimp [layout,Layout.addresses];omega)]
    exact h.settled v
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s121
section s122
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
lemma Memory.push {i : Input} {deleted : List (Fin i.k)} {tentative : Fin i.n → Option ℕ}
    {settled : Finset (Fin i.n)} {tree : LocatedTrie (heapHeight i)} {queue : Multiset (ℕ × Fin i.n)} {s : Data}
    (h : Memory i deleted tentative settled tree queue s) (key : ℕ) (v : Fin i.n)
    (hkey : s.natReg 260=key) (hvertex : s.natReg 262=v.val) (hbound : key<2^(heapHeight i)) :
    ∃ cost t next, Eval TriePush.code s cost t ∧ cost≤43*(heapHeight i+1) ∧
      Memory i deleted tentative settled next ((key,v)::ₘqueue) t := by
  obtain ⟨cost,t,next,he,hc,hh,hr,hm⟩ := h.heap.push key v hkey hvertex hbound
  refine ⟨cost,t,next,he,hc,h.heap_replace hh ?_ (he.real_frame (TriePush.code_real_frame 56)) hr hm⟩
  intro j hj
  apply he.nat_frame
  apply TriePush.code_nat_frame
  simp only [TriePush.registers,Finset.mem_insert,Finset.mem_singleton,not_or]
  omega
lemma Memory.pop {i : Input} {deleted : List (Fin i.k)} {tentative : Fin i.n → Option ℕ}
    {settled : Finset (Fin i.n)} {tree : LocatedTrie (heapHeight i)} {queue : Multiset (ℕ × Fin i.n)} {s : Data}
    (h : Memory i deleted tentative settled tree queue s) (hpositive : 0<queue.card) :
    ∃ (cost : ℕ) (t : Data) (next : LocatedTrie (heapHeight i)) (key : ℕ) (v : Fin i.n) (remaining : Multiset (ℕ × Fin i.n)),
      Eval TriePop.code s cost t ∧ cost≤34*(heapHeight i+1) ∧
      Memory i deleted tentative settled next remaining t ∧ t.natReg 260=key ∧ t.natReg 262=v.val ∧
      queue=(key,v)::ₘremaining ∧ (∀ item∈queue, key ≤ item.1) := by
  obtain ⟨cost,t,next,key,v,remaining,he,hc,hh,hkey,hvertex,hqueue,hmin,hr,hm⟩ := h.heap.pop hpositive
  refine ⟨cost,t,next,key,v,remaining,he,hc,h.heap_replace hh ?_ (he.real_frame (TriePop.code_real_frame 56)) hr hm,
    hkey,hvertex,hqueue,hmin⟩
  intro j hj
  apply he.nat_frame
  apply TriePop.code_nat_frame
  simp only [TriePop.registers,Finset.mem_insert,Finset.mem_singleton,not_or]
  omega
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s122
section s123
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
lemma improve_nat_frame (j : ℕ) (hj : 300 ≤ j) : NatFrame improve j := by
  refine ⟨improvePrefix_nat_frame j (by omega) (by omega),TriePush.code_nat_frame j ?_⟩
  simp only [TriePush.registers,Finset.mem_insert,Finset.mem_singleton,not_or]
  omega
lemma improve_real_frame (j : ℕ) (hj : j≠332) : RealFrame improve j :=
  ⟨improvePrefix_real_frame j hj,TriePush.code_real_frame j⟩
lemma Memory.improve {i : Input} {deleted : List (Fin i.k)} {tentative : Fin i.n → Option ℕ}
    {settled : Finset (Fin i.n)} {tree : LocatedTrie (heapHeight i)} {queue : Multiset (ℕ × Fin i.n)} {s : Data}
    (h : Memory i deleted tentative settled tree queue s) (target : Fin i.n) (candidate : ℕ)
    (h310 : s.natReg 310=target.val) (h322 : s.natReg 322=(layout i).distances+target.val)
    (h326 : s.natReg 326=candidate) (hbound : candidate < 2^(heapHeight i)) :
    ∃ cost t next, Eval improve s cost t ∧ cost ≤ 49*(heapHeight i+1) ∧
      Memory i deleted (Function.update tentative target (some candidate)) settled next ((candidate,target)::ₘqueue) t := by
  obtain ⟨hm,hkey,hvertex⟩ := h.improvePrefix target candidate h310 h322 h326
  obtain ⟨c,t,next,he,hc,ht⟩ := hm.push candidate target hkey hvertex hbound
  exact ⟨6+c,t,next,Eval.seq (improvePrefix_eval s) he,by omega,ht⟩
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s123
section s124
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact
lemma LabelInvariant.relax_edge {n k : ℕ} {g : Digraph n k} {active : Finset (Fin k)} {w : Fin k → ℕ}
    {source : Fin n} {tentative : Fin n → Option ℕ} {settled : Finset (Fin n)} {remaining : Multiset (ℕ × Fin n)}
    (key : ℕ) (v : Fin n)
    (h : LabelInvariant g active w source tentative settled ((key,v)::ₘremaining))
    (ht : tentative v = some key)
    (e : Fin k) (he : e ∈ active) (htail : g.tail e = v) (hn : g.head e ∉ settled)
    (hsmaller : ∀ d, tentative (g.head e) = some d → key+w e < d) :
    LabelInvariant g active w source (Function.update tentative (g.head e) (some (key+w e))) settled
      ((key,v)::ₘ((key+w e,g.head e)::ₘremaining)) := by
  have hpath := distance_edge_bound g active w source e he key (by rw [htail];exact h.pathBound v key ht)
  have hnew := h.decrease (g.head e) (key+w e) hn hsmaller hpath (by
    intro u hu d hd
    have hh := h.belowQueue u hu d hd (key,v) (Multiset.mem_cons_self _ _)
    omega)
  rw [Multiset.cons_swap] at hnew
  exact hnew
end DecrAlmostLinearSSSP.Decremental.Exact
end s124
section s125
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact
lemma LabelInvariant.settled_edge_bound {n k : ℕ} {g : Digraph n k} {active : Finset (Fin k)} {w : Fin k → ℕ}
    {source : Fin n} {tentative : Fin n → Option ℕ} {settled : Finset (Fin n)} {queue : Multiset (ℕ × Fin n)}
    (h : LabelInvariant g active w source tentative settled queue) (v : Fin n) (key : ℕ)
    (ht : tentative v = some key) (e : Fin k) (he : e ∈ active) (htail : g.tail e = v)
    (hh : g.head e ∈ settled) :
    ∃ d, tentative (g.head e) = some d ∧ d ≤ key+w e := by
  obtain ⟨d,hd,heq⟩ := h.exactSettled (g.head e) hh
  have hbound := distance_edge_bound g active w source e he key (by rw [htail];exact h.pathBound v key ht)
  rw [heq] at hbound
  exact ⟨d,hd,by exact_mod_cast hbound⟩
lemma improves_iff (old : Option ℕ) (candidate : ℕ) : Improves old candidate ↔ ∀ d, old=some d → candidate<d := by
  cases old <;> simp [Improves]
lemma not_improves (old : Option ℕ) (candidate : ℕ) (h : ¬Improves old candidate) :
    ∃ d, old=some d ∧ d≤candidate := by
  cases old with
  | none => simp [Improves] at h
  | some d => exact ⟨d,rfl,by simpa [Improves] using h⟩
end DecrAlmostLinearSSSP.Decremental.Exact
end s125
section s126
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact
lemma LabelInvariant.skip_settled {n k : ℕ} {g : Digraph n k} {active : Finset (Fin k)} {w : Fin k → ℕ}
    {source : Fin n} {tentative : Fin n → Option ℕ} {settled : Finset (Fin n)} {remaining : Multiset (ℕ × Fin n)}
    (key : ℕ) (v : Fin n)
    (h : LabelInvariant g active w source tentative settled ((key,v)::ₘremaining)) (hv : v ∈ settled) :
    LabelInvariant g active w source tentative settled remaining := by
  constructor
  · exact h.sourceZero
  · exact h.pathBound
  · exact h.exactSettled
  · intro u hu d hud item hitem
    exact h.belowQueue u hu d hud item (Multiset.mem_cons_of_mem hitem)
  · exact h.frontier
  · intro u hu d hud
    rcases Multiset.mem_cons.mp (h.covered u hu d hud) with hh | hh
    · have heq : u=v := congrArg Prod.snd hh
      exact False.elim (hu (heq ▸ hv))
    · exact hh
  · intro item hitem
    exact h.queueValid item (Multiset.mem_cons_of_mem hitem)
end DecrAlmostLinearSSSP.Decremental.Exact
end s126
section s127
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact
attribute [local instance] Classical.propDecidable
lemma scan_initial {n k : ℕ} {g : Digraph n k} {active : Finset (Fin k)} {w : Fin k → ℕ}
    {source v : Fin n} {key : ℕ} {settled : Finset (Fin n)}
    {tentative : Fin n → Option ℕ} {queue : Multiset (ℕ × Fin n)}
    (h : LabelInvariant g active w source tentative settled ((key,v)::ₘqueue)) (hv : v∉settled)
    (hmin : ∀ item ∈ queue, key ≤ item.1) :
    ScanState g active w source v key settled [] tentative queue := by
  have ht := (h.pop_exact key v (Multiset.mem_cons_self _ _) (by
    intro item hi
    rcases Multiset.mem_cons.mp hi with hh | hh
    · subst item;exact le_rfl
    · exact hmin item hh) hv).1
  exact ⟨h,ht,hmin,by simp⟩
lemma scan_finished {n k : ℕ} {g : Digraph n k} {active : Finset (Fin k)} {w : Fin k → ℕ}
    {source v : Fin n} {key : ℕ} {settled : Finset (Fin n)} {scanned : List (Fin k)}
    {tentative : Fin n → Option ℕ} {queue : Multiset (ℕ × Fin n)}
    (h : ScanState g active w source v key settled scanned tentative queue) (hv : v∉settled)
    (hcomplete : ∀ e ∈ active, g.tail e=v → e∈scanned) :
    LabelInvariant g active w source tentative (insert v settled) queue := by
  have hexact := (h.labels.pop_exact key v (Multiset.mem_cons_self _ _) (by
    intro item hi
    rcases Multiset.mem_cons.mp hi with hh | hh
    · subst item;exact le_rfl
    · exact h.minimum item hh) hv).2
  exact h.labels.settle key v hv h.current hexact h.minimum
    (fun e he ht => h.relaxed e (hcomplete e he ht) he ht)
end DecrAlmostLinearSSSP.Decremental.Exact
end s127
section s128
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
lemma Memory.candidate {i : Input} {deleted : List (Fin i.k)} {tentative : Fin i.n → Option ℕ}
    {settled : Finset (Fin i.n)} {tree : LocatedTrie (heapHeight i)} {queue : Multiset (ℕ × Fin i.n)} {s : Data}
    (h : Memory i deleted tentative settled tree queue s) (e : Fin i.k) (key : ℕ)
    (h308 : s.natReg 308=Adjacency.nodeAddress (layout i) e) (h310 : s.natReg 310=(i.graph.head e).val)
    (h304 : s.natReg 304=key) (hactive : e∈live deleted) (hunsettled : i.graph.head e∉settled)
    (hbound : key+i.weight e < 2^(heapHeight i)) :
    let result := Exact.relax i.graph (live deleted) i.weight settled key e tentative queue
    ∃ cost t next, Eval Dijkstra.candidate s cost t ∧ cost ≤ 60*(heapHeight i+1) ∧
      Memory i deleted result.1 settled next result.2 t := by
  let u := candidateData s
  obtain ⟨hm,hu310,hu326,hu316,hu322,hu324⟩ := h.candidatePrefix e key h308 h310 h304
  have huz : u.natReg 56=0 := hm.heap.zero
  change u.natReg 326=key+i.weight e at hu326
  have hePrefix := candidatePrefix_eval s
  cases hold : tentative (i.graph.head e) with
  | none =>
    have hyes : e∈live deleted ∧ i.graph.head e∉settled ∧ Improves (tentative (i.graph.head e)) (key+i.weight e) :=
      ⟨hactive,hunsettled,by simp [hold,Improves]⟩
    simp only [Exact.relax,if_pos hyes]
    have hflag : u.natReg 316=1 := hu316.trans (h.tentative.infinite _ hold)
    have htest : (Test.natLess 56 316).holds u := by simp [Test.holds,huz,hflag]
    obtain ⟨c,t,next,he,hc,ht⟩ := hm.improve (i.graph.head e) (key+i.weight e) hu310 hu322 hu326 hbound
    refine ⟨7+(c+1),t,next,Eval.seq hePrefix (Eval.branchYes htest he),by omega,ht⟩
  | some old =>
    have hflag : u.natReg 316=0 := hu316.trans (h.tentative.finite _ old hold).1
    have hvalue : u.natReg 324=old := hu324.trans (h.tentative.finite _ old hold).2.1
    have htest : ¬(Test.natLess 56 316).holds u := by simp [Test.holds,huz,hflag]
    by_cases himprove : key+i.weight e < old
    · have hyes : e∈live deleted ∧ i.graph.head e∉settled ∧ Improves (tentative (i.graph.head e)) (key+i.weight e) :=
        ⟨hactive,hunsettled,by simpa only [hold,Improves] using himprove⟩
      simp only [Exact.relax,if_pos hyes]
      have htcompare : (Test.natLess 326 324).holds u := by simpa [Test.holds,hu326,hvalue] using himprove
      obtain ⟨c,t,next,he,hc,ht⟩ := hm.improve (i.graph.head e) (key+i.weight e) hu310 hu322 hu326 hbound
      refine ⟨7+((c+1)+2),t,next,Eval.seq hePrefix (Eval.branchNo htest (Eval.branchYes htcompare he)),by omega,ht⟩
    · have hno : ¬(e∈live deleted ∧ i.graph.head e∉settled ∧ Improves (tentative (i.graph.head e)) (key+i.weight e)) := by
        intro hh;exact himprove (by simpa only [hold,Improves] using hh.2.2)
      simp only [Exact.relax,if_neg hno]
      have htcompare : ¬(Test.natLess 326 324).holds u := by simpa [Test.holds,hu326,hvalue] using himprove
      refine ⟨11,u,tree,?_,by omega,hm⟩
      exact Eval.seq hePrefix (Eval.branchNo htest (Eval.branchNo htcompare (Eval.skip u)))
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s128
section s129
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
lemma candidate_nat_frame (j : ℕ) (hj : 300 ≤ j)
    (hk : j ∉ ({312,316,322,324,326,336} : Finset ℕ)) : NatFrame Dijkstra.candidate j :=
  ⟨candidatePrefix_nat_frame j hk,improve_nat_frame j hj,improve_nat_frame j hj,trivial⟩
lemma candidate_real_frame (j : ℕ) (hj : j≠332) : RealFrame Dijkstra.candidate j :=
  ⟨candidatePrefix_real_frame j,improve_real_frame j hj,improve_real_frame j hj,trivial⟩
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s129
section s130
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
lemma edgeHeader_eval (s : Data) : Eval edgeHeader s 5 (edgeHeaderData s) := by
  exact Eval.seq (eval_loadN s 310 308) (eval_sequence_atoms activeAtoms _)
lemma edgeHeader_nat_frame (j : ℕ) (hk : j ∉ ({310,314,316,336} : Finset ℕ)) : NatFrame edgeHeader j := by
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hk
  simp [edgeHeader,activeAtoms,Structured.sequence,NatFrame,writesNat,loadN] <;> tauto
lemma edgeHeader_real_frame (j : ℕ) : RealFrame edgeHeader j := by
  simp [edgeHeader,activeAtoms,Structured.sequence,RealFrame,writesReal,loadN]
lemma Memory.edgeHeader {i : Input} {deleted : List (Fin i.k)} {tentative : Fin i.n → Option ℕ}
    {settled : Finset (Fin i.n)} {tree : LocatedTrie (heapHeight i)} {queue : Multiset (ℕ × Fin i.n)} {s : Data}
    (h : Memory i deleted tentative settled tree queue s) (e : Fin i.k)
    (h308 : s.natReg 308=Adjacency.nodeAddress (layout i) e) :
    Memory i deleted tentative settled tree queue (edgeHeaderData s) ∧
      (edgeHeaderData s).natReg 310=(i.graph.head e).val ∧
      (edgeHeaderData s).natReg 316=(if e∈live deleted then 1 else 0) := by
  have he := edgeHeader_eval s
  refine ⟨?_,?_,?_⟩
  · exact h.register_frame (fun j hj => he.nat_frame (edgeHeader_nat_frame j (by
      simp only [Finset.mem_insert,Finset.mem_singleton,not_or];omega)))
      (he.real_frame (edgeHeader_real_frame 56)) rfl rfl
  all_goals simp [edgeHeaderData,edgeHeaderAtoms,activeAtoms,Atom.effect,instructionEffect,data,Data.machine,
    h308,h.graph.head e,h.graph.flagAddress e,h.active e]
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s130
section s131
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
lemma target_eval (s : Data) : Eval (Structured.sequence (targetSettledAtoms.map Cmd.atom)) s 2 (targetData s) := eval_sequence_atoms targetSettledAtoms s
lemma next_eval (s : Data) : Eval (Structured.sequence (nextAtoms.map Cmd.atom)) s 3 (nextData s) := eval_sequence_atoms nextAtoms s
lemma target_nat_frame (j : ℕ) (h318 : j≠318) (h320 : j≠320) : NatFrame (Structured.sequence (targetSettledAtoms.map Cmd.atom)) j := by
  simp [targetSettledAtoms,Structured.sequence,NatFrame,writesNat,Ne.symm h318,Ne.symm h320]
lemma next_nat_frame (j : ℕ) (h308 : j≠308) (h336 : j≠336) : NatFrame (Structured.sequence (nextAtoms.map Cmd.atom)) j := by
  simp [nextAtoms,Structured.sequence,NatFrame,writesNat,Ne.symm h308,Ne.symm h336]
lemma target_real_frame (j : ℕ) : RealFrame (Structured.sequence (targetSettledAtoms.map Cmd.atom)) j := by
  simp [targetSettledAtoms,Structured.sequence,RealFrame,writesReal]
lemma next_real_frame (j : ℕ) : RealFrame (Structured.sequence (nextAtoms.map Cmd.atom)) j := by
  simp [nextAtoms,Structured.sequence,RealFrame,writesReal]
lemma Memory.target {i : Input} {deleted : List (Fin i.k)} {tentative : Fin i.n → Option ℕ}
    {settled : Finset (Fin i.n)} {tree : LocatedTrie (heapHeight i)} {queue : Multiset (ℕ × Fin i.n)} {s : Data}
    (h : Memory i deleted tentative settled tree queue s) (v : Fin i.n) (h310 : s.natReg 310=v.val) :
    Memory i deleted tentative settled tree queue (targetData s) ∧
      (targetData s).natReg 320=(if v∈settled then 1 else 0) := by
  have he := target_eval s
  refine ⟨?_,?_⟩
  · exact h.register_frame (fun j hj => he.nat_frame (target_nat_frame j (by omega) (by omega)))
      (he.real_frame (target_real_frame 56)) rfl rfl
  · simp [targetData,targetSettledAtoms,Atom.effect,instructionEffect,data,Data.machine,
      h310,h.layoutRegs.settled,h.settled v]
lemma Memory.advanceNext {i : Input} {deleted : List (Fin i.k)} {tentative : Fin i.n → Option ℕ}
    {settled : Finset (Fin i.n)} {tree : LocatedTrie (heapHeight i)} {queue : Multiset (ℕ × Fin i.n)} {s : Data}
    (h : Memory i deleted tentative settled tree queue s) (e : Fin i.k)
    (h308 : s.natReg 308=Adjacency.nodeAddress (layout i) e) :
    Memory i deleted tentative settled tree queue (nextData s) ∧
      (nextData s).natReg 308=Adjacency.root (layout i) (adjacency i.graph e.val (i.graph.tail e)) := by
  have he := next_eval s
  refine ⟨?_,?_⟩
  · exact h.register_frame (fun j hj => he.nat_frame (next_nat_frame j (by omega) (by omega)))
      (he.real_frame (next_real_frame 56)) rfl rfl
  · simp [nextData,nextAtoms,Atom.effect,instructionEffect,data,Data.machine,h308,h.graph.next e]
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s131
section s132
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
lemma edgeGuard_nat_frame (j : ℕ) (hj : 300 ≤ j)
    (hk : j∉({312,316,318,320,322,324,326,336} : Finset ℕ)) : NatFrame edgeGuard j := by
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hk
  refine ⟨⟨target_nat_frame j (by tauto) (by tauto),candidate_nat_frame j hj ?_,trivial⟩,trivial⟩
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or];tauto
lemma Memory.edgeGuard {i : Input} {deleted : List (Fin i.k)} {tentative : Fin i.n → Option ℕ}
    {settled : Finset (Fin i.n)} {tree : LocatedTrie (heapHeight i)} {queue : Multiset (ℕ × Fin i.n)} {s : Data}
    (h : Memory i deleted tentative settled tree queue s) (e : Fin i.k) (key : ℕ)
    (h308 : s.natReg 308=Adjacency.nodeAddress (layout i) e) (h310 : s.natReg 310=(i.graph.head e).val)
    (h304 : s.natReg 304=key) (h316 : s.natReg 316=(if e∈live deleted then 1 else 0))
    (hbound : key+i.weight e < 2^(heapHeight i)) :
    let r := Exact.relax i.graph (live deleted) i.weight settled key e tentative queue
    ∃ cost t next, Eval edgeGuard s cost t ∧ cost ≤ 64*(heapHeight i+1) ∧
      Memory i deleted r.1 settled next r.2 t := by
  by_cases ha : e∈live deleted
  · have hflag : s.natReg 316=1 := by simpa only [if_pos ha] using h316
    have htest : (Test.natLess 56 316).holds s := by simp [Test.holds,h.heap.zero,hflag]
    obtain ⟨hm,hvalue⟩ := h.target (i.graph.head e) h310
    let u := targetData s
    have hu56 : u.natReg 56=0 := hm.heap.zero
    have hu26 : u.natReg 26=1 := hm.heap.unit
    have hu304 : u.natReg 304=key := ((target_eval s).nat_frame (target_nat_frame 304 (by omega) (by omega))).trans h304
    have hu308 : u.natReg 308=Adjacency.nodeAddress (layout i) e := ((target_eval s).nat_frame (target_nat_frame 308 (by omega) (by omega))).trans h308
    have hu310 : u.natReg 310=(i.graph.head e).val := ((target_eval s).nat_frame (target_nat_frame 310 (by omega) (by omega))).trans h310
    change u.natReg 320=(if i.graph.head e∈settled then 1 else 0) at hvalue
    by_cases hs : i.graph.head e∈settled
    · have hno : ¬(e∈live deleted ∧ i.graph.head e∉settled ∧ Improves (tentative (i.graph.head e)) (key+i.weight e)) := by tauto
      simp only [Exact.relax,if_neg hno]
      have hu320 : u.natReg 320=1 := by simpa only [if_pos hs] using hvalue
      have ht : ¬(Test.natLess 320 26).holds u := by simp [Test.holds,hu320,hu26]
      refine ⟨5,u,tree,Eval.branchYes htest (Eval.seq (target_eval s) (Eval.branchNo ht (Eval.skip u))),by omega,hm⟩
    · have hu320 : u.natReg 320=0 := by simpa only [if_neg hs] using hvalue
      have ht : (Test.natLess 320 26).holds u := by simp [Test.holds,hu320,hu26]
      obtain ⟨c,t,next,he,hc,htm⟩ := hm.candidate e key hu308 hu310 hu304 ha hs hbound
      refine ⟨(2+(c+1))+1,t,next,Eval.branchYes htest (Eval.seq (target_eval s) (Eval.branchYes ht he)),by omega,htm⟩
  · have hno : ¬(e∈live deleted ∧ i.graph.head e∉settled ∧ Improves (tentative (i.graph.head e)) (key+i.weight e)) := by tauto
    simp only [Exact.relax,if_neg hno]
    have hflag : s.natReg 316=0 := by simpa only [if_neg ha] using h316
    have htest : ¬(Test.natLess 56 316).holds s := by simp [Test.holds,h.heap.zero,hflag]
    exact ⟨2,s,tree,Eval.branchNo htest (Eval.skip s),by omega,h⟩
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s132
section s133
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
lemma edgeBody_append {s u v t : Data} {a b c : ℕ} (hh : Eval edgeHeader s a u)
    (hg : Eval edgeGuard u b v) (hn : Eval (Structured.sequence (nextAtoms.map Cmd.atom)) v c t) :
    Eval edgeBody s (a+b+c) t := by
  cases hh with
  | seq hl ha =>
    have he := Eval.seq hl (Eval.seq ha (Eval.seq hg hn))
    convert he using 1 <;> first | rfl | omega
lemma edgeBody_frame (j : ℕ) (hh : NatFrame edgeHeader j) (hg : NatFrame edgeGuard j)
    (hn : NatFrame (Structured.sequence (nextAtoms.map Cmd.atom)) j) : NatFrame edgeBody j :=
  ⟨hh.1,hh.2,hg,hn⟩
lemma edgeBody_key_frame : NatFrame edgeBody 304 :=
  edgeBody_frame 304 (edgeHeader_nat_frame 304 (by norm_num))
    (edgeGuard_nat_frame 304 (by omega) (by norm_num)) (next_nat_frame 304 (by omega) (by omega))
lemma edgeBody_vertex_frame : NatFrame edgeBody 306 :=
  edgeBody_frame 306 (edgeHeader_nat_frame 306 (by norm_num))
    (edgeGuard_nat_frame 306 (by omega) (by norm_num)) (next_nat_frame 306 (by omega) (by omega))
lemma Memory.edgeBody {i : Input} {deleted : List (Fin i.k)} {tentative : Fin i.n → Option ℕ}
    {settled : Finset (Fin i.n)} {tree : LocatedTrie (heapHeight i)} {queue : Multiset (ℕ × Fin i.n)} {s : Data}
    (h : Memory i deleted tentative settled tree queue s) (e : Fin i.k) (key : ℕ)
    (h308 : s.natReg 308=Adjacency.nodeAddress (layout i) e) (h304 : s.natReg 304=key)
    (hbound : key+i.weight e < 2^(heapHeight i)) :
    let r := Exact.relax i.graph (live deleted) i.weight settled key e tentative queue
    ∃ cost t next, Eval edgeBody s cost t ∧ cost ≤ 80*(heapHeight i+1) ∧
      Memory i deleted r.1 settled next r.2 t ∧
      t.natReg 308=Adjacency.root (layout i) (adjacency i.graph e.val (i.graph.tail e)) := by
  let u := edgeHeaderData s
  obtain ⟨hu,huHead,huActive⟩ := h.edgeHeader e h308
  have heHeader := edgeHeader_eval s
  have hu308 : u.natReg 308=Adjacency.nodeAddress (layout i) e :=
    (heHeader.nat_frame (edgeHeader_nat_frame 308 (by norm_num))).trans h308
  have hu304 : u.natReg 304=key := (heHeader.nat_frame (edgeHeader_nat_frame 304 (by norm_num))).trans h304
  obtain ⟨c,v,next,heGuard,hc,hv⟩ := hu.edgeGuard e key hu308 huHead hu304 huActive hbound
  have hv308 : v.natReg 308=Adjacency.nodeAddress (layout i) e :=
    (heGuard.nat_frame (edgeGuard_nat_frame 308 (by omega) (by norm_num))).trans hu308
  obtain ⟨ht,htNext⟩ := hv.advanceNext e hv308
  refine ⟨5+c+3,nextData v,next,edgeBody_append heHeader heGuard (next_eval v),by omega,ht,htNext⟩
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s133
section s134
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Adjacency
lemma Chain.graph_frame {i : Input} {l : Layout.Addresses} {s t : Structured.Data}
    (hs : StaticImage i l s) (ht : StaticImage i l t) (es : List (Fin i.k)) (hc : Chain l s es) : Chain l t es := by
  induction es with
  | nil => trivial
  | cons e es ih =>
    refine ⟨?_,ih hc.2⟩
    exact (ht.next e).trans ((hs.next e).symm.trans hc.1)
end DecrAlmostLinearSSSP.Decremental.Exact.Adjacency
end s134
section s135
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact
lemma ScanState.relax {n k : ℕ} {g : Digraph n k} {active : Finset (Fin k)} {w : Fin k → ℕ}
    {source v : Fin n} {key : ℕ} {settled : Finset (Fin n)} {scanned : List (Fin k)}
    {tentative : Fin n → Option ℕ} {queue : Multiset (ℕ × Fin n)}
    (h : ScanState g active w source v key settled scanned tentative queue) (e : Fin k) (htail : g.tail e=v) :
    let result := Exact.relax g active w settled key e tentative queue
    ScanState g active w source v key settled (e::scanned) result.1 result.2 ∧ result.2.card ≤ queue.card+1 := by
  classical
  by_cases himprove : e∈active ∧ g.head e∉settled ∧ Improves (tentative (g.head e)) (key+w e)
  · simp only [Exact.relax,if_pos himprove]
    have hsmaller := (improves_iff _ _).mp himprove.2.2
    have hvne : v ≠ g.head e := by
      intro hh
      have hbad := hsmaller key (hh ▸ h.current)
      omega
    refine ⟨⟨h.labels.relax_edge key v h.current e himprove.1 htail himprove.2.1 hsmaller,?_,?_,?_⟩,by simp⟩
    · rw [Function.update_of_ne hvne];exact h.current
    · intro item hitem
      rcases Multiset.mem_cons.mp hitem with hh | hh
      · subst item;simp
      · exact h.minimum item hh
    · intro a ha hactive hatail
      rcases List.mem_cons.mp ha with ha | ha
      · subst a
        exact ⟨key+w e,Function.update_self _ _ _,le_rfl⟩
      · obtain ⟨dh,hdh,hle⟩ := h.relaxed a ha hactive hatail
        by_cases hh : g.head a = g.head e
        · refine ⟨key+w e,?_,?_⟩
          · rw [hh,Function.update_self]
          · have hlt := hsmaller dh (hh ▸ hdh);omega
        · exact ⟨dh,by rwa [Function.update_of_ne hh],hle⟩
  · simp only [Exact.relax,if_neg himprove]
    refine ⟨⟨h.labels,h.current,h.minimum,?_⟩,by omega⟩
    intro a ha hactive hatail
    rcases List.mem_cons.mp ha with ha | ha
    · subst a
      by_cases hsettled : g.head e∈settled
      · exact h.labels.settled_edge_bound v key h.current e hactive htail hsettled
      · apply not_improves (tentative (g.head e)) (key+w e)
        intro hyes
        exact himprove ⟨hactive,hsettled,hyes⟩
    · exact h.relaxed a ha hactive hatail
end DecrAlmostLinearSSSP.Decremental.Exact
end s135
section s136
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact
lemma ScanState.scan {n k : ℕ} {g : Digraph n k} {active : Finset (Fin k)} {w : Fin k → ℕ}
    {source v : Fin n} {key : ℕ} {settled : Finset (Fin n)} {scanned : List (Fin k)}
    {tentative : Fin n → Option ℕ} {queue : Multiset (ℕ × Fin n)}
    (h : ScanState g active w source v key settled scanned tentative queue)
    (es : List (Fin k)) (htail : ∀ e∈es, g.tail e=v) :
    let r := scanEdges g active w settled key es tentative queue
    ScanState g active w source v key settled (es.reverse++scanned) r.1 r.2 ∧
      r.2.card ≤ queue.card+es.length := by
  induction es generalizing scanned tentative queue with
  | nil => exact ⟨h,le_rfl⟩
  | cons e es ih =>
    have he := h.relax e (htail e (by simp))
    have hr := ih he.1 (fun a ha => htail a (List.mem_cons_of_mem _ ha))
    refine ⟨?_,?_⟩
    · simpa only [scanEdges,List.reverse_cons,List.append_assoc,List.singleton_append] using hr.1
    · have hc := he.2
      have hrc := hr.2
      change (scanEdges g active w settled key es
        (Exact.relax g active w settled key e tentative queue).1
        (Exact.relax g active w settled key e tentative queue).2).2.card ≤ _
      simp only [List.length_cons]
      omega
lemma scan_outgoing {n k : ℕ} {g : Digraph n k} {active : Finset (Fin k)} {w : Fin k → ℕ}
    {source v : Fin n} {key : ℕ} {settled : Finset (Fin n)}
    {tentative : Fin n → Option ℕ} {queue : Multiset (ℕ × Fin n)}
    (h : LabelInvariant g active w source tentative settled ((key,v)::ₘqueue)) (hv : v∉settled)
    (hmin : ∀ item∈queue, key ≤ item.1) :
    let r := scanEdges g active w settled key (adjacency g k v) tentative queue
    LabelInvariant g active w source r.1 (insert v settled) r.2 ∧
      r.2.card ≤ queue.card+(adjacency g k v).length := by
  have hs := scan_initial h hv hmin
  have hf := hs.scan (adjacency g k v) (fun e he => (adjacency_mem g k v e).mp he |>.2)
  refine ⟨scan_finished hf.1 hv ?_,hf.2⟩
  intro e he ht
  simp only [List.mem_append,List.mem_reverse,List.not_mem_nil,or_false]
  exact (adjacency_mem g k v e).mpr ⟨e.isLt,ht⟩
end DecrAlmostLinearSSSP.Decremental.Exact
end s136
section s137
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
lemma Memory.edgeLoop {i : Input} {deleted : List (Fin i.k)} {tentative : Fin i.n → Option ℕ}
    {settled : Finset (Fin i.n)} {tree : LocatedTrie (heapHeight i)} {queue : Multiset (ℕ × Fin i.n)} {s : Data}
    (h : Memory i deleted tentative settled tree queue s) (key : ℕ) (es : List (Fin i.k))
    (hchain : Adjacency.Chain (layout i) s es) (h308 : s.natReg 308=Adjacency.root (layout i) es)
    (h304 : s.natReg 304=key) (hbound : ∀ e∈es, key+i.weight e < 2^(heapHeight i)) :
    let r := scanEdges i.graph (live deleted) i.weight settled key es tentative queue
    ∃ cost t next, Eval edgeLoop s cost t ∧ cost ≤ 82*(heapHeight i+1)*es.length+2 ∧
      Memory i deleted r.1 settled next r.2 t ∧ t.natReg 308=0 := by
  induction es generalizing tentative queue tree s with
  | nil =>
    have hc : s.natReg 308=0 := h308
    have ht : ¬(Test.natLess 56 308).holds s := by simp [Test.holds,h.heap.zero,hc]
    exact ⟨2,s,tree,Eval.loopNo s ht,by simp,h,hc⟩
  | cons e es ih =>
    have hcursor : s.natReg 308=Adjacency.nodeAddress (layout i) e := h308
    obtain ⟨c,u,utree,heu,hc,hu,hu308⟩ := h.edgeBody e key hcursor h304 (hbound e (by simp))
    have hnext : Adjacency.root (layout i) (adjacency i.graph e.val (i.graph.tail e))=Adjacency.root (layout i) es :=
      (h.graph.next e).symm.trans hchain.1
    have huCursor : u.natReg 308=Adjacency.root (layout i) es := hu308.trans hnext
    have huKey : u.natReg 304=key := (heu.nat_frame edgeBody_key_frame).trans h304
    have huChain := Adjacency.Chain.graph_frame h.graph hu.graph es hchain.2
    obtain ⟨d,t,next,het,hd,ht,ht308⟩ := ih hu huChain huCursor huKey (fun a ha => hbound a (List.mem_cons_of_mem _ ha))
    have hpositive : 0<Adjacency.nodeAddress (layout i) e := Adjacency.node_positive i e
    have htest : (Test.natLess 56 308).holds s := by simpa [Test.holds,h.heap.zero,hcursor] using hpositive
    refine ⟨c+d+2,t,next,Eval.loopYes htest heu het,?_,ht,ht308⟩
    simp only [List.length_cons]
    have hh : 82*(heapHeight i+1)*(es.length+1)=82*(heapHeight i+1)*es.length+82*(heapHeight i+1) := by ring
    rw [hh]
    omega
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s137
section s138
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
lemma settle_eval (s : Data) : Eval (Structured.sequence (settleAtoms.map Cmd.atom)) s 2 (settledData s) := eval_sequence_atoms settleAtoms s
lemma settle_nat_frame (j : ℕ) (hj : j≠318) : NatFrame (Structured.sequence (settleAtoms.map Cmd.atom)) j := by
  simp [settleAtoms,Structured.sequence,NatFrame,writesNat,Ne.symm hj]
lemma settle_real_frame (j : ℕ) : RealFrame (Structured.sequence (settleAtoms.map Cmd.atom)) j := by
  simp [settleAtoms,Structured.sequence,RealFrame,writesReal]
lemma Memory.settle {i : Input} {deleted : List (Fin i.k)} {tentative : Fin i.n → Option ℕ}
    {settled : Finset (Fin i.n)} {tree : LocatedTrie (heapHeight i)} {queue : Multiset (ℕ × Fin i.n)} {s : Data}
    (h : Memory i deleted tentative settled tree queue s) (v : Fin i.n) (h306 : s.natReg 306=v.val) :
    Memory i deleted tentative (insert v settled) tree queue (settledData s) := by
  classical
  let t := settledData s
  have he := settle_eval s
  have hm : t.natMem=Function.update s.natMem ((layout i).settled+v.val) 1 := by
    simp [t,settledData,settleAtoms,Atom.effect,instructionEffect,data,Data.machine,h306,h.layoutRegs.settled,h.heap.unit]
  have hn (j : ℕ) (hj : j ≤ 246) : t.natReg j=s.natReg j := he.nat_frame (settle_nat_frame j (by omega))
  have hframe (a : ℕ) (ha : a≠(layout i).settled+v.val) : t.natMem a=s.natMem a := by rw [hm,Function.update_of_ne ha]
  have hv := v.isLt
  have hheap := h.heap.below_frame (fun j hj => hn j (by simp only [Finset.mem_insert,Finset.mem_singleton] at hj;omega)) (by
    intro a ha
    apply hframe a
    have hb := (Layout.vertex_bounds i v).2.2.1
    change (layout i).settled+v.val < heapBase i at hb
    omega)
  refine ⟨(hn 66 (by omega)).trans h.vertices,(hn 68 (by omega)).trans h.edges,
    (hn 72 (by omega)).trans h.source,(he.real_frame (settle_real_frame 56)).trans h.zeroR,
    ?_,?_,?_,?_,?_,hheap⟩
  · constructor
    · exact (hn 224 (by omega)).trans h.layoutRegs.heads
    · exact (hn 226 (by omega)).trans h.layoutRegs.settled
    · exact (hn 228 (by omega)).trans h.layoutRegs.active
    · exact (hn 230 (by omega)).trans h.layoutRegs.distances
    · exact (hn 232 (by omega)).trans h.layoutRegs.nodes
    · exact (hn 234 (by omega)).trans h.layoutRegs.powers
  · apply h.graph.frame
    intro a ha
    apply hframe a
    simp only [Adjacency.staticFootprint,Finset.mem_union,Finset.mem_Ico] at ha
    dsimp [layout,Layout.addresses] at ha ⊢
    rcases ha with ha | ha <;> omega
  · intro e
    rw [hframe _ (by dsimp [layout,Layout.addresses];omega)]
    exact h.active e
  · apply h.tentative.frame
    · intro u
      apply hframe
      have hu := u.isLt
      dsimp [layout,Layout.addresses]
      omega
    · intro u
      apply hframe
      have hu := u.isLt
      dsimp [layout,Layout.addresses]
      omega
    · intro u;rfl
  · intro u
    by_cases hu : u=v
    · subst u
      rw [hm,Function.update_self,if_pos (Finset.mem_insert_self _ _)]
    · rw [hframe _ (by intro hh;apply hu;apply Fin.ext;omega)]
      simpa [Finset.mem_insert,hu] using h.settled u
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s138
section s139
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
lemma scanPrepare_eval (s : Data) : Eval (Structured.sequence (scanPrepareAtoms.map Cmd.atom)) s 2 (scanPrepared s) := eval_sequence_atoms scanPrepareAtoms s
lemma scanPrepare_nat_frame (j : ℕ) (hj : j≠308) : NatFrame (Structured.sequence (scanPrepareAtoms.map Cmd.atom)) j := by
  simp [scanPrepareAtoms,Structured.sequence,NatFrame,writesNat,Ne.symm hj]
lemma scanPrepare_real_frame (j : ℕ) : RealFrame (Structured.sequence (scanPrepareAtoms.map Cmd.atom)) j := by
  simp [scanPrepareAtoms,Structured.sequence,RealFrame,writesReal]
lemma Memory.scanPrepare {i : Input} {deleted : List (Fin i.k)} {tentative : Fin i.n → Option ℕ}
    {settled : Finset (Fin i.n)} {tree : LocatedTrie (heapHeight i)} {queue : Multiset (ℕ × Fin i.n)} {s : Data}
    (h : Memory i deleted tentative settled tree queue s) (v : Fin i.n) (h306 : s.natReg 306=v.val) :
    Memory i deleted tentative settled tree queue (scanPrepared s) ∧
      (scanPrepared s).natReg 308=Adjacency.root (layout i) (adjacency i.graph i.k v) := by
  have he := scanPrepare_eval s
  refine ⟨?_,?_⟩
  · exact h.register_frame (fun j hj => he.nat_frame (scanPrepare_nat_frame j (by omega)))
      (he.real_frame (scanPrepare_real_frame 56)) rfl rfl
  · simp [scanPrepared,scanPrepareAtoms,Atom.effect,instructionEffect,data,Data.machine,
      h306,h.layoutRegs.heads,h.graph.heads v]
lemma Memory.scan {i : Input} {deleted : List (Fin i.k)} {tentative : Fin i.n → Option ℕ}
    {settled : Finset (Fin i.n)} {tree : LocatedTrie (heapHeight i)} {queue : Multiset (ℕ × Fin i.n)} {s : Data}
    (h : Memory i deleted tentative settled tree queue s) (v : Fin i.n) (key : ℕ)
    (h306 : s.natReg 306=v.val) (h304 : s.natReg 304=key)
    (hbound : ∀ e∈adjacency i.graph i.k v, key+i.weight e < 2^(heapHeight i)) :
    let r := scanEdges i.graph (live deleted) i.weight settled key (adjacency i.graph i.k v) tentative queue
    ∃ cost t next, Eval scan s cost t ∧ cost ≤ 82*(heapHeight i+1)*(adjacency i.graph i.k v).length+6 ∧
      Memory i deleted r.1 (insert v settled) next r.2 t := by
  let u := scanPrepared s
  obtain ⟨hu,hu308⟩ := h.scanPrepare v h306
  have hu304 : u.natReg 304=key := ((scanPrepare_eval s).nat_frame (scanPrepare_nat_frame 304 (by omega))).trans h304
  have hu306 : u.natReg 306=v.val := ((scanPrepare_eval s).nat_frame (scanPrepare_nat_frame 306 (by omega))).trans h306
  obtain ⟨d,w,next,hew,hd,hw,hw308⟩ := hu.edgeLoop key (adjacency i.graph i.k v) (hu.graph.chain v) hu308 hu304 hbound
  have hw306 : w.natReg 306=v.val := (hew.nat_frame edgeBody_vertex_frame).trans hu306
  have ht := hw.settle v hw306
  exact ⟨2+(d+2),settledData w,next,Eval.seq (scanPrepare_eval s) (Eval.seq hew (settle_eval w)),by omega,ht⟩
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
theorem solution : (((((((∀ {n h base slot : Nat} {tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin n))} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  @DecrAlmostLinearSSSP.Decremental.Exact.Heap.Image n h base slot tree queue s →
    ∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j h →
        @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base j ∉
          @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint h tree) ∧ (∀ {n h base slot : Nat} {tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin n))} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  @DecrAlmostLinearSSSP.Decremental.Exact.Heap.Image n h base slot tree queue s →
    @Eq.{1} Nat
      (@DecrAlmostLinearSSSP.Decremental.RadixQueue.count h
        (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.abstract h tree))
      (@Multiset.card.{0} (Prod.{0, 0} Nat (Fin n)) queue))) ∧ ((∀ {n h base slot : Nat} {tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h}
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
                      (∀ (a : Nat), @LT.lt.{0} Nat instLTNat a slot → @Eq.{1} Nat (t.natMem a) (s.natMem a)))))) ∧ (∀ {n h base slot : Nat} {tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h}
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
                        (∀ (a : Nat), @LT.lt.{0} Nat instLTNat a slot → @Eq.{1} Nat (t.natMem a) (s.natMem a)))))))))))) ∧ (((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (v : Fin i.n),
  @LT.lt.{0} Nat instLTNat (@Fin.val i.n v) (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapSlot i)) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (v : Fin i.n),
  @LT.lt.{0} Nat instLTNat
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.layout i).settled (@Fin.val i.n v))
    (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapSlot i))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (v : Fin i.n),
  @LT.lt.{0} Nat instLTNat
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.layout i).distances (@Fin.val i.n v))
    (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapSlot i)) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (e : Fin i.k),
  @LT.lt.{0} Nat instLTNat
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.layout i).active (@Fin.val i.k e))
    (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapSlot i)) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (a : Nat),
  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.staticFootprint i
        (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.layout i))
      a →
    @LT.lt.{0} Nat instLTNat a (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapSlot i)))))) ∧ ((((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)} {tentative : Fin i.n → Option.{0} Nat}
  {settled : Finset.{0} (Fin i.n)}
  {tree next :
    DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)}
  {queue remaining : Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled tree queue s →
    @DecrAlmostLinearSSSP.Decremental.Exact.Heap.Image i.n
        (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)
        (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapBase i)
        (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapSlot i) next remaining t →
      (∀ (j : Nat),
          @LT.lt.{0} Nat instLTNat j (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))) →
            @Eq.{1} Nat (t.natReg j) (s.natReg j)) →
        @Eq.{1} Real (t.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
            (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56)))) →
          @Eq.{1} (Nat → Real) t.realMem s.realMem →
            (∀ (a : Nat),
                @LT.lt.{0} Nat instLTNat a (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapSlot i) →
                  @Eq.{1} Nat (t.natMem a) (s.natMem a)) →
              DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled next remaining t) ∧ (∀ {n h base slot : Nat} {tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h}
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
        @DecrAlmostLinearSSSP.Decremental.Exact.Heap.Image n h base slot tree queue t)) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)} {tentative : Fin i.n → Option.{0} Nat}
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
            DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled tree queue t) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    ∃ c,
      And
        (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.queueCount s c
          (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.counted s))
        (@LE.le.{0} Nat instLENat c (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))) ∧ (((∀ (j : Nat),
  @Ne.{1} Nat j (@OfNat.ofNat.{0} Nat (nat_lit 346) (instOfNatNat (nat_lit 346))) →
    @Ne.{1} Nat j (@OfNat.ofNat.{0} Nat (nat_lit 348) (instOfNatNat (nat_lit 348))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.queueCount j) ∧ (∀ (j : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.queueCount j)) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)} {tentative : Fin i.n → Option.{0} Nat}
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
              (@Multiset.card.{0} (Prod.{0, 0} Nat (Fin i.n)) queue))))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval
    (DecrAlmostLinearSSSP.Decremental.Structured.sequence
      (@List.map.{0, 0} DecrAlmostLinearSSSP.Decremental.Structured.Atom DecrAlmostLinearSSSP.Decremental.Structured.Cmd
        DecrAlmostLinearSSSP.Decremental.Structured.Cmd.atom
        DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.candidateAtoms))
    s (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
    (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.candidateData s)) ∧ (∀
  j ∉
    @Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 312) (instOfNatNat (nat_lit 312)))
      (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 316) (instOfNatNat (nat_lit 316)))
        (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 322) (instOfNatNat (nat_lit 322)))
          (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 324) (instOfNatNat (nat_lit 324)))
            (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 326) (instOfNatNat (nat_lit 326)))
              (@Singleton.singleton.{0, 0} Nat (Finset.{0} Nat) (@Finset.instSingleton.{0} Nat)
                (@OfNat.ofNat.{0} Nat (nat_lit 336) (instOfNatNat (nat_lit 336)))))))),
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
    (DecrAlmostLinearSSSP.Decremental.Structured.sequence
      (@List.map.{0, 0} DecrAlmostLinearSSSP.Decremental.Structured.Atom DecrAlmostLinearSSSP.Decremental.Structured.Cmd
        DecrAlmostLinearSSSP.Decremental.Structured.Cmd.atom
        DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.candidateAtoms))
    j)))))) ∧ (((((∀ (j : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
    (DecrAlmostLinearSSSP.Decremental.Structured.sequence
      (@List.map.{0, 0} DecrAlmostLinearSSSP.Decremental.Structured.Atom DecrAlmostLinearSSSP.Decremental.Structured.Cmd
        DecrAlmostLinearSSSP.Decremental.Structured.Cmd.atom
        DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.candidateAtoms))
    j) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)} {tentative : Fin i.n → Option.{0} Nat}
  {settled : Finset.{0} (Fin i.n)}
  {tree :
    DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled tree queue s →
    ∀ (e : Fin i.k) (key : Nat),
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 308) (instOfNatNat (nat_lit 308))))
          (@DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.nodeAddress
            (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.layout i) i.k e) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 310) (instOfNatNat (nat_lit 310))))
            (@Fin.val i.n (@DecrAlmostLinearSSSP.Decremental.Digraph.head i.n i.k i.graph e)) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 304) (instOfNatNat (nat_lit 304)))) key →
            And
              (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled tree queue
                (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.candidateData s))
              (And
                (@Eq.{1} Nat
                  ((DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.candidateData s).natReg
                    (@OfNat.ofNat.{0} Nat (nat_lit 310) (instOfNatNat (nat_lit 310))))
                  (@Fin.val i.n (@DecrAlmostLinearSSSP.Decremental.Digraph.head i.n i.k i.graph e)))
                (And
                  (@Eq.{1} Nat
                    ((DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.candidateData s).natReg
                      (@OfNat.ofNat.{0} Nat (nat_lit 326) (instOfNatNat (nat_lit 326))))
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) key (i.weight e)))
                  (And
                    (@Eq.{1} Nat
                      ((DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.candidateData s).natReg
                        (@OfNat.ofNat.{0} Nat (nat_lit 316) (instOfNatNat (nat_lit 316))))
                      (s.natMem (@Fin.val i.n (@DecrAlmostLinearSSSP.Decremental.Digraph.head i.n i.k i.graph e))))
                    (And
                      (@Eq.{1} Nat
                        ((DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.candidateData s).natReg
                          (@OfNat.ofNat.{0} Nat (nat_lit 322) (instOfNatNat (nat_lit 322))))
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.layout i).distances
                          (@Fin.val i.n (@DecrAlmostLinearSSSP.Decremental.Digraph.head i.n i.k i.graph e))))
                      (@Eq.{1} Nat
                        ((DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.candidateData s).natReg
                          (@OfNat.ofNat.{0} Nat (nat_lit 324) (instOfNatNat (nat_lit 324))))
                        (s.natMem
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.layout i).distances
                            (@Fin.val i.n (@DecrAlmostLinearSSSP.Decremental.Digraph.head i.n i.k i.graph e))))))))))) ∧ ((∀ {n h base slot : Nat} {tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h}
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
      (∀ (a : Nat), @LE.le.{0} Nat instLENat base a → @Eq.{1} Nat (t.natMem a) (s.natMem a)) →
        @DecrAlmostLinearSSSP.Decremental.Exact.Heap.Image n h base slot tree queue t) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval
    (DecrAlmostLinearSSSP.Decremental.Structured.sequence
      (@List.map.{0, 0} DecrAlmostLinearSSSP.Decremental.Structured.Atom DecrAlmostLinearSSSP.Decremental.Structured.Cmd
        DecrAlmostLinearSSSP.Decremental.Structured.Cmd.atom
        DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.improveAtoms))
    s (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
    (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.improved s)))) ∧ (((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    And
      (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.improved s).natMem
        (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
          (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natMem
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 310) (instOfNatNat (nat_lit 310))))
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 322) (instOfNatNat (nat_lit 322))))
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 326) (instOfNatNat (nat_lit 326))))))
      (And
        (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.improved s).realMem
          (@Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realMem
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 310) (instOfNatNat (nat_lit 310))))
            (@Nat.cast.{0} Real Real.instNatCast
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 326) (instOfNatNat (nat_lit 326)))))))
        (And
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.improved s).natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260))))
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 326) (instOfNatNat (nat_lit 326)))))
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.improved s).natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 262) (instOfNatNat (nat_lit 262))))
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 310) (instOfNatNat (nat_lit 310)))))))) ∧ (∀ (j : Nat),
  @Ne.{1} Nat j (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260))) →
    @Ne.{1} Nat j (@OfNat.ofNat.{0} Nat (nat_lit 262) (instOfNatNat (nat_lit 262))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
        (DecrAlmostLinearSSSP.Decremental.Structured.sequence
          (@List.map.{0, 0} DecrAlmostLinearSSSP.Decremental.Structured.Atom
            DecrAlmostLinearSSSP.Decremental.Structured.Cmd DecrAlmostLinearSSSP.Decremental.Structured.Cmd.atom
            DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.improveAtoms))
        j)) ∧ ((∀ (j : Nat),
  @Ne.{1} Nat j (@OfNat.ofNat.{0} Nat (nat_lit 332) (instOfNatNat (nat_lit 332))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
      (DecrAlmostLinearSSSP.Decremental.Structured.sequence
        (@List.map.{0, 0} DecrAlmostLinearSSSP.Decremental.Structured.Atom
          DecrAlmostLinearSSSP.Decremental.Structured.Cmd DecrAlmostLinearSSSP.Decremental.Structured.Cmd.atom
          DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.improveAtoms))
      j) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {l : DecrAlmostLinearSSSP.Decremental.Exact.Layout.Addresses}
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
              t) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)} {tentative : Fin i.n → Option.{0} Nat}
  {settled : Finset.{0} (Fin i.n)}
  {tree :
    DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled tree queue s →
    ∀ (target : Fin i.n) (candidate : Nat),
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 310) (instOfNatNat (nat_lit 310)))) (@Fin.val i.n target) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 322) (instOfNatNat (nat_lit 322))))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.layout i).distances (@Fin.val i.n target)) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 326) (instOfNatNat (nat_lit 326)))) candidate →
            And
              (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted
                (@Function.update.{1, 1} (Fin i.n) (fun a => Option.{0} Nat) (instDecidableEqFin i.n) tentative target
                  (@Option.some.{0} Nat candidate))
                settled tree queue (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.improved s))
              (And
                (@Eq.{1} Nat
                  ((DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.improved s).natReg
                    (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260))))
                  candidate)
                (@Eq.{1} Nat
                  ((DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.improved s).natReg
                    (@OfNat.ofNat.{0} Nat (nat_lit 262) (instOfNatNat (nat_lit 262))))
                  (@Fin.val i.n target)))))))) ∧ ((((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)} {tentative : Fin i.n → Option.{0} Nat}
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
                    (@Multiset.cons.{0} (Prod.{0, 0} Nat (Fin i.n)) (@Prod.mk.{0, 0} Nat (Fin i.n) key v) queue) t))) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)} {tentative : Fin i.n → Option.{0} Nat}
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
                        @LE.le.{0} Nat instLENat key (@Prod.fst.{0, 0} Nat (Fin i.n) item))))))))) ∧ ((∀ (j : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 300) (instOfNatNat (nat_lit 300))) j →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.improve j) ∧ ((∀ (j : Nat),
  @Ne.{1} Nat j (@OfNat.ofNat.{0} Nat (nat_lit 332) (instOfNatNat (nat_lit 332))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.improve j) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)} {tentative : Fin i.n → Option.{0} Nat}
  {settled : Finset.{0} (Fin i.n)}
  {tree :
    DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled tree queue s →
    ∀ (target : Fin i.n) (candidate : Nat),
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 310) (instOfNatNat (nat_lit 310)))) (@Fin.val i.n target) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 322) (instOfNatNat (nat_lit 322))))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.layout i).distances (@Fin.val i.n target)) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 326) (instOfNatNat (nat_lit 326)))) candidate →
            @LT.lt.{0} Nat instLTNat candidate
                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                  (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)) →
              ∃ cost t next,
                And
                  (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                    DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.improve s cost t)
                  (And
                    (@LE.le.{0} Nat instLENat cost
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 49) (instOfNatNat (nat_lit 49)))
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                    (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted
                      (@Function.update.{1, 1} (Fin i.n) (fun a => Option.{0} Nat) (instDecidableEqFin i.n) tentative
                        target (@Option.some.{0} Nat candidate))
                      settled next
                      (@Multiset.cons.{0} (Prod.{0, 0} Nat (Fin i.n)) (@Prod.mk.{0, 0} Nat (Fin i.n) candidate target)
                        queue)
                      t)))))) ∧ (((∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {w : Fin k → Nat}
  {source : Fin n} {tentative : Fin n → Option.{0} Nat} {settled : Finset.{0} (Fin n)}
  {remaining : Multiset.{0} (Prod.{0, 0} Nat (Fin n))} (key : Nat) (v : Fin n),
  @DecrAlmostLinearSSSP.Decremental.Exact.LabelInvariant n k g active w source tentative settled
      (@Multiset.cons.{0} (Prod.{0, 0} Nat (Fin n)) (@Prod.mk.{0, 0} Nat (Fin n) key v) remaining) →
    @Eq.{1} (Option.{0} Nat) (tentative v) (@Option.some.{0} Nat key) →
      ∀ (e : Fin k),
        @Membership.mem.{0, 0} (Fin k) (Finset.{0} (Fin k))
            (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin k)) (Fin k) (@Finset.instSetLike.{0} (Fin k))) active e →
          @Eq.{1} (Fin n) (@DecrAlmostLinearSSSP.Decremental.Digraph.tail n k g e) v →
            @DecrAlmostLinearSSSP.Decremental.Digraph.head n k g e ∉ settled →
              (∀ (d : Nat),
                  @Eq.{1} (Option.{0} Nat) (tentative (@DecrAlmostLinearSSSP.Decremental.Digraph.head n k g e))
                      (@Option.some.{0} Nat d) →
                    @LT.lt.{0} Nat instLTNat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) key (w e))
                      d) →
                @DecrAlmostLinearSSSP.Decremental.Exact.LabelInvariant n k g active w source
                  (@Function.update.{1, 1} (Fin n) (fun a => Option.{0} Nat) (instDecidableEqFin n) tentative
                    (@DecrAlmostLinearSSSP.Decremental.Digraph.head n k g e)
                    (@Option.some.{0} Nat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) key (w e))))
                  settled
                  (@Multiset.cons.{0} (Prod.{0, 0} Nat (Fin n)) (@Prod.mk.{0, 0} Nat (Fin n) key v)
                    (@Multiset.cons.{0} (Prod.{0, 0} Nat (Fin n))
                      (@Prod.mk.{0, 0} Nat (Fin n)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) key (w e))
                        (@DecrAlmostLinearSSSP.Decremental.Digraph.head n k g e))
                      remaining))) ∧ (∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {w : Fin k → Nat}
  {source : Fin n} {tentative : Fin n → Option.{0} Nat} {settled : Finset.{0} (Fin n)}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin n))},
  @DecrAlmostLinearSSSP.Decremental.Exact.LabelInvariant n k g active w source tentative settled queue →
    ∀ (v : Fin n) (key : Nat),
      @Eq.{1} (Option.{0} Nat) (tentative v) (@Option.some.{0} Nat key) →
        ∀ (e : Fin k),
          @Membership.mem.{0, 0} (Fin k) (Finset.{0} (Fin k))
              (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin k)) (Fin k) (@Finset.instSetLike.{0} (Fin k))) active e →
            @Eq.{1} (Fin n) (@DecrAlmostLinearSSSP.Decremental.Digraph.tail n k g e) v →
              @Membership.mem.{0, 0} (Fin n) (Finset.{0} (Fin n))
                  (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin n)) (Fin n) (@Finset.instSetLike.{0} (Fin n)))
                  settled (@DecrAlmostLinearSSSP.Decremental.Digraph.head n k g e) →
                ∃ d,
                  And
                    (@Eq.{1} (Option.{0} Nat) (tentative (@DecrAlmostLinearSSSP.Decremental.Digraph.head n k g e))
                      (@Option.some.{0} Nat d))
                    (@LE.le.{0} Nat instLENat d
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) key (w e))))) ∧ ((∀ (old : Option.{0} Nat) (candidate : Nat),
  Iff (DecrAlmostLinearSSSP.Decremental.Exact.Improves old candidate)
    (∀ (d : Nat), @Eq.{1} (Option.{0} Nat) old (@Option.some.{0} Nat d) → @LT.lt.{0} Nat instLTNat candidate d)) ∧ ((∀ (old : Option.{0} Nat) (candidate : Nat),
  Not (DecrAlmostLinearSSSP.Decremental.Exact.Improves old candidate) →
    ∃ d, And (@Eq.{1} (Option.{0} Nat) old (@Option.some.{0} Nat d)) (@LE.le.{0} Nat instLENat d candidate)) ∧ (∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {w : Fin k → Nat}
  {source : Fin n} {tentative : Fin n → Option.{0} Nat} {settled : Finset.{0} (Fin n)}
  {remaining : Multiset.{0} (Prod.{0, 0} Nat (Fin n))} (key : Nat) (v : Fin n),
  @DecrAlmostLinearSSSP.Decremental.Exact.LabelInvariant n k g active w source tentative settled
      (@Multiset.cons.{0} (Prod.{0, 0} Nat (Fin n)) (@Prod.mk.{0, 0} Nat (Fin n) key v) remaining) →
    @Membership.mem.{0, 0} (Fin n) (Finset.{0} (Fin n))
        (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin n)) (Fin n) (@Finset.instSetLike.{0} (Fin n))) settled v →
      @DecrAlmostLinearSSSP.Decremental.Exact.LabelInvariant n k g active w source tentative settled remaining))))))) ∧ ((((((∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {w : Fin k → Nat}
  {source v : Fin n} {key : Nat} {settled : Finset.{0} (Fin n)} {tentative : Fin n → Option.{0} Nat}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin n))},
  @DecrAlmostLinearSSSP.Decremental.Exact.LabelInvariant n k g active w source tentative settled
      (@Multiset.cons.{0} (Prod.{0, 0} Nat (Fin n)) (@Prod.mk.{0, 0} Nat (Fin n) key v) queue) →
    v ∉ settled →
      (∀ (item : Prod.{0, 0} Nat (Fin n)),
          @Membership.mem.{0, 0} (Prod.{0, 0} Nat (Fin n)) (Multiset.{0} (Prod.{0, 0} Nat (Fin n)))
              (@Multiset.instMembership.{0} (Prod.{0, 0} Nat (Fin n))) queue item →
            @LE.le.{0} Nat instLENat key (@Prod.fst.{0, 0} Nat (Fin n) item)) →
        @DecrAlmostLinearSSSP.Decremental.Exact.ScanState n k g active w source v key settled (@List.nil.{0} (Fin k))
          tentative queue) ∧ (∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {w : Fin k → Nat}
  {source v : Fin n} {key : Nat} {settled : Finset.{0} (Fin n)} {scanned : List.{0} (Fin k)}
  {tentative : Fin n → Option.{0} Nat} {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin n))},
  @DecrAlmostLinearSSSP.Decremental.Exact.ScanState n k g active w source v key settled scanned tentative queue →
    v ∉ settled →
      (∀ (e : Fin k),
          @Membership.mem.{0, 0} (Fin k) (Finset.{0} (Fin k))
              (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin k)) (Fin k) (@Finset.instSetLike.{0} (Fin k))) active e →
            @Eq.{1} (Fin n) (@DecrAlmostLinearSSSP.Decremental.Digraph.tail n k g e) v →
              @Membership.mem.{0, 0} (Fin k) (List.{0} (Fin k)) (@List.instMembership.{0} (Fin k)) scanned e) →
        @DecrAlmostLinearSSSP.Decremental.Exact.LabelInvariant n k g active w source tentative
          (@Insert.insert.{0, 0} (Fin n) (Finset.{0} (Fin n)) (@Finset.instInsert.{0} (Fin n) (instDecidableEqFin n)) v
            settled)
          queue)) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)} {tentative : Fin i.n → Option.{0} Nat}
  {settled : Finset.{0} (Fin i.n)}
  {tree :
    DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled tree queue s →
    ∀ (e : Fin i.k) (key : Nat),
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 308) (instOfNatNat (nat_lit 308))))
          (@DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.nodeAddress
            (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.layout i) i.k e) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 310) (instOfNatNat (nat_lit 310))))
            (@Fin.val i.n (@DecrAlmostLinearSSSP.Decremental.Digraph.head i.n i.k i.graph e)) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 304) (instOfNatNat (nat_lit 304)))) key →
            @Membership.mem.{0, 0} (Fin i.k) (Finset.{0} (Fin i.k))
                (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin i.k)) (Fin i.k) (@Finset.instSetLike.{0} (Fin i.k)))
                (@DecrAlmostLinearSSSP.Decremental.live i.k deleted) e →
              @DecrAlmostLinearSSSP.Decremental.Digraph.head i.n i.k i.graph e ∉ settled →
                @LT.lt.{0} Nat instLTNat
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) key (i.weight e))
                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                      (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)) →
                  have result :=
                    @DecrAlmostLinearSSSP.Decremental.Exact.relax i.n i.k i.graph
                      (@DecrAlmostLinearSSSP.Decremental.live i.k deleted) i.weight settled key e tentative queue;
                  ∃ cost t next,
                    And
                      (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                        DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.candidate s cost t)
                      (And
                        (@LE.le.{0} Nat instLENat cost
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 60) (instOfNatNat (nat_lit 60)))
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                        (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted
                          (@Prod.fst.{0, 0} (Fin i.n → Option.{0} Nat) (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n)))
                            result)
                          settled next
                          (@Prod.snd.{0, 0} (Fin i.n → Option.{0} Nat) (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n)))
                            result)
                          t))) ∧ (∀ (j : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 300) (instOfNatNat (nat_lit 300))) j →
    j ∉
        @Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 312) (instOfNatNat (nat_lit 312)))
          (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 316) (instOfNatNat (nat_lit 316)))
            (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 322) (instOfNatNat (nat_lit 322)))
              (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 324) (instOfNatNat (nat_lit 324)))
                (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 326) (instOfNatNat (nat_lit 326)))
                  (@Singleton.singleton.{0, 0} Nat (Finset.{0} Nat) (@Finset.instSingleton.{0} Nat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 336) (instOfNatNat (nat_lit 336)))))))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.candidate j))) ∧ (((∀ (j : Nat),
  @Ne.{1} Nat j (@OfNat.ofNat.{0} Nat (nat_lit 332) (instOfNatNat (nat_lit 332))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.candidate j) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.edgeHeader s
    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
    (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.edgeHeaderData s))) ∧ ((∀
  j ∉
    @Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 310) (instOfNatNat (nat_lit 310)))
      (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 314) (instOfNatNat (nat_lit 314)))
        (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 316) (instOfNatNat (nat_lit 316)))
          (@Singleton.singleton.{0, 0} Nat (Finset.{0} Nat) (@Finset.instSingleton.{0} Nat)
            (@OfNat.ofNat.{0} Nat (nat_lit 336) (instOfNatNat (nat_lit 336)))))),
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.edgeHeader j) ∧ ((∀ (j : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.edgeHeader j) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)} {tentative : Fin i.n → Option.{0} Nat}
  {settled : Finset.{0} (Fin i.n)}
  {tree :
    DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled tree queue s →
    ∀ (e : Fin i.k),
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 308) (instOfNatNat (nat_lit 308))))
          (@DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.nodeAddress
            (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.layout i) i.k e) →
        And
          (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled tree queue
            (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.edgeHeaderData s))
          (And
            (@Eq.{1} Nat
              ((DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.edgeHeaderData s).natReg
                (@OfNat.ofNat.{0} Nat (nat_lit 310) (instOfNatNat (nat_lit 310))))
              (@Fin.val i.n (@DecrAlmostLinearSSSP.Decremental.Digraph.head i.n i.k i.graph e)))
            (@Eq.{1} Nat
              ((DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.edgeHeaderData s).natReg
                (@OfNat.ofNat.{0} Nat (nat_lit 316) (instOfNatNat (nat_lit 316))))
              (@ite.{1} Nat
                (@Membership.mem.{0, 0} (Fin i.k) (Finset.{0} (Fin i.k))
                  (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin i.k)) (Fin i.k) (@Finset.instSetLike.{0} (Fin i.k)))
                  (@DecrAlmostLinearSSSP.Decremental.live i.k deleted) e)
                (@Finset.decidableMem.{0} (Fin i.k) (instDecidableEqFin i.k) e
                  (@DecrAlmostLinearSSSP.Decremental.live i.k deleted))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))))) ∧ ((((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval
    (DecrAlmostLinearSSSP.Decremental.Structured.sequence
      (@List.map.{0, 0} DecrAlmostLinearSSSP.Decremental.Structured.Atom DecrAlmostLinearSSSP.Decremental.Structured.Cmd
        DecrAlmostLinearSSSP.Decremental.Structured.Cmd.atom
        DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.targetSettledAtoms))
    s (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.targetData s)) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval
    (DecrAlmostLinearSSSP.Decremental.Structured.sequence
      (@List.map.{0, 0} DecrAlmostLinearSSSP.Decremental.Structured.Atom DecrAlmostLinearSSSP.Decremental.Structured.Cmd
        DecrAlmostLinearSSSP.Decremental.Structured.Cmd.atom DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.nextAtoms))
    s (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
    (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.nextData s))) ∧ ((∀ (j : Nat),
  @Ne.{1} Nat j (@OfNat.ofNat.{0} Nat (nat_lit 318) (instOfNatNat (nat_lit 318))) →
    @Ne.{1} Nat j (@OfNat.ofNat.{0} Nat (nat_lit 320) (instOfNatNat (nat_lit 320))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
        (DecrAlmostLinearSSSP.Decremental.Structured.sequence
          (@List.map.{0, 0} DecrAlmostLinearSSSP.Decremental.Structured.Atom
            DecrAlmostLinearSSSP.Decremental.Structured.Cmd DecrAlmostLinearSSSP.Decremental.Structured.Cmd.atom
            DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.targetSettledAtoms))
        j) ∧ ((∀ (j : Nat),
  @Ne.{1} Nat j (@OfNat.ofNat.{0} Nat (nat_lit 308) (instOfNatNat (nat_lit 308))) →
    @Ne.{1} Nat j (@OfNat.ofNat.{0} Nat (nat_lit 336) (instOfNatNat (nat_lit 336))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
        (DecrAlmostLinearSSSP.Decremental.Structured.sequence
          (@List.map.{0, 0} DecrAlmostLinearSSSP.Decremental.Structured.Atom
            DecrAlmostLinearSSSP.Decremental.Structured.Cmd DecrAlmostLinearSSSP.Decremental.Structured.Cmd.atom
            DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.nextAtoms))
        j) ∧ (∀ (j : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
    (DecrAlmostLinearSSSP.Decremental.Structured.sequence
      (@List.map.{0, 0} DecrAlmostLinearSSSP.Decremental.Structured.Atom DecrAlmostLinearSSSP.Decremental.Structured.Cmd
        DecrAlmostLinearSSSP.Decremental.Structured.Cmd.atom
        DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.targetSettledAtoms))
    j)))) ∧ (((∀ (j : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
    (DecrAlmostLinearSSSP.Decremental.Structured.sequence
      (@List.map.{0, 0} DecrAlmostLinearSSSP.Decremental.Structured.Atom DecrAlmostLinearSSSP.Decremental.Structured.Cmd
        DecrAlmostLinearSSSP.Decremental.Structured.Cmd.atom DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.nextAtoms))
    j) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)} {tentative : Fin i.n → Option.{0} Nat}
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
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)} {tentative : Fin i.n → Option.{0} Nat}
  {settled : Finset.{0} (Fin i.n)}
  {tree :
    DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled tree queue s →
    ∀ (e : Fin i.k),
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 308) (instOfNatNat (nat_lit 308))))
          (@DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.nodeAddress
            (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.layout i) i.k e) →
        And
          (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled tree queue
            (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.nextData s))
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.nextData s).natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 308) (instOfNatNat (nat_lit 308))))
            (@DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.root
              (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.layout i) i.k
              (@DecrAlmostLinearSSSP.Decremental.Exact.adjacency i.n i.k i.graph (@Fin.val i.k e)
                (@DecrAlmostLinearSSSP.Decremental.Digraph.tail i.n i.k i.graph e))))) ∧ ((∀ (j : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 300) (instOfNatNat (nat_lit 300))) j →
    j ∉
        @Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 312) (instOfNatNat (nat_lit 312)))
          (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 316) (instOfNatNat (nat_lit 316)))
            (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 318) (instOfNatNat (nat_lit 318)))
              (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 320) (instOfNatNat (nat_lit 320)))
                (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 322) (instOfNatNat (nat_lit 322)))
                  (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 324) (instOfNatNat (nat_lit 324)))
                    (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 326) (instOfNatNat (nat_lit 326)))
                      (@Singleton.singleton.{0, 0} Nat (Finset.{0} Nat) (@Finset.instSingleton.{0} Nat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 336) (instOfNatNat (nat_lit 336)))))))))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.edgeGuard j) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)} {tentative : Fin i.n → Option.{0} Nat}
  {settled : Finset.{0} (Fin i.n)}
  {tree :
    DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled tree queue s →
    ∀ (e : Fin i.k) (key : Nat),
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 308) (instOfNatNat (nat_lit 308))))
          (@DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.nodeAddress
            (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.layout i) i.k e) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 310) (instOfNatNat (nat_lit 310))))
            (@Fin.val i.n (@DecrAlmostLinearSSSP.Decremental.Digraph.head i.n i.k i.graph e)) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 304) (instOfNatNat (nat_lit 304)))) key →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 316) (instOfNatNat (nat_lit 316))))
                (@ite.{1} Nat
                  (@Membership.mem.{0, 0} (Fin i.k) (Finset.{0} (Fin i.k))
                    (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin i.k)) (Fin i.k)
                      (@Finset.instSetLike.{0} (Fin i.k)))
                    (@DecrAlmostLinearSSSP.Decremental.live i.k deleted) e)
                  (@Finset.decidableMem.{0} (Fin i.k) (instDecidableEqFin i.k) e
                    (@DecrAlmostLinearSSSP.Decremental.live i.k deleted))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
              @LT.lt.{0} Nat instLTNat
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) key (i.weight e))
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
                      DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.edgeGuard s cost t)
                    (And
                      (@LE.le.{0} Nat instLENat cost
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64)))
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                      (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted
                        (@Prod.fst.{0, 0} (Fin i.n → Option.{0} Nat) (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))) r)
                        settled next
                        (@Prod.snd.{0, 0} (Fin i.n → Option.{0} Nat) (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))) r) t)))))))) ∧ (((((∀ {s u v t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {a b c : Nat},
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.edgeHeader s a u →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.edgeGuard u b v →
      DecrAlmostLinearSSSP.Decremental.Structured.Eval
          (DecrAlmostLinearSSSP.Decremental.Structured.sequence
            (@List.map.{0, 0} DecrAlmostLinearSSSP.Decremental.Structured.Atom
              DecrAlmostLinearSSSP.Decremental.Structured.Cmd DecrAlmostLinearSSSP.Decremental.Structured.Cmd.atom
              DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.nextAtoms))
          v c t →
        DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.edgeBody s
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a b) c)
          t) ∧ (∀ (j : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.edgeHeader j →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.edgeGuard j →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
          (DecrAlmostLinearSSSP.Decremental.Structured.sequence
            (@List.map.{0, 0} DecrAlmostLinearSSSP.Decremental.Structured.Atom
              DecrAlmostLinearSSSP.Decremental.Structured.Cmd DecrAlmostLinearSSSP.Decremental.Structured.Cmd.atom
              DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.nextAtoms))
          j →
        DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.edgeBody j)) ∧ ((DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.edgeBody
  (@OfNat.ofNat.{0} Nat (nat_lit 304) (instOfNatNat (nat_lit 304)))) ∧ (DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.edgeBody
  (@OfNat.ofNat.{0} Nat (nat_lit 306) (instOfNatNat (nat_lit 306)))))) ∧ (((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)} {tentative : Fin i.n → Option.{0} Nat}
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
                          (@DecrAlmostLinearSSSP.Decremental.Digraph.tail i.n i.k i.graph e))))))) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {l : DecrAlmostLinearSSSP.Decremental.Exact.Layout.Addresses}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.StaticImage i l s →
    DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.StaticImage i l t →
      ∀ (es : List.{0} (Fin i.k)),
        @DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.Chain i.k l s es →
          @DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.Chain i.k l t es)) ∧ ((∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {w : Fin k → Nat}
  {source v : Fin n} {key : Nat} {settled : Finset.{0} (Fin n)} {scanned : List.{0} (Fin k)}
  {tentative : Fin n → Option.{0} Nat} {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin n))},
  @DecrAlmostLinearSSSP.Decremental.Exact.ScanState n k g active w source v key settled scanned tentative queue →
    ∀ (e : Fin k),
      @Eq.{1} (Fin n) (@DecrAlmostLinearSSSP.Decremental.Digraph.tail n k g e) v →
        have result := @DecrAlmostLinearSSSP.Decremental.Exact.relax n k g active w settled key e tentative queue;
        And
          (@DecrAlmostLinearSSSP.Decremental.Exact.ScanState n k g active w source v key settled
            (@List.cons.{0} (Fin k) e scanned)
            (@Prod.fst.{0, 0} (Fin n → Option.{0} Nat) (Multiset.{0} (Prod.{0, 0} Nat (Fin n))) result)
            (@Prod.snd.{0, 0} (Fin n → Option.{0} Nat) (Multiset.{0} (Prod.{0, 0} Nat (Fin n))) result))
          (@LE.le.{0} Nat instLENat
            (@Multiset.card.{0} (Prod.{0, 0} Nat (Fin n))
              (@Prod.snd.{0, 0} (Fin n → Option.{0} Nat) (Multiset.{0} (Prod.{0, 0} Nat (Fin n))) result))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@Multiset.card.{0} (Prod.{0, 0} Nat (Fin n)) queue)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) ∧ ((∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {w : Fin k → Nat}
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
              (@Multiset.card.{0} (Prod.{0, 0} Nat (Fin n)) queue) (@List.length.{0} (Fin k) es)))) ∧ (∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {w : Fin k → Nat}
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
              (@List.length.{0} (Fin k) (@DecrAlmostLinearSSSP.Decremental.Exact.adjacency n k g k v))))))))) ∧ ((((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)} {tentative : Fin i.n → Option.{0} Nat}
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
                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval
    (DecrAlmostLinearSSSP.Decremental.Structured.sequence
      (@List.map.{0, 0} DecrAlmostLinearSSSP.Decremental.Structured.Atom DecrAlmostLinearSSSP.Decremental.Structured.Cmd
        DecrAlmostLinearSSSP.Decremental.Structured.Cmd.atom
        DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.settleAtoms))
    s (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.settledData s))) ∧ ((∀ (j : Nat),
  @Ne.{1} Nat j (@OfNat.ofNat.{0} Nat (nat_lit 318) (instOfNatNat (nat_lit 318))) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
      (DecrAlmostLinearSSSP.Decremental.Structured.sequence
        (@List.map.{0, 0} DecrAlmostLinearSSSP.Decremental.Structured.Atom
          DecrAlmostLinearSSSP.Decremental.Structured.Cmd DecrAlmostLinearSSSP.Decremental.Structured.Cmd.atom
          DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.settleAtoms))
      j) ∧ ((∀ (j : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
    (DecrAlmostLinearSSSP.Decremental.Structured.sequence
      (@List.map.{0, 0} DecrAlmostLinearSSSP.Decremental.Structured.Atom DecrAlmostLinearSSSP.Decremental.Structured.Cmd
        DecrAlmostLinearSSSP.Decremental.Structured.Cmd.atom
        DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.settleAtoms))
    j) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)} {tentative : Fin i.n → Option.{0} Nat}
  {settled : Finset.{0} (Fin i.n)}
  {tree :
    DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled tree queue s →
    ∀ (v : Fin i.n),
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 306) (instOfNatNat (nat_lit 306)))) (@Fin.val i.n v) →
        DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative
          (@Insert.insert.{0, 0} (Fin i.n) (Finset.{0} (Fin i.n))
            (@Finset.instInsert.{0} (Fin i.n) (instDecidableEqFin i.n)) v settled)
          tree queue (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.settledData s))))) ∧ (((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval
    (DecrAlmostLinearSSSP.Decremental.Structured.sequence
      (@List.map.{0, 0} DecrAlmostLinearSSSP.Decremental.Structured.Atom DecrAlmostLinearSSSP.Decremental.Structured.Cmd
        DecrAlmostLinearSSSP.Decremental.Structured.Cmd.atom
        DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.scanPrepareAtoms))
    s (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.scanPrepared s)) ∧ (∀ (j : Nat),
  @Ne.{1} Nat j (@OfNat.ofNat.{0} Nat (nat_lit 308) (instOfNatNat (nat_lit 308))) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
      (DecrAlmostLinearSSSP.Decremental.Structured.sequence
        (@List.map.{0, 0} DecrAlmostLinearSSSP.Decremental.Structured.Atom
          DecrAlmostLinearSSSP.Decremental.Structured.Cmd DecrAlmostLinearSSSP.Decremental.Structured.Cmd.atom
          DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.scanPrepareAtoms))
      j)) ∧ ((∀ (j : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
    (DecrAlmostLinearSSSP.Decremental.Structured.sequence
      (@List.map.{0, 0} DecrAlmostLinearSSSP.Decremental.Structured.Atom DecrAlmostLinearSSSP.Decremental.Structured.Cmd
        DecrAlmostLinearSSSP.Decremental.Structured.Cmd.atom
        DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.scanPrepareAtoms))
    j) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)} {tentative : Fin i.n → Option.{0} Nat}
  {settled : Finset.{0} (Fin i.n)}
  {tree :
    DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled tree queue s →
    ∀ (v : Fin i.n),
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 306) (instOfNatNat (nat_lit 306)))) (@Fin.val i.n v) →
        And
          (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled tree queue
            (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.scanPrepared s))
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.scanPrepared s).natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 308) (instOfNatNat (nat_lit 308))))
            (@DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.root
              (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.layout i) i.k
              (@DecrAlmostLinearSSSP.Decremental.Exact.adjacency i.n i.k i.graph i.k v)))) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)} {tentative : Fin i.n → Option.{0} Nat}
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
                    next (@Prod.snd.{0, 0} (Fin i.n → Option.{0} Nat) (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))) r) t)))))))))) := by
  exact ⟨⟨⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.Heap.Image.powers_not,DecrAlmostLinearSSSP.Decremental.Exact.Heap.Image.count⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.Heap.Image.push,DecrAlmostLinearSSSP.Decremental.Exact.Heap.Image.pop⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.public_below,DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.settled_below⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.distance_below,⟨DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.active_below,DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.graph_below⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory.heap_replace,DecrAlmostLinearSSSP.Decremental.Exact.Heap.Image.frame⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory.register_frame,DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.queueCount_eval⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.queueCount_nat_frame,DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.queueCount_real_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory.queueCount,⟨DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.candidatePrefix_eval,DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.candidatePrefix_nat_frame⟩⟩⟩⟩⟩,⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.candidatePrefix_real_frame,DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory.candidatePrefix⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.Heap.Image.below_frame,DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.improvePrefix_eval⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.improvePrefix_fields,DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.improvePrefix_nat_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.improvePrefix_real_frame,⟨DecrAlmostLinearSSSP.Decremental.Exact.TentativeImage.update,DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory.improvePrefix⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory.push,DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory.pop⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.improve_nat_frame,⟨DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.improve_real_frame,DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory.improve⟩⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.LabelInvariant.relax_edge,DecrAlmostLinearSSSP.Decremental.Exact.LabelInvariant.settled_edge_bound⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.improves_iff,⟨DecrAlmostLinearSSSP.Decremental.Exact.not_improves,DecrAlmostLinearSSSP.Decremental.Exact.LabelInvariant.skip_settled⟩⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.scan_initial,DecrAlmostLinearSSSP.Decremental.Exact.scan_finished⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory.candidate,DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.candidate_nat_frame⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.candidate_real_frame,DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.edgeHeader_eval⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.edgeHeader_nat_frame,⟨DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.edgeHeader_real_frame,DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory.edgeHeader⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.target_eval,DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.next_eval⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.target_nat_frame,⟨DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.next_nat_frame,DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.target_real_frame⟩⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.next_real_frame,DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory.target⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory.advanceNext,⟨DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.edgeGuard_nat_frame,DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory.edgeGuard⟩⟩⟩⟩⟩,⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.edgeBody_append,DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.edgeBody_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.edgeBody_key_frame,DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.edgeBody_vertex_frame⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory.edgeBody,DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.Chain.graph_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.ScanState.relax,⟨DecrAlmostLinearSSSP.Decremental.Exact.ScanState.scan,DecrAlmostLinearSSSP.Decremental.Exact.scan_outgoing⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory.edgeLoop,DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.settle_eval⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.settle_nat_frame,⟨DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.settle_real_frame,DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory.settle⟩⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.scanPrepare_eval,DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.scanPrepare_nat_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.scanPrepare_real_frame,⟨DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory.scanPrepare,DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory.scan⟩⟩⟩⟩⟩⟩⟩
