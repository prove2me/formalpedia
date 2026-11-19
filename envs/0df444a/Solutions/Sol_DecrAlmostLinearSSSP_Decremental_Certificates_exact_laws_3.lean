-- Prove2me | solution 1 for DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_3
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T11:14:37.43445+00:00
-- url     : https://prove2.me/submissions/2ee59b36-689b-4e8d-bbda-cdb14bf66969

import Definitions.Def_DecrAlmostLinearSSSP_RAMFoundation
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_1
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_2
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
open scoped ENNReal NNReal
attribute [local instance] Classical.propDecidable
theorem DecrAlmostLinearSSSP.Decremental.RadixQueue.count_insert : ∀ (height key value : Nat) (t : DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height),
  @Eq.{1} Nat
    (@DecrAlmostLinearSSSP.Decremental.RadixQueue.count height
      (DecrAlmostLinearSSSP.Decremental.RadixQueue.insert height key value t))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@DecrAlmostLinearSSSP.Decremental.RadixQueue.count height t)
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_1.1.1.1.1.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root_nonzero : ∀ {height : Nat} (tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie height),
  @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Separated height tree →
    Iff
      (@Ne.{1} Nat (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root height tree)
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@Ne.{1} (DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie height) tree
        (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.empty height)) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.1.1.2.1.2.2
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
theorem DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.leaf_field_mem : ∀ (address : Nat) (items : List.{0} (Prod.{0, 0} Nat Nat)) (offset : Nat),
  @LT.lt.{0} Nat instLTNat offset (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.leaf address items))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) address offset) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.1.2.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.leaf_payload_subset : ∀ (address : Nat) (items : List.{0} (Prod.{0, 0} Nat Nat)),
  @LE.le.{0} (Finset.{0} Nat)
    (@Preorder.toLE.{0} (Finset.{0} Nat)
      (@PartialOrder.toPreorder.{0} (Finset.{0} Nat) (@Finset.instPartialOrder.{0} Nat)))
    (DecrAlmostLinearSSSP.Decremental.Exact.Payload.footprint items)
    (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.leaf address items)) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.1.2.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.disjoint_fresh_interval : ∀ (old : Finset.{0} Nat) (fresh length : Nat),
  (∀ (address : Nat),
      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) old address →
        @LT.lt.{0} Nat instLTNat address fresh) →
    @Disjoint.{0} (Finset.{0} Nat) (@Finset.instPartialOrder.{0} Nat) (@Finset.instOrderBot.{0} Nat) old
      (@Finset.Ico.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder fresh
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) fresh length)) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.1.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Structured.CodeAt.left : ∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {start : Nat}
  {a b : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction},
  DecrAlmostLinearSSSP.Decremental.Structured.CodeAt p start
      (@HAppend.hAppend.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (@instHAppendOfAppend.{0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (@List.instAppend.{0} DecrAlmostLinearSSSP.Decremental.Instruction))
        a b) →
    DecrAlmostLinearSSSP.Decremental.Structured.CodeAt p start a := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.1.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Structured.CodeAt.right : ∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {start : Nat}
  {a b : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction},
  DecrAlmostLinearSSSP.Decremental.Structured.CodeAt p start
      (@HAppend.hAppend.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (@instHAppendOfAppend.{0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (@List.instAppend.{0} DecrAlmostLinearSSSP.Decremental.Instruction))
        a b) →
    DecrAlmostLinearSSSP.Decremental.Structured.CodeAt p
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start
        (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction a))
      b := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.1.2.1.2.2.2.2
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
theorem DecrAlmostLinearSSSP.Decremental.Exact.Allocate.node_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.Allocate.node s
    (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))
    (DecrAlmostLinearSSSP.Decremental.Exact.Allocate.nodeData s) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.2.2.1.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.Allocate.node_values : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      And
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.Exact.Allocate.nodeData s).natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 272) (instOfNatNat (nat_lit 272))))
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))))
        (And
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.Exact.Allocate.nodeData s).natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
          (And
            (DecrAlmostLinearSSSP.Decremental.Exact.Allocate.NodeImage
              (DecrAlmostLinearSSSP.Decremental.Exact.Allocate.nodeData s)
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))
              { count := @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)),
                left := @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)),
                right := @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)),
                payload := @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)) })
            (And (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.Exact.Allocate.nodeData s).realMem s.realMem)
              (∀ (address : Nat),
                Or
                    (@LT.lt.{0} Nat instLTNat address
                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))))
                    (@LE.le.{0} Nat instLENat
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                      address) →
                  @Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.Exact.Allocate.nodeData s).natMem address)
                    (s.natMem address))))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.2.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.Allocate.node_nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 272) (instOfNatNat (nat_lit 272))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 274) (instOfNatNat (nat_lit 274))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))) →
        DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.Allocate.node k := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.2.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.Allocate.node_real_frame : ∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Exact.Allocate.node k := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.Allocate.item_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.Allocate.item s
    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
    (DecrAlmostLinearSSSP.Decremental.Exact.Allocate.itemData s) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.2.2.2.2.2.1
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
lemma item_nat_frame (k : ℕ) (h272 : k ≠ 272) (h274 : k ≠ 274) (h244 : k ≠ 244) : NatFrame item k := by
  simp [item,itemAtoms,Structured.sequence,NatFrame,writesNat,Ne.symm h272,Ne.symm h274,Ne.symm h244]
lemma item_real_frame (k : ℕ) : RealFrame item k := by simp [item,itemAtoms,Structured.sequence,RealFrame,writesReal]
end DecrAlmostLinearSSSP.Decremental.Exact.Allocate
end s30
section s31
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePush
open Structured
lemma ensureNode_eval (s : Data) (hz : s.natReg 56 = 0) (h1 : s.natReg 26 = 1)
    (hslot : s.natReg 278 < s.natReg 244) :
    ∃ cost t, Eval ensureNode s cost t ∧ cost ≤ 14 ∧
      t.natReg 264 = (if s.natMem (s.natReg 278) = 0 then s.natReg 244 else s.natMem (s.natReg 278)) ∧
      t.natReg 244 = (if s.natMem (s.natReg 278) = 0 then s.natReg 244+4 else s.natReg 244) ∧
      t.natMem (s.natReg 278) = t.natReg 264 ∧ t.realMem = s.realMem ∧
      (s.natMem (s.natReg 278) = 0 → Allocate.NodeImage t (s.natReg 244) ⟨0,0,0,0⟩) ∧
      (∀ address, address ≠ s.natReg 278 → (address < s.natReg 244 ∨ s.natReg 244+4 ≤ address) →
        t.natMem address = s.natMem address) := by
  let u : Data := {s with natReg := Function.update s.natReg 264 (s.natMem (s.natReg 278))}
  have hu : Eval (loadN 264 278) s 1 u := eval_loadN s 264 278
  by_cases hzero : s.natMem (s.natReg 278) = 0
  · have htest : (Test.natLess 264 26).holds u := by simp [Test.holds,u,hzero,h1]
    let w := Allocate.nodeData u
    have hw := Allocate.node_eval u
    obtain ⟨hw272,hw244,hwNode,hwr,hwFrame⟩ := Allocate.node_values u hz (by simpa [u] using h1)
    have hw278 : w.natReg 278 = s.natReg 278 := (hw.nat_frame (Allocate.node_nat_frame 278 (by omega) (by omega) (by omega))).trans (by simp [u])
    have hw56 : w.natReg 56 = 0 := (hw.nat_frame (Allocate.node_nat_frame 56 (by omega) (by omega) (by omega))).trans hz
    have hw272' : w.natReg 272 = s.natReg 244 := by simpa [u] using hw272
    let x : Data := {w with natMem := Function.update w.natMem (w.natReg 278) (w.natReg 272)}
    have hx : Eval (storeN 278 272) w 1 x := eval_storeN w 278 272
    let t : Data := {x with natReg := Function.update x.natReg 264 (x.natReg 272+x.natReg 56)}
    have ht : Eval (nadd 264 272 56) x 1 t := eval_nadd x 264 272 56
    have ht264 : t.natReg 264 = s.natReg 244 := by simp [t,x,hw272',hw56]
    refine ⟨14,t,Eval.seq hu (Eval.branchYes htest (Eval.seq hw (Eval.seq hx ht))),le_rfl,?_,?_,?_,hwr,?_,?_⟩
    · simpa only [if_pos hzero] using ht264
    · simpa [t,x,u,if_pos hzero] using hw244
    · simp only [t,x,hw278,hw272',Function.update_self,hw56,Nat.add_zero]
    · intro hz'
      rcases hwNode with ⟨hn0,hn1,hn2,hn3⟩
      unfold Allocate.NodeImage at *
      change Function.update w.natMem (w.natReg 278) (w.natReg 272) (s.natReg 244) = 0 ∧
        Function.update w.natMem (w.natReg 278) (w.natReg 272) (s.natReg 244+1) = 0 ∧
        Function.update w.natMem (w.natReg 278) (w.natReg 272) (s.natReg 244+2) = 0 ∧
        Function.update w.natMem (w.natReg 278) (w.natReg 272) (s.natReg 244+3) = 0
      rw [hw278]
      simp only [Function.update_of_ne (show s.natReg 244 ≠ s.natReg 278 by omega),
        Function.update_of_ne (show s.natReg 244+1 ≠ s.natReg 278 by omega),
        Function.update_of_ne (show s.natReg 244+2 ≠ s.natReg 278 by omega),
        Function.update_of_ne (show s.natReg 244+3 ≠ s.natReg 278 by omega)]
      exact ⟨hn0,hn1,hn2,hn3⟩
    · intro address hne ha
      change Function.update w.natMem (w.natReg 278) (w.natReg 272) address = _
      rw [hw278,Function.update_of_ne hne]
      exact hwFrame address ha
  · have htest : ¬(Test.natLess 264 26).holds u := by simp [Test.holds,u,h1];omega
    refine ⟨3,u,Eval.seq hu (Eval.branchNo htest (Eval.skip u)),by omega,?_,?_,?_,rfl,?_,fun _ _ _ => rfl⟩
    · simp [u,hzero]
    · simp [u,hzero]
    · simp [u]
    · intro hh;contradiction
end DecrAlmostLinearSSSP.Decremental.Exact.TriePush
end s31
section s32
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact
open Structured
lemma LocatedTrie.materialize_root_empty (height fresh : ℕ) :
    ((LocatedTrie.empty (height := height)).materialize fresh).root = fresh := by cases height <;> rfl
lemma LocatedTrie.materialize_nonempty {height : ℕ} (tree : LocatedTrie height) (fresh : ℕ) (h : tree ≠ .empty) :
    tree.materialize fresh = tree := by cases tree <;> first | contradiction | rfl
lemma LocatedTrie.materialize_insert {height : ℕ} (tree : LocatedTrie height) (fresh key value : ℕ) :
    RadixQueue.insert height key value (tree.materialize fresh).abstract = RadixQueue.insert height key value tree.abstract := by
  cases height with
  | zero => cases tree <;> simp [LocatedTrie.materialize,LocatedTrie.abstract,RadixQueue.insert]
  | succ height => cases tree <;> simp [LocatedTrie.materialize,LocatedTrie.abstract,RadixQueue.insert]
lemma LocatedTrie.materialize_empty_image {s : Data} (height fresh : ℕ)
    (h : Allocate.NodeImage s fresh ⟨0,0,0,0⟩) : ((LocatedTrie.empty (height := height)).materialize fresh).Image s := by
  cases height
  · exact ⟨h.1,h.2.2.2,trivial⟩
  · exact ⟨by simpa only [LocatedTrie.abstract,RadixQueue.count,Nat.add_zero] using h.1,h.2.1,h.2.2.1,trivial,trivial⟩
lemma LocatedTrie.materialize_empty_separated (height fresh : ℕ) (h : 0 < fresh) :
    ((LocatedTrie.empty (height := height)).materialize fresh).Separated := by
  cases height <;> simp [LocatedTrie.materialize,LocatedTrie.Separated,LocatedTrie.footprint,Payload.footprint,Payload.Separated,h]
lemma LocatedTrie.materialize_empty_footprint (height fresh : ℕ) :
    ((LocatedTrie.empty (height := height)).materialize fresh).footprint = Finset.Ico fresh (fresh+4) := by
  cases height <;> simp [LocatedTrie.materialize,LocatedTrie.footprint,Payload.footprint]
namespace TriePush
lemma ensureNode_existing (s : Data) (h1 : s.natReg 26 = 1) (hroot : s.natMem (s.natReg 278) ≠ 0) :
    Eval ensureNode s 3 (loaded s) := by
  have ht : ¬(Test.natLess 264 26).holds (loaded s) := by simp [Test.holds,loaded,h1];omega
  exact Eval.seq (eval_loadN s 264 278) (Eval.branchNo ht (Eval.skip _))
end TriePush
end DecrAlmostLinearSSSP.Decremental.Exact
end s32
section s33
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePush
open Structured
lemma ensureNode_nat_frame (k : ℕ) (h264 : k ≠ 264) (h272 : k ≠ 272) (h274 : k ≠ 274) (h244 : k ≠ 244) :
    NatFrame ensureNode k :=
  ⟨Ne.symm h264,⟨Allocate.node_nat_frame k h272 h274 h244,not_false,Ne.symm h264⟩,trivial⟩
lemma ensureNode_real_frame (k : ℕ) : RealFrame ensureNode k :=
  ⟨not_false,⟨Allocate.node_real_frame k,not_false,not_false⟩,trivial⟩
lemma ensureNode_located {height : ℕ} (tree : LocatedTrie height) (low : ℕ) (s : Data)
    (hzero : s.natReg 56 = 0) (h1 : s.natReg 26 = 1)
    (himage : tree.Image s) (hsep : tree.Separated) (hbound : tree.Bounded low (s.natReg 244))
    (hslot : s.natMem (s.natReg 278) = tree.root)
    (hslotLow : low ≤ s.natReg 278) (hslotHigh : s.natReg 278 < s.natReg 244) :
    ∃ cost t, Eval ensureNode s cost t ∧ cost ≤ 14 ∧
      t.natReg 264 = (tree.materialize (s.natReg 244)).root ∧
      t.natReg 244 = (if tree.root = 0 then s.natReg 244+4 else s.natReg 244) ∧
      t.natMem (s.natReg 278) = (tree.materialize (s.natReg 244)).root ∧
      (tree.materialize (s.natReg 244)).Image t ∧ (tree.materialize (s.natReg 244)).Separated ∧
      (tree.materialize (s.natReg 244)).Bounded low (t.natReg 244) ∧
      (tree.materialize (s.natReg 244)).footprint ⊆ tree.footprint ∪ Finset.Ico (s.natReg 244) (t.natReg 244) ∧
      t.realMem = s.realMem ∧
      (∀ address, address ≠ s.natReg 278 → (address < s.natReg 244 ∨ t.natReg 244 ≤ address) →
        t.natMem address = s.natMem address) := by
  classical
  by_cases hroot : tree.root = 0
  · have hempty : tree = .empty := by
      by_contra hne
      exact ((LocatedTrie.root_nonzero tree hsep).mpr hne) hroot
    subst tree
    have hmemzero : s.natMem (s.natReg 278) = 0 := hslot
    obtain ⟨cost,t,he,hcost,ht264,ht244,htslot,htr,htNode,htframe⟩ := ensureNode_eval s hzero h1 hslotHigh
    have htptr : t.natReg 264 = s.natReg 244 := by simpa only [if_pos hmemzero] using ht264
    have htalloc : t.natReg 244 = s.natReg 244+4 := by simpa only [if_pos hmemzero] using ht244
    have hmatroot := LocatedTrie.materialize_root_empty height (s.natReg 244)
    refine ⟨cost,t,he,hcost,?_,?_,?_,?_,?_,?_,?_,htr,?_⟩
    · rwa [hmatroot]
    · simpa [LocatedTrie.root] using htalloc
    · rw [hmatroot];exact htslot.trans htptr
    · exact LocatedTrie.materialize_empty_image height _ (htNode hmemzero)
    · exact LocatedTrie.materialize_empty_separated height _ (by omega)
    · intro address ha
      rw [LocatedTrie.materialize_empty_footprint] at ha
      have hh := Finset.mem_Ico.mp ha
      rw [htalloc]
      constructor <;> omega
    · intro address ha
      rw [LocatedTrie.materialize_empty_footprint] at ha
      exact Finset.mem_union_right _ (by simpa only [htalloc] using ha)
    · intro address hne ha
      exact htframe address hne (by rwa [htalloc] at ha)
  · have hne : tree ≠ .empty := (LocatedTrie.root_nonzero tree hsep).mp hroot
    have hmaterialize := LocatedTrie.materialize_nonempty tree (s.natReg 244) hne
    let t := loaded s
    have he := ensureNode_existing s h1 (by rwa [hslot])
    refine ⟨3,t,he,by omega,?_,?_,?_,?_,?_,?_,?_,rfl,fun _ _ _ => rfl⟩
    · simp only [t,loaded,Function.update_self,hslot,hmaterialize]
    · simp only [t,loaded,Function.update_of_ne (by decide : (244 : ℕ) ≠ 264),if_neg hroot]
    · simpa only [t,loaded,hmaterialize] using hslot
    · rw [hmaterialize];exact himage.frame (fun _ _ => rfl)
    · rwa [hmaterialize]
    · rw [hmaterialize];exact hbound
    · rw [hmaterialize];exact Finset.subset_union_left
end DecrAlmostLinearSSSP.Decremental.Exact.TriePush
end s33
section s34
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePush
open Structured
lemma increment_eval (s : Data) : Eval increment s 3 (incremented s) := eval_sequence_atoms incrementAtoms s
lemma increment_fields (s : Data) (h1 : s.natReg 26 = 1) :
    (incremented s).natMem = Function.update s.natMem (s.natReg 264) (s.natMem (s.natReg 264)+1) ∧
      (incremented s).natReg 266 = s.natMem (s.natReg 264)+1 := by
  simp [incremented,incrementAtoms,Atom.effect,instructionEffect,data,Data.machine,h1]
lemma leafPrepare_eval (s : Data) : Eval leafPrepare s 3 (leafPrepared s) := eval_sequence_atoms leafAtoms s
lemma leafPrepare_fields (s : Data) : (leafPrepared s).natReg 280 = s.natReg 264+3 ∧
    (leafPrepared s).natReg 276 = s.natMem (s.natReg 264+3) := by
  simp [leafPrepared,leafAtoms,Atom.effect,instructionEffect,data,Data.machine]
lemma start_eval (s : Data) : Eval start s 3 (started s) := eval_sequence_atoms startAtoms s
lemma start_fields (s : Data) (hz : s.natReg 56 = 0) :
    (started s).natReg 256 = s.natReg 236 ∧ (started s).natReg 258 = s.natReg 238 ∧
      (started s).natReg 278 = s.natReg 246 := by
  simp [started,startAtoms,Atom.effect,instructionEffect,data,Data.machine,hz]
end DecrAlmostLinearSSSP.Decremental.Exact.TriePush
end s34
section s35
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePush
open Structured
lemma leafFinish_eval (s : Data) : Eval leafFinish s 12 (leafFinished s) :=
  Eval.seq (increment_eval s) (Eval.seq (leafPrepare_eval _) (Eval.seq (Allocate.item_eval _) (eval_storeN _ 280 272)))
lemma leafFinish_values (s : Data) (address count head : ℕ) (hz : s.natReg 56 = 0) (h1 : s.natReg 26 = 1)
    (hptr : s.natReg 264 = address) (hcount : s.natMem address = count) (hhead : s.natMem (address+3) = head) :
    (leafFinished s).natReg 244 = s.natReg 244+2 ∧
      (leafFinished s).natMem = Function.update (Function.update (Function.update
        (Function.update s.natMem address (count+1)) (s.natReg 244) (s.natReg 262))
        (s.natReg 244+1) head) (address+3) (s.natReg 244) ∧
      (leafFinished s).realMem = s.realMem := by
  simp [leafFinished,incremented,incrementAtoms,leafPrepared,leafAtoms,Allocate.itemData,Allocate.itemAtoms,
    Atom.effect,instructionEffect,data,Data.machine,hz,h1,hptr,hcount,hhead]
lemma leafFinish_nat_frame (k : ℕ) (h266 : k ≠ 266) (h282 : k ≠ 282) (h280 : k ≠ 280)
    (h276 : k ≠ 276) (h272 : k ≠ 272) (h274 : k ≠ 274) (h244 : k ≠ 244) : NatFrame leafFinish k := by
  refine ⟨?_,?_,Allocate.item_nat_frame k h272 h274 h244,not_false⟩
  · simp [increment,incrementAtoms,Structured.sequence,NatFrame,writesNat,Ne.symm h266]
  · simp [leafPrepare,leafAtoms,Structured.sequence,NatFrame,writesNat,Ne.symm h282,Ne.symm h280,Ne.symm h276]
end DecrAlmostLinearSSSP.Decremental.Exact.TriePush
end s35
section s36
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePush
open Structured
lemma leafFinish_image (address : ℕ) (items : List (ℕ × ℕ)) (low : ℕ) (s : Data)
    (hz : s.natReg 56 = 0) (h1 : s.natReg 26 = 1) (hptr : s.natReg 264 = address)
    (hi : (LocatedTrie.leaf address items).Image s) (hs : (LocatedTrie.leaf address items).Separated)
    (hb : (LocatedTrie.leaf address items).Bounded low (s.natReg 244)) :
    let next := LocatedTrie.leaf address ((s.natReg 244,s.natReg 262)::items)
    next.Image (leafFinished s) ∧ next.Separated ∧ next.Bounded low ((leafFinished s).natReg 244) ∧
      next.abstract = RadixQueue.insert 0 0 (s.natReg 262) (LocatedTrie.leaf address items).abstract ∧
      next.footprint ⊆ (LocatedTrie.leaf address items).footprint ∪ Finset.Ico (s.natReg 244) ((leafFinished s).natReg 244) ∧
      (∀ a, a ∉ (LocatedTrie.leaf address items).footprint →
        (a < s.natReg 244 ∨ (leafFinished s).natReg 244 ≤ a) → (leafFinished s).natMem a = s.natMem a) := by
  let fresh := s.natReg 244
  let t := leafFinished s
  let next := LocatedTrie.leaf address ((fresh,s.natReg 262)::items)
  obtain ⟨htalloc,htmem,_⟩ := leafFinish_values s address items.length (Payload.root items) hz h1 hptr hi.1 hi.2.1
  change t.natReg 244 = fresh+2 at htalloc
  change t.natMem = Function.update (Function.update (Function.update
    (Function.update s.natMem address (items.length+1)) fresh (s.natReg 262))
    (fresh+1) (Payload.root items)) (address+3) fresh at htmem
  have hnode (r : ℕ) (hr : r < 4) : low ≤ address+r ∧ address+r < fresh := hb _ (LocatedTrie.leaf_field_mem address items r hr)
  have h0 := hnode 0 (by omega)
  have h3 := hnode 3 (by omega)
  have hpBound (a : ℕ) (ha : a ∈ Payload.footprint items) : low ≤ a ∧ a < fresh :=
    hb a (LocatedTrie.leaf_payload_subset address items ha)
  have hpNot (a : ℕ) (ha : a ∈ Payload.footprint items) (r : ℕ) (hr : r < 4) : a ≠ address+r := by
    intro heq
    exact Finset.disjoint_left.mp hs.2.1 (Finset.mem_Ico.mpr ⟨by omega,by omega⟩) (heq ▸ ha)
  have hpFrame : ∀ a ∈ Payload.footprint items, t.natMem a = s.natMem a := by
    intro a ha
    have hab := (hpBound a ha).2
    have han0 : a ≠ address := by simpa only [Nat.add_zero] using hpNot a ha 0 (by omega)
    have han3 := hpNot a ha 3 (by omega)
    rw [htmem,Function.update_of_ne han3,Function.update_of_ne (show a ≠ fresh+1 by omega),
      Function.update_of_ne (show a ≠ fresh by omega),Function.update_of_ne han0]
  have htImage : next.Image t := by
    refine ⟨?_,?_,?_,?_,hi.2.2.frame hpFrame⟩
    · rw [htmem]
      simp only [Function.update_of_ne (show address ≠ address+3 by omega),
        Function.update_of_ne (show address ≠ fresh+1 by omega),Function.update_of_ne (show address ≠ fresh by omega),Function.update_self,List.length_cons]
    · rw [htmem,Function.update_self];rfl
    · rw [htmem,Function.update_of_ne (show fresh ≠ address+3 by omega),
        Function.update_of_ne (show fresh ≠ fresh+1 by omega),Function.update_self]
    · rw [htmem,Function.update_of_ne (show fresh+1 ≠ address+3 by omega),Function.update_self]
  have htSep : next.Separated := by
    refine ⟨hs.1,?_,?_,?_,hs.2.2⟩
    · apply Finset.disjoint_union_right.mpr
      constructor
      · exact disjoint_fresh_interval _ fresh 2 (by intro a ha;exact (hb _ (Finset.mem_union_left _ ha)).2)
      · exact hs.2.1
    · omega
    · exact (disjoint_fresh_interval (Payload.footprint items) fresh 2 (by intro a ha;exact (hpBound a ha).2)).symm
  have htBound : next.Bounded low (t.natReg 244) := by
    intro a ha
    rw [htalloc]
    simp only [next,LocatedTrie.footprint,Payload.footprint,Finset.mem_union] at ha
    rcases ha with ha | ha | ha
    · have hh := hb a (Finset.mem_union_left _ ha)
      constructor <;> omega
    · have hh := Finset.mem_Ico.mp ha
      constructor <;> omega
    · have hh := hpBound a ha
      constructor <;> omega
  have htFoot : next.footprint ⊆ (LocatedTrie.leaf address items).footprint ∪ Finset.Ico fresh (t.natReg 244) := by
    rw [htalloc]
    intro a ha
    simp only [next,LocatedTrie.footprint,Payload.footprint,Finset.mem_union] at ha ⊢
    tauto
  refine ⟨htImage,htSep,htBound,rfl,htFoot,?_⟩
  intro a ha hout
  have hn0 : a ≠ address := by intro hh;exact ha (by rw [hh];simpa only [Nat.add_zero] using LocatedTrie.leaf_field_mem address items 0 (by omega))
  have hn3 : a ≠ address+3 := by intro hh;exact ha (by rw [hh];exact LocatedTrie.leaf_field_mem address items 3 (by omega))
  rw [htalloc] at hout
  rw [htmem,Function.update_of_ne hn3,Function.update_of_ne (show a ≠ fresh+1 by omega),
    Function.update_of_ne (show a ≠ fresh by omega),Function.update_of_ne hn0]
end DecrAlmostLinearSSSP.Decremental.Exact.TriePush
end s36
section s37
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePush
open Structured
lemma core_zero (tree : LocatedTrie 0) (low : ℕ) (s : Data)
    (hz : s.natReg 56 = 0) (h1 : s.natReg 26 = 1) (hheight : s.natReg 256 = 0)
    (hi : tree.Image s) (hs : tree.Separated) (hb : tree.Bounded low (s.natReg 244))
    (hslot : s.natMem (s.natReg 278) = tree.root) (hslotLow : low ≤ s.natReg 278)
    (hslotHigh : s.natReg 278 < s.natReg 244) (hslotNot : s.natReg 278 ∉ tree.footprint) :
    ∃ (cost : ℕ) (t : Data) (next : LocatedTrie 0), Eval core s cost t ∧ cost ≤ 40 ∧
      t.natMem (s.natReg 278) = next.root ∧ next.Image t ∧ next.Separated ∧ next.Bounded low (t.natReg 244) ∧
      next.abstract = RadixQueue.insert 0 (s.natReg 260) (s.natReg 262) tree.abstract ∧
      s.natReg 244 ≤ t.natReg 244 ∧
      next.footprint ⊆ tree.footprint ∪ Finset.Ico (s.natReg 244) (t.natReg 244) ∧
      t.realMem = s.realMem ∧
      (∀ address, address ≠ s.natReg 278 → address ∉ tree.footprint →
        (address < s.natReg 244 ∨ t.natReg 244 ≤ address) → t.natMem address = s.natMem address) := by
  let fresh := s.natReg 244
  let slot := s.natReg 278
  let mat := tree.materialize fresh
  obtain ⟨ce,u,hu,hce,hu264,hu244,huSlot,hum,hus,hub,huFoot,hur,huFrame⟩ :=
    ensureNode_located tree low s hz h1 hi hs hb hslot hslotLow hslotHigh
  have halloc : fresh ≤ u.natReg 244 := by rw [hu244];split_ifs <;> omega
  have hmatNot : slot ∉ mat.footprint := by
    intro hm
    have hh := huFoot hm
    rcases Finset.mem_union.mp hh with hh | hh
    · exact hslotNot hh
    · have hgt := (Finset.mem_Ico.mp hh).1
      omega
  obtain ⟨address,items,hmat⟩ : ∃ address items, mat = LocatedTrie.leaf address items := by
    cases tree with
    | empty => exact ⟨fresh,[],rfl⟩
    | leaf a xs => exact ⟨a,xs,rfl⟩
  have hun (k : ℕ) (h264 : k ≠ 264) (h272 : k ≠ 272) (h274 : k ≠ 274) (h244 : k ≠ 244) : u.natReg k = s.natReg k :=
    hu.nat_frame (ensureNode_nat_frame k h264 h272 h274 h244)
  have huz := (hun 56 (by omega) (by omega) (by omega) (by omega)).trans hz
  have hu1 := (hun 26 (by omega) (by omega) (by omega) (by omega)).trans h1
  have hu262 := hun 262 (by omega) (by omega) (by omega) (by omega)
  have huAddress : u.natReg 264 = address := by
    change u.natReg 264 = mat.root at hu264
    simpa only [hmat,LocatedTrie.root] using hu264
  have hiLeaf : (LocatedTrie.leaf address items).Image u := by rwa [← hmat]
  have hsLeaf : (LocatedTrie.leaf address items).Separated := by rwa [← hmat]
  have hbLeaf : (LocatedTrie.leaf address items).Bounded low (u.natReg 244) := by rwa [← hmat]
  let t := leafFinished u
  let next := LocatedTrie.leaf address ((u.natReg 244,u.natReg 262)::items)
  obtain ⟨htImage,htSep,htBound,htAbstract,htFoot,htFrame⟩ := leafFinish_image address items low u huz hu1 huAddress hiLeaf hsLeaf hbLeaf
  have htEval : Eval leaf s (ce+12) t := Eval.seq hu (leafFinish_eval u)
  have htest : ¬(Test.natLess 56 256).holds s := by simp [Test.holds,hz,hheight]
  have hloop : Eval loop s 2 s := Eval.loopNo s htest
  have htAlloc : t.natReg 244 = u.natReg 244+2 := (leafFinish_values u address items.length (Payload.root items) huz hu1 huAddress hiLeaf.1 hiLeaf.2.1).1
  have htSlot : t.natMem slot = next.root := by
    have hh := htFrame slot (by rwa [← hmat]) (Or.inl (by omega))
    rw [hh]
    change u.natMem slot = address
    change u.natMem slot = mat.root at huSlot
    simpa only [hmat,LocatedTrie.root] using huSlot
  refine ⟨2+(ce+12),t,next,Eval.seq hloop htEval,by omega,htSlot,htImage,htSep,htBound,?_,by omega,?_,?_,?_⟩
  · rw [htAbstract,hu262]
    have hh := LocatedTrie.materialize_insert tree fresh (s.natReg 260) (s.natReg 262)
    change RadixQueue.insert 0 (s.natReg 260) (s.natReg 262) mat.abstract = _ at hh
    rw [hmat] at hh
    simpa only [LocatedTrie.abstract,RadixQueue.insert] using hh
  · intro a ha
    have hh := htFoot ha
    rcases Finset.mem_union.mp hh with hh | hh
    · have hm : a ∈ mat.footprint := by rwa [hmat]
      rcases Finset.mem_union.mp (huFoot hm) with hold | hnew
      · exact Finset.mem_union_left _ hold
      · exact Finset.mem_union_right _ (by have ht := Finset.mem_Ico.mp hnew;apply Finset.mem_Ico.mpr;constructor <;> omega)
    · have ht := Finset.mem_Ico.mp hh
      exact Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨by omega,ht.2⟩)
  · exact hur
  · intro a hne hnot hout
    have hmatNo : a ∉ (LocatedTrie.leaf address items).footprint := by
      intro hm
      have hm' : a ∈ mat.footprint := by rwa [hmat]
      rcases Finset.mem_union.mp (huFoot hm') with hold | hnew
      · exact hnot hold
      · have hh := Finset.mem_Ico.mp hnew
        omega
    have hfirst := huFrame a hne (by omega)
    have hsecond := htFrame a hmatNo (by
      change a < u.natReg 244 ∨ t.natReg 244 ≤ a
      omega)
    exact hsecond.trans hfirst
end DecrAlmostLinearSSSP.Decremental.Exact.TriePush
end s37
section s38
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
lemma Eval.deterministic {cmd : Cmd} {s t u : Data} {a b : ℕ}
    (ht : Eval cmd s a t) (hu : Eval cmd s b u) : a = b ∧ t = u := by
  induction ht generalizing b u with
  | skip s => cases hu;exact ⟨rfl,rfl⟩
  | atom atom s => cases hu;exact ⟨rfl,rfl⟩
  | seq ha hb iha ihb =>
    cases hu with
    | seq hc hd =>
      obtain ⟨rfl,rfl⟩ := iha hc
      obtain ⟨rfl,rfl⟩ := ihb hd
      exact ⟨rfl,rfl⟩
  | branchYes htest ht ih =>
    cases hu with
    | branchYes htest' hu =>
      obtain ⟨rfl,rfl⟩ := ih hu
      exact ⟨rfl,rfl⟩
    | branchNo htest' hu => exact False.elim (htest' htest)
  | branchNo htest ht ih =>
    cases hu with
    | branchYes htest' hu => exact False.elim (htest htest')
    | branchNo htest' hu =>
      obtain ⟨rfl,rfl⟩ := ih hu
      exact ⟨rfl,rfl⟩
  | loopNo s htest =>
    cases hu with
    | loopNo => exact ⟨rfl,rfl⟩
    | loopYes htest' ha hb => exact False.elim (htest htest')
  | loopYes htest ha hb iha ihb =>
    cases hu with
    | loopNo s htest' => exact False.elim (htest' htest)
    | loopYes htest' hc hd =>
      obtain ⟨rfl,rfl⟩ := iha hc
      obtain ⟨rfl,rfl⟩ := ihb hd
      exact ⟨rfl,rfl⟩
end DecrAlmostLinearSSSP.Decremental.Structured
end s38
section s39
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
lemma atom_no_memory (a : Atom) (s : Data) (h : NoStore a.instruction) :
    (a.effect s).realMem = s.realMem ∧ (a.effect s).natMem = s.natMem := by
  cases a with
  | mk ins hs =>
    cases ins <;> simp only [NoStore,Straight] at h hs
    all_goals try contradiction
    all_goals exact ⟨rfl,rfl⟩
lemma Eval.no_memory {cmd : Cmd} {s t : Data} {cost : ℕ} (he : Eval cmd s cost t)
    (h : NoMemory cmd) : t.realMem = s.realMem ∧ t.natMem = s.natMem := by
  induction he with
  | skip => exact ⟨rfl,rfl⟩
  | atom a s => exact atom_no_memory a s h
  | seq ha hb iha ihb => exact ⟨(ihb h.2).1.trans (iha h.1).1,(ihb h.2).2.trans (iha h.1).2⟩
  | branchYes ht he ih => exact ih h.1
  | branchNo ht he ih => exact ih h.2
  | loopNo => exact ⟨rfl,rfl⟩
  | loopYes ht ha hb iha ihb => exact ⟨(ihb h).1.trans (iha h).1,(ihb h).2.trans (iha h).2⟩
end DecrAlmostLinearSSSP.Decremental.Structured
end s39
section s40
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
lemma atom_no_real_memory (a : Atom) (s : Data) (h : NoRealStore a.instruction) : (a.effect s).realMem = s.realMem := by
  cases a with
  | mk ins hs =>
    cases ins <;> simp only [NoRealStore,Straight] at h hs
    all_goals first | contradiction | rfl
lemma Eval.no_real_memory {cmd : Cmd} {s t : Data} {cost : ℕ} (he : Eval cmd s cost t)
    (h : NoRealMemory cmd) : t.realMem = s.realMem := by
  induction he with
  | skip => rfl
  | atom a s => exact atom_no_real_memory a s h
  | seq ha hb iha ihb => exact (ihb h.2).trans (iha h.1)
  | branchYes ht he ih => exact ih h.1
  | branchNo ht he ih => exact ih h.2
  | loopNo => rfl
  | loopYes ht ha hb iha ihb => exact (ihb h).trans (iha h)
end DecrAlmostLinearSSSP.Decremental.Structured
end s40
section s41
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePush
open Structured
lemma core_nat_frame (k : ℕ) (hk : k ∉ registers) : NatFrame core k := by
  simp only [registers,Finset.mem_insert,Finset.mem_singleton,not_or] at hk
  simp [core,loop,body,leaf,ensureNode,increment,incrementAtoms,descend,leftChild,rightChild,
    leafPrepare,leafAtoms,Allocate.node,Allocate.nodeAtoms,Allocate.item,Allocate.itemAtoms,
    Structured.sequence,NatFrame,writesNat,loadN,storeN,nadd,nsub,natural] <;> tauto
lemma core_real_frame (k : ℕ) : RealFrame core k := by
  simp [core,loop,body,leaf,ensureNode,increment,incrementAtoms,descend,leftChild,rightChild,
    leafPrepare,leafAtoms,Allocate.node,Allocate.nodeAtoms,Allocate.item,Allocate.itemAtoms,
    Structured.sequence,RealFrame,writesReal,loadN,storeN,nadd,nsub,natural]
lemma core_no_real_memory : NoRealMemory core := by
  simp [core,loop,body,leaf,ensureNode,increment,incrementAtoms,descend,leftChild,rightChild,
    leafPrepare,leafAtoms,Allocate.node,Allocate.nodeAtoms,Allocate.item,Allocate.itemAtoms,
    Structured.sequence,NoRealMemory,NoRealStore,loadN,storeN,nadd,nsub,natural]
lemma core_unroll {s u t : Data} {c d : ℕ} (ht : (Test.natLess 56 256).holds s)
    (hb : Eval body s c u) (hc : Eval core u d t) : Eval core s (c+d+2) t := by
  cases hc with
  | seq hl he =>
    have hh := Eval.seq (Eval.loopYes ht hb hl) he
    convert hh using 1 <;> first | rfl | omega
end DecrAlmostLinearSSSP.Decremental.Exact.TriePush
end s41
section s42
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePush
open Structured
lemma descend_eval (s : Data) :
    Eval descend s (if s.natReg 260 < s.natMem (s.natReg 258) then 6 else 8) (descended s) := by
  let u := descendLoaded s
  have hu : Eval (loadN 268 258) s 1 u := eval_loadN s 268 258
  have hb : Eval (.branch (.natLess 260 268) leftChild rightChild) u
      (if s.natReg 260 < s.natMem (s.natReg 258) then 3 else 5) (descendBranched s) := by
    by_cases ht : s.natReg 260 < s.natMem (s.natReg 258)
    · have htest : (Test.natLess 260 268).holds u := by simpa [Test.holds,u,descendLoaded] using ht
      rw [if_pos ht]
      have hh := Eval.branchYes (no := rightChild) htest (Eval.seq (eval_natural u 282 1) (eval_nadd _ 278 264 282))
      simpa only [leftChild,descendBranched,if_pos ht] using hh
    · have htest : ¬(Test.natLess 260 268).holds u := by simpa [Test.holds,u,descendLoaded] using ht
      rw [if_neg ht]
      have hh := Eval.branchNo (yes := leftChild) htest (Eval.seq (eval_natural u 282 2)
        (Eval.seq (eval_nadd _ 278 264 282) (Eval.seq (eval_nsub _ 260 260 268) (Eval.skip _))))
      simpa only [rightChild,Structured.sequence,descendBranched,if_neg ht,Nat.add_zero] using hh
  have ht := Eval.seq hu (Eval.seq hb (Eval.seq (eval_nsub _ 256 256 26) (eval_nsub _ 258 258 26)))
  convert ht using 1 <;> first | rfl | (split_ifs <;> omega)
lemma descend_values (s : Data) (h : ℕ) (h1 : s.natReg 26 = 1) (hh : s.natReg 256 = h+1) :
    (descended s).natReg 256 = h ∧ (descended s).natReg 258 = s.natReg 258-1 ∧
    (descended s).natReg 278 = s.natReg 264+(if s.natReg 260 < s.natMem (s.natReg 258) then 1 else 2) ∧
    (descended s).natReg 260 = (if s.natReg 260 < s.natMem (s.natReg 258) then s.natReg 260 else s.natReg 260-s.natMem (s.natReg 258)) ∧
    (descended s).natMem = s.natMem ∧ (descended s).realMem = s.realMem := by
  unfold descended descendBranched descendLoaded
  split_ifs <;> simp [h1,hh]
lemma descend_nat_frame (k : ℕ) (h268 : k ≠ 268) (h282 : k ≠ 282) (h278 : k ≠ 278)
    (h260 : k ≠ 260) (h256 : k ≠ 256) (h258 : k ≠ 258) : NatFrame descend k := by
  simp [descend,leftChild,rightChild,Structured.sequence,NatFrame,writesNat,loadN,natural,nadd,nsub,
    Ne.symm h268,Ne.symm h282,Ne.symm h278,Ne.symm h260,Ne.symm h256,Ne.symm h258]
end DecrAlmostLinearSSSP.Decremental.Exact.TriePush
end s42
section s43
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie
lemma branch_root {h : ℕ} (b : Bool) (a : ℕ) (c o : LocatedTrie h) : (branch b a c o).root = a := by cases b <;> rfl
lemma branch_footprint {h : ℕ} (b : Bool) (a : ℕ) (c o : LocatedTrie h) :
    (branch b a c o).footprint = Finset.Ico a (a+4) ∪ (c.footprint ∪ o.footprint) := by
  cases b <;> simp [branch,footprint,Finset.union_comm]
lemma branch_image {h : ℕ} (b : Bool) (a : ℕ) (c o : LocatedTrie h) (s : Structured.Data) :
    (branch b a c o).Image s ↔ s.natMem a = RadixQueue.count c.abstract+RadixQueue.count o.abstract ∧
      s.natMem (a+childOffset b) = c.root ∧ s.natMem (a+otherOffset b) = o.root ∧ c.Image s ∧ o.Image s := by
  cases b <;> simp [branch,Image,childOffset,otherOffset,Nat.add_comm,and_comm,and_left_comm,and_assoc]
lemma branch_separated {h : ℕ} (b : Bool) (a : ℕ) (c o : LocatedTrie h) :
    (branch b a c o).Separated ↔ 0<a ∧ Disjoint (Finset.Ico a (a+4)) (c.footprint ∪ o.footprint) ∧
      Disjoint c.footprint o.footprint ∧ c.Separated ∧ o.Separated := by
  cases b <;> simp [branch,Separated,Finset.union_comm,disjoint_comm,and_comm,and_left_comm,and_assoc]
lemma branch_field_mem {h : ℕ} (b : Bool) (a : ℕ) (c o : LocatedTrie h) (r : ℕ) (hr : r<4) :
    a+r ∈ (branch b a c o).footprint := by
  rw [branch_footprint];exact Finset.mem_union_left _ (Finset.mem_Ico.mpr ⟨by omega,by omega⟩)
lemma branch_child_subset {h : ℕ} (b : Bool) (a : ℕ) (c o : LocatedTrie h) :
    c.footprint ⊆ (branch b a c o).footprint := by
  rw [branch_footprint];exact fun _ hh => Finset.mem_union_right _ (Finset.mem_union_left _ hh)
lemma branch_other_subset {h : ℕ} (b : Bool) (a : ℕ) (c o : LocatedTrie h) :
    o.footprint ⊆ (branch b a c o).footprint := by
  rw [branch_footprint];exact fun _ hh => Finset.mem_union_right _ (Finset.mem_union_right _ hh)
lemma childOffset_pos (b : Bool) : 0<childOffset b ∧ childOffset b<4 := by cases b <;> decide
lemma offsets_ne (b : Bool) : otherOffset b ≠ childOffset b := by cases b <;> decide
lemma otherOffset_lt (b : Bool) : otherOffset b<4 := by cases b <;> decide
end DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie
end s43
section s44
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePush
open Structured
lemma increment_nat_frame (k : ℕ) (hk : k ≠ 266) : NatFrame increment k := by
  simp [increment,incrementAtoms,Structured.sequence,NatFrame,writesNat,Ne.symm hk]
lemma descent_node_step (h address power : ℕ) (s : Data)
    (h1 : s.natReg 26 = 1) (hheight : s.natReg 256 = h+1)
    (haddress : s.natReg 264 = address) (hp : s.natMem (s.natReg 258) = power)
    (hne : s.natReg 258 ≠ address) :
    let t := descended (incremented s)
    Eval (.seq increment descend) s (if s.natReg 260 < power then 9 else 11) t ∧
      t.natReg 256 = h ∧ t.natReg 258 = s.natReg 258-1 ∧
      t.natReg 278 = address+(if s.natReg 260 < power then 1 else 2) ∧
      t.natReg 260 = (if s.natReg 260 < power then s.natReg 260 else s.natReg 260-power) ∧
      t.natMem = Function.update s.natMem address (s.natMem address+1) ∧
      t.realMem = s.realMem ∧
      (∀ k, k ≠ 266 → k ≠ 268 → k ≠ 282 → k ≠ 278 → k ≠ 260 → k ≠ 256 → k ≠ 258 →
        t.natReg k = s.natReg k) := by
  let u := incremented s
  have hu := increment_eval s
  have huf (k : ℕ) (hk : k ≠ 266) := hu.nat_frame (increment_nat_frame k hk)
  have hu26 : u.natReg 26 = 1 := (huf 26 (by omega)).trans h1
  have huHeight : u.natReg 256 = h+1 := (huf 256 (by omega)).trans hheight
  have huMem : u.natMem = Function.update s.natMem address (s.natMem address+1) := by
    simpa only [haddress] using (increment_fields s h1).1
  have huPower : u.natMem (u.natReg 258) = power := by
    rw [huf 258 (by omega),huMem,Function.update_of_ne hne,hp]
  have huKey : u.natReg 260 = s.natReg 260 := huf 260 (by omega)
  have huv := descend_values u h hu26 huHeight
  have he := Eval.seq hu (descend_eval u)
  have he' : Eval (.seq increment descend) s (if s.natReg 260 < power then 9 else 11) (descended u) := by
    rw [huKey,huPower] at he
    convert he using 1 <;> first | rfl | (split_ifs <;> omega)
  refine ⟨he',huv.1,?_,?_,?_,huv.2.2.2.2.1.trans huMem,huv.2.2.2.2.2,?_⟩
  · rw [huv.2.1,huf 258 (by omega)]
  · rw [huv.2.2.1,huf 264 (by omega),haddress,huKey,huPower]
  · rw [huv.2.2.2.1,huKey,huPower]
  · intro k h266 h268 h282 h278 h260 h256 h258
    exact ((descend_eval u).nat_frame (descend_nat_frame k h268 h282 h278 h260 h256 h258)).trans (huf k h266)
end DecrAlmostLinearSSSP.Decremental.Exact.TriePush
end s44
section s45
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie
lemma branch_rebuild {h : ℕ} (b : Bool) (address : ℕ) (child other next : LocatedTrie h)
    (low fresh stop : ℕ) (s t : Structured.Data)
    (hi : (branch b address child other).Image s)
    (hs : (branch b address child other).Separated)
    (hb : (branch b address child other).Bounded low fresh)
    (hmono : fresh ≤ stop) (hnext : next.Image t) (hsnext : next.Separated)
    (hbnext : next.Bounded low stop)
    (hfoot : next.footprint ⊆ child.footprint ∪ Finset.Ico fresh stop)
    (hcount : RadixQueue.count next.abstract = RadixQueue.count child.abstract+1)
    (hslot : t.natMem (address+childOffset b) = next.root)
    (hframe : ∀ a, a ≠ address+childOffset b → a ∉ child.footprint →
      (a < fresh ∨ stop ≤ a) → t.natMem a = Function.update s.natMem address (s.natMem address+1) a) :
    (branch b address next other).Image t ∧ (branch b address next other).Separated ∧
      (branch b address next other).Bounded low stop ∧
      (branch b address next other).footprint ⊆ (branch b address child other).footprint ∪ Finset.Ico fresh stop := by
  have hs' := (branch_separated b address child other).mp hs
  have hi' := (branch_image b address child other s).mp hi
  have hfield (r : ℕ) (hr : r<4) := hb _ (branch_field_mem b address child other r hr)
  have hchild (a : ℕ) (ha : a ∈ child.footprint) := hb a (branch_child_subset b address child other ha)
  have hother (a : ℕ) (ha : a ∈ other.footprint) := hb a (branch_other_subset b address child other ha)
  have hfieldNot (r : ℕ) (hr : r<4) : address+r ∉ child.footprint := by
    intro hm
    exact Finset.disjoint_left.mp hs'.2.1 (Finset.mem_Ico.mpr ⟨by omega,by omega⟩) (Finset.mem_union_left _ hm)
  have hotherNot (a : ℕ) (ha : a ∈ other.footprint) : a ∉ child.footprint :=
    fun hh => Finset.disjoint_left.mp hs'.2.2.1 hh ha
  have hotherField (a : ℕ) (ha : a ∈ other.footprint) (r : ℕ) (hr : r<4) : a ≠ address+r := by
    intro hh
    exact Finset.disjoint_left.mp hs'.2.1 (Finset.mem_Ico.mpr ⟨by omega,by omega⟩) (Finset.mem_union_right _ (hh ▸ ha))
  have hotherFrame (a : ℕ) (ha : a ∈ other.footprint) : t.natMem a = s.natMem a := by
    rw [hframe a (hotherField a ha _ (childOffset_pos b).2) (hotherNot a ha) (Or.inl (hother a ha).2),
      Function.update_of_ne (by simpa only [Nat.add_zero] using hotherField a ha 0 (by omega))]
  have htImage : (branch b address next other).Image t := by
    apply (branch_image b address next other t).mpr
    refine ⟨?_,hslot,?_,hnext,hi'.2.2.2.2.frame hotherFrame⟩
    · have hh := hframe address (by have := (childOffset_pos b).1;omega)
        (by simpa only [Nat.add_zero] using hfieldNot 0 (by omega))
        (Or.inl (by simpa only [Nat.add_zero] using (hfield 0 (by omega)).2))
      rw [hh,Function.update_self,hi'.1,hcount]
      omega
    · have hh := hframe (address+otherOffset b) (by have := offsets_ne b;omega)
        (hfieldNot _ (otherOffset_lt b)) (Or.inl (hfield _ (otherOffset_lt b)).2)
      rw [hh,Function.update_of_ne (by cases b <;> simp [otherOffset])]
      exact hi'.2.2.1
  have htSep : (branch b address next other).Separated := by
    apply (branch_separated b address next other).mpr
    refine ⟨hs'.1,?_,?_,hsnext,hs'.2.2.2.2⟩
    · apply Finset.disjoint_left.mpr
      intro a ha hh
      rcases Finset.mem_union.mp hh with hn | ho
      · rcases Finset.mem_union.mp (hfoot hn) with hc | hf
        · exact Finset.disjoint_left.mp hs'.2.1 ha (Finset.mem_union_left _ hc)
        · have hh := (Finset.mem_Ico.mp hf).1
          have hh' : a < fresh := (hb a (by rw [branch_footprint];exact Finset.mem_union_left _ ha)).2
          omega
      · exact Finset.disjoint_left.mp hs'.2.1 ha (Finset.mem_union_right _ ho)
    · apply Finset.disjoint_left.mpr
      intro a hn ho
      rcases Finset.mem_union.mp (hfoot hn) with hc | hf
      · exact Finset.disjoint_left.mp hs'.2.2.1 hc ho
      · have hh := (Finset.mem_Ico.mp hf).1
        have hh' := (hother a ho).2
        omega
  refine ⟨htImage,htSep,?_,?_⟩
  · intro a ha
    rw [branch_footprint] at ha
    rcases Finset.mem_union.mp ha with hf | hchildren
    · have hh := hb a (by rw [branch_footprint];exact Finset.mem_union_left _ hf)
      exact ⟨hh.1,hh.2.trans_le hmono⟩
    · rcases Finset.mem_union.mp hchildren with hn | ho
      · exact hbnext a hn
      · exact ⟨(hother a ho).1,(hother a ho).2.trans_le hmono⟩
  · intro a ha
    rw [branch_footprint] at ha
    rcases Finset.mem_union.mp ha with hf | hchildren
    · exact Finset.mem_union_left _ (by rw [branch_footprint];exact Finset.mem_union_left _ hf)
    · rcases Finset.mem_union.mp hchildren with hn | ho
      · rcases Finset.mem_union.mp (hfoot hn) with hc | hf
        · exact Finset.mem_union_left _ (branch_child_subset b address child other hc)
        · exact Finset.mem_union_right _ hf
      · exact Finset.mem_union_left _ (branch_other_subset b address child other ho)
end DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie
end s45
section s46
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePush
open Structured
lemma Result.nat_frame {h : ℕ} {tree : LocatedTrie h} {low : ℕ} {s : Data} (r : Result tree low s)
    (k : ℕ) (hk : k ∉ registers) : r.final.natReg k = s.natReg k := r.eval.nat_frame (core_nat_frame k hk)
lemma result_zero (tree : LocatedTrie 0) (low : ℕ) (s : Data)
    (hz : s.natReg 56 = 0) (h1 : s.natReg 26 = 1) (hheight : s.natReg 256 = 0)
    (hi : tree.Image s) (hs : tree.Separated) (hb : tree.Bounded low (s.natReg 244))
    (hslot : s.natMem (s.natReg 278) = tree.root) (hslotLow : low ≤ s.natReg 278)
    (hslotHigh : s.natReg 278 < s.natReg 244) (hslotNot : s.natReg 278 ∉ tree.footprint) :
    Nonempty (Result tree low s) := by
  obtain ⟨cost,t,next,he,hc,hslot,hi,hs,hb,ha,hal,hf,hr,hframe⟩ :=
    core_zero tree low s hz h1 hheight hi hs hb hslot hslotLow hslotHigh hslotNot
  exact ⟨⟨cost,t,next,he,by simpa using hc,hslot,hi,hs,hb,ha,hal,hf,hr,hframe⟩⟩
end DecrAlmostLinearSSSP.Decremental.Exact.TriePush
end s46
section s47
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePush
open Structured
lemma ready_zero (tree : LocatedTrie 0) (low base : ℕ) (s : Data) (hr : Ready tree low base s) :
    Nonempty (Result tree low s) := result_zero tree low s hr.zero hr.unit hr.height hr.image hr.separated hr.bounded hr.slot hr.slotLow hr.slotHigh hr.slotNot
end DecrAlmostLinearSSSP.Decremental.Exact.TriePush
end s47
section s48
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePush
open Structured
lemma child_ready {h : ℕ} (b : Bool) (address : ℕ) (child other : LocatedTrie h)
    (low base : ℕ) (s : Data) (hr : Ready (LocatedTrie.branch b address child other) low base s)
    (haddress : s.natReg 264 = address)
    (hchoice : b = if s.natReg 260 < 2^h then false else true) :
    Ready child low base (descended (incremented s)) := by
  let q := descended (incremented s)
  have hi := (LocatedTrie.branch_image b address child other s).mp hr.image
  have hs := (LocatedTrie.branch_separated b address child other).mp hr.separated
  have hhigh := hr.powersHigh
  have hptr := hr.powerPtr (by omega)
  have hpowerPtr : s.natReg 258 = base+h := by omega
  have hpower : s.natMem (s.natReg 258) = 2^h := by rw [hpowerPtr];exact hr.powers h (by omega)
  have hfield (r : ℕ) (hh : r<4) := hr.bounded _ (LocatedTrie.branch_field_mem b address child other r hh)
  have hne : s.natReg 258 ≠ address := by have hh := hfield 0 (by omega);omega
  obtain ⟨he,hh,hp,hslot,hkey,hmem,hreal,hframe⟩ := descent_node_step h address (2^h) s hr.unit hr.height haddress hpower hne
  have halloc : q.natReg 244 = s.natReg 244 := hframe 244 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hslot' : q.natReg 278 = address+LocatedTrie.childOffset b := by
    rw [hslot,hchoice];split_ifs <;> rfl
  have hchildNot (r : ℕ) (hh : r<4) : address+r ∉ child.footprint := by
    intro hm
    exact Finset.disjoint_left.mp hs.2.1 (Finset.mem_Ico.mpr ⟨by omega,by omega⟩) (Finset.mem_union_left _ hm)
  have hchildFrame (a : ℕ) (ha : a ∈ child.footprint) : q.natMem a = s.natMem a := by
    rw [hmem,Function.update_of_ne (by intro hh;subst a;exact hchildNot 0 (by omega) (by simpa using ha))]
  refine ⟨?_,?_,hh,hi.2.2.2.1.frame hchildFrame,hs.2.2.2.1,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (hframe 56 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hr.zero
  · exact (hframe 26 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hr.unit
  · intro a ha
    rw [halloc]
    exact hr.bounded a (LocatedTrie.branch_child_subset b address child other ha)
  · rw [hslot',hmem,Function.update_of_ne (by have := (LocatedTrie.childOffset_pos b).1;omega)]
    exact hi.2.1
  · rw [hslot'];exact (hfield _ (LocatedTrie.childOffset_pos b).2).1
  · rw [hslot',halloc];exact (hfield _ (LocatedTrie.childOffset_pos b).2).2
  · rw [hslot'];exact hchildNot _ (LocatedTrie.childOffset_pos b).2
  · intro j hj
    rw [hmem,Function.update_of_ne (by have hh := hfield 0 (by omega);omega)]
    exact hr.powers j (by omega)
  · omega
  · intro hnonzero
    rw [hp]
    omega
end DecrAlmostLinearSSSP.Decremental.Exact.TriePush
end s48
section s49
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePush
open Structured
lemma ensure_ready {h : ℕ} (tree : LocatedTrie h) (low base : ℕ) (s : Data)
    (hr : Ready tree low base s) :
    ∃ cost u, Eval ensureNode s cost u ∧ cost ≤ 14 ∧
      u.natReg 264 = (tree.materialize (s.natReg 244)).root ∧
      Ready (tree.materialize (s.natReg 244)) low base u ∧
      s.natReg 244 ≤ u.natReg 244 ∧
      (tree.materialize (s.natReg 244)).footprint ⊆ tree.footprint ∪ Finset.Ico (s.natReg 244) (u.natReg 244) ∧
      u.realMem = s.realMem ∧
      (∀ a, a ≠ s.natReg 278 → (a < s.natReg 244 ∨ u.natReg 244 ≤ a) → u.natMem a = s.natMem a) := by
  obtain ⟨cost,u,he,hc,hptr,ha,hslot,hi,hs,hb,hfoot,hreal,hframe⟩ :=
    ensureNode_located tree low s hr.zero hr.unit hr.image hr.separated hr.bounded hr.slot hr.slotLow hr.slotHigh
  have hn (k : ℕ) (h264 : k ≠ 264) (h272 : k ≠ 272) (h274 : k ≠ 274) (h244 : k ≠ 244) : u.natReg k = s.natReg k :=
    he.nat_frame (ensureNode_nat_frame k h264 h272 h274 h244)
  have h278 := hn 278 (by omega) (by omega) (by omega) (by omega)
  have h256 := hn 256 (by omega) (by omega) (by omega) (by omega)
  have h258 := hn 258 (by omega) (by omega) (by omega) (by omega)
  have halloc : s.natReg 244 ≤ u.natReg 244 := by rw [ha];split_ifs <;> omega
  refine ⟨cost,u,he,hc,hptr,?_,halloc,hfoot,hreal,hframe⟩
  refine ⟨?_,?_,h256.trans hr.height,hi,hs,hb,?_,?_,?_,?_,?_,hr.powersHigh,?_⟩
  · exact (hn 56 (by omega) (by omega) (by omega) (by omega)).trans hr.zero
  · exact (hn 26 (by omega) (by omega) (by omega) (by omega)).trans hr.unit
  · rwa [h278]
  · rw [h278];exact hr.slotLow
  · rw [h278];exact hr.slotHigh.trans_le halloc
  · rw [h278]
    intro hm
    rcases Finset.mem_union.mp (hfoot hm) with ho | hf
    · exact hr.slotNot ho
    · have hh := (Finset.mem_Ico.mp hf).1
      have hh' := hr.slotHigh
      omega
  · intro j hj
    rw [hframe (base+j) (by have := hr.slotLow;have := hr.powersHigh;omega) (Or.inl (by have := hr.slotLow;have := hr.slotHigh;have := hr.powersHigh;omega))]
    exact hr.powers j hj
  · intro hh
    rw [h258];exact hr.powerPtr hh
end DecrAlmostLinearSSSP.Decremental.Exact.TriePush
end s49
section s50
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePush
open Structured
lemma result_succ (h : ℕ)
    (ih : ∀ (child : LocatedTrie h) (low base : ℕ) (s : Data), Ready child low base s → Nonempty (Result child low s))
    (tree : LocatedTrie (h+1)) (low base : ℕ) (s : Data) (hr : Ready tree low base s) :
    Nonempty (Result tree low s) := by
  obtain ⟨ce,u,heu,hce,hup,hu,halloc,hfoot,hreal,hframe⟩ := ensure_ready tree low base s hr
  let mat := tree.materialize (s.natReg 244)
  obtain ⟨address,left,right,hmat⟩ : ∃ address left right, mat = LocatedTrie.node address left right := by
    cases tree with
    | empty => exact ⟨s.natReg 244,.empty,.empty,rfl⟩
    | node a l r => exact ⟨a,l,r,rfl⟩
  let b : Bool := if u.natReg 260 < 2^h then false else true
  let child := if b then right else left
  let other := if b then left else right
  have hb : mat = LocatedTrie.branch b address child other := by
    rw [hmat]
    cases hb : b <;> simp [LocatedTrie.branch,child,other,hb]
  have hu' : Ready (LocatedTrie.branch b address child other) low base u := by rwa [← hb]
  have haddress : u.natReg 264 = address := by
    change u.natReg 264 = mat.root at hup
    simpa only [hb,LocatedTrie.branch_root] using hup
  let q := descended (incremented u)
  have hq : Ready child low base q := child_ready b address child other low base u hu' haddress rfl
  have hpPtr : u.natReg 258 = base+h := by have := hu'.powerPtr (by omega);omega
  have hp : u.natMem (u.natReg 258) = 2^h := by rw [hpPtr];exact hu'.powers h (by omega)
  have hfield (r : ℕ) (hh : r<4) := hu'.bounded _ (LocatedTrie.branch_field_mem b address child other r hh)
  have hneq : u.natReg 258 ≠ address := by have := hu'.powersHigh;have := hfield 0 (by omega);omega
  obtain ⟨heq,hqh,hqp,hqs,hqk,hqm,hqr,hqn⟩ := descent_node_step h address (2^h) u hu'.unit hu'.height haddress hp hneq
  have hqalloc : q.natReg 244 = u.natReg 244 := hqn 244 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hqval : q.natReg 262 = u.natReg 262 := hqn 262 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hqslot : q.natReg 278 = address+LocatedTrie.childOffset b := by rw [hqs];unfold b;split_ifs <;> rfl
  obtain ⟨r⟩ := ih child low base q hq
  let next := LocatedTrie.branch b address r.next other
  have hrfoot : r.next.footprint ⊆ child.footprint ∪ Finset.Ico (u.natReg 244) (r.final.natReg 244) := by
    simpa only [hqalloc] using r.footprint
  have hrframe (a : ℕ) (hne : a ≠ address+LocatedTrie.childOffset b) (hnot : a ∉ child.footprint)
      (hout : a < u.natReg 244 ∨ r.final.natReg 244 ≤ a) :
      r.final.natMem a = Function.update u.natMem address (u.natMem address+1) a := by
    rw [r.frame a (by rwa [hqslot]) hnot (by rwa [hqalloc]),hqm]
  have hrslot : r.final.natMem (address+LocatedTrie.childOffset b) = r.next.root := by
    simpa only [hqslot] using r.slot
  have hrcount : RadixQueue.count r.next.abstract = RadixQueue.count child.abstract+1 := by
    rw [r.abstract,RadixQueue.count_insert]
  obtain ⟨htImage,htSep,htBound,htFoot⟩ := LocatedTrie.branch_rebuild b address child other r.next low
    (u.natReg 244) (r.final.natReg 244) u r.final hu'.image hu'.separated hu'.bounded
    (by simpa only [hqalloc] using r.alloc) r.image r.separated r.bounded hrfoot hrcount hrslot hrframe
  have hun (k : ℕ) (h264 : k ≠ 264) (h272 : k ≠ 272) (h274 : k ≠ 274) (h244 : k ≠ 244) : u.natReg k = s.natReg k :=
    heu.nat_frame (ensureNode_nat_frame k h264 h272 h274 h244)
  have hu278 := hun 278 (by omega) (by omega) (by omega) (by omega)
  have hu260 := hun 260 (by omega) (by omega) (by omega) (by omega)
  have hu262 := hun 262 (by omega) (by omega) (by omega) (by omega)
  have hralloc : u.natReg 244 ≤ r.final.natReg 244 := by simpa only [hqalloc] using r.alloc
  have hslotNot : s.natReg 278 ∉ mat.footprint := by
    rw [← hu278];exact hu.slotNot
  have hslotHigh : s.natReg 278 < u.natReg 244 := by rw [← hu278];exact hu.slotHigh
  have hfieldNot (a : ℕ) (ha : a ∉ mat.footprint) : a ≠ address ∧ a ≠ address+LocatedTrie.childOffset b ∧ a ∉ child.footprint := by
    constructor
    · intro hh;apply ha;rw [hh,hb];simpa only [Nat.add_zero] using LocatedTrie.branch_field_mem b address child other 0 (by omega)
    · constructor
      · intro hh;apply ha;rw [hh,hb];exact LocatedTrie.branch_field_mem b address child other _ (LocatedTrie.childOffset_pos b).2
      · intro hh;apply ha;rw [hb];exact LocatedTrie.branch_child_subset b address child other hh
  have htSlot : r.final.natMem (s.natReg 278) = next.root := by
    obtain ⟨hn0,hns,hnc⟩ := hfieldNot _ hslotNot
    rw [hrframe _ hns hnc (Or.inl hslotHigh),Function.update_of_ne hn0]
    change u.natMem (s.natReg 278) = next.root
    rw [← hu278,hu.slot]
    change mat.root = (LocatedTrie.branch b address r.next other).root
    rw [hb,LocatedTrie.branch_root,LocatedTrie.branch_root]
  have habstract : next.abstract = RadixQueue.insert (h+1) (s.natReg 260) (s.natReg 262) tree.abstract := by
    have hmaterialize := LocatedTrie.materialize_insert tree (s.natReg 244) (s.natReg 260) (s.natReg 262)
    change RadixQueue.insert (h+1) (s.natReg 260) (s.natReg 262) mat.abstract = _ at hmaterialize
    rw [← hmaterialize,hb,← hu260,← hu262]
    have hab := r.abstract
    rw [hqval,hqk] at hab
    change (LocatedTrie.branch b address r.next other).abstract = _
    unfold b at *
    split_ifs with hk
    · simpa only [LocatedTrie.branch,Bool.false_eq_true,if_false,LocatedTrie.abstract,RadixQueue.insert,if_pos hk] using congrArg (fun x => RadixQueue.Trie.node x other.abstract) hab
    · simpa only [LocatedTrie.branch,if_true,LocatedTrie.abstract,RadixQueue.insert,if_neg hk] using congrArg (fun x => RadixQueue.Trie.node other.abstract x) hab
  have htFoot : next.footprint ⊆ tree.footprint ∪ Finset.Ico (s.natReg 244) (r.final.natReg 244) := by
    intro a ha
    rcases Finset.mem_union.mp (htFoot ha) with hm | hn
    · have hm' : a ∈ mat.footprint := by rwa [hb]
      rcases Finset.mem_union.mp (hfoot hm') with ho | hf
      · exact Finset.mem_union_left _ ho
      · have hh := Finset.mem_Ico.mp hf
        exact Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨hh.1,hh.2.trans_le hralloc⟩)
    · have hh := Finset.mem_Ico.mp hn
      exact Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨halloc.trans hh.1,hh.2⟩)
  have htFrame (a : ℕ) (hne : a ≠ s.natReg 278) (hnot : a ∉ tree.footprint)
      (hout : a < s.natReg 244 ∨ r.final.natReg 244 ≤ a) : r.final.natMem a = s.natMem a := by
    have hmatNo : a ∉ mat.footprint := by
      intro hm
      rcases Finset.mem_union.mp (hfoot hm) with ho | hf
      · exact hnot ho
      · have hh := Finset.mem_Ico.mp hf;omega
    obtain ⟨hn0,hns,hnc⟩ := hfieldNot a hmatNo
    rw [hrframe a hns hnc (by omega),Function.update_of_ne hn0,hframe a hne (by omega)]
  have heBody := Eval.seq heu heq
  have heCore := core_unroll (by simp [Test.holds,hr.zero,hr.height]) heBody r.eval
  refine ⟨⟨ce+(if u.natReg 260 < 2^h then 9 else 11)+r.cost+2,r.final,next,heCore,?_,htSlot,
    htImage,htSep,htBound,habstract,halloc.trans hralloc,htFoot,r.realMem.trans (hqr.trans hreal),htFrame⟩⟩
  have hc := r.costBound
  split_ifs <;> omega
end DecrAlmostLinearSSSP.Decremental.Exact.TriePush
end s50
section s51
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePush
open Structured
lemma core_result (h : ℕ) (tree : LocatedTrie h) (low base : ℕ) (s : Data)
    (hr : Ready tree low base s) : Nonempty (Result tree low s) := by
  induction h generalizing low base s with
  | zero => exact ready_zero tree low base s hr
  | succ h ih => exact result_succ h ih tree low base s hr
lemma code_nat_frame (k : ℕ) (hk : k ∉ registers) : NatFrame code k := by
  refine ⟨?_,core_nat_frame k hk⟩
  simp only [registers,Finset.mem_insert,Finset.mem_singleton,not_or] at hk
  simp [start,startAtoms,Structured.sequence,NatFrame,writesNat] <;> tauto
lemma code_real_frame (k : ℕ) : RealFrame code k := by
  refine ⟨?_,core_real_frame k⟩
  simp [start,startAtoms,Structured.sequence,RealFrame,writesReal]
lemma code_result (h : ℕ) (tree : LocatedTrie h) (low base : ℕ) (s : Data)
    (hz : s.natReg 56 = 0) (h1 : s.natReg 26 = 1) (hheight : s.natReg 236 = h)
    (hi : tree.Image s) (hs : tree.Separated) (hb : tree.Bounded low (s.natReg 244))
    (hslot : s.natMem (s.natReg 246) = tree.root) (hslotLow : low ≤ s.natReg 246)
    (hslotHigh : s.natReg 246 < s.natReg 244) (hslotNot : s.natReg 246 ∉ tree.footprint)
    (hpowers : ∀ j<h, s.natMem (base+j) = 2^j) (hpowerHigh : base+h ≤ low)
    (hpowerPtr : h ≠ 0 → s.natReg 238+1 = base+h) :
    ∃ (cost : ℕ) (t : Data) (next : LocatedTrie h), Eval code s cost t ∧ cost ≤ 43*(h+1) ∧
      t.natMem (s.natReg 246) = next.root ∧ next.Image t ∧ next.Separated ∧ next.Bounded low (t.natReg 244) ∧
      next.abstract = RadixQueue.insert h (s.natReg 260) (s.natReg 262) tree.abstract ∧
      s.natReg 244 ≤ t.natReg 244 ∧
      next.footprint ⊆ tree.footprint ∪ Finset.Ico (s.natReg 244) (t.natReg 244) ∧
      t.realMem = s.realMem ∧
      (∀ address, address ≠ s.natReg 246 → address ∉ tree.footprint →
        (address < s.natReg 244 ∨ t.natReg 244 ≤ address) → t.natMem address = s.natMem address) := by
  let u := started s
  have hu := start_eval s
  have huf := start_fields s hz
  have hmem : u.natMem = s.natMem := by rfl
  have hreal : u.realMem = s.realMem := by rfl
  have h244 : u.natReg 244 = s.natReg 244 := by
    simp [u,started,startAtoms,Atom.effect,instructionEffect,data,Data.machine]
  have h278 : u.natReg 278 = s.natReg 246 := huf.2.2
  have hready : Ready tree low base u := by
    refine ⟨?_,?_,huf.1.trans hheight,hi.frame (fun a _ => congrFun hmem a),hs,?_,?_,?_,?_,?_,?_,hpowerHigh,?_⟩
    · simpa [u,started,startAtoms,Atom.effect,instructionEffect,data,Data.machine] using hz
    · simpa [u,started,startAtoms,Atom.effect,instructionEffect,data,Data.machine] using h1
    · rwa [h244]
    · rwa [h278,hmem]
    · rwa [h278]
    · rwa [h278,h244]
    · rwa [h278]
    · intro j hj;rw [hmem];exact hpowers j hj
    · intro hh;rw [huf.2.1];exact hpowerPtr hh
  obtain ⟨r⟩ := core_result h tree low base u hready
  refine ⟨3+r.cost,r.final,r.next,Eval.seq hu r.eval,?_,?_,r.image,r.separated,r.bounded,?_,?_,?_,r.realMem.trans hreal,?_⟩
  · have hh := r.costBound;omega
  · rw [←h278];exact r.slot
  · simpa [u,started,startAtoms,Atom.effect,instructionEffect,data,Data.machine] using r.abstract
  · rw [←h244];exact r.alloc
  · simpa only [h244] using r.footprint
  · intro a hne hnot hout
    exact (r.frame a (by rwa [h278]) hnot (by rwa [h244])).trans (congrFun hmem a)
end DecrAlmostLinearSSSP.Decremental.Exact.TriePush
end s51
section s52
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePop
open Structured
lemma decrement_eval (s : Data) : Eval decrement s 3 (decremented s) := eval_sequence_atoms decrementAtoms s
lemma decrement_fields (s : Data) (h1 : s.natReg 26 = 1) :
    (decremented s).natMem = Function.update s.natMem (s.natReg 264) (s.natMem (s.natReg 264)-1) := by
  simp [decremented,decrementAtoms,Atom.effect,instructionEffect,data,Data.machine,h1]
lemma leftPointer_eval (s : Data) : Eval leftPointer s 3 (leftPointerData s) := eval_sequence_atoms leftPointerAtoms s
lemma leafFinish_eval (s : Data) : Eval leafFinish s 7 (leafFinished s) := eval_sequence_atoms leafAtoms s
lemma leaf_eval (s : Data) : Eval leaf s 10 (leafData s) := Eval.seq (decrement_eval s) (leafFinish_eval _)
lemma start_eval (s : Data) : Eval start s 4 (started s) := eval_sequence_atoms startAtoms s
end DecrAlmostLinearSSSP.Decremental.Exact.TriePop
end s52
section s53
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePop
open Structured
lemma core_nat_frame (k : ℕ) (hk : k ∉ registers) : NatFrame core k := by
  simp only [registers,Finset.mem_insert,Finset.mem_singleton,not_or] at hk
  simp [core,loop,body,leaf,decrement,decrementAtoms,descend,leftPointer,leftPointerAtoms,leftCount,
    choose,chooseLeft,chooseRight,rightAtoms,leafFinish,leafAtoms,
    Structured.sequence,NatFrame,writesNat,loadN,storeN,nadd,nsub,natural] <;> tauto
lemma core_real_frame (k : ℕ) : RealFrame core k := by
  simp [core,loop,body,leaf,decrement,decrementAtoms,descend,leftPointer,leftPointerAtoms,leftCount,
    choose,chooseLeft,chooseRight,rightAtoms,leafFinish,leafAtoms,
    Structured.sequence,RealFrame,writesReal,loadN,storeN,nadd,nsub,natural]
lemma core_no_real_memory : NoRealMemory core := by
  simp [core,loop,body,leaf,decrement,decrementAtoms,descend,leftPointer,leftPointerAtoms,leftCount,
    choose,chooseLeft,chooseRight,rightAtoms,leafFinish,leafAtoms,
    Structured.sequence,NoRealMemory,NoRealStore,loadN,storeN,nadd,nsub,natural]
lemma core_unroll {s u t : Data} {c d : ℕ} (ht : (Test.natLess 56 256).holds s)
    (hb : Eval body s c u) (hc : Eval core u d t) : Eval core s (c+d+2) t := by
  cases hc with
  | seq hl he =>
    have hh := Eval.seq (Eval.loopYes ht hb hl) he
    convert hh using 1 <;> first | rfl | omega
end DecrAlmostLinearSSSP.Decremental.Exact.TriePop
end s53
section s54
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePop
open Structured
lemma leftCount_eval (s : Data) (hz : s.natReg 56 = 0) :
    ∃ c, Eval leftCount s c (leftCountData s) ∧ c ≤ 3 := by
  by_cases hp : 0 < s.natReg 278
  · refine ⟨2,?_,by omega⟩
    have ht : (Test.natLess 56 278).holds s := by simpa [Test.holds,hz] using hp
    have he := Eval.branchYes (no := natural 284 0) ht (eval_loadN s 284 278)
    simpa [leftCount,leftCountData,if_pos hp] using he
  · refine ⟨3,?_,by omega⟩
    have ht : ¬(Test.natLess 56 278).holds s := by simpa [Test.holds,hz] using hp
    have he := Eval.branchNo (yes := loadN 284 278) ht (eval_natural s 284 0)
    simpa [leftCount,leftCountData,if_neg hp] using he
lemma choose_eval (s : Data) (hz : s.natReg 56 = 0) :
    ∃ c, Eval choose s c (chosen s) ∧ c ≤ 7 := by
  by_cases hp : 0 < s.natReg 284
  · refine ⟨2,?_,by omega⟩
    have ht : (Test.natLess 56 284).holds s := by simpa [Test.holds,hz] using hp
    have he := Eval.branchYes (no := chooseRight) ht (eval_nadd s 264 278 56)
    simpa only [choose,chooseLeft,chosen,if_pos hp] using he
  · refine ⟨7,?_,by omega⟩
    have ht : ¬(Test.natLess 56 284).holds s := by simpa [Test.holds,hz] using hp
    have he := Eval.branchNo (yes := chooseLeft) ht (eval_sequence_atoms rightAtoms s)
    change Eval (.branch (.natLess 56 284) chooseLeft chooseRight) s 7 (rightData s) at he
    simpa only [choose,chosen,if_neg hp] using he
lemma descend_eval (s : Data) (hz : s.natReg 56 = 0) :
    ∃ c, Eval descend s c (descended s) ∧ c ≤ 15 := by
  let u := leftPointerData s
  have huz : u.natReg 56 = 0 := by simp [u,leftPointerData,leftPointerAtoms,Atom.effect,instructionEffect,data,Data.machine,hz]
  obtain ⟨cl,hel,hcl⟩ := leftCount_eval u huz
  let v := leftCountData u
  have hvz : v.natReg 56 = 0 := by simpa [v,leftCountData] using huz
  obtain ⟨cc,hec,hcc⟩ := choose_eval v hvz
  refine ⟨3+(cl+(cc+(1+1))),Eval.seq (leftPointer_eval s) (Eval.seq hel (Eval.seq hec (Eval.seq (eval_nsub _ 256 256 26) (eval_nsub _ 258 258 26)))),by omega⟩
lemma descend_fields (s : Data) (h : ℕ) (hz : s.natReg 56 = 0) (h1 : s.natReg 26 = 1)
    (hheight : s.natReg 256 = h+1) :
    let left := s.natMem (s.natReg 264+1)
    let count := if 0<left then s.natMem left else 0
    (descended s).natReg 264 = (if 0<count then left else s.natMem (s.natReg 264+2)) ∧
      (descended s).natReg 260 = s.natReg 260+(if 0<count then 0 else s.natMem (s.natReg 258)) ∧
      (descended s).natReg 256 = h ∧ (descended s).natReg 258 = s.natReg 258-1 ∧
      (descended s).natMem = s.natMem ∧ (descended s).realMem = s.realMem := by
  unfold descended chosen leftCountData leftPointerData
  simp only [leftPointerAtoms,List.foldl_cons,List.foldl_nil]
  simp only [Atom.effect,instructionEffect,data,Data.machine]
  simp only [Function.update_self,Function.update_of_ne (by decide : (284 : ℕ) ≠ 278),
    Function.update_of_ne (by decide : (264 : ℕ) ≠ 282),Function.update_of_ne (by decide : (264 : ℕ) ≠ 278),
    Function.update_of_ne (by decide : (284 : ℕ) ≠ 282)]
  split_ifs <;> simp_all [rightData,rightAtoms,Atom.effect,instructionEffect,data,Data.machine]
lemma descend_nat_frame (k : ℕ) (hk : k ∉ ({256,258,260,264,268,278,282,284} : Finset ℕ)) : NatFrame descend k := by
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hk
  simp [descend,leftPointer,leftPointerAtoms,leftCount,choose,chooseLeft,chooseRight,rightAtoms,
    Structured.sequence,NatFrame,writesNat,natural,nadd,nsub,loadN] <;> tauto
end DecrAlmostLinearSSSP.Decremental.Exact.TriePop
end s54
section s55
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePop
open Structured
lemma leaf_fields (address payload value : ℕ) (items : List (ℕ × ℕ)) (s : Data)
    (h1 : s.natReg 26 = 1) (hptr : s.natReg 264 = address)
    (hi : (LocatedTrie.leaf address ((payload,value)::items)).Image s)
    (hs : (LocatedTrie.leaf address ((payload,value)::items)).Separated) :
    (leafData s).natMem = Function.update (Function.update s.natMem address items.length) (address+3) (Payload.root items) ∧
      (leafData s).natReg 262 = value ∧ (leafData s).natReg 260 = s.natReg 260 ∧
      (leafData s).realMem = s.realMem := by
  have hpn : payload ≠ address := by
    intro hh
    exact Finset.disjoint_left.mp hs.2.1 (Finset.mem_Ico.mpr ⟨le_rfl,by omega⟩)
      (Finset.mem_union_left _ (Finset.mem_Ico.mpr ⟨by omega,by omega⟩))
  have hpn1 : payload+1 ≠ address := by
    intro hh
    exact Finset.disjoint_left.mp hs.2.1 (Finset.mem_Ico.mpr ⟨le_rfl,by omega⟩)
      (Finset.mem_union_left _ (Finset.mem_Ico.mpr ⟨by omega,by omega⟩))
  have hcount := hi.1
  have hhead := hi.2.1
  have hval := hi.2.2.1
  have hnext := hi.2.2.2.1
  simp only [Payload.root] at hhead
  simp [leafData,leafFinished,leafAtoms,decremented,decrementAtoms,Atom.effect,instructionEffect,data,Data.machine,
    h1,hptr,hcount,hhead,hpn,hpn1,hval,hnext]
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
theorem solution : (((((((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 272) (instOfNatNat (nat_lit 272))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 274) (instOfNatNat (nat_lit 274))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))) →
        DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.Allocate.item k) ∧ (∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Exact.Allocate.item k)) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @LT.lt.{0} Nat instLTNat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278))))
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))) →
        ∃ cost t,
          And
            (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePush.ensureNode
              s cost t)
            (And (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
              (And
                (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 264) (instOfNatNat (nat_lit 264))))
                  (@ite.{1} Nat
                    (@Eq.{1} Nat (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278)))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                    (instDecidableEqNat
                      (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278)))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))
                    (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278)))))))
                (And
                  (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))
                    (@ite.{1} Nat
                      (@Eq.{1} Nat
                        (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278)))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                      (instDecidableEqNat
                        (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278)))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))))
                  (And
                    (@Eq.{1} Nat (t.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278)))))
                      (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 264) (instOfNatNat (nat_lit 264)))))
                    (And (@Eq.{1} (Nat → Real) t.realMem s.realMem)
                      (And
                        (@Eq.{1} Nat
                            (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278)))))
                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                          DecrAlmostLinearSSSP.Decremental.Exact.Allocate.NodeImage t
                            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))
                            { count := @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)),
                              left := @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)),
                              right := @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)),
                              payload := @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)) })
                        (∀ (address : Nat),
                          @Ne.{1} Nat address
                              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278)))) →
                            Or
                                (@LT.lt.{0} Nat instLTNat address
                                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))))
                                (@LE.le.{0} Nat instLENat
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                                  address) →
                              @Eq.{1} Nat (t.natMem address) (s.natMem address))))))))) ∧ (∀ (height fresh : Nat),
  @Eq.{1} Nat
    (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root height
      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.materialize height
        (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.empty height) fresh))
    fresh))) ∧ (((∀ {height : Nat} (tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie height) (fresh : Nat),
  @Ne.{1} (DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie height) tree
      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.empty height) →
    @Eq.{1} (DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie height)
      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.materialize height tree fresh) tree) ∧ (∀ {height : Nat} (tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie height) (fresh key value : Nat),
  @Eq.{1} (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height)
    (DecrAlmostLinearSSSP.Decremental.RadixQueue.insert height key value
      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.abstract height
        (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.materialize height tree fresh)))
    (DecrAlmostLinearSSSP.Decremental.RadixQueue.insert height key value
      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.abstract height tree)))) ∧ ((∀ {s : DecrAlmostLinearSSSP.Decremental.Structured.Data} (height fresh : Nat),
  DecrAlmostLinearSSSP.Decremental.Exact.Allocate.NodeImage s fresh
      { count := @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)),
        left := @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)),
        right := @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)),
        payload := @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)) } →
    @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image s height
      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.materialize height
        (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.empty height) fresh)) ∧ ((∀ (height fresh : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) fresh →
    @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Separated height
      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.materialize height
        (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.empty height) fresh)) ∧ (∀ (height fresh : Nat),
  @Eq.{1} (Finset.{0} Nat)
    (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint height
      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.materialize height
        (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.empty height) fresh))
    (@Finset.Ico.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder fresh
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) fresh
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))))) ∧ ((((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
    @Ne.{1} Nat (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278)))))
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
      DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePush.ensureNode s
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
        (DecrAlmostLinearSSSP.Decremental.Exact.TriePush.loaded s)) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 264) (instOfNatNat (nat_lit 264))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 272) (instOfNatNat (nat_lit 272))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 274) (instOfNatNat (nat_lit 274))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
            DecrAlmostLinearSSSP.Decremental.Exact.TriePush.ensureNode k)) ∧ ((∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Exact.TriePush.ensureNode k) ∧ (∀ {height : Nat} (tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie height) (low : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image s height tree →
        @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Separated height tree →
          @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Bounded height tree low
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))) →
            @Eq.{1} Nat (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278)))))
                (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root height tree) →
              @LE.le.{0} Nat instLENat low
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278)))) →
                @LT.lt.{0} Nat instLTNat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278))))
                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))) →
                  ∃ cost t,
                    And
                      (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                        DecrAlmostLinearSSSP.Decremental.Exact.TriePush.ensureNode s cost t)
                      (And
                        (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
                        (And
                          (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 264) (instOfNatNat (nat_lit 264))))
                            (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root height
                              (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.materialize height tree
                                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))))))
                          (And
                            (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))
                              (@ite.{1} Nat
                                (@Eq.{1} Nat (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root height tree)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                (instDecidableEqNat
                                  (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root height tree)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))))
                            (And
                              (@Eq.{1} Nat
                                (t.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278)))))
                                (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root height
                                  (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.materialize height tree
                                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))))))
                              (And
                                (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image t height
                                  (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.materialize height tree
                                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))))
                                (And
                                  (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Separated height
                                    (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.materialize height tree
                                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))))
                                  (And
                                    (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Bounded height
                                      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.materialize height tree
                                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))))
                                      low (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))))
                                    (And
                                      (@LE.le.{0} (Finset.{0} Nat)
                                        (@Preorder.toLE.{0} (Finset.{0} Nat)
                                          (@PartialOrder.toPreorder.{0} (Finset.{0} Nat)
                                            (@Finset.instPartialOrder.{0} Nat)))
                                        (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint height
                                          (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.materialize height tree
                                            (s.natReg
                                              (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))))
                                        (@Union.union.{0} (Finset.{0} Nat)
                                          (@Finset.instUnion.{0} Nat instDecidableEqNat)
                                          (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint height tree)
                                          (@Finset.Ico.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                                            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))
                                            (t.natReg
                                              (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))))))
                                      (And (@Eq.{1} (Nat → Real) t.realMem s.realMem)
                                        (∀ (address : Nat),
                                          @Ne.{1} Nat address
                                              (s.natReg
                                                (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278)))) →
                                            Or
                                                (@LT.lt.{0} Nat instLTNat address
                                                  (s.natReg
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))))
                                                (@LE.le.{0} Nat instLENat
                                                  (t.natReg
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))
                                                  address) →
                                              @Eq.{1} Nat (t.natMem address) (s.natMem address)))))))))))))) ∧ (((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePush.increment s
    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
    (DecrAlmostLinearSSSP.Decremental.Exact.TriePush.incremented s)) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
    And
      (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.Exact.TriePush.incremented s).natMem
        (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natMem
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 264) (instOfNatNat (nat_lit 264))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 264) (instOfNatNat (nat_lit 264)))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@Eq.{1} Nat
        ((DecrAlmostLinearSSSP.Decremental.Exact.TriePush.incremented s).natReg
          (@OfNat.ofNat.{0} Nat (nat_lit 266) (instOfNatNat (nat_lit 266))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 264) (instOfNatNat (nat_lit 264)))))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePush.leafPrepare s
    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
    (DecrAlmostLinearSSSP.Decremental.Exact.TriePush.leafPrepared s)) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  And
    (@Eq.{1} Nat
      ((DecrAlmostLinearSSSP.Decremental.Exact.TriePush.leafPrepared s).natReg
        (@OfNat.ofNat.{0} Nat (nat_lit 280) (instOfNatNat (nat_lit 280))))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 264) (instOfNatNat (nat_lit 264))))
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@Eq.{1} Nat
      ((DecrAlmostLinearSSSP.Decremental.Exact.TriePush.leafPrepared s).natReg
        (@OfNat.ofNat.{0} Nat (nat_lit 276) (instOfNatNat (nat_lit 276))))
      (s.natMem
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 264) (instOfNatNat (nat_lit 264))))
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePush.start s
    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
    (DecrAlmostLinearSSSP.Decremental.Exact.TriePush.started s))))))) ∧ (((((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    And
      (@Eq.{1} Nat
        ((DecrAlmostLinearSSSP.Decremental.Exact.TriePush.started s).natReg
          (@OfNat.ofNat.{0} Nat (nat_lit 256) (instOfNatNat (nat_lit 256))))
        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 236) (instOfNatNat (nat_lit 236)))))
      (And
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.Exact.TriePush.started s).natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 258) (instOfNatNat (nat_lit 258))))
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 238) (instOfNatNat (nat_lit 238)))))
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.Exact.TriePush.started s).natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278))))
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 246) (instOfNatNat (nat_lit 246))))))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePush.leafFinish s
    (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))
    (DecrAlmostLinearSSSP.Decremental.Exact.TriePush.leafFinished s))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (address count head : Nat),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 264) (instOfNatNat (nat_lit 264)))) address →
        @Eq.{1} Nat (s.natMem address) count →
          @Eq.{1} Nat
              (s.natMem
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) address
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
              head →
            And
              (@Eq.{1} Nat
                ((DecrAlmostLinearSSSP.Decremental.Exact.TriePush.leafFinished s).natReg
                  (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              (And
                (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.Exact.TriePush.leafFinished s).natMem
                  (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
                    (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
                      (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
                        (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natMem address
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) count
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))
                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 262) (instOfNatNat (nat_lit 262)))))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      head)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) address
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))))
                (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.Exact.TriePush.leafFinished s).realMem
                  s.realMem))) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 266) (instOfNatNat (nat_lit 266))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 282) (instOfNatNat (nat_lit 282))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 280) (instOfNatNat (nat_lit 280))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 276) (instOfNatNat (nat_lit 276))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 272) (instOfNatNat (nat_lit 272))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 274) (instOfNatNat (nat_lit 274))) →
              @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))) →
                DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
                  DecrAlmostLinearSSSP.Decremental.Exact.TriePush.leafFinish k))) ∧ (((∀ (address : Nat) (items : List.{0} (Prod.{0, 0} Nat Nat)) (low : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 264) (instOfNatNat (nat_lit 264)))) address →
        @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image s
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.leaf address items) →
          @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Separated
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.leaf address items) →
            @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Bounded
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.leaf address items) low
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))) →
              have next :=
                DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.leaf address
                  (@List.cons.{0} (Prod.{0, 0} Nat Nat)
                    (@Prod.mk.{0, 0} Nat Nat
                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))
                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 262) (instOfNatNat (nat_lit 262)))))
                    items);
              And
                (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image
                  (DecrAlmostLinearSSSP.Decremental.Exact.TriePush.leafFinished s)
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) next)
                (And
                  (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Separated
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) next)
                  (And
                    (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Bounded
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) next low
                      ((DecrAlmostLinearSSSP.Decremental.Exact.TriePush.leafFinished s).natReg
                        (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))))
                    (And
                      (@Eq.{1}
                        (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie
                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                        (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.abstract
                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) next)
                        (DecrAlmostLinearSSSP.Decremental.RadixQueue.insert
                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 262) (instOfNatNat (nat_lit 262))))
                          (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.abstract
                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                            (DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.leaf address items))))
                      (And
                        (@LE.le.{0} (Finset.{0} Nat)
                          (@Preorder.toLE.{0} (Finset.{0} Nat)
                            (@PartialOrder.toPreorder.{0} (Finset.{0} Nat) (@Finset.instPartialOrder.{0} Nat)))
                          (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint
                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) next)
                          (@Union.union.{0} (Finset.{0} Nat) (@Finset.instUnion.{0} Nat instDecidableEqNat)
                            (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint
                              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                              (DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.leaf address items))
                            (@Finset.Ico.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))
                              ((DecrAlmostLinearSSSP.Decremental.Exact.TriePush.leafFinished s).natReg
                                (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))))))
                        (∀
                          a ∉
                            @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint
                              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                              (DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.leaf address items),
                          Or
                              (@LT.lt.{0} Nat instLTNat a
                                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))))
                              (@LE.le.{0} Nat instLENat
                                ((DecrAlmostLinearSSSP.Decremental.Exact.TriePush.leafFinished s).natReg
                                  (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))
                                a) →
                            @Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.Exact.TriePush.leafFinished s).natMem a)
                              (s.natMem a))))))) ∧ (∀
  (tree :
    DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (low : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 256) (instOfNatNat (nat_lit 256))))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
        @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image s
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) tree →
          @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Separated
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) tree →
            @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Bounded
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) tree low
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))) →
              @Eq.{1} Nat (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278)))))
                  (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) tree) →
                @LE.le.{0} Nat instLENat low
                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278)))) →
                  @LT.lt.{0} Nat instLTNat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278))))
                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))) →
                    s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278))) ∉
                        @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint
                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) tree →
                      ∃ cost t next,
                        And
                          (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                            DecrAlmostLinearSSSP.Decremental.Exact.TriePush.core s cost t)
                          (And
                            (@LE.le.{0} Nat instLENat cost
                              (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40))))
                            (And
                              (@Eq.{1} Nat
                                (t.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278)))))
                                (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root
                                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) next))
                              (And
                                (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image t
                                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) next)
                                (And
                                  (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Separated
                                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) next)
                                  (And
                                    (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Bounded
                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) next low
                                      (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))))
                                    (And
                                      (@Eq.{1}
                                        (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie
                                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                        (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.abstract
                                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) next)
                                        (DecrAlmostLinearSSSP.Decremental.RadixQueue.insert
                                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260))))
                                          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 262) (instOfNatNat (nat_lit 262))))
                                          (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.abstract
                                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) tree)))
                                      (And
                                        (@LE.le.{0} Nat instLENat
                                          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))
                                          (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))))
                                        (And
                                          (@LE.le.{0} (Finset.{0} Nat)
                                            (@Preorder.toLE.{0} (Finset.{0} Nat)
                                              (@PartialOrder.toPreorder.{0} (Finset.{0} Nat)
                                                (@Finset.instPartialOrder.{0} Nat)))
                                            (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint
                                              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) next)
                                            (@Union.union.{0} (Finset.{0} Nat)
                                              (@Finset.instUnion.{0} Nat instDecidableEqNat)
                                              (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint
                                                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) tree)
                                              (@Finset.Ico.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                                                (s.natReg
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))
                                                (t.natReg
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))))))
                                          (And (@Eq.{1} (Nat → Real) t.realMem s.realMem)
                                            (∀ (address : Nat),
                                              @Ne.{1} Nat address
                                                  (s.natReg
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278)))) →
                                                address ∉
                                                    @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                                      tree →
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
                                                    @Eq.{1} Nat (t.natMem address) (s.natMem address))))))))))))) ∧ ((∀ {cmd : DecrAlmostLinearSSSP.Decremental.Structured.Cmd} {s t u : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {a b : Nat},
  DecrAlmostLinearSSSP.Decremental.Structured.Eval cmd s a t →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval cmd s b u →
      And (@Eq.{1} Nat a b) (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Structured.Data t u)) ∧ ((∀ (a : DecrAlmostLinearSSSP.Decremental.Structured.Atom) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.NoStore a.instruction →
    And (@Eq.{1} (Nat → Real) (a.effect s).realMem s.realMem) (@Eq.{1} (Nat → Nat) (a.effect s).natMem s.natMem)) ∧ (∀ {cmd : DecrAlmostLinearSSSP.Decremental.Structured.Cmd} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {cost : Nat},
  DecrAlmostLinearSSSP.Decremental.Structured.Eval cmd s cost t →
    DecrAlmostLinearSSSP.Decremental.Structured.NoMemory cmd →
      And (@Eq.{1} (Nat → Real) t.realMem s.realMem) (@Eq.{1} (Nat → Nat) t.natMem s.natMem)))))) ∧ ((((∀ (a : DecrAlmostLinearSSSP.Decremental.Structured.Atom) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.NoRealStore a.instruction →
    @Eq.{1} (Nat → Real) (a.effect s).realMem s.realMem) ∧ (∀ {cmd : DecrAlmostLinearSSSP.Decremental.Structured.Cmd} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {cost : Nat},
  DecrAlmostLinearSSSP.Decremental.Structured.Eval cmd s cost t →
    DecrAlmostLinearSSSP.Decremental.Structured.NoRealMemory cmd → @Eq.{1} (Nat → Real) t.realMem s.realMem)) ∧ ((∀ k ∉ DecrAlmostLinearSSSP.Decremental.Exact.TriePush.registers,
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.TriePush.core k) ∧ ((∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Exact.TriePush.core k) ∧ (DecrAlmostLinearSSSP.Decremental.Structured.NoRealMemory DecrAlmostLinearSSSP.Decremental.Exact.TriePush.core)))) ∧ (((∀ {s u t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {c d : Nat},
  (DecrAlmostLinearSSSP.Decremental.Structured.Test.natLess
          (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56)))
          (@OfNat.ofNat.{0} Nat (nat_lit 256) (instOfNatNat (nat_lit 256)))).holds
      s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePush.body s c u →
      DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePush.core u d t →
        DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePush.core s
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c d)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          t) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePush.descend s
    (@ite.{1} Nat
      (@LT.lt.{0} Nat instLTNat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260))))
        (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 258) (instOfNatNat (nat_lit 258))))))
      ((s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260)))).decLt
        (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 258) (instOfNatNat (nat_lit 258))))))
      (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
      (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
    (DecrAlmostLinearSSSP.Decremental.Exact.TriePush.descended s))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (h : Nat),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 256) (instOfNatNat (nat_lit 256))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
      And
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.Exact.TriePush.descended s).natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 256) (instOfNatNat (nat_lit 256))))
          h)
        (And
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.Exact.TriePush.descended s).natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 258) (instOfNatNat (nat_lit 258))))
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 258) (instOfNatNat (nat_lit 258))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (And
            (@Eq.{1} Nat
              ((DecrAlmostLinearSSSP.Decremental.Exact.TriePush.descended s).natReg
                (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278))))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 264) (instOfNatNat (nat_lit 264))))
                (@ite.{1} Nat
                  (@LT.lt.{0} Nat instLTNat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260))))
                    (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 258) (instOfNatNat (nat_lit 258))))))
                  ((s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260)))).decLt
                    (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 258) (instOfNatNat (nat_lit 258))))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
            (And
              (@Eq.{1} Nat
                ((DecrAlmostLinearSSSP.Decremental.Exact.TriePush.descended s).natReg
                  (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260))))
                (@ite.{1} Nat
                  (@LT.lt.{0} Nat instLTNat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260))))
                    (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 258) (instOfNatNat (nat_lit 258))))))
                  ((s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260)))).decLt
                    (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 258) (instOfNatNat (nat_lit 258))))))
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260))))
                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260))))
                    (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 258) (instOfNatNat (nat_lit 258))))))))
              (And (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.Exact.TriePush.descended s).natMem s.natMem)
                (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.Exact.TriePush.descended s).realMem
                  s.realMem)))))) ∧ ((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 268) (instOfNatNat (nat_lit 268))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 282) (instOfNatNat (nat_lit 282))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 256) (instOfNatNat (nat_lit 256))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 258) (instOfNatNat (nat_lit 258))) →
              DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
                DecrAlmostLinearSSSP.Decremental.Exact.TriePush.descend k) ∧ (∀ {h : Nat} (b : Bool) (a : Nat) (c o : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h),
  @Eq.{1} Nat
    (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.branch h b a c o))
    a))))))) ∧ ((((((∀ {h : Nat} (b : Bool) (a : Nat) (c o : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h),
  @Eq.{1} (Finset.{0} Nat)
    (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.branch h b a c o))
    (@Union.union.{0} (Finset.{0} Nat) (@Finset.instUnion.{0} Nat instDecidableEqNat)
      (@Finset.Ico.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder a
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
      (@Union.union.{0} (Finset.{0} Nat) (@Finset.instUnion.{0} Nat instDecidableEqNat)
        (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint h c)
        (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint h o)))) ∧ (∀ {h : Nat} (b : Bool) (a : Nat) (c o : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  Iff
    (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image s
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.branch h b a c o))
    (And
      (@Eq.{1} Nat (s.natMem a)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@DecrAlmostLinearSSSP.Decremental.RadixQueue.count h
            (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.abstract h c))
          (@DecrAlmostLinearSSSP.Decremental.RadixQueue.count h
            (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.abstract h o))))
      (And
        (@Eq.{1} Nat
          (s.natMem
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a
              (DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.childOffset b)))
          (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root h c))
        (And
          (@Eq.{1} Nat
            (s.natMem
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a
                (DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.otherOffset b)))
            (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root h o))
          (And (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image s h c)
            (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image s h o))))))) ∧ ((∀ {h : Nat} (b : Bool) (a : Nat) (c o : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h),
  Iff
    (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Separated
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.branch h b a c o))
    (And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) a)
      (And
        (@Disjoint.{0} (Finset.{0} Nat) (@Finset.instPartialOrder.{0} Nat) (@Finset.instOrderBot.{0} Nat)
          (@Finset.Ico.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder a
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
          (@Union.union.{0} (Finset.{0} Nat) (@Finset.instUnion.{0} Nat instDecidableEqNat)
            (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint h c)
            (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint h o)))
        (And
          (@Disjoint.{0} (Finset.{0} Nat) (@Finset.instPartialOrder.{0} Nat) (@Finset.instOrderBot.{0} Nat)
            (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint h c)
            (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint h o))
          (And (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Separated h c)
            (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Separated h o)))))) ∧ (∀ {h : Nat} (b : Bool) (a : Nat) (c o : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h) (r : Nat),
  @LT.lt.{0} Nat instLTNat r (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.branch h b a c o))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a r)))) ∧ (((∀ {h : Nat} (b : Bool) (a : Nat) (c o : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h),
  @LE.le.{0} (Finset.{0} Nat)
    (@Preorder.toLE.{0} (Finset.{0} Nat)
      (@PartialOrder.toPreorder.{0} (Finset.{0} Nat) (@Finset.instPartialOrder.{0} Nat)))
    (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint h c)
    (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.branch h b a c o))) ∧ (∀ {h : Nat} (b : Bool) (a : Nat) (c o : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h),
  @LE.le.{0} (Finset.{0} Nat)
    (@Preorder.toLE.{0} (Finset.{0} Nat)
      (@PartialOrder.toPreorder.{0} (Finset.{0} Nat) (@Finset.instPartialOrder.{0} Nat)))
    (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint h o)
    (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.branch h b a c o)))) ∧ ((∀ (b : Bool),
  And
    (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.childOffset b))
    (@LT.lt.{0} Nat instLTNat (DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.childOffset b)
      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))) ∧ ((∀ (b : Bool),
  @Ne.{1} Nat (DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.otherOffset b)
    (DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.childOffset b)) ∧ (∀ (b : Bool),
  @LT.lt.{0} Nat instLTNat (DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.otherOffset b)
    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))) ∧ ((((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 266) (instOfNatNat (nat_lit 266))) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.TriePush.increment k) ∧ (∀ (h address power : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 256) (instOfNatNat (nat_lit 256))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 264) (instOfNatNat (nat_lit 264)))) address →
        @Eq.{1} Nat (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 258) (instOfNatNat (nat_lit 258))))) power →
          @Ne.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 258) (instOfNatNat (nat_lit 258)))) address →
            have t :=
              DecrAlmostLinearSSSP.Decremental.Exact.TriePush.descended
                (DecrAlmostLinearSSSP.Decremental.Exact.TriePush.incremented s);
            And
              (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                (DecrAlmostLinearSSSP.Decremental.Exact.TriePush.increment.seq
                  DecrAlmostLinearSSSP.Decremental.Exact.TriePush.descend)
                s
                (@ite.{1} Nat
                  (@LT.lt.{0} Nat instLTNat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260))))
                    power)
                  ((s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260)))).decLt power)
                  (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11))))
                t)
              (And (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 256) (instOfNatNat (nat_lit 256)))) h)
                (And
                  (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 258) (instOfNatNat (nat_lit 258))))
                    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 258) (instOfNatNat (nat_lit 258))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (And
                    (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278))))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) address
                        (@ite.{1} Nat
                          (@LT.lt.{0} Nat instLTNat
                            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260)))) power)
                          ((s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260)))).decLt power)
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                    (And
                      (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260))))
                        (@ite.{1} Nat
                          (@LT.lt.{0} Nat instLTNat
                            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260)))) power)
                          ((s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260)))).decLt power)
                          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260))))
                          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260)))) power)))
                      (And
                        (@Eq.{1} (Nat → Nat) t.natMem
                          (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natMem address
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (s.natMem address)
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                        (And (@Eq.{1} (Nat → Real) t.realMem s.realMem)
                          (∀ (k : Nat),
                            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 266) (instOfNatNat (nat_lit 266))) →
                              @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 268) (instOfNatNat (nat_lit 268))) →
                                @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 282) (instOfNatNat (nat_lit 282))) →
                                  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278))) →
                                    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260))) →
                                      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 256) (instOfNatNat (nat_lit 256))) →
                                        @Ne.{1} Nat k
                                            (@OfNat.ofNat.{0} Nat (nat_lit 258) (instOfNatNat (nat_lit 258))) →
                                          @Eq.{1} Nat (t.natReg k) (s.natReg k)))))))))) ∧ ((∀ {h : Nat} (b : Bool) (address : Nat) (child other next : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h)
  (low fresh stop : Nat) (s t : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image s
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.branch h b address child other) →
    @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Separated
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.branch h b address child other) →
      @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Bounded
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.branch h b address child other) low fresh →
        @LE.le.{0} Nat instLENat fresh stop →
          @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image t h next →
            @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Separated h next →
              @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Bounded h next low stop →
                @LE.le.{0} (Finset.{0} Nat)
                    (@Preorder.toLE.{0} (Finset.{0} Nat)
                      (@PartialOrder.toPreorder.{0} (Finset.{0} Nat) (@Finset.instPartialOrder.{0} Nat)))
                    (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint h next)
                    (@Union.union.{0} (Finset.{0} Nat) (@Finset.instUnion.{0} Nat instDecidableEqNat)
                      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint h child)
                      (@Finset.Ico.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder fresh stop)) →
                  @Eq.{1} Nat
                      (@DecrAlmostLinearSSSP.Decremental.RadixQueue.count h
                        (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.abstract h next))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@DecrAlmostLinearSSSP.Decremental.RadixQueue.count h
                          (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.abstract h child))
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                    @Eq.{1} Nat
                        (t.natMem
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) address
                            (DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.childOffset b)))
                        (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root h next) →
                      (∀ (a : Nat),
                          @Ne.{1} Nat a
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) address
                                (DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.childOffset b)) →
                            a ∉ @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint h child →
                              Or (@LT.lt.{0} Nat instLTNat a fresh) (@LE.le.{0} Nat instLENat stop a) →
                                @Eq.{1} Nat (t.natMem a)
                                  (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natMem address
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (s.natMem address)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                    a)) →
                        And
                          (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image t
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                            (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.branch h b address next other))
                          (And
                            (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Separated
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.branch h b address next other))
                            (And
                              (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Bounded
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.branch h b address next other) low
                                stop)
                              (@LE.le.{0} (Finset.{0} Nat)
                                (@Preorder.toLE.{0} (Finset.{0} Nat)
                                  (@PartialOrder.toPreorder.{0} (Finset.{0} Nat) (@Finset.instPartialOrder.{0} Nat)))
                                (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                  (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.branch h b address next other))
                                (@Union.union.{0} (Finset.{0} Nat) (@Finset.instUnion.{0} Nat instDecidableEqNat)
                                  (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                    (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.branch h b address child
                                      other))
                                  (@Finset.Ico.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder fresh stop)))))) ∧ ((∀ {h : Nat} {tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h} {low : Nat}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  (r : @DecrAlmostLinearSSSP.Decremental.Exact.TriePush.Result h tree low s),
  ∀ k ∉ DecrAlmostLinearSSSP.Decremental.Exact.TriePush.registers,
    @Eq.{1} Nat ((@DecrAlmostLinearSSSP.Decremental.Exact.TriePush.Result.final h tree low s r).natReg k) (s.natReg k)) ∧ (∀
  (tree :
    DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (low : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 256) (instOfNatNat (nat_lit 256))))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
        @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image s
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) tree →
          @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Separated
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) tree →
            @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Bounded
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) tree low
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))) →
              @Eq.{1} Nat (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278)))))
                  (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) tree) →
                @LE.le.{0} Nat instLENat low
                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278)))) →
                  @LT.lt.{0} Nat instLTNat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278))))
                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))) →
                    s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278))) ∉
                        @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint
                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) tree →
                      Nonempty.{1}
                        (@DecrAlmostLinearSSSP.Decremental.Exact.TriePush.Result
                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) tree low s))))) ∧ (((∀
  (tree :
    DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (low base : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @DecrAlmostLinearSSSP.Decremental.Exact.TriePush.Ready (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      tree low base s →
    Nonempty.{1}
      (@DecrAlmostLinearSSSP.Decremental.Exact.TriePush.Result
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) tree low s)) ∧ (∀ {h : Nat} (b : Bool) (address : Nat) (child other : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h)
  (low base : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @DecrAlmostLinearSSSP.Decremental.Exact.TriePush.Ready
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.branch h b address child other) low base s →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 264) (instOfNatNat (nat_lit 264)))) address →
      @Eq.{1} Bool b
          (@ite.{1} Bool
            (@LT.lt.{0} Nat instLTNat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260))))
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h))
            ((s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260)))).decLt
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h))
            Bool.false Bool.true) →
        @DecrAlmostLinearSSSP.Decremental.Exact.TriePush.Ready h child low base
          (DecrAlmostLinearSSSP.Decremental.Exact.TriePush.descended
            (DecrAlmostLinearSSSP.Decremental.Exact.TriePush.incremented s)))) ∧ ((∀ {h : Nat} (tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h) (low base : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @DecrAlmostLinearSSSP.Decremental.Exact.TriePush.Ready h tree low base s →
    ∃ cost u,
      And
        (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePush.ensureNode s
          cost u)
        (And (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
          (And
            (@Eq.{1} Nat (u.natReg (@OfNat.ofNat.{0} Nat (nat_lit 264) (instOfNatNat (nat_lit 264))))
              (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root h
                (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.materialize h tree
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))))))
            (And
              (@DecrAlmostLinearSSSP.Decremental.Exact.TriePush.Ready h
                (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.materialize h tree
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))))
                low base u)
              (And
                (@LE.le.{0} Nat instLENat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))
                  (u.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))))
                (And
                  (@LE.le.{0} (Finset.{0} Nat)
                    (@Preorder.toLE.{0} (Finset.{0} Nat)
                      (@PartialOrder.toPreorder.{0} (Finset.{0} Nat) (@Finset.instPartialOrder.{0} Nat)))
                    (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint h
                      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.materialize h tree
                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))))
                    (@Union.union.{0} (Finset.{0} Nat) (@Finset.instUnion.{0} Nat instDecidableEqNat)
                      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint h tree)
                      (@Finset.Ico.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))
                        (u.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))))))
                  (And (@Eq.{1} (Nat → Real) u.realMem s.realMem)
                    (∀ (a : Nat),
                      @Ne.{1} Nat a (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278)))) →
                        Or
                            (@LT.lt.{0} Nat instLTNat a
                              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))))
                            (@LE.le.{0} Nat instLENat
                              (u.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))) a) →
                          @Eq.{1} Nat (u.natMem a) (s.natMem a))))))))) ∧ ((∀ (h : Nat),
  (∀ (child : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h) (low base : Nat)
      (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
      @DecrAlmostLinearSSSP.Decremental.Exact.TriePush.Ready h child low base s →
        Nonempty.{1} (@DecrAlmostLinearSSSP.Decremental.Exact.TriePush.Result h child low s)) →
    ∀
      (tree :
        DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (low base : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
      @DecrAlmostLinearSSSP.Decremental.Exact.TriePush.Ready
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          tree low base s →
        Nonempty.{1}
          (@DecrAlmostLinearSSSP.Decremental.Exact.TriePush.Result
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            tree low s)) ∧ (∀ (h : Nat) (tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h) (low base : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @DecrAlmostLinearSSSP.Decremental.Exact.TriePush.Ready h tree low base s →
    Nonempty.{1} (@DecrAlmostLinearSSSP.Decremental.Exact.TriePush.Result h tree low s))))))) ∧ (((((∀ k ∉ DecrAlmostLinearSSSP.Decremental.Exact.TriePush.registers,
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.TriePush.code k) ∧ (∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Exact.TriePush.code k)) ∧ ((∀ (h : Nat) (tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h) (low base : Nat)
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
                                                          @Eq.{1} Nat (t.natMem address) (s.natMem address)))))))))))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePop.decrement s
    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
    (DecrAlmostLinearSSSP.Decremental.Exact.TriePop.decremented s)))) ∧ (((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
    @Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.Exact.TriePop.decremented s).natMem
      (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natMem
        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 264) (instOfNatNat (nat_lit 264))))
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
          (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 264) (instOfNatNat (nat_lit 264)))))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePop.leftPointer s
    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
    (DecrAlmostLinearSSSP.Decremental.Exact.TriePop.leftPointerData s))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePop.leafFinish s
    (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
    (DecrAlmostLinearSSSP.Decremental.Exact.TriePop.leafFinished s)) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePop.leaf s
    (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))
    (DecrAlmostLinearSSSP.Decremental.Exact.TriePop.leafData s)) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePop.start s
    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
    (DecrAlmostLinearSSSP.Decremental.Exact.TriePop.started s)))))) ∧ ((((∀ k ∉ DecrAlmostLinearSSSP.Decremental.Exact.TriePop.registers,
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.TriePop.core k) ∧ (∀ (k : Nat), DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Exact.TriePop.core k)) ∧ ((DecrAlmostLinearSSSP.Decremental.Structured.NoRealMemory DecrAlmostLinearSSSP.Decremental.Exact.TriePop.core) ∧ ((∀ {s u t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {c d : Nat},
  (DecrAlmostLinearSSSP.Decremental.Structured.Test.natLess
          (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56)))
          (@OfNat.ofNat.{0} Nat (nat_lit 256) (instOfNatNat (nat_lit 256)))).holds
      s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePop.body s c u →
      DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePop.core u d t →
        DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePop.core s
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c d)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          t) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    ∃ c,
      And
        (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePop.leftCount s c
          (DecrAlmostLinearSSSP.Decremental.Exact.TriePop.leftCountData s))
        (@LE.le.{0} Nat instLENat c (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))) ∧ (((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    ∃ c,
      And
        (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePop.choose s c
          (DecrAlmostLinearSSSP.Decremental.Exact.TriePop.chosen s))
        (@LE.le.{0} Nat instLENat c (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    ∃ c,
      And
        (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePop.descend s c
          (DecrAlmostLinearSSSP.Decremental.Exact.TriePop.descended s))
        (@LE.le.{0} Nat instLENat c (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (h : Nat),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 256) (instOfNatNat (nat_lit 256))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
        have left :=
          s.natMem
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 264) (instOfNatNat (nat_lit 264))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))));
        have count :=
          @ite.{1} Nat (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) left)
            (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) left) (s.natMem left)
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)));
        And
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.Exact.TriePop.descended s).natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 264) (instOfNatNat (nat_lit 264))))
            (@ite.{1} Nat (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) count)
              (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) count) left
              (s.natMem
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 264) (instOfNatNat (nat_lit 264))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
          (And
            (@Eq.{1} Nat
              ((DecrAlmostLinearSSSP.Decremental.Exact.TriePop.descended s).natReg
                (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260))))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260))))
                (@ite.{1} Nat
                  (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) count)
                  (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) count)
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 258) (instOfNatNat (nat_lit 258))))))))
            (And
              (@Eq.{1} Nat
                ((DecrAlmostLinearSSSP.Decremental.Exact.TriePop.descended s).natReg
                  (@OfNat.ofNat.{0} Nat (nat_lit 256) (instOfNatNat (nat_lit 256))))
                h)
              (And
                (@Eq.{1} Nat
                  ((DecrAlmostLinearSSSP.Decremental.Exact.TriePop.descended s).natReg
                    (@OfNat.ofNat.{0} Nat (nat_lit 258) (instOfNatNat (nat_lit 258))))
                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 258) (instOfNatNat (nat_lit 258))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (And (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.Exact.TriePop.descended s).natMem s.natMem)
                  (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.Exact.TriePop.descended s).realMem
                    s.realMem)))))) ∧ ((∀
  k ∉
    @Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 256) (instOfNatNat (nat_lit 256)))
      (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 258) (instOfNatNat (nat_lit 258)))
        (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260)))
          (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 264) (instOfNatNat (nat_lit 264)))
            (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 268) (instOfNatNat (nat_lit 268)))
              (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278)))
                (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 282) (instOfNatNat (nat_lit 282)))
                  (@Singleton.singleton.{0, 0} Nat (Finset.{0} Nat) (@Finset.instSingleton.{0} Nat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 284) (instOfNatNat (nat_lit 284)))))))))),
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.TriePop.descend k) ∧ (∀ (address payload value : Nat) (items : List.{0} (Prod.{0, 0} Nat Nat))
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 264) (instOfNatNat (nat_lit 264)))) address →
      @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image s
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.leaf address
            (@List.cons.{0} (Prod.{0, 0} Nat Nat) (@Prod.mk.{0, 0} Nat Nat payload value) items)) →
        @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Separated
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.leaf address
              (@List.cons.{0} (Prod.{0, 0} Nat Nat) (@Prod.mk.{0, 0} Nat Nat payload value) items)) →
          And
            (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.Exact.TriePop.leafData s).natMem
              (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
                (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natMem address
                  (@List.length.{0} (Prod.{0, 0} Nat Nat) items))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) address
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (DecrAlmostLinearSSSP.Decremental.Exact.Payload.root items)))
            (And
              (@Eq.{1} Nat
                ((DecrAlmostLinearSSSP.Decremental.Exact.TriePop.leafData s).natReg
                  (@OfNat.ofNat.{0} Nat (nat_lit 262) (instOfNatNat (nat_lit 262))))
                value)
              (And
                (@Eq.{1} Nat
                  ((DecrAlmostLinearSSSP.Decremental.Exact.TriePop.leafData s).natReg
                    (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260))))
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260)))))
                (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.Exact.TriePop.leafData s).realMem s.realMem))))))))))) := by
  exact ⟨⟨⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.Allocate.item_nat_frame,DecrAlmostLinearSSSP.Decremental.Exact.Allocate.item_real_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.TriePush.ensureNode_eval,DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.materialize_root_empty⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.materialize_nonempty,DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.materialize_insert⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.materialize_empty_image,⟨DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.materialize_empty_separated,DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.materialize_empty_footprint⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.TriePush.ensureNode_existing,DecrAlmostLinearSSSP.Decremental.Exact.TriePush.ensureNode_nat_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.TriePush.ensureNode_real_frame,DecrAlmostLinearSSSP.Decremental.Exact.TriePush.ensureNode_located⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.TriePush.increment_eval,DecrAlmostLinearSSSP.Decremental.Exact.TriePush.increment_fields⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.TriePush.leafPrepare_eval,⟨DecrAlmostLinearSSSP.Decremental.Exact.TriePush.leafPrepare_fields,DecrAlmostLinearSSSP.Decremental.Exact.TriePush.start_eval⟩⟩⟩⟩⟩,⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.TriePush.start_fields,DecrAlmostLinearSSSP.Decremental.Exact.TriePush.leafFinish_eval⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.TriePush.leafFinish_values,DecrAlmostLinearSSSP.Decremental.Exact.TriePush.leafFinish_nat_frame⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.TriePush.leafFinish_image,DecrAlmostLinearSSSP.Decremental.Exact.TriePush.core_zero⟩,⟨DecrAlmostLinearSSSP.Decremental.Structured.Eval.deterministic,⟨DecrAlmostLinearSSSP.Decremental.Structured.atom_no_memory,DecrAlmostLinearSSSP.Decremental.Structured.Eval.no_memory⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Structured.atom_no_real_memory,DecrAlmostLinearSSSP.Decremental.Structured.Eval.no_real_memory⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.TriePush.core_nat_frame,⟨DecrAlmostLinearSSSP.Decremental.Exact.TriePush.core_real_frame,DecrAlmostLinearSSSP.Decremental.Exact.TriePush.core_no_real_memory⟩⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.TriePush.core_unroll,DecrAlmostLinearSSSP.Decremental.Exact.TriePush.descend_eval⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.TriePush.descend_values,⟨DecrAlmostLinearSSSP.Decremental.Exact.TriePush.descend_nat_frame,DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.branch_root⟩⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.branch_footprint,DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.branch_image⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.branch_separated,DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.branch_field_mem⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.branch_child_subset,DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.branch_other_subset⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.childOffset_pos,⟨DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.offsets_ne,DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.otherOffset_lt⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.TriePush.increment_nat_frame,DecrAlmostLinearSSSP.Decremental.Exact.TriePush.descent_node_step⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.branch_rebuild,⟨DecrAlmostLinearSSSP.Decremental.Exact.TriePush.Result.nat_frame,DecrAlmostLinearSSSP.Decremental.Exact.TriePush.result_zero⟩⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.TriePush.ready_zero,DecrAlmostLinearSSSP.Decremental.Exact.TriePush.child_ready⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.TriePush.ensure_ready,⟨DecrAlmostLinearSSSP.Decremental.Exact.TriePush.result_succ,DecrAlmostLinearSSSP.Decremental.Exact.TriePush.core_result⟩⟩⟩⟩⟩,⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.TriePush.code_nat_frame,DecrAlmostLinearSSSP.Decremental.Exact.TriePush.code_real_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.TriePush.code_result,DecrAlmostLinearSSSP.Decremental.Exact.TriePop.decrement_eval⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.TriePop.decrement_fields,DecrAlmostLinearSSSP.Decremental.Exact.TriePop.leftPointer_eval⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.TriePop.leafFinish_eval,⟨DecrAlmostLinearSSSP.Decremental.Exact.TriePop.leaf_eval,DecrAlmostLinearSSSP.Decremental.Exact.TriePop.start_eval⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.TriePop.core_nat_frame,DecrAlmostLinearSSSP.Decremental.Exact.TriePop.core_real_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.TriePop.core_no_real_memory,⟨DecrAlmostLinearSSSP.Decremental.Exact.TriePop.core_unroll,DecrAlmostLinearSSSP.Decremental.Exact.TriePop.leftCount_eval⟩⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.TriePop.choose_eval,DecrAlmostLinearSSSP.Decremental.Exact.TriePop.descend_eval⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.TriePop.descend_fields,⟨DecrAlmostLinearSSSP.Decremental.Exact.TriePop.descend_nat_frame,DecrAlmostLinearSSSP.Decremental.Exact.TriePop.leaf_fields⟩⟩⟩⟩⟩⟩⟩
