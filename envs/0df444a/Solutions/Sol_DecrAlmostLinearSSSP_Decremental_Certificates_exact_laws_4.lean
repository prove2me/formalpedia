-- Prove2me | solution 1 for DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T11:14:37.896116+00:00
-- url     : https://prove2.me/submissions/8075e393-d303-411a-adcf-375fd84bf67a

import Definitions.Def_DecrAlmostLinearSSSP_RAMFoundation
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_1
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_2
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_3
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
open scoped ENNReal NNReal
attribute [local instance] Classical.propDecidable
theorem DecrAlmostLinearSSSP.Decremental.RadixQueue.count_pop : ∀ {height : Nat} (t : DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height) (key value : Nat)
  (next : DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height),
  @Eq.{1} (Option.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height))))
      (@DecrAlmostLinearSSSP.Decremental.RadixQueue.pop height t)
      (@Option.some.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height)))
        (@Prod.mk.{0, 0} Nat (Prod.{0, 0} Nat (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height)) key
          (@Prod.mk.{0, 0} Nat (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height) value next))) →
    @Eq.{1} Nat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@DecrAlmostLinearSSSP.Decremental.RadixQueue.count height next)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@DecrAlmostLinearSSSP.Decremental.RadixQueue.count height t) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_1.1.1.1.2.2.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.node_field_mem : ∀ {height : Nat} (address : Nat) (left right : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie height)
  (offset : Nat),
  @LT.lt.{0} Nat instLTNat offset (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) height
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.node height address left right))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) address offset) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.1.1.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.leaf_field_mem : ∀ (address : Nat) (items : List.{0} (Prod.{0, 0} Nat Nat)) (offset : Nat),
  @LT.lt.{0} Nat instLTNat offset (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.leaf address items))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) address offset) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.1.2.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Separated.left_field : ∀ {height address : Nat} {left right : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie height},
  @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Separated
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) height
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.node height address left right) →
    ∀ (offset : Nat),
      @LT.lt.{0} Nat instLTNat offset (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
        @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) address offset ∉
          @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint height left := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.1.2.1.2.1.1
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
theorem DecrAlmostLinearSSSP.Decremental.Exact.TriePush.start_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePush.start s
    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
    (DecrAlmostLinearSSSP.Decremental.Exact.TriePush.started s) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_3.1.1.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.TriePush.start_fields : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
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
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 246) (instOfNatNat (nat_lit 246)))))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_3.1.2.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.TriePush.core_nat_frame : ∀ k ∉ DecrAlmostLinearSSSP.Decremental.Exact.TriePush.registers,
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.TriePush.core k := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_3.1.2.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.TriePush.core_real_frame : ∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Exact.TriePush.core k := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_3.1.2.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.TriePush.core_unroll : ∀ {s u t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {c d : Nat},
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
          t := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_3.1.2.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.TriePush.descend_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePush.descend s
    (@ite.{1} Nat
      (@LT.lt.{0} Nat instLTNat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260))))
        (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 258) (instOfNatNat (nat_lit 258))))))
      ((s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260)))).decLt
        (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 258) (instOfNatNat (nat_lit 258))))))
      (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
      (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
    (DecrAlmostLinearSSSP.Decremental.Exact.TriePush.descended s) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_3.1.2.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.branch_root : ∀ {h : Nat} (b : Bool) (a : Nat) (c o : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h),
  @Eq.{1} Nat
    (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.branch h b a c o))
    a := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_3.1.2.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.branch_footprint : ∀ {h : Nat} (b : Bool) (a : Nat) (c o : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h),
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
        (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint h o))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_3.2.1.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.branch_image : ∀ {h : Nat} (b : Bool) (a : Nat) (c o : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h)
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
            (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image s h o))))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_3.2.1.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.branch_separated : ∀ {h : Nat} (b : Bool) (a : Nat) (c o : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h),
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
            (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Separated h o))))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_3.2.1.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.branch_field_mem : ∀ {h : Nat} (b : Bool) (a : Nat) (c o : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h) (r : Nat),
  @LT.lt.{0} Nat instLTNat r (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.branch h b a c o))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a r) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_3.2.1.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.branch_child_subset : ∀ {h : Nat} (b : Bool) (a : Nat) (c o : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h),
  @LE.le.{0} (Finset.{0} Nat)
    (@Preorder.toLE.{0} (Finset.{0} Nat)
      (@PartialOrder.toPreorder.{0} (Finset.{0} Nat) (@Finset.instPartialOrder.{0} Nat)))
    (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint h c)
    (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.branch h b a c o)) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_3.2.1.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.childOffset_pos : ∀ (b : Bool),
  And
    (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.childOffset b))
    (@LT.lt.{0} Nat instLTNat (DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.childOffset b)
      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_3.2.1.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.otherOffset_lt : ∀ (b : Bool),
  @LT.lt.{0} Nat instLTNat (DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.otherOffset b)
    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_3.2.1.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.TriePush.Result.nat_frame : ∀ {h : Nat} {tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h} {low : Nat}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  (r : @DecrAlmostLinearSSSP.Decremental.Exact.TriePush.Result h tree low s),
  ∀ k ∉ DecrAlmostLinearSSSP.Decremental.Exact.TriePush.registers,
    @Eq.{1} Nat ((@DecrAlmostLinearSSSP.Decremental.Exact.TriePush.Result.final h tree low s r).natReg k) (s.natReg k) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_3.2.1.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.TriePush.result_zero : ∀
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
                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) tree low s) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_3.2.1.2.1.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.TriePush.result_succ : ∀ (h : Nat),
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
            tree low s) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_3.2.1.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.TriePush.core_result : ∀ (h : Nat) (tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h) (low base : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @DecrAlmostLinearSSSP.Decremental.Exact.TriePush.Ready h tree low base s →
    Nonempty.{1} (@DecrAlmostLinearSSSP.Decremental.Exact.TriePush.Result h tree low s) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_3.2.1.2.2.2.2.2
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
theorem DecrAlmostLinearSSSP.Decremental.Exact.TriePop.decrement_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePop.decrement s
    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
    (DecrAlmostLinearSSSP.Decremental.Exact.TriePop.decremented s) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_3.2.2.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.TriePop.decrement_fields : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
    @Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.Exact.TriePop.decremented s).natMem
      (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natMem
        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 264) (instOfNatNat (nat_lit 264))))
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
          (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 264) (instOfNatNat (nat_lit 264)))))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_3.2.2.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.TriePop.leaf_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePop.leaf s
    (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))
    (DecrAlmostLinearSSSP.Decremental.Exact.TriePop.leafData s) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_3.2.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.TriePop.start_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePop.start s
    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
    (DecrAlmostLinearSSSP.Decremental.Exact.TriePop.started s) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_3.2.2.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.TriePop.core_nat_frame : ∀ k ∉ DecrAlmostLinearSSSP.Decremental.Exact.TriePop.registers,
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.TriePop.core k := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_3.2.2.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.TriePop.core_real_frame : ∀ (k : Nat), DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Exact.TriePop.core k := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_3.2.2.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.TriePop.core_unroll : ∀ {s u t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {c d : Nat},
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
          t := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_3.2.2.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.TriePop.descend_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    ∃ c,
      And
        (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePop.descend s c
          (DecrAlmostLinearSSSP.Decremental.Exact.TriePop.descended s))
        (@LE.le.{0} Nat instLENat c (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_3.2.2.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.TriePop.descend_fields : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (h : Nat),
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
                    s.realMem))))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_3.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.TriePop.leaf_fields : ∀ (address payload value : Nat) (items : List.{0} (Prod.{0, 0} Nat Nat))
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
                (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.Exact.TriePop.leafData s).realMem s.realMem))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_3.2.2.2.2.2.2.2
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
lemma leaf_image (address payload value : ℕ) (items : List (ℕ × ℕ)) (low high : ℕ) (s : Data)
    (h1 : s.natReg 26 = 1) (hptr : s.natReg 264 = address)
    (hi : (LocatedTrie.leaf address ((payload,value)::items)).Image s)
    (hs : (LocatedTrie.leaf address ((payload,value)::items)).Separated)
    (hb : (LocatedTrie.leaf address ((payload,value)::items)).Bounded low high) :
    let next := LocatedTrie.leaf address items
    next.Image (leafData s) ∧ next.Separated ∧ next.Bounded low high ∧
      next.footprint ⊆ (LocatedTrie.leaf address ((payload,value)::items)).footprint ∧
      (∀ a, a ∉ (LocatedTrie.leaf address ((payload,value)::items)).footprint → (leafData s).natMem a = s.natMem a) := by
  have ht := (leaf_fields address payload value items s h1 hptr hi hs).1
  have hsubset : (LocatedTrie.leaf address items).footprint ⊆ (LocatedTrie.leaf address ((payload,value)::items)).footprint := by
    intro a ha
    simp only [LocatedTrie.footprint,Payload.footprint,Finset.mem_union] at ha ⊢
    tauto
  have hnot (a : ℕ) (ha : a ∈ Payload.footprint items) (r : ℕ) (hr : r<4) : a ≠ address+r := by
    intro heq
    exact Finset.disjoint_left.mp hs.2.1
      (show address+r ∈ Finset.Ico address (address+4) from Finset.mem_Ico.mpr ⟨by omega,by omega⟩)
      (Finset.mem_union_right _ (heq ▸ ha))
  have hframe (a : ℕ) (ha : a ∈ Payload.footprint items) : (leafData s).natMem a = s.natMem a := by
    rw [ht,Function.update_of_ne (hnot a ha 3 (by omega)),
      Function.update_of_ne (by simpa only [Nat.add_zero] using hnot a ha 0 (by omega))]
  refine ⟨?_,?_,fun a ha => hb a (hsubset ha),hsubset,?_⟩
  · refine ⟨?_,?_,hi.2.2.2.2.frame hframe⟩
    · rw [ht,Function.update_of_ne (by omega),Function.update_self]
    · rw [ht,Function.update_self]
  · exact ⟨hs.1,Finset.disjoint_union_right.mp hs.2.1 |>.2,hs.2.2.2.2⟩
  · intro a ha
    have hn0 : a ≠ address := by
      intro hh;apply ha;rw [hh];simpa only [Nat.add_zero] using LocatedTrie.leaf_field_mem address ((payload,value)::items) 0 (by omega)
    have hn3 : a ≠ address+3 := by
      intro hh;apply ha;rw [hh];exact LocatedTrie.leaf_field_mem address ((payload,value)::items) 3 (by omega)
    rw [ht,Function.update_of_ne hn3,Function.update_of_ne hn0]
end DecrAlmostLinearSSSP.Decremental.Exact.TriePop
end s55
section s56
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePop
open Structured
lemma Result.nat_frame {h : ℕ} {tree : LocatedTrie h} {s : Data} (r : Result tree s)
    (k : ℕ) (hk : k ∉ registers) : r.final.natReg k = s.natReg k := r.eval.nat_frame (core_nat_frame k hk)
lemma result_zero (tree : LocatedTrie 0) (low base : ℕ) (s : Data) (hr : Ready tree low base s) :
    Nonempty (Result tree s) := by
  cases tree with
  | empty => have hh := hr.positive;simpa [LocatedTrie.abstract,RadixQueue.count] using hh
  | leaf address items =>
    cases items with
    | nil => have hh := hr.positive;simpa [LocatedTrie.abstract,RadixQueue.count] using hh
    | cons item items =>
      rcases item with ⟨payload,value⟩
      obtain ⟨hi,hs,hb,hf,hm⟩ := leaf_image address payload value items low (s.natReg 244) s hr.unit hr.current hr.image hr.separated hr.bounded
      have hv := leaf_fields address payload value items s hr.unit hr.current hr.image hr.separated
      have hl : Eval loop s 2 s := Eval.loopNo s (by simp [Test.holds,hr.zero,hr.height])
      refine ⟨⟨12,leafData s,.leaf address items,0,Eval.seq hl (leaf_eval s),by omega,?_,?_,hi,hs,rfl,hf,hv.2.2.2,hm⟩⟩
      · rw [hv.2.1];rfl
      · simpa only [Nat.add_zero] using hv.2.2.1
end DecrAlmostLinearSSSP.Decremental.Exact.TriePop
end s56
section s57
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact
open Structured
lemma LocatedTrie.Image.read_count {h : ℕ} (tree : LocatedTrie h) (s : Data)
    (hi : tree.Image s) (hs : tree.Separated) :
    (if 0<tree.root then s.natMem tree.root else 0) = RadixQueue.count tree.abstract := by
  cases tree with
  | empty => simp [LocatedTrie.root,LocatedTrie.abstract,RadixQueue.count]
  | leaf a items =>
    have hpos : 0<a := hs.1
    change (if 0<a then s.natMem a else 0) = _
    rw [if_pos hpos]
    simpa only [LocatedTrie.abstract,RadixQueue.count,List.length_map] using hi.1
  | node a l r =>
    have hpos : 0<a := hs.1
    change (if 0<a then s.natMem a else 0) = _
    rw [if_pos hpos]
    exact hi.1
namespace TriePop
lemma decrement_nat_frame (k : ℕ) (hk : k ≠ 266) : NatFrame decrement k := by
  simp [decrement,decrementAtoms,Structured.sequence,NatFrame,writesNat,Ne.symm hk]
lemma body_nat_frame (k : ℕ) (hk : k ∉ registers) : NatFrame body k := (core_nat_frame k hk).1
lemma node_step (h address : ℕ) (left right : LocatedTrie h) (low base : ℕ) (s : Data)
    (hr : Ready (.node address left right) low base s) :
    let q := descended (decremented s)
    ∃ c, Eval body s c q ∧ c ≤ 18 ∧
      q.natReg 264 = (if 0<RadixQueue.count left.abstract then left.root else right.root) ∧
      q.natReg 260 = s.natReg 260+(if 0<RadixQueue.count left.abstract then 0 else 2^h) ∧
      q.natReg 256 = h ∧ q.natReg 258 = s.natReg 258-1 ∧
      q.natMem = Function.update s.natMem address (s.natMem address-1) ∧
      q.realMem = s.realMem := by
  let v := decremented s
  have hv := decrement_eval s
  have hvf (k : ℕ) (hk : k ≠ 266) := hv.nat_frame (decrement_nat_frame k hk)
  have hvz : v.natReg 56 = 0 := (hvf 56 (by omega)).trans hr.zero
  have hv1 : v.natReg 26 = 1 := (hvf 26 (by omega)).trans hr.unit
  have hvheight : v.natReg 256 = h+1 := (hvf 256 (by omega)).trans hr.height
  have hvptr : v.natReg 264 = address := (hvf 264 (by omega)).trans hr.current
  have hvm : v.natMem = Function.update s.natMem address (s.natMem address-1) := by
    simpa only [hr.current,LocatedTrie.root] using decrement_fields s hr.unit
  have hvLeftPtr : v.natMem (v.natReg 264+1) = left.root := by
    rw [hvptr,hvm,Function.update_of_ne (by omega)]
    exact hr.image.2.1
  have hvRightPtr : v.natMem (v.natReg 264+2) = right.root := by
    rw [hvptr,hvm,Function.update_of_ne (by omega)]
    exact hr.image.2.2.1
  have hleftFrame (a : ℕ) (ha : a ∈ left.footprint) : v.natMem a = s.natMem a := by
    rw [hvm,Function.update_of_ne (by intro hh;subst a;exact hr.separated.left_field 0 (by omega) (by simpa only [Nat.add_zero] using ha))]
  have hvLeft := hr.image.2.2.2.1.frame hleftFrame
  have hvCount := LocatedTrie.Image.read_count left v hvLeft hr.separated.2.2.2.1
  have hpPtr : s.natReg 258 = base+h := by have := hr.powerPtr (by omega);omega
  have hfield := hr.bounded _ (LocatedTrie.node_field_mem address left right 0 (by omega))
  have hpNe : s.natReg 258 ≠ address := by have := hr.powersHigh;omega
  have hvPower : v.natMem (v.natReg 258) = 2^h := by
    rw [hvf 258 (by omega),hvm,Function.update_of_ne hpNe,hpPtr]
    exact hr.powers h (by omega)
  obtain ⟨c,he,hc⟩ := descend_eval v hvz
  have hf := descend_fields v h hvz hv1 hvheight
  simp only [hvLeftPtr,hvCount,hvRightPtr,hvPower] at hf
  refine ⟨3+c,Eval.seq hv he,by omega,hf.1,?_,hf.2.2.1,?_,hf.2.2.2.2.1.trans hvm,hf.2.2.2.2.2⟩
  · rw [hf.2.1,hvf 260 (by omega)]
  · rw [hf.2.2.2.1,hvf 258 (by omega)]
end TriePop
end DecrAlmostLinearSSSP.Decremental.Exact
end s57
section s58
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie
lemma branch_delete_rebuild {h : ℕ} (b : Bool) (address : ℕ) (child other next : LocatedTrie h)
    (s t : Structured.Data)
    (hi : (branch b address child other).Image s)
    (hs : (branch b address child other).Separated)
    (hnext : next.Image t) (hsnext : next.Separated)
    (hfoot : next.footprint ⊆ child.footprint)
    (hcount : RadixQueue.count next.abstract+1 = RadixQueue.count child.abstract)
    (hroot : next.root = child.root)
    (hframe : ∀ a, a ∉ child.footprint → t.natMem a = Function.update s.natMem address (s.natMem address-1) a) :
    (branch b address next other).Image t ∧ (branch b address next other).Separated ∧
      (branch b address next other).footprint ⊆ (branch b address child other).footprint := by
  have hi' := (branch_image b address child other s).mp hi
  have hs' := (branch_separated b address child other).mp hs
  have hfieldNot (r : ℕ) (hr : r<4) : address+r ∉ child.footprint := by
    intro hm
    exact Finset.disjoint_left.mp hs'.2.1
      (show address+r ∈ Finset.Ico address (address+4) from Finset.mem_Ico.mpr ⟨by omega,by omega⟩)
      (Finset.mem_union_left _ hm)
  have hotherNot (a : ℕ) (ha : a ∈ other.footprint) : a ∉ child.footprint :=
    fun hh => Finset.disjoint_left.mp hs'.2.2.1 hh ha
  have hotherField (a : ℕ) (ha : a ∈ other.footprint) : a ≠ address := by
    intro hh
    exact Finset.disjoint_left.mp hs'.2.1
      (show address ∈ Finset.Ico address (address+4) from Finset.mem_Ico.mpr ⟨le_rfl,by omega⟩)
      (Finset.mem_union_right _ (hh ▸ ha))
  have hotherFrame (a : ℕ) (ha : a ∈ other.footprint) : t.natMem a = s.natMem a := by
    rw [hframe a (hotherNot a ha),Function.update_of_ne (hotherField a ha)]
  have htImage : (branch b address next other).Image t := by
    apply (branch_image b address next other t).mpr
    refine ⟨?_,?_,?_,hnext,hi'.2.2.2.2.frame hotherFrame⟩
    · rw [hframe address (by simpa only [Nat.add_zero] using hfieldNot 0 (by omega)),Function.update_self,hi'.1]
      omega
    · rw [hframe _ (hfieldNot _ (childOffset_pos b).2),Function.update_of_ne (by have := (childOffset_pos b).1;omega),hroot]
      exact hi'.2.1
    · rw [hframe _ (hfieldNot _ (otherOffset_lt b)),Function.update_of_ne (by cases b <;> simp [otherOffset])]
      exact hi'.2.2.1
  have htSep : (branch b address next other).Separated := by
    apply (branch_separated b address next other).mpr
    refine ⟨hs'.1,?_,?_,hsnext,hs'.2.2.2.2⟩
    · apply Finset.disjoint_left.mpr
      intro a ha hb
      rcases Finset.mem_union.mp hb with hn | ho
      · exact Finset.disjoint_left.mp hs'.2.1 ha (Finset.mem_union_left _ (hfoot hn))
      · exact Finset.disjoint_left.mp hs'.2.1 ha (Finset.mem_union_right _ ho)
    · exact Finset.disjoint_left.mpr (fun a hn ho => Finset.disjoint_left.mp hs'.2.2.1 (hfoot hn) ho)
  refine ⟨htImage,htSep,?_⟩
  intro a ha
  rw [branch_footprint] at ha ⊢
  rcases Finset.mem_union.mp ha with hf | hc
  · exact Finset.mem_union_left _ hf
  · rcases Finset.mem_union.mp hc with hn | ho
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ (hfoot hn))
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ ho)
end DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie
end s58
section s59
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePop
open Structured
lemma result_succ (h : ℕ)
    (ih : ∀ (child : LocatedTrie h) (low base : ℕ) (s : Data), Ready child low base s → Nonempty (Result child s))
    (tree : LocatedTrie (h+1)) (low base : ℕ) (s : Data) (hr : Ready tree low base s) :
    Nonempty (Result tree s) := by
  cases tree with
  | empty => have hh := hr.positive;simpa [LocatedTrie.abstract,RadixQueue.count] using hh
  | node address left right =>
    let b : Bool := if 0<RadixQueue.count left.abstract then false else true
    let child := if b then right else left
    let other := if b then left else right
    have hbranch : LocatedTrie.node address left right = LocatedTrie.branch b address child other := by
      cases hb : b <;> simp [LocatedTrie.branch,child,other,hb]
    let q := descended (decremented s)
    obtain ⟨c,he,hc,hcurrent,hkey,hheight,hptr,hmem,hreal⟩ := node_step h address left right low base s hr
    have hn (k : ℕ) (hk : k ∉ registers) : q.natReg k = s.natReg k := he.nat_frame (body_nat_frame k hk)
    have halloc : q.natReg 244 = s.natReg 244 := hn 244 (by norm_num [registers])
    have hi : (LocatedTrie.branch b address child other).Image s := by rw [← hbranch];exact hr.image
    have hs : (LocatedTrie.branch b address child other).Separated := by rw [← hbranch];exact hr.separated
    have hb : (LocatedTrie.branch b address child other).Bounded low (s.natReg 244) := by rw [← hbranch];exact hr.bounded
    have hi' := (LocatedTrie.branch_image b address child other s).mp hi
    have hs' := (LocatedTrie.branch_separated b address child other).mp hs
    have hfield (r : ℕ) (hh : r<4) := hb _ (LocatedTrie.branch_field_mem b address child other r hh)
    have hchildFrame (a : ℕ) (ha : a ∈ child.footprint) : q.natMem a = s.natMem a := by
      rw [hmem,Function.update_of_ne (by
        intro hh;subst a
        exact Finset.disjoint_left.mp hs'.2.1
          (show address ∈ Finset.Ico address (address+4) from Finset.mem_Ico.mpr ⟨le_rfl,by omega⟩)
          (Finset.mem_union_left _ ha))]
    have hqCurrent : q.natReg 264 = child.root := by
      by_cases hk : 0<RadixQueue.count left.abstract
      · simpa [child,b,hk] using hcurrent
      · simpa [child,b,hk] using hcurrent
    have hpositive : 0<RadixQueue.count child.abstract := by
      have ht := hr.positive
      simp only [LocatedTrie.abstract,RadixQueue.count] at ht
      unfold child b
      split_ifs <;> simp_all <;> omega
    have hq : Ready child low base q := by
      refine ⟨(hn 56 (by norm_num [registers])).trans hr.zero,
        (hn 26 (by norm_num [registers])).trans hr.unit,hheight,
        hi'.2.2.2.1.frame hchildFrame,hs'.2.2.2.1,?_,hqCurrent,hpositive,?_,?_,?_⟩
      · intro a ha;rw [halloc];exact hb a (LocatedTrie.branch_child_subset b address child other ha)
      · intro j hj
        rw [hmem,Function.update_of_ne (by have := hfield 0 (by omega);have := hr.powersHigh;omega)]
        exact hr.powers j (by omega)
      · have := hr.powersHigh;omega
      · intro hh
        rw [hptr]
        have := hr.powerPtr (by omega)
        omega
    obtain ⟨r⟩ := ih child low base q hq
    let next := LocatedTrie.branch b address r.next other
    have hrCount := RadixQueue.count_pop child.abstract r.key (r.final.natReg 262) r.next.abstract r.pop
    have hrFrame (a : ℕ) (ha : a ∉ child.footprint) :
        r.final.natMem a = Function.update s.natMem address (s.natMem address-1) a := by
      rw [r.frame a ha,hmem]
    obtain ⟨htImage,htSep,htFoot⟩ := LocatedTrie.branch_delete_rebuild b address child other r.next s r.final
      hi hs r.image r.separated r.footprint hrCount r.root hrFrame
    let offset := if 0<RadixQueue.count left.abstract then 0 else 2^h
    have htPop : RadixQueue.pop (LocatedTrie.node address left right).abstract =
        some (offset+r.key,r.final.natReg 262,next.abstract) := by
      have hp := r.pop
      by_cases hk : 0<RadixQueue.count left.abstract
      · have hne : RadixQueue.count left.abstract ≠ 0 := by omega
        simp only [child,b,if_pos hk,Bool.false_eq_true,if_false] at hp
        simp only [LocatedTrie.abstract,RadixQueue.pop,if_neg hne,hp]
        simp [offset,next,LocatedTrie.branch,LocatedTrie.abstract,other,b,if_pos hk]
      · have hz : RadixQueue.count left.abstract = 0 := by omega
        simp only [child,b,if_neg hk,if_true] at hp
        simp only [LocatedTrie.abstract,RadixQueue.pop,if_pos hz,hp]
        simp [offset,next,LocatedTrie.branch,LocatedTrie.abstract,other,b,if_neg hk]
    have htKey : r.final.natReg 260 = s.natReg 260+(offset+r.key) := by
      rw [r.keyReg,hkey];omega
    have htFrame (a : ℕ) (ha : a ∉ (LocatedTrie.node address left right).footprint) : r.final.natMem a = s.natMem a := by
      have hnChild : a ∉ child.footprint := by
        intro hh;apply ha;rw [hbranch];exact LocatedTrie.branch_child_subset b address child other hh
      have hnAddress : a ≠ address := by
        intro hh;apply ha;rw [hh];simpa only [Nat.add_zero] using LocatedTrie.node_field_mem address left right 0 (by omega)
      rw [hrFrame a hnChild,Function.update_of_ne hnAddress]
    refine ⟨⟨c+r.cost+2,r.final,next,offset+r.key,
      core_unroll (by simp [Test.holds,hr.zero,hr.height]) he r.eval,?_,htPop,htKey,
      htImage,htSep,?_,?_,r.realMem.trans hreal,htFrame⟩⟩
    · have hh := r.costBound;omega
    · exact LocatedTrie.branch_root b address r.next other
    · rwa [hbranch]
end DecrAlmostLinearSSSP.Decremental.Exact.TriePop
end s59
section s60
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePop
open Structured
lemma core_result (h : ℕ) (tree : LocatedTrie h) (low base : ℕ) (s : Data)
    (hr : Ready tree low base s) : Nonempty (Result tree s) := by
  induction h generalizing low base s with
  | zero => exact result_zero tree low base s hr
  | succ h ih => exact result_succ h ih tree low base s hr
lemma code_nat_frame (k : ℕ) (hk : k ∉ registers) : NatFrame code k := by
  refine ⟨?_,core_nat_frame k hk⟩
  simp only [registers,Finset.mem_insert,Finset.mem_singleton,not_or] at hk
  simp [start,startAtoms,Structured.sequence,NatFrame,writesNat] <;> tauto
lemma code_real_frame (k : ℕ) : RealFrame code k := by
  refine ⟨?_,core_real_frame k⟩
  simp [start,startAtoms,Structured.sequence,RealFrame,writesReal]
lemma start_fields (s : Data) (hz : s.natReg 56 = 0) :
    (started s).natReg 256 = s.natReg 236 ∧ (started s).natReg 258 = s.natReg 238 ∧
      (started s).natReg 260 = 0 ∧ (started s).natReg 264 = s.natMem (s.natReg 246) := by
  simp [started,startAtoms,Atom.effect,instructionEffect,data,Data.machine,hz]
lemma code_result (h : ℕ) (tree : LocatedTrie h) (low base : ℕ) (s : Data)
    (hz : s.natReg 56 = 0) (h1 : s.natReg 26 = 1) (hheight : s.natReg 236 = h)
    (hi : tree.Image s) (hs : tree.Separated) (hb : tree.Bounded low (s.natReg 244))
    (hslot : s.natMem (s.natReg 246) = tree.root) (hpositive : 0<RadixQueue.count tree.abstract)
    (hpowers : ∀ j<h, s.natMem (base+j) = 2^j) (hpowerHigh : base+h ≤ low)
    (hpowerPtr : h ≠ 0 → s.natReg 238+1 = base+h) :
    ∃ (cost : ℕ) (t : Data) (next : LocatedTrie h) (key : ℕ), Eval code s cost t ∧ cost ≤ 34*(h+1) ∧
      RadixQueue.pop tree.abstract = some (key,t.natReg 262,next.abstract) ∧ t.natReg 260 = key ∧
      next.Image t ∧ next.Separated ∧ next.Bounded low (t.natReg 244) ∧ next.root = tree.root ∧
      next.footprint ⊆ tree.footprint ∧ t.realMem = s.realMem ∧
      (∀ a, a ∉ tree.footprint → t.natMem a = s.natMem a) := by
  let u := started s
  have heStart := start_eval s
  have hf := start_fields s hz
  have hmem : u.natMem = s.natMem := by rfl
  have hreal : u.realMem = s.realMem := by rfl
  have halloc : u.natReg 244 = s.natReg 244 := by
    simp [u,started,startAtoms,Atom.effect,instructionEffect,data,Data.machine]
  have hready : Ready tree low base u := by
    refine ⟨?_,?_,hf.1.trans hheight,hi.frame (fun a _ => congrFun hmem a),hs,?_,hf.2.2.2.trans hslot,hpositive,?_,hpowerHigh,?_⟩
    · simpa [u,started,startAtoms,Atom.effect,instructionEffect,data,Data.machine] using hz
    · simpa [u,started,startAtoms,Atom.effect,instructionEffect,data,Data.machine] using h1
    · rwa [halloc]
    · intro j hj;rw [hmem];exact hpowers j hj
    · intro hh;rw [hf.2.1];exact hpowerPtr hh
  obtain ⟨r⟩ := core_result h tree low base u hready
  have htalloc : r.final.natReg 244 = s.natReg 244 := (r.nat_frame 244 (by norm_num [registers])).trans halloc
  refine ⟨4+r.cost,r.final,r.next,r.key,Eval.seq heStart r.eval,?_,r.pop,?_,r.image,r.separated,?_,r.root,r.footprint,r.realMem.trans hreal,?_⟩
  · have hh := r.costBound;omega
  · rw [r.keyReg,hf.2.2.1,Nat.zero_add]
  · intro a ha
    rw [htalloc];exact hb a (r.footprint ha)
  · intro a ha
    exact (r.frame a ha).trans (congrFun hmem a)
end DecrAlmostLinearSSSP.Decremental.Exact.TriePop
end s60
section s61
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
lemma input_vertex_positive (i : Input) : 0 < i.n := lt_of_le_of_lt (Nat.zero_le _) i.source.isLt
lemma scale_positive (j : ℕ) : 0 < scale j := pow_pos (by norm_num) _
lemma delta_positive (i : Input) (hi : i.Valid) (j : ℕ) : 0 < delta i j := by
  have hn : (0 : ℝ) < i.n := by exact_mod_cast input_vertex_positive i
  have he := hi.2.2.2.1
  dsimp [delta]
  exact div_pos (mul_pos he (scale_positive j)) (by positivity)
lemma rounded_weight_bounds (i : Input) (hi : i.Valid) (j : ℕ) (e : Fin (roundedInput i j).k) :
    1 ≤ (roundedInput i j).weight e ∧ (roundedInput i j).weight e ≤ (roundedInput i j).W := by
  let orig := (Fintype.equivFin (ScaleEdge i j)).symm e
  have hn : (0 : ℝ) < i.n := by exact_mod_cast input_vertex_positive i
  have heps := hi.2.2.2.1
  have hscale := scale_positive j
  have hdelta := delta_positive i hi j
  have hw : (0 : ℝ) < i.weight orig.val := by exact_mod_cast (hi.2.2.2.2.2 orig.val).1
  have hcut : (i.weight orig.val : ℝ) ≤ 2 * scale j := orig.property
  change 1 ≤ ⌈(i.weight orig.val : ℝ) / delta i j⌉₊ ∧
    ⌈(i.weight orig.val : ℝ) / delta i j⌉₊ ≤ ⌈256 * (i.n : ℝ) / i.accuracy⌉₊
  constructor
  · exact Nat.ceil_pos.mpr (div_pos hw hdelta)
  · apply Nat.ceil_le_ceil
    have hh := div_le_div_of_nonneg_right hcut hdelta.le
    have hid : (2 * scale j) / delta i j = 256 * (i.n : ℝ) / i.accuracy := by
      dsimp [delta]
      field_simp
      <;> ring
    exact hh.trans hid.le
lemma rounded_valid (i : Input) (hi : i.Valid) (j : ℕ) : (roundedInput i j).Valid := by
  have hn : (0 : ℝ) < i.n := by exact_mod_cast input_vertex_positive i
  have heps := hi.2.2.2.1
  have heps1 := hi.2.2.2.2.1
  have hk : Fintype.card (ScaleEdge i j) ≤ i.k := by
    simpa only [ScaleEdge, Fintype.card_fin] using
      Fintype.card_subtype_le (fun e : Fin i.k => (i.weight e : ℝ) ≤ 2 * scale j)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · change i.n ≤ 64 * i.size
    have hh := hi.1
    omega
  · change Fintype.card (ScaleEdge i j) ≤ 64 * i.size
    have hh := hi.2.1
    omega
  · change 1 ≤ ⌈256 * (i.n : ℝ) / i.accuracy⌉₊
    exact Nat.ceil_pos.mpr (by positivity)
  · change 0 < i.accuracy / 16
    positivity
  · change i.accuracy / 16 ≤ 1
    linarith
  · exact rounded_weight_bounds i hi j
lemma rounded_polynomial_domain (i : Input) (hi : i.Valid) (hn : 2 ≤ i.n)
    (hepslow : 1 / (i.size : ℝ) < i.accuracy) (j : ℕ) :
    2 ≤ (roundedInput i j).n ∧ (roundedInput i j).W ≤ (roundedInput i j).size ^ 2 ∧
      1 / ((roundedInput i j).size : ℝ) < (roundedInput i j).accuracy ∧
      (roundedInput i j).accuracy < 1 := by
  have hm : (0 : ℝ) < i.size := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < i.n) hi.1)
  have heps := hi.2.2.2.1
  have heps1 := hi.2.2.2.2.1
  have hmul : 1 < i.accuracy * i.size := (div_lt_iff₀ hm).mp hepslow
  have hnsize : (i.n : ℝ) ≤ i.size := by exact_mod_cast hi.1
  refine ⟨hn, ?_, ?_, ?_⟩
  · change ⌈256 * (i.n : ℝ) / i.accuracy⌉₊ ≤ (64 * i.size) ^ 2
    apply Nat.ceil_le.mpr
    norm_num only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat]
    apply (div_le_iff₀ heps).mpr
    have hh := mul_lt_mul_of_pos_right hmul hm
    nlinarith only [hh, hnsize, hm]
  · change 1 / ((64 * i.size : ℕ) : ℝ) < i.accuracy / 16
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    apply (div_lt_div_iff₀ (by positivity : 0 < (64 : ℝ) * i.size) (by norm_num : (0 : ℝ) < 16)).mpr
    nlinarith only [hmul]
  · change i.accuracy / 16 < 1
    linarith
end DecrAlmostLinearSSSP.Decremental
end s61
section s62
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
lemma logarithm2_eq_logb (x : ℝ) : logarithm2 x = Real.logb 2 x := rfl
lemma ceiling_scale_bounds {d : ℝ} (hd : 1 ≤ d) :
    d ≤ scale ⌈logarithm2 d⌉₊ ∧ scale ⌈logarithm2 d⌉₊ ≤ 2 * d := by
  have hdpos : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have hb : (1 : ℝ) < 2 := by norm_num
  have hlog : 0 ≤ logarithm2 d := Real.logb_nonneg hb hd
  have hlo : logarithm2 d ≤ (⌈logarithm2 d⌉₊ : ℝ) := Nat.le_ceil _
  have hhi : (⌈logarithm2 d⌉₊ : ℝ) ≤ logarithm2 d + 1 := (Nat.ceil_lt_add_one hlog).le
  constructor
  · have hh := (Real.logb_le_iff_le_rpow hb hdpos).mp hlo
    simpa only [scale, Real.rpow_natCast] using hh
  · have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hhi
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one] at hh
    have heq : (2 : ℝ) ^ (logarithm2 d) = d := Real.rpow_logb (by norm_num) (by norm_num) hdpos
    rw [heq] at hh
    simpa only [scale, Real.rpow_natCast, mul_comm] using hh
lemma scale_covers_distance (i : Input) (d : ℝ) (hd : 1 ≤ d)
    (hbound : d ≤ (i.n : ℝ) * i.W) :
    ∃ j : Fin (scaleCount i), d ≤ scale j.val ∧ scale j.val ≤ 2 * d := by
  let j := ⌈logarithm2 d⌉₊
  have hdpos : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have hmono : logarithm2 d ≤ logarithm2 ((i.n : ℝ) * i.W) :=
    Real.logb_le_logb_of_le (by norm_num) hdpos hbound
  have hj : j < scaleCount i := by
    unfold scaleCount
    exact Nat.lt_succ_of_le (Nat.ceil_le_ceil hmono)
  exact ⟨⟨j,hj⟩, ceiling_scale_bounds hd⟩
end DecrAlmostLinearSSSP.Decremental
end s62
section s63
set_option autoImplicit false
open Filter
open scoped Topology
namespace DecrAlmostLinearSSSP.Decremental
lemma log_size_positive (m : ℕ) : 0 < Real.log (max 2 m : ℕ) := by
  apply Real.log_pos
  exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) (le_max_left 2 m))
lemma log_size_tendsto : Tendsto (fun m : ℕ => Real.log (max 2 m : ℕ)) atTop atTop := by
  have hh : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2] with m hm
  simp only [max_eq_right hm]
lemma subpolynomial_constant (c : ℝ) (hc : 0 < c) : Subpolynomial (fun _ => c) :=
  ⟨fun _ => hc, log_size_tendsto.const_div_atTop (Real.log c)⟩
lemma subpolynomial_mul (a b : ℕ → ℝ) (ha : Subpolynomial a) (hb : Subpolynomial b) :
    Subpolynomial (fun m => a m * b m) := by
  refine ⟨fun m => mul_pos (ha.1 m) (hb.1 m), ?_⟩
  have hfun : (fun m => Real.log (a m * b m) / Real.log (max 2 m : ℕ)) =
      fun m => Real.log (a m) / Real.log (max 2 m : ℕ) + Real.log (b m) / Real.log (max 2 m : ℕ) := by
    funext m
    rw [Real.log_mul (ha.1 m).ne' (hb.1 m).ne', add_div]
  rw [hfun]
  simpa only [add_zero] using ha.2.add hb.2
lemma subpolynomial_exp (f : ℕ → ℝ)
    (hf : Tendsto (fun m => f m / Real.log (max 2 m : ℕ)) atTop (nhds 0)) :
    Subpolynomial (fun m => Real.exp (f m)) := by
  exact ⟨fun m => Real.exp_pos _, by simpa only [Real.log_exp] using hf⟩
lemma subpolynomial_add (a b : ℕ → ℝ) (ha : Subpolynomial a) (hb : Subpolynomial b) :
    Subpolynomial (fun m => a m + b m) := by
  refine ⟨fun m => add_pos (ha.1 m) (hb.1 m), ?_⟩
  have hu : Tendsto (fun m => Real.log 2 / Real.log (max 2 m : ℕ) +
      max (Real.log (a m) / Real.log (max 2 m : ℕ))
        (Real.log (b m) / Real.log (max 2 m : ℕ))) atTop (nhds 0) := by
    simpa only [max_self, add_zero] using (log_size_tendsto.const_div_atTop (Real.log 2)).add (ha.2.max hb.2)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le ha.2 hu
  · intro m
    exact div_le_div_of_nonneg_right (Real.log_le_log (ha.1 m) (le_add_of_nonneg_right (hb.1 m).le)) (log_size_positive m).le
  · intro m
    have hsum : a m + b m ≤ 2 * max (a m) (b m) := by
      have h1 := le_max_left (a m) (b m)
      have h2 := le_max_right (a m) (b m)
      linarith
    have hmax : Real.log (max (a m) (b m)) = max (Real.log (a m)) (Real.log (b m)) := by
      rcases le_total (a m) (b m) with hab | hba
      · rw [max_eq_right hab, max_eq_right (Real.log_le_log (ha.1 m) hab)]
      · rw [max_eq_left hba, max_eq_left (Real.log_le_log (hb.1 m) hba)]
    have hl := Real.log_le_log (add_pos (ha.1 m) (hb.1 m)) hsum
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (ne_of_gt ((ha.1 m).trans_le (le_max_left _ _))), hmax] at hl
    have hh := div_le_div_of_nonneg_right hl (log_size_positive m).le
    simpa only [add_div, max_div_div_right (log_size_positive m).le] using hh
end DecrAlmostLinearSSSP.Decremental
end s63
section s64
set_option autoImplicit false
open Filter
open scoped Topology
namespace DecrAlmostLinearSSSP.Decremental
lemma subpolynomial_log_size : Subpolynomial (fun m => Real.log (max 2 m : ℕ)) := by
  refine ⟨log_size_positive, ?_⟩
  exact Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp log_size_tendsto
lemma subpolynomial_pow (a : ℕ → ℝ) (ha : Subpolynomial a) (k : ℕ) :
    Subpolynomial (fun m => a m ^ k) := by
  induction k with
  | zero => simpa only [pow_zero] using subpolynomial_constant 1 (by norm_num)
  | succ k ih => simpa only [pow_succ] using subpolynomial_mul (fun m => a m ^ k) a ih ha
lemma subpolynomial_polylog (k : ℕ) :
    Subpolynomial (fun m => (1 + Real.log (max 2 m : ℕ)) ^ k) :=
  subpolynomial_pow _ (subpolynomial_add (fun _ => 1) _ (subpolynomial_constant 1 (by norm_num)) subpolynomial_log_size) k
end DecrAlmostLinearSSSP.Decremental
end s64
section s65
set_option autoImplicit false
open Filter
open scoped Topology
namespace DecrAlmostLinearSSSP.Decremental
lemma logarithm2_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ logarithm2 x := by
  unfold logarithm2
  exact div_nonneg (Real.log_nonneg hx) (Real.log_pos (by norm_num)).le
lemma logarithm2_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : logarithm2 x ≤ logarithm2 y := by
  unfold logarithm2
  exact div_le_div_of_nonneg_right (Real.log_le_log hx hxy) (Real.log_pos (by norm_num)).le
lemma logarithm2_mul {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    logarithm2 (x*y) = logarithm2 x + logarithm2 y := by
  unfold logarithm2
  rw [Real.log_mul hx.ne' hy.ne',add_div]
lemma scaleCount_real_bound (i : Input) (hi : i.Valid) :
    (scaleCount i : ℝ) ≤ logarithm2 i.n + logarithm2 i.W + 2 := by
  have hn : (1 : ℝ) ≤ i.n := by exact_mod_cast input_vertex_positive i
  have hW : (1 : ℝ) ≤ i.W := by exact_mod_cast hi.2.2.1
  have hprod : (1 : ℝ) ≤ (i.n : ℝ)*i.W := by nlinarith [mul_nonneg (sub_nonneg.mpr hn) (sub_nonneg.mpr hW)]
  have hlog := logarithm2_nonneg hprod
  have hceil := (Nat.ceil_lt_add_one hlog).le
  change ((⌈logarithm2 ((i.n : ℝ)*i.W)⌉₊ + 1 : ℕ) : ℝ) ≤ _
  rw [Nat.cast_add,Nat.cast_one]
  rw [logarithm2_mul (by linarith : (0 : ℝ) < i.n) (by linarith : (0 : ℝ) < i.W)] at hceil ⊢
  linarith
lemma scaleCount_saturated_bound (i : Input) (hi : i.Valid) :
    (scaleCount i : ℝ) ≤ (3 + logarithm2 (max 2 i.size : ℕ)) * max 1 (logarithm2 i.W) := by
  have hcount := scaleCount_real_bound i hi
  have hn : (0 : ℝ) < i.n := by exact_mod_cast input_vertex_positive i
  have hnm : (i.n : ℝ) ≤ (max 2 i.size : ℕ) := by exact_mod_cast (hi.1.trans (le_max_right 2 i.size))
  have hnlog := logarithm2_mono hn hnm
  have hmlog : 0 ≤ logarithm2 (max 2 i.size : ℕ) :=
    logarithm2_nonneg (by exact_mod_cast (show 1 ≤ max 2 i.size from (by omega)))
  have hW1 : (1 : ℝ) ≤ max 1 (logarithm2 i.W) := le_max_left _ _
  have hWlog : logarithm2 i.W ≤ max 1 (logarithm2 i.W) := le_max_right _ _
  have hmul := mul_le_mul_of_nonneg_left hW1 hmlog
  nlinarith
lemma subpolynomial_logarithm2_size : Subpolynomial (fun m => logarithm2 (max 2 m : ℕ)) := by
  have hc : 0 < (Real.log 2)⁻¹ := inv_pos.mpr (Real.log_pos (by norm_num))
  simpa only [logarithm2,div_eq_mul_inv] using
    subpolynomial_mul (fun m => Real.log (max 2 m : ℕ)) (fun _ => (Real.log 2)⁻¹)
      subpolynomial_log_size (subpolynomial_constant _ hc)
lemma subpolynomial_scale_overhead : Subpolynomial (fun m => 3 + logarithm2 (max 2 m : ℕ)) :=
  subpolynomial_add (fun _ => 3) _ (subpolynomial_constant 3 (by norm_num)) subpolynomial_logarithm2_size
end DecrAlmostLinearSSSP.Decremental
end s65
section s66
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact
lemma height_spec (bound : ℕ) : bound < 2^height bound := Nat.find_spec (exists_power_above bound)
lemma height_minimal (bound h : ℕ) (hh : h < height bound) : 2^h ≤ bound := by
  have hn := Nat.find_min (exists_power_above bound) hh
  omega
lemma height_le {bound h : ℕ} (hh : bound < 2^h) : height bound ≤ h := Nat.find_min' (exists_power_above bound) hh
lemma height_positive {bound : ℕ} (hb : 1 ≤ bound) : 1 ≤ height bound := by
  have hh := height_spec bound
  by_contra hn
  have hzero : height bound = 0 := by omega
  rw [hzero,pow_zero] at hh
  omega
lemma input_power_bound (i : Input) (hi : i.Valid) : i.n*i.W < 2^scaleCount i := by
  have hn : (1 : ℝ) ≤ i.n := by exact_mod_cast input_vertex_positive i
  have hW : (1 : ℝ) ≤ i.W := by exact_mod_cast hi.2.2.1
  have hprod : (1 : ℝ) ≤ (i.n : ℝ)*i.W := by nlinarith
  have hh := (ceiling_scale_bounds hprod).1
  have hpow : (0 : ℝ) < 2^⌈logarithm2 ((i.n : ℝ)*i.W)⌉₊ := pow_pos (by norm_num) _
  have hreal : (i.n : ℝ)*i.W < (2 : ℝ)^scaleCount i := by
    unfold scaleCount
    rw [pow_succ]
    unfold scale at hh
    nlinarith only [hh,hpow]
  exact_mod_cast hreal
lemma input_height_le (i : Input) (hi : i.Valid) : height (i.n*i.W) ≤ scaleCount i := height_le (input_power_bound i hi)
end DecrAlmostLinearSSSP.Decremental.Exact
end s66
section s67
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Powers
open Structured
lemma body_eval (s : Data) : Eval body s 5 (advanced s) := eval_sequence_atoms bodyAtoms s
lemma body_fields (s : Data) (h1 : s.natReg 26 = 1) :
    (advanced s).natReg 248 = s.natReg 248+1 ∧ (advanced s).natReg 250 = 2*s.natReg 250 ∧
    (advanced s).realReg 250 = (2*s.natReg 250 : ℕ) ∧ (advanced s).natReg 252 = s.natReg 252+1 ∧
    (advanced s).natMem = Function.update s.natMem (s.natReg 248) (s.natReg 250) ∧
    (advanced s).realMem = s.realMem := by
  simp [advanced,bodyAtoms,Atom.effect,instructionEffect,data,Data.machine,h1,two_mul]
lemma body_nat_frame (k : ℕ) (h248 : k ≠ 248) (h250 : k ≠ 250) (h252 : k ≠ 252) : NatFrame body k := by
  simp [body,bodyAtoms,Structured.sequence,NatFrame,writesNat,Ne.symm h248,Ne.symm h250,Ne.symm h252]
lemma body_real_frame (k : ℕ) (h250 : k ≠ 250) : RealFrame body k := by
  simp [body,bodyAtoms,Structured.sequence,RealFrame,writesReal,Ne.symm h250]
lemma Prefix.step {bound base d : ℕ} {s : Data} (h : Prefix bound base d s) : Prefix bound base (d+1) (advanced s) := by
  obtain ⟨hp,hpow,hrpow,hi,hn,hr⟩ := body_fields s h.unit
  have he := body_eval s
  constructor
  · exact (he.real_frame (body_real_frame 248 (by omega))).trans h.cutoff
  · rw [hp,h.pointer];omega
  · rw [hpow,h.power,pow_succ];omega
  · rw [hrpow,h.power,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow,pow_succ];ring
  · rw [hi,h.index]
  · exact (he.nat_frame (body_nat_frame 26 (by omega) (by omega) (by omega))).trans h.unit
  · intro j hj
    rw [hn,h.pointer,h.power]
    by_cases hjd : j = d
    · subst j;rw [Function.update_self]
    · rw [Function.update_of_ne (show base+j ≠ base+d by omega)]
      exact h.entries j (by omega)
lemma loop_eval (bound base remaining done : ℕ) (htotal : done+remaining = height bound) (s : Data)
    (h : Prefix bound base done s) :
    ∃ t, Eval loop s (7*remaining+2) t ∧ Prefix bound base (height bound) t ∧ t.realMem = s.realMem ∧
      (∀ address, address < base+done ∨ base+height bound ≤ address → t.natMem address = s.natMem address) := by
  induction remaining generalizing done s with
  | zero =>
    have hd : done = height bound := by omega
    have hspec : (bound : ℝ) < (2 : ℝ)^done := by exact_mod_cast (hd ▸ height_spec bound)
    have htest : ¬(Test.realLess 250 248).holds s := by
      rw [Test.holds,h.realPower,h.cutoff]
      have hspecN : bound < 2^done := hd ▸ height_spec bound
      have hNat : bound+1 ≤ 2^done := by omega
      have hh : (bound : ℝ)+1 ≤ (2 : ℝ)^done := by exact_mod_cast hNat
      linarith
    exact ⟨s,by simpa only [loop,Nat.mul_zero,Nat.zero_add] using Eval.loopNo (body := body) s htest,hd ▸ h,rfl,fun _ _ => rfl⟩
  | succ remaining ih =>
    have hdone : done < height bound := by omega
    have hpower := height_minimal bound done hdone
    have hpowerR : (2 : ℝ)^done ≤ bound := by exact_mod_cast hpower
    have htest : (Test.realLess 250 248).holds s := by rw [Test.holds,h.realPower,h.cutoff];linarith
    have hnext := h.step
    obtain ⟨t,ht,htp,htr,hframe⟩ := ih (done+1) (by omega) (advanced s) hnext
    have hh := body_fields s h.unit
    refine ⟨t,?_,htp,htr.trans hh.2.2.2.2.2,?_⟩
    · have he := Eval.loopYes htest (body_eval s) ht
      have hcost : 7*(remaining+1)+2 = 5+(7*remaining+2)+2 := by omega
      rw [hcost]
      exact he
    · intro address ha
      rw [hframe address (by omega),hh.2.2.2.2.1,h.pointer,Function.update_of_ne (show address ≠ base+done by omega)]
end DecrAlmostLinearSSSP.Decremental.Exact.Powers
end s67
section s68
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma bankFactor_positive (j : ℕ) : 0 < bankFactor j := by unfold bankFactor; positivity
lemma two_pow_odd_unique {j k a b : ℕ}
    (heq : 2 ^ j * (2 * a + 1) = 2 ^ k * (2 * b + 1)) : j = k ∧ a = b := by
  wlog hjk : j ≤ k generalizing j k a b
  · obtain ⟨hkj,hba⟩ := this heq.symm (by omega)
    exact ⟨hkj.symm,hba.symm⟩
  have hjkeq : j = k := by
    by_contra hne
    have hlt : j < k := by omega
    obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le (show j + 1 ≤ k by omega)
    rw [ht] at heq
    have hpow : 2 ^ (j + 1 + t) = 2 ^ j * (2 * 2 ^ t) := by rw [pow_add, pow_succ]; ring
    rw [hpow, mul_assoc] at heq
    have hc : 2 * a + 1 = 2 * 2 ^ t * (2 * b + 1) :=
      Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ j) heq
    have hm := congrArg (fun x : ℕ => x % 2) hc
    norm_num [Nat.add_mod, Nat.mul_mod] at hm
  subst k
  have hab : 2 * a + 1 = 2 * b + 1 := Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ j) heq
  exact ⟨rfl, by omega⟩
lemma bankAddress_injective {base j k a b : ℕ} (heq : bankAddress base j a = bankAddress base k b) :
    j = k ∧ a = b := by
  have hh : 2 ^ (j + 1) * (2 * a + 1) = 2 ^ (k + 1) * (2 * b + 1) := Nat.add_left_cancel heq
  obtain ⟨hjk,hab⟩ := two_pow_odd_unique hh
  exact ⟨by omega,hab⟩
lemma guest_bank_above (base j a : ℕ) : base < bankAddress base j a := by
  have hf := bankFactor_positive j
  unfold bankAddress
  nlinarith
lemma guest_bank_ne_host (base j a b : ℕ) : bankAddress base j a ≠ base + (2 * b + 1) := by
  intro heq
  have hh : 2 ^ (j + 1) * (2 * a + 1) = 2 ^ 0 * (2 * b + 1) := by
    simpa only [bankAddress, bankFactor, Nat.add_left_cancel_iff, pow_zero, one_mul] using heq
  have hj := (two_pow_odd_unique hh).1
  omega
lemma scaled_nadd (F a b : ℕ) : F * a + F * b = F * (a + b) := by ring
lemma scaled_nsub (F a b : ℕ) : F * a - F * b = F * (a - b) := (Nat.mul_sub F a b).symm
lemma scaled_less (F a b : ℕ) (hF : 0 < F) : F * a < F * b ↔ a < b := Nat.mul_lt_mul_left hF
lemma scaled_address (base F a : ℕ) : base + (F * a + F * a) + F = base + F * (2 * a + 1) := by ring
lemma scaled_cast (F a : ℕ) (hF : 0 < F) : ((F * a : ℕ) : ℝ) / (F : ℝ) = (a : ℝ) := by
  have hne : (F : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hF
  push_cast
  field_simp
lemma scaled_decode (F a : ℕ) (hF : 0 < F) : (F * a) / F = a := Nat.mul_div_cancel_left a hF
end DecrAlmostLinearSSSP.Decremental
end s68
section s69
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma shadowReg_injective : Function.Injective shadowReg := by
  intro a b h
  dsimp [shadowReg] at h
  omega
lemma shadowReg_ne_meta (j k : ℕ) (hk : k < 9) : shadowReg j ≠ k := by
  dsimp [shadowReg]
  omega
lemma ShadowRep.host_clock {base F : ℕ} {c g : Machine} (h : ShadowRep base F c g)
    (pc work : ℕ) : ShadowRep base F {c with pc := pc, work := work} g := ⟨h.pc, h.work, h.halted, h.fault, h.realReg, h.natReg, h.realMem, h.natMem⟩
lemma ShadowRep.real_register {base F : ℕ} {c g : Machine} (h : ShadowRep base F c g)
    (a : ℕ) (x : ℝ) :
    ShadowRep base F {c with realReg := Function.update c.realReg (shadowReg a) x}
      {g with realReg := Function.update g.realReg a x} := by
  classical
  refine ⟨h.pc, h.work, h.halted, h.fault, ?_, h.natReg, h.realMem, h.natMem⟩
  intro j
  by_cases hj : j = a
  · subst j
    simp
  · have hr : shadowReg j ≠ shadowReg a := shadowReg_injective.ne hj
    simp only [Function.update_of_ne hr, Function.update_of_ne hj]
    exact h.realReg j
lemma ShadowRep.nat_register {base F : ℕ} {c g : Machine} (h : ShadowRep base F c g)
    (a x : ℕ) :
    ShadowRep base F {c with natReg := Function.update c.natReg (shadowReg a) (F * x)}
      {g with natReg := Function.update g.natReg a x} := by
  classical
  have hm (k : ℕ) (hk : k < 9) :
      Function.update c.natReg (shadowReg a) (F * x) k = c.natReg k :=
    Function.update_of_ne (shadowReg_ne_meta a k hk).symm _ _
  refine ⟨?_, ?_, ?_, ?_, h.realReg, ?_, h.realMem, h.natMem⟩
  · simpa only [hm 2 (by omega)] using h.pc
  · simpa only [hm 3 (by omega)] using h.work
  · simpa only [hm 4 (by omega)] using h.halted
  · simpa only [hm 5 (by omega)] using h.fault
  · intro j
    by_cases hj : j = a
    · subst j
      simp
    · have hr : shadowReg j ≠ shadowReg a := shadowReg_injective.ne hj
      simp only [Function.update_of_ne hr, Function.update_of_ne hj]
      exact h.natReg j
lemma shadow_address_injective (base F : ℕ) (hF : 0 < F) :
    Function.Injective (fun a : ℕ => base + F * (2 * a + 1)) := by
  intro a b hab
  have hh : F * (2 * a + 1) = F * (2 * b + 1) := Nat.add_left_cancel hab
  have he := Nat.eq_of_mul_eq_mul_left hF hh
  omega
lemma ShadowRep.real_memory {base F : ℕ} {c g : Machine} (h : ShadowRep base F c g)
    (hF : 0 < F) (a : ℕ) (x : ℝ) :
    ShadowRep base F {c with realMem := Function.update c.realMem (base + F * (2 * a + 1)) x}
      {g with realMem := Function.update g.realMem a x} := by
  classical
  refine ⟨h.pc, h.work, h.halted, h.fault, h.realReg, h.natReg, ?_, h.natMem⟩
  intro b
  by_cases hb : b = a
  · subst b
    simp
  · have hh : base + F * (2 * b + 1) ≠ base + F * (2 * a + 1) := (shadow_address_injective base F hF).ne hb
    simp only [Function.update_of_ne hh, Function.update_of_ne hb]
    exact h.realMem b
lemma ShadowRep.nat_memory {base F : ℕ} {c g : Machine} (h : ShadowRep base F c g)
    (hF : 0 < F) (a x : ℕ) :
    ShadowRep base F {c with natMem := Function.update c.natMem (base + F * (2 * a + 1)) (F * x)}
      {g with natMem := Function.update g.natMem a x} := by
  classical
  refine ⟨h.pc, h.work, h.halted, h.fault, h.realReg, h.natReg, h.realMem, ?_⟩
  intro b
  by_cases hb : b = a
  · subst b
    simp
  · have hh : base + F * (2 * b + 1) ≠ base + F * (2 * a + 1) := (shadow_address_injective base F hF).ne hb
    simp only [Function.update_of_ne hh, Function.update_of_ne hb]
    exact h.natMem b
lemma ShadowRep.scratch {base F : ℕ} {c g : Machine} (h : ShadowRep base F c g)
    (x : ℕ) : ShadowRep base F {c with natReg := Function.update c.natReg 6 x} g := by
  classical
  refine ⟨h.pc, h.work, h.halted, h.fault, h.realReg, ?_, h.realMem, h.natMem⟩
  intro j
  simp only [Function.update_of_ne (shadowReg_ne_meta j 6 (by omega))]
  exact h.natReg j
end DecrAlmostLinearSSSP.Decremental
end s69
section s70
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma shadow_scalar {base F : ℕ} {c g : Machine} (h : ShadowRep base F c g)
    (ins tr : Instruction) (ht : shadowScalarTranslation ins = some tr) :
    ShadowRep base F (instructionEffect tr c) (instructionEffect ins g) := by
  cases ins with
  | rational d q =>
    cases ht
    exact h.real_register d q
  | add d a b =>
    cases ht
    simp only [instructionEffect, h.realReg]
    exact h.real_register d _
  | sub d a b =>
    cases ht
    simp only [instructionEffect, h.realReg]
    exact h.real_register d _
  | mul d a b =>
    cases ht
    simp only [instructionEffect, h.realReg]
    exact h.real_register d _
  | div d a b =>
    cases ht
    simp only [instructionEffect, h.realReg]
    exact h.real_register d _
  | log d a =>
    cases ht
    simp only [instructionEffect, h.realReg]
    exact h.real_register d _
  | nadd d a b =>
    cases ht
    simp only [instructionEffect, h.natReg, scaled_nadd]
    exact h.nat_register d _
  | nsub d a b =>
    cases ht
    simp only [instructionEffect, h.natReg, scaled_nsub]
    exact h.nat_register d _
  | _ => simp [shadowScalarTranslation] at ht
lemma shadow_cast {base F : ℕ} {c g : Machine} (h : ShadowRep base F c g)
    (hF : 0 < F) (d a : ℕ) (hf : c.realReg 7 = (F : ℝ)) :
    ShadowRep base F
      (instructionEffect (.div (shadowReg d) (shadowReg d) 7)
        (instructionEffect (.cast (shadowReg d) (shadowReg a)) c))
      (instructionEffect (.cast d a) g) := by
  classical
  have hmeta : shadowReg d ≠ 7 := shadowReg_ne_meta d 7 (by omega)
  simp only [instructionEffect, Function.update_self, Function.update_of_ne hmeta.symm, hf, h.natReg, scaled_cast F _ hF]
  have heq : Function.update (Function.update c.realReg (shadowReg d) (↑(F * g.natReg a))) (shadowReg d) (g.natReg a : ℝ) =
      Function.update c.realReg (shadowReg d) (g.natReg a : ℝ) := by rw [Function.update_idem]
  rw [heq]
  exact h.real_register d _
end DecrAlmostLinearSSSP.Decremental
end s70
section s71
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma shadow_load {base F : ℕ} {c g : Machine} (h : ShadowRep base F c g) (d a : ℕ)
    (ha : c.natReg 6 = base + F * (2 * g.natReg a + 1)) :
    ShadowRep base F (instructionEffect (.load (shadowReg d) 6) c) (instructionEffect (.load d a) g) := by
  simp only [instructionEffect, ha, h.realMem]
  exact h.real_register d _
lemma shadow_loadN {base F : ℕ} {c g : Machine} (h : ShadowRep base F c g) (d a : ℕ)
    (ha : c.natReg 6 = base + F * (2 * g.natReg a + 1)) :
    ShadowRep base F (instructionEffect (.loadN (shadowReg d) 6) c) (instructionEffect (.loadN d a) g) := by
  simp only [instructionEffect, ha, h.natMem]
  exact h.nat_register d _
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
theorem solution : (((((((∀ (address payload value : Nat) (items : List.{0} (Prod.{0, 0} Nat Nat)) (low high : Nat)
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
          @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Bounded
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.leaf address
                (@List.cons.{0} (Prod.{0, 0} Nat Nat) (@Prod.mk.{0, 0} Nat Nat payload value) items))
              low high →
            have next := DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.leaf address items;
            And
              (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image
                (DecrAlmostLinearSSSP.Decremental.Exact.TriePop.leafData s)
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) next)
              (And
                (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Separated
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) next)
                (And
                  (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Bounded
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) next low high)
                  (And
                    (@LE.le.{0} (Finset.{0} Nat)
                      (@Preorder.toLE.{0} (Finset.{0} Nat)
                        (@PartialOrder.toPreorder.{0} (Finset.{0} Nat) (@Finset.instPartialOrder.{0} Nat)))
                      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint
                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) next)
                      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint
                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                        (DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.leaf address
                          (@List.cons.{0} (Prod.{0, 0} Nat Nat) (@Prod.mk.{0, 0} Nat Nat payload value) items))))
                    (∀
                      a ∉
                        @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint
                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                          (DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.leaf address
                            (@List.cons.{0} (Prod.{0, 0} Nat Nat) (@Prod.mk.{0, 0} Nat Nat payload value) items)),
                      @Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.Exact.TriePop.leafData s).natMem a)
                        (s.natMem a)))))) ∧ (∀ {h : Nat} {tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  (r : @DecrAlmostLinearSSSP.Decremental.Exact.TriePop.Result h tree s),
  ∀ k ∉ DecrAlmostLinearSSSP.Decremental.Exact.TriePop.registers,
    @Eq.{1} Nat ((@DecrAlmostLinearSSSP.Decremental.Exact.TriePop.Result.final h tree s r).natReg k) (s.natReg k))) ∧ ((∀
  (tree :
    DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (low base : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @DecrAlmostLinearSSSP.Decremental.Exact.TriePop.Ready (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      tree low base s →
    Nonempty.{1}
      (@DecrAlmostLinearSSSP.Decremental.Exact.TriePop.Result
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) tree s)) ∧ (∀ {h : Nat} (tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h)
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
          (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.abstract h tree))))) ∧ (((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 266) (instOfNatNat (nat_lit 266))) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.TriePop.decrement k) ∧ (∀ k ∉ DecrAlmostLinearSSSP.Decremental.Exact.TriePop.registers,
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.TriePop.body k)) ∧ ((∀ (h address : Nat) (left right : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h) (low base : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @DecrAlmostLinearSSSP.Decremental.Exact.TriePop.Ready
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.node h address left right) low base s →
    have q :=
      DecrAlmostLinearSSSP.Decremental.Exact.TriePop.descended
        (DecrAlmostLinearSSSP.Decremental.Exact.TriePop.decremented s);
    ∃ c,
      And (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePop.body s c q)
        (And (@LE.le.{0} Nat instLENat c (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18))))
          (And
            (@Eq.{1} Nat (q.natReg (@OfNat.ofNat.{0} Nat (nat_lit 264) (instOfNatNat (nat_lit 264))))
              (@ite.{1} Nat
                (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@DecrAlmostLinearSSSP.Decremental.RadixQueue.count h
                    (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.abstract h left)))
                (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@DecrAlmostLinearSSSP.Decremental.RadixQueue.count h
                    (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.abstract h left)))
                (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root h left)
                (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root h right)))
            (And
              (@Eq.{1} Nat (q.natReg (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260))))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260))))
                  (@ite.{1} Nat
                    (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                      (@DecrAlmostLinearSSSP.Decremental.RadixQueue.count h
                        (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.abstract h left)))
                    (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                      (@DecrAlmostLinearSSSP.Decremental.RadixQueue.count h
                        (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.abstract h left)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h))))
              (And (@Eq.{1} Nat (q.natReg (@OfNat.ofNat.{0} Nat (nat_lit 256) (instOfNatNat (nat_lit 256)))) h)
                (And
                  (@Eq.{1} Nat (q.natReg (@OfNat.ofNat.{0} Nat (nat_lit 258) (instOfNatNat (nat_lit 258))))
                    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 258) (instOfNatNat (nat_lit 258))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (And
                    (@Eq.{1} (Nat → Nat) q.natMem
                      (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natMem address
                        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (s.natMem address)
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                    (@Eq.{1} (Nat → Real) q.realMem s.realMem)))))))) ∧ ((∀ {h : Nat} (b : Bool) (address : Nat) (child other next : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h)
  (s t : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image s
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.branch h b address child other) →
    @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Separated
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.branch h b address child other) →
      @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image t h next →
        @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Separated h next →
          @LE.le.{0} (Finset.{0} Nat)
              (@Preorder.toLE.{0} (Finset.{0} Nat)
                (@PartialOrder.toPreorder.{0} (Finset.{0} Nat) (@Finset.instPartialOrder.{0} Nat)))
              (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint h next)
              (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint h child) →
            @Eq.{1} Nat
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@DecrAlmostLinearSSSP.Decremental.RadixQueue.count h
                    (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.abstract h next))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (@DecrAlmostLinearSSSP.Decremental.RadixQueue.count h
                  (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.abstract h child)) →
              @Eq.{1} Nat (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root h next)
                  (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root h child) →
                (∀ a ∉ @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint h child,
                    @Eq.{1} Nat (t.natMem a)
                      (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natMem address
                        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (s.natMem address)
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
                      (@LE.le.{0} (Finset.{0} Nat)
                        (@Preorder.toLE.{0} (Finset.{0} Nat)
                          (@PartialOrder.toPreorder.{0} (Finset.{0} Nat) (@Finset.instPartialOrder.{0} Nat)))
                        (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.branch h b address next other))
                        (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.branch h b address child other))))) ∧ (∀ (h : Nat),
  (∀ (child : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h) (low base : Nat)
      (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
      @DecrAlmostLinearSSSP.Decremental.Exact.TriePop.Ready h child low base s →
        Nonempty.{1} (@DecrAlmostLinearSSSP.Decremental.Exact.TriePop.Result h child s)) →
    ∀
      (tree :
        DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (low base : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
      @DecrAlmostLinearSSSP.Decremental.Exact.TriePop.Ready
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          tree low base s →
        Nonempty.{1}
          (@DecrAlmostLinearSSSP.Decremental.Exact.TriePop.Result
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            tree s)))))) ∧ ((((∀ (h : Nat) (tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h) (low base : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @DecrAlmostLinearSSSP.Decremental.Exact.TriePop.Ready h tree low base s →
    Nonempty.{1} (@DecrAlmostLinearSSSP.Decremental.Exact.TriePop.Result h tree s)) ∧ (∀ k ∉ DecrAlmostLinearSSSP.Decremental.Exact.TriePop.registers,
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.TriePop.code k)) ∧ ((∀ (k : Nat), DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Exact.TriePop.code k) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    And
      (@Eq.{1} Nat
        ((DecrAlmostLinearSSSP.Decremental.Exact.TriePop.started s).natReg
          (@OfNat.ofNat.{0} Nat (nat_lit 256) (instOfNatNat (nat_lit 256))))
        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 236) (instOfNatNat (nat_lit 236)))))
      (And
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.Exact.TriePop.started s).natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 258) (instOfNatNat (nat_lit 258))))
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 238) (instOfNatNat (nat_lit 238)))))
        (And
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.Exact.TriePop.started s).natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260))))
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.Exact.TriePop.started s).natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 264) (instOfNatNat (nat_lit 264))))
            (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 246) (instOfNatNat (nat_lit 246))))))))))) ∧ (((∀ (h : Nat) (tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h) (low base : Nat)
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
                                                @Eq.{1} Nat (t.natMem a) (s.natMem a)))))))))))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) i.n)) ∧ ((∀ (j : Nat),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
    (DecrAlmostLinearSSSP.Decremental.scale j)) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (j : Nat),
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (DecrAlmostLinearSSSP.Decremental.delta i j)) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (j : Nat) (e : Fin (DecrAlmostLinearSSSP.Decremental.roundedInput i j).k),
      And
        (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          ((DecrAlmostLinearSSSP.Decremental.roundedInput i j).weight e))
        (@LE.le.{0} Nat instLENat ((DecrAlmostLinearSSSP.Decremental.roundedInput i j).weight e)
          (DecrAlmostLinearSSSP.Decremental.roundedInput i j).W))))))) ∧ (((((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid → ∀ (j : Nat), (DecrAlmostLinearSSSP.Decremental.roundedInput i j).Valid) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) i.n →
      @LT.lt.{0} Real Real.instLT
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@Nat.cast.{0} Real Real.instNatCast i.size))
          i.accuracy →
        ∀ (j : Nat),
          And
            (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (DecrAlmostLinearSSSP.Decremental.roundedInput i j).n)
            (And
              (@LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.roundedInput i j).W
                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                  (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                  (DecrAlmostLinearSSSP.Decremental.roundedInput i j).size
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              (And
                (@LT.lt.{0} Real Real.instLT
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                    (@Nat.cast.{0} Real Real.instNatCast (DecrAlmostLinearSSSP.Decremental.roundedInput i j).size))
                  (DecrAlmostLinearSSSP.Decremental.roundedInput i j).accuracy)
                (@LT.lt.{0} Real Real.instLT (DecrAlmostLinearSSSP.Decremental.roundedInput i j).accuracy
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))))) ∧ ((∀ (x : Real),
  @Eq.{1} Real (DecrAlmostLinearSSSP.Decremental.logarithm2 x)
    (Real.logb
      (@OfNat.ofNat.{0} Real (nat_lit 2)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
      x)) ∧ (∀ {d : Real},
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) d →
    And
      (@LE.le.{0} Real Real.instLE d
        (DecrAlmostLinearSSSP.Decremental.scale
          (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
            (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing)
            (DecrAlmostLinearSSSP.Decremental.logarithm2 d))))
      (@LE.le.{0} Real Real.instLE
        (DecrAlmostLinearSSSP.Decremental.scale
          (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
            (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing)
            (DecrAlmostLinearSSSP.Decremental.logarithm2 d)))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
          d))))) ∧ (((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (d : Real),
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) d →
    @LE.le.{0} Real Real.instLE d
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (@Nat.cast.{0} Real Real.instNatCast i.n)
          (@Nat.cast.{0} Real Real.instNatCast i.W)) →
      ∃ j,
        And
          (@LE.le.{0} Real Real.instLE d
            (DecrAlmostLinearSSSP.Decremental.scale (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)))
          (@LE.le.{0} Real Real.instLE
            (DecrAlmostLinearSSSP.Decremental.scale (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              d))) ∧ (∀ (m : Nat),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
    (Real.log
      (@Nat.cast.{0} Real Real.instNatCast
        (@Max.max.{0} Nat Nat.instMax (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))))) ∧ ((@Filter.Tendsto.{0, 0} Nat Real
  (fun m =>
    Real.log
      (@Nat.cast.{0} Real Real.instNatCast
        (@Max.max.{0} Nat Nat.instMax (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))
  (@Filter.atTop.{0} Nat Nat.instPreorder) (@Filter.atTop.{0} Real Real.instPreorder)) ∧ ((∀ (c : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) c →
    DecrAlmostLinearSSSP.Decremental.Subpolynomial fun x => c) ∧ (∀ (a b : Nat → Real),
  DecrAlmostLinearSSSP.Decremental.Subpolynomial a →
    DecrAlmostLinearSSSP.Decremental.Subpolynomial b →
      DecrAlmostLinearSSSP.Decremental.Subpolynomial fun m =>
        @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (a m) (b m)))))) ∧ ((((∀ (f : Nat → Real),
  @Filter.Tendsto.{0, 0} Nat Real
      (fun m =>
        @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (f m)
          (Real.log
            (@Nat.cast.{0} Real Real.instNatCast
              (@Max.max.{0} Nat Nat.instMax (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))))
      (@Filter.atTop.{0} Nat Nat.instPreorder)
      (@nhds.{0} Real
        (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) →
    DecrAlmostLinearSSSP.Decremental.Subpolynomial fun m => Real.exp (f m)) ∧ (∀ (a b : Nat → Real),
  DecrAlmostLinearSSSP.Decremental.Subpolynomial a →
    DecrAlmostLinearSSSP.Decremental.Subpolynomial b →
      DecrAlmostLinearSSSP.Decremental.Subpolynomial fun m =>
        @HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (a m) (b m))) ∧ ((DecrAlmostLinearSSSP.Decremental.Subpolynomial fun m =>
  Real.log
    (@Nat.cast.{0} Real Real.instNatCast
      (@Max.max.{0} Nat Nat.instMax (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))) ∧ ((∀ (a : Nat → Real),
  DecrAlmostLinearSSSP.Decremental.Subpolynomial a →
    ∀ (k : Nat),
      DecrAlmostLinearSSSP.Decremental.Subpolynomial fun m =>
        @HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) (a m) k) ∧ (∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Subpolynomial fun m =>
    @HPow.hPow.{0, 0, 0} Real Nat Real
      (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (Real.log
          (@Nat.cast.{0} Real Real.instNatCast
            (@Max.max.{0} Nat Nat.instMax (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))))
      k)))) ∧ (((∀ {x : Real},
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) x →
    @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (DecrAlmostLinearSSSP.Decremental.logarithm2 x)) ∧ (∀ {x y : Real},
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) x →
    @LE.le.{0} Real Real.instLE x y →
      @LE.le.{0} Real Real.instLE (DecrAlmostLinearSSSP.Decremental.logarithm2 x)
        (DecrAlmostLinearSSSP.Decremental.logarithm2 y))) ∧ ((∀ {x y : Real},
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) x →
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) y →
      @Eq.{1} Real
        (DecrAlmostLinearSSSP.Decremental.logarithm2
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) x y))
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (DecrAlmostLinearSSSP.Decremental.logarithm2 x) (DecrAlmostLinearSSSP.Decremental.logarithm2 y))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast (DecrAlmostLinearSSSP.Decremental.scaleCount i))
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (DecrAlmostLinearSSSP.Decremental.logarithm2 (@Nat.cast.{0} Real Real.instNatCast i.n))
          (DecrAlmostLinearSSSP.Decremental.logarithm2 (@Nat.cast.{0} Real Real.instNatCast i.W)))
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast (DecrAlmostLinearSSSP.Decremental.scaleCount i))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (@OfNat.ofNat.{0} Real (nat_lit 3)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
          (DecrAlmostLinearSSSP.Decremental.logarithm2
            (@Nat.cast.{0} Real Real.instNatCast
              (@Max.max.{0} Nat Nat.instMax (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) i.size))))
        (@Max.max.{0} Real Real.instMax (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (DecrAlmostLinearSSSP.Decremental.logarithm2 (@Nat.cast.{0} Real Real.instNatCast i.W))))))))))) ∧ ((((((DecrAlmostLinearSSSP.Decremental.Subpolynomial fun m =>
  DecrAlmostLinearSSSP.Decremental.logarithm2
    (@Nat.cast.{0} Real Real.instNatCast
      (@Max.max.{0} Nat Nat.instMax (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))) ∧ (DecrAlmostLinearSSSP.Decremental.Subpolynomial fun m =>
  @HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
    (@OfNat.ofNat.{0} Real (nat_lit 3)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (DecrAlmostLinearSSSP.Decremental.logarithm2
      (@Nat.cast.{0} Real Real.instNatCast
        (@Max.max.{0} Nat Nat.instMax (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))))) ∧ ((∀ (bound : Nat),
  @LT.lt.{0} Nat instLTNat bound
    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
      (DecrAlmostLinearSSSP.Decremental.Exact.height bound))) ∧ (∀ (bound h : Nat),
  @LT.lt.{0} Nat instLTNat h (DecrAlmostLinearSSSP.Decremental.Exact.height bound) →
    @LE.le.{0} Nat instLENat
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h)
      bound))) ∧ (((∀ {bound h : Nat},
  @LT.lt.{0} Nat instLTNat bound
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h) →
    @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.Exact.height bound) h) ∧ (∀ {bound : Nat},
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) bound →
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (DecrAlmostLinearSSSP.Decremental.Exact.height bound))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    @LT.lt.{0} Nat instLTNat (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) i.n i.W)
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (DecrAlmostLinearSSSP.Decremental.scaleCount i))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    @LE.le.{0} Nat instLENat
      (DecrAlmostLinearSSSP.Decremental.Exact.height
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) i.n i.W))
      (DecrAlmostLinearSSSP.Decremental.scaleCount i)) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.Powers.body s
    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
    (DecrAlmostLinearSSSP.Decremental.Exact.Powers.advanced s)))))) ∧ ((((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
    And
      (@Eq.{1} Nat
        ((DecrAlmostLinearSSSP.Decremental.Exact.Powers.advanced s).natReg
          (@OfNat.ofNat.{0} Nat (nat_lit 248) (instOfNatNat (nat_lit 248))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 248) (instOfNatNat (nat_lit 248))))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (And
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.Exact.Powers.advanced s).natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 250) (instOfNatNat (nat_lit 250))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 250) (instOfNatNat (nat_lit 250))))))
        (And
          (@Eq.{1} Real
            ((DecrAlmostLinearSSSP.Decremental.Exact.Powers.advanced s).realReg
              (@OfNat.ofNat.{0} Nat (nat_lit 250) (instOfNatNat (nat_lit 250))))
            (@Nat.cast.{0} Real Real.instNatCast
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 250) (instOfNatNat (nat_lit 250)))))))
          (And
            (@Eq.{1} Nat
              ((DecrAlmostLinearSSSP.Decremental.Exact.Powers.advanced s).natReg
                (@OfNat.ofNat.{0} Nat (nat_lit 252) (instOfNatNat (nat_lit 252))))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 252) (instOfNatNat (nat_lit 252))))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (And
              (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.Exact.Powers.advanced s).natMem
                (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natMem
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 248) (instOfNatNat (nat_lit 248))))
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 250) (instOfNatNat (nat_lit 250))))))
              (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.Exact.Powers.advanced s).realMem s.realMem)))))) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 248) (instOfNatNat (nat_lit 248))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 250) (instOfNatNat (nat_lit 250))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 252) (instOfNatNat (nat_lit 252))) →
        DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.Powers.body k)) ∧ ((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 250) (instOfNatNat (nat_lit 250))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Exact.Powers.body k) ∧ ((∀ {bound base d : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Powers.Prefix bound base d s →
    DecrAlmostLinearSSSP.Decremental.Exact.Powers.Prefix bound base
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (DecrAlmostLinearSSSP.Decremental.Exact.Powers.advanced s)) ∧ (∀ (bound base remaining done : Nat),
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
                    @Eq.{1} Nat (t.natMem address) (s.natMem address)))))))) ∧ (((∀ (j : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
    (DecrAlmostLinearSSSP.Decremental.bankFactor j)) ∧ (∀ {j k a b : Nat},
  @Eq.{1} Nat
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
    And (@Eq.{1} Nat j k) (@Eq.{1} Nat a b))) ∧ ((∀ {base j k a b : Nat},
  @Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.bankAddress base j a)
      (DecrAlmostLinearSSSP.Decremental.bankAddress base k b) →
    And (@Eq.{1} Nat j k) (@Eq.{1} Nat a b)) ∧ ((∀ (base j a : Nat), @LT.lt.{0} Nat instLTNat base (DecrAlmostLinearSSSP.Decremental.bankAddress base j a)) ∧ (∀ (base j a b : Nat),
  @Ne.{1} Nat (DecrAlmostLinearSSSP.Decremental.bankAddress base j a)
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))))) ∧ (((((∀ (F a b : Nat),
  @Eq.{1} Nat
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F a)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F b))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a b))) ∧ (∀ (F a b : Nat),
  @Eq.{1} Nat
    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F a)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F b))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) a b)))) ∧ ((∀ (F a b : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) F →
    Iff
      (@LT.lt.{0} Nat instLTNat (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F a)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F b))
      (@LT.lt.{0} Nat instLTNat a b)) ∧ (∀ (base F a : Nat),
  @Eq.{1} Nat
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F a)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F a)))
      F)
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))) ∧ (((∀ (F a : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) F →
    @Eq.{1} Real
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@Nat.cast.{0} Real Real.instNatCast (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F a))
        (@Nat.cast.{0} Real Real.instNatCast F))
      (@Nat.cast.{0} Real Real.instNatCast a)) ∧ (∀ (F a : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) F →
    @Eq.{1} Nat
      (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F a) F)
      a)) ∧ ((@Function.Injective.{1, 1} Nat Nat DecrAlmostLinearSSSP.Decremental.shadowReg) ∧ ((∀ (j k : Nat),
  @LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) →
    @Ne.{1} Nat (DecrAlmostLinearSSSP.Decremental.shadowReg j) k) ∧ (∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    ∀ (pc work : Nat),
      DecrAlmostLinearSSSP.Decremental.ShadowRep base F
        { pc := pc, realReg := c.realReg, natReg := c.natReg, realMem := c.realMem, natMem := c.natMem,
          halted := c.halted, fault := c.fault, work := work }
        g))))) ∧ ((((∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
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
          work := g.work }) ∧ (∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
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
          natMem := g.natMem, halted := g.halted, fault := g.fault, work := g.work })) ∧ ((∀ (base F : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) F →
    @Function.Injective.{1, 1} Nat Nat fun a =>
      @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) ∧ ((∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
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
            halted := g.halted, fault := g.fault, work := g.work }) ∧ (∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
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
            fault := g.fault, work := g.work })))) ∧ (((∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    ∀ (x : Nat),
      DecrAlmostLinearSSSP.Decremental.ShadowRep base F
        { pc := c.pc, realReg := c.realReg,
          natReg :=
            @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat c.natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) x,
          realMem := c.realMem, natMem := c.natMem, halted := c.halted, fault := c.fault, work := c.work }
        g) ∧ (∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    ∀ (ins tr : DecrAlmostLinearSSSP.Decremental.Instruction),
      @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (DecrAlmostLinearSSSP.Decremental.shadowScalarTranslation ins)
          (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction tr) →
        DecrAlmostLinearSSSP.Decremental.ShadowRep base F (DecrAlmostLinearSSSP.Decremental.instructionEffect tr c)
          (DecrAlmostLinearSSSP.Decremental.instructionEffect ins g))) ∧ ((∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
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
              g)) ∧ ((∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    ∀ (d a : Nat),
      @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (g.natReg a))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
        DecrAlmostLinearSSSP.Decremental.ShadowRep base F
          (DecrAlmostLinearSSSP.Decremental.instructionEffect
            (DecrAlmostLinearSSSP.Decremental.Instruction.load (DecrAlmostLinearSSSP.Decremental.shadowReg d)
              (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
            c)
          (DecrAlmostLinearSSSP.Decremental.instructionEffect (DecrAlmostLinearSSSP.Decremental.Instruction.load d a) g)) ∧ (∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    ∀ (d a : Nat),
      @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (g.natReg a))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
        DecrAlmostLinearSSSP.Decremental.ShadowRep base F
          (DecrAlmostLinearSSSP.Decremental.instructionEffect
            (DecrAlmostLinearSSSP.Decremental.Instruction.loadN (DecrAlmostLinearSSSP.Decremental.shadowReg d)
              (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
            c)
          (DecrAlmostLinearSSSP.Decremental.instructionEffect (DecrAlmostLinearSSSP.Decremental.Instruction.loadN d a)
            g))))))))) := by
  exact ⟨⟨⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.TriePop.leaf_image,DecrAlmostLinearSSSP.Decremental.Exact.TriePop.Result.nat_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.TriePop.result_zero,DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image.read_count⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.TriePop.decrement_nat_frame,DecrAlmostLinearSSSP.Decremental.Exact.TriePop.body_nat_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.TriePop.node_step,⟨DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.branch_delete_rebuild,DecrAlmostLinearSSSP.Decremental.Exact.TriePop.result_succ⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.TriePop.core_result,DecrAlmostLinearSSSP.Decremental.Exact.TriePop.code_nat_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.TriePop.code_real_frame,DecrAlmostLinearSSSP.Decremental.Exact.TriePop.start_fields⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.TriePop.code_result,DecrAlmostLinearSSSP.Decremental.input_vertex_positive⟩,⟨DecrAlmostLinearSSSP.Decremental.scale_positive,⟨DecrAlmostLinearSSSP.Decremental.delta_positive,DecrAlmostLinearSSSP.Decremental.rounded_weight_bounds⟩⟩⟩⟩⟩,⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.rounded_valid,DecrAlmostLinearSSSP.Decremental.rounded_polynomial_domain⟩,⟨DecrAlmostLinearSSSP.Decremental.logarithm2_eq_logb,DecrAlmostLinearSSSP.Decremental.ceiling_scale_bounds⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.scale_covers_distance,DecrAlmostLinearSSSP.Decremental.log_size_positive⟩,⟨DecrAlmostLinearSSSP.Decremental.log_size_tendsto,⟨DecrAlmostLinearSSSP.Decremental.subpolynomial_constant,DecrAlmostLinearSSSP.Decremental.subpolynomial_mul⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.subpolynomial_exp,DecrAlmostLinearSSSP.Decremental.subpolynomial_add⟩,⟨DecrAlmostLinearSSSP.Decremental.subpolynomial_log_size,⟨DecrAlmostLinearSSSP.Decremental.subpolynomial_pow,DecrAlmostLinearSSSP.Decremental.subpolynomial_polylog⟩⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.logarithm2_nonneg,DecrAlmostLinearSSSP.Decremental.logarithm2_mono⟩,⟨DecrAlmostLinearSSSP.Decremental.logarithm2_mul,⟨DecrAlmostLinearSSSP.Decremental.scaleCount_real_bound,DecrAlmostLinearSSSP.Decremental.scaleCount_saturated_bound⟩⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.subpolynomial_logarithm2_size,DecrAlmostLinearSSSP.Decremental.subpolynomial_scale_overhead⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.height_spec,DecrAlmostLinearSSSP.Decremental.Exact.height_minimal⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.height_le,DecrAlmostLinearSSSP.Decremental.Exact.height_positive⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.input_power_bound,⟨DecrAlmostLinearSSSP.Decremental.Exact.input_height_le,DecrAlmostLinearSSSP.Decremental.Exact.Powers.body_eval⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.Powers.body_fields,DecrAlmostLinearSSSP.Decremental.Exact.Powers.body_nat_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.Powers.body_real_frame,⟨DecrAlmostLinearSSSP.Decremental.Exact.Powers.Prefix.step,DecrAlmostLinearSSSP.Decremental.Exact.Powers.loop_eval⟩⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.bankFactor_positive,DecrAlmostLinearSSSP.Decremental.two_pow_odd_unique⟩,⟨DecrAlmostLinearSSSP.Decremental.bankAddress_injective,⟨DecrAlmostLinearSSSP.Decremental.guest_bank_above,DecrAlmostLinearSSSP.Decremental.guest_bank_ne_host⟩⟩⟩⟩⟩,⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.scaled_nadd,DecrAlmostLinearSSSP.Decremental.scaled_nsub⟩,⟨DecrAlmostLinearSSSP.Decremental.scaled_less,DecrAlmostLinearSSSP.Decremental.scaled_address⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.scaled_cast,DecrAlmostLinearSSSP.Decremental.scaled_decode⟩,⟨DecrAlmostLinearSSSP.Decremental.shadowReg_injective,⟨DecrAlmostLinearSSSP.Decremental.shadowReg_ne_meta,DecrAlmostLinearSSSP.Decremental.ShadowRep.host_clock⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.ShadowRep.real_register,DecrAlmostLinearSSSP.Decremental.ShadowRep.nat_register⟩,⟨DecrAlmostLinearSSSP.Decremental.shadow_address_injective,⟨DecrAlmostLinearSSSP.Decremental.ShadowRep.real_memory,DecrAlmostLinearSSSP.Decremental.ShadowRep.nat_memory⟩⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.ShadowRep.scratch,DecrAlmostLinearSSSP.Decremental.shadow_scalar⟩,⟨DecrAlmostLinearSSSP.Decremental.shadow_cast,⟨DecrAlmostLinearSSSP.Decremental.shadow_load,DecrAlmostLinearSSSP.Decremental.shadow_loadN⟩⟩⟩⟩⟩⟩⟩
