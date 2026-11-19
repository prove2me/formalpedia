-- Prove2me | solution 1 for DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_10
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T11:22:27.663254+00:00
-- url     : https://prove2.me/submissions/e6848226-0c58-4dbf-af3d-1bca0226b465

import Definitions.Def_DecrAlmostLinearSSSP_RAMFoundation
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_1
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
theorem DecrAlmostLinearSSSP.Decremental.step_of_halted : ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine),
  @Eq.{1} Bool c.halted Bool.true →
    @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine (DecrAlmostLinearSSSP.Decremental.step p c) c := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_1.2.2.2.2.2.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image.count : ∀ {s : DecrAlmostLinearSSSP.Decremental.Structured.Data} {height : Nat}
  {tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie height},
  @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image s height tree →
    @Ne.{1} Nat (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root height tree)
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
      @Eq.{1} Nat (s.natMem (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root height tree))
        (@DecrAlmostLinearSSSP.Decremental.RadixQueue.count height
          (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.abstract height tree)) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.1.1.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.Structured.CodeAt.tail : ∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {start : Nat} {ins : DecrAlmostLinearSSSP.Decremental.Instruction}
  {rest : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction},
  DecrAlmostLinearSSSP.Decremental.Structured.CodeAt p start
      (@List.cons.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins rest) →
    DecrAlmostLinearSSSP.Decremental.Structured.CodeAt p
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      rest := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.1.2.2.1.1.2
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
theorem DecrAlmostLinearSSSP.Decremental.delta_positive : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (j : Nat),
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (DecrAlmostLinearSSSP.Decremental.delta i j) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.1.1.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.log_size_positive : ∀ (m : Nat),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
    (Real.log
      (@Nat.cast.{0} Real Real.instNatCast
        (@Max.max.{0} Nat Nat.instMax (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.1.2.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.log_size_tendsto : @Filter.Tendsto.{0, 0} Nat Real
  (fun m =>
    Real.log
      (@Nat.cast.{0} Real Real.instNatCast
        (@Max.max.{0} Nat Nat.instMax (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))
  (@Filter.atTop.{0} Nat Nat.instPreorder) (@Filter.atTop.{0} Real Real.instPreorder) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.1.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.subpolynomial_constant : ∀ (c : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) c →
    DecrAlmostLinearSSSP.Decremental.Subpolynomial fun x => c := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.1.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.subpolynomial_mul : ∀ (a b : Nat → Real),
  DecrAlmostLinearSSSP.Decremental.Subpolynomial a →
    DecrAlmostLinearSSSP.Decremental.Subpolynomial b →
      DecrAlmostLinearSSSP.Decremental.Subpolynomial fun m =>
        @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (a m) (b m) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.1.2.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.subpolynomial_add : ∀ (a b : Nat → Real),
  DecrAlmostLinearSSSP.Decremental.Subpolynomial a →
    DecrAlmostLinearSSSP.Decremental.Subpolynomial b →
      DecrAlmostLinearSSSP.Decremental.Subpolynomial fun m =>
        @HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (a m) (b m) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.1.2.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.logarithm2_nonneg : ∀ {x : Real},
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) x →
    @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (DecrAlmostLinearSSSP.Decremental.logarithm2 x) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.1.2.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.scaleCount_saturated_bound : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
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
          (DecrAlmostLinearSSSP.Decremental.logarithm2 (@Nat.cast.{0} Real Real.instNatCast i.W)))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.1.2.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.subpolynomial_logarithm2_size : DecrAlmostLinearSSSP.Decremental.Subpolynomial fun m =>
  DecrAlmostLinearSSSP.Decremental.logarithm2
    (@Nat.cast.{0} Real Real.instNatCast
      (@Max.max.{0} Nat Nat.instMax (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.1.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.subpolynomial_scale_overhead : DecrAlmostLinearSSSP.Decremental.Subpolynomial fun m =>
  @HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
    (@OfNat.ofNat.{0} Real (nat_lit 3)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (DecrAlmostLinearSSSP.Decremental.logarithm2
      (@Nat.cast.{0} Real Real.instNatCast
        (@Max.max.{0} Nat Nat.instMax (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.1.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.Powers.Prefix.step : ∀ {bound base d : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Powers.Prefix bound base d s →
    DecrAlmostLinearSSSP.Decremental.Exact.Powers.Prefix bound base
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (DecrAlmostLinearSSSP.Decremental.Exact.Powers.advanced s) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.1.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.bankFactor_positive : ∀ (j : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
    (DecrAlmostLinearSSSP.Decremental.bankFactor j) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.1.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.ShadowRep.metadata : ∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
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
          halted := g.halted, fault := g.fault, work := work } := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.1.1.1.1.2.2
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
theorem DecrAlmostLinearSSSP.Decremental.Reachable.trans : ∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {u v w : Fin n},
  @DecrAlmostLinearSSSP.Decremental.Reachable n k g active u v →
    @DecrAlmostLinearSSSP.Decremental.Reachable n k g active v w →
      @DecrAlmostLinearSSSP.Decremental.Reachable n k g active u w := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.prepare_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.prepare s
    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
    (DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.prepared s) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_6.1.2.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.code_real_frame : ∀ (j : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.code j := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_6.1.2.2.1.2.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory.target : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)} {tentative : Fin i.n → Option.{0} Nat}
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
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_7.2.1.2.2.1.2
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
theorem DecrAlmostLinearSSSP.Decremental.PreservesOutside.trans : ∀ {base F : Nat} {c d e : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.PreservesOutside base F c d →
    DecrAlmostLinearSSSP.Decremental.PreservesOutside base F d e →
      DecrAlmostLinearSSSP.Decremental.PreservesOutside base F c e := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_2.1.1.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.Structured.Eval.flag_bound : ∀ {cmd : DecrAlmostLinearSSSP.Decremental.Structured.Cmd} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {cost k : Nat},
  DecrAlmostLinearSSSP.Decremental.Structured.Eval cmd s cost t →
    DecrAlmostLinearSSSP.Decremental.Structured.FlagFrame cmd k →
      @LE.le.{0} Nat instLENat (s.natReg k) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
        @LE.le.{0} Nat instLENat (t.natReg k) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_2.1.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.ShadowDataRep.halt_flag : ∀ {B F : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F s g →
    @LE.le.{0} Nat instLENat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        (@ite.{1} Nat (@Eq.{1} Bool g.halted Bool.true) (instDecidableEqBool g.halted Bool.true)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_2.1.2.2.1.2.2.2
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
theorem DecrAlmostLinearSSSP.Decremental.utilityDepth_bound : ∀ (m : Nat),
  @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast (DecrAlmostLinearSSSP.Decremental.utilityDepth m))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      (@OfNat.ofNat.{0} Real (nat_lit 12)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 12) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))))))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (DecrAlmostLinearSSSP.Decremental.logarithm2
          (@Nat.cast.{0} Real Real.instNatCast
            (@Max.max.{0} Nat Nat.instMax (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_3.1.1.2.2.1.2
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
theorem DecrAlmostLinearSSSP.Decremental.ScaledCeiling.productReal_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (d p x N : Nat),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (s.realReg x) →
        @LE.le.{0} Real Real.instLE (s.realReg x)
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              N) →
          ∃ cost t,
            And
              (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.productReal d p x) s cost t)
              (And
                (@Eq.{1} Nat (t.natReg d)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (s.natReg p)
                    (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
                      (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing)
                      (s.realReg x))))
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
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                  (And
                    (∀ (address : Nat),
                      (∀ (a : Nat),
                          @Ne.{1} Nat address
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 48) (instOfNatNat (nat_lit 48))))
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a))
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                        And (@Eq.{1} Real (t.realMem address) (s.realMem address))
                          (@Eq.{1} Nat (t.natMem address) (s.natMem address)))
                    (∀ (k : Nat),
                      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
                        @Even.{0} Nat instAddNat k →
                          @Ne.{1} Nat k d →
                            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
                              And (@Eq.{1} Nat (t.natReg k) (s.natReg k)) (@Eq.{1} Real (t.realReg k) (s.realReg k)))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_3.1.2.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.ScaledCeiling.productReal_nat_frame : ∀ (d p x k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k d →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
            (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.productReal d p x) k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_3.1.2.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.ScaledCeiling.productReal_real_frame : ∀ (d p x k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
        DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
          (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.productReal d p x) k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_3.1.2.2.1.2.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.ScaleParameters.prepare_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    @LT.lt.{0} Real Real.instLT
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@Nat.cast.{0} Real Real.instNatCast i.size))
        i.accuracy →
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
                      ∃ cost t,
                        And
                          (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                            DecrAlmostLinearSSSP.Decremental.ScaleParameters.prepare s cost t)
                          (And
                            (@LE.le.{0} Nat instLENat cost
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
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
                                      (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))))
                                (@OfNat.ofNat.{0} Nat (nat_lit 88) (instOfNatNat (nat_lit 88)))))
                            (And
                              (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 154) (instOfNatNat (nat_lit 154))))
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (DecrAlmostLinearSSSP.Decremental.bankFactor
                                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 110) (instOfNatNat (nat_lit 110)))))
                                  i.n))
                              (And
                                (@Eq.{1} Nat
                                  (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 156) (instOfNatNat (nat_lit 156))))
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (DecrAlmostLinearSSSP.Decremental.bankFactor
                                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 110) (instOfNatNat (nat_lit 110)))))
                                    i.k))
                                (And
                                  (@Eq.{1} Nat
                                    (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 158) (instOfNatNat (nat_lit 158))))
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (DecrAlmostLinearSSSP.Decremental.bankFactor
                                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 110) (instOfNatNat (nat_lit 110)))))
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64))) i.size)))
                                  (And
                                    (@Eq.{1} Nat
                                      (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 160) (instOfNatNat (nat_lit 160))))
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (DecrAlmostLinearSSSP.Decremental.bankFactor
                                          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 110) (instOfNatNat (nat_lit 110)))))
                                        (@Fin.val i.n i.source)))
                                    (And
                                      (@Eq.{1} Nat
                                        (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 152) (instOfNatNat (nat_lit 152))))
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (DecrAlmostLinearSSSP.Decremental.bankFactor
                                            (s.natReg
                                              (@OfNat.ofNat.{0} Nat (nat_lit 110) (instOfNatNat (nat_lit 110)))))
                                          (DecrAlmostLinearSSSP.Decremental.barrierHigh i)))
                                      (∀ (address : Nat),
                                        (∀ (a : Nat),
                                            @Ne.{1} Nat address
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (s.natReg
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 48) (instOfNatNat (nat_lit 48))))
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a))
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                                          And (@Eq.{1} Real (t.realMem address) (s.realMem address))
                                            (@Eq.{1} Nat (t.natMem address) (s.natMem address))))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_3.2.1.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.registerBound_ge : ∀ (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
    (DecrAlmostLinearSSSP.Decremental.registerBound code) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_3.2.2.1.1.1.1
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
theorem DecrAlmostLinearSSSP.Decremental.eval_observed_dispatch_aux : ∀ {B bank start : Nat} (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (pc : Nat)
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
                                    t))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_5.1.2.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.observedDispatchAux_nat_frame : ∀ (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (start k : Nat),
  Or (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (Or (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
      (DecrAlmostLinearSSSP.Decremental.observedDispatchAux start code) k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_5.1.2.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.observedDispatchAux_real_frame : ∀ (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (start : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
    (DecrAlmostLinearSSSP.Decremental.observedDispatchAux start code)
    (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_5.1.2.2.1.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.observedDispatchAux_flag_frame : ∀ (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (start : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.FlagFrame
    (DecrAlmostLinearSSSP.Decremental.observedDispatchAux start code)
    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_5.1.2.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.observedDispatchAux_nat14_frame : ∀ (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (pc : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.observedDispatchAux pc code)
    (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_5.1.2.2.2.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame.seq : ∀ {a b : DecrAlmostLinearSSSP.Decremental.Structured.Cmd},
  DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame a →
    DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame b →
      DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame (a.seq b) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_5.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.Globals.transfer : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B utility cost : Nat}
  {cmd : DecrAlmostLinearSSSP.Decremental.Structured.Cmd} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.Globals i B utility s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval cmd s cost t →
      DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame cmd →
        DecrAlmostLinearSSSP.Decremental.Native.Globals i B utility t := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_5.2.2.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Native.BankFrame.seq : ∀ {a b : DecrAlmostLinearSSSP.Decremental.Structured.Cmd},
  DecrAlmostLinearSSSP.Decremental.Native.BankFrame a →
    DecrAlmostLinearSSSP.Decremental.Native.BankFrame b → DecrAlmostLinearSSSP.Decremental.Native.BankFrame (a.seq b) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_6.1.1.2.2.1.1
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
theorem DecrAlmostLinearSSSP.Decremental.Native.record_cell_before_caches : ∀ (B n S reserve N j r : Nat),
  @LT.lt.{0} Nat instLTNat j S →
    @LT.lt.{0} Nat instLTNat r
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) N
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) →
      @LT.lt.{0} Nat instLTNat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (DecrAlmostLinearSSSP.Decremental.Native.recordAt
            (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B n S reserve N).records
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) N)
              (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
            j)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
        (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B n S reserve N).caches := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_7.2.1.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Native.cache_cells_injective : ∀ {B n S reserve N j k v w : Nat},
  @LT.lt.{0} Nat instLTNat v n →
    @LT.lt.{0} Nat instLTNat w n →
      @Eq.{1} Nat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (DecrAlmostLinearSSSP.Decremental.Native.cacheAt
              (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B n S reserve N).caches n j)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) v))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (DecrAlmostLinearSSSP.Decremental.Native.cacheAt
              (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B n S reserve N).caches n k)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)) →
        @Eq.{1} Nat j k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_7.2.1.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.Native.normalSetup_eval : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (coefficient N : Nat),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) N →
        ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
          DecrAlmostLinearSSSP.Decremental.InputCapture.RawInput i s →
            @Eq.{1} (Nat → Nat) s.natMem (DecrAlmostLinearSSSP.Decremental.initialMachine p i).natMem →
              (@Eq.{1} (Nat → Real) s.realMem fun x =>
                  @OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
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
                        (DecrAlmostLinearSSSP.Decremental.Native.normalSetup coefficient N) s cost t)
                      (And
                        (@LE.le.{0} Nat instLENat cost
                          (DecrAlmostLinearSSSP.Decremental.Native.setupCost i coefficient N))
                        (And
                          (DecrAlmostLinearSSSP.Decremental.Native.Globals i
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i)
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) coefficient
                                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                      (@instHPow.{0, 0} Nat Nat
                                        (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                      i.size (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                N).utility
                            t)
                          (And
                            (DecrAlmostLinearSSSP.Decremental.Layout.Represents t
                              (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i)
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) coefficient
                                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                      (@instHPow.{0, 0} Nat Nat
                                        (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                      i.size (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                N))
                            (And
                              (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 60) (instOfNatNat (nat_lit 60))))
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) coefficient
                                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                      (@instHPow.{0, 0} Nat Nat
                                        (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                      i.size (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                              (And
                                (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
                                  (DecrAlmostLinearSSSP.Decremental.scaleCount i))
                                (And
                                  (@Eq.{1} Nat
                                    (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 100) (instOfNatNat (nat_lit 100))))
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) i.n))
                                  (And
                                    (∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
                                      DecrAlmostLinearSSSP.Decremental.SourceMemory.Image
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q) t
                                        (fun x => @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) fun x =>
                                        @OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                    (And
                                      (∀ (address : Nat),
                                        @LE.le.{0} Nat instLENat address
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
                                          @Eq.{1} Nat (t.natMem address)
                                            ((DecrAlmostLinearSSSP.Decremental.initialMachine p i).natMem address))
                                      (∀ (r : Nat),
                                        @LE.le.{0} Nat instLENat N r →
                                          And
                                            (@Eq.{1} Nat (t.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg r))
                                              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                            (@Eq.{1} Real (t.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg r))
                                              (@OfNat.ofNat.{0} Real (nat_lit 0)
                                                (@Zero.toOfNat0.{0} Real Real.instZero)))))))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_7.2.1.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.FootprintFrame.preserves_scale : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program} {B S reserve j k : Nat}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine}
  {b : Fin i.n → ENNReal},
  DecrAlmostLinearSSSP.Decremental.Native.FootprintFrame B i.n S reserve
      (DecrAlmostLinearSSSP.Decremental.registerBound p.code) j s t →
    @LT.lt.{0} Nat instLTNat j S →
      @LT.lt.{0} Nat instLTNat k S →
        @Ne.{1} Nat j k →
          DecrAlmostLinearSSSP.Decremental.Native.ScaleMemory i p B k
              (DecrAlmostLinearSSSP.Decremental.Native.recordAt
                (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n S reserve
                    (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).records
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (DecrAlmostLinearSSSP.Decremental.registerBound p.code))
                  (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                k)
              (DecrAlmostLinearSSSP.Decremental.Native.cacheAt
                (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n S reserve
                    (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).caches
                i.n k)
              (DecrAlmostLinearSSSP.Decremental.Native.recordAt
                (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n S reserve
                    (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).records
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (DecrAlmostLinearSSSP.Decremental.registerBound p.code))
                  (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              g b s →
            DecrAlmostLinearSSSP.Decremental.Native.ScaleMemory i p B k
              (DecrAlmostLinearSSSP.Decremental.Native.recordAt
                (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n S reserve
                    (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).records
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (DecrAlmostLinearSSSP.Decremental.registerBound p.code))
                  (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                k)
              (DecrAlmostLinearSSSP.Decremental.Native.cacheAt
                (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n S reserve
                    (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).caches
                i.n k)
              (DecrAlmostLinearSSSP.Decremental.Native.recordAt
                (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n S reserve
                    (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).records
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (DecrAlmostLinearSSSP.Decremental.registerBound p.code))
                  (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              g b t := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_7.2.1.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.polynomial_maintains_barrier : ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (C : Real) (a : Nat → Real) (queryBound : Nat),
  (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
      i.Valid →
        @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) i.n →
          @LE.le.{0} Nat instLENat i.W
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) i.size
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
            @LT.lt.{0} Real Real.instLT
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                  (@Nat.cast.{0} Real Real.instNatCast i.size))
                i.accuracy →
              @LT.lt.{0} Real Real.instLT i.accuracy
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
                DecrAlmostLinearSSSP.Decremental.Maintains p C a queryBound Bool.false i) →
    ∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
      i.Valid →
        @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) i.n →
          @LT.lt.{0} Real Real.instLT
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                (@Nat.cast.{0} Real Real.instNatCast i.size))
              i.accuracy →
            ∀ (j : Nat),
              DecrAlmostLinearSSSP.Decremental.Maintains p C a queryBound Bool.false
                (DecrAlmostLinearSSSP.Decremental.barrierInput i j) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_7.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.choose_initial_family : ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (C : Real) (a : Nat → Real) (queryBound : Nat),
  (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
      i.Valid →
        @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) i.n →
          @LE.le.{0} Nat instLENat i.W
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) i.size
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
            @LT.lt.{0} Real Real.instLT
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                  (@Nat.cast.{0} Real Real.instNatCast i.size))
                i.accuracy →
              @LT.lt.{0} Real Real.instLT i.accuracy
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
                DecrAlmostLinearSSSP.Decremental.Maintains p C a queryBound Bool.false i) →
    ∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
      i.Valid →
        @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) i.n →
          @LT.lt.{0} Real Real.instLT
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                (@Nat.cast.{0} Real Real.instNatCast i.size))
              i.accuracy →
            ∃ (f : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → DecrAlmostLinearSSSP.Decremental.Machine),
              ∀ (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
                DecrAlmostLinearSSSP.Decremental.Native.InitialFacts p C a i
                  (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) (f j) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_7.2.1.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Native.max_initial_work_bound : ∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {C : Real} {a : Nat → Real}
  {i : DecrAlmostLinearSSSP.Decremental.Input}
  (f : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → DecrAlmostLinearSSSP.Decremental.Machine),
  (∀ (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
      DecrAlmostLinearSSSP.Decremental.Native.InitialFacts p C a i
        (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) (f j)) →
    @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@OfNat.ofNat.{0} Real (nat_lit 64)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 64) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 63) (instOfNatNat (nat_lit 63)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 62) (instOfNatNat (nat_lit 62)))))))
                (@Nat.cast.{0} Real Real.instNatCast i.size)))
            (a
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64))) i.size)))
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            i.accuracy
            (@OfNat.ofNat.{0} Real (nat_lit 16)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))))))) →
      @LE.le.{0} Real Real.instLE
        (@Nat.cast.{0} Real Real.instNatCast (@DecrAlmostLinearSSSP.Decremental.Native.maxInitialWork i f))
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@OfNat.ofNat.{0} Real (nat_lit 64)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 64) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 63) (instOfNatNat (nat_lit 63)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 62) (instOfNatNat (nat_lit 62)))))))
                (@Nat.cast.{0} Real Real.instNatCast i.size)))
            (a
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64))) i.size)))
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            i.accuracy
            (@OfNat.ofNat.{0} Real (nat_lit 16)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_7.2.2.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Native.controlFrame_scaleInitAll : ∀ (p : DecrAlmostLinearSSSP.Decremental.Program),
  DecrAlmostLinearSSSP.Decremental.Native.ControlFrame (DecrAlmostLinearSSSP.Decremental.Native.scaleInitAll p) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_7.2.2.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.Native.initAll_eval : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (C : Real) (a : Nat → Real) (queryBound : Nat),
      @LT.lt.{0} Real Real.instLT
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@Nat.cast.{0} Real Real.instNatCast i.size))
          i.accuracy →
        ∀ (B reserve : Nat),
          @LE.le.{0} Nat instLENat
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
              B →
            ∀ (f : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → DecrAlmostLinearSSSP.Decremental.Machine),
              (∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
                  DecrAlmostLinearSSSP.Decremental.Native.InitialFacts p C a i
                    (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q) (f q)) →
                (∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
                    DecrAlmostLinearSSSP.Decremental.Maintains p C a queryBound Bool.false
                      (DecrAlmostLinearSSSP.Decremental.barrierInput i
                        (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q))) →
                  ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
                    DecrAlmostLinearSSSP.Decremental.Native.Globals i B
                        (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n
                            (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve
                            (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).utility
                        s →
                      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 84) (instOfNatNat (nat_lit 84))))
                          (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n
                              (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve
                              (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).records →
                        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 88) (instOfNatNat (nat_lit 88))))
                            (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n
                                (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve
                                (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).caches →
                          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
                              (DecrAlmostLinearSSSP.Decremental.scaleCount i) →
                            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 100) (instOfNatNat (nat_lit 100))))
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) i.n) →
                              (∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
                                  DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B
                                    (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q) s
                                    (fun x => @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) fun x =>
                                    @OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
                                (∀ (address : Nat),
                                    @LE.le.{0} Nat instLENat address B →
                                      @Eq.{1} Nat (s.natMem address)
                                        ((DecrAlmostLinearSSSP.Decremental.initialMachine p i).natMem address)) →
                                  (∀ (r : Nat),
                                      @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.registerBound p.code)
                                          r →
                                        And
                                          (@Eq.{1} Nat (s.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg r))
                                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                          (@Eq.{1} Real (s.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg r))
                                            (@OfNat.ofNat.{0} Real (nat_lit 0)
                                              (@Zero.toOfNat0.{0} Real Real.instZero)))) →
                                    ∃ cost t,
                                      And
                                        (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                          (DecrAlmostLinearSSSP.Decremental.Native.scaleInitAll p) s cost t)
                                        (And
                                          (DecrAlmostLinearSSSP.Decremental.Native.InitPrefix i p B reserve f
                                            (DecrAlmostLinearSSSP.Decremental.scaleCount i) t)
                                          (@LE.le.{0} Nat instLENat cost
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (DecrAlmostLinearSSSP.Decremental.dispatchCharge p.code)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                      (@DecrAlmostLinearSSSP.Decremental.Native.maxInitialWork i f))
                                                    (DecrAlmostLinearSSSP.Decremental.Native.initOverhead i p))
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                                                (DecrAlmostLinearSSSP.Decremental.scaleCount i))
                                              (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_7.2.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.clearLast_nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 218) (instOfNatNat (nat_lit 218))) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Native.clearLast k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_7.2.2.2.1.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Native.finalize_init : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (p : DecrAlmostLinearSSSP.Decremental.Program) (B reserve : Nat)
  (f : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → DecrAlmostLinearSSSP.Decremental.Machine)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Native.InitPrefix i p B reserve f (DecrAlmostLinearSSSP.Decremental.scaleCount i) s →
    ∃ t,
      And
        (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Native.clearLast s
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) t)
        (DecrAlmostLinearSSSP.Decremental.Native.InitDone i p B reserve f t) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_7.2.2.2.2.2.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.adapterWrite_pointer_unconditional : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (s : DecrAlmostLinearSSSP.Decremental.AdapterState i),
  (∀ (u : Fin i.n),
      DecrAlmostLinearSSSP.Decremental.PointerValid i (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i s) u
        (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i s u)) →
    ∀ (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n) (value : ENNReal),
      @Eq.{1} (Fin i.n → Nat)
        (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i
          (DecrAlmostLinearSSSP.Decremental.adapterWrite i s j v value))
        (@Function.update.{1, 1} (Fin i.n) (fun a => Nat) (instDecidableEqFin i.n)
          (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i s) v
          (DecrAlmostLinearSSSP.Decremental.advance i
            (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i
              (DecrAlmostLinearSSSP.Decremental.adapterWrite i s j v value))
            v
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (DecrAlmostLinearSSSP.Decremental.scaleCount i)
              (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i s v))
            (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i s v))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_8.1.2.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.adapterWrite_dirty_subset : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (s : DecrAlmostLinearSSSP.Decremental.AdapterState i)
  (marked : Finset.{0} (Fin i.n)),
  @LE.le.{0} (Finset.{0} (Fin i.n))
      (@Preorder.toLE.{0} (Finset.{0} (Fin i.n))
        (@PartialOrder.toPreorder.{0} (Finset.{0} (Fin i.n)) (@Finset.instPartialOrder.{0} (Fin i.n))))
      (@DecrAlmostLinearSSSP.Decremental.AdapterState.dirty i s) marked →
    ∀ (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n) (value : ENNReal),
      @LE.le.{0} (Finset.{0} (Fin i.n))
        (@Preorder.toLE.{0} (Finset.{0} (Fin i.n))
          (@PartialOrder.toPreorder.{0} (Finset.{0} (Fin i.n)) (@Finset.instPartialOrder.{0} (Fin i.n))))
        (@DecrAlmostLinearSSSP.Decremental.AdapterState.dirty i
          (DecrAlmostLinearSSSP.Decremental.adapterWrite i s j v value))
        (@Insert.insert.{0, 0} (Fin i.n) (Finset.{0} (Fin i.n))
          (@Finset.instInsert.{0} (Fin i.n) (instDecidableEqFin i.n)) v marked) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_8.1.2.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.LinkedScan.rowsFrom_selected : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input)
  (b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal) (v : Fin i.n)
  (row : Nat → DecrAlmostLinearSSSP.Decremental.LinkedScan.Row) (record : Nat → Nat),
  (∀ (j : Nat), Iff (row j).Eligible (@Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.eligible i b v j) Bool.true)) →
    (∀ (j : Nat), @Eq.{1} Nat (row j).address (record j)) →
      ∀ (fuel p : Nat),
        @Eq.{1} Nat (record (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) p fuel))
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
          @Eq.{1} Nat
            (DecrAlmostLinearSSSP.Decremental.LinkedScan.selectedAddress
              (DecrAlmostLinearSSSP.Decremental.LinkedScan.rowsFrom row fuel p))
            (record (DecrAlmostLinearSSSP.Decremental.advance i b v fuel p)) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_8.1.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.LinkedScan.rowsFrom_travel : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input)
  (b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal) (v : Fin i.n)
  (row : Nat → DecrAlmostLinearSSSP.Decremental.LinkedScan.Row),
  (∀ (j : Nat), Iff (row j).Eligible (@Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.eligible i b v j) Bool.true)) →
    ∀ (fuel p : Nat),
      @Eq.{1} Nat
        (DecrAlmostLinearSSSP.Decremental.LinkedScan.skipped
          (DecrAlmostLinearSSSP.Decremental.LinkedScan.rowsFrom row fuel p))
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
          (DecrAlmostLinearSSSP.Decremental.advance i b v fuel p) p) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_8.1.2.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Native.scanRow_address : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (recordBase cacheBase stride : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (v : Fin i.n) (j : Nat),
  @Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.Native.scanRow i recordBase cacheBase stride s v j).address
    (DecrAlmostLinearSSSP.Decremental.Native.scanRecord i recordBase stride j) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_8.1.2.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.scanRows_view : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (recordBase cacheBase stride : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data)
  (b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal),
  DecrAlmostLinearSSSP.Decremental.Native.ScanTable i recordBase cacheBase stride b s →
    ∀ (v : Fin i.n) (fuel start : Nat),
      @Eq.{1} Nat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start fuel)
          (DecrAlmostLinearSSSP.Decremental.scaleCount i) →
        DecrAlmostLinearSSSP.Decremental.LinkedScan.RowsView s
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val i.n v))
          (DecrAlmostLinearSSSP.Decremental.LinkedScan.rowsFrom
            (DecrAlmostLinearSSSP.Decremental.Native.scanRow i recordBase cacheBase stride s v) fuel start) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_8.1.2.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.scanRow_eligible : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (recordBase cacheBase stride : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data)
  (b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal),
  DecrAlmostLinearSSSP.Decremental.Native.ScanTable i recordBase cacheBase stride b s →
    ∀ (v : Fin i.n) (j : Nat),
      Iff (DecrAlmostLinearSSSP.Decremental.Native.scanRow i recordBase cacheBase stride s v j).Eligible
        (@Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.eligible i b v j) Bool.true) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_8.1.2.2.1.2.2.2
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
theorem DecrAlmostLinearSSSP.Decremental.Native.pointerBody_nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 38) (instOfNatNat (nat_lit 38))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 196) (instOfNatNat (nat_lit 196))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 42) (instOfNatNat (nat_lit 42))) →
              @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 44) (instOfNatNat (nat_lit 44))) →
                @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 46) (instOfNatNat (nat_lit 46))) →
                  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 184) (instOfNatNat (nat_lit 184))) →
                    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 180) (instOfNatNat (nat_lit 180))) →
                      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 182) (instOfNatNat (nat_lit 182))) →
                        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94))) →
                          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
                            DecrAlmostLinearSSSP.Decremental.Native.pointerBody k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_8.2.1.2.1.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Native.pointerArray_before_record : ∀ {B n S reserve N address : Nat},
  DecrAlmostLinearSSSP.Decremental.Native.PointerArrayCell
      (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B n S reserve N) n address →
    @LT.lt.{0} Nat instLTNat address (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B n S reserve N).record := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_8.2.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.pointerArray_above_base : ∀ {B n S reserve N address : Nat},
  DecrAlmostLinearSSSP.Decremental.Native.PointerArrayCell
      (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B n S reserve N) n address →
    @LT.lt.{0} Nat instLTNat B address := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_8.2.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.pointerLayout_order : ∀ (B n S reserve N : Nat),
  And
    (@LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B n S reserve N).record
      (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B n S reserve N).cache)
    (And
      (∀ (v : Nat),
        @LT.lt.{0} Nat instLTNat v n →
          @LT.lt.{0} Nat instLTNat
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B n S reserve N).pointer
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) v))
            (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B n S reserve N).flags)
      (And
        (∀ (v : Nat),
          @LT.lt.{0} Nat instLTNat v n →
            @LT.lt.{0} Nat instLTNat
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B n S reserve N).flags
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) v))
              (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B n S reserve N).list)
        (∀ (v : Nat),
          @LT.lt.{0} Nat instLTNat v n →
            @LT.lt.{0} Nat instLTNat
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B n S reserve N).list
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) v))
              (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B n S reserve N).record))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_8.2.2.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.Native.PublicFrame.trans : ∀ {l : DecrAlmostLinearSSSP.Decremental.Native.PointerLayout} {n : Nat}
  {s t u : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.PublicFrame l n s t →
    DecrAlmostLinearSSSP.Decremental.Native.PublicFrame l n t u →
      DecrAlmostLinearSSSP.Decremental.Native.PublicFrame l n s u := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_8.2.2.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.PublicFrame.preserves_scale : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program} {B S reserve j next : Nat}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine}
  {b : Fin i.n → ENNReal},
  DecrAlmostLinearSSSP.Decremental.Native.PublicFrame
      (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n S reserve
        (DecrAlmostLinearSSSP.Decremental.registerBound p.code))
      i.n s t →
    @LE.le.{0} Nat instLENat i.n B →
      DecrAlmostLinearSSSP.Decremental.Native.ScaleMemory i p B j
          (DecrAlmostLinearSSSP.Decremental.Native.recordAt
            (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n S reserve
                (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).records
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (DecrAlmostLinearSSSP.Decremental.registerBound p.code))
              (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
            j)
          (DecrAlmostLinearSSSP.Decremental.Native.cacheAt
            (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n S reserve
                (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).caches
            i.n j)
          next g b s →
        DecrAlmostLinearSSSP.Decremental.Native.ScaleMemory i p B j
          (DecrAlmostLinearSSSP.Decremental.Native.recordAt
            (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n S reserve
                (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).records
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (DecrAlmostLinearSSSP.Decremental.registerBound p.code))
              (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
            j)
          (DecrAlmostLinearSSSP.Decremental.Native.cacheAt
            (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n S reserve
                (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).caches
            i.n j)
          next g b t := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_8.2.2.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.Native.pointerStart_nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 182) (instOfNatNat (nat_lit 182))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 180) (instOfNatNat (nat_lit 180))) →
        DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Native.pointerStart k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_8.2.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.PointerBases.start : ∀ {record pointer flags list cost : Nat} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.PointerBases record pointer flags list s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Native.pointerStart s cost t →
      DecrAlmostLinearSSSP.Decremental.Native.PointerBases record pointer flags list t := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_9.1.1.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.buildPointers_eval : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (B reserve N : Nat)
  (b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Native.Globals i B
      (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve
          N).utility
      s →
    DecrAlmostLinearSSSP.Decremental.Native.PointerBases
        (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i)
            reserve N).record
        (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i)
            reserve N).pointer
        (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i)
            reserve N).flags
        (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i)
            reserve N).list
        s →
      DecrAlmostLinearSSSP.Decremental.Native.ScanTable i
          (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i)
              reserve N).record
          (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i)
              reserve N).cache
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) N)
            (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
          b s →
        ∃ cost t,
          And
            (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Native.buildPointers s
              cost t)
            (And
              (@LE.le.{0} Nat instLENat cost
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
                        (DecrAlmostLinearSSSP.Decremental.scaleCount i))
                      (@OfNat.ofNat.{0} Nat (nat_lit 28) (instOfNatNat (nat_lit 28))))
                    i.n)
                  (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))
              (And (DecrAlmostLinearSSSP.Decremental.Native.PointerPrefix i B reserve N b i.n t)
                (DecrAlmostLinearSSSP.Decremental.Native.PublicFrame
                  (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                    (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N)
                  i.n s t))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_9.1.1.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.Native.tailFrame_buildPointers : DecrAlmostLinearSSSP.Decremental.TailFrame DecrAlmostLinearSSSP.Decremental.Native.buildPointers := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_9.1.1.1.2.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.Native.tailFrame_commit : DecrAlmostLinearSSSP.Decremental.TailFrame DecrAlmostLinearSSSP.Decremental.DirtyCommit.code := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_9.2.1.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.Native.commit_initial_pointers : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (B reserve N : Nat)
  (b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Native.PointerPrefix i B reserve N b i.n s →
    @LE.le.{0} Nat instLENat i.n B →
      ∃ cost t,
        And
          (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.DirtyCommit.code s cost t)
          (And
            (@LE.le.{0} Nat instLENat cost
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) i.n)
                (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
            (And
              (DecrAlmostLinearSSSP.Decremental.Native.Globals i B
                (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n
                    (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).utility
                t)
              (And
                (@DecrAlmostLinearSSSP.Decremental.DirtyMark.View i.n
                  (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                      (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).flags
                  (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                      (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).list
                  (@List.nil.{0} (Fin i.n)) t)
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
                  (And
                    (∀ (v : Fin i.n),
                      @Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.stored t.machine (@Fin.val i.n v))
                        (DecrAlmostLinearSSSP.Decremental.selected i b
                          (DecrAlmostLinearSSSP.Decremental.Native.initialPointers i b) v))
                    (And
                      (∀ (v : Fin i.n),
                        @Eq.{1} Nat
                          (t.natMem
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                                  (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).pointer
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val i.n v))))
                          (DecrAlmostLinearSSSP.Decremental.Native.scanRecord i
                            (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                                (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).record
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) N)
                              (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                            (DecrAlmostLinearSSSP.Decremental.Native.initialPointers i b v)))
                      (DecrAlmostLinearSSSP.Decremental.Native.PublicFrame
                        (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                          (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N)
                        i.n s t))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_9.2.1.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.initial_selected_accuracy : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (C : Real) (a : Nat → Real)
      (f : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → DecrAlmostLinearSSSP.Decremental.Machine),
      (∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
          DecrAlmostLinearSSSP.Decremental.Native.InitialFacts p C a i
            (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q) (f q)) →
        ∀ (v : Fin i.n),
          And
            (@LE.le.{0} ENNReal ENNReal.instLE (i.dist (@List.nil.{0} (Fin i.k)) v)
              (DecrAlmostLinearSSSP.Decremental.selected i
                (fun q v => DecrAlmostLinearSSSP.Decremental.stored (f q) (@Fin.val i.n v))
                (DecrAlmostLinearSSSP.Decremental.Native.initialPointers i fun q v =>
                  DecrAlmostLinearSSSP.Decremental.stored (f q) (@Fin.val i.n v))
                v))
            (And
              (@LE.le.{0} ENNReal ENNReal.instLE
                (DecrAlmostLinearSSSP.Decremental.selected i
                  (fun q v => DecrAlmostLinearSSSP.Decremental.stored (f q) (@Fin.val i.n v))
                  (DecrAlmostLinearSSSP.Decremental.Native.initialPointers i fun q v =>
                    DecrAlmostLinearSSSP.Decremental.stored (f q) (@Fin.val i.n v))
                  v)
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
                (@Eq.{1} ENNReal
                  (DecrAlmostLinearSSSP.Decremental.selected i
                    (fun q v => DecrAlmostLinearSSSP.Decremental.stored (f q) (@Fin.val i.n v))
                    (DecrAlmostLinearSSSP.Decremental.Native.initialPointers i fun q v =>
                      DecrAlmostLinearSSSP.Decremental.stored (f q) (@Fin.val i.n v))
                    v)
                  (@Top.top.{0} ENNReal ENNReal.instTop))
                (Not
                  (@DecrAlmostLinearSSSP.Decremental.Reachable i.n i.k i.graph
                    (@DecrAlmostLinearSSSP.Decremental.live i.k (@List.nil.{0} (Fin i.k))) i.source v)))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_9.2.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.initDone_scanTable : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (p : DecrAlmostLinearSSSP.Decremental.Program) (B reserve : Nat)
  (f : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → DecrAlmostLinearSSSP.Decremental.Machine)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Native.InitDone i p B reserve f s →
    DecrAlmostLinearSSSP.Decremental.Native.ScanTable i
      (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i)
          reserve (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).record
      (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i)
          reserve (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).cache
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (DecrAlmostLinearSSSP.Decremental.registerBound p.code))
        (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
      (fun q v => DecrAlmostLinearSSSP.Decremental.stored (f q) (@Fin.val i.n v)) s := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_9.2.2.2.2.2.2.2
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
lemma initializePublic_eval (i : Input) (hi : i.Valid) (p : Program) (C : ℝ) (a : ℕ → ℝ)
    (B reserve : ℕ) (f : Fin (scaleCount i) → Machine) (hf : ∀ q, InitialFacts p C a i q.val (f q))
    (s : Data) (h : InitDone i p B reserve f s) (hB : i.n ≤ B)
    (hb : PointerBases (pointerLayout B i.n (scaleCount i) reserve (registerBound p.code)).record
      (pointerLayout B i.n (scaleCount i) reserve (registerBound p.code)).pointer
      (pointerLayout B i.n (scaleCount i) reserve (registerBound p.code)).flags
      (pointerLayout B i.n (scaleCount i) reserve (registerBound p.code)).list s) :
    ∃ cost t, Eval initializePublic s cost t ∧ cost ≤ (13*scaleCount i+48)*i.n+11 ∧
      Globals i B (scaleLayout B i.n (scaleCount i) reserve (registerBound p.code)).utility t ∧
      (∀ q : Fin (scaleCount i), ScaleMemory i p B q.val
        (recordAt (scaleLayout B i.n (scaleCount i) reserve (registerBound p.code)).records (2*registerBound p.code+8) q.val)
        (cacheAt (scaleLayout B i.n (scaleCount i) reserve (registerBound p.code)).caches i.n q.val)
        (nextRecord (scaleLayout B i.n (scaleCount i) reserve (registerBound p.code)).records (2*registerBound p.code+8) (scaleCount i) q.val)
        (f q) (fun v => stored (f q) v.val) t) ∧
      DirtyMark.View (n := i.n) (pointerLayout B i.n (scaleCount i) reserve (registerBound p.code)).flags
        (pointerLayout B i.n (scaleCount i) reserve (registerBound p.code)).list [] t ∧
      stored t.machine i.source.val = 0 ∧
      (∀ v : Fin i.n, t.natMem v.val ≤ 1 ∧ (t.natMem v.val = 0 → 0 ≤ t.realMem v.val)) ∧
      (∀ v : Fin i.n, i.dist [] v ≤ stored t.machine v.val ∧
        stored t.machine v.val ≤ ENNReal.ofReal (1+i.accuracy)*i.dist [] v ∧
        (stored t.machine v.val = ⊤ ↔ ¬Reachable i.graph (live []) i.source v)) ∧
      (∀ v : Fin i.n, stored t.machine v.val = selected i (fun q v => stored (f q) v.val)
        (initialPointers i (fun q v => stored (f q) v.val)) v) ∧
      (∀ v : Fin i.n, t.natMem ((pointerLayout B i.n (scaleCount i) reserve (registerBound p.code)).pointer+2*v.val) =
        scanRecord i (pointerLayout B i.n (scaleCount i) reserve (registerBound p.code)).record (2*registerBound p.code+8)
          (initialPointers i (fun q v => stored (f q) v.val) v)) ∧
      (∀ r, registerBound p.code ≤ r → t.natReg (shadowReg r) = 0 ∧ t.realReg (shadowReg r) = 0) ∧
      PublicFrame (pointerLayout B i.n (scaleCount i) reserve (registerBound p.code)) i.n s t := by
  let b : Fin (scaleCount i) → Fin i.n → ℝ≥0∞ := fun q v => stored (f q) v.val
  have ht := initDone_scanTable i p B reserve f s h
  obtain ⟨cb,u,hu,hcb,huPrefix,huframe⟩ := buildPointers_eval i B reserve (registerBound p.code) b s h.globals hb ht
  obtain ⟨cc,t,hc,hcc,hg,hdirty,hnormal,hstored,hpointers,hcframe⟩ := commit_initial_pointers i B reserve
    (registerBound p.code) b u huPrefix hB
  have hframe := huframe.trans hcframe
  have hsource : stored t.machine i.source.val = 0 := by
    rw [hstored]
    simp [selected]
  have haccurate : ∀ v : Fin i.n, i.dist [] v ≤ stored t.machine v.val ∧
      stored t.machine v.val ≤ ENNReal.ofReal (1+i.accuracy)*i.dist [] v ∧
      (stored t.machine v.val = ⊤ ↔ ¬Reachable i.graph (live []) i.source v) := by
    intro v
    rw [hstored]
    exact initial_selected_accuracy i hi p C a f hf v
  have htailu := tailFrame_buildPointers.preserves hu (registerBound_ge p.code) h.tail
  have htailt := tailFrame_commit.preserves hc (registerBound_ge p.code) htailu
  refine ⟨cb+cc,t,Eval.seq hu hc,by nlinarith only [hcb,hcc],hg,?_,hdirty,hsource,hnormal,haccurate,hstored,hpointers,htailt,hframe⟩
  intro q
  exact hframe.preserves_scale hB (h.completed q)
end DecrAlmostLinearSSSP.Decremental.Native
end s217
section s218
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
lemma PublicControlFrame.seq {a b : Cmd} (ha : PublicControlFrame a) (hb : PublicControlFrame b) : PublicControlFrame (.seq a b) :=
  fun k hlo hhi hev h94 => ⟨ha k hlo hhi hev h94,hb k hlo hhi hev h94⟩
lemma ControlFrame.asPublic {cmd : Cmd} (h : ControlFrame cmd) : PublicControlFrame cmd := fun k hlo hhi hev _ => h k hlo hhi hev
lemma publicControlFrame_pointerStart : PublicControlFrame pointerStart := by
  intro k hlo hhi hev h94
  apply pointerStart_nat_frame <;> omega
lemma publicControlFrame_pointerBody : PublicControlFrame pointerBody := by
  intro k hlo hhi hev h94
  apply pointerBody_nat_frame <;> omega
lemma publicControlFrame_pointerLoop : PublicControlFrame pointerLoop := publicControlFrame_pointerBody
lemma publicControlFrame_buildPointers : PublicControlFrame buildPointers :=
  publicControlFrame_pointerStart.seq publicControlFrame_pointerLoop
lemma publicControlFrame_commit : PublicControlFrame DirtyCommit.code := by
  intro k hlo hhi hev h94
  apply DirtyCommit.code_nat_frame <;> omega
lemma publicControlFrame_initializePublic : PublicControlFrame initializePublic :=
  publicControlFrame_buildPointers.seq publicControlFrame_commit
lemma controlFrame_clearLast : ControlFrame clearLast := by
  intro k hlo hhi hev
  apply clearLast_nat_frame
  omega
lemma Controls.transfer {B n S reserve N cost : ℕ} {s t : Data} {cmd : Cmd}
    (h : Controls B n S reserve N s) (he : Eval cmd s cost t) (hf : PublicControlFrame cmd) : Controls B n S reserve N t := by
  have hn (k : ℕ) (hlo : 60 ≤ k) (hhi : k ≤ 104) (hev : Even k) (h94 : k ≠ 94) : t.natReg k = s.natReg k :=
    he.nat_frame (hf k hlo hhi hev h94)
  rcases h with ⟨_,_,_,_,_,_,_,_,_⟩
  constructor
  all_goals rw [hn _ (by omega) (by omega) (by decide) (by omega)]
  all_goals assumption
lemma Controls.pointerBases {B n S reserve N : ℕ} {s : Data} (h : Controls B n S reserve N s) :
    PointerBases (pointerLayout B n S reserve N).record (pointerLayout B n S reserve N).pointer
      (pointerLayout B n S reserve N).flags (pointerLayout B n S reserve N).list s :=
  ⟨h.records,h.pointers,h.flags,h.list⟩
end DecrAlmostLinearSSSP.Decremental.Native
end s218
section s219
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
lemma NormalMemory.source {i : Input} {p : Program} {B reserve : ℕ}
    {g : Fin (scaleCount i) → Machine} {b : Fin (scaleCount i) → Fin i.n → ℝ≥0∞} {ptr : Fin i.n → ℕ} {s : Data}
    (h : NormalMemory i p B reserve g b ptr s) : stored s.machine i.source.val = 0 := by
  rw [h.output]
  simp [selected]
lemma NormalMemory.scanTable {i : Input} {p : Program} {B reserve : ℕ}
    {g : Fin (scaleCount i) → Machine} {b : Fin (scaleCount i) → Fin i.n → ℝ≥0∞} {ptr : Fin i.n → ℕ} {s : Data}
    (h : NormalMemory i p B reserve g b ptr s) :
    ScanTable i (pointerLayout B i.n (scaleCount i) reserve (registerBound p.code)).record
      (pointerLayout B i.n (scaleCount i) reserve (registerBound p.code)).cache (2*registerBound p.code+8) b s := by
  constructor
  · dsimp [pointerLayout,scaleLayout,Layout.addresses]
    omega
  · intro q
    exact (h.scales q).metadata
  · intro q
    exact (h.scales q).cache
end DecrAlmostLinearSSSP.Decremental.Native
end s219
section s220
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
lemma normalInitialize_eval (i : Input) (hi : i.Valid) (hn2 : 2 ≤ i.n) (heps : 1/(i.size : ℝ) < i.accuracy)
    (p : Program) (C : ℝ) (a : ℕ → ℝ) (queryBound coefficient : ℕ)
    (hpoly : ∀ x : Input, x.Valid → 2 ≤ x.n → x.W ≤ x.size^2 →
      1/(x.size : ℝ) < x.accuracy → x.accuracy < 1 → Maintains p C a queryBound false x)
    (s : Data) (hraw : InputCapture.RawInput i s) (hn : s.natMem = (initialMachine p i).natMem) (hr : s.realMem = fun _ => 0)
    (htail : ∀ r, registerBound p.code ≤ r → s.natReg (shadowReg r) = 0 ∧ s.realReg (shadowReg r) = 0) :
    ∃ (f : Fin (scaleCount i) → Machine) (cost : ℕ) (t : Data), (∀ q, InitialFacts p C a i q.val (f q)) ∧
      Eval (normalInitialize coefficient p) s cost t ∧
      cost ≤ setupCost i coefficient (registerBound p.code)+
        ((dispatchCharge p.code+2)*maxInitialWork f+initOverhead i p+7)*scaleCount i+
        (13*scaleCount i+48)*i.n+22 ∧
      NormalMemory i p (i.n+3*i.k+2) (coefficient*i.size^3+1) f (fun q v => stored (f q) v.val)
        (initialPointers i (fun q v => stored (f q) v.val)) t ∧
      stored t.machine i.source.val = 0 ∧
      (∀ v : Fin i.n, i.dist [] v ≤ stored t.machine v.val ∧
        stored t.machine v.val ≤ ENNReal.ofReal (1+i.accuracy)*i.dist [] v ∧
        (stored t.machine v.val = ⊤ ↔ ¬Reachable i.graph (live []) i.source v)) := by
  let N := registerBound p.code
  let B := i.n+3*i.k+2
  let R := coefficient*i.size^3+1
  obtain ⟨f,hf⟩ := choose_initial_family p C a queryBound hpoly i hi hn2 heps
  have hmaintains : ∀ q : Fin (scaleCount i), Maintains p C a queryBound false (barrierInput i q.val) :=
    fun q => polynomial_maintains_barrier p C a queryBound hpoly i hi hn2 heps q.val
  obtain ⟨cs,u,hs,hcs,hg,hrep,h60,h80,h100,hfresh,hprefix,hutail⟩ := normalSetup_eval i hi p coefficient N (registerBound_ge p.code) s hraw hn hr htail
  obtain ⟨h96,h98,h102,h84,h88,h92,_⟩ := hrep
  have hucontrols : Controls B i.n (scaleCount i) R N u := ⟨h60,h80,h84,h88,h92,h96,h98,h100,h102⟩
  have hB : i.n+3*i.k ≤ B := by dsimp [B];omega
  obtain ⟨ca,v,ha,hvprefix,hca⟩ := initAll_eval i hi p C a queryBound heps B R hB f hf hmaintains u hg h84 h88 h80 h100 hfresh hprefix hutail
  have hvcontrols := hucontrols.transfer ha (controlFrame_scaleInitAll p).asPublic
  obtain ⟨w,hclear,hwdone⟩ := finalize_init i p B R f v hvprefix
  have hwcontrols := hvcontrols.transfer hclear controlFrame_clearLast.asPublic
  obtain ⟨cp,t,hpub,hcp,htg,htscales,htdirty,htsource,htnormal,htaccuracy,htoutput,htpointers,httail,_⟩ :=
    initializePublic_eval i hi p C a B R f hf w hwdone (by dsimp [B];omega) hwcontrols.pointerBases
  have htcontrols := hwcontrols.transfer hpub publicControlFrame_initializePublic
  have htstate : NormalMemory i p B R f (fun q v => stored (f q) v.val)
      (initialPointers i (fun q v => stored (f q) v.val)) t :=
    ⟨htg,htcontrols,htscales,htpointers,htdirty,htnormal,htoutput,httail⟩
  refine ⟨f,cs+(ca+(3+cp)),t,hf,Eval.seq hs (Eval.seq ha (Eval.seq hclear hpub)),?_,htstate,htsource,htaccuracy⟩
  dsimp only [N] at hcs
  omega
end DecrAlmostLinearSSSP.Decremental.Native
end s220
section s221
set_option autoImplicit false
open Filter
open scoped Topology
namespace DecrAlmostLinearSSSP.Decremental
lemma nat_rescale_tendsto (c : ℕ) (hc : 0 < c) : Tendsto (fun m : ℕ => c * m) atTop atTop := by
  apply tendsto_atTop.2
  intro N
  filter_upwards [eventually_ge_atTop N] with m hm
  exact hm.trans (Nat.le_mul_of_pos_left m hc)
lemma log_rescale_ratio (c : ℕ) (hc : 0 < c) :
    Tendsto (fun m : ℕ => Real.log (max 2 (c * m) : ℕ) / Real.log (max 2 m : ℕ)) atTop (nhds 1) := by
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hlim : Tendsto (fun m : ℕ => Real.log (c : ℝ) / Real.log (max 2 m : ℕ) + 1) atTop (nhds 1) := by
    simpa only [zero_add] using (log_size_tendsto.const_div_atTop (Real.log (c : ℝ))).add tendsto_const_nhds
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 2] with m hm
  have hcm : 2 ≤ c * m := hm.trans (Nat.le_mul_of_pos_left m hc)
  have hmR : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hm)
  have hlogm : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hm))
  simp only [max_eq_right hm, max_eq_right hcm, Nat.cast_mul,
    Real.log_mul hcR.ne' hmR.ne', add_div, div_self hlogm.ne']
lemma subpolynomial_rescale (a : ℕ → ℝ) (ha : Subpolynomial a) (c : ℕ) (hc : 0 < c) :
    Subpolynomial (fun m => a (c * m)) := by
  refine ⟨fun m => ha.1 _, ?_⟩
  have hfirst := ha.2.comp (nat_rescale_tendsto c hc)
  have hsecond := log_rescale_ratio c hc
  have hfun : (fun m : ℕ => Real.log (a (c * m)) / Real.log (max 2 m : ℕ)) =
      fun m => (Real.log (a (c * m)) / Real.log (max 2 (c * m) : ℕ)) *
        (Real.log (max 2 (c * m) : ℕ) / Real.log (max 2 m : ℕ)) := by
    funext m
    have h1 := log_size_positive (c * m)
    have h2 := log_size_positive m
    field_simp
  rw [hfun]
  simpa only [Function.comp_apply, zero_mul] using hfirst.mul hsecond
end DecrAlmostLinearSSSP.Decremental
end s221
section s222
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma normalWrapperOverhead_subpolynomial (a : ℕ → ℝ) (ha : Subpolynomial a) :
    Subpolynomial (normalWrapperOverhead a) := by
  have h1 := subpolynomial_add (fun _ => 1) (fun m => a (64*m))
    (subpolynomial_constant 1 (by norm_num)) (subpolynomial_rescale a ha 64 (by norm_num))
  have h2 := subpolynomial_add (fun _ => 256) (fun m => 32*logarithm2 (max 2 m : ℕ))
    (subpolynomial_constant 256 (by norm_num))
    (subpolynomial_mul (fun _ => 32) _ (subpolynomial_constant 32 (by norm_num)) subpolynomial_logarithm2_size)
  exact subpolynomial_mul _ _ (subpolynomial_mul _ _ h1 subpolynomial_scale_overhead) h2
lemma normal_wrapper_cost_bound (i : Input) (hi : i.Valid) (C D work : ℝ)
    (hC : 0 < C) (hD : 0 < D) (a : ℕ → ℝ) (ha : Subpolynomial a)
    (hwork : work ≤ D*((i.size : ℝ)+1024*C*i.size*a (64*i.size)/i.accuracy)*
      (16*(utilityDepth i.size : ℝ)+32)*(scaleCount i : ℝ)) :
    work ≤ (D*(1+1024*C))*i.size*normalWrapperOverhead a i.size/i.accuracy*
      max 1 (logarithm2 i.W) := by
  have he := hi.2.2.2.1
  have he1 := hi.2.2.2.2.1
  have hm : (0 : ℝ) < i.size := by exact_mod_cast (lt_of_lt_of_le (input_vertex_positive i) hi.1)
  have hlog := logarithm2_nonneg (show (1 : ℝ) ≤ (max 2 i.size : ℕ) by exact_mod_cast (show 1 ≤ max 2 i.size from by omega))
  have ha0 := ha.1 (64*i.size)
  have hs := scaleCount_saturated_bound i hi
  have hd := utilityDepth_bound i.size
  have hbase : (i.size : ℝ)+1024*C*i.size*a (64*i.size)/i.accuracy ≤
      (1+1024*C)*i.size*(1+a (64*i.size))/i.accuracy := by
    apply (le_div_iff₀ he).mpr
    have hid : ((i.size : ℝ)+1024*C*i.size*a (64*i.size)/i.accuracy)*i.accuracy =
        i.size*i.accuracy+1024*C*i.size*a (64*i.size) := by field_simp <;> ring
    rw [hid]
    have hh := mul_le_mul_of_nonneg_left he1 hm.le
    nlinarith only [hh,mul_nonneg hC.le hm.le,mul_nonneg hm.le ha0.le]
  have hdepth : 16*(utilityDepth i.size : ℝ)+32 ≤ 256+32*logarithm2 (max 2 i.size : ℕ) := by linarith
  have hmul1 := mul_le_mul_of_nonneg_left hbase hD.le
  have hmul2 := mul_le_mul hmul1 hdepth (by positivity : 0 ≤ 16*(utilityDepth i.size : ℝ)+32)
    (by positivity : 0 ≤ D*((1+1024*C)*i.size*(1+a (64*i.size))/i.accuracy))
  have hmul3 := mul_le_mul hmul2 hs (Nat.cast_nonneg _) (by positivity)
  apply hwork.trans
  apply hmul3.trans_eq
  unfold normalWrapperOverhead
  ring
end DecrAlmostLinearSSSP.Decremental
end s222
section s223
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Native
lemma initialization_cost_arithmetic (m n k S d M N dc dp coefficient : ℕ)
    (hm : 1 ≤ m) (hn : n ≤ m) (hk : k ≤ m) (hS : 1 ≤ S) :
    2*(dc+3)*(16*d+32)+2*(dc+4)*(16*S+32)+coefficient+(2*N+8)+38+
      ((dp+2)*M+(14*N+5*((dc+3)*(16*d+32))+
        k*(3*((dc+3)*(16*d+32))+30)+13*n+158)+7)*S+
      (13*S+48)*n+22 ≤
      (coefficient+16*N+14*dc+dp+500)*(m+M)*(16*d+32)*S := by
  let T := 16*d+32
  have hT : 32 ≤ T := by dsimp [T];omega
  have hTS : 1 ≤ T*S := by nlinarith
  have hmTS : m ≤ m*T*S := by nlinarith
  have hnTS : n ≤ m*T*S := hn.trans hmTS
  have hSbound : 16*S+32 ≤ 2*T*S := by nlinarith
  have hsetup : 2*(dc+3)*T+2*(dc+4)*(16*S+32)+coefficient+(2*N+8)+38 ≤
      (6*dc+coefficient+2*N+68)*m*T*S := by
    have h1 : 2*(dc+3)*T ≤ 2*(dc+3)*m*T*S := by
      calc
        _ ≤ 2*(dc+3)*m*T := by
          have hh := Nat.mul_le_mul_right T (Nat.mul_le_mul_left (2*(dc+3)) hm)
          simpa only [Nat.mul_one] using hh
        _ ≤ _ := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (2*(dc+3)*m*T) hS
    have h2 : 2*(dc+4)*(16*S+32) ≤ 4*(dc+4)*m*T*S := by
      calc
        _ ≤ 2*(dc+4)*(2*T*S) := Nat.mul_le_mul_left _ hSbound
        _ ≤ 4*(dc+4)*m*T*S := by
          calc
            _ ≤ 2*(dc+4)*(2*T*S)*m := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left _ hm
            _ = _ := by ring
    have h3 : coefficient+2*N+46 ≤ (coefficient+2*N+46)*m*T*S := by nlinarith
    nlinarith only [h1,h2,h3]
  have hover : (14*N+5*((dc+3)*T)+k*(3*((dc+3)*T)+30)+13*n+158+7)*S ≤
      (14*N+8*dc+232)*m*T*S := by
    have h1 : (14*N+165)*S ≤ (14*N+165)*m*T*S := by
      have hh : S ≤ m*T*S := by nlinarith
      simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (14*N+165) hh
    have h2 : 5*((dc+3)*T)*S ≤ 5*(dc+3)*m*T*S := by
      calc
        _ ≤ 5*((dc+3)*T)*S*m := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left _ hm
        _ = _ := by ring
    have h3 : k*(3*((dc+3)*T)+30)*S ≤ (3*dc+39)*m*T*S := by
      have hh : 3*((dc+3)*T)+30 ≤ (3*dc+39)*T := by nlinarith
      have hh' := Nat.mul_le_mul_right S (Nat.mul_le_mul hk hh)
      nlinarith only [hh']
    have h4 : 13*n*S ≤ 13*m*T*S := by nlinarith
    nlinarith only [h1,h2,h3,h4]
  have hpub : (13*S+48)*n+22 ≤ 83*m*T*S := by
    have h1 : 13*S*n ≤ 13*m*T*S := by nlinarith
    have h2 : 48*n+22 ≤ 70*m*T*S := by nlinarith
    nlinarith only [h1,h2]
  have hM : (dp+2)*M*S ≤ (dp+2)*M*T*S := by
    have hh : 1 ≤ T := by omega
    simpa only [Nat.mul_one] using Nat.mul_le_mul_right S (Nat.mul_le_mul_left ((dp+2)*M) hh)
  have htotal := Nat.add_le_add (Nat.add_le_add hsetup hover) (Nat.add_le_add hpub hM)
  have hmextra : (coefficient+16*N+14*dc+383)*m*T*S ≤
      (coefficient+16*N+14*dc+dp+500)*m*T*S := by
    exact Nat.mul_le_mul_right S (Nat.mul_le_mul_right T (Nat.mul_le_mul_right m (by omega)))
  have hMextra : (dp+2)*M*T*S ≤ (coefficient+16*N+14*dc+dp+500)*M*T*S := by
    exact Nat.mul_le_mul_right S (Nat.mul_le_mul_right T (Nat.mul_le_mul_right M (by omega)))
  dsimp only [T] at *
  nlinarith only [htotal,hmextra,hMextra]
lemma normalInitConstant_positive (p : Program) (coefficient : ℕ) : 0 < normalInitConstant p coefficient := by
  unfold normalInitConstant
  omega
lemma normal_initialization_uniform_cost {i : Input} (hi : i.Valid) {p : Program} {C : ℝ} (hC : 0 < C)
    {a : ℕ → ℝ} (ha : Subpolynomial a) (f : Fin (scaleCount i) → Machine)
    (hf : ∀ q, InitialFacts p C a i q.val (f q)) (coefficient cost : ℕ)
    (hcost : cost ≤ setupCost i coefficient (registerBound p.code)+
      ((dispatchCharge p.code+2)*maxInitialWork f+initOverhead i p+7)*scaleCount i+
      (13*scaleCount i+48)*i.n+22) :
    (cost : ℝ) ≤ ((normalInitConstant p coefficient : ℝ)*(1+1024*C))*i.size*
      normalWrapperOverhead a i.size/i.accuracy*max 1 (logarithm2 i.W) := by
  have hm : 1 ≤ i.size := (input_vertex_positive i).trans_le hi.1
  have hs : 1 ≤ scaleCount i := by unfold scaleCount;omega
  have hc := initialization_cost_arithmetic i.size i.n i.k (scaleCount i) (utilityDepth i.size)
    (maxInitialWork f) (registerBound p.code) (dispatchCharge ScaledCeiling.ceilingProgram.code)
    (dispatchCharge p.code) coefficient hm hi.1 hi.2.1 hs
  change cost ≤ _ at hcost
  have hnat : cost ≤ normalInitConstant p coefficient*(i.size+maxInitialWork f)*(16*utilityDepth i.size+32)*scaleCount i := by
    exact hcost.trans hc
  have he := hi.2.2.2.1
  have hboundNonneg : 0 ≤ C*(64*i.size)*a (64*i.size)/(i.accuracy/16) := by
    have ha0 := (ha.1 (64*i.size)).le
    positivity
  have hM := max_initial_work_bound f hf hboundNonneg
  have hMid : C*(64*i.size)*a (64*i.size)/(i.accuracy/16) =
      1024*C*i.size*a (64*i.size)/i.accuracy := by ring
  rw [hMid] at hM
  apply normal_wrapper_cost_bound i hi C (normalInitConstant p coefficient) cost hC
    (by exact_mod_cast normalInitConstant_positive p coefficient) a ha
  have hh : (cost : ℝ) ≤ (normalInitConstant p coefficient : ℝ)*
      ((i.size : ℝ)+(maxInitialWork f : ℝ))*(16*(utilityDepth i.size : ℝ)+32)*(scaleCount i : ℝ) := by
    exact_mod_cast hnat
  apply hh.trans
  gcongr
end DecrAlmostLinearSSSP.Decremental.Native
end s223
section s224
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
namespace CacheRefresh
lemma prepare_eval (s : Data) : Eval prepare s 4 (prepared s) := eval_sequence_atoms atoms s
lemma prepare_fields (s : Data) (hz : s.natReg 56 = 0) :
    (prepared s).natReg 128 = s.natReg 198 ∧ (prepared s).natReg 132 = s.natReg 112 ∧
    (prepared s).natReg 20 = s.natReg 108+2*s.natReg 94 := by
  simp [prepared,atoms,Atom.effect,instructionEffect,data,Data.machine,hz,two_mul]
lemma eval_code (i : Input) (hi : i.Valid) (B j cache : ℕ) (g : Machine)
    (b : Fin i.n → ℝ≥0∞) (v : Fin i.n) (s : Data)
    (hsource : SourceMemory.Image B j s g.natMem g.realMem) (hcache : CacheImage i j cache b s)
    (hnormal : ∀ u : Fin i.n, g.natMem u.val ≤ 1 ∧ (g.natMem u.val = 0 → 0 ≤ g.realMem u.val))
    (hz : s.natReg 56 = 0) (h1 : s.natReg 26 = 1) (hv : s.natReg 94 = v.val)
    (haddress : s.natReg 198 = bankAddress B j v.val) (hF : s.natReg 112 = bankFactor j)
    (hc : s.natReg 108 = cache) (hd : s.realReg 70 = delta i j) :
    ∃ cost t, Eval code s cost t ∧ cost ≤ 16 ∧
      CacheImage i j cache (Function.update b v (max (b v) (stored g v.val))) t ∧
      (∀ address, address ≠ cache+2*v.val →
        t.natMem address = s.natMem address ∧ t.realMem address = s.realMem address) := by
  let u := prepared s
  have hu := prepare_eval s
  obtain ⟨hu128,hu132,hu20⟩ := prepare_fields s hz
  have haddr : u.natReg 128 = bankAddress B j v.val := hu128.trans haddress
  have hfactor : u.natReg 132 = bankFactor j := hu132.trans hF
  have hcell : u.natReg 20 = cache+2*v.val := by simpa only [hc,hv] using hu20
  have hun : u.natMem = s.natMem := rfl
  have hur : u.realMem = s.realMem := rfl
  have hud : u.realReg 70 = delta i j := hd
  have hvn : u.natMem (u.natReg 128) = bankFactor j*g.natMem v.val := by
    rw [haddr,hun];exact hsource.natMem v.val
  have hvr : u.realMem (u.natReg 128) = g.realMem v.val := by
    rw [haddr,hur];exact hsource.realMem v.val
  obtain ⟨cr,w,hw,hcr,hw22,hw20,hwfinite,hwincoming,hwr,hwn⟩ :=
    ScaledReadout.eval_code u (bankFactor j) (g.natMem v.val) (delta i j) (g.realMem v.val)
      (bankFactor_positive j) (delta_positive i hi j) hfactor hud (hnormal v).1 hvn hvr (hnormal v).2
  have hwcell : w.natReg 20 = cache+2*v.val := by
    have hh : NatFrame ScaledReadout.code 20 := by
      norm_num [ScaledReadout.code,Structured.sequence,NatFrame,loadN,load,mul,natural,writesNat]
    exact (hw.nat_frame hh).trans hcell
  have hw1 : w.natReg 26 = 1 := by
    have hh : NatFrame ScaledReadout.code 26 := by
      norm_num [ScaledReadout.code,Structured.sequence,NatFrame,loadN,load,mul,natural,writesNat]
    exact (hw.nat_frame hh).trans h1
  have hwnormal : w.natReg 22 ≤ 1 := hw22 ▸ (hnormal v).1
  have hwold : w.natMem (w.natReg 20) ≤ 1 := by rw [hwcell,hwn,hun];exact hcache.flags v
  have hwoldfinite : w.natMem (w.natReg 20) = 0 → 0 ≤ w.realMem (w.natReg 20) := by
    rw [hwcell,hwn,hwr,hun,hur];exact hcache.finite v
  obtain ⟨cm,t,ht,hcm,htflag,htfinite,htvalue,htframe⟩ :=
    ExtendedMax.eval_code w hw1 hwnormal hwold hwfinite hwoldfinite
  have htcache : CacheImage i j cache (Function.update b v (max (b v) (stored g v.val))) t := by
    constructor
    · intro z
      by_cases hzv : z = v
      · subst z;simpa only [hwcell] using htflag
      · have hne : cache+2*z.val ≠ w.natReg 20 := by rw [hwcell];intro hh;apply hzv;apply Fin.ext;omega
        rw [(htframe _ hne).2,hwn,hun];exact hcache.flags z
    · intro z hz
      by_cases hzv : z = v
      · subst z;simpa only [hwcell] using htfinite (by simpa only [hwcell] using hz)
      · have hne : cache+2*z.val ≠ w.natReg 20 := by rw [hwcell];intro hh;apply hzv;apply Fin.ext;omega
        rw [(htframe _ hne).1,hwr,hur]
        exact hcache.finite z (by simpa only [(htframe _ hne).2,hwn,hun] using hz)
    · intro z
      by_cases hzv : z = v
      · subst z
        rw [Function.update_self,← hwcell,htvalue]
        have hwvalue : ExtendedMax.cell w (w.natReg 20) = ENNReal.ofReal (delta i j)*b v := by
          simpa only [ExtendedMax.cell,hwcell,hwn,hwr,hun,hur] using hcache.value v
        have hwnew : ExtendedMax.incoming w = ENNReal.ofReal (delta i j)*stored g v.val := hwincoming
        rw [hwvalue,hwnew,mul_max]
      · rw [Function.update_of_ne hzv]
        have hne : cache+2*z.val ≠ w.natReg 20 := by rw [hwcell];intro hh;apply hzv;apply Fin.ext;omega
        simpa only [ExtendedMax.cell,(htframe _ hne).1,(htframe _ hne).2,hwn,hwr,hun,hur] using hcache.value z
  refine ⟨4+(cr+cm),t,Eval.seq hu (Eval.seq hw ht),by omega,htcache,?_⟩
  intro address hne
  have hh := htframe address (by rwa [hwcell])
  exact ⟨hh.2.trans (congrFun hwn address),hh.1.trans (congrFun hwr address)⟩
end CacheRefresh
end DecrAlmostLinearSSSP.Decremental.Native
end s224
section s225
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
lemma ScanTable.refresh {i : Input} {B reserve N : ℕ} {s t : Data}
    {b : Fin (scaleCount i) → Fin i.n → ℝ≥0∞}
    (ht : ScanTable i (scaleLayout B i.n (scaleCount i) reserve N).records
      (scaleLayout B i.n (scaleCount i) reserve N).caches (2*N+8) b s)
    (j : Fin (scaleCount i)) (v : Fin i.n) (bnew : Fin i.n → ℝ≥0∞)
    (hnew : CacheImage i j.val (cacheAt (scaleLayout B i.n (scaleCount i) reserve N).caches i.n j.val) bnew t)
    (hframe : ∀ address, address ≠ cacheAt (scaleLayout B i.n (scaleCount i) reserve N).caches i.n j.val+2*v.val →
      t.natMem address = s.natMem address ∧ t.realMem address = s.realMem address) :
    ScanTable i (scaleLayout B i.n (scaleCount i) reserve N).records
      (scaleLayout B i.n (scaleCount i) reserve N).caches (2*N+8) (Function.update b j bnew) t := by
  classical
  constructor
  · exact ht.positive
  · intro q
    apply (ht.metadata q).frame
    intro offset hoff
    have ho : offset = 0 ∨ offset = 2 ∨ offset = 4 := by simpa using hoff
    have hbefore : recordAt (scaleLayout B i.n (scaleCount i) reserve N).records (2*N+8) q.val+offset <
        (scaleLayout B i.n (scaleCount i) reserve N).caches := by
      rcases ho with rfl | rfl | rfl
      · simpa using record_cell_before_caches B i.n (scaleCount i) reserve N q.val 0 q.isLt (by omega)
      · exact record_cell_before_caches B i.n (scaleCount i) reserve N q.val 1 q.isLt (by omega)
      · exact record_cell_before_caches B i.n (scaleCount i) reserve N q.val 2 q.isLt (by omega)
    apply hframe
    dsimp [cacheAt]
    omega
  · intro q
    by_cases hq : q = j
    · subst q;simpa only [Function.update_self] using hnew
    · rw [Function.update_of_ne hq]
      apply (ht.cache q).frame
      intro z
      apply hframe
      intro heq
      have hh := cache_cells_injective (B := B) (S := scaleCount i) (reserve := reserve) (N := N) z.isLt v.isLt heq
      exact hq (Fin.ext hh)
end DecrAlmostLinearSSSP.Decremental.Native
end s225
section s226
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
lemma scanRows_head_from (i : Input) (recordBase cacheBase stride : ℕ) (s : Data) (v : Fin i.n)
    (start : ℕ) (hstart : start ≤ scaleCount i) :
    LinkedScan.headAddress (LinkedScan.rowsFrom (scanRow i recordBase cacheBase stride s v)
      (scaleCount i-start) start) = scanRecord i recordBase stride start := by
  by_cases hlt : start < scaleCount i
  · have hpos : 0 < scaleCount i-start := by omega
    obtain ⟨r,hr⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
    rw [hr]
    simp only [LinkedScan.rowsFrom,LinkedScan.headAddress,scanRow_address]
  · have heq : start = scaleCount i := by omega
    simp [heq,LinkedScan.rowsFrom,LinkedScan.headAddress,scanRecord]
lemma advance_scan (i : Input) (recordBase cacheBase stride : ℕ) (s : Data)
    (b : Fin (scaleCount i) → Fin i.n → ℝ≥0∞) (ht : ScanTable i recordBase cacheBase stride b s)
    (v : Fin i.n) (start : ℕ) (hstart : start ≤ scaleCount i)
    (hp : s.natReg 30 = scanRecord i recordBase stride start) (hv : s.natReg 38 = 2*v.val)
    (hz : s.natReg 34 = 0) (h1 : s.natReg 36 = 1) :
    ∃ cost t, Eval LinkedScan.code s cost t ∧
      cost ≤ 13*(DecrAlmostLinearSSSP.Decremental.advance i b v (scaleCount i-start) start-start)+16 ∧
      t.natReg 30 = scanRecord i recordBase stride
        (DecrAlmostLinearSSSP.Decremental.advance i b v (scaleCount i-start) start) ∧
      t.realMem = s.realMem ∧ t.natMem = s.natMem := by
  let rows := LinkedScan.rowsFrom (scanRow i recordBase cacheBase stride s v) (scaleCount i-start) start
  have hr : LinkedScan.RowsView s (2*v.val) rows :=
    scanRows_view i recordBase cacheBase stride s b ht v _ start (by omega)
  have hh : s.natReg 30 = LinkedScan.headAddress rows := by
    rw [scanRows_head_from i recordBase cacheBase stride s v start hstart];exact hp
  obtain ⟨cost,t,he,hcost,htp,_,hmr,hmn⟩ := LinkedScan.eval_code rows s (2*v.val) hh hv hz h1 hr
  have htravel := LinkedScan.rowsFrom_travel i b v (scanRow i recordBase cacheBase stride s v)
    (scanRow_eligible i recordBase cacheBase stride s b ht v) (scaleCount i-start) start
  have hselected := LinkedScan.rowsFrom_selected i b v (scanRow i recordBase cacheBase stride s v)
    (scanRecord i recordBase stride) (scanRow_eligible i recordBase cacheBase stride s b ht v)
    (scanRow_address i recordBase cacheBase stride s v) (scaleCount i-start) start
    (by rw [Nat.add_sub_of_le hstart];simp [scanRecord])
  exact ⟨cost,t,he,by simpa only [rows,htravel] using hcost,htp.trans hselected,hmr,hmn⟩
end DecrAlmostLinearSSSP.Decremental.Native
end s226
section s227
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
namespace PointerRefresh
lemma prepare_eval (s : Data) : Eval prepare s 3 (prepared s) := eval_sequence_atoms atoms s
lemma prepare_fields (s : Data) :
    (prepared s).natReg 38 = 2*s.natReg 94 ∧ (prepared s).natReg 196 = s.natReg 96+2*s.natReg 94 ∧
    (prepared s).natReg 30 = s.natMem (s.natReg 96+2*s.natReg 94) := by
  simp [prepared,atoms,Atom.effect,instructionEffect,data,Data.machine,two_mul]
lemma prepare_nat_frame (k : ℕ) (h38 : k ≠ 38) (h196 : k ≠ 196) (h30 : k ≠ 30) : NatFrame prepare k := by
  simp [prepare,atoms,Structured.sequence,NatFrame,writesNat,Ne.symm h38,Ne.symm h196,Ne.symm h30]
lemma eval_code (i : Input) (recordBase cacheBase stride pointerBase : ℕ)
    (b : Fin (scaleCount i) → Fin i.n → ℝ≥0∞) (v : Fin i.n) (start : ℕ) (s : Data)
    (ht : ScanTable i recordBase cacheBase stride b s) (hRC : recordBase ≤ cacheBase)
    (hstart : start ≤ scaleCount i) (hptr : s.natMem (pointerBase+2*v.val) = scanRecord i recordBase stride start)
    (hv : s.natReg 94 = v.val) (hbase : s.natReg 96 = pointerBase)
    (hz : s.natReg 34 = 0) (h1 : s.natReg 36 = 1) :
    ∃ cost t, Eval code s cost t ∧
      cost ≤ 13*(DecrAlmostLinearSSSP.Decremental.advance i b v (scaleCount i-start) start-start)+20 ∧
      t.natMem = Function.update s.natMem (pointerBase+2*v.val)
        (scanRecord i recordBase stride (DecrAlmostLinearSSSP.Decremental.advance i b v (scaleCount i-start) start)) ∧
      t.realMem = s.realMem := by
  let u := prepared s
  have hu := prepare_eval s
  obtain ⟨hu38,hu196,hu30⟩ := prepare_fields s
  have hu38' : u.natReg 38 = 2*v.val := by simpa only [hv] using hu38
  have hu196' : u.natReg 196 = pointerBase+2*v.val := by simpa only [hv,hbase] using hu196
  have hu30' : u.natReg 30 = scanRecord i recordBase stride start := by
    have hh : u.natReg 30 = s.natMem (pointerBase+2*v.val) := by simpa only [hv,hbase] using hu30
    exact hh.trans hptr
  have hut : ScanTable i recordBase cacheBase stride b u := ht.frame_above hRC (fun _ _ => ⟨rfl,rfl⟩)
  have huz : u.natReg 34 = 0 := (hu.nat_frame (prepare_nat_frame 34 (by omega) (by omega) (by omega))).trans hz
  have hu1 : u.natReg 36 = 1 := (hu.nat_frame (prepare_nat_frame 36 (by omega) (by omega) (by omega))).trans h1
  obtain ⟨c,w,hw,hcost,hw30,hwr,hwn⟩ := advance_scan i recordBase cacheBase stride u b hut v start hstart hu30' hu38' huz hu1
  have hw196 : w.natReg 196 = pointerBase+2*v.val := (hw.nat_frame
    (LinkedScan.code_nat_frame 196 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))).trans hu196'
  let t : Data := {w with natMem := Function.update w.natMem (w.natReg 196) (w.natReg 30)}
  refine ⟨3+(c+1),t,Eval.seq hu (Eval.seq hw (eval_storeN w 196 30)),by omega,?_,?_⟩
  · change Function.update w.natMem (w.natReg 196) (w.natReg 30) = _
    rw [hw196,hw30,hwn];rfl
  · exact hwr
lemma nat_frame (k : ℕ) (h38 : k ≠ 38) (h196 : k ≠ 196) (h30 : k ≠ 30) (h32 : k ≠ 32)
    (h40 : k ≠ 40) (h42 : k ≠ 42) (h44 : k ≠ 44) (h46 : k ≠ 46) : NatFrame code k :=
  ⟨prepare_nat_frame k h38 h196 h30,LinkedScan.code_nat_frame k h30 h32 h40 h42 h44 h46,not_false⟩
lemma real_frame (k : ℕ) (h30 : k ≠ 30) (h32 : k ≠ 32) : RealFrame code k := by
  refine ⟨?_,LinkedScan.code_real_frame k h30 h32,not_false⟩
  simp [prepare,atoms,Structured.sequence,RealFrame,writesReal]
end PointerRefresh
end DecrAlmostLinearSSSP.Decremental.Native
end s227
section s228
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
open Structured
lemma DirtyMark.View.frame {n flags list : ℕ} {xs : List (Fin n)} {s t : Data}
    (h : DirtyMark.View flags list xs s)
    (hf : ∀ v : Fin n, t.natMem (flags+2*v.val) = s.natMem (flags+2*v.val))
    (hl : ∀ j < xs.length, t.natMem (list+2*j) = s.natMem (list+2*j))
    (hc : t.natReg 182 = s.natReg 182) (hp : t.natReg 180 = s.natReg 180) :
    DirtyMark.View flags list xs t := by
  exact ⟨h.nodup,fun v => (hf v).trans (h.flags v),fun j hj => (hl j hj).trans (h.entries j hj),
    hc.trans h.count,hp.trans h.pointer⟩
namespace Native
lemma AdapterMemory.frame {i : Input} {B reserve N : ℕ} {a : AdapterState i} {xs : List (Fin i.n)} {s t : Data}
    (h : AdapterMemory i B reserve N a xs s) (hn : t.natMem = s.natMem) (hr : t.realMem = s.realMem)
    (hc : t.natReg 182 = s.natReg 182) (hp : t.natReg 180 = s.natReg 180) :
    AdapterMemory i B reserve N a xs t := by
  constructor
  · exact h.table.frame_above (pointerLayout_order B i.n (scaleCount i) reserve N).1
      (fun _ _ => ⟨congrFun hn _,congrFun hr _⟩)
  · simpa only [hn] using h.pointers
  · exact h.pending.frame (fun _ => congrFun hn _) (fun _ _ => congrFun hn _) hc hp
  · exact h.covered
  · intro v
    change (if t.natMem v.val = 1 then ⊤ else ENNReal.ofReal (t.realMem v.val)) = a.output v
    rw [hn,hr]
    exact h.output v
end Native
end DecrAlmostLinearSSSP.Decremental
end s228
section s229
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
lemma CacheRefresh.nat_frame (k : ℕ) (h128 : k ≠ 128) (h132 : k ≠ 132) (h38 : k ≠ 38) (h20 : k ≠ 20)
    (h130 : k ≠ 130) (h22 : k ≠ 22) (h24 : k ≠ 24) : NatFrame CacheRefresh.code k := by
  simp [CacheRefresh.code,CacheRefresh.prepare,CacheRefresh.atoms,ScaledReadout.code,ExtendedMax.code,
    Structured.sequence,NatFrame,nadd,loadN,load,mul,natural,store,storeN,writesNat,
    Ne.symm h128,Ne.symm h132,Ne.symm h38,Ne.symm h20,Ne.symm h130,Ne.symm h22,Ne.symm h24]
lemma CacheRefresh.real_frame (k : ℕ) (h20 : k ≠ 20) (h22 : k ≠ 22) : RealFrame CacheRefresh.code k := by
  simp [CacheRefresh.code,CacheRefresh.prepare,CacheRefresh.atoms,ScaledReadout.code,ExtendedMax.code,
    Structured.sequence,RealFrame,nadd,loadN,load,mul,natural,store,storeN,writesReal,Ne.symm h20,Ne.symm h22]
lemma DirtyMark.nat_frame (k : ℕ) (h186 : k ≠ 186) (h184 : k ≠ 184) (h188 : k ≠ 188)
    (h180 : k ≠ 180) (h182 : k ≠ 182) : NatFrame DirtyMark.code k := by
  simp [DirtyMark.code,DirtyMark.prefixCode,DirtyMark.prefixAtoms,DirtyMark.insertCode,
    Structured.sequence,NatFrame,nadd,loadN,storeN,writesNat,Ne.symm h186,Ne.symm h184,Ne.symm h188,Ne.symm h180,Ne.symm h182]
lemma DirtyMark.real_frame (k : ℕ) : RealFrame DirtyMark.code k := by
  simp [DirtyMark.code,DirtyMark.prefixCode,DirtyMark.prefixAtoms,DirtyMark.insertCode,
    Structured.sequence,RealFrame,nadd,loadN,storeN,writesReal]
lemma globalFrame_cacheRefresh : GlobalFrame CacheRefresh.code := by
  constructor
  · intro k hk
    simp only [globalNat,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals apply CacheRefresh.nat_frame <;> omega
  · intro k hk
    simp only [globalReal,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl <;> apply CacheRefresh.real_frame <;> omega
lemma globalFrame_pointerRefresh : GlobalFrame PointerRefresh.code := by
  constructor
  · intro k hk
    simp only [globalNat,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals apply PointerRefresh.nat_frame <;> omega
  · intro k hk
    simp only [globalReal,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl <;> apply PointerRefresh.real_frame <;> omega
lemma globalFrame_dirtyMark : GlobalFrame DirtyMark.code := by
  constructor
  · intro k hk
    simp only [globalNat,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals apply DirtyMark.nat_frame <;> omega
  · intro k hk;exact DirtyMark.real_frame k
end DecrAlmostLinearSSSP.Decremental.Native
end s229
section s230
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
lemma adapter_cache_step (i : Input) (hi : i.Valid) (p : Program) (B reserve N : ℕ) (hB : i.n ≤ B)
    (a : AdapterState i) (xs : List (Fin i.n)) (s : Data) (h : AdapterMemory i B reserve N a xs s)
    (j : Fin (scaleCount i)) (v : Fin i.n) (g : Machine)
    (hsource : SourceMemory.Image B j.val s g.natMem g.realMem)
    (hnormal : ∀ z : Fin i.n, g.natMem z.val ≤ 1 ∧ (g.natMem z.val = 0 → 0 ≤ g.realMem z.val))
    (hz : s.natReg 56 = 0) (h1 : s.natReg 26 = 1) (hv : s.natReg 94 = v.val)
    (haddress : s.natReg 198 = bankAddress B j.val v.val) (hF : s.natReg 112 = bankFactor j.val)
    (hc : s.natReg 108 = cacheAt (pointerLayout B i.n (scaleCount i) reserve N).cache i.n j.val)
    (hd : s.realReg 70 = delta i j.val) :
    ∃ cost t, Eval CacheRefresh.code s cost t ∧ cost ≤ 16 ∧
      AdapterMemory i B reserve N (cacheUpdated i a j v (stored g v.val)) xs t ∧
      (∀ address, address ≠ cacheAt (pointerLayout B i.n (scaleCount i) reserve N).cache i.n j.val+2*v.val →
        t.natMem address = s.natMem address ∧ t.realMem address = s.realMem address) := by
  let l := pointerLayout B i.n (scaleCount i) reserve N
  let cache := cacheAt l.cache i.n j.val
  obtain ⟨cost,t,he,hcost,hnew,hframe⟩ := CacheRefresh.eval_code i hi B j.val cache g (a.maxima j) v s
    hsource (h.table.cache j) hnormal hz h1 hv haddress hF hc hd
  have hnewTable := h.table.refresh (reserve := reserve) j v _ hnew hframe
  have hbefore : ∀ address, address < l.record →
      t.natMem address = s.natMem address ∧ t.realMem address = s.realMem address := by
    intro address ha
    apply hframe
    have hRC := (pointerLayout_order B i.n (scaleCount i) reserve N).1
    dsimp [cache,cacheAt,l] at *
    omega
  have harray : ∀ address, PointerArrayCell l i.n address →
      t.natMem address = s.natMem address ∧ t.realMem address = s.realMem address :=
    fun address ha => hbefore address (pointerArray_before_record ha)
  have hlen : xs.length ≤ i.n := by simpa only [Fintype.card_fin] using h.pending.nodup.length_le_card
  have htmem : AdapterMemory i B reserve N (cacheUpdated i a j v (stored g v.val)) xs t := by
    constructor
    · exact hnewTable
    · intro z
      exact (harray _ ⟨z.val,z.isLt,Or.inl rfl⟩).1.trans (h.pointers z)
    · apply h.pending.frame
      · intro z;exact (harray _ ⟨z.val,z.isLt,Or.inr (Or.inl rfl)⟩).1
      · intro r hr;exact (harray _ ⟨r,by omega,Or.inr (Or.inr rfl)⟩).1
      · exact he.nat_frame (CacheRefresh.nat_frame 182 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
      · exact he.nat_frame (CacheRefresh.nat_frame 180 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
    · exact h.covered
    · intro z
      have hm := hbefore z.val (by dsimp [l,pointerLayout,scaleLayout,Layout.addresses];omega)
      change (if t.natMem z.val = 1 then ⊤ else ENNReal.ofReal (t.realMem z.val)) = a.output z
      rw [hm.1,hm.2]
      exact h.output z
  exact ⟨cost,t,he,hcost,htmem,hframe⟩
end DecrAlmostLinearSSSP.Decremental.Native
end s230
section s231
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
lemma adapter_pointer_step (i : Input) (B reserve N : ℕ) (hB : i.n ≤ B)
    (a : AdapterState i) (xs : List (Fin i.n)) (s : Data) (h : AdapterMemory i B reserve N a xs s)
    (v : Fin i.n) (hp : a.pointer v ≤ scaleCount i)
    (hv : s.natReg 94 = v.val) (hbase : s.natReg 96 = (pointerLayout B i.n (scaleCount i) reserve N).pointer)
    (hz : s.natReg 34 = 0) (h1 : s.natReg 36 = 1) :
    ∃ cost t, Eval PointerRefresh.code s cost t ∧
      cost ≤ 13*((pointerUpdated i a v).pointer v-a.pointer v)+20 ∧
      AdapterMemory i B reserve N (pointerUpdated i a v) xs t ∧
      t.natMem = Function.update s.natMem ((pointerLayout B i.n (scaleCount i) reserve N).pointer+2*v.val)
        (scanRecord i (pointerLayout B i.n (scaleCount i) reserve N).record (2*N+8) ((pointerUpdated i a v).pointer v)) ∧
      t.realMem = s.realMem := by
  classical
  let l := pointerLayout B i.n (scaleCount i) reserve N
  have horder := pointerLayout_order B i.n (scaleCount i) reserve N
  obtain ⟨cost,t,he,hcost,hn,hr⟩ := PointerRefresh.eval_code i l.record l.cache (2*N+8) l.pointer a.maxima v (a.pointer v) s
    h.table horder.1 hp (h.pointers v) hv hbase hz h1
  have hnewptr : (pointerUpdated i a v).pointer v =
      DecrAlmostLinearSSSP.Decremental.advance i a.maxima v (scaleCount i-a.pointer v) (a.pointer v) := by
    simp only [pointerUpdated,Function.update_self]
  have hcellBefore : l.pointer+2*v.val < l.record := pointerArray_before_record ⟨v.val,v.isLt,Or.inl rfl⟩
  have hframe (address : ℕ) (hne : address ≠ l.pointer+2*v.val) : t.natMem address = s.natMem address := by
    rw [hn,Function.update_of_ne hne]
  have hlen : xs.length ≤ i.n := by simpa only [Fintype.card_fin] using h.pending.nodup.length_le_card
  have htmem : AdapterMemory i B reserve N (pointerUpdated i a v) xs t := by
    constructor
    · apply h.table.frame_above horder.1
      intro address ha
      exact ⟨hframe address (by dsimp only [l] at hcellBefore ⊢;omega),congrFun hr _⟩
    · intro z
      by_cases hzv : z = v
      · subst z;rw [hn,Function.update_self,hnewptr]
      · rw [hframe _ (by dsimp only [l];intro hh;apply hzv;apply Fin.ext;omega),h.pointers z]
        simp only [pointerUpdated,Function.update_of_ne hzv]
    · apply h.pending.frame
      · intro z
        have hh := horder.2.1 v.val v.isLt
        exact hframe _ (by dsimp [l] at *;omega)
      · intro r hr'
        have hh := horder.2.1 v.val v.isLt
        exact hframe _ (by dsimp [l,pointerLayout,scaleLayout,Layout.addresses] at *;omega)
      · exact he.nat_frame (PointerRefresh.nat_frame 182 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
      · exact he.nat_frame (PointerRefresh.nat_frame 180 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
    · exact h.covered
    · intro z
      have hm : t.natMem z.val = s.natMem z.val := hframe z.val (by dsimp [l,pointerLayout,scaleLayout,Layout.addresses];omega)
      change (if t.natMem z.val = 1 then ⊤ else ENNReal.ofReal (t.realMem z.val)) = a.output z
      rw [hm,hr];exact h.output z
  exact ⟨cost,t,he,by simpa only [hnewptr] using hcost,htmem,by simpa only [hnewptr] using hn,hr⟩
end DecrAlmostLinearSSSP.Decremental.Native
end s231
section s232
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
lemma DirtyMark.existing_eval {n flags list : ℕ} (xs : List (Fin n)) (s : Data) (v : Fin n)
    (h : DirtyMark.View flags list xs s) (hv : s.natReg 94 = v.val) (hf : s.natReg 98 = flags)
    (h1 : s.natReg 26 = 1) (hmem : v ∈ xs) : Eval DirtyMark.code s 5 (DirtyMark.prefixData s) := by
  have hfields := DirtyMark.prefix_fields s
  have hval : (DirtyMark.prefixData s).natReg 188 = 1 := by
    rw [hfields.2.1,hf,hv,h.flags v]
    simp only [if_pos hmem]
  have hu1 : (DirtyMark.prefixData s).natReg 26 = 1 :=
    (hfields.2.2 26 (by omega) (by omega) (by omega)).trans h1
  have ht : ¬(Test.natLess 188 26).holds (DirtyMark.prefixData s) := by simp [Test.holds,hval,hu1]
  exact Eval.seq (DirtyMark.prefix_eval s) (Eval.branchNo ht (Eval.skip _))
end DecrAlmostLinearSSSP.Decremental
end s232
section s233
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
lemma adapter_mark_step (i : Input) (B reserve N : ℕ) (hB : i.n ≤ B)
    (a : AdapterState i) (xs : List (Fin i.n)) (s : Data) (h : AdapterMemory i B reserve N a xs s)
    (v : Fin i.n) (hv : s.natReg 94 = v.val)
    (hf : s.natReg 98 = (pointerLayout B i.n (scaleCount i) reserve N).flags)
    (h1 : s.natReg 26 = 1) (h2 : s.natReg 14 = 2) :
    ∃ cost t ys, Eval DirtyMark.code s cost t ∧ cost ≤ 8 ∧
      ys = (if v ∈ xs then xs else xs++[v]) ∧
      AdapterMemory i B reserve N {a with dirty := insert v a.dirty} ys t ∧
      (∀ address, ¬PointerArrayCell (pointerLayout B i.n (scaleCount i) reserve N) i.n address →
        t.natMem address = s.natMem address ∧ t.realMem address = s.realMem address) := by
  classical
  let l := pointerLayout B i.n (scaleCount i) reserve N
  have horder := pointerLayout_order B i.n (scaleCount i) reserve N
  obtain ⟨cost,t,ys,he,hcost,hys,hview,hlen,hr,hframe⟩ := DirtyMark.eval_code l.flags l.list xs s v
    h.pending hf hv h1 h2 (fun z => horder.2.2.1 z.val z.isLt)
  have hmem (address : ℕ) (hnot : ¬PointerArrayCell l i.n address) :
      t.natMem address = s.natMem address ∧ t.realMem address = s.realMem address := by
    refine ⟨?_,congrFun hr _⟩
    by_cases hvxs : v ∈ xs
    · obtain ⟨_,rfl⟩ := he.deterministic (DirtyMark.existing_eval xs s v h.pending hv hf h1 hvxs)
      rfl
    · have hxlen : xs.length < i.n := by
        have hlen' : (xs++[v]).length ≤ i.n := by simpa only [hys,if_neg hvxs] using hlen
        simp only [List.length_append,List.length_singleton] at hlen'
        omega
      apply hframe
      · intro hh;exact hnot ⟨v.val,v.isLt,Or.inr (Or.inl hh)⟩
      · intro hh;exact hnot ⟨xs.length,hxlen,Or.inr (Or.inr hh)⟩
  have hbefore (address : ℕ) (ha : l.record ≤ address) :
      t.natMem address = s.natMem address ∧ t.realMem address = s.realMem address := by
    apply hmem
    intro hh;have hb := pointerArray_before_record hh;dsimp only [l] at ha;omega
  have htmem : AdapterMemory i B reserve N {a with dirty := insert v a.dirty} ys t := by
    constructor
    · exact h.table.frame_above horder.1 hbefore
    · intro z
      have hn : t.natMem (l.pointer+2*z.val) = s.natMem (l.pointer+2*z.val) := by
        by_cases hvxs : v ∈ xs
        · obtain ⟨_,rfl⟩ := he.deterministic (DirtyMark.existing_eval xs s v h.pending hv hf h1 hvxs);rfl
        · have hpf := horder.2.1 z.val z.isLt
          have hfl : l.flags ≤ l.list := by dsimp [l,pointerLayout,scaleLayout,Layout.addresses];omega
          exact hframe _ (by dsimp only [l] at *;omega) (by dsimp only [l] at *;omega)
      exact hn.trans (h.pointers z)
    · exact hview
    · intro z hz
      simp only [Finset.mem_insert] at hz
      have hxs : xs.toFinset ⊆ ys.toFinset := by
        intro z hz
        rw [hys]
        split_ifs
        · exact hz
        · exact List.mem_toFinset.mpr (List.mem_append_left _ (List.mem_toFinset.mp hz))
      rcases hz with rfl | hz
      · rw [hys];split_ifs <;> simp_all
      · exact hxs (h.covered hz)
    · intro z
      have hm := hmem z.val (by intro hh;have hb := pointerArray_above_base hh;omega)
      change (if t.natMem z.val = 1 then ⊤ else ENNReal.ofReal (t.realMem z.val)) = a.output z
      rw [hm.1,hm.2];exact h.output z
  exact ⟨cost,t,ys,he,hcost,hys,htmem,hmem⟩
end DecrAlmostLinearSSSP.Decremental.Native
end s233
section s234
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
lemma AdapterMemory.state_transport {i : Input} {B reserve N : ℕ} {a b : AdapterState i}
    {xs : List (Fin i.n)} {s : Data} (h : AdapterMemory i B reserve N a xs s)
    (hm : b.maxima = a.maxima) (hp : b.pointer = a.pointer) (ho : b.output = a.output)
    (hd : b.dirty ⊆ a.dirty) : AdapterMemory i B reserve N b xs s := by
  constructor
  · rw [hm];exact h.table
  · rw [hp];exact h.pointers
  · exact h.pending
  · exact hd.trans h.covered
  · rw [ho];exact h.output
end DecrAlmostLinearSSSP.Decremental.Native
end s234
section s235
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
lemma reportEvent_eval (i : Input) (hi : i.Valid) (p : Program) (B reserve N utility : ℕ) (hB : i.n ≤ B)
    (a : AdapterState i) (xs : List (Fin i.n)) (s : Data) (h : AdapterMemory i B reserve N a xs s)
    (hg : Globals i B utility s) (hp : ∀ z, PointerValid i a.maxima z (a.pointer z))
    (j : Fin (scaleCount i)) (v : Fin i.n) (g : Machine)
    (hsource : SourceMemory.Image B j.val s g.natMem g.realMem)
    (hnormal : ∀ z : Fin i.n, g.natMem z.val ≤ 1 ∧ (g.natMem z.val = 0 → 0 ≤ g.realMem z.val))
    (hv : s.natReg 94 = v.val) (haddress : s.natReg 198 = bankAddress B j.val v.val)
    (hF : s.natReg 112 = bankFactor j.val)
    (hc : s.natReg 108 = cacheAt (pointerLayout B i.n (scaleCount i) reserve N).cache i.n j.val)
    (hd : s.realReg 70 = delta i j.val)
    (hptrbase : s.natReg 96 = (pointerLayout B i.n (scaleCount i) reserve N).pointer)
    (hflagbase : s.natReg 98 = (pointerLayout B i.n (scaleCount i) reserve N).flags) :
    ∃ cost t ys, Eval reportEvent s cost t ∧
      cost ≤ 13*((adapterWrite i a j v (stored g v.val)).pointer v-a.pointer v)+44 ∧
      AdapterMemory i B reserve N (adapterWrite i a j v (stored g v.val)) ys t ∧
      ys = (if v ∈ xs then xs else xs++[v]) ∧
      (∀ address, address ≠ cacheAt (pointerLayout B i.n (scaleCount i) reserve N).cache i.n j.val+2*v.val →
        ¬PointerArrayCell (pointerLayout B i.n (scaleCount i) reserve N) i.n address →
        t.natMem address = s.natMem address ∧ t.realMem address = s.realMem address) := by
  classical
  let l := pointerLayout B i.n (scaleCount i) reserve N
  let ac := cacheUpdated i a j v (stored g v.val)
  let ap := pointerUpdated i ac v
  let aw := adapterWrite i a j v (stored g v.val)
  obtain ⟨cc,u,hu,hcc,hum,huframe⟩ := adapter_cache_step i hi p B reserve N hB a xs s h j v g
    hsource hnormal hg.zeroN hg.unit hv haddress hF hc hd
  have hug := hg.transfer hu globalFrame_cacheRefresh
  have hun (k : ℕ) (h128 : k ≠ 128) (h132 : k ≠ 132) (h38 : k ≠ 38) (h20 : k ≠ 20)
      (h130 : k ≠ 130) (h22 : k ≠ 22) (h24 : k ≠ 24) : u.natReg k = s.natReg k :=
    hu.nat_frame (CacheRefresh.nat_frame k h128 h132 h38 h20 h130 h22 h24)
  have huv : u.natReg 94 = v.val := (hun 94 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hv
  have hu96 : u.natReg 96 = l.pointer := (hun 96 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hptrbase
  have hu98 : u.natReg 98 = l.flags := (hun 98 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hflagbase
  obtain ⟨cp,w,hw,hcp,hwm,hwn,hwr⟩ := adapter_pointer_step i B reserve N hB ac xs u hum v (hp v).1 huv hu96 hug.scanZero hug.scanUnit
  have hwg := hug.transfer hw globalFrame_pointerRefresh
  have hwnreg (k : ℕ) (h38 : k ≠ 38) (h196 : k ≠ 196) (h30 : k ≠ 30) (h32 : k ≠ 32)
      (h40 : k ≠ 40) (h42 : k ≠ 42) (h44 : k ≠ 44) (h46 : k ≠ 46) : w.natReg k = u.natReg k :=
    hw.nat_frame (PointerRefresh.nat_frame k h38 h196 h30 h32 h40 h42 h44 h46)
  have hwv : w.natReg 94 = v.val := (hwnreg 94 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans huv
  have hw98 : w.natReg 98 = l.flags := (hwnreg 98 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hu98
  obtain ⟨cm,t,ys,ht,hcm,hys,htm,htframe⟩ := adapter_mark_step i B reserve N hB ap xs w hwm v hwv hw98 hwg.unit hwg.two
  have hmax : aw.maxima = ap.maxima := rfl
  have hpointer : aw.pointer = ap.pointer := by
    exact adapterWrite_pointer_unconditional i a hp j v (stored g v.val)
  have houtput : aw.output = ap.output := rfl
  have hdirty : aw.dirty ⊆ insert v ap.dirty := adapterWrite_dirty_subset i a a.dirty (fun _ h => h) j v (stored g v.val)
  have hfinal : AdapterMemory i B reserve N aw ys t := htm.state_transport hmax hpointer houtput hdirty
  have htravel : ap.pointer v-a.pointer v = aw.pointer v-a.pointer v := by rw [hpointer]
  refine ⟨cc+(cp+cm),t,ys,Eval.seq hu (Eval.seq hw ht),?_,hfinal,hys,?_⟩
  · change cp ≤ 13*(ap.pointer v-ac.pointer v)+20 at hcp
    have hac : ac.pointer v = a.pointer v := rfl
    rw [hac,htravel] at hcp
    change cc+(cp+cm) ≤ 13*(aw.pointer v-a.pointer v)+44
    omega
  · intro address hcache hnot
    have hm := htframe address hnot
    have hpne : address ≠ l.pointer+2*v.val := by
      intro hh;exact hnot ⟨v.val,v.isLt,Or.inl hh⟩
    have hpm : w.natMem address = u.natMem address := by rw [hwn,Function.update_of_ne hpne]
    have hcmem := huframe address hcache
    exact ⟨hm.1.trans (hpm.trans hcmem.1),hm.2.trans ((congrFun hwr address).trans hcmem.2)⟩
end DecrAlmostLinearSSSP.Decremental.Native
end s235
section s236
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
lemma eval_observed_interpreter (guest : Program) (t : ℕ) (B bank start : ℕ)
    (s : Data) (g : Machine) (h : ShadowDataRep B (bankFactor bank) s g) (hb : s.natReg 0 = B)
    (h1 : s.natReg 1 = 1) (hf : s.natReg 7 = bankFactor bank)
    (hrf : s.realReg 7 = (bankFactor bank : ℝ)) (h14 : s.natReg 14 = 2)
    (reports : List ℕ) (hl : ReportLog start reports s) (hstart : ∃ r, start = B+2*r+1)
    (hflag : s.natReg 4 ≤ 1)
    (hvalid : ∀ j < t, (execute guest g j).halted = false → ∃ ins, guest.code[(execute guest g j).pc]? = some ins)
    (hfinal : (execute guest g t).halted = true) :
    ∃ cost u, Eval (observedInterpreter guest.code) s cost u ∧
      cost ≤ (observedDispatchCharge guest.code+2)*t+2 ∧
      ShadowDataRep B (bankFactor bank) u (execute guest g t) ∧
      ReportLog start (reports++physicalTraceWrites B bank guest g t) u := by
  induction t generalizing s g reports with
  | zero =>
    have hgh : g.halted = true := hfinal
    have hs := h.halt_flag hflag
    have htest : ¬(Test.natLess 4 1).holds s := by simp [Test.holds,hs,hgh,h1]
    exact ⟨2,s,Eval.loopNo s htest,by simp,h,by simpa [physicalTraceWrites] using hl⟩
  | succ t ih =>
    by_cases hgh : g.halted = true
    · have hs := h.halt_flag hflag
      have htest : ¬(Test.natLess 4 1).holds s := by simp [Test.holds,hs,hgh,h1]
      refine ⟨2,s,Eval.loopNo s htest,by omega,?_,?_⟩
      · rwa [execute_halted guest g hgh]
      · simpa [physicalTraceWrites,hgh] using hl
    · have hgh' : g.halted = false := Bool.eq_false_iff.mpr hgh
      obtain ⟨ins,hins⟩ := hvalid 0 (by omega) hgh'
      have hins' : guest.code[g.pc]? = some ins := by simpa [execute] using hins
      obtain ⟨cost,u,he,hcost,hrep,hlog⟩ := eval_observed_dispatch_aux guest.code 0 s g h hb h1 hf hrf h14
        reports hl hstart (Nat.zero_le _) ins (by simpa only [Nat.sub_zero] using hins')
      rw [← step_eq_effect guest g ins hgh' hins'] at hrep
      have hu0 : u.natReg 0 = B := (he.nat_frame (observedDispatchAux_nat_frame _ _ 0 (Or.inl rfl))).trans hb
      have hu1 : u.natReg 1 = 1 := (he.nat_frame (observedDispatchAux_nat_frame _ _ 1 (Or.inr (Or.inl rfl)))).trans h1
      have hu7 : u.natReg 7 = bankFactor bank := (he.nat_frame (observedDispatchAux_nat_frame _ _ 7 (Or.inr (Or.inr rfl)))).trans hf
      have hur7 : u.realReg 7 = (bankFactor bank : ℝ) := (he.real_frame (observedDispatchAux_real_frame _ _)).trans hrf
      have hu14 : u.natReg 14 = 2 := (he.nat_frame (observedDispatchAux_nat14_frame _ _)).trans h14
      have huflag : u.natReg 4 ≤ 1 := he.flag_bound (observedDispatchAux_flag_frame _ _) hflag
      have hv : ∀ j < t, (execute guest (step guest g) j).halted = false → ∃ ins, guest.code[(execute guest (step guest g) j).pc]? = some ins := by
        intro j hj hh
        rw [← execute_succ_front] at hh ⊢
        exact hvalid (j+1) (by omega) hh
      have hfin : (execute guest (step guest g) t).halted = true := by rwa [← execute_succ_front]
      obtain ⟨rest,v,hrest,hrestcost,hrestrep,hrestlog⟩ := ih u (step guest g) hrep hu0 hu1 hu7 hur7 hu14
        (reports++physicalWrites B bank ins g) hlog huflag hv hfin
      have hs := h.halt_flag hflag
      have htest : (Test.natLess 4 1).holds s := by simp [Test.holds,hs,hgh',h1]
      refine ⟨cost+rest+2,v,Eval.loopYes htest he hrest,?_,?_,?_⟩
      · rw [Nat.mul_succ]
        omega
      · rwa [execute_succ_front]
      · simpa only [physicalTraceWrites,hgh',Bool.false_eq_true,if_false,hins',List.append_assoc] using hrestlog
lemma eval_observed_interpreter_ends (guest : Program) (B bank start : ℕ)
    (s : Data) (g final : Machine) (h : ShadowDataRep B (bankFactor bank) s g) (hb : s.natReg 0 = B)
    (h1 : s.natReg 1 = 1) (hf : s.natReg 7 = bankFactor bank)
    (hrf : s.realReg 7 = (bankFactor bank : ℝ)) (h14 : s.natReg 14 = 2)
    (reports : List ℕ) (hl : ReportLog start reports s) (hstart : ∃ r, start = B+2*r+1)
    (hflag : s.natReg 4 ≤ 1) (he : Ends guest g final) :
    ∃ cost u t, Eval (observedInterpreter guest.code) s cost u ∧ execute guest g t = final ∧
      cost ≤ (observedDispatchCharge guest.code+2)*(final.work-g.work)+2 ∧
      ShadowDataRep B (bankFactor bank) u final ∧
      ReportLog start (reports++physicalTraceWrites B bank guest g t) u ∧ t = final.work-g.work := by
  obtain ⟨t,ht,hhalt,hfault⟩ := he
  have hhalt' : (execute guest g t).halted = true := by rwa [ht]
  obtain ⟨r,_,hrun,hrwork⟩ := terminating_prefix guest g t hhalt'
  have hrfinal : execute guest g r = final := hrun.trans ht
  have hrfault : (execute guest g r).fault = false := by rwa [hrfinal]
  obtain ⟨cost,u,hu,hcost,hrep,hlog⟩ := eval_observed_interpreter guest r B bank start s g h hb h1 hf hrf h14
    reports hl hstart hflag (execution_valid_code guest g r hrfault) (by rwa [hrfinal])
  rw [ht] at hrwork
  refine ⟨cost,u,r,hu,hrfinal,?_,?_,hlog,hrwork⟩
  · rwa [← hrwork]
  · rwa [hrfinal] at hrep
lemma physicalTraceWrites_length (B bank : ℕ) (guest : Program) (g : Machine) (t : ℕ) :
    (physicalTraceWrites B bank guest g t).length ≤ t := by
  induction t generalizing g with
  | zero => simp [physicalTraceWrites]
  | succ t ih =>
    unfold physicalTraceWrites
    split_ifs
    · simp
    · cases hf : guest.code[g.pc]? with
      | none => simp
      | some ins =>
        have hc : (physicalWrites B bank ins g).length ≤ 1 := by cases ins <;> simp [physicalWrites,sourceWrite]
        have hr := ih (step guest g)
        simpa only [List.length_append,Nat.add_comm 1 t] using Nat.add_le_add hc hr
end DecrAlmostLinearSSSP.Decremental
end s236
section s237
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
lemma writtenVertex_store (i : Input) (p : Program) (c : Machine) (v : Fin i.n)
    (a d : ℕ) (hh : c.halted = false)
    (hc : p.code[c.pc]? = some (.store a d)) (ha : c.natReg a = v.val) :
    writtenVertex i p c = some v := by
  have hv : c.natReg a < i.n := by rw [ha]; exact v.isLt
  simp only [writtenVertex, hh, Bool.false_eq_true, if_false, hc, dif_pos hv]
  congr 1
  exact Fin.ext ha
lemma writtenVertex_storeN (i : Input) (p : Program) (c : Machine) (v : Fin i.n)
    (a d : ℕ) (hh : c.halted = false)
    (hc : p.code[c.pc]? = some (.storeN a d)) (ha : c.natReg a = v.val) :
    writtenVertex i p c = some v := by
  have hv : c.natReg a < i.n := by rw [ha]; exact v.isLt
  simp only [writtenVertex, hh, Bool.false_eq_true, if_false, hc, dif_pos hv]
  congr 1
  exact Fin.ext ha
lemma no_write_step (i : Input) (p : Program) (c : Machine) (v : Fin i.n)
    (hv : v ∉ (writtenVertex i p c).toList) :
    (step p c).realMem v.val = c.realMem v.val ∧ (step p c).natMem v.val = c.natMem v.val := by
  classical
  by_cases hh : c.halted = true
  · rw [step_of_halted p c hh]
    exact ⟨rfl, rfl⟩
  · have hhfalse : c.halted = false := Bool.eq_false_iff.mpr hh
    cases hc : p.code[c.pc]? with
    | none => simp only [step, hhfalse, Bool.false_eq_true, if_false, hc, and_self]
    | some ins =>
      cases ins with
      | store a d =>
        have ha : c.natReg a ≠ v.val := by
          intro ha
          have hw := writtenVertex_store i p c v a d hhfalse hc ha
          simp [hw] at hv
        simp only [step, hhfalse, Bool.false_eq_true, if_false, hc, Function.update_of_ne ha.symm, and_self]
      | storeN a d =>
        have ha : c.natReg a ≠ v.val := by
          intro ha
          have hw := writtenVertex_storeN i p c v a d hhfalse hc ha
          simp [hw] at hv
        simp only [step, hhfalse, Bool.false_eq_true, if_false, hc, Function.update_of_ne ha.symm, and_self]
      | less a b target | lessN a b target =>
        all_goals simp only [step, hhfalse, Bool.false_eq_true, if_false, hc]
        all_goals split_ifs <;> exact ⟨rfl, rfl⟩
      | _ => simp only [step, hhfalse, Bool.false_eq_true, if_false, hc, and_self]
lemma no_observed_write (i : Input) (p : Program) (c : Machine) (t : ℕ) (v : Fin i.n)
    (hv : v ∉ observedWrites i p c t) :
    (execute p c t).realMem v.val = c.realMem v.val ∧
      (execute p c t).natMem v.val = c.natMem v.val := by
  induction t generalizing c with
  | zero => exact ⟨rfl, rfl⟩
  | succ t ih =>
    simp only [observedWrites, List.mem_append, not_or] at hv
    obtain ⟨hreal, hnat⟩ := no_write_step i p c v hv.1
    obtain ⟨hreal', hnat'⟩ := ih (step p c) hv.2
    rw [execute_succ_front]
    exact ⟨hreal'.trans hreal, hnat'.trans hnat⟩
lemma stored_change_observed (i : Input) (p : Program) (c : Machine) (t : ℕ) (v : Fin i.n)
    (hv : stored (execute p c t) v.val ≠ stored c v.val) : v ∈ observedWrites i p c t := by
  by_contra hh
  obtain ⟨hr, hn⟩ := no_observed_write i p c t v hh
  exact hv (by simp only [stored, hr, hn])
end DecrAlmostLinearSSSP.Decremental
end s237
section s238
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma physicalWrites_writtenVertex (B bank : ℕ) (i : Input) (guest : Program) (g : Machine)
    (ins : Instruction) (hins : guest.code[g.pc]? = some ins) (hh : g.halted = false)
    (v : Fin i.n) (hv : v ∈ (writtenVertex i guest g).toList) :
    B+bankFactor bank*(2*v.val+1) ∈ physicalWrites B bank ins g := by
  cases ins with
  | store a d | storeN a d =>
    all_goals
      simp only [writtenVertex,hh,Bool.false_eq_true,if_false,hins] at hv
      split_ifs at hv with ha
      · have heq : (⟨g.natReg a,ha⟩ : Fin i.n) = v := by simpa [eq_comm] using hv
        have heq' : g.natReg a = v.val := congrArg Fin.val heq
        simp [physicalWrites,sourceWrite,heq']
      · simp at hv
  | _ => all_goals simp [writtenVertex,hh,hins] at hv
lemma physicalTraceWrites_covers (B bank : ℕ) (i : Input) (guest : Program) (g : Machine)
    (t : ℕ) (v : Fin i.n) (hv : v ∈ observedWrites i guest g t) :
    B+bankFactor bank*(2*v.val+1) ∈ physicalTraceWrites B bank guest g t := by
  induction t generalizing g with
  | zero => simp [observedWrites] at hv
  | succ t ih =>
    by_cases hh : g.halted = true
    · have hnil : observedWrites i guest g (t+1) = [] := by
        have hn : ∀ j, observedWrites i guest g j = [] := by
          intro j
          induction j with
          | zero => rfl
          | succ j ih => simpa only [observedWrites,writtenVertex,hh,if_true,Option.toList_none,
              step_of_halted guest g hh,List.nil_append] using ih
        exact hn _
      simp [hnil] at hv
    · have hh' := Bool.eq_false_iff.mpr hh
      cases hf : guest.code[g.pc]? with
      | none =>
        have hstep : (step guest g).halted = true := by simp [step,hh',hf]
        have hnil : ∀ j, observedWrites i guest (step guest g) j = [] := by
          intro j
          induction j with
          | zero => rfl
          | succ j ih =>
            simpa only [observedWrites,writtenVertex,hstep,if_true,Option.toList_none,
              step_of_halted guest (step guest g) hstep,List.nil_append] using ih
        simp only [observedWrites,writtenVertex,hh',Bool.false_eq_true,if_false,hf,Option.toList_none,
          List.nil_append,hnil] at hv
        simp at hv
      | some ins =>
        simp only [observedWrites,List.mem_append] at hv
        simp only [physicalTraceWrites,hh',Bool.false_eq_true,if_false,hf,List.mem_append]
        rcases hv with hv|hv
        · exact Or.inl (physicalWrites_writtenVertex B bank i guest g ins hf hh' v hv)
        · exact Or.inr (ih (step guest g) hv)
lemma physicalTraceWrites_covers_change (B bank : ℕ) (i : Input) (guest : Program)
    (g : Machine) (t : ℕ) (v : Fin i.n) (hv : stored (execute guest g t) v.val ≠ stored g v.val) :
    B+bankFactor bank*(2*v.val+1) ∈ physicalTraceWrites B bank guest g t :=
  physicalTraceWrites_covers B bank i guest g t v (stored_change_observed i guest g t v hv)
end DecrAlmostLinearSSSP.Decremental
end s238
section s239
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
lemma report_real_index (B bank a : ℕ) : reportRealIndex B bank (B+bankFactor bank*(2*a+1)) = (a : ℝ) := by
  have hF : (bankFactor bank : ℝ) ≠ 0 := by exact_mod_cast (bankFactor_positive bank).ne'
  unfold reportRealIndex
  push_cast
  field_simp
  <;> ring
lemma report_index (B bank a : ℕ) : reportIndex B bank (B+bankFactor bank*(2*a+1)) = a := by
  simp only [reportIndex,report_real_index,Nat.ceil_natCast]
lemma report_public_test (B bank a n : ℕ) :
    B+bankFactor bank*(2*a+1) < B+bankFactor bank*(2*n+1) ↔ a < n := by
  rw [Nat.add_lt_add_iff_left,Nat.mul_lt_mul_left (bankFactor_positive bank)]
  omega
lemma publicReport_encode (i : Input) (B bank : ℕ) (v : Fin i.n) :
    publicReport i B bank (B+bankFactor bank*(2*v.val+1)) = some v := by
  simp only [publicReport,report_public_test,v.isLt,if_true,report_index,dif_pos]
lemma publicReports_covers_change (i : Input) (B bank : ℕ) (guest : Program)
    (g : Machine) (t : ℕ) (v : Fin i.n) (hv : stored (execute guest g t) v.val ≠ stored g v.val) :
    v ∈ publicReports i B bank (physicalTraceWrites B bank guest g t) := by
  apply List.mem_filterMap.mpr
  exact ⟨_,physicalTraceWrites_covers_change B bank i guest g t v hv,publicReport_encode i B bank v⟩
lemma publicReports_length (i : Input) (B bank : ℕ) (guest : Program) (g : Machine) (t : ℕ) :
    (publicReports i B bank (physicalTraceWrites B bank guest g t)).length ≤ t :=
  (List.length_filterMap_le _ _).trans (physicalTraceWrites_length B bank guest g t)
lemma public_report_decoding_bound (i : Input) (hi : i.Valid) (B bank : ℕ) (a : ℕ) (ha : a < i.n) :
    0 ≤ reportRealIndex B bank (B+bankFactor bank*(2*a+1)) ∧
      reportRealIndex B bank (B+bankFactor bank*(2*a+1)) ≤ (2 : ℝ)^utilityDepth i.size := by
  rw [report_real_index]
  have ham : a ≤ i.size := (Nat.le_of_lt ha).trans hi.1
  have hamR : (a : ℝ) ≤ i.size := by exact_mod_cast ham
  have hm : (1 : ℝ) ≤ i.size := by
    exact_mod_cast (lt_of_lt_of_le (input_vertex_positive i) hi.1)
  refine ⟨Nat.cast_nonneg _,le_trans ?_ (utilityDepth_power i.size)⟩
  nlinarith only [hamR,hm]
end DecrAlmostLinearSSSP.Decremental
end s239
section s240
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.ReportDecode
open Structured
lemma prepare_eval (s : Data) : Eval prepare s 8 (prepared s) := eval_sequence_atoms atoms s
lemma prepare_nat (s : Data) : (prepared s).natReg = s.natReg := rfl
lemma prepare_memory (s : Data) : (prepared s).natMem = s.natMem ∧ (prepared s).realMem = s.realMem := ⟨rfl,rfl⟩
lemma prepare_value (s : Data) (B bank : ℕ) (hB : s.natReg 74 = B) (hF : s.natReg 112 = bankFactor bank) :
    (prepared s).realReg 202 = reportRealIndex B bank (s.natReg 198) := by
  simp [prepared,atoms,Atom.effect,instructionEffect,data,Data.machine,reportRealIndex,hB,hF,mul_comm]
lemma eval_code (s : Data) (B bank a N : ℕ) (hB : s.natReg 74 = B) (hF : s.natReg 112 = bankFactor bank)
    (haddress : s.natReg 198 = B+bankFactor bank*(2*a+1))
    (hz : s.natReg 56 = 0) (hrz : s.realReg 56 = 0) (h1 : s.natReg 26 = 1)
    (hupper : (a : ℝ) ≤ (2 : ℝ)^N) :
    ∃ cost t, Eval code s cost t ∧ t.natReg 94 = a ∧
      cost ≤ (dispatchCharge ScaledCeiling.ceilingProgram.code+3)*(16*N+32)+11 ∧
      (∀ address, (∀ r, address ≠ s.natReg 48+2*r+1) →
        t.natMem address = s.natMem address ∧ t.realMem address = s.realMem address) := by
  let u := prepared s
  have hu := prepare_eval s
  have hx : u.realReg 202 = (a : ℝ) := by rw [prepare_value s B bank hB hF,haddress,report_real_index]
  have huz : u.natReg 56 = 0 := hz
  have hurz : u.realReg 56 = 0 := by simpa [u,prepared,atoms,Atom.effect,instructionEffect,data,Data.machine] using hrz
  obtain ⟨cost,t,he,hout,hcost,hframe,_⟩ := ScaledCeiling.productReal_eval u 94 26 202 N huz hurz
    (by rw [hx];exact Nat.cast_nonneg _) (by rwa [hx])
  refine ⟨8+cost,t,Eval.seq hu he,?_,by omega,?_⟩
  · have hu1 : u.natReg 26 = 1 := h1
    simpa only [hx,Nat.ceil_natCast,hu1,Nat.one_mul] using hout
  · intro address havoid
    have hh := hframe address havoid
    exact ⟨hh.2,hh.1⟩
lemma nat_frame (k : ℕ) (hk : 10 ≤ k) (hev : Even k) (h94 : k ≠ 94) (h58 : k ≠ 58) : NatFrame code k := by
  refine ⟨?_,ScaledCeiling.productReal_nat_frame _ _ _ k hk hev h94 h58⟩
  simp [prepare,atoms,Structured.sequence,NatFrame,writesNat]
lemma real_frame (k : ℕ) (hk : 10 ≤ k) (hev : Even k)
    (h202 : k ≠ 202) (h204 : k ≠ 204) (h206 : k ≠ 206) (h58 : k ≠ 58) : RealFrame code k := by
  refine ⟨?_,ScaledCeiling.productReal_real_frame _ _ _ k hk hev h58⟩
  simp [prepare,atoms,Structured.sequence,RealFrame,writesReal,Ne.symm h202,Ne.symm h204,Ne.symm h206]
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
theorem solution : (((((((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (C : Real) (a : Nat → Real) (B reserve : Nat)
      (f : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → DecrAlmostLinearSSSP.Decremental.Machine),
      (∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
          DecrAlmostLinearSSSP.Decremental.Native.InitialFacts p C a i
            (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q) (f q)) →
        ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
          DecrAlmostLinearSSSP.Decremental.Native.InitDone i p B reserve f s →
            @LE.le.{0} Nat instLENat i.n B →
              DecrAlmostLinearSSSP.Decremental.Native.PointerBases
                  (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                      (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve
                      (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).record
                  (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                      (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve
                      (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).pointer
                  (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                      (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve
                      (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).flags
                  (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                      (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve
                      (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).list
                  s →
                ∃ cost t,
                  And
                    (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                      DecrAlmostLinearSSSP.Decremental.Native.initializePublic s cost t)
                    (And
                      (@LE.le.{0} Nat instLENat cost
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
                                (DecrAlmostLinearSSSP.Decremental.scaleCount i))
                              (@OfNat.ofNat.{0} Nat (nat_lit 48) (instOfNatNat (nat_lit 48))))
                            i.n)
                          (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))))
                      (And
                        (DecrAlmostLinearSSSP.Decremental.Native.Globals i B
                          (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n
                              (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve
                              (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).utility
                          t)
                        (And
                          (∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
                            DecrAlmostLinearSSSP.Decremental.Native.ScaleMemory i p B
                              (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q)
                              (DecrAlmostLinearSSSP.Decremental.Native.recordAt
                                (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n
                                    (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve
                                    (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).records
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                    (DecrAlmostLinearSSSP.Decremental.registerBound p.code))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                                (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q))
                              (DecrAlmostLinearSSSP.Decremental.Native.cacheAt
                                (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n
                                    (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve
                                    (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).caches
                                i.n (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q))
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
                                (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q))
                              (f q) (fun v => DecrAlmostLinearSSSP.Decremental.stored (f q) (@Fin.val i.n v)) t)
                          (And
                            (@DecrAlmostLinearSSSP.Decremental.DirtyMark.View i.n
                              (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                                  (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve
                                  (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).flags
                              (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                                  (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve
                                  (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).list
                              (@List.nil.{0} (Fin i.n)) t)
                            (And
                              (@Eq.{1} ENNReal
                                (DecrAlmostLinearSSSP.Decremental.stored t.machine (@Fin.val i.n i.source))
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
                                (And
                                  (∀ (v : Fin i.n),
                                    And
                                      (@LE.le.{0} ENNReal ENNReal.instLE (i.dist (@List.nil.{0} (Fin i.k)) v)
                                        (DecrAlmostLinearSSSP.Decremental.stored t.machine (@Fin.val i.n v)))
                                      (And
                                        (@LE.le.{0} ENNReal ENNReal.instLE
                                          (DecrAlmostLinearSSSP.Decremental.stored t.machine (@Fin.val i.n v))
                                          (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                                            (@instHMul.{0} ENNReal
                                              (@Distrib.toMul.{0} ENNReal
                                                (@instDistribOfSemiring.{0} ENNReal
                                                  (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                                            (ENNReal.ofReal
                                              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                                (@OfNat.ofNat.{0} Real (nat_lit 1)
                                                  (@One.toOfNat1.{0} Real Real.instOne))
                                                i.accuracy))
                                            (i.dist (@List.nil.{0} (Fin i.k)) v)))
                                        (Iff
                                          (@Eq.{1} ENNReal
                                            (DecrAlmostLinearSSSP.Decremental.stored t.machine (@Fin.val i.n v))
                                            (@Top.top.{0} ENNReal ENNReal.instTop))
                                          (Not
                                            (@DecrAlmostLinearSSSP.Decremental.Reachable i.n i.k i.graph
                                              (@DecrAlmostLinearSSSP.Decremental.live i.k (@List.nil.{0} (Fin i.k)))
                                              i.source v)))))
                                  (And
                                    (∀ (v : Fin i.n),
                                      @Eq.{1} ENNReal
                                        (DecrAlmostLinearSSSP.Decremental.stored t.machine (@Fin.val i.n v))
                                        (DecrAlmostLinearSSSP.Decremental.selected i
                                          (fun q v => DecrAlmostLinearSSSP.Decremental.stored (f q) (@Fin.val i.n v))
                                          (DecrAlmostLinearSSSP.Decremental.Native.initialPointers i fun q v =>
                                            DecrAlmostLinearSSSP.Decremental.stored (f q) (@Fin.val i.n v))
                                          v))
                                    (And
                                      (∀ (v : Fin i.n),
                                        @Eq.{1} Nat
                                          (t.natMem
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                                                  (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve
                                                  (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).pointer
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                (@Fin.val i.n v))))
                                          (DecrAlmostLinearSSSP.Decremental.Native.scanRecord i
                                            (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                                                (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve
                                                (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).record
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                (DecrAlmostLinearSSSP.Decremental.registerBound p.code))
                                              (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                                            (DecrAlmostLinearSSSP.Decremental.Native.initialPointers i
                                              (fun q v =>
                                                DecrAlmostLinearSSSP.Decremental.stored (f q) (@Fin.val i.n v))
                                              v)))
                                      (And
                                        (∀ (r : Nat),
                                          @LE.le.{0} Nat instLENat
                                              (DecrAlmostLinearSSSP.Decremental.registerBound p.code) r →
                                            And
                                              (@Eq.{1} Nat (t.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg r))
                                                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                              (@Eq.{1} Real (t.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg r))
                                                (@OfNat.ofNat.{0} Real (nat_lit 0)
                                                  (@Zero.toOfNat0.{0} Real Real.instZero))))
                                        (DecrAlmostLinearSSSP.Decremental.Native.PublicFrame
                                          (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                                            (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve
                                            (DecrAlmostLinearSSSP.Decremental.registerBound p.code))
                                          i.n s t)))))))))))) ∧ (∀ {a b : DecrAlmostLinearSSSP.Decremental.Structured.Cmd},
  DecrAlmostLinearSSSP.Decremental.Native.PublicControlFrame a →
    DecrAlmostLinearSSSP.Decremental.Native.PublicControlFrame b →
      DecrAlmostLinearSSSP.Decremental.Native.PublicControlFrame (a.seq b))) ∧ ((∀ {cmd : DecrAlmostLinearSSSP.Decremental.Structured.Cmd},
  DecrAlmostLinearSSSP.Decremental.Native.ControlFrame cmd →
    DecrAlmostLinearSSSP.Decremental.Native.PublicControlFrame cmd) ∧ (DecrAlmostLinearSSSP.Decremental.Native.PublicControlFrame DecrAlmostLinearSSSP.Decremental.Native.pointerStart))) ∧ (((DecrAlmostLinearSSSP.Decremental.Native.PublicControlFrame DecrAlmostLinearSSSP.Decremental.Native.pointerBody) ∧ (DecrAlmostLinearSSSP.Decremental.Native.PublicControlFrame DecrAlmostLinearSSSP.Decremental.Native.pointerLoop)) ∧ ((DecrAlmostLinearSSSP.Decremental.Native.PublicControlFrame DecrAlmostLinearSSSP.Decremental.Native.buildPointers) ∧ ((DecrAlmostLinearSSSP.Decremental.Native.PublicControlFrame DecrAlmostLinearSSSP.Decremental.DirtyCommit.code) ∧ (DecrAlmostLinearSSSP.Decremental.Native.PublicControlFrame DecrAlmostLinearSSSP.Decremental.Native.initializePublic))))) ∧ ((((DecrAlmostLinearSSSP.Decremental.Native.ControlFrame DecrAlmostLinearSSSP.Decremental.Native.clearLast) ∧ (∀ {B n S reserve N cost : Nat} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {cmd : DecrAlmostLinearSSSP.Decremental.Structured.Cmd},
  DecrAlmostLinearSSSP.Decremental.Native.Controls B n S reserve N s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval cmd s cost t →
      DecrAlmostLinearSSSP.Decremental.Native.PublicControlFrame cmd →
        DecrAlmostLinearSSSP.Decremental.Native.Controls B n S reserve N t)) ∧ ((∀ {B n S reserve N : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.Controls B n S reserve N s →
    DecrAlmostLinearSSSP.Decremental.Native.PointerBases
      (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B n S reserve N).record
      (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B n S reserve N).pointer
      (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B n S reserve N).flags
      (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B n S reserve N).list s) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program} {B reserve : Nat}
  {g : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → DecrAlmostLinearSSSP.Decremental.Machine}
  {b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal} {ptr : Fin i.n → Nat}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.NormalMemory i p B reserve g b ptr s →
    @Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.stored s.machine (@Fin.val i.n i.source))
      (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero))))) ∧ (((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program} {B reserve : Nat}
  {g : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → DecrAlmostLinearSSSP.Decremental.Machine}
  {b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal} {ptr : Fin i.n → Nat}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.NormalMemory i p B reserve g b ptr s →
    DecrAlmostLinearSSSP.Decremental.Native.ScanTable i
      (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i)
          reserve (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).record
      (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i)
          reserve (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).cache
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (DecrAlmostLinearSSSP.Decremental.registerBound p.code))
        (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
      b s) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) i.n →
      @LT.lt.{0} Real Real.instLT
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@Nat.cast.{0} Real Real.instNatCast i.size))
          i.accuracy →
        ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (C : Real) (a : Nat → Real) (queryBound coefficient : Nat),
          (∀ (x : DecrAlmostLinearSSSP.Decremental.Input),
              x.Valid →
                @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) x.n →
                  @LE.le.{0} Nat instLENat x.W
                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) x.size
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
                    @LT.lt.{0} Real Real.instLT
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                          (@Nat.cast.{0} Real Real.instNatCast x.size))
                        x.accuracy →
                      @LT.lt.{0} Real Real.instLT x.accuracy
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
                        DecrAlmostLinearSSSP.Decremental.Maintains p C a queryBound Bool.false x) →
            ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
              DecrAlmostLinearSSSP.Decremental.InputCapture.RawInput i s →
                @Eq.{1} (Nat → Nat) s.natMem (DecrAlmostLinearSSSP.Decremental.initialMachine p i).natMem →
                  (@Eq.{1} (Nat → Real) s.realMem fun x =>
                      @OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
                    (∀ (r : Nat),
                        @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.registerBound p.code) r →
                          And
                            (@Eq.{1} Nat (s.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg r))
                              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                            (@Eq.{1} Real (s.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg r))
                              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))) →
                      ∃ f cost t,
                        And
                          (∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
                            DecrAlmostLinearSSSP.Decremental.Native.InitialFacts p C a i
                              (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q) (f q))
                          (And
                            (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                              (DecrAlmostLinearSSSP.Decremental.Native.normalInitialize coefficient p) s cost t)
                            (And
                              (@LE.le.{0} Nat instLENat cost
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (DecrAlmostLinearSSSP.Decremental.Native.setupCost i coefficient
                                        (DecrAlmostLinearSSSP.Decremental.registerBound p.code))
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (DecrAlmostLinearSSSP.Decremental.dispatchCharge p.code)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                              (@DecrAlmostLinearSSSP.Decremental.Native.maxInitialWork i f))
                                            (DecrAlmostLinearSSSP.Decremental.Native.initOverhead i p))
                                          (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                                        (DecrAlmostLinearSSSP.Decremental.scaleCount i)))
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
                                          (DecrAlmostLinearSSSP.Decremental.scaleCount i))
                                        (@OfNat.ofNat.{0} Nat (nat_lit 48) (instOfNatNat (nat_lit 48))))
                                      i.n))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))))
                              (And
                                (DecrAlmostLinearSSSP.Decremental.Native.NormalMemory i p
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) coefficient
                                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                        (@instHPow.{0, 0} Nat Nat
                                          (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                        i.size (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                  f (fun q v => DecrAlmostLinearSSSP.Decremental.stored (f q) (@Fin.val i.n v))
                                  (DecrAlmostLinearSSSP.Decremental.Native.initialPointers i fun q v =>
                                    DecrAlmostLinearSSSP.Decremental.stored (f q) (@Fin.val i.n v))
                                  t)
                                (And
                                  (@Eq.{1} ENNReal
                                    (DecrAlmostLinearSSSP.Decremental.stored t.machine (@Fin.val i.n i.source))
                                    (@OfNat.ofNat.{0} ENNReal (nat_lit 0)
                                      (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero)))
                                  (∀ (v : Fin i.n),
                                    And
                                      (@LE.le.{0} ENNReal ENNReal.instLE (i.dist (@List.nil.{0} (Fin i.k)) v)
                                        (DecrAlmostLinearSSSP.Decremental.stored t.machine (@Fin.val i.n v)))
                                      (And
                                        (@LE.le.{0} ENNReal ENNReal.instLE
                                          (DecrAlmostLinearSSSP.Decremental.stored t.machine (@Fin.val i.n v))
                                          (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                                            (@instHMul.{0} ENNReal
                                              (@Distrib.toMul.{0} ENNReal
                                                (@instDistribOfSemiring.{0} ENNReal
                                                  (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                                            (ENNReal.ofReal
                                              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                                (@OfNat.ofNat.{0} Real (nat_lit 1)
                                                  (@One.toOfNat1.{0} Real Real.instOne))
                                                i.accuracy))
                                            (i.dist (@List.nil.{0} (Fin i.k)) v)))
                                        (Iff
                                          (@Eq.{1} ENNReal
                                            (DecrAlmostLinearSSSP.Decremental.stored t.machine (@Fin.val i.n v))
                                            (@Top.top.{0} ENNReal ENNReal.instTop))
                                          (Not
                                            (@DecrAlmostLinearSSSP.Decremental.Reachable i.n i.k i.graph
                                              (@DecrAlmostLinearSSSP.Decremental.live i.k (@List.nil.{0} (Fin i.k)))
                                              i.source v))))))))))) ∧ ((∀ (c : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) c →
    @Filter.Tendsto.{0, 0} Nat Nat (fun m => @HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) c m)
      (@Filter.atTop.{0} Nat Nat.instPreorder) (@Filter.atTop.{0} Nat Nat.instPreorder)) ∧ ((∀ (c : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) c →
    @Filter.Tendsto.{0, 0} Nat Real
      (fun m =>
        @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (Real.log
            (@Nat.cast.{0} Real Real.instNatCast
              (@Max.max.{0} Nat Nat.instMax (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) c m))))
          (Real.log
            (@Nat.cast.{0} Real Real.instNatCast
              (@Max.max.{0} Nat Nat.instMax (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))))
      (@Filter.atTop.{0} Nat Nat.instPreorder)
      (@nhds.{0} Real
        (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))) ∧ (∀ (a : Nat → Real),
  DecrAlmostLinearSSSP.Decremental.Subpolynomial a →
    ∀ (c : Nat),
      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) c →
        DecrAlmostLinearSSSP.Decremental.Subpolynomial fun m =>
          a (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) c m))))))) ∧ (((((∀ (a : Nat → Real),
  DecrAlmostLinearSSSP.Decremental.Subpolynomial a →
    DecrAlmostLinearSSSP.Decremental.Subpolynomial (DecrAlmostLinearSSSP.Decremental.normalWrapperOverhead a)) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (C D work : Real),
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C →
        @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) D →
          ∀ (a : Nat → Real),
            DecrAlmostLinearSSSP.Decremental.Subpolynomial a →
              @LE.le.{0} Real Real.instLE work
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) D
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@Nat.cast.{0} Real Real.instNatCast i.size)
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                  (@OfNat.ofNat.{0} Real (nat_lit 1024)
                                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 1024) Real.instNatCast
                                      (@Nat.instAtLeastTwoHAddOfNat
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1023) (instOfNatNat (nat_lit 1023)))
                                        (@Nat.instNeZeroSucc
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1022) (instOfNatNat (nat_lit 1022)))))))
                                  C)
                                (@Nat.cast.{0} Real Real.instNatCast i.size))
                              (a
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64))) i.size)))
                            i.accuracy)))
                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@OfNat.ofNat.{0} Real (nat_lit 16)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))))))
                          (@Nat.cast.{0} Real Real.instNatCast (DecrAlmostLinearSSSP.Decremental.utilityDepth i.size)))
                        (@OfNat.ofNat.{0} Real (nat_lit 32)
                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
                            (@Nat.instAtLeastTwoHAddOfNat
                              (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))))
                    (@Nat.cast.{0} Real Real.instNatCast (DecrAlmostLinearSSSP.Decremental.scaleCount i))) →
                @LE.le.{0} Real Real.instLE work
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) D
                            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                (@OfNat.ofNat.{0} Real (nat_lit 1024)
                                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 1024) Real.instNatCast
                                    (@Nat.instAtLeastTwoHAddOfNat
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1023) (instOfNatNat (nat_lit 1023)))
                                      (@Nat.instNeZeroSucc
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1022) (instOfNatNat (nat_lit 1022)))))))
                                C)))
                          (@Nat.cast.{0} Real Real.instNatCast i.size))
                        (DecrAlmostLinearSSSP.Decremental.normalWrapperOverhead a i.size))
                      i.accuracy)
                    (@Max.max.{0} Real Real.instMax
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                      (DecrAlmostLinearSSSP.Decremental.logarithm2 (@Nat.cast.{0} Real Real.instNatCast i.W)))))) ∧ ((∀ (m n k S d M N dc dp coefficient : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m →
    @LE.le.{0} Nat instLENat n m →
      @LE.le.{0} Nat instLENat k m →
        @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) S →
          @LE.le.{0} Nat instLENat
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dc
                                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16))) d)
                              (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))))
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dc
                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16))) S)
                              (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))))
                        coefficient)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) N)
                        (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 38) (instOfNatNat (nat_lit 38))))
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dp
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          M)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))) N)
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16))) d)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))))))
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) k
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dc
                                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16))) d)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))))
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13))) n))
                          (@OfNat.ofNat.{0} Nat (nat_lit 158) (instOfNatNat (nat_lit 158)))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                    S))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13))) S)
                    (@OfNat.ofNat.{0} Nat (nat_lit 48) (instOfNatNat (nat_lit 48))))
                  n))
              (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) coefficient
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16))) N))
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))) dc))
                      dp)
                    (@OfNat.ofNat.{0} Nat (nat_lit 500) (instOfNatNat (nat_lit 500))))
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m M))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16))) d)
                  (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))))
              S)) ∧ (∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (coefficient : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
    (DecrAlmostLinearSSSP.Decremental.Native.normalInitConstant p coefficient)))) ∧ (((∀ {i : DecrAlmostLinearSSSP.Decremental.Input},
  i.Valid →
    ∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {C : Real},
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C →
        ∀ {a : Nat → Real},
          DecrAlmostLinearSSSP.Decremental.Subpolynomial a →
            ∀ (f : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → DecrAlmostLinearSSSP.Decremental.Machine),
              (∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
                  DecrAlmostLinearSSSP.Decremental.Native.InitialFacts p C a i
                    (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q) (f q)) →
                ∀ (coefficient cost : Nat),
                  @LE.le.{0} Nat instLENat cost
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (DecrAlmostLinearSSSP.Decremental.Native.setupCost i coefficient
                              (DecrAlmostLinearSSSP.Decremental.registerBound p.code))
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (DecrAlmostLinearSSSP.Decremental.dispatchCharge p.code)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (@DecrAlmostLinearSSSP.Decremental.Native.maxInitialWork i f))
                                  (DecrAlmostLinearSSSP.Decremental.Native.initOverhead i p))
                                (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                              (DecrAlmostLinearSSSP.Decremental.scaleCount i)))
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
                                (DecrAlmostLinearSSSP.Decremental.scaleCount i))
                              (@OfNat.ofNat.{0} Nat (nat_lit 48) (instOfNatNat (nat_lit 48))))
                            i.n))
                        (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))) →
                    @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast cost)
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                (@Nat.cast.{0} Real Real.instNatCast
                                  (DecrAlmostLinearSSSP.Decremental.Native.normalInitConstant p coefficient))
                                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                    (@OfNat.ofNat.{0} Real (nat_lit 1024)
                                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 1024) Real.instNatCast
                                        (@Nat.instAtLeastTwoHAddOfNat
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1023) (instOfNatNat (nat_lit 1023)))
                                          (@Nat.instNeZeroSucc
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1022) (instOfNatNat (nat_lit 1022)))))))
                                    C)))
                              (@Nat.cast.{0} Real Real.instNatCast i.size))
                            (DecrAlmostLinearSSSP.Decremental.normalWrapperOverhead a i.size))
                          i.accuracy)
                        (@Max.max.{0} Real Real.instMax
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                          (DecrAlmostLinearSSSP.Decremental.logarithm2 (@Nat.cast.{0} Real Real.instNatCast i.W))))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Native.CacheRefresh.prepare s
    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
    (DecrAlmostLinearSSSP.Decremental.Native.CacheRefresh.prepared s))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    And
      (@Eq.{1} Nat
        ((DecrAlmostLinearSSSP.Decremental.Native.CacheRefresh.prepared s).natReg
          (@OfNat.ofNat.{0} Nat (nat_lit 128) (instOfNatNat (nat_lit 128))))
        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 198) (instOfNatNat (nat_lit 198)))))
      (And
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.Native.CacheRefresh.prepared s).natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 132) (instOfNatNat (nat_lit 132))))
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112)))))
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.Native.CacheRefresh.prepared s).natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 108) (instOfNatNat (nat_lit 108))))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94))))))))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
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
                                        (@Eq.{1} Real (t.realMem address) (s.realMem address)))))) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B reserve N : Nat}
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
            t))))) ∧ ((((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (recordBase cacheBase stride : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (v : Fin i.n) (start : Nat),
  @LE.le.{0} Nat instLENat start (DecrAlmostLinearSSSP.Decremental.scaleCount i) →
    @Eq.{1} Nat
      (DecrAlmostLinearSSSP.Decremental.LinkedScan.headAddress
        (DecrAlmostLinearSSSP.Decremental.LinkedScan.rowsFrom
          (DecrAlmostLinearSSSP.Decremental.Native.scanRow i recordBase cacheBase stride s v)
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
            (DecrAlmostLinearSSSP.Decremental.scaleCount i) start)
          start))
      (DecrAlmostLinearSSSP.Decremental.Native.scanRecord i recordBase stride start)) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (recordBase cacheBase stride : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data)
  (b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal),
  DecrAlmostLinearSSSP.Decremental.Native.ScanTable i recordBase cacheBase stride b s →
    ∀ (v : Fin i.n) (start : Nat),
      @LE.le.{0} Nat instLENat start (DecrAlmostLinearSSSP.Decremental.scaleCount i) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
            (DecrAlmostLinearSSSP.Decremental.Native.scanRecord i recordBase stride start) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 38) (instOfNatNat (nat_lit 38))))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val i.n v)) →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 34) (instOfNatNat (nat_lit 34))))
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
              @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 36) (instOfNatNat (nat_lit 36))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                ∃ cost t,
                  And
                    (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.LinkedScan.code s
                      cost t)
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
                          (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))))
                      (And
                        (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
                          (DecrAlmostLinearSSSP.Decremental.Native.scanRecord i recordBase stride
                            (DecrAlmostLinearSSSP.Decremental.advance i b v
                              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                                (DecrAlmostLinearSSSP.Decremental.scaleCount i) start)
                              start)))
                        (And (@Eq.{1} (Nat → Real) t.realMem s.realMem) (@Eq.{1} (Nat → Nat) t.natMem s.natMem)))))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Native.PointerRefresh.prepare s
    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
    (DecrAlmostLinearSSSP.Decremental.Native.PointerRefresh.prepared s)) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  And
    (@Eq.{1} Nat
      ((DecrAlmostLinearSSSP.Decremental.Native.PointerRefresh.prepared s).natReg
        (@OfNat.ofNat.{0} Nat (nat_lit 38) (instOfNatNat (nat_lit 38))))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94))))))
    (And
      (@Eq.{1} Nat
        ((DecrAlmostLinearSSSP.Decremental.Native.PointerRefresh.prepared s).natReg
          (@OfNat.ofNat.{0} Nat (nat_lit 196) (instOfNatNat (nat_lit 196))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 96) (instOfNatNat (nat_lit 96))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94)))))))
      (@Eq.{1} Nat
        ((DecrAlmostLinearSSSP.Decremental.Native.PointerRefresh.prepared s).natReg
          (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
        (s.natMem
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 96) (instOfNatNat (nat_lit 96))))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94)))))))))) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 38) (instOfNatNat (nat_lit 38))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 196) (instOfNatNat (nat_lit 196))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))) →
        DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
          DecrAlmostLinearSSSP.Decremental.Native.PointerRefresh.prepare k)))) ∧ (((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (recordBase cacheBase stride pointerBase : Nat)
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
                          (@Eq.{1} (Nat → Real) t.realMem s.realMem)))) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 38) (instOfNatNat (nat_lit 38))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 196) (instOfNatNat (nat_lit 196))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 42) (instOfNatNat (nat_lit 42))) →
              @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 44) (instOfNatNat (nat_lit 44))) →
                @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 46) (instOfNatNat (nat_lit 46))) →
                  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
                    DecrAlmostLinearSSSP.Decremental.Native.PointerRefresh.code k)) ∧ ((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))) →
      DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Native.PointerRefresh.code
        k) ∧ ((∀ {n flags list : Nat} {xs : List.{0} (Fin n)} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
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
            @DecrAlmostLinearSSSP.Decremental.DirtyMark.View n flags list xs t) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B reserve N : Nat} {a : DecrAlmostLinearSSSP.Decremental.AdapterState i}
  {xs : List.{0} (Fin i.n)} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.AdapterMemory i B reserve N a xs s →
    @Eq.{1} (Nat → Nat) t.natMem s.natMem →
      @Eq.{1} (Nat → Real) t.realMem s.realMem →
        @Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 182) (instOfNatNat (nat_lit 182))))
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 182) (instOfNatNat (nat_lit 182)))) →
          @Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 180) (instOfNatNat (nat_lit 180))))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 180) (instOfNatNat (nat_lit 180)))) →
            DecrAlmostLinearSSSP.Decremental.Native.AdapterMemory i B reserve N a xs t))))))) ∧ ((((((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 128) (instOfNatNat (nat_lit 128))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 132) (instOfNatNat (nat_lit 132))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 38) (instOfNatNat (nat_lit 38))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 130) (instOfNatNat (nat_lit 130))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) →
              @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 24) (instOfNatNat (nat_lit 24))) →
                DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
                  DecrAlmostLinearSSSP.Decremental.Native.CacheRefresh.code k) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) →
      DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Native.CacheRefresh.code k)) ∧ ((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 186) (instOfNatNat (nat_lit 186))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 184) (instOfNatNat (nat_lit 184))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 188) (instOfNatNat (nat_lit 188))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 180) (instOfNatNat (nat_lit 180))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 182) (instOfNatNat (nat_lit 182))) →
            DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.DirtyMark.code k) ∧ (∀ (k : Nat), DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.DirtyMark.code k))) ∧ (((DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame DecrAlmostLinearSSSP.Decremental.Native.CacheRefresh.code) ∧ (DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame DecrAlmostLinearSSSP.Decremental.Native.PointerRefresh.code)) ∧ ((DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame DecrAlmostLinearSSSP.Decremental.DirtyMark.code) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (B reserve N : Nat),
      @LE.le.{0} Nat instLENat i.n B →
        ∀ (a : DecrAlmostLinearSSSP.Decremental.AdapterState i) (xs : List.{0} (Fin i.n))
          (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
          DecrAlmostLinearSSSP.Decremental.Native.AdapterMemory i B reserve N a xs s →
            ∀ (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n)
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
                  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94))))
                          (@Fin.val i.n v) →
                        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 198) (instOfNatNat (nat_lit 198))))
                            (DecrAlmostLinearSSSP.Decremental.bankAddress B
                              (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) (@Fin.val i.n v)) →
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
                                ∃ cost t,
                                  And
                                    (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                      DecrAlmostLinearSSSP.Decremental.Native.CacheRefresh.code s cost t)
                                    (And
                                      (@LE.le.{0} Nat instLENat cost
                                        (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16))))
                                      (And
                                        (DecrAlmostLinearSSSP.Decremental.Native.AdapterMemory i B reserve N
                                          (DecrAlmostLinearSSSP.Decremental.Native.cacheUpdated i a j v
                                            (DecrAlmostLinearSSSP.Decremental.stored g (@Fin.val i.n v)))
                                          xs t)
                                        (∀ (address : Nat),
                                          @Ne.{1} Nat address
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (DecrAlmostLinearSSSP.Decremental.Native.cacheAt
                                                  (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                                                      (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).cache
                                                  i.n (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j))
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                  (@Fin.val i.n v))) →
                                            And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                              (@Eq.{1} Real (t.realMem address) (s.realMem address)))))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (B reserve N : Nat),
  @LE.le.{0} Nat instLENat i.n B →
    ∀ (a : DecrAlmostLinearSSSP.Decremental.AdapterState i) (xs : List.{0} (Fin i.n))
      (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
      DecrAlmostLinearSSSP.Decremental.Native.AdapterMemory i B reserve N a xs s →
        ∀ (v : Fin i.n),
          @LE.le.{0} Nat instLENat (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i a v)
              (DecrAlmostLinearSSSP.Decremental.scaleCount i) →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94)))) (@Fin.val i.n v) →
              @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 96) (instOfNatNat (nat_lit 96))))
                  (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                      (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).pointer →
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
                                  (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i
                                    (DecrAlmostLinearSSSP.Decremental.Native.pointerUpdated i a v) v)
                                  (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i a v)))
                              (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
                          (And
                            (DecrAlmostLinearSSSP.Decremental.Native.AdapterMemory i B reserve N
                              (DecrAlmostLinearSSSP.Decremental.Native.pointerUpdated i a v) xs t)
                            (And
                              (@Eq.{1} (Nat → Nat) t.natMem
                                (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natMem
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                                        (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).pointer
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val i.n v)))
                                  (DecrAlmostLinearSSSP.Decremental.Native.scanRecord i
                                    (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                                        (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).record
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) N)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                                    (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i
                                      (DecrAlmostLinearSSSP.Decremental.Native.pointerUpdated i a v) v))))
                              (@Eq.{1} (Nat → Real) t.realMem s.realMem))))))))) ∧ ((((∀ {n flags list : Nat} (xs : List.{0} (Fin n)) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (v : Fin n),
  @DecrAlmostLinearSSSP.Decremental.DirtyMark.View n flags list xs s →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94)))) (@Fin.val n v) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 98) (instOfNatNat (nat_lit 98)))) flags →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
          @Membership.mem.{0, 0} (Fin n) (List.{0} (Fin n)) (@List.instMembership.{0} (Fin n)) xs v →
            DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.DirtyMark.code s
              (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
              (DecrAlmostLinearSSSP.Decremental.DirtyMark.prefixData s)) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (B reserve N : Nat),
  @LE.le.{0} Nat instLENat i.n B →
    ∀ (a : DecrAlmostLinearSSSP.Decremental.AdapterState i) (xs : List.{0} (Fin i.n))
      (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
      DecrAlmostLinearSSSP.Decremental.Native.AdapterMemory i B reserve N a xs s →
        ∀ (v : Fin i.n),
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94)))) (@Fin.val i.n v) →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 98) (instOfNatNat (nat_lit 98))))
                (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                    (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).flags →
              @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                  ∃ cost t ys,
                    And
                      (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.DirtyMark.code
                        s cost t)
                      (And (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                        (And
                          (@Eq.{1} (List.{0} (Fin i.n)) ys
                            (@ite.{1} (List.{0} (Fin i.n))
                              (@Membership.mem.{0, 0} (Fin i.n) (List.{0} (Fin i.n))
                                (@List.instMembership.{0} (Fin i.n)) xs v)
                              (@List.instDecidableMemOfLawfulBEq.{0} (Fin i.n)
                                (@instBEqOfDecidableEq.{0} (Fin i.n) (instDecidableEqFin i.n))
                                (@Std.LawfulBEqOrd.lawfulBEq.{0} (Fin i.n)
                                  (@instBEqOfDecidableEq.{0} (Fin i.n) (instDecidableEqFin i.n)) (instOrdFin i.n)
                                  (@Std.LawfulBCmp.toLawfulBEqCmp.{0} (Fin i.n)
                                    (@Preorder.toLE.{0} (Fin i.n)
                                      (@PartialOrder.toPreorder.{0} (Fin i.n)
                                        (@LinearOrder.toPartialOrder.{0} (Fin i.n) (@Fin.instLinearOrder i.n))))
                                    (@Preorder.toLT.{0} (Fin i.n)
                                      (@PartialOrder.toPreorder.{0} (Fin i.n)
                                        (@LinearOrder.toPartialOrder.{0} (Fin i.n) (@Fin.instLinearOrder i.n))))
                                    (@instBEqOfDecidableEq.{0} (Fin i.n) (instDecidableEqFin i.n))
                                    (@Ord.compare.{0} (Fin i.n) (instOrdFin i.n))
                                    (@instLawfulBCmpCompare_mathlib.{0} (Fin i.n) (@Fin.instLinearOrder i.n)))
                                  (Fin.instLawfulEqOrd i.n))
                                v xs)
                              xs
                              (@HAppend.hAppend.{0, 0, 0} (List.{0} (Fin i.n)) (List.{0} (Fin i.n)) (List.{0} (Fin i.n))
                                (@instHAppendOfAppend.{0} (List.{0} (Fin i.n)) (@List.instAppend.{0} (Fin i.n))) xs
                                (@List.cons.{0} (Fin i.n) v (@List.nil.{0} (Fin i.n))))))
                          (And
                            (DecrAlmostLinearSSSP.Decremental.Native.AdapterMemory i B reserve N
                              (@DecrAlmostLinearSSSP.Decremental.AdapterState.mk i
                                (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i a)
                                (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i a)
                                (@Insert.insert.{0, 0} (Fin i.n) (Finset.{0} (Fin i.n))
                                  (@Finset.instInsert.{0} (Fin i.n) (instDecidableEqFin i.n)) v
                                  (@DecrAlmostLinearSSSP.Decremental.AdapterState.dirty i a))
                                (@DecrAlmostLinearSSSP.Decremental.AdapterState.output i a))
                              ys t)
                            (∀ (address : Nat),
                              Not
                                  (DecrAlmostLinearSSSP.Decremental.Native.PointerArrayCell
                                    (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                                      (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N)
                                    i.n address) →
                                And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                  (@Eq.{1} Real (t.realMem address) (s.realMem address)))))))) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B reserve N : Nat}
  {a b : DecrAlmostLinearSSSP.Decremental.AdapterState i} {xs : List.{0} (Fin i.n)}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.AdapterMemory i B reserve N a xs s →
    @Eq.{1} (Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal)
        (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i b)
        (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i a) →
      @Eq.{1} (Fin i.n → Nat) (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i b)
          (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i a) →
        @Eq.{1} (Fin i.n → ENNReal) (@DecrAlmostLinearSSSP.Decremental.AdapterState.output i b)
            (@DecrAlmostLinearSSSP.Decremental.AdapterState.output i a) →
          @LE.le.{0} (Finset.{0} (Fin i.n))
              (@Preorder.toLE.{0} (Finset.{0} (Fin i.n))
                (@PartialOrder.toPreorder.{0} (Finset.{0} (Fin i.n)) (@Finset.instPartialOrder.{0} (Fin i.n))))
              (@DecrAlmostLinearSSSP.Decremental.AdapterState.dirty i b)
              (@DecrAlmostLinearSSSP.Decremental.AdapterState.dirty i a) →
            DecrAlmostLinearSSSP.Decremental.Native.AdapterMemory i B reserve N b xs s) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (B reserve N utility : Nat),
      @LE.le.{0} Nat instLENat i.n B →
        ∀ (a : DecrAlmostLinearSSSP.Decremental.AdapterState i) (xs : List.{0} (Fin i.n))
          (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
          DecrAlmostLinearSSSP.Decremental.Native.AdapterMemory i B reserve N a xs s →
            DecrAlmostLinearSSSP.Decremental.Native.Globals i B utility s →
              (∀ (z : Fin i.n),
                  DecrAlmostLinearSSSP.Decremental.PointerValid i
                    (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i a) z
                    (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i a z)) →
                ∀ (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n)
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
                      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94))))
                          (@Fin.val i.n v) →
                        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 198) (instOfNatNat (nat_lit 198))))
                            (DecrAlmostLinearSSSP.Decremental.bankAddress B
                              (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) (@Fin.val i.n v)) →
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
                                    ∃ cost t ys,
                                      And
                                        (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                          DecrAlmostLinearSSSP.Decremental.Native.reportEvent s cost t)
                                        (And
                                          (@LE.le.{0} Nat instLENat cost
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
                                                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                                                  (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i
                                                    (DecrAlmostLinearSSSP.Decremental.adapterWrite i a j v
                                                      (DecrAlmostLinearSSSP.Decremental.stored g (@Fin.val i.n v)))
                                                    v)
                                                  (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i a v)))
                                              (@OfNat.ofNat.{0} Nat (nat_lit 44) (instOfNatNat (nat_lit 44)))))
                                          (And
                                            (DecrAlmostLinearSSSP.Decremental.Native.AdapterMemory i B reserve N
                                              (DecrAlmostLinearSSSP.Decremental.adapterWrite i a j v
                                                (DecrAlmostLinearSSSP.Decremental.stored g (@Fin.val i.n v)))
                                              ys t)
                                            (And
                                              (@Eq.{1} (List.{0} (Fin i.n)) ys
                                                (@ite.{1} (List.{0} (Fin i.n))
                                                  (@Membership.mem.{0, 0} (Fin i.n) (List.{0} (Fin i.n))
                                                    (@List.instMembership.{0} (Fin i.n)) xs v)
                                                  (@List.instDecidableMemOfLawfulBEq.{0} (Fin i.n)
                                                    (@instBEqOfDecidableEq.{0} (Fin i.n) (instDecidableEqFin i.n))
                                                    (@Std.LawfulBEqOrd.lawfulBEq.{0} (Fin i.n)
                                                      (@instBEqOfDecidableEq.{0} (Fin i.n) (instDecidableEqFin i.n))
                                                      (instOrdFin i.n)
                                                      (@Std.LawfulBCmp.toLawfulBEqCmp.{0} (Fin i.n)
                                                        (@Preorder.toLE.{0} (Fin i.n)
                                                          (@PartialOrder.toPreorder.{0} (Fin i.n)
                                                            (@LinearOrder.toPartialOrder.{0} (Fin i.n)
                                                              (@Fin.instLinearOrder i.n))))
                                                        (@Preorder.toLT.{0} (Fin i.n)
                                                          (@PartialOrder.toPreorder.{0} (Fin i.n)
                                                            (@LinearOrder.toPartialOrder.{0} (Fin i.n)
                                                              (@Fin.instLinearOrder i.n))))
                                                        (@instBEqOfDecidableEq.{0} (Fin i.n) (instDecidableEqFin i.n))
                                                        (@Ord.compare.{0} (Fin i.n) (instOrdFin i.n))
                                                        (@instLawfulBCmpCompare_mathlib.{0} (Fin i.n)
                                                          (@Fin.instLinearOrder i.n)))
                                                      (Fin.instLawfulEqOrd i.n))
                                                    v xs)
                                                  xs
                                                  (@HAppend.hAppend.{0, 0, 0} (List.{0} (Fin i.n)) (List.{0} (Fin i.n))
                                                    (List.{0} (Fin i.n))
                                                    (@instHAppendOfAppend.{0} (List.{0} (Fin i.n))
                                                      (@List.instAppend.{0} (Fin i.n)))
                                                    xs (@List.cons.{0} (Fin i.n) v (@List.nil.{0} (Fin i.n))))))
                                              (∀ (address : Nat),
                                                @Ne.{1} Nat address
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (DecrAlmostLinearSSSP.Decremental.Native.cacheAt
                                                        (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                                                            (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve
                                                            N).cache
                                                        i.n
                                                        (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j))
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                        (@Fin.val i.n v))) →
                                                  Not
                                                      (DecrAlmostLinearSSSP.Decremental.Native.PointerArrayCell
                                                        (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                                                          (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N)
                                                        i.n address) →
                                                    And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                                      (@Eq.{1} Real (t.realMem address) (s.realMem address))))))) ∧ (∀ (guest : DecrAlmostLinearSSSP.Decremental.Program) (t B bank start : Nat)
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
                    @LE.le.{0} Nat instLENat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                      (∀ (j : Nat),
                          @LT.lt.{0} Nat instLTNat j t →
                            @Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.execute guest g j).halted Bool.false →
                              ∃ ins,
                                @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                                  (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                                    Nat DecrAlmostLinearSSSP.Decremental.Instruction
                                    (fun as i =>
                                      @LT.lt.{0} Nat instLTNat i
                                        (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                                    (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                                    guest.code (DecrAlmostLinearSSSP.Decremental.execute guest g j).pc)
                                  (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins)) →
                        @Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.execute guest g t).halted Bool.true →
                          ∃ cost u,
                            And
                              (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                (DecrAlmostLinearSSSP.Decremental.observedInterpreter guest.code) s cost u)
                              (And
                                (@LE.le.{0} Nat instLENat cost
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (DecrAlmostLinearSSSP.Decremental.observedDispatchCharge guest.code)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      t)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                (And
                                  (DecrAlmostLinearSSSP.Decremental.ShadowDataRep B
                                    (DecrAlmostLinearSSSP.Decremental.bankFactor bank) u
                                    (DecrAlmostLinearSSSP.Decremental.execute guest g t))
                                  (DecrAlmostLinearSSSP.Decremental.ReportLog start
                                    (@HAppend.hAppend.{0, 0, 0} (List.{0} Nat) (List.{0} Nat) (List.{0} Nat)
                                      (@instHAppendOfAppend.{0} (List.{0} Nat) (@List.instAppend.{0} Nat)) reports
                                      (DecrAlmostLinearSSSP.Decremental.physicalTraceWrites B bank guest g t))
                                    u))))))) ∧ (((∀ (guest : DecrAlmostLinearSSSP.Decremental.Program) (B bank start : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (g final : DecrAlmostLinearSSSP.Decremental.Machine),
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
                    @LE.le.{0} Nat instLENat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                      DecrAlmostLinearSSSP.Decremental.Ends guest g final →
                        ∃ cost u t,
                          And
                            (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                              (DecrAlmostLinearSSSP.Decremental.observedInterpreter guest.code) s cost u)
                            (And
                              (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                                (DecrAlmostLinearSSSP.Decremental.execute guest g t) final)
                              (And
                                (@LE.le.{0} Nat instLENat cost
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (DecrAlmostLinearSSSP.Decremental.observedDispatchCharge guest.code)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) final.work
                                        g.work))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                (And
                                  (DecrAlmostLinearSSSP.Decremental.ShadowDataRep B
                                    (DecrAlmostLinearSSSP.Decremental.bankFactor bank) u final)
                                  (And
                                    (DecrAlmostLinearSSSP.Decremental.ReportLog start
                                      (@HAppend.hAppend.{0, 0, 0} (List.{0} Nat) (List.{0} Nat) (List.{0} Nat)
                                        (@instHAppendOfAppend.{0} (List.{0} Nat) (@List.instAppend.{0} Nat)) reports
                                        (DecrAlmostLinearSSSP.Decremental.physicalTraceWrites B bank guest g t))
                                      u)
                                    (@Eq.{1} Nat t
                                      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) final.work
                                        g.work))))))) ∧ (∀ (B bank : Nat) (guest : DecrAlmostLinearSSSP.Decremental.Program) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  (t : Nat),
  @LE.le.{0} Nat instLENat
    (@List.length.{0} Nat (DecrAlmostLinearSSSP.Decremental.physicalTraceWrites B bank guest g t)) t)) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (p : DecrAlmostLinearSSSP.Decremental.Program)
  (c : DecrAlmostLinearSSSP.Decremental.Machine) (v : Fin i.n) (a d : Nat),
  @Eq.{1} Bool c.halted Bool.false →
    @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
          DecrAlmostLinearSSSP.Decremental.Instruction
          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code c.pc)
        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
          (DecrAlmostLinearSSSP.Decremental.Instruction.store a d)) →
      @Eq.{1} Nat (c.natReg a) (@Fin.val i.n v) →
        @Eq.{1} (Option.{0} (Fin i.n)) (DecrAlmostLinearSSSP.Decremental.writtenVertex i p c)
          (@Option.some.{0} (Fin i.n) v)) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (p : DecrAlmostLinearSSSP.Decremental.Program)
  (c : DecrAlmostLinearSSSP.Decremental.Machine) (v : Fin i.n) (a d : Nat),
  @Eq.{1} Bool c.halted Bool.false →
    @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
          DecrAlmostLinearSSSP.Decremental.Instruction
          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code c.pc)
        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
          (DecrAlmostLinearSSSP.Decremental.Instruction.storeN a d)) →
      @Eq.{1} Nat (c.natReg a) (@Fin.val i.n v) →
        @Eq.{1} (Option.{0} (Fin i.n)) (DecrAlmostLinearSSSP.Decremental.writtenVertex i p c)
          (@Option.some.{0} (Fin i.n) v)) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (p : DecrAlmostLinearSSSP.Decremental.Program)
  (c : DecrAlmostLinearSSSP.Decremental.Machine),
  ∀ v ∉ @Option.toList.{0} (Fin i.n) (DecrAlmostLinearSSSP.Decremental.writtenVertex i p c),
    And
      (@Eq.{1} Real ((DecrAlmostLinearSSSP.Decremental.step p c).realMem (@Fin.val i.n v)) (c.realMem (@Fin.val i.n v)))
      (@Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.step p c).natMem (@Fin.val i.n v)) (c.natMem (@Fin.val i.n v))))))))) ∧ (((((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (p : DecrAlmostLinearSSSP.Decremental.Program)
  (c : DecrAlmostLinearSSSP.Decremental.Machine) (t : Nat),
  ∀ v ∉ DecrAlmostLinearSSSP.Decremental.observedWrites i p c t,
    And
      (@Eq.{1} Real ((DecrAlmostLinearSSSP.Decremental.execute p c t).realMem (@Fin.val i.n v))
        (c.realMem (@Fin.val i.n v)))
      (@Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.execute p c t).natMem (@Fin.val i.n v))
        (c.natMem (@Fin.val i.n v)))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (p : DecrAlmostLinearSSSP.Decremental.Program)
  (c : DecrAlmostLinearSSSP.Decremental.Machine) (t : Nat) (v : Fin i.n),
  @Ne.{1} ENNReal
      (DecrAlmostLinearSSSP.Decremental.stored (DecrAlmostLinearSSSP.Decremental.execute p c t) (@Fin.val i.n v))
      (DecrAlmostLinearSSSP.Decremental.stored c (@Fin.val i.n v)) →
    @Membership.mem.{0, 0} (Fin i.n) (List.{0} (Fin i.n)) (@List.instMembership.{0} (Fin i.n))
      (DecrAlmostLinearSSSP.Decremental.observedWrites i p c t) v)) ∧ ((∀ (B bank : Nat) (i : DecrAlmostLinearSSSP.Decremental.Input) (guest : DecrAlmostLinearSSSP.Decremental.Program)
  (g : DecrAlmostLinearSSSP.Decremental.Machine) (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
  @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
      (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
        DecrAlmostLinearSSSP.Decremental.Instruction
        (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
        (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) guest.code g.pc)
      (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins) →
    @Eq.{1} Bool g.halted Bool.false →
      ∀ (v : Fin i.n),
        @Membership.mem.{0, 0} (Fin i.n) (List.{0} (Fin i.n)) (@List.instMembership.{0} (Fin i.n))
            (@Option.toList.{0} (Fin i.n) (DecrAlmostLinearSSSP.Decremental.writtenVertex i guest g)) v →
          @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat)
            (DecrAlmostLinearSSSP.Decremental.physicalWrites B bank ins g)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val i.n v))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) ∧ (∀ (B bank : Nat) (i : DecrAlmostLinearSSSP.Decremental.Input) (guest : DecrAlmostLinearSSSP.Decremental.Program)
  (g : DecrAlmostLinearSSSP.Decremental.Machine) (t : Nat) (v : Fin i.n),
  @Membership.mem.{0, 0} (Fin i.n) (List.{0} (Fin i.n)) (@List.instMembership.{0} (Fin i.n))
      (DecrAlmostLinearSSSP.Decremental.observedWrites i guest g t) v →
    @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat)
      (DecrAlmostLinearSSSP.Decremental.physicalTraceWrites B bank guest g t)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val i.n v))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))) ∧ (((∀ (B bank : Nat) (i : DecrAlmostLinearSSSP.Decremental.Input) (guest : DecrAlmostLinearSSSP.Decremental.Program)
  (g : DecrAlmostLinearSSSP.Decremental.Machine) (t : Nat) (v : Fin i.n),
  @Ne.{1} ENNReal
      (DecrAlmostLinearSSSP.Decremental.stored (DecrAlmostLinearSSSP.Decremental.execute guest g t) (@Fin.val i.n v))
      (DecrAlmostLinearSSSP.Decremental.stored g (@Fin.val i.n v)) →
    @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat)
      (DecrAlmostLinearSSSP.Decremental.physicalTraceWrites B bank guest g t)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val i.n v))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) ∧ (∀ (B bank a : Nat),
  @Eq.{1} Real
    (DecrAlmostLinearSSSP.Decremental.reportRealIndex B bank
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@Nat.cast.{0} Real Real.instNatCast a))) ∧ ((∀ (B bank a : Nat),
  @Eq.{1} Nat
    (DecrAlmostLinearSSSP.Decremental.reportIndex B bank
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    a) ∧ ((∀ (B bank a n : Nat),
  Iff
    (@LT.lt.{0} Nat instLTNat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@LT.lt.{0} Nat instLTNat a n)) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (B bank : Nat) (v : Fin i.n),
  @Eq.{1} (Option.{0} (Fin i.n))
    (DecrAlmostLinearSSSP.Decremental.publicReport i B bank
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val i.n v))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@Option.some.{0} (Fin i.n) v)))))) ∧ ((((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (B bank : Nat) (guest : DecrAlmostLinearSSSP.Decremental.Program)
  (g : DecrAlmostLinearSSSP.Decremental.Machine) (t : Nat) (v : Fin i.n),
  @Ne.{1} ENNReal
      (DecrAlmostLinearSSSP.Decremental.stored (DecrAlmostLinearSSSP.Decremental.execute guest g t) (@Fin.val i.n v))
      (DecrAlmostLinearSSSP.Decremental.stored g (@Fin.val i.n v)) →
    @Membership.mem.{0, 0} (Fin i.n) (List.{0} (Fin i.n)) (@List.instMembership.{0} (Fin i.n))
      (DecrAlmostLinearSSSP.Decremental.publicReports i B bank
        (DecrAlmostLinearSSSP.Decremental.physicalTraceWrites B bank guest g t))
      v) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (B bank : Nat) (guest : DecrAlmostLinearSSSP.Decremental.Program)
  (g : DecrAlmostLinearSSSP.Decremental.Machine) (t : Nat),
  @LE.le.{0} Nat instLENat
    (@List.length.{0} (Fin i.n)
      (DecrAlmostLinearSSSP.Decremental.publicReports i B bank
        (DecrAlmostLinearSSSP.Decremental.physicalTraceWrites B bank guest g t)))
    t)) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (B bank a : Nat),
      @LT.lt.{0} Nat instLTNat a i.n →
        And
          (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (DecrAlmostLinearSSSP.Decremental.reportRealIndex B bank
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))
          (@LE.le.{0} Real Real.instLE
            (DecrAlmostLinearSSSP.Decremental.reportRealIndex B bank
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              (DecrAlmostLinearSSSP.Decremental.utilityDepth i.size)))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.ReportDecode.prepare s
    (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
    (DecrAlmostLinearSSSP.Decremental.ReportDecode.prepared s)) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.ReportDecode.prepared s).natReg s.natReg)))) ∧ (((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  And (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.ReportDecode.prepared s).natMem s.natMem)
    (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.ReportDecode.prepared s).realMem s.realMem)) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (B bank : Nat),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))) B →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))))
        (DecrAlmostLinearSSSP.Decremental.bankFactor bank) →
      @Eq.{1} Real
        ((DecrAlmostLinearSSSP.Decremental.ReportDecode.prepared s).realReg
          (@OfNat.ofNat.{0} Nat (nat_lit 202) (instOfNatNat (nat_lit 202))))
        (DecrAlmostLinearSSSP.Decremental.reportRealIndex B bank
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 198) (instOfNatNat (nat_lit 198))))))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (B bank a N : Nat),
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
                              (@Eq.{1} Real (t.realMem address) (s.realMem address)))))) ∧ ((∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.ReportDecode.code k) ∧ (∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 202) (instOfNatNat (nat_lit 202))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 204) (instOfNatNat (nat_lit 204))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 206) (instOfNatNat (nat_lit 206))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
              DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.ReportDecode.code k)))))))) := by
  exact ⟨⟨⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Native.initializePublic_eval,DecrAlmostLinearSSSP.Decremental.Native.PublicControlFrame.seq⟩,⟨DecrAlmostLinearSSSP.Decremental.Native.ControlFrame.asPublic,DecrAlmostLinearSSSP.Decremental.Native.publicControlFrame_pointerStart⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Native.publicControlFrame_pointerBody,DecrAlmostLinearSSSP.Decremental.Native.publicControlFrame_pointerLoop⟩,⟨DecrAlmostLinearSSSP.Decremental.Native.publicControlFrame_buildPointers,⟨DecrAlmostLinearSSSP.Decremental.Native.publicControlFrame_commit,DecrAlmostLinearSSSP.Decremental.Native.publicControlFrame_initializePublic⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Native.controlFrame_clearLast,DecrAlmostLinearSSSP.Decremental.Native.Controls.transfer⟩,⟨DecrAlmostLinearSSSP.Decremental.Native.Controls.pointerBases,DecrAlmostLinearSSSP.Decremental.Native.NormalMemory.source⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Native.NormalMemory.scanTable,DecrAlmostLinearSSSP.Decremental.Native.normalInitialize_eval⟩,⟨DecrAlmostLinearSSSP.Decremental.nat_rescale_tendsto,⟨DecrAlmostLinearSSSP.Decremental.log_rescale_ratio,DecrAlmostLinearSSSP.Decremental.subpolynomial_rescale⟩⟩⟩⟩⟩,⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.normalWrapperOverhead_subpolynomial,DecrAlmostLinearSSSP.Decremental.normal_wrapper_cost_bound⟩,⟨DecrAlmostLinearSSSP.Decremental.Native.initialization_cost_arithmetic,DecrAlmostLinearSSSP.Decremental.Native.normalInitConstant_positive⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Native.normal_initialization_uniform_cost,DecrAlmostLinearSSSP.Decremental.Native.CacheRefresh.prepare_eval⟩,⟨DecrAlmostLinearSSSP.Decremental.Native.CacheRefresh.prepare_fields,⟨DecrAlmostLinearSSSP.Decremental.Native.CacheRefresh.eval_code,DecrAlmostLinearSSSP.Decremental.Native.ScanTable.refresh⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Native.scanRows_head_from,DecrAlmostLinearSSSP.Decremental.Native.advance_scan⟩,⟨DecrAlmostLinearSSSP.Decremental.Native.PointerRefresh.prepare_eval,⟨DecrAlmostLinearSSSP.Decremental.Native.PointerRefresh.prepare_fields,DecrAlmostLinearSSSP.Decremental.Native.PointerRefresh.prepare_nat_frame⟩⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Native.PointerRefresh.eval_code,DecrAlmostLinearSSSP.Decremental.Native.PointerRefresh.nat_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.Native.PointerRefresh.real_frame,⟨DecrAlmostLinearSSSP.Decremental.DirtyMark.View.frame,DecrAlmostLinearSSSP.Decremental.Native.AdapterMemory.frame⟩⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Native.CacheRefresh.nat_frame,DecrAlmostLinearSSSP.Decremental.Native.CacheRefresh.real_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.Native.DirtyMark.nat_frame,DecrAlmostLinearSSSP.Decremental.Native.DirtyMark.real_frame⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Native.globalFrame_cacheRefresh,DecrAlmostLinearSSSP.Decremental.Native.globalFrame_pointerRefresh⟩,⟨DecrAlmostLinearSSSP.Decremental.Native.globalFrame_dirtyMark,⟨DecrAlmostLinearSSSP.Decremental.Native.adapter_cache_step,DecrAlmostLinearSSSP.Decremental.Native.adapter_pointer_step⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.DirtyMark.existing_eval,DecrAlmostLinearSSSP.Decremental.Native.adapter_mark_step⟩,⟨DecrAlmostLinearSSSP.Decremental.Native.AdapterMemory.state_transport,⟨DecrAlmostLinearSSSP.Decremental.Native.reportEvent_eval,DecrAlmostLinearSSSP.Decremental.eval_observed_interpreter⟩⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.eval_observed_interpreter_ends,DecrAlmostLinearSSSP.Decremental.physicalTraceWrites_length⟩,⟨DecrAlmostLinearSSSP.Decremental.writtenVertex_store,⟨DecrAlmostLinearSSSP.Decremental.writtenVertex_storeN,DecrAlmostLinearSSSP.Decremental.no_write_step⟩⟩⟩⟩⟩,⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.no_observed_write,DecrAlmostLinearSSSP.Decremental.stored_change_observed⟩,⟨DecrAlmostLinearSSSP.Decremental.physicalWrites_writtenVertex,DecrAlmostLinearSSSP.Decremental.physicalTraceWrites_covers⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.physicalTraceWrites_covers_change,DecrAlmostLinearSSSP.Decremental.report_real_index⟩,⟨DecrAlmostLinearSSSP.Decremental.report_index,⟨DecrAlmostLinearSSSP.Decremental.report_public_test,DecrAlmostLinearSSSP.Decremental.publicReport_encode⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.publicReports_covers_change,DecrAlmostLinearSSSP.Decremental.publicReports_length⟩,⟨DecrAlmostLinearSSSP.Decremental.public_report_decoding_bound,⟨DecrAlmostLinearSSSP.Decremental.ReportDecode.prepare_eval,DecrAlmostLinearSSSP.Decremental.ReportDecode.prepare_nat⟩⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.ReportDecode.prepare_memory,DecrAlmostLinearSSSP.Decremental.ReportDecode.prepare_value⟩,⟨DecrAlmostLinearSSSP.Decremental.ReportDecode.eval_code,⟨DecrAlmostLinearSSSP.Decremental.ReportDecode.nat_frame,DecrAlmostLinearSSSP.Decremental.ReportDecode.real_frame⟩⟩⟩⟩⟩⟩⟩
