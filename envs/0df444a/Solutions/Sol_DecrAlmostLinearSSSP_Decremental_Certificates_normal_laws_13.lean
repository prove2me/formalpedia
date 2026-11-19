-- Prove2me | solution 1 for DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_13
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T11:22:29.583177+00:00
-- url     : https://prove2.me/submissions/1e8394d0-7276-4132-96f5-adc172846256

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
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_normal_laws_6
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_normal_laws_7
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_normal_laws_8
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_normal_laws_9
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_normal_laws_10
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_normal_laws_11
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_normal_laws_12
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
open scoped ENNReal NNReal
attribute [local instance] Classical.propDecidable
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
theorem DecrAlmostLinearSSSP.Decremental.Structured.CodeAt.tail : ∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {start : Nat} {ins : DecrAlmostLinearSSSP.Decremental.Instruction}
  {rest : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction},
  DecrAlmostLinearSSSP.Decremental.Structured.CodeAt p start
      (@List.cons.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins rest) →
    DecrAlmostLinearSSSP.Decremental.Structured.CodeAt p
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      rest := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.1.2.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Structured.program_init : ∀ (init update : DecrAlmostLinearSSSP.Decremental.Structured.Cmd),
  DecrAlmostLinearSSSP.Decremental.Structured.CodeAt (DecrAlmostLinearSSSP.Decremental.Structured.program init update)
    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
    (DecrAlmostLinearSSSP.Decremental.Structured.compile init
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.1.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.Structured.program_init_halt : ∀ (init update : DecrAlmostLinearSSSP.Decremental.Structured.Cmd),
  @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
    (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
      DecrAlmostLinearSSSP.Decremental.Instruction
      (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
      (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
      (DecrAlmostLinearSSSP.Decremental.Structured.program init update).code
      (DecrAlmostLinearSSSP.Decremental.Structured.codeSize init))
    (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction DecrAlmostLinearSSSP.Decremental.Instruction.halt) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.1.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.Structured.program_update : ∀ (init update : DecrAlmostLinearSSSP.Decremental.Structured.Cmd),
  DecrAlmostLinearSSSP.Decremental.Structured.CodeAt (DecrAlmostLinearSSSP.Decremental.Structured.program init update)
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (DecrAlmostLinearSSSP.Decremental.Structured.codeSize init)
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (DecrAlmostLinearSSSP.Decremental.Structured.compile update
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (DecrAlmostLinearSSSP.Decremental.Structured.codeSize init)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.1.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.Structured.program_update_halt : ∀ (init update : DecrAlmostLinearSSSP.Decremental.Structured.Cmd),
  @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
    (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
      DecrAlmostLinearSSSP.Decremental.Instruction
      (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
      (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
      (DecrAlmostLinearSSSP.Decremental.Structured.program init update).code
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (DecrAlmostLinearSSSP.Decremental.Structured.codeSize init)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (DecrAlmostLinearSSSP.Decremental.Structured.codeSize update)))
    (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction DecrAlmostLinearSSSP.Decremental.Instruction.halt) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.1.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Structured.program_query_nine : ∀ (init update : DecrAlmostLinearSSSP.Decremental.Structured.Cmd) (c : DecrAlmostLinearSSSP.Decremental.Machine)
  (v : Nat),
  ∃ d,
    And
      (DecrAlmostLinearSSSP.Decremental.Ends (DecrAlmostLinearSSSP.Decremental.Structured.program init update)
        (have __src :=
          DecrAlmostLinearSSSP.Decremental.resume c
            (DecrAlmostLinearSSSP.Decremental.Structured.program init update).query;
        { pc := __src.pc, realReg := __src.realReg,
          natReg :=
            @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat c.natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) v,
          realMem := __src.realMem, natMem := __src.natMem, halted := __src.halted, fault := __src.fault,
          work := __src.work })
        d)
      (And
        (@LE.le.{0} Nat instLENat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d.work
            (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
            (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))))
        (And (@Eq.{1} Nat (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))) (c.natMem v))
          (And (@Eq.{1} Real (d.realReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (c.realMem v))
            (And (@Eq.{1} (Nat → Real) d.realMem c.realMem) (@Eq.{1} (Nat → Nat) d.natMem c.natMem))))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.1.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Structured.command_ends : ∀ {cmd : DecrAlmostLinearSSSP.Decremental.Structured.Cmd} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {cost : Nat},
  DecrAlmostLinearSSSP.Decremental.Structured.Eval cmd s cost t →
    ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (start : Nat) (c : DecrAlmostLinearSSSP.Decremental.Machine),
      DecrAlmostLinearSSSP.Decremental.Structured.CodeAt p start
          (DecrAlmostLinearSSSP.Decremental.Structured.compile cmd start) →
        @Eq.{1} Nat c.pc start →
          @Eq.{1} DecrAlmostLinearSSSP.Decremental.Structured.Data (DecrAlmostLinearSSSP.Decremental.Structured.data c)
              s →
            @Eq.{1} Bool c.halted Bool.false →
              @Eq.{1} Bool c.fault Bool.false →
                @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                    (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                      DecrAlmostLinearSSSP.Decremental.Instruction
                      (fun as i =>
                        @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                      (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start
                        (DecrAlmostLinearSSSP.Decremental.Structured.codeSize cmd)))
                    (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                      DecrAlmostLinearSSSP.Decremental.Instruction.halt) →
                  ∃ d,
                    And (DecrAlmostLinearSSSP.Decremental.Ends p c d)
                      (And
                        (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Structured.Data
                          (DecrAlmostLinearSSSP.Decremental.Structured.data d) t)
                        (@Eq.{1} Nat d.work
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work cost)
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.1.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.Structured.eval_natural : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (d q : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.natural d q) s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    { realReg := s.realReg, natReg := @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natReg d q,
      realMem := s.realMem, natMem := s.natMem } := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.1.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Structured.Eval.deterministic : ∀ {cmd : DecrAlmostLinearSSSP.Decremental.Structured.Cmd} {s t u : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {a b : Nat},
  DecrAlmostLinearSSSP.Decremental.Structured.Eval cmd s a t →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval cmd s b u →
      And (@Eq.{1} Nat a b) (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Structured.Data t u) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_3.1.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.input_vertex_positive : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) i.n := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.1.1.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.log_size_positive : ∀ (m : Nat),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
    (Real.log
      (@Nat.cast.{0} Real Real.instNatCast
        (@Max.max.{0} Nat Nat.instMax (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.1.2.1.2.1.2
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
theorem DecrAlmostLinearSSSP.Decremental.InputCapture.raw_initial : ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (i : DecrAlmostLinearSSSP.Decremental.Input),
  DecrAlmostLinearSSSP.Decremental.InputCapture.RawInput i
    (DecrAlmostLinearSSSP.Decremental.Structured.data (DecrAlmostLinearSSSP.Decremental.initialMachine p i)) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_8.1.2.2.2.1.1
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
theorem DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.program_update : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (deleted : List.{0} (Fin i.k)) (c : DecrAlmostLinearSSSP.Decremental.Machine),
      DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Ready i deleted
          (DecrAlmostLinearSSSP.Decremental.Structured.data c) →
        ∀ (e : Fin i.k),
          ∃ cost d,
            And
              (DecrAlmostLinearSSSP.Decremental.Ends DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.hostProgram
                (DecrAlmostLinearSSSP.Decremental.deletionMachine
                  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.hostProgram c (@Fin.val i.k e))
                d)
              (And
                (@Eq.{1} Nat d.work
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work cost)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (And
                  (@LE.le.{0} Nat instLENat cost
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 602) (instOfNatNat (nat_lit 602)))
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n i.k)
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                  (And
                    (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Ready i
                      (@HAppend.hAppend.{0, 0, 0} (List.{0} (Fin i.k)) (List.{0} (Fin i.k)) (List.{0} (Fin i.k))
                        (@instHAppendOfAppend.{0} (List.{0} (Fin i.k)) (@List.instAppend.{0} (Fin i.k))) deleted
                        (@List.cons.{0} (Fin i.k) e (@List.nil.{0} (Fin i.k))))
                      (DecrAlmostLinearSSSP.Decremental.Structured.data d))
                    (∃ q,
                      And
                        (@DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State.memory i
                          (@HAppend.hAppend.{0, 0, 0} (List.{0} (Fin i.k)) (List.{0} (Fin i.k)) (List.{0} (Fin i.k))
                            (@instHAppendOfAppend.{0} (List.{0} (Fin i.k)) (@List.instAppend.{0} (Fin i.k))) deleted
                            (@List.cons.{0} (Fin i.k) e (@List.nil.{0} (Fin i.k))))
                          q (DecrAlmostLinearSSSP.Decremental.Structured.data d))
                        (@Eq.{1} (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n)))
                          (@DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.State.queue i
                            (@HAppend.hAppend.{0, 0, 0} (List.{0} (Fin i.k)) (List.{0} (Fin i.k)) (List.{0} (Fin i.k))
                              (@instHAppendOfAppend.{0} (List.{0} (Fin i.k)) (@List.instAppend.{0} (Fin i.k))) deleted
                              (@List.cons.{0} (Fin i.k) e (@List.nil.{0} (Fin i.k))))
                            q)
                          (@OfNat.ofNat.{0} (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))) (nat_lit 0)
                            (@Zero.toOfNat0.{0} (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n)))
                              (@Multiset.instZero.{0} (Prod.{0, 0} Nat (Fin i.n)))))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_8.2.1.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Completed.good : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input},
  i.Valid →
    ∀ {deleted : List.{0} (Fin i.k)} {c : DecrAlmostLinearSSSP.Decremental.Machine},
      DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Completed i deleted c →
        DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Good i deleted c := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_8.2.2.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.live_take_subset : ∀ {k : Nat} (ds : List.{0} (Fin k)) (j : Nat),
  @LE.le.{0} (Finset.{0} (Fin k))
    (@Preorder.toLE.{0} (Finset.{0} (Fin k))
      (@PartialOrder.toPreorder.{0} (Finset.{0} (Fin k)) (@Finset.instPartialOrder.{0} (Fin k))))
    (@DecrAlmostLinearSSSP.Decremental.live k ds)
    (@DecrAlmostLinearSSSP.Decremental.live k (@List.take.{0} (Fin k) j ds)) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_8.2.2.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.OnlineRun.initial_execution : ∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {i : DecrAlmostLinearSSSP.Decremental.Input} {ds : List.{0} (Fin i.k)}
  {cs : List.{0} DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.OnlineRun p i ds cs →
    ∃ c,
      And
        (@Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Machine)
          (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Machine) Nat
            DecrAlmostLinearSSSP.Decremental.Machine
            (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Machine as))
            (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Machine) cs
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Machine c))
        (DecrAlmostLinearSSSP.Decremental.Ends p (DecrAlmostLinearSSSP.Decremental.initialMachine p i) c) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_8.2.2.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.Ends.deterministic : ∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {c d e : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.Ends p c d →
    DecrAlmostLinearSSSP.Decremental.Ends p c e → @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine d e := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_8.2.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.OnlineRun.length : ∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {i : DecrAlmostLinearSSSP.Decremental.Input} {ds : List.{0} (Fin i.k)}
  {cs : List.{0} DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.OnlineRun p i ds cs →
    @Eq.{1} Nat (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Machine cs)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_8.2.2.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.OnlineRun.transition_at : ∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {i : DecrAlmostLinearSSSP.Decremental.Input} {ds : List.{0} (Fin i.k)}
  {cs : List.{0} DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.OnlineRun p i ds cs →
    ∀ (k : Nat) (hk : @LT.lt.{0} Nat instLTNat k (@List.length.{0} (Fin i.k) ds)),
      ∃ c d,
        And
          (@Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Machine)
            (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Machine) Nat
              DecrAlmostLinearSSSP.Decremental.Machine
              (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Machine as))
              (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Machine) cs k)
            (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Machine c))
          (And
            (@Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Machine)
              (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Machine) Nat
                DecrAlmostLinearSSSP.Decremental.Machine
                (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Machine as))
                (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Machine) cs
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Machine d))
            (DecrAlmostLinearSSSP.Decremental.Ends p
              (DecrAlmostLinearSSSP.Decremental.deletionMachine p c
                (@Fin.val i.k
                  (@GetElem.getElem.{0, 0, 0} (List.{0} (Fin i.k)) Nat (Fin i.k)
                    (fun as i_1 => @LT.lt.{0} Nat instLTNat i_1 (@List.length.{0} (Fin i.k) as))
                    (@List.instGetElemNatLtLength.{0} (Fin i.k)) ds k hk)))
              d)) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_8.2.2.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.Ends.work_mono : ∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {c d : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.Ends p c d → @LE.le.{0} Nat instLENat c.work d.work := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_8.2.2.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.OnlineRun.work_le_last : ∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {i : DecrAlmostLinearSSSP.Decremental.Input} {ds : List.{0} (Fin i.k)}
  {cs : List.{0} DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.OnlineRun p i ds cs →
    ∀ (last : DecrAlmostLinearSSSP.Decremental.Machine),
      @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Machine)
          (@List.getLast?.{0} DecrAlmostLinearSSSP.Decremental.Machine cs)
          (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Machine last) →
        ∀ (c : DecrAlmostLinearSSSP.Decremental.Machine),
          @Membership.mem.{0, 0} DecrAlmostLinearSSSP.Decremental.Machine
              (List.{0} DecrAlmostLinearSSSP.Decremental.Machine)
              (@List.instMembership.{0} DecrAlmostLinearSSSP.Decremental.Machine) cs c →
            @LE.le.{0} Nat instLENat c.work last.work := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_8.2.2.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.PreservesOutside.trans : ∀ {base F : Nat} {c d e : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.PreservesOutside base F c d →
    DecrAlmostLinearSSSP.Decremental.PreservesOutside base F d e →
      DecrAlmostLinearSSSP.Decremental.PreservesOutside base F c e := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_2.1.1.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.registerBound_ge : ∀ (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
    (DecrAlmostLinearSSSP.Decremental.registerBound code) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_3.2.2.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail.execute : ∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {c : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail (DecrAlmostLinearSSSP.Decremental.registerBound p.code) c →
    ∀ (t : Nat),
      DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail (DecrAlmostLinearSSSP.Decremental.registerBound p.code)
        (DecrAlmostLinearSSSP.Decremental.execute p c t) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_3.2.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail.ends : ∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {c d : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail (DecrAlmostLinearSSSP.Decremental.registerBound p.code) c →
    DecrAlmostLinearSSSP.Decremental.Ends p c d →
      DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail (DecrAlmostLinearSSSP.Decremental.registerBound p.code) d := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_3.2.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.OnlineRun.zero_register_tail : ∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {i : DecrAlmostLinearSSSP.Decremental.Input} {ds : List.{0} (Fin i.k)}
  {cs : List.{0} DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.OnlineRun p i ds cs →
    ∀ (c : DecrAlmostLinearSSSP.Decremental.Machine),
      @Membership.mem.{0, 0} DecrAlmostLinearSSSP.Decremental.Machine
          (List.{0} DecrAlmostLinearSSSP.Decremental.Machine)
          (@List.instMembership.{0} DecrAlmostLinearSSSP.Decremental.Machine) cs c →
        DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail (DecrAlmostLinearSSSP.Decremental.registerBound p.code) c := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_3.2.2.2.1.1.2
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
theorem DecrAlmostLinearSSSP.Decremental.Native.Globals.transfer : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B utility cost : Nat}
  {cmd : DecrAlmostLinearSSSP.Decremental.Structured.Cmd} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.Globals i B utility s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval cmd s cost t →
      DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame cmd →
        DecrAlmostLinearSSSP.Decremental.Native.Globals i B utility t := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_5.2.2.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Native.BankEnv.transfer : ∀ {j record cache stride cost : Nat} {cmd : DecrAlmostLinearSSSP.Decremental.Structured.Cmd}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.BankEnv j record cache stride s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval cmd s cost t →
      DecrAlmostLinearSSSP.Decremental.Native.BankFrame cmd →
        DecrAlmostLinearSSSP.Decremental.Native.BankEnv j record cache stride t := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_6.1.1.2.2.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.Native.ScaleMemory.same_memory : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program}
  {B j record cache next : Nat} {g : DecrAlmostLinearSSSP.Decremental.Machine} {b : Fin i.n → ENNReal}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.ScaleMemory i p B j record cache next g b s →
    @Eq.{1} (Nat → Nat) t.natMem s.natMem →
      @Eq.{1} (Nat → Real) t.realMem s.realMem →
        DecrAlmostLinearSSSP.Decremental.Native.ScaleMemory i p B j record cache next g b t := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_7.1.2.1.1.2.2
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
theorem DecrAlmostLinearSSSP.Decremental.adapterInitialize_pointer_valid : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input)
  (b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal) (v : Fin i.n),
  DecrAlmostLinearSSSP.Decremental.PointerValid i b v
    (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i (DecrAlmostLinearSSSP.Decremental.adapterInitialize i b)
      v) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_8.1.1.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.Native.PublicFrame.trans : ∀ {l : DecrAlmostLinearSSSP.Decremental.Native.PointerLayout} {n : Nat}
  {s t u : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.PublicFrame l n s t →
    DecrAlmostLinearSSSP.Decremental.Native.PublicFrame l n t u →
      DecrAlmostLinearSSSP.Decremental.Native.PublicFrame l n s u := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_8.2.2.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.PointerBases.start : ∀ {record pointer flags list cost : Nat} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.PointerBases record pointer flags list s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Native.pointerStart s cost t →
      DecrAlmostLinearSSSP.Decremental.Native.PointerBases record pointer flags list t := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_9.1.1.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.SelectedRead.normalized : ∀ {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {cost : Nat},
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.SelectedRead.code s cost t →
      @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.SelectedRead.flag s)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
        (@Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.SelectedRead.flag s)
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
            @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              (DecrAlmostLinearSSSP.Decremental.SelectedRead.realValue s)) →
          And
            (@LE.le.{0} Nat instLENat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))))
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
              @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                (t.realReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_9.1.1.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.AnswerTable.Image.frame : ∀ {n : Nat} {l : DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout n}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  @DecrAlmostLinearSSSP.Decremental.AnswerTable.Image n l s →
    (∀ (address : Nat),
        @DecrAlmostLinearSSSP.Decremental.AnswerTable.Protected n l address →
          And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
            (@Eq.{1} Real (t.realMem address) (s.realMem address))) →
      @DecrAlmostLinearSSSP.Decremental.AnswerTable.Image n l t := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_9.1.2.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.AnswerTable.Image.same_memory : ∀ {n : Nat} {l : DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout n}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  @DecrAlmostLinearSSSP.Decremental.AnswerTable.Image n l s →
    @Eq.{1} (Nat → Nat) t.natMem s.natMem →
      @Eq.{1} (Nat → Real) t.realMem s.realMem → @DecrAlmostLinearSSSP.Decremental.AnswerTable.Image n l t := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_9.1.2.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.AnswerTable.normalized : ∀ {n : Nat} (l : DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout n),
  (∀ (v : Fin n),
      @LE.le.{0} Nat instLENat (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.cacheFlag n l v)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
    (∀ (v : Fin n),
        @Eq.{1} Nat (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.cacheFlag n l v)
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
          @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.cacheReal n l v)) →
      ∀ (v : Fin n),
        And
          (@LE.le.{0} Nat instLENat (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.flag n l v)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@Eq.{1} Nat (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.flag n l v)
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
            @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.realValue n l v)) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_9.1.2.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.barrier_cache_selected_accuracy : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ {ι : Type} (S : Finset.{0} ι) (past : ι → Finset.{0} (Fin i.k)) (current : Finset.{0} (Fin i.k)),
      (∀ (t : ι),
          @Membership.mem.{0, 0} ι (Finset.{0} ι)
              (@SetLike.instMembership.{0, 0} (Finset.{0} ι) ι (@Finset.instSetLike.{0} ι)) S t →
            @LE.le.{0} (Finset.{0} (Fin i.k))
              (@Preorder.toLE.{0} (Finset.{0} (Fin i.k))
                (@PartialOrder.toPreorder.{0} (Finset.{0} (Fin i.k)) (@Finset.instPartialOrder.{0} (Fin i.k))))
              current (past t)) →
        ∀ (B : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → ι → Fin i.n → ENNReal)
          (cache : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal),
          (∀ (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n),
              @LE.le.{0} ENNReal ENNReal.instLE
                (@DecrAlmostLinearSSSP.Decremental.distance
                  (DecrAlmostLinearSSSP.Decremental.barrierInput i
                      (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)).n
                  (DecrAlmostLinearSSSP.Decremental.barrierInput i
                      (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)).k
                  (DecrAlmostLinearSSSP.Decremental.barrierInput i
                      (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)).graph
                  current
                  (fun e =>
                    @Nat.cast.{0} ENNReal
                      (@AddMonoidWithOne.toNatCast.{0} ENNReal
                        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                      ((DecrAlmostLinearSSSP.Decremental.barrierInput i
                            (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)).weight
                        e))
                  i.source v)
                (cache j v)) →
            (∀ (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n),
                @LE.le.{0} ENNReal ENNReal.instLE (cache j v)
                  (@Finset.sup.{0, 0} ENNReal ι ENNReal.instSemilatticeSup ENNReal.instOrderBot S fun t => B j t v)) →
              (∀ (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (t : ι),
                  @Membership.mem.{0, 0} ι (Finset.{0} ι)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} ι) ι (@Finset.instSetLike.{0} ι)) S t →
                    ∀ (v : Fin i.n),
                      @LE.le.{0} ENNReal ENNReal.instLE (B j t v)
                        (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                          (@instHMul.{0} ENNReal
                            (@Distrib.toMul.{0} ENNReal
                              (@instDistribOfSemiring.{0} ENNReal
                                (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                          (ENNReal.ofReal
                            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) i.accuracy
                                (@OfNat.ofNat.{0} Real (nat_lit 16)
                                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                                    (@Nat.instAtLeastTwoHAddOfNat
                                      (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                                      (@Nat.instNeZeroSucc
                                        (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))))))))
                          (@DecrAlmostLinearSSSP.Decremental.distance
                            (DecrAlmostLinearSSSP.Decremental.barrierInput i
                                (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)).n
                            (DecrAlmostLinearSSSP.Decremental.barrierInput i
                                (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)).k
                            (DecrAlmostLinearSSSP.Decremental.barrierInput i
                                (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)).graph
                            (past t)
                            (fun e =>
                              @Nat.cast.{0} ENNReal
                                (@AddMonoidWithOne.toNatCast.{0} ENNReal
                                  (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal
                                    ENNReal.instAddCommMonoidWithOne))
                                ((DecrAlmostLinearSSSP.Decremental.barrierInput i
                                      (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)).weight
                                  e))
                            i.source v))) →
                ∀ (p : Fin i.n → Nat),
                  (∀ (v : Fin i.n), DecrAlmostLinearSSSP.Decremental.PointerValid i cache v (p v)) →
                    ∀ (v : Fin i.n),
                      And
                        (@LE.le.{0} ENNReal ENNReal.instLE
                          (@DecrAlmostLinearSSSP.Decremental.distance i.n i.k i.graph current
                            (fun e =>
                              @Nat.cast.{0} ENNReal
                                (@AddMonoidWithOne.toNatCast.{0} ENNReal
                                  (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal
                                    ENNReal.instAddCommMonoidWithOne))
                                (i.weight e))
                            i.source v)
                          (DecrAlmostLinearSSSP.Decremental.selected i cache p v))
                        (And
                          (@LE.le.{0} ENNReal ENNReal.instLE (DecrAlmostLinearSSSP.Decremental.selected i cache p v)
                            (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                              (@instHMul.{0} ENNReal
                                (@Distrib.toMul.{0} ENNReal
                                  (@instDistribOfSemiring.{0} ENNReal
                                    (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                              (ENNReal.ofReal
                                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) i.accuracy))
                              (@DecrAlmostLinearSSSP.Decremental.distance i.n i.k i.graph current
                                (fun e =>
                                  @Nat.cast.{0} ENNReal
                                    (@AddMonoidWithOne.toNatCast.{0} ENNReal
                                      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal
                                        ENNReal.instAddCommMonoidWithOne))
                                    (i.weight e))
                                i.source v)))
                          (Iff
                            (@Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.selected i cache p v)
                              (@Top.top.{0} ENNReal ENNReal.instTop))
                            (Not (@DecrAlmostLinearSSSP.Decremental.Reachable i.n i.k i.graph current i.source v)))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_9.2.2.2.2.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.Native.normalInitialize_eval : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
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
                                              i.source v))))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_10.1.1.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.normal_wrapper_cost_bound : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
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
                      (DecrAlmostLinearSSSP.Decremental.logarithm2 (@Nat.cast.{0} Real Real.instNatCast i.W)))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_10.1.2.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Native.normal_initialization_uniform_cost : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input},
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
                          (DecrAlmostLinearSSSP.Decremental.logarithm2 (@Nat.cast.{0} Real Real.instNatCast i.W)))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_10.1.2.1.2.1.1
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
theorem DecrAlmostLinearSSSP.Decremental.pointer_energy_bound : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (s : DecrAlmostLinearSSSP.Decremental.AdapterState i),
  (∀ (v : Fin i.n),
      DecrAlmostLinearSSSP.Decremental.PointerValid i (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i s) v
        (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i s v)) →
    @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.pointerEnergy i s)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) i.n
        (DecrAlmostLinearSSSP.Decremental.scaleCount i)) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_11.1.2.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.adapterTrace_pointer_valid : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (s : DecrAlmostLinearSSSP.Decremental.AdapterState i)
  (events : List.{0} (DecrAlmostLinearSSSP.Decremental.AdapterEvent i)),
  (∀ (v : Fin i.n),
      DecrAlmostLinearSSSP.Decremental.PointerValid i (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i s) v
        (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i s v)) →
    ∀ (v : Fin i.n),
      DecrAlmostLinearSSSP.Decremental.PointerValid i
        (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i
          (DecrAlmostLinearSSSP.Decremental.adapterTrace i s events))
        v
        (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i
          (DecrAlmostLinearSSSP.Decremental.adapterTrace i s events) v) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_11.1.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.adapterTrace_maxima_mono : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (s : DecrAlmostLinearSSSP.Decremental.AdapterState i)
  (events : List.{0} (DecrAlmostLinearSSSP.Decremental.AdapterEvent i))
  (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n),
  @LE.le.{0} ENNReal ENNReal.instLE (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i s j v)
    (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i (DecrAlmostLinearSSSP.Decremental.adapterTrace i s events)
      j v) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_11.1.2.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.adapterTrace_append : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (a : DecrAlmostLinearSSSP.Decremental.AdapterState i)
  (xs ys : List.{0} (DecrAlmostLinearSSSP.Decremental.AdapterEvent i)),
  @Eq.{1} (DecrAlmostLinearSSSP.Decremental.AdapterState i)
    (DecrAlmostLinearSSSP.Decremental.adapterTrace i a
      (@HAppend.hAppend.{0, 0, 0} (List.{0} (DecrAlmostLinearSSSP.Decremental.AdapterEvent i))
        (List.{0} (DecrAlmostLinearSSSP.Decremental.AdapterEvent i))
        (List.{0} (DecrAlmostLinearSSSP.Decremental.AdapterEvent i))
        (@instHAppendOfAppend.{0} (List.{0} (DecrAlmostLinearSSSP.Decremental.AdapterEvent i))
          (@List.instAppend.{0} (DecrAlmostLinearSSSP.Decremental.AdapterEvent i)))
        xs ys))
    (DecrAlmostLinearSSSP.Decremental.adapterTrace i (DecrAlmostLinearSSSP.Decremental.adapterTrace i a xs) ys) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_11.1.2.2.1.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.Environment.transfer : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B reserve N cost : Nat}
  {j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)} {g : DecrAlmostLinearSSSP.Decremental.Machine}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.Environment i B reserve N j g s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.body s cost
        t →
      DecrAlmostLinearSSSP.Decremental.Native.ReportFrame i B reserve N
          (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) s t →
        DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.Environment i B reserve N j g t := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_11.2.1.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.allEvents_public : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (B : Nat) (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i))
  (g : DecrAlmostLinearSSSP.Decremental.Machine) (reports : List.{0} Nat),
  @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.AdapterEvent i))
    (DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.allEvents i B j g reports)
    (@List.map.{0, 0} (Fin i.n)
      (Prod.{0, 0} (Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (Prod.{0, 0} (Fin i.n) ENNReal))
      (fun v =>
        @Prod.mk.{0, 0} (Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (Prod.{0, 0} (Fin i.n) ENNReal) j
          (@Prod.mk.{0, 0} (Fin i.n) ENNReal v (DecrAlmostLinearSSSP.Decremental.stored g (@Fin.val i.n v))))
      (DecrAlmostLinearSSSP.Decremental.publicReports i B (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)
        reports)) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_11.2.1.1.2.1.2
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
theorem DecrAlmostLinearSSSP.Decremental.consumed_physical_reports_dominate : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (s : DecrAlmostLinearSSSP.Decremental.AdapterState i)
  (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (B bank : Nat)
  (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (t : Nat),
  (∀ (v : Fin i.n),
      @LE.le.{0} ENNReal ENNReal.instLE (DecrAlmostLinearSSSP.Decremental.stored c (@Fin.val i.n v))
        (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i s j v)) →
    ∀ (v : Fin i.n),
      @LE.le.{0} ENNReal ENNReal.instLE
        (DecrAlmostLinearSSSP.Decremental.stored (DecrAlmostLinearSSSP.Decremental.execute p c t) (@Fin.val i.n v))
        (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i
          (DecrAlmostLinearSSSP.Decremental.adapterTrace i s
            (@List.map.{0, 0} (Fin i.n) (DecrAlmostLinearSSSP.Decremental.AdapterEvent i)
              (fun v =>
                @Prod.mk.{0, 0} (Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (Prod.{0, 0} (Fin i.n) ENNReal) j
                  (@Prod.mk.{0, 0} (Fin i.n) ENNReal v
                    (DecrAlmostLinearSSSP.Decremental.stored (DecrAlmostLinearSSSP.Decremental.execute p c t)
                      (@Fin.val i.n v))))
              (DecrAlmostLinearSSSP.Decremental.publicReports i B bank
                (DecrAlmostLinearSSSP.Decremental.physicalTraceWrites B bank p c t))))
          j v) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_12.1.2.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.Native.FamilyMemory.same_memory : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program} {B reserve : Nat}
  {f : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → DecrAlmostLinearSSSP.Decremental.Machine}
  {a : DecrAlmostLinearSSSP.Decremental.AdapterState i} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.FamilyMemory i p B reserve f a s →
    @Eq.{1} (Nat → Nat) t.natMem s.natMem →
      @Eq.{1} (Nat → Real) t.realMem s.realMem →
        DecrAlmostLinearSSSP.Decremental.Native.FamilyMemory i p B reserve f a t := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_12.2.1.1.1.1.2
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
theorem DecrAlmostLinearSSSP.Decremental.Native.updateWorkPrefix_ge : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (p : DecrAlmostLinearSSSP.Decremental.Program) (e : Fin i.k)
  (before after : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → DecrAlmostLinearSSSP.Decremental.Machine),
  (∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
      DecrAlmostLinearSSSP.Decremental.Ends p
        (DecrAlmostLinearSSSP.Decremental.deletionMachine p (before q) (@Fin.val i.k e)) (after q)) →
    ∀ (d : Nat),
      @LE.le.{0} Nat instLENat d (DecrAlmostLinearSSSP.Decremental.scaleCount i) →
        @LE.le.{0} Nat instLENat d (DecrAlmostLinearSSSP.Decremental.Native.updateWorkPrefix i before after d) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_12.2.2.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.Native.updateWorkPrefix_eq_sum : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input)
  (before after : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → DecrAlmostLinearSSSP.Decremental.Machine),
  @Eq.{1} Nat
    (DecrAlmostLinearSSSP.Decremental.Native.updateWorkPrefix i before after
      (DecrAlmostLinearSSSP.Decremental.scaleCount i))
    (∑ q, @HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (after q).work (before q).work) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_12.2.2.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Native.normalUpdate_eval : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (B reserve : Nat),
      @LE.le.{0} Nat instLENat i.n B →
        ∀ (e : Fin i.k)
          (before after :
            Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → DecrAlmostLinearSSSP.Decremental.Machine)
          (b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal) (ptr : Fin i.n → Nat)
          (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
          DecrAlmostLinearSSSP.Decremental.Native.NormalMemory i p B reserve before b ptr s →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) (@Fin.val i.k e) →
              (∀ (v : Fin i.n), DecrAlmostLinearSSSP.Decremental.PointerValid i b v (ptr v)) →
                (∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
                    DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail
                      (DecrAlmostLinearSSSP.Decremental.registerBound p.code) (before q)) →
                  (∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
                      DecrAlmostLinearSSSP.Decremental.Ends p
                        (DecrAlmostLinearSSSP.Decremental.deletionMachine p (before q) (@Fin.val i.k e)) (after q)) →
                    (∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
                        @LE.le.{0} Nat instLENat (after q).work reserve) →
                      (∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n),
                          And
                            (@LE.le.{0} Nat instLENat ((after q).natMem (@Fin.val i.n v))
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                            (@Eq.{1} Nat ((after q).natMem (@Fin.val i.n v))
                                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                              @LE.le.{0} Real Real.instLE
                                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                ((after q).realMem (@Fin.val i.n v)))) →
                        have initial := DecrAlmostLinearSSSP.Decremental.Native.boundaryAdapter i b ptr;
                        have final :=
                          DecrAlmostLinearSSSP.Decremental.adapterTrace i initial
                            (DecrAlmostLinearSSSP.Decremental.Native.updateEventsPrefix i p B e before after
                              (DecrAlmostLinearSSSP.Decremental.scaleCount i));
                        ∃ cost t,
                          And
                            (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                              (DecrAlmostLinearSSSP.Decremental.Native.normalUpdate p) s cost t)
                            (And
                              (DecrAlmostLinearSSSP.Decremental.Native.NormalMemory i p B reserve after
                                (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i final)
                                (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i final) t)
                              (@LE.le.{0} Nat instLENat
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cost
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
                                    (DecrAlmostLinearSSSP.Decremental.pointerEnergy i initial)))
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (DecrAlmostLinearSSSP.Decremental.Native.scaleUpdateCharge p i.size)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 36) (instOfNatNat (nat_lit 36))))
                                    (DecrAlmostLinearSSSP.Decremental.Native.updateWorkPrefix i before after
                                      (DecrAlmostLinearSSSP.Decremental.scaleCount i)))
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
                                    (DecrAlmostLinearSSSP.Decremental.pointerEnergy i final))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_12.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.globalFrame_external : ∀ (e : Nat),
  DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame
    (DecrAlmostLinearSSSP.Decremental.Structured.natural (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
      e) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_12.2.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.publicControlFrame_external : ∀ (e : Nat),
  DecrAlmostLinearSSSP.Decremental.Native.PublicControlFrame
    (DecrAlmostLinearSSSP.Decremental.Structured.natural (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
      e) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_12.2.2.2.2.2.2.2
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
lemma NormalMemory.external_input {i : Input} {p : Program} {B reserve : ℕ}
    {f : Fin (scaleCount i) → Machine} {b : Fin (scaleCount i) → Fin i.n → ℝ≥0∞}
    {ptr : Fin i.n → ℕ} {s : Data} (h : NormalMemory i p B reserve f b ptr s) (e : ℕ) :
    NormalMemory i p B reserve f b ptr (externalInput s e) := by
  have he : Eval (natural 5 e) s 1 (externalInput s e) := eval_natural s 5 e
  constructor
  · exact h.globals.transfer he (globalFrame_external e)
  · exact h.controls.transfer he (publicControlFrame_external e)
  · intro q;exact (h.scales q).same_memory rfl rfl
  · exact h.pointers
  · exact h.dirty.frame (fun _ => rfl) (fun _ _ => rfl) (by simp [externalInput]) (by simp [externalInput])
  · exact h.normalized
  · exact h.output
  · intro r hr
    have hh := h.tail r hr
    have hne : shadowReg r ≠ 5 := by unfold shadowReg;omega
    simpa only [externalInput,Function.update_of_ne hne] using hh
lemma data_deletion (host : Program) (c : Machine) (e : ℕ) :
    data (deletionMachine host c e) = externalInput (data c) e := rfl
end DecrAlmostLinearSSSP.Decremental.Native
end s291
section s292
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
lemma normalProgram_initialization (i : Input) (hi : i.Valid) (hn : 2 ≤ i.n) (heps : 1/(i.size : ℝ) < i.accuracy)
    (p : Program) (C : ℝ) (a : ℕ → ℝ) (queryBound coefficient : ℕ)
    (hpoly : ∀ x : Input, x.Valid → 2 ≤ x.n → x.W ≤ x.size^2 →
      1/(x.size : ℝ) < x.accuracy → x.accuracy < 1 → Maintains p C a queryBound false x) :
    ∃ (f : Fin (scaleCount i) → Machine) (cost : ℕ) (c : Machine), (∀ q, InitialFacts p C a i q.val (f q)) ∧
      Ends (normalProgram coefficient p) (initialMachine (normalProgram coefficient p) i) c ∧
      c.work = cost+1 ∧
      cost ≤ setupCost i coefficient (registerBound p.code)+
        ((dispatchCharge p.code+2)*maxInitialWork f+initOverhead i p+7)*scaleCount i+(13*scaleCount i+48)*i.n+22 ∧
      NormalMemory i p (i.n+3*i.k+2) (coefficient*i.size^3+1) f (fun q v => stored (f q) v.val)
        (initialPointers i (fun q v => stored (f q) v.val)) (data c) ∧
      (∀ v : Fin i.n, i.dist [] v ≤ stored c v.val ∧ stored c v.val ≤ ENNReal.ofReal (1+i.accuracy)*i.dist [] v ∧
        (stored c v.val = ⊤ ↔ ¬Reachable i.graph (live []) i.source v)) := by
  let host := normalProgram coefficient p
  let c0 := initialMachine host i
  let s := data c0
  have htail : ∀ r, registerBound p.code ≤ r → s.natReg (shadowReg r) = 0 ∧ s.realReg (shadowReg r) = 0 := by
    intro r hr
    have hN := registerBound_ge p.code
    have hshadow : 4 < shadowReg r := by unfold shadowReg;omega
    simp [s,c0,data,initialMachine,show shadowReg r ≠ 0 by omega,show shadowReg r ≠ 1 by omega,
      show shadowReg r ≠ 2 by omega,show shadowReg r ≠ 3 by omega,show shadowReg r ≠ 4 by omega]
  obtain ⟨f,cost,t,hf,he,hcost,htmem,_,htaccuracy⟩ := normalInitialize_eval i hi hn heps p C a queryBound coefficient hpoly s
    (InputCapture.raw_initial host i) rfl rfl htail
  obtain ⟨c,hend,hdata,hwork⟩ := command_ends he host 0 c0 (program_init _ _) rfl rfl rfl rfl (by simpa only [host,normalProgram,Nat.zero_add] using program_init_halt (normalInitialize coefficient p) (normalUpdate p))
  have hmem : NormalMemory i p (i.n+3*i.k+2) (coefficient*i.size^3+1) f (fun q v => stored (f q) v.val)
      (initialPointers i (fun q v => stored (f q) v.val)) (data c) := by rw [hdata];exact htmem
  have haccuracy : ∀ v : Fin i.n, i.dist [] v ≤ stored c v.val ∧ stored c v.val ≤ ENNReal.ofReal (1+i.accuracy)*i.dist [] v ∧
      (stored c v.val = ⊤ ↔ ¬Reachable i.graph (live []) i.source v) := by
    intro v
    have hstored : stored c v.val = stored t.machine v.val := by change stored (data c).machine v.val = _;rw [hdata]
    rw [hstored];exact htaccuracy v
  exact ⟨f,cost,c,hf,hend,by simpa only [c0,initialMachine,Nat.zero_add] using hwork,hcost,hmem,haccuracy⟩
lemma normalProgram_update (i : Input) (hi : i.Valid) (p : Program) (coefficient B reserve : ℕ) (hB : i.n ≤ B)
    (e : Fin i.k) (before after : Fin (scaleCount i) → Machine)
    (b : Fin (scaleCount i) → Fin i.n → ℝ≥0∞) (ptr : Fin i.n → ℕ) (c : Machine)
    (h : NormalMemory i p B reserve before b ptr (data c)) (hp : ∀ v, PointerValid i b v (ptr v))
    (hbeforeTail : ∀ q, ZeroRegisterTail (registerBound p.code) (before q))
    (hends : ∀ q, Ends p (deletionMachine p (before q) e.val) (after q)) (hbudget : ∀ q, (after q).work ≤ reserve)
    (hnormal : ∀ (q : Fin (scaleCount i)) (v : Fin i.n), (after q).natMem v.val ≤ 1 ∧
      ((after q).natMem v.val = 0 → 0 ≤ (after q).realMem v.val)) :
    let initial := boundaryAdapter i b ptr
    let final := adapterTrace i initial (updateEventsPrefix i p B e before after (scaleCount i))
    ∃ d, Ends (normalProgram coefficient p) (deletionMachine (normalProgram coefficient p) c e.val) d ∧
      NormalMemory i p B reserve after final.maxima final.pointer (data d) ∧
      d.work+13*pointerEnergy i initial ≤ c.work+(scaleUpdateCharge p i.size+36)*updateWorkPrefix i before after (scaleCount i)+13*pointerEnergy i final+1 := by
  let host := normalProgram coefficient p
  let start := deletionMachine host c e.val
  have hstart : NormalMemory i p B reserve before b ptr (data start) := by
    rw [data_deletion];exact h.external_input e.val
  obtain ⟨cost,t,he,htmem,hcost⟩ := normalUpdate_eval i hi p B reserve hB e before after b ptr (data start) hstart rfl hp hbeforeTail hends hbudget hnormal
  obtain ⟨d,hend,hdata,hwork⟩ := command_ends he host host.update start (program_update _ _) rfl rfl rfl rfl (program_update_halt _ _)
  refine ⟨d,hend,?_,?_⟩
  · rw [hdata];exact htmem
  · change d.work+13*pointerEnergy i (boundaryAdapter i b ptr) ≤ _
    change d.work = c.work+cost+1 at hwork
    rw [hwork]
    omega
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
lemma Maintains.source_guide {p : Program} {C : ℝ} {a : ℕ → ℝ} {queryBound : ℕ} {i : Input}
    (h : Maintains p C a queryBound false i) (ds : List (Fin i.k)) (hds : Legal ds) :
    Nonempty (SourceGuide p C a i ds) := by
  obtain ⟨cs,hrun,hlen,hgood,hcost,_⟩ := h ds hds
  let f : Fin (ds.length+1) → Machine := fun t => cs[t.val]'(by have ht := t.isLt;omega)
  have hget (t : Fin (ds.length+1)) : cs[t.val]? = some (f t) := List.getElem?_eq_getElem (by have ht := t.isLt;omega)
  have hmem (t : Fin (ds.length+1)) : f t ∈ cs := List.mem_of_getElem? (hget t)
  have hlast : cs.getLast? = some (f (Fin.last ds.length)) := by
    rw [List.getLast?_eq_getElem?,hlen,Nat.add_sub_cancel]
    exact hget (Fin.last ds.length)
  have hworkLast : ((f (Fin.last ds.length)).work : ℝ) ≤ C*i.size*a i.size/i.accuracy := by
    have hh := hcost _ hlast
    simp only [Bool.false_eq_true,if_false,mul_one,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at hh
    have hn : (0 : ℝ) ≤ ds.length := Nat.cast_nonneg _
    linarith
  refine ⟨⟨f,?_,?_,?_,?_,?_,?_,?_⟩⟩
  · obtain ⟨c,hc,he⟩ := hrun.initial_execution
    have heq : c = f 0 := Option.some.inj (hc.symm.trans (hget 0))
    rwa [heq] at he
  · intro t
    obtain ⟨c,d,hc,hd,he⟩ := hrun.transition_at t.val t.isLt
    have hc' : c = f t.castSucc := Option.some.inj (hc.symm.trans (hget t.castSucc))
    have hd' : d = f t.succ := Option.some.inj (hd.symm.trans (hget t.succ))
    rwa [hc',hd'] at he
  · intro t;exact (hgood t.val (f t) (hget t)).1
  · intro t;exact (hgood t.val (f t) (hget t)).2.1
  · intro t;exact (hgood t.val (f t) (hget t)).2.2
  · intro t
    have hh := hrun.work_le_last _ hlast (f t) (hmem t)
    exact (show ((f t).work : ℝ) ≤ (f (Fin.last ds.length)).work by exact_mod_cast hh).trans hworkLast
  · intro t;exact hrun.zero_register_tail _ (hmem t)
end DecrAlmostLinearSSSP.Decremental
end s294
section s295
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
lemma adapterWrite_maxima_le (i : Input) (a : AdapterState i)
    (upper : Fin (scaleCount i) → Fin i.n → ℝ≥0∞)
    (ha : ∀ j v, a.maxima j v ≤ upper j v) (j : Fin (scaleCount i)) (v : Fin i.n) (value : ℝ≥0∞)
    (hv : value ≤ upper j v) : ∀ k z, (adapterWrite i a j v value).maxima k z ≤ upper k z := by
  classical
  intro k z
  change Function.update a.maxima j (Function.update (a.maxima j) v (max (a.maxima j v) value)) k z ≤ _
  by_cases hk : k = j
  · subst k
    rw [Function.update_self]
    by_cases hz : z = v
    · subst z;rw [Function.update_self];exact max_le (ha j v) hv
    · rw [Function.update_of_ne hz];exact ha j z
  · rw [Function.update_of_ne hk];exact ha k z
lemma adapterTrace_maxima_le (i : Input) (a : AdapterState i)
    (upper : Fin (scaleCount i) → Fin i.n → ℝ≥0∞)
    (ha : ∀ j v, a.maxima j v ≤ upper j v) (xs : List (AdapterEvent i))
    (hx : ∀ j v value, (j,v,value) ∈ xs → value ≤ upper j v) :
    ∀ j v, (adapterTrace i a xs).maxima j v ≤ upper j v := by
  induction xs generalizing a with
  | nil => exact ha
  | cons event xs ih =>
    rcases event with ⟨j,v,value⟩
    exact ih _ (adapterWrite_maxima_le i a upper ha j v value (hx j v value (by simp)))
      (fun k z x hm => hx k z x (by simp [hm]))
end DecrAlmostLinearSSSP.Decremental
end s295
section s296
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma Ends.execute_elapsed {p : Program} {c d : Machine} (h : Ends p c d) :
    execute p c (d.work-c.work) = d := by
  obtain ⟨t,ht,hhalt,_⟩ := h
  have hh : (execute p c t).halted = true := by rwa [ht]
  obtain ⟨r,_,he,hr⟩ := terminating_prefix p c t hh
  rw [ht] at he hr
  rwa [hr] at he
end DecrAlmostLinearSSSP.Decremental
end s296
section s297
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
lemma scaleEvents_value (i : Input) (p : Program) (B : ℕ) (e : Fin i.k)
    (before after : Fin (scaleCount i) → Machine) (j q : Fin (scaleCount i)) (v : Fin i.n) (value : ℝ≥0∞)
    (h : (q,v,value) ∈ scaleEvents i p B e before after j) : value = stored (after q) v.val := by
  rw [scaleEvents,ReportConsume.allEvents_public] at h
  obtain ⟨u,_,heq⟩ := List.mem_map.mp h
  cases heq
  rfl
lemma updateEventsPrefix_value (i : Input) (p : Program) (B : ℕ) (e : Fin i.k)
    (before after : Fin (scaleCount i) → Machine) (d : ℕ)
    (q : Fin (scaleCount i)) (v : Fin i.n) (value : ℝ≥0∞)
    (h : (q,v,value) ∈ updateEventsPrefix i p B e before after d) : value = stored (after q) v.val := by
  induction d with
  | zero => simp [updateEventsPrefix] at h
  | succ d ih =>
    simp only [updateEventsPrefix,List.mem_append] at h
    rcases h with h | h
    · exact ih h
    · split_ifs at h with hd
      · exact scaleEvents_value i p B e before after ⟨d,hd⟩ q v value h
      · simp at h
lemma update_cache_upper (i : Input) (p : Program) (B : ℕ) (e : Fin i.k)
    (before after : Fin (scaleCount i) → Machine) (a : AdapterState i)
    (upper : Fin (scaleCount i) → Fin i.n → ℝ≥0∞)
    (ha : ∀ q v, a.maxima q v ≤ upper q v) (hafter : ∀ q (v : Fin i.n), stored (after q) v.val ≤ upper q v) (d : ℕ) :
    ∀ q v, (adapterTrace i a (updateEventsPrefix i p B e before after d)).maxima q v ≤ upper q v := by
  apply adapterTrace_maxima_le i a upper ha
  intro q v value h
  rw [updateEventsPrefix_value i p B e before after d q v value h]
  exact hafter q v
lemma scale_cache_dominates (i : Input) (p : Program) (B : ℕ) (e : Fin i.k)
    (before after : Fin (scaleCount i) → Machine) (a : AdapterState i) (j : Fin (scaleCount i))
    (hend : Ends p (deletionMachine p (before j) e.val) (after j))
    (ha : ∀ v : Fin i.n, stored (before j) v.val ≤ a.maxima j v) :
    ∀ v : Fin i.n, stored (after j) v.val ≤ (adapterTrace i a (scaleEvents i p B e before after j)).maxima j v := by
  have hr := hend.execute_elapsed
  change execute p (deletionMachine p (before j) e.val) ((after j).work-(before j).work) = after j at hr
  have hh := consumed_physical_reports_dominate i a j B j.val p (deletionMachine p (before j) e.val)
    ((after j).work-(before j).work) ha
  rw [hr] at hh
  simpa only [scaleEvents,ReportConsume.allEvents_public,scaleReports,hr] using hh
lemma update_cache_dominates_prefix (i : Input) (p : Program) (B : ℕ) (e : Fin i.k)
    (before after : Fin (scaleCount i) → Machine) (a : AdapterState i)
    (hends : ∀ q, Ends p (deletionMachine p (before q) e.val) (after q))
    (ha : ∀ q (v : Fin i.n), stored (before q) v.val ≤ a.maxima q v)
    (d : ℕ) (q : Fin (scaleCount i)) (hq : q.val < d) :
    ∀ v : Fin i.n, stored (after q) v.val ≤ (adapterTrace i a (updateEventsPrefix i p B e before after d)).maxima q v := by
  induction d with
  | zero => omega
  | succ d ih =>
    by_cases hqd : q.val < d
    · intro v
      have hh := ih hqd v
      simp only [updateEventsPrefix,adapterTrace_append]
      exact hh.trans (adapterTrace_maxima_mono i _ _ q v)
    · have hval : q.val = d := by omega
      have hd : d < scaleCount i := by have hh := q.isLt;omega
      have hqeq : q = (⟨d,hd⟩ : Fin (scaleCount i)) := Fin.ext hval
      let ac := adapterTrace i a (updateEventsPrefix i p B e before after d)
      have hac : ∀ v : Fin i.n, stored (before q) v.val ≤ ac.maxima q v :=
        fun v => (ha q v).trans (adapterTrace_maxima_mono i a _ q v)
      have hh := scale_cache_dominates i p B e before after ac q (hends q) hac
      simpa only [updateEventsPrefix,dif_pos hd,adapterTrace_append,hqeq] using hh
lemma update_cache_dominates (i : Input) (p : Program) (B : ℕ) (e : Fin i.k)
    (before after : Fin (scaleCount i) → Machine) (a : AdapterState i)
    (hends : ∀ q, Ends p (deletionMachine p (before q) e.val) (after q))
    (ha : ∀ q (v : Fin i.n), stored (before q) v.val ≤ a.maxima q v) :
    ∀ q (v : Fin i.n), stored (after q) v.val ≤
      (adapterTrace i a (updateEventsPrefix i p B e before after (scaleCount i))).maxima q v :=
  fun q => update_cache_dominates_prefix i p B e before after a hends ha (scaleCount i) q q.isLt
end DecrAlmostLinearSSSP.Decremental.Native
end s297
section s298
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
lemma choose_barrier_guides (i : Input) (hi : i.Valid) (hn : 2 ≤ i.n) (heps : 1/(i.size : ℝ) < i.accuracy)
    (p : Program) (C : ℝ) (a : ℕ → ℝ) (queryBound : ℕ)
    (hpoly : ∀ x : Input, x.Valid → 2 ≤ x.n → x.W ≤ x.size^2 →
      1/(x.size : ℝ) < x.accuracy → x.accuracy < 1 → Maintains p C a queryBound false x)
    (ds : List (Fin i.k)) (hds : Legal ds) : Nonempty (BarrierGuides i p C a ds) := by
  classical
  exact ⟨fun q => Classical.choice ((polynomial_maintains_barrier p C a queryBound hpoly i hi hn heps q.val).source_guide ds hds)⟩
lemma live_prefix_mono {k : ℕ} (ds : List (Fin k)) (r t : ℕ) (htr : t ≤ r) :
    live (ds.take r) ⊆ live (ds.take t) := by
  have hh := live_take_subset (ds.take r) t
  simpa only [List.take_take,min_eq_left htr] using hh
lemma HistoryBoundary.accurate {i : Input} (hi : i.Valid) {p : Program} {C : ℝ} {a : ℕ → ℝ} {ds : List (Fin i.k)}
    {guides : BarrierGuides i p C a ds} {t : Fin (ds.length+1)}
    {b : Fin (scaleCount i) → Fin i.n → ℝ≥0∞} {ptr : Fin i.n → ℕ} (h : HistoryBoundary guides t b ptr) :
    ∀ v : Fin i.n, i.dist (ds.take t.val) v ≤ selected i b ptr v ∧
      selected i b ptr v ≤ ENNReal.ofReal (1+i.accuracy)*i.dist (ds.take t.val) v ∧
      (selected i b ptr v = ⊤ ↔ ¬Reachable i.graph (live (ds.take t.val)) i.source v) := by
  apply barrier_cache_selected_accuracy i hi (historyIndices ds t.val) (fun r => live (ds.take r.val))
    (live (ds.take t.val)) ?_ (fun q r v => stored (sourceAt guides r q) v.val) b ?_ h.upper ?_ ptr h.valid
  · intro r hr
    have hrt : r.val ≤ t.val := (Finset.mem_filter.mp hr).2
    exact live_prefix_mono ds t.val r.val hrt
  · intro q v
    exact ((guides q).accurate t v).1.trans (h.current q v)
  · intro q r hr v
    exact ((guides q).accurate r v).2.1
end DecrAlmostLinearSSSP.Decremental.Native
end s298
section s299
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
lemma historySup_mono {i : Input} {p : Program} {C : ℝ} {a : ℕ → ℝ} {ds : List (Fin i.k)}
    (guides : BarrierGuides i p C a ds) (r t : ℕ) (hrt : r ≤ t) (q : Fin (scaleCount i)) (v : Fin i.n) :
    historySup guides r q v ≤ historySup guides t q v := by
  apply Finset.sup_mono
  intro k hk
  have hkr := (Finset.mem_filter.mp hk).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hkr.trans hrt⟩
lemma historySup_current {i : Input} {p : Program} {C : ℝ} {a : ℕ → ℝ} {ds : List (Fin i.k)}
    (guides : BarrierGuides i p C a ds) (t : Fin (ds.length+1)) (q : Fin (scaleCount i)) (v : Fin i.n) :
    stored (sourceAt guides t q) v.val ≤ historySup guides t.val q v :=
  Finset.le_sup (f := fun r => stored (sourceAt guides r q) v.val) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,le_rfl⟩)
lemma historyBoundary_initial {i : Input} {p : Program} {C : ℝ} {a : ℕ → ℝ} {ds : List (Fin i.k)}
    (guides : BarrierGuides i p C a ds) :
    HistoryBoundary guides 0 (fun q v => stored (sourceAt guides 0 q) v.val)
      (initialPointers i (fun q v => stored (sourceAt guides 0 q) v.val)) := by
  constructor
  · intro q v;exact le_rfl
  · exact historySup_current guides 0
  · intro v
    exact adapterInitialize_pointer_valid i (fun q v => stored (sourceAt guides 0 q) v.val) v
lemma historyBoundary_update {i : Input} {p : Program} {C : ℝ} {a : ℕ → ℝ} {ds : List (Fin i.k)}
    (guides : BarrierGuides i p C a ds) (B : ℕ) (t : Fin ds.length)
    {b : Fin (scaleCount i) → Fin i.n → ℝ≥0∞} {ptr : Fin i.n → ℕ}
    (h : HistoryBoundary guides t.castSucc b ptr) :
    let before := sourceAt guides t.castSucc
    let after := sourceAt guides t.succ
    let final := adapterTrace i (boundaryAdapter i b ptr)
      (updateEventsPrefix i p B ds[t] before after (scaleCount i))
    HistoryBoundary guides t.succ final.maxima final.pointer := by
  let before := sourceAt guides t.castSucc
  let after := sourceAt guides t.succ
  let initial := boundaryAdapter i b ptr
  let final := adapterTrace i initial (updateEventsPrefix i p B ds[t] before after (scaleCount i))
  have hends : ∀ q, Ends p (deletionMachine p (before q) ds[t].val) (after q) := fun q => (guides q).update t
  constructor
  · exact update_cache_dominates i p B ds[t] before after initial hends h.current
  · apply update_cache_upper i p B ds[t] before after initial (historySup guides t.succ.val)
    · intro q v
      exact (h.upper q v).trans (historySup_mono guides t.castSucc.val t.succ.val (by simp) q v)
    · exact historySup_current guides t.succ
  · exact adapterTrace_pointer_valid i initial _ h.valid
end DecrAlmostLinearSSSP.Decremental.Native
end s299
section s300
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
lemma normalProgram_guided_initialization (i : Input) (hi : i.Valid) (hn : 2 ≤ i.n) (heps : 1/(i.size : ℝ) < i.accuracy)
    (p : Program) (C : ℝ) (hC : 0 < C) (a : ℕ → ℝ) (ha : Subpolynomial a) (queryBound coefficient : ℕ)
    (hpoly : ∀ x : Input, x.Valid → 2 ≤ x.n → x.W ≤ x.size^2 →
      1/(x.size : ℝ) < x.accuracy → x.accuracy < 1 → Maintains p C a queryBound false x)
    (ds : List (Fin i.k)) (guides : BarrierGuides i p C a ds) :
    ∃ c, Ends (normalProgram coefficient p) (initialMachine (normalProgram coefficient p) i) c ∧
      NormalMemory i p (i.n+3*i.k+2) (coefficient*i.size^3+1) (sourceAt guides 0)
        (fun q v => stored (sourceAt guides 0 q) v.val) (initialPointers i (fun q v => stored (sourceAt guides 0 q) v.val)) (data c) ∧
      (c.work : ℝ) ≤ ((normalInitConstant p coefficient : ℝ)*(1+1024*C))*i.size*
        normalWrapperOverhead a i.size/i.accuracy*max 1 (logarithm2 i.W)+1 := by
  obtain ⟨f,cost,c,hf,hend,hwork,hcost,hmem,_⟩ := normalProgram_initialization i hi hn heps p C a queryBound coefficient hpoly
  have hfeq : f = sourceAt guides 0 := by
    funext q
    exact (hf q).ends.deterministic (guides q).initial
  have huniform := normal_initialization_uniform_cost hi hC ha f hf coefficient cost hcost
  refine ⟨c,hend,?_,?_⟩
  · rwa [hfeq] at hmem
  · rw [hwork,Nat.cast_add,Nat.cast_one]
    linarith
end DecrAlmostLinearSSSP.Decremental.Native
end s300
section s301
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
lemma NormalMemory.good {i : Input} (hi : i.Valid) {p : Program} {C : ℝ} {a : ℕ → ℝ} {ds : List (Fin i.k)}
    {guides : BarrierGuides i p C a ds} {t : Fin (ds.length+1)} {B reserve : ℕ}
    {b : Fin (scaleCount i) → Fin i.n → ℝ≥0∞} {ptr : Fin i.n → ℕ} {c : Machine}
    (h : NormalMemory i p B reserve (sourceAt guides t) b ptr (data c)) (hh : HistoryBoundary guides t b ptr) :
    GoodBoundary i ds t.val c := by
  refine ⟨h.source,h.normalized,?_⟩
  intro v
  have hvalue : stored c v.val = selected i b ptr v := h.output v
  rw [hvalue]
  exact hh.accurate hi v
lemma maintenance_credit_step (Q delta oldWork newWork index oldEnergy newEnergy initialEnergy initialSum currentSum nextSum initialWork : ℕ)
    (hdelta : delta+currentSum = nextSum) (hpositive : 1 ≤ delta)
    (hstep : newWork+13*oldEnergy ≤ oldWork+Q*delta+13*newEnergy+1)
    (hcredit : oldWork+6*index+13*initialEnergy+(Q+7)*initialSum ≤ initialWork+(Q+7)*currentSum+13*oldEnergy) :
    newWork+6*(index+1)+13*initialEnergy+(Q+7)*initialSum ≤ initialWork+(Q+7)*nextSum+13*newEnergy := by
  have hmul := congrArg (fun n => (Q+7)*n) hdelta
  nlinarith only [hdelta,hpositive,hstep,hcredit,hmul]
end DecrAlmostLinearSSSP.Decremental.Native
end s301
section s302
set_option autoImplicit false
open Filter
open scoped Topology
namespace DecrAlmostLinearSSSP.Decremental
lemma subpolynomial_linear_envelope (a : ℕ → ℝ) (ha : Subpolynomial a) :
    ∃ B : ℕ, 0 < B ∧ ∀ m, a m ≤ (B : ℝ)*(max 2 m : ℕ) := by
  classical
  have hev : ∀ᶠ m : ℕ in atTop, Real.log (a m)/Real.log (max 2 m : ℕ) < 1 :=
    ha.2.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨N,hN⟩ := eventually_atTop.mp hev
  let c := 1 + ∑ m ∈ Finset.range N, a m
  have hc : 0 < c := by
    have hs : 0 ≤ ∑ m ∈ Finset.range N, a m := Finset.sum_nonneg (fun m _ => (ha.1 m).le)
    dsimp [c]
    linarith
  obtain ⟨B,hB⟩ := exists_nat_gt c
  have hBpos : 0 < B := by exact_mod_cast (hc.trans hB)
  refine ⟨B,hBpos,?_⟩
  intro m
  by_cases hm : N ≤ m
  · have hh : Real.log (a m) ≤ Real.log (max 2 m : ℕ) :=
      ((div_lt_one (log_size_positive m)).mp (hN m hm)).le
    have hsize : (0 : ℝ) < (max 2 m : ℕ) := by exact_mod_cast (show 0 < max 2 m from by omega)
    have hlo := (Real.log_le_log_iff (ha.1 m) hsize).mp hh
    have hBone : (1 : ℝ) ≤ B := by exact_mod_cast hBpos
    exact hlo.trans (by nlinarith only [hsize,hBone])
  · have hmem : m ∈ Finset.range N := Finset.mem_range.mpr (by omega)
    have hsum := Finset.single_le_sum (fun r (_ : r ∈ Finset.range N) => (ha.1 r).le) hmem
    have ham : a m ≤ c := by dsimp [c]; linarith
    have hmone : (1 : ℝ) ≤ (max 2 m : ℕ) := by exact_mod_cast (show 1 ≤ max 2 m from by omega)
    have hBzero : (0 : ℝ) ≤ B := Nat.cast_nonneg _
    exact ham.trans (hB.le.trans (by nlinarith only [hmone,hBzero]))
lemma normal_source_work_envelope (C : ℝ) (hC : 0 < C) (a : ℕ → ℝ) (ha : Subpolynomial a) :
    ∃ B : ℕ, 0 < B ∧ ∀ (i : Input), i.Valid → 1/(i.size : ℝ) < i.accuracy →
      C*(64*(i.size : ℝ))*a (64*i.size)*(i.accuracy/16)⁻¹ ≤
        (B : ℝ)*(i.size : ℝ)^3 := by
  obtain ⟨A,hA,hbound⟩ := subpolynomial_linear_envelope a ha
  obtain ⟨B,hB⟩ := exists_nat_gt (65536*C*A)
  have hBpos : 0 < B := by
    have hh : (0 : ℝ) < A := by exact_mod_cast hA
    exact_mod_cast (lt_trans (by positivity : (0 : ℝ) < 65536*C*A) hB)
  refine ⟨B,hBpos,?_⟩
  intro i hi heps
  have hm : (0 : ℝ) < i.size := by
    exact_mod_cast (lt_of_lt_of_le (lt_of_le_of_lt (Nat.zero_le _) i.source.isLt) hi.1)
  have hmNat : 1 ≤ i.size := by exact_mod_cast (show (0 : ℝ) < i.size from hm)
  have h64 : 2 ≤ 64*i.size := by omega
  have hab : a (64*i.size) ≤ (A : ℝ)*(64*(i.size : ℝ)) := by
    simpa only [max_eq_right h64,Nat.cast_mul,Nat.cast_ofNat] using hbound (64*i.size)
  have he := hi.2.2.2.1
  have hinv : (i.accuracy/16)⁻¹ ≤ 16*(i.size : ℝ) := by
    have hmul : 1 < i.accuracy*i.size := (div_lt_iff₀ hm).mp heps
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (by positivity : 0 < i.accuracy/16)).mpr
    nlinarith only [hmul]
  have hpos : 0 ≤ C*(64*(i.size : ℝ)) := by positivity
  have hfirst := mul_le_mul_of_nonneg_left hab hpos
  have hsecond := mul_le_mul hfirst hinv (by positivity : 0 ≤ (i.accuracy/16)⁻¹)
    (by have hAN : (0 : ℝ) ≤ A := Nat.cast_nonneg _; positivity)
  calc
    _ ≤ C*(64*(i.size : ℝ))*((A : ℝ)*(64*(i.size : ℝ)))*(16*(i.size : ℝ)) := hsecond
    _ = (65536*C*A)*(i.size : ℝ)^3 := by ring
    _ ≤ (B : ℝ)*(i.size : ℝ)^3 := mul_le_mul_of_nonneg_right hB.le (by positivity)
end DecrAlmostLinearSSSP.Decremental
end s302
section s303
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
lemma sourceSumWork_update {i : Input} {p : Program} {C : ℝ} {a : ℕ → ℝ} {ds : List (Fin i.k)}
    (guides : BarrierGuides i p C a ds) (t : Fin ds.length) :
    updateWorkPrefix i (sourceAt guides t.castSucc) (sourceAt guides t.succ) (scaleCount i)+
      sourceSumWork guides t.castSucc = sourceSumWork guides t.succ := by
  rw [updateWorkPrefix_eq_sum]
  unfold sourceSumWork
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  apply Nat.sub_add_cancel
  exact ((guides q).update t).work_mono
lemma sourceSumWork_uniform {i : Input} {p : Program} {C : ℝ} {a : ℕ → ℝ} {ds : List (Fin i.k)}
    (guides : BarrierGuides i p C a ds) (t : Fin (ds.length+1)) :
    (sourceSumWork guides t : ℝ) ≤ (scaleCount i : ℝ)*(C*(64*i.size)*a (64*i.size)/(i.accuracy/16)) := by
  unfold sourceSumWork
  rw [Nat.cast_sum]
  calc
    _ ≤ ∑ _q : Fin (scaleCount i), C*(64*i.size)*a (64*i.size)/(i.accuracy/16) := by
      apply Finset.sum_le_sum
      intro q hq
      simpa only [sourceAt,barrierInput,Nat.cast_mul,Nat.cast_ofNat] using (guides q).work t
    _ = _ := by simp
lemma source_guide_reserve {i : Input} {p : Program} {C : ℝ} {a : ℕ → ℝ} {ds : List (Fin i.k)}
    (guides : BarrierGuides i p C a ds) (coefficient : ℕ)
    (henvelope : C*(64*(i.size : ℝ))*a (64*i.size)*(i.accuracy/16)⁻¹ ≤
      (coefficient : ℝ)*(i.size : ℝ)^3) (t : Fin (ds.length+1)) (q : Fin (scaleCount i)) :
    (sourceAt guides t q).work ≤ coefficient*i.size^3+1 := by
  have hw : ((sourceAt guides t q).work : ℝ) ≤ C*(64*i.size)*a (64*i.size)/(i.accuracy/16) := by
    simpa only [sourceAt,barrierInput,Nat.cast_mul,Nat.cast_ofNat] using (guides q).work t
  rw [div_eq_mul_inv] at hw
  have hh : (sourceAt guides t q).work ≤ coefficient*i.size^3 := by exact_mod_cast hw.trans henvelope
  omega
lemma choose_reserve_coefficient (C : ℝ) (hC : 0 < C) (a : ℕ → ℝ) (ha : Subpolynomial a) :
    ∃ coefficient : ℕ, 32 ≤ coefficient ∧ ∀ (i : Input), i.Valid → 1/(i.size : ℝ) < i.accuracy →
      C*(64*(i.size : ℝ))*a (64*i.size)*(i.accuracy/16)⁻¹ ≤ (coefficient : ℝ)*(i.size : ℝ)^3 := by
  obtain ⟨B,hB,hbound⟩ := normal_source_work_envelope C hC a ha
  refine ⟨B+32,by omega,?_⟩
  intro i hi heps
  apply (hbound i hi heps).trans
  have hh : (B : ℝ) ≤ (B+32 : ℕ) := by exact_mod_cast (show B ≤ B+32 by omega)
  exact mul_le_mul_of_nonneg_right hh (by positivity)
end DecrAlmostLinearSSSP.Decremental.Native
end s303
section s304
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
lemma normalRunState_initial (i : Input) (hi : i.Valid) (p : Program) (C : ℝ) (a : ℕ → ℝ) (ds : List (Fin i.k))
    (guides : BarrierGuides i p C a ds) (coefficient : ℕ) (c : Machine)
    (hend : Ends (normalProgram coefficient p) (initialMachine (normalProgram coefficient p) i) c)
    (hm : NormalMemory i p (i.n+3*i.k+2) (coefficient*i.size^3+1) (sourceAt guides 0)
      (sourceInitialCache guides) (sourceInitialPointer guides) (data c)) :
    Nonempty (NormalRunState i p C a ds guides coefficient c 0) := by
  have hh := historyBoundary_initial guides
  have hg := hm.good hi hh
  refine ⟨⟨c,sourceInitialCache guides,sourceInitialPointer guides,hm,hh,[c],?_,rfl,?_,?_⟩⟩
  · simpa only [Fin.val_zero,List.take_zero] using OnlineRun.init hend
  · intro j d hd
    have heq : j = 0 := by
      by_contra hj
      have hnone : ([c] : List Machine)[j]? = none := List.getElem?_eq_none (by simp;omega)
      rw [hnone] at hd
      contradiction
    subst j
    have hdc : d = c := by simpa using hd.symm
    subst d
    exact hg
  · dsimp only [Fin.val_zero,initialPointerEnergy]
    omega
end DecrAlmostLinearSSSP.Decremental.Native
end s304
section s305
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
lemma normalRunState_next (i : Input) (hi : i.Valid) (p : Program) (C : ℝ) (a : ℕ → ℝ) (ds : List (Fin i.k))
    (guides : BarrierGuides i p C a ds) (coefficient : ℕ) (initial : Machine) (t : Fin ds.length)
    (henvelope : C*(64*(i.size : ℝ))*a (64*i.size)*(i.accuracy/16)⁻¹ ≤ (coefficient : ℝ)*(i.size : ℝ)^3)
    (st : NormalRunState i p C a ds guides coefficient initial t.castSucc) :
    Nonempty (NormalRunState i p C a ds guides coefficient initial t.succ) := by
  let B := i.n+3*i.k+2
  let before := sourceAt guides t.castSucc
  let after := sourceAt guides t.succ
  let ac := boundaryAdapter i st.cache st.pointer
  let af := adapterTrace i ac (updateEventsPrefix i p B ds[t] before after (scaleCount i))
  have hends : ∀ q, Ends p (deletionMachine p (before q) ds[t].val) (after q) := fun q => (guides q).update t
  have hbudget : ∀ q, (after q).work ≤ coefficient*i.size^3+1 := source_guide_reserve guides coefficient henvelope t.succ
  obtain ⟨d,hend,hm,hstep⟩ := normalProgram_update i hi p coefficient B (coefficient*i.size^3+1) (by dsimp [B];omega)
    ds[t] before after st.cache st.pointer st.machine st.memory st.history.valid
    (fun q => (guides q).tail t.castSucc) hends hbudget (fun q => (guides q).normal t.succ)
  have hhist : HistoryBoundary guides t.succ af.maxima af.pointer := historyBoundary_update guides B t st.history
  have hgood : GoodBoundary i ds t.succ.val d := hm.good hi hhist
  have hlen : st.log.length = t.val+1 := by
    have hh := st.run.length
    change st.log.length = (ds.take t.val).length+1 at hh
    simpa only [List.length_take,min_eq_left (Nat.le_of_lt t.isLt)] using hh
  have htake : ds.take t.castSucc.val++[ds[t]] = ds.take t.succ.val :=
    List.take_concat_get' ds t.val t.isLt
  have hrun : OnlineRun (normalProgram coefficient p) i (ds.take t.succ.val) (st.log++[d]) := by
    have hh := OnlineRun.next st.run st.last ds[t] hend
    rwa [htake] at hh
  have hlogGood : ∀ j c, (st.log++[d])[j]? = some c → GoodBoundary i ds j c := by
    intro j c hc
    by_cases hj : j < st.log.length
    · rw [List.getElem?_append_left hj] at hc
      exact st.good j c hc
    · by_cases hjeq : j = st.log.length
      · subst j
        rw [List.getElem?_append_right le_rfl,Nat.sub_self] at hc
        have hcd : d = c := by simpa using hc
        subst c
        rw [hlen]
        exact hgood
      · have hout : (st.log++[d])[j]? = none := List.getElem?_eq_none (by simp only [List.length_append,List.length_singleton];omega)
        rw [hout] at hc
        contradiction
  let Q := scaleUpdateCharge p i.size+36
  let delta := updateWorkPrefix i before after (scaleCount i)
  have hdelta : delta+sourceSumWork guides t.castSucc = sourceSumWork guides t.succ := sourceSumWork_update guides t
  have hpositive : 1 ≤ delta := by
    have hh := updateWorkPrefix_ge i p ds[t] before after hends (scaleCount i) le_rfl
    have hS : 1 ≤ scaleCount i := by unfold scaleCount;omega
    omega
  have hc := maintenance_credit_step Q delta st.machine.work d.work t.val
    (pointerEnergy i ac) (pointerEnergy i af) (initialPointerEnergy guides) (sourceSumWork guides 0)
    (sourceSumWork guides t.castSucc) (sourceSumWork guides t.succ) initial.work hdelta hpositive hstep st.credit
  refine ⟨⟨d,af.maxima,af.pointer,hm,hhist,st.log++[d],hrun,by simp,hlogGood,?_⟩⟩
  exact hc
end DecrAlmostLinearSSSP.Decremental.Native
end s305
section s306
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
lemma normalRunState_full (i : Input) (hi : i.Valid) (p : Program) (C : ℝ) (a : ℕ → ℝ) (ds : List (Fin i.k))
    (guides : BarrierGuides i p C a ds) (coefficient : ℕ) (initial : Machine)
    (henvelope : C*(64*(i.size : ℝ))*a (64*i.size)*(i.accuracy/16)⁻¹ ≤ (coefficient : ℝ)*(i.size : ℝ)^3)
    (st0 : NormalRunState i p C a ds guides coefficient initial 0) :
    Nonempty (NormalRunState i p C a ds guides coefficient initial (Fin.last ds.length)) := by
  have hex : ∀ n (hn : n ≤ ds.length), Nonempty
      (NormalRunState i p C a ds guides coefficient initial (⟨n,by omega⟩ : Fin (ds.length+1))) := by
    intro n
    induction n with
    | zero => intro hn;exact ⟨st0⟩
    | succ n ih =>
      intro hn
      obtain ⟨st⟩ := ih (by omega)
      exact normalRunState_next i hi p C a ds guides coefficient initial ⟨n,by omega⟩ henvelope st
  exact hex ds.length le_rfl
lemma NormalRunState.work_bound {i : Input} {p : Program} {C : ℝ} {a : ℕ → ℝ} {ds : List (Fin i.k)}
    {guides : BarrierGuides i p C a ds} {coefficient : ℕ} {initial : Machine}
    (st : NormalRunState i p C a ds guides coefficient initial (Fin.last ds.length)) :
    st.machine.work+6*ds.length ≤ initial.work+normalMaintenanceCharge p i.size*sourceSumWork guides (Fin.last ds.length)+13*i.n*scaleCount i := by
  have he := pointer_energy_bound i (boundaryAdapter i st.cache st.pointer) st.history.valid
  have hc := st.credit
  change st.machine.work+6*ds.length+13*initialPointerEnergy guides+normalMaintenanceCharge p i.size*sourceSumWork guides 0 ≤
    initial.work+normalMaintenanceCharge p i.size*sourceSumWork guides (Fin.last ds.length)+13*pointerEnergy i (boundaryAdapter i st.cache st.pointer) at hc
  nlinarith only [he,hc]
end DecrAlmostLinearSSSP.Decremental.Native
end s306
section s307
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
lemma normalMaintenanceCharge_bound (p : Program) (m : ℕ) :
    normalMaintenanceCharge p m ≤ normalUpdateConstant p*(16*utilityDepth m+32) := by
  unfold normalMaintenanceCharge scaleUpdateCharge normalUpdateConstant
  have hT : 1 ≤ 16*utilityDepth m+32 := by omega
  have hh := Nat.mul_le_mul_left (observedDispatchCharge p.code+8*registerBound p.code+203) hT
  nlinarith only [hh]
lemma normalProgramConstant_positive (p : Program) (coefficient : ℕ) (C : ℝ) (hC : 0 < C) :
    0 < normalProgramConstant p coefficient C := by unfold normalProgramConstant;positivity
lemma normal_update_uniform_cost (i : Input) (hi : i.Valid) (p : Program) (C : ℝ) (hC : 0 < C)
    (a : ℕ → ℝ) (ha : Subpolynomial a) :
    1+(normalMaintenanceCharge p i.size : ℝ)*(scaleCount i : ℝ)*(C*(64*i.size)*a (64*i.size)/(i.accuracy/16))+
      13*(i.n : ℝ)*(scaleCount i : ℝ) ≤
      (((normalUpdateConstant p : ℝ)+14)*(1+1024*C))*i.size*normalWrapperOverhead a i.size/i.accuracy*max 1 (logarithm2 i.W) := by
  let X : ℝ := 1024*C*i.size*a (64*i.size)/i.accuracy
  let T : ℕ := 16*utilityDepth i.size+32
  have hX : 0 ≤ X := by have hh := (ha.1 (64*i.size)).le;have he := hi.2.2.2.1;dsimp [X];positivity
  have hsource : C*(64*i.size)*a (64*i.size)/(i.accuracy/16) = X := by dsimp [X];ring
  have hm : 1 ≤ i.size := (input_vertex_positive i).trans_le hi.1
  have hS : 1 ≤ scaleCount i := by unfold scaleCount;omega
  have hT : 1 ≤ T := by dsimp [T];omega
  have hmS : 1 ≤ i.size*scaleCount i := by nlinarith
  have hnS := Nat.mul_le_mul_right (scaleCount i) hi.1
  have hmTS : i.size*scaleCount i ≤ i.size*T*scaleCount i := by nlinarith
  have hsmallN : 13*i.n*scaleCount i+1 ≤ 14*i.size*T*scaleCount i := by nlinarith only [hmS,hnS,hmTS]
  have hsmall : 1+13*(i.n : ℝ)*(scaleCount i : ℝ) ≤ 14*(i.size : ℝ)*(T : ℝ)*(scaleCount i : ℝ) := by
    have hh : (13 : ℝ)*i.n*scaleCount i+1 ≤ 14*(i.size : ℝ)*(T : ℝ)*(scaleCount i : ℝ) := by exact_mod_cast hsmallN
    linarith
  have hQ : (normalMaintenanceCharge p i.size : ℝ) ≤ (normalUpdateConstant p : ℝ)*(T : ℝ) := by exact_mod_cast normalMaintenanceCharge_bound p i.size
  have hQX := mul_le_mul_of_nonneg_right hQ (mul_nonneg (Nat.cast_nonneg (scaleCount i)) hX)
  have hbase : 1+(normalMaintenanceCharge p i.size : ℝ)*(scaleCount i : ℝ)*X+13*(i.n : ℝ)*(scaleCount i : ℝ) ≤
      ((normalUpdateConstant p : ℝ)+14)*((i.size : ℝ)+X)*(T : ℝ)*(scaleCount i : ℝ) := by
    have hmargin : 0 ≤ ((normalUpdateConstant p : ℝ)*i.size+14*X)*(T : ℝ)*(scaleCount i : ℝ) := by positivity
    nlinarith only [hQX,hsmall,hmargin]
  rw [hsource]
  apply normal_wrapper_cost_bound i hi C ((normalUpdateConstant p : ℝ)+14) _ hC (by positivity) a ha
  simpa only [X,T,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hbase
lemma normal_total_work_bound (i : Input) (hi : i.Valid) (p : Program) (coefficient : ℕ) (C : ℝ) (hC : 0 < C)
    (a : ℕ → ℝ) (ha : Subpolynomial a) (initial work : ℝ)
    (hinitial : initial ≤ ((normalInitConstant p coefficient : ℝ)*(1+1024*C))*i.size*
      normalWrapperOverhead a i.size/i.accuracy*max 1 (logarithm2 i.W)+1)
    (hwork : work ≤ initial+(normalMaintenanceCharge p i.size : ℝ)*(scaleCount i : ℝ)*
      (C*(64*i.size)*a (64*i.size)/(i.accuracy/16))+13*(i.n : ℝ)*(scaleCount i : ℝ)) :
    work ≤ normalProgramConstant p coefficient C*i.size*normalWrapperOverhead a i.size/i.accuracy*max 1 (logarithm2 i.W) := by
  have hu := normal_update_uniform_cost i hi p C hC a ha
  calc
    work ≤ ((normalInitConstant p coefficient : ℝ)*(1+1024*C))*i.size*
        normalWrapperOverhead a i.size/i.accuracy*max 1 (logarithm2 i.W)+
      (1+(normalMaintenanceCharge p i.size : ℝ)*(scaleCount i : ℝ)*
        (C*(64*i.size)*a (64*i.size)/(i.accuracy/16))+13*(i.n : ℝ)*(scaleCount i : ℝ)) := by
      linarith only [hinitial,hwork]
    _ ≤ ((normalInitConstant p coefficient : ℝ)*(1+1024*C))*i.size*
        normalWrapperOverhead a i.size/i.accuracy*max 1 (logarithm2 i.W)+
      (((normalUpdateConstant p : ℝ)+14)*(1+1024*C))*i.size*normalWrapperOverhead a i.size/i.accuracy*max 1 (logarithm2 i.W) := add_le_add le_rfl hu
    _ = _ := by unfold normalProgramConstant;ring
end DecrAlmostLinearSSSP.Decremental.Native
end s307
section s308
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
lemma normalProgram_maintains (p : Program) (C : ℝ) (hC : 0 < C) (a : ℕ → ℝ) (ha : Subpolynomial a)
    (queryBound coefficient : ℕ)
    (hpoly : ∀ x : Input, x.Valid → 2 ≤ x.n → x.W ≤ x.size^2 →
      1/(x.size : ℝ) < x.accuracy → x.accuracy < 1 → Maintains p C a queryBound false x)
    (hreserve : ∀ (i : Input), i.Valid → 1/(i.size : ℝ) < i.accuracy →
      C*(64*(i.size : ℝ))*a (64*i.size)*(i.accuracy/16)⁻¹ ≤ (coefficient : ℝ)*(i.size : ℝ)^3)
    (i : Input) (hi : i.Valid) (hn : 2 ≤ i.n) (heps : 1/(i.size : ℝ) < i.accuracy) :
    Maintains (normalProgram coefficient p) (normalProgramConstant p coefficient C) (normalWrapperOverhead a) 9 true i := by
  intro ds hds
  obtain ⟨guides⟩ := choose_barrier_guides i hi hn heps p C a queryBound hpoly ds hds
  obtain ⟨initial,hinit,hmemory,hinitCost⟩ := normalProgram_guided_initialization i hi hn heps p C hC a ha queryBound coefficient hpoly ds guides
  obtain ⟨st0⟩ := normalRunState_initial i hi p C a ds guides coefficient initial hinit hmemory
  obtain ⟨st⟩ := normalRunState_full i hi p C a ds guides coefficient initial (hreserve i hi heps) st0
  have hnat := st.work_bound
  have hreal : ((st.machine.work+6*ds.length : ℕ) : ℝ) ≤ (initial.work : ℝ)+
      (normalMaintenanceCharge p i.size : ℝ)*(sourceSumWork guides (Fin.last ds.length) : ℝ)+13*(i.n : ℝ)*(scaleCount i : ℝ) := by
    exact_mod_cast hnat
  have hsource := sourceSumWork_uniform guides (Fin.last ds.length)
  have hmul := mul_le_mul_of_nonneg_left hsource (Nat.cast_nonneg (normalMaintenanceCharge p i.size) : (0 : ℝ) ≤ normalMaintenanceCharge p i.size)
  have hwork : ((st.machine.work+6*ds.length : ℕ) : ℝ) ≤ (initial.work : ℝ)+
      (normalMaintenanceCharge p i.size : ℝ)*(scaleCount i : ℝ)*(C*(64*i.size)*a (64*i.size)/(i.accuracy/16))+
      13*(i.n : ℝ)*(scaleCount i : ℝ) := by nlinarith only [hreal,hmul]
  have htotal := normal_total_work_bound i hi p coefficient C hC a ha (initial.work : ℝ) (((st.machine.work+6*ds.length : ℕ) : ℝ)) hinitCost hwork
  refine ⟨st.log,?_,?_,?_,?_,?_⟩
  · simpa only [Fin.val_last,List.take_length] using st.run
  · have hh := st.run.length
    simpa only [Fin.val_last,List.take_length] using hh
  · intro j c hc
    exact st.good j c hc
  · intro c hc
    have heq : c = st.machine := Option.some.inj (hc.symm.trans st.last)
    subst c
    simpa using htotal
  · intro c hc v
    exact program_query_nine (normalInitialize coefficient p) (normalUpdate p) c v.val
end DecrAlmostLinearSSSP.Decremental.Native
end s308
open DecrAlmostLinearSSSP.Decremental
set_option autoImplicit false
theorem solution : ((((((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program} {B reserve : Nat}
  {f : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → DecrAlmostLinearSSSP.Decremental.Machine}
  {b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal} {ptr : Fin i.n → Nat}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.NormalMemory i p B reserve f b ptr s →
    ∀ (e : Nat),
      DecrAlmostLinearSSSP.Decremental.Native.NormalMemory i p B reserve f b ptr
        (DecrAlmostLinearSSSP.Decremental.Native.externalInput s e)) ∧ (∀ (host : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (e : Nat),
  @Eq.{1} DecrAlmostLinearSSSP.Decremental.Structured.Data
    (DecrAlmostLinearSSSP.Decremental.Structured.data (DecrAlmostLinearSSSP.Decremental.deletionMachine host c e))
    (DecrAlmostLinearSSSP.Decremental.Native.externalInput (DecrAlmostLinearSSSP.Decremental.Structured.data c) e))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
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
            ∃ f cost c,
              And
                (∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
                  DecrAlmostLinearSSSP.Decremental.Native.InitialFacts p C a i
                    (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q) (f q))
                (And
                  (DecrAlmostLinearSSSP.Decremental.Ends
                    (DecrAlmostLinearSSSP.Decremental.Native.normalProgram coefficient p)
                    (DecrAlmostLinearSSSP.Decremental.initialMachine
                      (DecrAlmostLinearSSSP.Decremental.Native.normalProgram coefficient p) i)
                    c)
                  (And
                    (@Eq.{1} Nat c.work
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cost
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
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
                                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                i.size (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          f (fun q v => DecrAlmostLinearSSSP.Decremental.stored (f q) (@Fin.val i.n v))
                          (DecrAlmostLinearSSSP.Decremental.Native.initialPointers i fun q v =>
                            DecrAlmostLinearSSSP.Decremental.stored (f q) (@Fin.val i.n v))
                          (DecrAlmostLinearSSSP.Decremental.Structured.data c))
                        (∀ (v : Fin i.n),
                          And
                            (@LE.le.{0} ENNReal ENNReal.instLE (i.dist (@List.nil.{0} (Fin i.k)) v)
                              (DecrAlmostLinearSSSP.Decremental.stored c (@Fin.val i.n v)))
                            (And
                              (@LE.le.{0} ENNReal ENNReal.instLE
                                (DecrAlmostLinearSSSP.Decremental.stored c (@Fin.val i.n v))
                                (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                                  (@instHMul.{0} ENNReal
                                    (@Distrib.toMul.{0} ENNReal
                                      (@instDistribOfSemiring.{0} ENNReal
                                        (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                                  (ENNReal.ofReal
                                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                                      i.accuracy))
                                  (i.dist (@List.nil.{0} (Fin i.k)) v)))
                              (Iff
                                (@Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.stored c (@Fin.val i.n v))
                                  (@Top.top.{0} ENNReal ENNReal.instTop))
                                (Not
                                  (@DecrAlmostLinearSSSP.Decremental.Reachable i.n i.k i.graph
                                    (@DecrAlmostLinearSSSP.Decremental.live i.k (@List.nil.{0} (Fin i.k))) i.source
                                    v)))))))))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (coefficient B reserve : Nat),
      @LE.le.{0} Nat instLENat i.n B →
        ∀ (e : Fin i.k)
          (before after :
            Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → DecrAlmostLinearSSSP.Decremental.Machine)
          (b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal) (ptr : Fin i.n → Nat)
          (c : DecrAlmostLinearSSSP.Decremental.Machine),
          DecrAlmostLinearSSSP.Decremental.Native.NormalMemory i p B reserve before b ptr
              (DecrAlmostLinearSSSP.Decremental.Structured.data c) →
            (∀ (v : Fin i.n), DecrAlmostLinearSSSP.Decremental.PointerValid i b v (ptr v)) →
              (∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
                  DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail
                    (DecrAlmostLinearSSSP.Decremental.registerBound p.code) (before q)) →
                (∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
                    DecrAlmostLinearSSSP.Decremental.Ends p
                      (DecrAlmostLinearSSSP.Decremental.deletionMachine p (before q) (@Fin.val i.k e)) (after q)) →
                  (∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
                      @LE.le.{0} Nat instLENat (after q).work reserve) →
                    (∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n),
                        And
                          (@LE.le.{0} Nat instLENat ((after q).natMem (@Fin.val i.n v))
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          (@Eq.{1} Nat ((after q).natMem (@Fin.val i.n v))
                              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                            @LE.le.{0} Real Real.instLE
                              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                              ((after q).realMem (@Fin.val i.n v)))) →
                      have initial := DecrAlmostLinearSSSP.Decremental.Native.boundaryAdapter i b ptr;
                      have final :=
                        DecrAlmostLinearSSSP.Decremental.adapterTrace i initial
                          (DecrAlmostLinearSSSP.Decremental.Native.updateEventsPrefix i p B e before after
                            (DecrAlmostLinearSSSP.Decremental.scaleCount i));
                      ∃ d,
                        And
                          (DecrAlmostLinearSSSP.Decremental.Ends
                            (DecrAlmostLinearSSSP.Decremental.Native.normalProgram coefficient p)
                            (DecrAlmostLinearSSSP.Decremental.deletionMachine
                              (DecrAlmostLinearSSSP.Decremental.Native.normalProgram coefficient p) c (@Fin.val i.k e))
                            d)
                          (And
                            (DecrAlmostLinearSSSP.Decremental.Native.NormalMemory i p B reserve after
                              (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i final)
                              (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i final)
                              (DecrAlmostLinearSSSP.Decremental.Structured.data d))
                            (@LE.le.{0} Nat instLENat
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d.work
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
                                  (DecrAlmostLinearSSSP.Decremental.pointerEnergy i initial)))
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (DecrAlmostLinearSSSP.Decremental.Native.scaleUpdateCharge p i.size)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 36) (instOfNatNat (nat_lit 36))))
                                      (DecrAlmostLinearSSSP.Decremental.Native.updateWorkPrefix i before after
                                        (DecrAlmostLinearSSSP.Decremental.scaleCount i))))
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
                                    (DecrAlmostLinearSSSP.Decremental.pointerEnergy i final)))
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))) ∧ (((∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {C : Real} {a : Nat → Real} {queryBound : Nat}
  {i : DecrAlmostLinearSSSP.Decremental.Input},
  DecrAlmostLinearSSSP.Decremental.Maintains p C a queryBound Bool.false i →
    ∀ (ds : List.{0} (Fin i.k)),
      @DecrAlmostLinearSSSP.Decremental.Legal i.k ds →
        Nonempty.{1} (DecrAlmostLinearSSSP.Decremental.SourceGuide p C a i ds)) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (a : DecrAlmostLinearSSSP.Decremental.AdapterState i)
  (upper : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal),
  (∀ (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n),
      @LE.le.{0} ENNReal ENNReal.instLE (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i a j v) (upper j v)) →
    ∀ (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n) (value : ENNReal),
      @LE.le.{0} ENNReal ENNReal.instLE value (upper j v) →
        ∀ (k : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (z : Fin i.n),
          @LE.le.{0} ENNReal ENNReal.instLE
            (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i
              (DecrAlmostLinearSSSP.Decremental.adapterWrite i a j v value) k z)
            (upper k z))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (a : DecrAlmostLinearSSSP.Decremental.AdapterState i)
  (upper : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal),
  (∀ (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n),
      @LE.le.{0} ENNReal ENNReal.instLE (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i a j v) (upper j v)) →
    ∀ (xs : List.{0} (DecrAlmostLinearSSSP.Decremental.AdapterEvent i)),
      (∀ (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n) (value : ENNReal),
          @Membership.mem.{0, 0}
              (Prod.{0, 0} (Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (Prod.{0, 0} (Fin i.n) ENNReal))
              (List.{0} (DecrAlmostLinearSSSP.Decremental.AdapterEvent i))
              (@List.instMembership.{0} (DecrAlmostLinearSSSP.Decremental.AdapterEvent i)) xs
              (@Prod.mk.{0, 0} (Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (Prod.{0, 0} (Fin i.n) ENNReal) j
                (@Prod.mk.{0, 0} (Fin i.n) ENNReal v value)) →
            @LE.le.{0} ENNReal ENNReal.instLE value (upper j v)) →
        ∀ (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n),
          @LE.le.{0} ENNReal ENNReal.instLE
            (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i
              (DecrAlmostLinearSSSP.Decremental.adapterTrace i a xs) j v)
            (upper j v)) ∧ ((∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {c d : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.Ends p c d →
    @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
      (DecrAlmostLinearSSSP.Decremental.execute p c
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) d.work c.work))
      d) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (p : DecrAlmostLinearSSSP.Decremental.Program) (B : Nat) (e : Fin i.k)
  (before after : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → DecrAlmostLinearSSSP.Decremental.Machine)
  (j q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n) (value : ENNReal),
  @Membership.mem.{0, 0}
      (Prod.{0, 0} (Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (Prod.{0, 0} (Fin i.n) ENNReal))
      (List.{0} (DecrAlmostLinearSSSP.Decremental.AdapterEvent i))
      (@List.instMembership.{0} (DecrAlmostLinearSSSP.Decremental.AdapterEvent i))
      (DecrAlmostLinearSSSP.Decremental.Native.scaleEvents i p B e before after j)
      (@Prod.mk.{0, 0} (Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (Prod.{0, 0} (Fin i.n) ENNReal) q
        (@Prod.mk.{0, 0} (Fin i.n) ENNReal v value)) →
    @Eq.{1} ENNReal value (DecrAlmostLinearSSSP.Decremental.stored (after q) (@Fin.val i.n v))))))) ∧ ((((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (p : DecrAlmostLinearSSSP.Decremental.Program) (B : Nat) (e : Fin i.k)
  (before after : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → DecrAlmostLinearSSSP.Decremental.Machine)
  (d : Nat) (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n) (value : ENNReal),
  @Membership.mem.{0, 0}
      (Prod.{0, 0} (Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (Prod.{0, 0} (Fin i.n) ENNReal))
      (List.{0} (DecrAlmostLinearSSSP.Decremental.AdapterEvent i))
      (@List.instMembership.{0} (DecrAlmostLinearSSSP.Decremental.AdapterEvent i))
      (DecrAlmostLinearSSSP.Decremental.Native.updateEventsPrefix i p B e before after d)
      (@Prod.mk.{0, 0} (Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (Prod.{0, 0} (Fin i.n) ENNReal) q
        (@Prod.mk.{0, 0} (Fin i.n) ENNReal v value)) →
    @Eq.{1} ENNReal value (DecrAlmostLinearSSSP.Decremental.stored (after q) (@Fin.val i.n v))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (p : DecrAlmostLinearSSSP.Decremental.Program) (B : Nat) (e : Fin i.k)
  (before after : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → DecrAlmostLinearSSSP.Decremental.Machine)
  (a : DecrAlmostLinearSSSP.Decremental.AdapterState i)
  (upper : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal),
  (∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n),
      @LE.le.{0} ENNReal ENNReal.instLE (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i a q v) (upper q v)) →
    (∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n),
        @LE.le.{0} ENNReal ENNReal.instLE (DecrAlmostLinearSSSP.Decremental.stored (after q) (@Fin.val i.n v))
          (upper q v)) →
      ∀ (d : Nat) (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n),
        @LE.le.{0} ENNReal ENNReal.instLE
          (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i
            (DecrAlmostLinearSSSP.Decremental.adapterTrace i a
              (DecrAlmostLinearSSSP.Decremental.Native.updateEventsPrefix i p B e before after d))
            q v)
          (upper q v))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (p : DecrAlmostLinearSSSP.Decremental.Program) (B : Nat) (e : Fin i.k)
  (before after : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → DecrAlmostLinearSSSP.Decremental.Machine)
  (a : DecrAlmostLinearSSSP.Decremental.AdapterState i) (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
  DecrAlmostLinearSSSP.Decremental.Ends p
      (DecrAlmostLinearSSSP.Decremental.deletionMachine p (before j) (@Fin.val i.k e)) (after j) →
    (∀ (v : Fin i.n),
        @LE.le.{0} ENNReal ENNReal.instLE (DecrAlmostLinearSSSP.Decremental.stored (before j) (@Fin.val i.n v))
          (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i a j v)) →
      ∀ (v : Fin i.n),
        @LE.le.{0} ENNReal ENNReal.instLE (DecrAlmostLinearSSSP.Decremental.stored (after j) (@Fin.val i.n v))
          (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i
            (DecrAlmostLinearSSSP.Decremental.adapterTrace i a
              (DecrAlmostLinearSSSP.Decremental.Native.scaleEvents i p B e before after j))
            j v)) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (p : DecrAlmostLinearSSSP.Decremental.Program) (B : Nat) (e : Fin i.k)
  (before after : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → DecrAlmostLinearSSSP.Decremental.Machine)
  (a : DecrAlmostLinearSSSP.Decremental.AdapterState i),
  (∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
      DecrAlmostLinearSSSP.Decremental.Ends p
        (DecrAlmostLinearSSSP.Decremental.deletionMachine p (before q) (@Fin.val i.k e)) (after q)) →
    (∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n),
        @LE.le.{0} ENNReal ENNReal.instLE (DecrAlmostLinearSSSP.Decremental.stored (before q) (@Fin.val i.n v))
          (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i a q v)) →
      ∀ (d : Nat) (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
        @LT.lt.{0} Nat instLTNat (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q) d →
          ∀ (v : Fin i.n),
            @LE.le.{0} ENNReal ENNReal.instLE (DecrAlmostLinearSSSP.Decremental.stored (after q) (@Fin.val i.n v))
              (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i
                (DecrAlmostLinearSSSP.Decremental.adapterTrace i a
                  (DecrAlmostLinearSSSP.Decremental.Native.updateEventsPrefix i p B e before after d))
                q v)) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (p : DecrAlmostLinearSSSP.Decremental.Program) (B : Nat) (e : Fin i.k)
  (before after : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → DecrAlmostLinearSSSP.Decremental.Machine)
  (a : DecrAlmostLinearSSSP.Decremental.AdapterState i),
  (∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
      DecrAlmostLinearSSSP.Decremental.Ends p
        (DecrAlmostLinearSSSP.Decremental.deletionMachine p (before q) (@Fin.val i.k e)) (after q)) →
    (∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n),
        @LE.le.{0} ENNReal ENNReal.instLE (DecrAlmostLinearSSSP.Decremental.stored (before q) (@Fin.val i.n v))
          (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i a q v)) →
      ∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n),
        @LE.le.{0} ENNReal ENNReal.instLE (DecrAlmostLinearSSSP.Decremental.stored (after q) (@Fin.val i.n v))
          (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i
            (DecrAlmostLinearSSSP.Decremental.adapterTrace i a
              (DecrAlmostLinearSSSP.Decremental.Native.updateEventsPrefix i p B e before after
                (DecrAlmostLinearSSSP.Decremental.scaleCount i)))
            q v))))) ∧ (((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) i.n →
      @LT.lt.{0} Real Real.instLT
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@Nat.cast.{0} Real Real.instNatCast i.size))
          i.accuracy →
        ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (C : Real) (a : Nat → Real) (queryBound : Nat),
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
            ∀ (ds : List.{0} (Fin i.k)),
              @DecrAlmostLinearSSSP.Decremental.Legal i.k ds →
                Nonempty.{1} (DecrAlmostLinearSSSP.Decremental.Native.BarrierGuides i p C a ds)) ∧ (∀ {k : Nat} (ds : List.{0} (Fin k)) (r t : Nat),
  @LE.le.{0} Nat instLENat t r →
    @LE.le.{0} (Finset.{0} (Fin k))
      (@Preorder.toLE.{0} (Finset.{0} (Fin k))
        (@PartialOrder.toPreorder.{0} (Finset.{0} (Fin k)) (@Finset.instPartialOrder.{0} (Fin k))))
      (@DecrAlmostLinearSSSP.Decremental.live k (@List.take.{0} (Fin k) r ds))
      (@DecrAlmostLinearSSSP.Decremental.live k (@List.take.{0} (Fin k) t ds)))) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input},
  i.Valid →
    ∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {C : Real} {a : Nat → Real} {ds : List.{0} (Fin i.k)}
      {guides : DecrAlmostLinearSSSP.Decremental.Native.BarrierGuides i p C a ds}
      {t :
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))}
      {b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal} {ptr : Fin i.n → Nat},
      @DecrAlmostLinearSSSP.Decremental.Native.HistoryBoundary i p C a ds guides t b ptr →
        ∀ (v : Fin i.n),
          And
            (@LE.le.{0} ENNReal ENNReal.instLE
              (i.dist
                (@List.take.{0} (Fin i.k)
                  (@Fin.val
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    t)
                  ds)
                v)
              (DecrAlmostLinearSSSP.Decremental.selected i b ptr v))
            (And
              (@LE.le.{0} ENNReal ENNReal.instLE (DecrAlmostLinearSSSP.Decremental.selected i b ptr v)
                (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                  (@instHMul.{0} ENNReal
                    (@Distrib.toMul.{0} ENNReal
                      (@instDistribOfSemiring.{0} ENNReal
                        (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                  (ENNReal.ofReal
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) i.accuracy))
                  (i.dist
                    (@List.take.{0} (Fin i.k)
                      (@Fin.val
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        t)
                      ds)
                    v)))
              (Iff
                (@Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.selected i b ptr v)
                  (@Top.top.{0} ENNReal ENNReal.instTop))
                (Not
                  (@DecrAlmostLinearSSSP.Decremental.Reachable i.n i.k i.graph
                    (@DecrAlmostLinearSSSP.Decremental.live i.k
                      (@List.take.{0} (Fin i.k)
                        (@Fin.val
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@List.length.{0} (Fin i.k) ds)
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          t)
                        ds))
                    i.source v))))) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program} {C : Real}
  {a : Nat → Real} {ds : List.{0} (Fin i.k)} (guides : DecrAlmostLinearSSSP.Decremental.Native.BarrierGuides i p C a ds)
  (r t : Nat),
  @LE.le.{0} Nat instLENat r t →
    ∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n),
      @LE.le.{0} ENNReal ENNReal.instLE (@DecrAlmostLinearSSSP.Decremental.Native.historySup i p C a ds guides r q v)
        (@DecrAlmostLinearSSSP.Decremental.Native.historySup i p C a ds guides t q v)) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program} {C : Real}
  {a : Nat → Real} {ds : List.{0} (Fin i.k)} (guides : DecrAlmostLinearSSSP.Decremental.Native.BarrierGuides i p C a ds)
  (t :
    Fin
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n),
  @LE.le.{0} ENNReal ENNReal.instLE
    (DecrAlmostLinearSSSP.Decremental.stored (@DecrAlmostLinearSSSP.Decremental.Native.sourceAt i p C a ds guides t q)
      (@Fin.val i.n v))
    (@DecrAlmostLinearSSSP.Decremental.Native.historySup i p C a ds guides
      (@Fin.val
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        t)
      q v))))))) ∧ (((((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program} {C : Real}
  {a : Nat → Real} {ds : List.{0} (Fin i.k)}
  (guides : DecrAlmostLinearSSSP.Decremental.Native.BarrierGuides i p C a ds),
  @DecrAlmostLinearSSSP.Decremental.Native.HistoryBoundary i p C a ds guides
    (@OfNat.ofNat.{0}
      (Fin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (nat_lit 0)
      (@Fin.instOfNat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@instNeZeroNatHAdd_1 (@List.length.{0} (Fin i.k) ds)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (nat_lit 0)))
    (fun q v =>
      DecrAlmostLinearSSSP.Decremental.stored
        (@DecrAlmostLinearSSSP.Decremental.Native.sourceAt i p C a ds guides
          (@OfNat.ofNat.{0}
            (Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (nat_lit 0)
            (@Fin.instOfNat
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@instNeZeroNatHAdd_1 (@List.length.{0} (Fin i.k) ds)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (nat_lit 0)))
          q)
        (@Fin.val i.n v))
    (DecrAlmostLinearSSSP.Decremental.Native.initialPointers i fun q v =>
      DecrAlmostLinearSSSP.Decremental.stored
        (@DecrAlmostLinearSSSP.Decremental.Native.sourceAt i p C a ds guides
          (@OfNat.ofNat.{0}
            (Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (nat_lit 0)
            (@Fin.instOfNat
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@instNeZeroNatHAdd_1 (@List.length.{0} (Fin i.k) ds)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (nat_lit 0)))
          q)
        (@Fin.val i.n v))) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program} {C : Real}
  {a : Nat → Real} {ds : List.{0} (Fin i.k)} (guides : DecrAlmostLinearSSSP.Decremental.Native.BarrierGuides i p C a ds)
  (B : Nat) (t : Fin (@List.length.{0} (Fin i.k) ds))
  {b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal} {ptr : Fin i.n → Nat},
  @DecrAlmostLinearSSSP.Decremental.Native.HistoryBoundary i p C a ds guides
      (@Fin.castSucc (@List.length.{0} (Fin i.k) ds) t) b ptr →
    have before :=
      @DecrAlmostLinearSSSP.Decremental.Native.sourceAt i p C a ds guides
        (@Fin.castSucc (@List.length.{0} (Fin i.k) ds) t);
    have after :=
      @DecrAlmostLinearSSSP.Decremental.Native.sourceAt i p C a ds guides (@Fin.succ (@List.length.{0} (Fin i.k) ds) t);
    have final :=
      DecrAlmostLinearSSSP.Decremental.adapterTrace i (DecrAlmostLinearSSSP.Decremental.Native.boundaryAdapter i b ptr)
        (DecrAlmostLinearSSSP.Decremental.Native.updateEventsPrefix i p B
          (@GetElem.getElem.{0, 0, 0} (List.{0} (Fin i.k)) (Fin (@List.length.{0} (Fin i.k) ds)) (Fin i.k)
            (fun xs i_1 =>
              @LT.lt.{0} Nat instLTNat (@Fin.val (@List.length.{0} (Fin i.k) ds) i_1) (@List.length.{0} (Fin i.k) xs))
            (@Fin.instGetElemFinVal.{0, 0} (List.{0} (Fin i.k)) (Fin i.k)
              (fun as i_1 => @LT.lt.{0} Nat instLTNat i_1 (@List.length.{0} (Fin i.k) as))
              (@List.length.{0} (Fin i.k) ds) (@List.instGetElemNatLtLength.{0} (Fin i.k)))
            ds t
            (@Decidable.byContradiction
              (@LT.lt.{0} Nat instLTNat (@Fin.val (@List.length.{0} (Fin i.k) ds) t) (@List.length.{0} (Fin i.k) ds))
              ((@Fin.val (@List.length.{0} (Fin i.k) ds) t).decLt (@List.length.{0} (Fin i.k) ds)) fun a =>
              (a t.isLt)))
          before after (DecrAlmostLinearSSSP.Decremental.scaleCount i));
    @DecrAlmostLinearSSSP.Decremental.Native.HistoryBoundary i p C a ds guides
      (@Fin.succ (@List.length.{0} (Fin i.k) ds) t) (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i final)
      (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i final))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) i.n →
      @LT.lt.{0} Real Real.instLT
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@Nat.cast.{0} Real Real.instNatCast i.size))
          i.accuracy →
        ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (C : Real),
          @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C →
            ∀ (a : Nat → Real),
              DecrAlmostLinearSSSP.Decremental.Subpolynomial a →
                ∀ (queryBound coefficient : Nat),
                  (∀ (x : DecrAlmostLinearSSSP.Decremental.Input),
                      x.Valid →
                        @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) x.n →
                          @LE.le.{0} Nat instLENat x.W
                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                x.size (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
                            @LT.lt.{0} Real Real.instLT
                                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                                  (@Nat.cast.{0} Real Real.instNatCast x.size))
                                x.accuracy →
                              @LT.lt.{0} Real Real.instLT x.accuracy
                                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
                                DecrAlmostLinearSSSP.Decremental.Maintains p C a queryBound Bool.false x) →
                    ∀ (ds : List.{0} (Fin i.k))
                      (guides : DecrAlmostLinearSSSP.Decremental.Native.BarrierGuides i p C a ds),
                      ∃ c,
                        And
                          (DecrAlmostLinearSSSP.Decremental.Ends
                            (DecrAlmostLinearSSSP.Decremental.Native.normalProgram coefficient p)
                            (DecrAlmostLinearSSSP.Decremental.initialMachine
                              (DecrAlmostLinearSSSP.Decremental.Native.normalProgram coefficient p) i)
                            c)
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
                              (@DecrAlmostLinearSSSP.Decremental.Native.sourceAt i p C a ds guides
                                (@OfNat.ofNat.{0}
                                  (Fin
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@List.length.{0} (Fin i.k) ds)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                  (nat_lit 0)
                                  (@Fin.instOfNat
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@List.length.{0} (Fin i.k) ds)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                    (@instNeZeroNatHAdd_1 (@List.length.{0} (Fin i.k) ds)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                      (@Nat.instNeZeroSucc
                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                                    (nat_lit 0))))
                              (fun q v =>
                                DecrAlmostLinearSSSP.Decremental.stored
                                  (@DecrAlmostLinearSSSP.Decremental.Native.sourceAt i p C a ds guides
                                    (@OfNat.ofNat.{0}
                                      (Fin
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@List.length.{0} (Fin i.k) ds)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                      (nat_lit 0)
                                      (@Fin.instOfNat
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@List.length.{0} (Fin i.k) ds)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                        (@instNeZeroNatHAdd_1 (@List.length.{0} (Fin i.k) ds)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                          (@Nat.instNeZeroSucc
                                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                                        (nat_lit 0)))
                                    q)
                                  (@Fin.val i.n v))
                              (DecrAlmostLinearSSSP.Decremental.Native.initialPointers i fun q v =>
                                DecrAlmostLinearSSSP.Decremental.stored
                                  (@DecrAlmostLinearSSSP.Decremental.Native.sourceAt i p C a ds guides
                                    (@OfNat.ofNat.{0}
                                      (Fin
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@List.length.{0} (Fin i.k) ds)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                      (nat_lit 0)
                                      (@Fin.instOfNat
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@List.length.{0} (Fin i.k) ds)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                        (@instNeZeroNatHAdd_1 (@List.length.{0} (Fin i.k) ds)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                          (@Nat.instNeZeroSucc
                                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                                        (nat_lit 0)))
                                    q)
                                  (@Fin.val i.n v))
                              (DecrAlmostLinearSSSP.Decremental.Structured.data c))
                            (@LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast c.work)
                              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
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
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1022)
                                                        (instOfNatNat (nat_lit 1022)))))))
                                              C)))
                                        (@Nat.cast.{0} Real Real.instNatCast i.size))
                                      (DecrAlmostLinearSSSP.Decremental.normalWrapperOverhead a i.size))
                                    i.accuracy)
                                  (@Max.max.{0} Real Real.instMax
                                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                                    (DecrAlmostLinearSSSP.Decremental.logarithm2
                                      (@Nat.cast.{0} Real Real.instNatCast i.W))))
                                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input},
  i.Valid →
    ∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {C : Real} {a : Nat → Real} {ds : List.{0} (Fin i.k)}
      {guides : DecrAlmostLinearSSSP.Decremental.Native.BarrierGuides i p C a ds}
      {t :
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))}
      {B reserve : Nat} {b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal}
      {ptr : Fin i.n → Nat} {c : DecrAlmostLinearSSSP.Decremental.Machine},
      DecrAlmostLinearSSSP.Decremental.Native.NormalMemory i p B reserve
          (@DecrAlmostLinearSSSP.Decremental.Native.sourceAt i p C a ds guides t) b ptr
          (DecrAlmostLinearSSSP.Decremental.Structured.data c) →
        @DecrAlmostLinearSSSP.Decremental.Native.HistoryBoundary i p C a ds guides t b ptr →
          DecrAlmostLinearSSSP.Decremental.Native.GoodBoundary i ds
            (@Fin.val
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              t)
            c) ∧ (∀ (Q delta oldWork newWork index oldEnergy newEnergy initialEnergy initialSum currentSum nextSum initialWork : Nat),
  @Eq.{1} Nat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) delta currentSum) nextSum →
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) delta →
      @LE.le.{0} Nat instLENat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) newWork
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13))) oldEnergy))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) oldWork
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) Q delta))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13))) newEnergy))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
        @LE.le.{0} Nat instLENat
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) oldWork
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) index))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13))) initialEnergy))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) Q
                  (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                initialSum))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) initialWork
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) Q
                    (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                  currentSum))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13))) oldEnergy)) →
          @LE.le.{0} Nat instLENat
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) newWork
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) index
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13))) initialEnergy))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) Q
                  (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                initialSum))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) initialWork
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) Q
                    (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                  nextSum))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13))) newEnergy)))))) ∧ (((∀ (a : Nat → Real),
  DecrAlmostLinearSSSP.Decremental.Subpolynomial a →
    ∃ B,
      And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) B)
        (∀ (m : Nat),
          @LE.le.{0} Real Real.instLE (a m)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@Nat.cast.{0} Real Real.instNatCast B)
              (@Nat.cast.{0} Real Real.instNatCast
                (@Max.max.{0} Nat Nat.instMax (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))))) ∧ (∀ (C : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C →
    ∀ (a : Nat → Real),
      DecrAlmostLinearSSSP.Decremental.Subpolynomial a →
        ∃ B,
          And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) B)
            (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
              i.Valid →
                @LT.lt.{0} Real Real.instLT
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                      (@Nat.cast.{0} Real Real.instNatCast i.size))
                    i.accuracy →
                  @LE.le.{0} Real Real.instLE
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@OfNat.ofNat.{0} Real (nat_lit 64)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 64) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 63) (instOfNatNat (nat_lit 63)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 62) (instOfNatNat (nat_lit 62)))))))
                            (@Nat.cast.{0} Real Real.instNatCast i.size)))
                        (a
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64))) i.size)))
                      (@Inv.inv.{0} Real Real.instInv
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) i.accuracy
                          (@OfNat.ofNat.{0} Real (nat_lit 16)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                                (@Nat.instNeZeroSucc
                                  (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))))))))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@Nat.cast.{0} Real Real.instNatCast B)
                      (@HPow.hPow.{0, 0, 0} Real Nat Real
                        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                        (@Nat.cast.{0} Real Real.instNatCast i.size)
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program} {C : Real}
  {a : Nat → Real} {ds : List.{0} (Fin i.k)} (guides : DecrAlmostLinearSSSP.Decremental.Native.BarrierGuides i p C a ds)
  (t : Fin (@List.length.{0} (Fin i.k) ds)),
  @Eq.{1} Nat
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (DecrAlmostLinearSSSP.Decremental.Native.updateWorkPrefix i
        (@DecrAlmostLinearSSSP.Decremental.Native.sourceAt i p C a ds guides
          (@Fin.castSucc (@List.length.{0} (Fin i.k) ds) t))
        (@DecrAlmostLinearSSSP.Decremental.Native.sourceAt i p C a ds guides
          (@Fin.succ (@List.length.{0} (Fin i.k) ds) t))
        (DecrAlmostLinearSSSP.Decremental.scaleCount i))
      (@DecrAlmostLinearSSSP.Decremental.Native.sourceSumWork i p C a ds guides
        (@Fin.castSucc (@List.length.{0} (Fin i.k) ds) t)))
    (@DecrAlmostLinearSSSP.Decremental.Native.sourceSumWork i p C a ds guides
      (@Fin.succ (@List.length.{0} (Fin i.k) ds) t))) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program} {C : Real}
  {a : Nat → Real} {ds : List.{0} (Fin i.k)} (guides : DecrAlmostLinearSSSP.Decremental.Native.BarrierGuides i p C a ds)
  (t :
    Fin
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
  @LE.le.{0} Real Real.instLE
    (@Nat.cast.{0} Real Real.instNatCast (@DecrAlmostLinearSSSP.Decremental.Native.sourceSumWork i p C a ds guides t))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@Nat.cast.{0} Real Real.instNatCast (DecrAlmostLinearSSSP.Decremental.scaleCount i))
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
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))))))))) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program} {C : Real}
  {a : Nat → Real} {ds : List.{0} (Fin i.k)} (guides : DecrAlmostLinearSSSP.Decremental.Native.BarrierGuides i p C a ds)
  (coefficient : Nat),
  @LE.le.{0} Real Real.instLE
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
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
        (@Inv.inv.{0} Real Real.instInv
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            i.accuracy
            (@OfNat.ofNat.{0} Real (nat_lit 16)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))))))))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Nat.cast.{0} Real Real.instNatCast coefficient)
        (@HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
          (@Nat.cast.{0} Real Real.instNatCast i.size) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))) →
    ∀
      (t :
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
      @LE.le.{0} Nat instLENat (@DecrAlmostLinearSSSP.Decremental.Native.sourceAt i p C a ds guides t q).work
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) coefficient
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) i.size
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))) ∧ ((((∀ (C : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C →
    ∀ (a : Nat → Real),
      DecrAlmostLinearSSSP.Decremental.Subpolynomial a →
        ∃ coefficient,
          And (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))) coefficient)
            (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
              i.Valid →
                @LT.lt.{0} Real Real.instLT
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                      (@Nat.cast.{0} Real Real.instNatCast i.size))
                    i.accuracy →
                  @LE.le.{0} Real Real.instLE
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@OfNat.ofNat.{0} Real (nat_lit 64)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 64) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 63) (instOfNatNat (nat_lit 63)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 62) (instOfNatNat (nat_lit 62)))))))
                            (@Nat.cast.{0} Real Real.instNatCast i.size)))
                        (a
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64))) i.size)))
                      (@Inv.inv.{0} Real Real.instInv
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) i.accuracy
                          (@OfNat.ofNat.{0} Real (nat_lit 16)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                                (@Nat.instNeZeroSucc
                                  (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))))))))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@Nat.cast.{0} Real Real.instNatCast coefficient)
                      (@HPow.hPow.{0, 0, 0} Real Nat Real
                        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                        (@Nat.cast.{0} Real Real.instNatCast i.size)
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (C : Real) (a : Nat → Real) (ds : List.{0} (Fin i.k))
      (guides : DecrAlmostLinearSSSP.Decremental.Native.BarrierGuides i p C a ds) (coefficient : Nat)
      (c : DecrAlmostLinearSSSP.Decremental.Machine),
      DecrAlmostLinearSSSP.Decremental.Ends (DecrAlmostLinearSSSP.Decremental.Native.normalProgram coefficient p)
          (DecrAlmostLinearSSSP.Decremental.initialMachine
            (DecrAlmostLinearSSSP.Decremental.Native.normalProgram coefficient p) i)
          c →
        DecrAlmostLinearSSSP.Decremental.Native.NormalMemory i p
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) coefficient
                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                  (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) i.size
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@DecrAlmostLinearSSSP.Decremental.Native.sourceAt i p C a ds guides
              (@OfNat.ofNat.{0}
                (Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (nat_lit 0)
                (@Fin.instOfNat
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@instNeZeroNatHAdd_1 (@List.length.{0} (Fin i.k) ds)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                  (nat_lit 0))))
            (@DecrAlmostLinearSSSP.Decremental.Native.sourceInitialCache i p C a ds guides)
            (@DecrAlmostLinearSSSP.Decremental.Native.sourceInitialPointer i p C a ds guides)
            (DecrAlmostLinearSSSP.Decremental.Structured.data c) →
          Nonempty.{1}
            (DecrAlmostLinearSSSP.Decremental.Native.NormalRunState i p C a ds guides coefficient c
              (@OfNat.ofNat.{0}
                (Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (nat_lit 0)
                (@Fin.instOfNat
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@instNeZeroNatHAdd_1 (@List.length.{0} (Fin i.k) ds)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                  (nat_lit 0)))))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (C : Real) (a : Nat → Real) (ds : List.{0} (Fin i.k))
      (guides : DecrAlmostLinearSSSP.Decremental.Native.BarrierGuides i p C a ds) (coefficient : Nat)
      (initial : DecrAlmostLinearSSSP.Decremental.Machine) (t : Fin (@List.length.{0} (Fin i.k) ds)),
      @LE.le.{0} Real Real.instLE
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
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
            (@Inv.inv.{0} Real Real.instInv
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) i.accuracy
                (@OfNat.ofNat.{0} Real (nat_lit 16)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))))))))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@Nat.cast.{0} Real Real.instNatCast coefficient)
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
              (@Nat.cast.{0} Real Real.instNatCast i.size)
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))) →
        ∀
          (st :
            DecrAlmostLinearSSSP.Decremental.Native.NormalRunState i p C a ds guides coefficient initial
              (@Fin.castSucc (@List.length.{0} (Fin i.k) ds) t)),
          Nonempty.{1}
            (DecrAlmostLinearSSSP.Decremental.Native.NormalRunState i p C a ds guides coefficient initial
              (@Fin.succ (@List.length.{0} (Fin i.k) ds) t))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (C : Real) (a : Nat → Real) (ds : List.{0} (Fin i.k))
      (guides : DecrAlmostLinearSSSP.Decremental.Native.BarrierGuides i p C a ds) (coefficient : Nat)
      (initial : DecrAlmostLinearSSSP.Decremental.Machine),
      @LE.le.{0} Real Real.instLE
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
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
            (@Inv.inv.{0} Real Real.instInv
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) i.accuracy
                (@OfNat.ofNat.{0} Real (nat_lit 16)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))))))))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@Nat.cast.{0} Real Real.instNatCast coefficient)
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
              (@Nat.cast.{0} Real Real.instNatCast i.size)
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))) →
        ∀
          (st0 :
            DecrAlmostLinearSSSP.Decremental.Native.NormalRunState i p C a ds guides coefficient initial
              (@OfNat.ofNat.{0}
                (Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (nat_lit 0)
                (@Fin.instOfNat
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@instNeZeroNatHAdd_1 (@List.length.{0} (Fin i.k) ds)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                  (nat_lit 0)))),
          Nonempty.{1}
            (DecrAlmostLinearSSSP.Decremental.Native.NormalRunState i p C a ds guides coefficient initial
              (Fin.last (@List.length.{0} (Fin i.k) ds)))) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program} {C : Real}
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
        (DecrAlmostLinearSSSP.Decremental.scaleCount i))))))) ∧ (((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (m : Nat),
  @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.Native.normalMaintenanceCharge p m)
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (DecrAlmostLinearSSSP.Decremental.Native.normalUpdateConstant p)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))
          (DecrAlmostLinearSSSP.Decremental.utilityDepth m))
        (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))))) ∧ (∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (coefficient : Nat) (C : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C →
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (DecrAlmostLinearSSSP.Decremental.Native.normalProgramConstant p coefficient C))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (C : Real),
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C →
        ∀ (a : Nat → Real),
          DecrAlmostLinearSSSP.Decremental.Subpolynomial a →
            @LE.le.{0} Real Real.instLE
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@Nat.cast.{0} Real Real.instNatCast
                        (DecrAlmostLinearSSSP.Decremental.Native.normalMaintenanceCharge p i.size))
                      (@Nat.cast.{0} Real Real.instNatCast (DecrAlmostLinearSSSP.Decremental.scaleCount i)))
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@OfNat.ofNat.{0} Real (nat_lit 64)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 64) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 63) (instOfNatNat (nat_lit 63)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 62) (instOfNatNat (nat_lit 62)))))))
                            (@Nat.cast.{0} Real Real.instNatCast i.size)))
                        (a
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64))) i.size)))
                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) i.accuracy
                        (@OfNat.ofNat.{0} Real (nat_lit 16)
                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                            (@Nat.instAtLeastTwoHAddOfNat
                              (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                              (@Nat.instNeZeroSucc
                                (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))))))))))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@OfNat.ofNat.{0} Real (nat_lit 13)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 13) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))))))
                    (@Nat.cast.{0} Real Real.instNatCast i.n))
                  (@Nat.cast.{0} Real Real.instNatCast (DecrAlmostLinearSSSP.Decremental.scaleCount i))))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@Nat.cast.{0} Real Real.instNatCast
                            (DecrAlmostLinearSSSP.Decremental.Native.normalUpdateConstant p))
                          (@OfNat.ofNat.{0} Real (nat_lit 14)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 14) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
                                (@Nat.instNeZeroSucc
                                  (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))))))
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
                  (DecrAlmostLinearSSSP.Decremental.logarithm2 (@Nat.cast.{0} Real Real.instNatCast i.W))))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (coefficient : Nat) (C : Real),
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C →
        ∀ (a : Nat → Real),
          DecrAlmostLinearSSSP.Decremental.Subpolynomial a →
            ∀ (initial work : Real),
              @LE.le.{0} Real Real.instLE initial
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
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
                        (DecrAlmostLinearSSSP.Decremental.logarithm2 (@Nat.cast.{0} Real Real.instNatCast i.W))))
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) →
                @LE.le.{0} Real Real.instLE work
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) initial
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@Nat.cast.{0} Real Real.instNatCast
                              (DecrAlmostLinearSSSP.Decremental.Native.normalMaintenanceCharge p i.size))
                            (@Nat.cast.{0} Real Real.instNatCast (DecrAlmostLinearSSSP.Decremental.scaleCount i)))
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                  (@OfNat.ofNat.{0} Real (nat_lit 64)
                                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 64) Real.instNatCast
                                      (@Nat.instAtLeastTwoHAddOfNat
                                        (@OfNat.ofNat.{0} Nat (nat_lit 63) (instOfNatNat (nat_lit 63)))
                                        (@Nat.instNeZeroSucc
                                          (@OfNat.ofNat.{0} Nat (nat_lit 62) (instOfNatNat (nat_lit 62)))))))
                                  (@Nat.cast.{0} Real Real.instNatCast i.size)))
                              (a
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64))) i.size)))
                            (@HDiv.hDiv.{0, 0, 0} Real Real Real
                              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) i.accuracy
                              (@OfNat.ofNat.{0} Real (nat_lit 16)
                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                                    (@Nat.instNeZeroSucc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))))))))))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@OfNat.ofNat.{0} Real (nat_lit 13)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 13) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))))))
                          (@Nat.cast.{0} Real Real.instNatCast i.n))
                        (@Nat.cast.{0} Real Real.instNatCast (DecrAlmostLinearSSSP.Decremental.scaleCount i)))) →
                  @LE.le.{0} Real Real.instLE work
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (DecrAlmostLinearSSSP.Decremental.Native.normalProgramConstant p coefficient C)
                            (@Nat.cast.{0} Real Real.instNatCast i.size))
                          (DecrAlmostLinearSSSP.Decremental.normalWrapperOverhead a i.size))
                        i.accuracy)
                      (@Max.max.{0} Real Real.instMax
                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                        (DecrAlmostLinearSSSP.Decremental.logarithm2 (@Nat.cast.{0} Real Real.instNatCast i.W))))) ∧ (∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (C : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C →
    ∀ (a : Nat → Real),
      DecrAlmostLinearSSSP.Decremental.Subpolynomial a →
        ∀ (queryBound coefficient : Nat),
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
            (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
                i.Valid →
                  @LT.lt.{0} Real Real.instLT
                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                        (@Nat.cast.{0} Real Real.instNatCast i.size))
                      i.accuracy →
                    @LE.le.{0} Real Real.instLE
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                              (@OfNat.ofNat.{0} Real (nat_lit 64)
                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 64) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 63) (instOfNatNat (nat_lit 63)))
                                    (@Nat.instNeZeroSucc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 62) (instOfNatNat (nat_lit 62)))))))
                              (@Nat.cast.{0} Real Real.instNatCast i.size)))
                          (a
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64))) i.size)))
                        (@Inv.inv.{0} Real Real.instInv
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) i.accuracy
                            (@OfNat.ofNat.{0} Real (nat_lit 16)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))))))))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@Nat.cast.{0} Real Real.instNatCast coefficient)
                        (@HPow.hPow.{0, 0, 0} Real Nat Real
                          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                          (@Nat.cast.{0} Real Real.instNatCast i.size)
                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))) →
              ∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
                i.Valid →
                  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) i.n →
                    @LT.lt.{0} Real Real.instLT
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                          (@Nat.cast.{0} Real Real.instNatCast i.size))
                        i.accuracy →
                      DecrAlmostLinearSSSP.Decremental.Maintains
                        (DecrAlmostLinearSSSP.Decremental.Native.normalProgram coefficient p)
                        (DecrAlmostLinearSSSP.Decremental.Native.normalProgramConstant p coefficient C)
                        (DecrAlmostLinearSSSP.Decremental.normalWrapperOverhead a)
                        (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) Bool.true i))))))) := by
  exact ⟨⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Native.NormalMemory.external_input,DecrAlmostLinearSSSP.Decremental.Native.data_deletion⟩,⟨DecrAlmostLinearSSSP.Decremental.Native.normalProgram_initialization,DecrAlmostLinearSSSP.Decremental.Native.normalProgram_update⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Maintains.source_guide,DecrAlmostLinearSSSP.Decremental.adapterWrite_maxima_le⟩,⟨DecrAlmostLinearSSSP.Decremental.adapterTrace_maxima_le,⟨DecrAlmostLinearSSSP.Decremental.Ends.execute_elapsed,DecrAlmostLinearSSSP.Decremental.Native.scaleEvents_value⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Native.updateEventsPrefix_value,DecrAlmostLinearSSSP.Decremental.Native.update_cache_upper⟩,⟨DecrAlmostLinearSSSP.Decremental.Native.scale_cache_dominates,⟨DecrAlmostLinearSSSP.Decremental.Native.update_cache_dominates_prefix,DecrAlmostLinearSSSP.Decremental.Native.update_cache_dominates⟩⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Native.choose_barrier_guides,DecrAlmostLinearSSSP.Decremental.Native.live_prefix_mono⟩,⟨DecrAlmostLinearSSSP.Decremental.Native.HistoryBoundary.accurate,⟨DecrAlmostLinearSSSP.Decremental.Native.historySup_mono,DecrAlmostLinearSSSP.Decremental.Native.historySup_current⟩⟩⟩⟩⟩,⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Native.historyBoundary_initial,DecrAlmostLinearSSSP.Decremental.Native.historyBoundary_update⟩,⟨DecrAlmostLinearSSSP.Decremental.Native.normalProgram_guided_initialization,⟨DecrAlmostLinearSSSP.Decremental.Native.NormalMemory.good,DecrAlmostLinearSSSP.Decremental.Native.maintenance_credit_step⟩⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.subpolynomial_linear_envelope,DecrAlmostLinearSSSP.Decremental.normal_source_work_envelope⟩,⟨DecrAlmostLinearSSSP.Decremental.Native.sourceSumWork_update,⟨DecrAlmostLinearSSSP.Decremental.Native.sourceSumWork_uniform,DecrAlmostLinearSSSP.Decremental.Native.source_guide_reserve⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Native.choose_reserve_coefficient,DecrAlmostLinearSSSP.Decremental.Native.normalRunState_initial⟩,⟨DecrAlmostLinearSSSP.Decremental.Native.normalRunState_next,⟨DecrAlmostLinearSSSP.Decremental.Native.normalRunState_full,DecrAlmostLinearSSSP.Decremental.Native.NormalRunState.work_bound⟩⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Native.normalMaintenanceCharge_bound,DecrAlmostLinearSSSP.Decremental.Native.normalProgramConstant_positive⟩,⟨DecrAlmostLinearSSSP.Decremental.Native.normal_update_uniform_cost,⟨DecrAlmostLinearSSSP.Decremental.Native.normal_total_work_bound,DecrAlmostLinearSSSP.Decremental.Native.normalProgram_maintains⟩⟩⟩⟩⟩⟩
