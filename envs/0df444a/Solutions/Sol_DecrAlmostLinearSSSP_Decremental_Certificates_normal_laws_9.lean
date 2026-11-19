-- Prove2me | solution 1 for DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_9
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T11:22:27.033648+00:00
-- url     : https://prove2.me/submissions/5b8a5e7e-c48c-4865-814e-dd0386665509

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
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_normal_laws_5
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_normal_laws_6
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_normal_laws_7
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_normal_laws_8
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
theorem DecrAlmostLinearSSSP.Decremental.Structured.CodeAt.tail : ∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {start : Nat} {ins : DecrAlmostLinearSSSP.Decremental.Instruction}
  {rest : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction},
  DecrAlmostLinearSSSP.Decremental.Structured.CodeAt p start
      (@List.cons.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins rest) →
    DecrAlmostLinearSSSP.Decremental.Structured.CodeAt p
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      rest := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.1.2.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.ram_query_nine : ∀ (p : DecrAlmostLinearSSSP.Decremental.Program),
  @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
      (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
        DecrAlmostLinearSSSP.Decremental.Instruction
        (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
        (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code p.query)
      (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
        (DecrAlmostLinearSSSP.Decremental.Instruction.loadN
          (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
          (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))) →
    @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
          DecrAlmostLinearSSSP.Decremental.Instruction
          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) p.query
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
          (DecrAlmostLinearSSSP.Decremental.Instruction.load
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))) →
      @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
            DecrAlmostLinearSSSP.Decremental.Instruction
            (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
            (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) p.query
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
            DecrAlmostLinearSSSP.Decremental.Instruction.halt) →
        ∀ (c : DecrAlmostLinearSSSP.Decremental.Machine) (v : Nat),
          ∃ d,
            And
              (DecrAlmostLinearSSSP.Decremental.Ends p
                (have __src := DecrAlmostLinearSSSP.Decremental.resume c p.query;
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
                  (And
                    (@Eq.{1} Real (d.realReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      (c.realMem v))
                    (And (@Eq.{1} (Nat → Real) d.realMem c.realMem) (@Eq.{1} (Nat → Nat) d.natMem c.natMem))))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.1.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.Structured.eval_natural : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (d q : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.natural d q) s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    { realReg := s.realReg, natReg := @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natReg d q,
      realMem := s.realMem, natMem := s.natMem } := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.1.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Structured.eval_rational : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (d : Nat) (q : Rat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.rational d q) s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    {
      realReg :=
        @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realReg d
          (@Rat.cast.{0} Real Real.instRatCast q),
      natReg := s.natReg, realMem := s.realMem, natMem := s.natMem } := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.1.2.1.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.Structured.Eval.deterministic : ∀ {cmd : DecrAlmostLinearSSSP.Decremental.Structured.Cmd} {s t u : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {a b : Nat},
  DecrAlmostLinearSSSP.Decremental.Structured.Eval cmd s a t →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval cmd s b u →
      And (@Eq.{1} Nat a b) (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Structured.Data t u) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_3.1.2.1.2.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.Exact.TriePop.choose_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    ∃ c,
      And
        (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePop.choose s c
          (DecrAlmostLinearSSSP.Decremental.Exact.TriePop.chosen s))
        (@LE.le.{0} Nat instLENat c (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_3.2.2.2.2.1.1
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
theorem DecrAlmostLinearSSSP.Decremental.scale_positive : ∀ (j : Nat),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
    (DecrAlmostLinearSSSP.Decremental.scale j) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.1.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.delta_positive : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (j : Nat),
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (DecrAlmostLinearSSSP.Decremental.delta i j) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.1.1.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.scale_covers_distance : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (d : Real),
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
              d)) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.1.2.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.Powers.body_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.Powers.body s
    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
    (DecrAlmostLinearSSSP.Decremental.Exact.Powers.advanced s) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.1.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.Exact.Powers.Prefix.step : ∀ {bound base d : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Powers.Prefix bound base d s →
    DecrAlmostLinearSSSP.Decremental.Exact.Powers.Prefix bound base
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (DecrAlmostLinearSSSP.Decremental.Exact.Powers.advanced s) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.1.2.1.2.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.nat_weight_list_real : ∀ {k : Nat} (w : Fin k → Nat) (es : List.{0} (Fin k)),
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
        (@List.map.{0, 0} (Fin k) Real (fun e => @Nat.cast.{0} Real Real.instNatCast (w e)) es))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.2.2.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.rounded_distance_lower : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
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
            u v)) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.2.2.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.rounded_distance_upper_of_walk : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
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
                  (DecrAlmostLinearSSSP.Decremental.delta i j)))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.2.2.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.real_weight_le_walk_sum : ∀ {k : Nat} (w : Fin k → Nat) (es : List.{0} (Fin k)) (e : Fin k),
  @Membership.mem.{0, 0} (Fin k) (List.{0} (Fin k)) (@List.instMembership.{0} (Fin k)) es e →
    @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast (w e))
      (@List.sum.{0} Real Real.instAdd Real.instZero
        (@List.map.{0, 0} (Fin k) Real (fun e => @Nat.cast.{0} Real Real.instNatCast (w e)) es)) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.2.2.2.1.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.rounded_shortest_upper : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
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
                        (@Nat.cast.{0} Real Real.instNatCast i.n) (DecrAlmostLinearSSSP.Decremental.delta i j)))))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.2.2.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.distance_top_of_unreachable : ∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (active : Finset.{0} (Fin k)) (w : Fin k → ENNReal)
  (u v : Fin n),
  Not (@DecrAlmostLinearSSSP.Decremental.Reachable n k g active u v) →
    @Eq.{1} ENNReal (@DecrAlmostLinearSSSP.Decremental.distance n k g active w u v)
      (@Top.top.{0} ENNReal ENNReal.instTop) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.2.2.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.input_reachable_distance_bounds : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
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
                  (ENNReal.ofReal d))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.2.2.2.2.2.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.Ends.deterministic : ∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {c d e : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.Ends p c d →
    DecrAlmostLinearSSSP.Decremental.Ends p c e → @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine d e := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_8.2.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.OnlineRun.length : ∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {i : DecrAlmostLinearSSSP.Decremental.Input} {ds : List.{0} (Fin i.k)}
  {cs : List.{0} DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.OnlineRun p i ds cs →
    @Eq.{1} Nat (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Machine cs)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_8.2.2.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.ScaledCeiling.choose_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.ScaledCeiling.chooseBody s
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.chooseStep s) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_1.1.1.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.PreservesOutside.refl : ∀ (base F : Nat) (c : DecrAlmostLinearSSSP.Decremental.Machine),
  DecrAlmostLinearSSSP.Decremental.PreservesOutside base F c c := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_2.1.1.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.PreservesOutside.trans : ∀ {base F : Nat} {c d e : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.PreservesOutside base F c d →
    DecrAlmostLinearSSSP.Decremental.PreservesOutside base F d e →
      DecrAlmostLinearSSSP.Decremental.PreservesOutside base F c e := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_2.1.1.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.Structured.NatFrame.flag : ∀ {cmd : DecrAlmostLinearSSSP.Decremental.Structured.Cmd} {k : Nat},
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame cmd k →
    DecrAlmostLinearSSSP.Decremental.Structured.FlagFrame cmd k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_2.1.1.2.2.1.2
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
theorem DecrAlmostLinearSSSP.Decremental.barrier_low_cost : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (j : Nat) (e : Fin i.k),
      @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast (i.weight e))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
            (DecrAlmostLinearSSSP.Decremental.scale j)) →
        And
          (@LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast (i.weight e))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (DecrAlmostLinearSSSP.Decremental.delta i j)
              (@Nat.cast.{0} Real Real.instNatCast (DecrAlmostLinearSSSP.Decremental.barrierWeight i j e))))
          (@LE.le.{0} Real Real.instLE
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (DecrAlmostLinearSSSP.Decremental.delta i j)
              (@Nat.cast.{0} Real Real.instNatCast (DecrAlmostLinearSSSP.Decremental.barrierWeight i j e)))
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@Nat.cast.{0} Real Real.instNatCast (i.weight e)) (DecrAlmostLinearSSSP.Decremental.delta i j))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_3.1.1.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.barrier_high_cost : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (j : Nat) (e : Fin i.k),
      Not
          (@LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast (i.weight e))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              (DecrAlmostLinearSSSP.Decremental.scale j))) →
        @LE.le.{0} Real Real.instLE
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 4)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
            (DecrAlmostLinearSSSP.Decremental.scale j))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (DecrAlmostLinearSSSP.Decremental.delta i j)
            (@Nat.cast.{0} Real Real.instNatCast (DecrAlmostLinearSSSP.Decremental.barrierWeight i j e))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_3.1.1.2.1.2.2
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
theorem DecrAlmostLinearSSSP.Decremental.shadowReg_ne_of_even : ∀ (j d : Nat), @Even.{0} Nat instAddNat d → @Ne.{1} Nat (DecrAlmostLinearSSSP.Decremental.shadowReg j) d := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_4.1.2.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.TailFrame.seq : ∀ {a b : DecrAlmostLinearSSSP.Decremental.Structured.Cmd},
  DecrAlmostLinearSSSP.Decremental.TailFrame a →
    DecrAlmostLinearSSSP.Decremental.TailFrame b → DecrAlmostLinearSSSP.Decremental.TailFrame (a.seq b) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_4.2.1.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.tailFrame_atoms : ∀ (atoms : List.{0} DecrAlmostLinearSSSP.Decremental.Structured.Atom),
  (∀ (a : DecrAlmostLinearSSSP.Decremental.Structured.Atom),
      @Membership.mem.{0, 0} DecrAlmostLinearSSSP.Decremental.Structured.Atom
          (List.{0} DecrAlmostLinearSSSP.Decremental.Structured.Atom)
          (@List.instMembership.{0} DecrAlmostLinearSSSP.Decremental.Structured.Atom) atoms a →
        DecrAlmostLinearSSSP.Decremental.EvenRegisterWrites a.instruction) →
    DecrAlmostLinearSSSP.Decremental.TailFrame
      (DecrAlmostLinearSSSP.Decremental.Structured.sequence
        (@List.map.{0, 0} DecrAlmostLinearSSSP.Decremental.Structured.Atom
          DecrAlmostLinearSSSP.Decremental.Structured.Cmd DecrAlmostLinearSSSP.Decremental.Structured.Cmd.atom atoms)) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_4.2.1.2.1.2.2.2
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
theorem DecrAlmostLinearSSSP.Decremental.CacheCopy.suffix_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CacheCopy.suffix s
    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
    (DecrAlmostLinearSSSP.Decremental.CacheCopy.suffixData s) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_5.2.2.1.1.2.2
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
theorem DecrAlmostLinearSSSP.Decremental.Native.ScaleMemory.same_memory : ∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program}
  {B j record cache next : Nat} {g : DecrAlmostLinearSSSP.Decremental.Machine} {b : Fin i.n → ENNReal}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.ScaleMemory i p B j record cache next g b s →
    @Eq.{1} (Nat → Nat) t.natMem s.natMem →
      @Eq.{1} (Nat → Real) t.realMem s.realMem →
        DecrAlmostLinearSSSP.Decremental.Native.ScaleMemory i p B j record cache next g b t := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_7.1.2.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.LinkedScan.eval_loop : ∀ (rows : List.{0} DecrAlmostLinearSSSP.Decremental.LinkedScan.Row)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (vertex : Nat),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
      (DecrAlmostLinearSSSP.Decremental.LinkedScan.headAddress rows) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 38) (instOfNatNat (nat_lit 38)))) vertex →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 34) (instOfNatNat (nat_lit 34))))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 36) (instOfNatNat (nat_lit 36))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
            DecrAlmostLinearSSSP.Decremental.LinkedScan.RowsView s vertex rows →
              ∃ cost t,
                And
                  (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.LinkedScan.loop s
                    cost t)
                  (And
                    (@LE.le.{0} Nat instLENat cost
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
                          (DecrAlmostLinearSSSP.Decremental.LinkedScan.skipped rows))
                        (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))))
                    (And
                      (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
                        (DecrAlmostLinearSSSP.Decremental.LinkedScan.selectedAddress rows))
                      (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_8.1.1.1.2.1.2
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
theorem DecrAlmostLinearSSSP.Decremental.adapterInitialize_pointer_valid : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input)
  (b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal) (v : Fin i.n),
  DecrAlmostLinearSSSP.Decremental.PointerValid i b v
    (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i (DecrAlmostLinearSSSP.Decremental.adapterInitialize i b)
      v) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_8.1.1.2.2.1.1
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
theorem DecrAlmostLinearSSSP.Decremental.Native.pointerStart_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Native.pointerStart s
    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
    (DecrAlmostLinearSSSP.Decremental.Native.pointerStartData s) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_8.2.1.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.PointerBases.body : ∀ {record pointer flags list cost : Nat} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.PointerBases record pointer flags list s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Native.pointerBody s cost t →
      DecrAlmostLinearSSSP.Decremental.Native.PointerBases record pointer flags list t := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_8.2.2.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.Native.tailFrame_pointerLoop : DecrAlmostLinearSSSP.Decremental.TailFrame DecrAlmostLinearSSSP.Decremental.Native.pointerLoop := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_8.2.2.1.2.1.2
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
theorem DecrAlmostLinearSSSP.Decremental.Native.PublicFrame.refl : ∀ (l : DecrAlmostLinearSSSP.Decremental.Native.PointerLayout) (n : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data), DecrAlmostLinearSSSP.Decremental.Native.PublicFrame l n s s := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_8.2.2.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.Native.PublicFrame.trans : ∀ {l : DecrAlmostLinearSSSP.Decremental.Native.PointerLayout} {n : Nat}
  {s t u : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.PublicFrame l n s t →
    DecrAlmostLinearSSSP.Decremental.Native.PublicFrame l n t u →
      DecrAlmostLinearSSSP.Decremental.Native.PublicFrame l n s u := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_8.2.2.2.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.pointerPrefix_loop : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (B reserve N : Nat)
  (b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal) (done : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Native.PointerPrefix i B reserve N b done s →
    ∃ cost t,
      And
        (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Native.pointerLoop s cost t)
        (And (DecrAlmostLinearSSSP.Decremental.Native.PointerPrefix i B reserve N b i.n t)
          (And
            (@LE.le.{0} Nat instLENat cost
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
                      (DecrAlmostLinearSSSP.Decremental.scaleCount i))
                    (@OfNat.ofNat.{0} Nat (nat_lit 28) (instOfNatNat (nat_lit 28))))
                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) i.n done))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (DecrAlmostLinearSSSP.Decremental.Native.PublicFrame
              (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N)
              i.n s t))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_8.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.pointerStart_nat_frame : ∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 182) (instOfNatNat (nat_lit 182))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 180) (instOfNatNat (nat_lit 180))) →
        DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Native.pointerStart k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_8.2.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Native.pointerStart_real_frame : ∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Native.pointerStart k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_8.2.2.2.2.2.2.2
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
lemma pointerStart_no_memory : NoMemory pointerStart := by
  simp [pointerStart,pointerStartAtoms,Structured.sequence,NoMemory,NoStore]
lemma globalFrame_pointerStart : GlobalFrame pointerStart := by
  constructor
  · intro k hk
    have hhi : k ≤ 74 := by simp only [globalNat,List.mem_cons,List.not_mem_nil,or_false] at hk;omega
    apply pointerStart_nat_frame <;> omega
  · intro k hk
    exact pointerStart_real_frame k
lemma PointerBases.start {record pointer flags list cost : ℕ} {s t : Data}
    (h : PointerBases record pointer flags list s) (he : Eval pointerStart s cost t) : PointerBases record pointer flags list t := by
  have hn (k : ℕ) (hk : k ∈ ([84,96,98,102] : List ℕ)) : t.natReg k = s.natReg k := by
    apply he.nat_frame
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl
    all_goals apply pointerStart_nat_frame <;> norm_num
  exact ⟨(hn 84 (by simp)).trans h.record,(hn 96 (by simp)).trans h.pointer,
    (hn 98 (by simp)).trans h.flags,(hn 102 (by simp)).trans h.list⟩
lemma PointerPrefix.dirty_view {i : Input} {B reserve N : ℕ}
    {b : Fin (scaleCount i) → Fin i.n → ℝ≥0∞} {s : Data} (h : PointerPrefix i B reserve N b i.n s) :
    DirtyMark.View (pointerLayout B i.n (scaleCount i) reserve N).flags
      (pointerLayout B i.n (scaleCount i) reserve N).list (List.finRange i.n) s := by
  constructor
  · exact List.nodup_finRange i.n
  · intro v
    simpa [List.mem_finRange] using h.flags v v.isLt
  · intro r hr
    have hrn : r < i.n := by simpa only [List.length_finRange] using hr
    simpa only [List.getElem_finRange,Fin.coe_cast,Fin.val_mk] using h.entries r hrn
  · simpa only [List.length_finRange] using h.count
  · simpa only [List.length_finRange] using h.writer
lemma buildPointers_eval (i : Input) (B reserve N : ℕ) (b : Fin (scaleCount i) → Fin i.n → ℝ≥0∞)
    (s : Data)
    (hg : Globals i B (scaleLayout B i.n (scaleCount i) reserve N).utility s)
    (hb : PointerBases (pointerLayout B i.n (scaleCount i) reserve N).record
      (pointerLayout B i.n (scaleCount i) reserve N).pointer (pointerLayout B i.n (scaleCount i) reserve N).flags
      (pointerLayout B i.n (scaleCount i) reserve N).list s)
    (ht : ScanTable i (pointerLayout B i.n (scaleCount i) reserve N).record
      (pointerLayout B i.n (scaleCount i) reserve N).cache (2*N+8) b s) :
    ∃ cost t, Eval buildPointers s cost t ∧ cost ≤ (13*scaleCount i+28)*i.n+5 ∧
      PointerPrefix i B reserve N b i.n t ∧
      PublicFrame (pointerLayout B i.n (scaleCount i) reserve N) i.n s t := by
  let u := pointerStartData s
  have hu := pointerStart_eval s
  have hug := hg.transfer hu globalFrame_pointerStart
  have hub := hb.start hu
  have hm := hu.no_memory pointerStart_no_memory
  have hut : ScanTable i (pointerLayout B i.n (scaleCount i) reserve N).record
      (pointerLayout B i.n (scaleCount i) reserve N).cache (2*N+8) b u :=
    ht.frame_above (pointerLayout_order B i.n (scaleCount i) reserve N).1 (fun address _ => ⟨congrFun hm.2 address,congrFun hm.1 address⟩)
  have hus : PointerPrefix i B reserve N b 0 u := by
    constructor
    · omega
    · exact hug
    · exact hub
    · simp [u,pointerStartData,pointerStartAtoms,Atom.effect,instructionEffect,data,Data.machine]
    · simp [u,pointerStartData,pointerStartAtoms,Atom.effect,instructionEffect,data,Data.machine]
    · simp [u,pointerStartData,pointerStartAtoms,Atom.effect,instructionEffect,data,Data.machine,hg.zeroN,hb.list]
    · exact hut
    · intro v hv;omega
    · intro v hv;omega
    · intro r hr;omega
  obtain ⟨c,t,he,hstate,hcost,hframe⟩ := pointerPrefix_loop i B reserve N b 0 u hus
  have hstartframe : PublicFrame (pointerLayout B i.n (scaleCount i) reserve N) i.n s u :=
    fun address _ => ⟨congrFun hm.2 address,congrFun hm.1 address⟩
  refine ⟨3+c,t,Eval.seq hu he,?_,hstate,hstartframe.trans hframe⟩
  simp only [Nat.sub_zero] at hcost
  omega
lemma tailFrame_pointerStart : TailFrame pointerStart := by
  apply tailFrame_atoms
  norm_num [pointerStartAtoms,EvenRegisterWrites]
lemma tailFrame_buildPointers : TailFrame buildPointers := tailFrame_pointerStart.seq tailFrame_pointerLoop
end DecrAlmostLinearSSSP.Decremental.Native
end s190
section s191
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.PointerRead
open Structured
lemma eval_code (s : Data) (hz : s.natReg 56 = 0) :
    ∃ cost t, Eval code s cost t ∧ cost ≤ 6 ∧
      t.natReg 22 = (if pointer s = 0 then 1 else s.natMem (cellAddress s)) ∧
      t.realReg 20 = (if pointer s = 0 then 0 else s.realMem (cellAddress s)) ∧
      t.realMem = s.realMem ∧ t.natMem = s.natMem := by
  let a : Data := {s with natReg := Function.update s.natReg 30 (pointer s)}
  have ha : Eval (loadN 30 196) s 1 a := eval_loadN s 30 196
  by_cases hp : pointer s = 0
  · have htest : ¬(Test.natLess 56 30).holds a := by simp [Test.holds,a,hz,hp]
    let b : Data := {a with natReg := Function.update a.natReg 22 1}
    let t : Data := {b with realReg := Function.update b.realReg 20 0}
    have hb : Eval (natural 22 1) a 1 b := eval_natural a 22 1
    have ht : Eval (rational 20 0) b 1 t := by simpa [t] using eval_rational b 20 0
    refine ⟨5,t,Eval.seq ha (Eval.branchNo htest (Eval.seq hb (Eval.seq ht (Eval.skip t)))),by omega,?_,?_,rfl,rfl⟩
    · simp [t,b,if_pos hp]
    · simp [t,if_pos hp]
  · have hpos : 0 < pointer s := by omega
    have htest : (Test.natLess 56 30).holds a := by simpa [Test.holds,a,hz] using hpos
    let b : Data := {a with natReg := Function.update a.natReg 44 (s.natMem (pointer s))}
    let c : Data := {b with natReg := Function.update b.natReg 20 (cellAddress s)}
    let d : Data := {c with natReg := Function.update c.natReg 22 (s.natMem (cellAddress s))}
    let t : Data := {d with realReg := Function.update d.realReg 20 (s.realMem (cellAddress s))}
    have hb : Eval (loadN 44 30) a 1 b := by simpa only [a,b,Function.update_self] using eval_loadN a 44 30
    have hc : Eval (nadd 20 44 38) b 1 c := by
      simpa [c,b,a,cellAddress] using eval_nadd b 20 44 38
    have hd : Eval (loadN 22 20) c 1 d := by simpa only [d,c,Function.update_self] using eval_loadN c 22 20
    have ht : Eval (load 20 20) d 1 t := by simpa [t,d,c] using eval_load d 20 20
    refine ⟨6,t,Eval.seq ha (Eval.branchYes htest (Eval.seq hb (Eval.seq hc (Eval.seq hd (Eval.seq ht (Eval.skip t)))))),le_rfl,?_,?_,rfl,rfl⟩
    · simp [t,d,if_neg hp]
    · simp [t,if_neg hp]
lemma incoming_value (s : Data) (hz : s.natReg 56 = 0) :
    ∃ cost t, Eval code s cost t ∧ cost ≤ 6 ∧
      ExtendedMax.incoming t = (if pointer s = 0 then ⊤ else ExtendedMax.cell s (cellAddress s)) ∧
      t.realMem = s.realMem ∧ t.natMem = s.natMem := by
  obtain ⟨cost,t,he,hcost,hn,hr,hmr,hmn⟩ := eval_code s hz
  refine ⟨cost,t,he,hcost,?_,hmr,hmn⟩
  by_cases hp : pointer s = 0 <;> simp [ExtendedMax.incoming,ExtendedMax.cell,hn,hr,hp]
lemma no_memory : NoMemory code := by
  simp [code,Structured.sequence,NoMemory,loadN,nadd,load,Structured.natural,rational,NoStore]
end DecrAlmostLinearSSSP.Decremental.PointerRead
end s191
section s192
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.SelectedRead
open Structured
attribute [local instance] Classical.propDecidable
lemma prefix_eval (s : Data) : Eval prefixCode s 2 (prefixData s) := eval_sequence_atoms prefixAtoms s
lemma prefix_fields (s : Data) :
    (prefixData s).natReg 38 = 2*s.natReg 94 ∧
    (prefixData s).natReg 196 = s.natReg 96+2*s.natReg 94 ∧
    (∀ k, k ≠ 38 → k ≠ 196 → (prefixData s).natReg k = s.natReg k) := by
  simp [prefixData,prefixAtoms,Atom.effect,instructionEffect,data,Data.machine,two_mul]
  intro k h38 h196
  simp [h38,h196]
lemma no_memory : NoMemory code := by
  simp [code,chooseCode,prefixCode,prefixAtoms,zeroCode,Structured.sequence,NoMemory,
    NoStore,PointerRead.no_memory,natural,rational]
lemma choose_eval (s : Data) (hz : s.natReg 56 = 0) :
    ∃ cost t, Eval chooseCode s cost t ∧ cost ≤ 9 ∧
      ExtendedMax.incoming t = (if s.natReg 94 = s.natReg 72 then 0
        else if PointerRead.pointer s = 0 then ⊤ else ExtendedMax.cell s (PointerRead.cellAddress s)) := by
  by_cases hlt : s.natReg 94 < s.natReg 72
  · obtain ⟨c,t,he,hc,hv,_,_⟩ := PointerRead.incoming_value s hz
    refine ⟨c+1,t,Eval.branchYes hlt he,by omega,?_⟩
    simpa [if_neg (show s.natReg 94 ≠ s.natReg 72 by omega)] using hv
  · by_cases hgt : s.natReg 72 < s.natReg 94
    · obtain ⟨c,t,he,hc,hv,_,_⟩ := PointerRead.incoming_value s hz
      refine ⟨c+1+2,t,Eval.branchNo hlt (Eval.branchYes hgt he),by omega,?_⟩
      simpa [if_neg (show s.natReg 94 ≠ s.natReg 72 by omega)] using hv
    · have heq : s.natReg 94 = s.natReg 72 := by omega
      let a : Data := {s with natReg := Function.update s.natReg 22 0}
      let t : Data := {a with realReg := Function.update a.realReg 20 0}
      have ha : Eval (natural 22 0) s 1 a := eval_natural s 22 0
      have ht : Eval (rational 20 0) a 1 t := by simpa [t] using eval_rational a 20 0
      refine ⟨6,t,Eval.branchNo hlt (Eval.branchNo hgt (Eval.seq ha (Eval.seq ht (Eval.skip t)))),by omega,?_⟩
      simp [ExtendedMax.incoming,t,a,heq]
lemma eval_code (s : Data) (hz : s.natReg 56 = 0) :
    ∃ cost t, Eval code s cost t ∧ cost ≤ 11 ∧
      ExtendedMax.incoming t = value s ∧ t.realMem = s.realMem ∧ t.natMem = s.natMem := by
  let a := prefixData s
  obtain ⟨h38,h196,hregs⟩ := prefix_fields s
  have ha56 : a.natReg 56 = 0 := (hregs 56 (by omega) (by omega)).trans hz
  change a.natReg 38 = _ at h38
  change a.natReg 196 = _ at h196
  change ∀ k, k ≠ 38 → k ≠ 196 → a.natReg k = s.natReg k at hregs
  have hmN : a.natMem = s.natMem := rfl
  have hmR : a.realMem = s.realMem := rfl
  obtain ⟨c,t,he,hc,hv⟩ := choose_eval a ha56
  have hall : Eval code s (2+c) t := Eval.seq (prefix_eval s) he
  obtain ⟨hr,hn⟩ := hall.no_memory no_memory
  refine ⟨2+c,t,hall,by omega,?_,hr,hn⟩
  simpa only [value,PointerRead.pointer,PointerRead.cellAddress,ExtendedMax.cell,h38,h196,hmN,hmR,
    hregs 94 (by omega) (by omega),hregs 72 (by omega) (by omega)] using hv
lemma choose_fields {s t : Data} {cost : ℕ} (hz : s.natReg 56 = 0)
    (he : Eval chooseCode s cost t) :
    t.natReg 22 = (if s.natReg 94 = s.natReg 72 then 0
      else if PointerRead.pointer s = 0 then 1 else s.natMem (PointerRead.cellAddress s)) ∧
    t.realReg 20 = (if s.natReg 94 = s.natReg 72 then 0
      else if PointerRead.pointer s = 0 then 0 else s.realMem (PointerRead.cellAddress s)) := by
  unfold chooseCode at he
  cases he with
  | branchYes ht he =>
    obtain ⟨c,u,hu,_,hn,hr,_,_⟩ := PointerRead.eval_code s hz
    obtain ⟨_,rfl⟩ := he.deterministic hu
    have hne : s.natReg 94 ≠ s.natReg 72 := by change s.natReg 94 < s.natReg 72 at ht;omega
    simpa only [if_neg hne] using And.intro hn hr
  | branchNo ht he =>
    cases he with
    | branchYes ht' he =>
      obtain ⟨c,u,hu,_,hn,hr,_,_⟩ := PointerRead.eval_code s hz
      obtain ⟨_,rfl⟩ := he.deterministic hu
      have hne : s.natReg 94 ≠ s.natReg 72 := by change s.natReg 72 < s.natReg 94 at ht';omega
      simpa only [if_neg hne] using And.intro hn hr
    | branchNo ht' he =>
      have heq : s.natReg 94 = s.natReg 72 := by
        change ¬s.natReg 94 < s.natReg 72 at ht
        change ¬s.natReg 72 < s.natReg 94 at ht'
        omega
      let a : Data := {s with natReg := Function.update s.natReg 22 0}
      let u : Data := {a with realReg := Function.update a.realReg 20 0}
      have ha : Eval (natural 22 0) s 1 a := eval_natural s 22 0
      have hu : Eval (rational 20 0) a 1 u := by simpa [u] using eval_rational a 20 0
      have he' : Eval zeroCode s 2 u := Eval.seq ha (Eval.seq hu (Eval.skip u))
      obtain ⟨_,rfl⟩ := he.deterministic he'
      simp [u,a,heq]
lemma fields {s t : Data} {cost : ℕ} (hz : s.natReg 56 = 0)
    (he : Eval code s cost t) : t.natReg 22 = flag s ∧ t.realReg 20 = realValue s := by
  unfold code at he
  cases he with
  | seq hp hc =>
    obtain ⟨_,rfl⟩ := hp.deterministic (prefix_eval s)
    obtain ⟨h38,h196,hregs⟩ := prefix_fields s
    have hz' : (prefixData s).natReg 56 = 0 := (hregs 56 (by omega) (by omega)).trans hz
    have hmN : (prefixData s).natMem = s.natMem := rfl
    have hmR : (prefixData s).realMem = s.realMem := rfl
    have hh := choose_fields hz' hc
    simpa only [flag,realValue,PointerRead.pointer,PointerRead.cellAddress,h38,h196,hmN,hmR,
      hregs 94 (by omega) (by omega),hregs 72 (by omega) (by omega)] using hh
lemma normalized {s t : Data} {cost : ℕ} (hz : s.natReg 56 = 0)
    (he : Eval code s cost t) (hf : flag s ≤ 1) (hr : flag s = 0 → 0 ≤ realValue s) :
    t.natReg 22 ≤ 1 ∧ (t.natReg 22 = 0 → 0 ≤ t.realReg 20) := by
  obtain ⟨hn,hv⟩ := fields hz he
  simpa only [hn,hv] using And.intro hf hr
lemma nat_frame (k : ℕ) (h30 : k ≠ 30) (h38 : k ≠ 38) (h196 : k ≠ 196)
    (h44 : k ≠ 44) (h20 : k ≠ 20) (h22 : k ≠ 22) : NatFrame code k := by
  simp [code,chooseCode,prefixCode,prefixAtoms,zeroCode,PointerRead.code,Structured.sequence,
    NatFrame,writesNat,natural,rational,loadN,nadd,load,Ne.symm h30,Ne.symm h38,Ne.symm h196,Ne.symm h44,Ne.symm h20,Ne.symm h22]
end DecrAlmostLinearSSSP.Decremental.SelectedRead
end s192
section s193
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.AnswerTable
open Structured
attribute [local instance] Classical.propDecidable
lemma Image.frame {n : ℕ} {l : Layout n} {s t : Data} (h : Image l s)
    (hf : ∀ address, Protected l address → t.natMem address = s.natMem address ∧
      t.realMem address = s.realMem address) : Image l t := by
  constructor
  · intro v
    exact (hf _ (Or.inl ⟨v,rfl⟩)).1.trans (h.pointers v)
  · intro v hv
    obtain ⟨hc,hn,hr⟩ := h.caches v hv
    exact ⟨(hf _ (Or.inr ⟨v,hv,Or.inl rfl⟩)).1.trans hc,
      (hf _ (Or.inr ⟨v,hv,Or.inr rfl⟩)).1.trans hn,
      (hf _ (Or.inr ⟨v,hv,Or.inr rfl⟩)).2.trans hr⟩
lemma read_fields {n : ℕ} (l : Layout n) (s : Data) (v : Fin n) (himage : Image l s)
    (hp : s.natReg 96 = l.pointerBase) (hs : s.natReg 72 = l.source.val)
    (hv : s.natReg 94 = v.val) :
    SelectedRead.flag s = l.flag v ∧ SelectedRead.realValue s = l.realValue v := by
  have heq : s.natReg 94 = s.natReg 72 ↔ v = l.source := by
    rw [hv,hs]
    exact Fin.val_inj
  have heqv : v.val = l.source.val ↔ v = l.source := Fin.val_inj
  by_cases hvs : v = l.source
  · simp [SelectedRead.flag,SelectedRead.realValue,Layout.flag,Layout.realValue,hp,hv,hs,heqv,hvs]
  · by_cases hz : l.record v = 0
    · simp [SelectedRead.flag,SelectedRead.realValue,Layout.flag,Layout.realValue,hp,hv,hs,heqv,hvs,hp,hv,himage.pointers,hz]
    · obtain ⟨hc,hn,hr⟩ := himage.caches v hz
      simp [SelectedRead.flag,SelectedRead.realValue,Layout.flag,Layout.realValue,hv,hs,heqv,if_neg hvs,
        hp,hv,himage.pointers,hc,if_neg hz,hn,hr]
lemma Image.same_memory {n : ℕ} {l : Layout n} {s t : Data} (h : Image l s)
    (hn : t.natMem = s.natMem) (hr : t.realMem = s.realMem) : Image l t :=
  h.frame (fun address _ => ⟨congrFun hn address,congrFun hr address⟩)
lemma normalized {n : ℕ} (l : Layout n)
    (hf : ∀ v, l.cacheFlag v ≤ 1) (hr : ∀ v, l.cacheFlag v = 0 → 0 ≤ l.cacheReal v) :
    ∀ v, l.flag v ≤ 1 ∧ (l.flag v = 0 → 0 ≤ l.realValue v) := by
  intro v
  by_cases hs : v = l.source
  · simp [Layout.flag,Layout.realValue,hs]
  · by_cases hz : l.record v = 0
    · simp [Layout.flag,Layout.realValue,hs,hz]
    · simpa [Layout.flag,Layout.realValue,hs,hz] using And.intro (hf v) (hr v)
end DecrAlmostLinearSSSP.Decremental.AnswerTable
end s193
section s194
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
attribute [local instance] Classical.propDecidable
lemma scanRecord_nonzero {i : Input} {base stride j : ℕ} (hbase : 0 < base) :
    scanRecord i base stride j ≠ 0 ↔ j < scaleCount i := by
  by_cases hj : j < scaleCount i
  · have hpos : 0 < recordAt base stride j := by dsimp [recordAt];omega
    simp only [scanRecord,if_pos hj]
    exact iff_of_true (Nat.ne_of_gt hpos) hj
  · simp [scanRecord,hj]
lemma answerLayout_image (i : Input) (recordBase cacheBase stride pointerBase : ℕ)
    (p : Fin i.n → ℕ) (s : Data) (b : Fin (scaleCount i) → Fin i.n → ℝ≥0∞)
    (ht : ScanTable i recordBase cacheBase stride b s)
    (hp : ∀ v, s.natMem (pointerBase+2*v.val) = scanRecord i recordBase stride (p v)) :
    AnswerTable.Image (answerLayout i recordBase cacheBase stride pointerBase p s) s := by
  constructor
  · exact hp
  · intro v hv
    have hj : p v < scaleCount i := (scanRecord_nonzero ht.positive).mp hv
    have hm := ht.metadata ⟨p v,hj⟩
    refine ⟨?_,rfl,rfl⟩
    simpa only [answerLayout,scanRecord,answerCache,if_pos hj] using hm.cachebase
lemma answerLayout_normal (i : Input) (recordBase cacheBase stride pointerBase : ℕ)
    (p : Fin i.n → ℕ) (s : Data) (b : Fin (scaleCount i) → Fin i.n → ℝ≥0∞)
    (ht : ScanTable i recordBase cacheBase stride b s) :
    ∀ v, (answerLayout i recordBase cacheBase stride pointerBase p s).flag v ≤ 1 ∧
      ((answerLayout i recordBase cacheBase stride pointerBase p s).flag v = 0 →
        0 ≤ (answerLayout i recordBase cacheBase stride pointerBase p s).realValue v) := by
  intro v
  by_cases hs : v = i.source
  · simp [answerLayout,AnswerTable.Layout.flag,AnswerTable.Layout.realValue,hs]
  · by_cases hj : p v < scaleCount i
    · have hne : scanRecord i recordBase stride (p v) ≠ 0 := (scanRecord_nonzero ht.positive).mpr hj
      have hc := ht.cache ⟨p v,hj⟩
      simpa only [answerLayout,AnswerTable.Layout.flag,AnswerTable.Layout.realValue,if_neg hs,if_neg hne,
        answerCache,if_pos hj] using And.intro (hc.flags v) (hc.finite v)
    · simp [answerLayout,AnswerTable.Layout.flag,AnswerTable.Layout.realValue,hs,scanRecord,hj]
lemma answerLayout_value (i : Input) (recordBase cacheBase stride pointerBase : ℕ)
    (p : Fin i.n → ℕ) (s : Data) (b : Fin (scaleCount i) → Fin i.n → ℝ≥0∞)
    (ht : ScanTable i recordBase cacheBase stride b s) (v : Fin i.n) :
    (if (answerLayout i recordBase cacheBase stride pointerBase p s).flag v = 1 then (⊤ : ℝ≥0∞)
      else ENNReal.ofReal ((answerLayout i recordBase cacheBase stride pointerBase p s).realValue v)) = selected i b p v := by
  by_cases hs : v = i.source
  · simp [answerLayout,AnswerTable.Layout.flag,AnswerTable.Layout.realValue,hs,selected]
  · by_cases hj : p v < scaleCount i
    · have hne : scanRecord i recordBase stride (p v) ≠ 0 := (scanRecord_nonzero ht.positive).mpr hj
      have hc := ht.cache ⟨p v,hj⟩
      simpa only [answerLayout,AnswerTable.Layout.flag,AnswerTable.Layout.realValue,if_neg hs,if_neg hne,
        answerCache,if_pos hj,selected,dif_pos hj,ExtendedMax.cell] using hc.value v
    · simp [answerLayout,AnswerTable.Layout.flag,AnswerTable.Layout.realValue,hs,scanRecord,hj,selected]
end DecrAlmostLinearSSSP.Decremental.Native
end s194
section s195
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
lemma answerLayout_protected (i : Input) (B reserve N : ℕ) (s : Data)
    (b : Fin (scaleCount i) → Fin i.n → ℝ≥0∞) (p : Fin i.n → ℕ)
    (ht : ScanTable i (pointerLayout B i.n (scaleCount i) reserve N).record
      (pointerLayout B i.n (scaleCount i) reserve N).cache (2*N+8) b s) (hB : i.n ≤ B) :
    ∀ address, AnswerTable.Protected
      (answerLayout i (pointerLayout B i.n (scaleCount i) reserve N).record
        (pointerLayout B i.n (scaleCount i) reserve N).cache (2*N+8)
        (pointerLayout B i.n (scaleCount i) reserve N).pointer p s) address →
      i.n ≤ address ∧ ∀ v : Fin i.n, address ≠ (pointerLayout B i.n (scaleCount i) reserve N).flags+2*v.val := by
  let l := pointerLayout B i.n (scaleCount i) reserve N
  have ho := pointerLayout_order B i.n (scaleCount i) reserve N
  have hnr : i.n ≤ l.record := by dsimp [l,pointerLayout,scaleLayout,Layout.addresses];omega
  have hlist : l.list ≤ l.record := by dsimp [l,pointerLayout,scaleLayout,Layout.addresses];omega
  have habove : ∀ address, l.record ≤ address → i.n ≤ address ∧ ∀ v : Fin i.n, address ≠ l.flags+2*v.val := by
    intro address ha
    refine ⟨by omega,?_⟩
    intro v
    have hh : l.flags+2*v.val < l.list := ho.2.2.1 v.val v.isLt
    omega
  intro address haddr
  rcases haddr with ⟨v,rfl⟩ | ⟨v,hv,hvaddr⟩
  · change i.n ≤ l.pointer+2*v.val ∧ ∀ w : Fin i.n, l.pointer+2*v.val ≠ l.flags+2*w.val
    constructor
    · dsimp [l,pointerLayout,scaleLayout,Layout.addresses]
      omega
    · intro w
      have hh : l.pointer+2*v.val < l.flags := ho.2.1 v.val v.isLt
      omega
  · have hj : p v < scaleCount i := (scanRecord_nonzero ht.positive).mp hv
    rcases hvaddr with rfl | rfl
    · change i.n ≤ scanRecord i l.record (2*N+8) (p v) ∧ ∀ w : Fin i.n, scanRecord i l.record (2*N+8) (p v) ≠ l.flags+2*w.val
      rw [scanRecord,if_pos hj]
      apply habove
      dsimp [recordAt]
      omega
    · change i.n ≤ answerCache i l.cache p v+2*v.val ∧ ∀ w : Fin i.n, answerCache i l.cache p v+2*v.val ≠ l.flags+2*w.val
      rw [answerCache,if_pos hj]
      apply habove
      have hcache : l.record ≤ l.cache := ho.1
      dsimp [cacheAt]
      omega
end DecrAlmostLinearSSSP.Decremental.Native
end s195
section s196
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.DirtyCommit
open Structured
lemma suffix_eval (s : Data) : Eval suffix s 6 (afterStores s) := by
  have he := Eval.seq (eval_storeN s 94 22) (Eval.seq (eval_store _ 94 20)
    (Eval.seq (eval_nadd _ 184 98 38) (Eval.seq (eval_storeN _ 184 56)
      (Eval.seq (eval_nadd _ 192 192 14) (Eval.seq (eval_nsub _ 194 194 26) (Eval.skip _))))))
  simpa only [suffix,Structured.sequence,afterStores,
    Function.update_of_ne (by decide : (56 : ℕ) ≠ 184),
    Function.update_of_ne (by decide : (192 : ℕ) ≠ 184),
    Function.update_of_ne (by decide : (14 : ℕ) ≠ 184),
    Function.update_of_ne (by decide : (194 : ℕ) ≠ 184),
    Function.update_of_ne (by decide : (26 : ℕ) ≠ 184),
    Function.update_of_ne (by decide : (194 : ℕ) ≠ 192),
    Function.update_of_ne (by decide : (26 : ℕ) ≠ 192),Function.update_self] using he
lemma read_reg_frame {s t : Data} {cost : ℕ} (he : Eval SelectedRead.code s cost t)
    (k : ℕ) (h30 : k ≠ 30) (h38 : k ≠ 38) (h196 : k ≠ 196)
    (h44 : k ≠ 44) (h20 : k ≠ 20) (h22 : k ≠ 22) : t.natReg k = s.natReg k :=
  he.nat_frame (SelectedRead.nat_frame k h30 h38 h196 h44 h20 h22)
lemma body_eval (s : Data) (hz : s.natReg 56 = 0) (h1 : s.natReg 26 = 1)
    (h2 : s.natReg 14 = 2)
    (hsep : s.natMem (s.natReg 192) ≠ s.natReg 98+2*s.natMem (s.natReg 192)) :
    ∃ cost t, Eval body s cost t ∧ cost ≤ 18 ∧
      t.natReg 192 = s.natReg 192+2 ∧ t.natReg 194 = s.natReg 194-1 ∧
      t.natMem (s.natMem (s.natReg 192)) = SelectedRead.flag (loaded s) ∧
      t.realMem (s.natMem (s.natReg 192)) = SelectedRead.realValue (loaded s) ∧
      t.natMem (s.natReg 98+2*s.natMem (s.natReg 192)) = 0 ∧
      (∀ address, address ≠ s.natMem (s.natReg 192) →
        address ≠ s.natReg 98+2*s.natMem (s.natReg 192) →
        t.natMem address = s.natMem address ∧ t.realMem address = s.realMem address) := by
  let a := loaded s
  have ha : Eval (loadN 94 192) s 1 a := eval_loadN s 94 192
  have haz : a.natReg 56 = 0 := by simpa [a,loaded] using hz
  obtain ⟨c,b,hb,hc,_,hr,hn⟩ := SelectedRead.eval_code a haz
  obtain ⟨hbf,hbr⟩ := SelectedRead.fields haz hb
  have bf (k : ℕ) (h30 : k ≠ 30) (h38 : k ≠ 38) (h196 : k ≠ 196)
      (h44 : k ≠ 44) (h20 : k ≠ 20) (h22 : k ≠ 22) : b.natReg k = a.natReg k :=
    read_reg_frame hb k h30 h38 h196 h44 h20 h22
  have bv : b.natReg 94 = s.natMem (s.natReg 192) := (bf 94 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans (by simp [a,loaded])
  have b98 : b.natReg 98 = s.natReg 98 := (bf 98 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans (by simp [a,loaded])
  have b192 : b.natReg 192 = s.natReg 192 := (bf 192 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans (by simp [a,loaded])
  have b194 : b.natReg 194 = s.natReg 194 := (bf 194 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans (by simp [a,loaded])
  have b14 : b.natReg 14 = 2 := (bf 14 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans (by simpa [a,loaded] using h2)
  have b26 : b.natReg 26 = 1 := (bf 26 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans (by simpa [a,loaded] using h1)
  have b56 : b.natReg 56 = 0 := (bf 56 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans haz
  have b38 : b.natReg 38 = 2*s.natMem (s.natReg 192) := by
    unfold SelectedRead.code at hb
    cases hb with
    | seq hp hchoose =>
      obtain ⟨_,rfl⟩ := hp.deterministic (SelectedRead.prefix_eval a)
      have hcframe : NatFrame SelectedRead.chooseCode 38 := by
        simp [SelectedRead.chooseCode,PointerRead.code,SelectedRead.zeroCode,Structured.sequence,
          NatFrame,writesNat,loadN,nadd,load,natural,rational]
      rw [hchoose.nat_frame hcframe,(SelectedRead.prefix_fields a).1]
      simp [a,loaded]
  let t := afterStores b
  refine ⟨1+(c+6),t,Eval.seq ha (Eval.seq hb (suffix_eval b)),by omega,?_,?_,?_,?_,?_,?_⟩
  · simp [t,afterStores,b192,b14]
  · simp [t,afterStores,b194,b26]
  · simp [t,afterStores,bv,b98,b38,hsep,hbf,a]
  · simp [t,afterStores,bv,hbr,a]
  · simp [t,afterStores,b98,b38,b56]
  · intro address hv hflag
    simp [t,afterStores,bv,b98,b38,Function.update_of_ne hv,Function.update_of_ne hflag,hr,hn,a,loaded]
lemma nat_frame (k : ℕ) (h30 : k ≠ 30) (h38 : k ≠ 38) (h196 : k ≠ 196)
    (h44 : k ≠ 44) (h20 : k ≠ 20) (h22 : k ≠ 22) (h94 : k ≠ 94)
    (h184 : k ≠ 184) (h192 : k ≠ 192) (h194 : k ≠ 194) : NatFrame body k := by
  simp [body,suffix,NatFrame,SelectedRead.nat_frame k h30 h38 h196 h44 h20 h22,
    Structured.sequence,storeN,store,nadd,nsub,loadN,writesNat,
    Ne.symm h94,Ne.symm h184,Ne.symm h192,Ne.symm h194]
end DecrAlmostLinearSSSP.Decremental.DirtyCommit
end s196
section s197
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.DirtyCommit
open Structured
lemma body_fixed {s t : Data} {cost : ℕ} (he : Eval body s cost t) :
    t.natReg 14 = s.natReg 14 ∧ t.natReg 26 = s.natReg 26 ∧
    t.natReg 56 = s.natReg 56 ∧ t.natReg 72 = s.natReg 72 ∧
    t.natReg 96 = s.natReg 96 ∧ t.natReg 98 = s.natReg 98 := by
  repeat' apply And.intro
  all_goals apply he.nat_frame
  all_goals apply nat_frame <;> omega
lemma eval_loop {n : ℕ} (l : AnswerTable.Layout n) (flagBase listBase : ℕ)
    (hflags : n ≤ flagBase) (hlists : flagBase+2*n ≤ listBase)
    (hprotected : ∀ address, AnswerTable.Protected l address → n ≤ address ∧
      ∀ v : Fin n, address ≠ flagBase+2*v.val)
    (xs : List (Fin n)) (readBase : ℕ) (s : Data)
    (hread : listBase ≤ readBase) (himage : AnswerTable.Image l s)
    (hp : s.natReg 96 = l.pointerBase) (hs : s.natReg 72 = l.source.val)
    (hf : s.natReg 98 = flagBase) (hz : s.natReg 56 = 0)
    (h1 : s.natReg 26 = 1) (h2 : s.natReg 14 = 2)
    (h192 : s.natReg 192 = readBase) (h194 : s.natReg 194 = xs.length)
    (hentries : ∀ j (hj : j < xs.length), s.natMem (readBase+2*j) = (xs[j]).val) :
    ∃ cost t, Eval loop s cost t ∧ cost ≤ 20*xs.length+2 ∧
      t.natReg 192 = readBase+2*xs.length ∧ t.natReg 194 = 0 ∧
      AnswerTable.Image l t ∧
      (∀ v ∈ xs, t.natMem v.val = l.flag v ∧ t.realMem v.val = l.realValue v ∧
        t.natMem (flagBase+2*v.val) = 0) ∧
      (∀ address, (∀ v ∈ xs, address ≠ v.val ∧ address ≠ flagBase+2*v.val) →
        t.natMem address = s.natMem address ∧ t.realMem address = s.realMem address) := by
  induction xs generalizing readBase s with
  | nil =>
    have ht : ¬(Test.natLess 56 194).holds s := by simp [Test.holds,hz,h194]
    exact ⟨2,s,Eval.loopNo s ht,by simp,by simpa using h192,h194,himage,by simp,fun _ _ => ⟨rfl,rfl⟩⟩
  | cons v xs ih =>
    have hhead : s.natMem (s.natReg 192) = v.val := by
      have hh := hentries 0 (by simp)
      change s.natMem (readBase+2*0) = v.val at hh
      simpa [h192] using hh
    have hsep : s.natMem (s.natReg 192) ≠ s.natReg 98+2*s.natMem (s.natReg 192) := by
      rw [hhead,hf]
      have hv := v.isLt
      omega
    obtain ⟨c,u,hu,hc,hu192,hu194,hun,hur,huflag,huframe⟩ := body_eval s hz h1 h2 hsep
    obtain ⟨hu14,hu26,hu56,hu72,hu96,hu98⟩ := body_fixed hu
    have huimage : AnswerTable.Image l u := himage.frame (by
      intro address haddr
      have hh := hprotected address haddr
      exact huframe address (by rw [hhead];have hv := v.isLt;omega) (by rw [hf,hhead];exact hh.2 v))
    have hloadImage : AnswerTable.Image l (loaded s) := himage.same_memory rfl rfl
    have hload96 : (loaded s).natReg 96 = l.pointerBase := by simpa [loaded] using hp
    have hload72 : (loaded s).natReg 72 = l.source.val := by simpa [loaded] using hs
    have hload94 : (loaded s).natReg 94 = v.val := by simp [loaded,hhead]
    obtain ⟨hflag,hreal⟩ := AnswerTable.read_fields l (loaded s) v hloadImage hload96 hload72 hload94
    have hucell : u.natMem v.val = l.flag v ∧ u.realMem v.val = l.realValue v ∧ u.natMem (flagBase+2*v.val) = 0 := by
      simpa only [hhead,hf,hflag,hreal] using And.intro hun (And.intro hur huflag)
    have huentries : ∀ j (hj : j < xs.length), u.natMem (readBase+2+2*j) = (xs[j]).val := by
      intro j hj
      have haddr : readBase+2+2*j = readBase+2*(j+1) := by omega
      have hpub : readBase+2+2*j ≠ s.natMem (s.natReg 192) := by rw [hhead];have hv := v.isLt;omega
      have hdirty : readBase+2+2*j ≠ s.natReg 98+2*s.natMem (s.natReg 192) := by rw [hf,hhead];have hv := v.isLt;omega
      rw [(huframe _ hpub hdirty).1,haddr]
      exact hentries (j+1) (by simpa using hj)
    obtain ⟨rest,t,ht,hrest,ht192,ht194,htimage,htcells,htframe⟩ :=
      ih (readBase+2) u (by omega) huimage (hu96.trans hp) (hu72.trans hs)
        (hu98.trans hf) (hu56.trans hz) (hu26.trans h1) (hu14.trans h2)
        (by simpa only [h192] using hu192) (by simpa only [h194,List.length_cons,Nat.add_sub_cancel] using hu194) huentries
    have htest : (Test.natLess 56 194).holds s := by simp [Test.holds,hz,h194]
    refine ⟨c+rest+2,t,Eval.loopYes htest hu ht,by simp only [List.length_cons];omega,?_,ht194,htimage,?_,?_⟩
    · simp only [List.length_cons]
      omega
    · intro w hw
      rcases List.mem_cons.mp hw with hw | hw
      · subst w
        by_cases hvtail : v ∈ xs
        · exact htcells v hvtail
        · have hpout : ∀ w ∈ xs, v.val ≠ w.val ∧ v.val ≠ flagBase+2*w.val := by
            intro w hw
            constructor
            · intro heq;exact hvtail ((Fin.ext heq) ▸ hw)
            · have hv := v.isLt;omega
          have hfout : ∀ w ∈ xs, flagBase+2*v.val ≠ w.val ∧ flagBase+2*v.val ≠ flagBase+2*w.val := by
            intro w hw
            constructor
            · have hwlt := w.isLt;omega
            · intro heq
              have hvw : v = w := Fin.ext (by omega)
              exact hvtail (hvw ▸ hw)
          have hfp := htframe v.val hpout
          have hff := htframe (flagBase+2*v.val) hfout
          exact ⟨hfp.1.trans hucell.1,hfp.2.trans hucell.2.1,hff.1.trans hucell.2.2⟩
      · exact htcells w hw
    · intro address hout
      have htout : ∀ w ∈ xs, address ≠ w.val ∧ address ≠ flagBase+2*w.val :=
        fun w hw => hout w (List.mem_cons_of_mem _ hw)
      have hh := hout v (by simp)
      have hsout := huframe address (by simpa only [hhead] using hh.1) (by simpa only [hf,hhead] using hh.2)
      have htu := htframe address htout
      exact ⟨htu.1.trans hsout.1,htu.2.trans hsout.2⟩
end DecrAlmostLinearSSSP.Decremental.DirtyCommit
end s197
section s198
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.DirtyCommit
open Structured
lemma begin_eval (s : Data) : Eval beginCode s 2 (beginData s) := by
  have hh := Eval.seq (eval_nadd s 192 102 56) (Eval.seq (eval_nadd _ 194 182 56) (Eval.skip _))
  simpa [beginCode,Structured.sequence,beginData] using hh
lemma end_eval (s : Data) : Eval endCode s 2 (endData s) := by
  have hh := Eval.seq (eval_natural s 182 0) (Eval.seq (eval_nadd _ 180 102 56) (Eval.skip _))
  simpa [endCode,Structured.sequence,endData] using hh
lemma loop_frame (k : ℕ) (h30 : k ≠ 30) (h38 : k ≠ 38) (h196 : k ≠ 196)
    (h44 : k ≠ 44) (h20 : k ≠ 20) (h22 : k ≠ 22) (h94 : k ≠ 94)
    (h184 : k ≠ 184) (h192 : k ≠ 192) (h194 : k ≠ 194) : NatFrame loop k :=
  nat_frame k h30 h38 h196 h44 h20 h22 h94 h184 h192 h194
lemma eval_code {n : ℕ} (l : AnswerTable.Layout n) (flagBase listBase : ℕ)
    (hflags : n ≤ flagBase) (hlists : flagBase+2*n ≤ listBase)
    (hprotected : ∀ address, AnswerTable.Protected l address → n ≤ address ∧
      ∀ v : Fin n, address ≠ flagBase+2*v.val)
    (xs : List (Fin n)) (s : Data) (hview : DirtyMark.View flagBase listBase xs s)
    (himage : AnswerTable.Image l s)
    (hp : s.natReg 96 = l.pointerBase) (hs : s.natReg 72 = l.source.val)
    (hf : s.natReg 98 = flagBase) (hl : s.natReg 102 = listBase) (hz : s.natReg 56 = 0)
    (h1 : s.natReg 26 = 1) (h2 : s.natReg 14 = 2)
    (hclean : ∀ v : Fin n, v ∉ xs → s.natMem v.val = l.flag v ∧ s.realMem v.val = l.realValue v) :
    ∃ cost t, Eval code s cost t ∧ cost ≤ 20*xs.length+6 ∧
      DirtyMark.View (n := n) flagBase listBase [] t ∧ AnswerTable.Image l t ∧
      (∀ v : Fin n, t.natMem v.val = l.flag v ∧ t.realMem v.val = l.realValue v) ∧
      (∀ address, (∀ v ∈ xs, address ≠ v.val ∧ address ≠ flagBase+2*v.val) →
        t.natMem address = s.natMem address ∧ t.realMem address = s.realMem address) := by
  let a := beginData s
  have haimage : AnswerTable.Image l a := himage.same_memory rfl rfl
  have ha192 : a.natReg 192 = listBase := by simp [a,beginData,hl,hz]
  have ha194 : a.natReg 194 = xs.length := by simp [a,beginData,hview.count,hz]
  have hap : a.natReg 96 = l.pointerBase := by simpa [a,beginData] using hp
  have has : a.natReg 72 = l.source.val := by simpa [a,beginData] using hs
  have haf : a.natReg 98 = flagBase := by simpa [a,beginData] using hf
  have haz : a.natReg 56 = 0 := by simpa [a,beginData] using hz
  have ha1 : a.natReg 26 = 1 := by simpa [a,beginData] using h1
  have ha2 : a.natReg 14 = 2 := by simpa [a,beginData] using h2
  obtain ⟨c,u,hu,hc,_,_,huimage,hucells,huframe⟩ := eval_loop l flagBase listBase hflags hlists
    hprotected xs listBase a le_rfl haimage hap has haf haz ha1 ha2 ha192 ha194 hview.entries
  have hul : u.natReg 102 = listBase := by
    rw [hu.nat_frame (loop_frame 102 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega))]
    simpa [a,beginData] using hl
  have huz : u.natReg 56 = 0 := by
    rw [hu.nat_frame (loop_frame 56 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega))]
    exact haz
  let t := endData u
  have htimage : AnswerTable.Image l t := huimage.same_memory rfl rfl
  have htview : DirtyMark.View (n := n) flagBase listBase [] t := by
    refine ⟨by simp,?_,by simp,?_,?_⟩
    · intro v
      change u.natMem (flagBase+2*v.val) = _
      by_cases hv : v ∈ xs
      · simpa using (hucells v hv).2.2
      · have hout : ∀ w ∈ xs, flagBase+2*v.val ≠ w.val ∧ flagBase+2*v.val ≠ flagBase+2*w.val := by
          intro w hw
          constructor
          · have hwlt := w.isLt;omega
          · intro heq
            have hvw : v = w := Fin.ext (by omega)
            exact hv (hvw ▸ hw)
        rw [(huframe _ hout).1]
        simpa [a,beginData,hv] using hview.flags v
    · simp [t,endData]
    · simp [t,endData,hul,huz]
  refine ⟨2+(c+2),t,Eval.seq (begin_eval s) (Eval.seq hu (end_eval u)),by omega,htview,htimage,?_,?_⟩
  · intro v
    by_cases hv : v ∈ xs
    · exact ⟨(hucells v hv).1,(hucells v hv).2.1⟩
    · have hout : ∀ w ∈ xs, v.val ≠ w.val ∧ v.val ≠ flagBase+2*w.val := by
        intro w hw
        constructor
        · intro heq;exact hv ((Fin.ext heq) ▸ hw)
        · have hvlt := v.isLt;omega
      have hh := huframe v.val hout
      exact ⟨hh.1.trans (hclean v hv).1,hh.2.trans (hclean v hv).2⟩
  · intro address hout
    exact huframe address hout
end DecrAlmostLinearSSSP.Decremental.DirtyCommit
end s198
section s199
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
namespace SelectedRead
lemma real_frame (k : ℕ) (h20 : k ≠ 20) : RealFrame code k := by
  simp [code,chooseCode,prefixCode,prefixAtoms,zeroCode,PointerRead.code,Structured.sequence,RealFrame,
    writesReal,natural,rational,loadN,nadd,load,Ne.symm h20]
end SelectedRead
namespace DirtyCommit
lemma code_nat_frame (k : ℕ) (h30 : k ≠ 30) (h38 : k ≠ 38) (h196 : k ≠ 196)
    (h44 : k ≠ 44) (h20 : k ≠ 20) (h22 : k ≠ 22) (h94 : k ≠ 94)
    (h184 : k ≠ 184) (h192 : k ≠ 192) (h194 : k ≠ 194) (h182 : k ≠ 182) (h180 : k ≠ 180) : NatFrame code k := by
  refine ⟨?_,loop_frame k h30 h38 h196 h44 h20 h22 h94 h184 h192 h194,?_⟩
  · simp [beginCode,Structured.sequence,NatFrame,nadd,writesNat,Ne.symm h192,Ne.symm h194]
  · simp [endCode,Structured.sequence,NatFrame,nadd,natural,writesNat,Ne.symm h182,Ne.symm h180]
lemma code_real_frame (k : ℕ) (h20 : k ≠ 20) : RealFrame code k := by
  refine ⟨?_,?_,?_⟩
  · simp [beginCode,Structured.sequence,RealFrame,nadd,writesReal]
  · refine ⟨not_false,SelectedRead.real_frame k h20,?_⟩
    simp [suffix,Structured.sequence,RealFrame,storeN,store,nadd,nsub,writesReal]
  · simp [endCode,Structured.sequence,RealFrame,nadd,natural,writesReal]
end DirtyCommit
namespace Native
lemma globalFrame_commit : GlobalFrame DirtyCommit.code := by
  constructor
  · intro k hk
    simp only [globalNat,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals apply DirtyCommit.code_nat_frame <;> norm_num
  · intro k hk
    simp only [globalReal,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl
    all_goals apply DirtyCommit.code_real_frame <;> norm_num
lemma tailFrame_commit : TailFrame DirtyCommit.code := by
  intro j hj
  refine ⟨DirtyCommit.code_nat_frame _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_,
    DirtyCommit.code_real_frame _ (shadowReg_ne_of_even j 20 (by decide))⟩
  all_goals apply shadowReg_ne_of_even <;> decide
end Native
end DecrAlmostLinearSSSP.Decremental
end s199
section s200
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
lemma commit_initial_pointers (i : Input) (B reserve N : ℕ)
    (b : Fin (scaleCount i) → Fin i.n → ℝ≥0∞) (s : Data)
    (h : PointerPrefix i B reserve N b i.n s) (hB : i.n ≤ B) :
    ∃ cost t, Eval DirtyCommit.code s cost t ∧ cost ≤ 20*i.n+6 ∧
      Globals i B (scaleLayout B i.n (scaleCount i) reserve N).utility t ∧
      DirtyMark.View (n := i.n) (pointerLayout B i.n (scaleCount i) reserve N).flags
        (pointerLayout B i.n (scaleCount i) reserve N).list [] t ∧
      (∀ v : Fin i.n, t.natMem v.val ≤ 1 ∧ (t.natMem v.val = 0 → 0 ≤ t.realMem v.val)) ∧
      (∀ v : Fin i.n, stored t.machine v.val = selected i b (initialPointers i b) v) ∧
      (∀ v : Fin i.n, t.natMem ((pointerLayout B i.n (scaleCount i) reserve N).pointer+2*v.val) =
        scanRecord i (pointerLayout B i.n (scaleCount i) reserve N).record (2*N+8) (initialPointers i b v)) ∧
      PublicFrame (pointerLayout B i.n (scaleCount i) reserve N) i.n s t := by
  let l := pointerLayout B i.n (scaleCount i) reserve N
  let p := initialPointers i b
  let a := answerLayout i l.record l.cache (2*N+8) l.pointer p s
  have hptr : ∀ v : Fin i.n, s.natMem (l.pointer+2*v.val) = scanRecord i l.record (2*N+8) (p v) :=
    fun v => h.pointers v v.isLt
  have himage : AnswerTable.Image a s := answerLayout_image i l.record l.cache (2*N+8) l.pointer p s b h.table hptr
  have hprotected : ∀ address, AnswerTable.Protected a address → i.n ≤ address ∧
      ∀ v : Fin i.n, address ≠ l.flags+2*v.val := answerLayout_protected i B reserve N s b p h.table hB
  have hflags : i.n ≤ l.flags := by dsimp [l,pointerLayout,scaleLayout,Layout.addresses];omega
  have hlists : l.flags+2*i.n ≤ l.list := by dsimp [l,pointerLayout,scaleLayout,Layout.addresses];omega
  obtain ⟨cost,t,he,hcost,hview,hafterImage,houtputs,hframe⟩ := DirtyCommit.eval_code a l.flags l.list hflags hlists hprotected
    (List.finRange i.n) s h.dirty_view himage h.bases.pointer h.globals.source h.bases.flags h.bases.list
    h.globals.zeroN h.globals.unit h.globals.two (by intro v hv;exact False.elim (hv (List.mem_finRange v)))
  have hnormal := answerLayout_normal i l.record l.cache (2*N+8) l.pointer p s b h.table
  have hpublic : ∀ v : Fin i.n, t.natMem v.val ≤ 1 ∧ (t.natMem v.val = 0 → 0 ≤ t.realMem v.val) := by
    intro v
    obtain ⟨hn,hr⟩ := houtputs v
    simpa only [hn,hr] using hnormal v
  have hstored : ∀ v : Fin i.n, stored t.machine v.val = selected i b p v := by
    intro v
    obtain ⟨hn,hr⟩ := houtputs v
    have hv := answerLayout_value i l.record l.cache (2*N+8) l.pointer p s b h.table v
    change (if t.natMem v.val = 1 then ⊤ else ENNReal.ofReal (t.realMem v.val)) = _
    rw [hn,hr]
    exact hv
  have hpubframe : PublicFrame l i.n s t := by
    intro address hout
    apply hframe
    intro v hv
    constructor
    · intro heq
      exact hout (Or.inl (by rw [heq];exact v.isLt))
    · intro heq
      exact hout (Or.inr ⟨v.val,v.isLt,Or.inr (Or.inl heq)⟩)
  refine ⟨cost,t,he,?_,h.globals.transfer he globalFrame_commit,hview,hpublic,hstored,?_,hpubframe⟩
  · simpa only [List.length_finRange] using hcost
  · exact hafterImage.pointers
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
lemma barrier_walk_cost (i : Input) (hi : i.Valid) (j : ℕ) (es : List (Fin i.k))
    (hcut : ∀ e ∈ es, (i.weight e : ℝ) ≤ 2*scale j) :
    (es.map (fun e => (i.weight e : ℝ))).sum ≤
        delta i j*(es.map (fun e => (barrierWeight i j e : ℝ))).sum ∧
    delta i j*(es.map (fun e => (barrierWeight i j e : ℝ))).sum ≤
        (es.map (fun e => (i.weight e : ℝ))).sum + es.length*delta i j := by
  induction es with
  | nil => simp
  | cons e es ih =>
    have he := barrier_low_cost i hi j e (hcut e List.mem_cons_self)
    have hh := ih (fun f hf => hcut f (List.mem_cons_of_mem e hf))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    constructor <;> nlinarith only [he.1,he.2,hh.1,hh.2]
lemma barrier_distance_upper_of_walk (i : Input) (hi : i.Valid) (j : ℕ)
    (active : Finset (Fin i.k)) {u v : Fin i.n} {es : List (Fin i.k)}
    (hwalk : Walk i.graph active u v es)
    (hcut : ∀ e ∈ es, (i.weight e : ℝ) ≤ 2*scale j) :
    ENNReal.ofReal (delta i j)*distance (barrierInput i j).graph active
      (fun e => ((barrierInput i j).weight e : ℝ≥0∞)) u v ≤
      ENNReal.ofReal ((es.map (fun e => (i.weight e : ℝ))).sum+es.length*delta i j) := by
  have hh := mul_le_mul_right (distance_le_walk hwalk
    (fun e => (barrierWeight i j e : ℝ≥0∞))) (ENNReal.ofReal (delta i j))
  apply hh.trans
  rw [nat_weight_list_real,← ENNReal.ofReal_mul (delta_positive i hi j).le]
  exact ENNReal.ofReal_le_ofReal (barrier_walk_cost i hi j es hcut).2
lemma barrier_distance_lower_guarded (i : Input) (hi : i.Valid) (j : ℕ)
    (active : Finset (Fin i.k)) (u v : Fin i.n)
    (hguard : ENNReal.ofReal (delta i j)*distance (barrierInput i j).graph active
      (fun e => ((barrierInput i j).weight e : ℝ≥0∞)) u v ≤ ENNReal.ofReal (2*scale j)) :
    distance i.graph active (fun e => (i.weight e : ℝ≥0∞)) u v ≤
      ENNReal.ofReal (delta i j)*distance (barrierInput i j).graph active
        (fun e => ((barrierInput i j).weight e : ℝ≥0∞)) u v := by
  classical
  have hd := delta_positive i hi j
  have hs := scale_positive j
  have hr : Reachable i.graph active u v := by
    by_contra hnot
    have ht := distance_top_of_unreachable i.graph active
      (fun e => (barrierWeight i j e : ℝ≥0∞)) u v hnot
    change ENNReal.ofReal (delta i j)*distance i.graph active
      (fun e => (barrierWeight i j e : ℝ≥0∞)) u v ≤ _ at hguard
    rw [ht,ENNReal.mul_top (ENNReal.ofReal_pos.mpr hd).ne'] at hguard
    exact ENNReal.ofReal_ne_top (top_le_iff.mp hguard)
  obtain ⟨es,hes,_,hdist⟩ := distance_min_weight i.graph active
    (fun e => (barrierWeight i j e : ℝ)) (fun e => Nat.cast_nonneg _) u v hr
  have heq : distance (barrierInput i j).graph active
      (fun e => ((barrierInput i j).weight e : ℝ≥0∞)) u v =
      ENNReal.ofReal ((es.map (fun e => (barrierWeight i j e : ℝ))).sum) := by
    simpa only [barrierInput, ENNReal.ofReal_natCast] using hdist
  rw [heq,← ENNReal.ofReal_mul hd.le] at hguard ⊢
  have hsum : delta i j*(es.map (fun e => (barrierWeight i j e : ℝ))).sum ≤ 2*scale j :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ 2*scale j)).mp hguard
  have hcut : ∀ e ∈ es, (i.weight e : ℝ) ≤ 2*scale j := by
    intro e he
    by_contra hh
    have hlo := barrier_high_cost i hi j e hh
    have hle := mul_le_mul_of_nonneg_left (real_weight_le_walk_sum (barrierWeight i j) es e he) hd.le
    linarith
  have hlo := distance_le_walk hes (fun e => (i.weight e : ℝ≥0∞))
  rw [nat_weight_list_real] at hlo
  exact hlo.trans (ENNReal.ofReal_le_ofReal (barrier_walk_cost i hi j es hcut).1)
end DecrAlmostLinearSSSP.Decremental
end s206
section s207
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
lemma delta_vertex_product (i : Input) (j : ℕ) :
    (i.n : ℝ) * delta i j = i.accuracy * scale j / 128 := by
  have hn : (i.n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (input_vertex_positive i))
  dsimp [delta]
  field_simp
  <;> ring
lemma rounding_factor_bound {epsilon d L : ℝ} (he : 0 < epsilon) (he1 : epsilon ≤ 1)
    (hd : 0 ≤ d) (hL : L ≤ 2 * d) :
    (1 + epsilon / 16) * (d + epsilon * L / 128) ≤ (1 + epsilon / 8) * d := by
  have hr : d + epsilon * L / 128 ≤ (1 + epsilon / 64) * d := by nlinarith only [mul_le_mul_of_nonneg_left hL he.le]
  have he2 : epsilon ^ 2 ≤ epsilon := by nlinarith only [mul_le_mul_of_nonneg_left he1 he.le]
  have hfactor : (1 + epsilon / 16) * (1 + epsilon / 64) ≤ 1 + epsilon / 8 := by nlinarith only [he2, he.le]
  calc
    (1 + epsilon / 16) * (d + epsilon * L / 128) ≤
        (1 + epsilon / 16) * ((1 + epsilon / 64) * d) := mul_le_mul_of_nonneg_left hr (by positivity)
    _ = ((1 + epsilon / 16) * (1 + epsilon / 64)) * d := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hfactor hd
lemma scaled_estimate_upper (i : Input) (hi : i.Valid) (j : ℕ)
    (active : Finset (Fin i.k)) (u v : Fin i.n) (B : ℝ≥0∞)
    (hr : Reachable i.graph active u v)
    (hcut : distance i.graph active (fun e => (i.weight e : ℝ≥0∞)) u v ≤ ENNReal.ofReal (2 * scale j))
    (hupper : B ≤ ENNReal.ofReal (1 + i.accuracy / 16) *
      distance (roundedInput i j).graph (scaleActive i j active) (fun e => ((roundedInput i j).weight e : ℝ≥0∞)) u v) :
    ∃ d : ℝ, 0 ≤ d ∧ distance i.graph active (fun e => (i.weight e : ℝ≥0∞)) u v = ENNReal.ofReal d ∧
      ENNReal.ofReal (delta i j) * B ≤ ENNReal.ofReal ((1 + i.accuracy / 16) * (d + i.accuracy * scale j / 128)) := by
  obtain ⟨d, hd, hdist, hup⟩ := rounded_shortest_upper i hi j active u v hr hcut
  have hmul := mul_le_mul_right hupper (ENNReal.ofReal (delta i j))
  have hmul2 := mul_le_mul_right hup (ENNReal.ofReal (1 + i.accuracy / 16))
  refine ⟨d, hd, hdist, hmul.trans ?_⟩
  calc
    ENNReal.ofReal (delta i j) * (ENNReal.ofReal (1 + i.accuracy / 16) *
        distance (roundedInput i j).graph (scaleActive i j active) (fun e => ((roundedInput i j).weight e : ℝ≥0∞)) u v) =
      ENNReal.ofReal (1 + i.accuracy / 16) * (ENNReal.ofReal (delta i j) *
        distance (roundedInput i j).graph (scaleActive i j active) (fun e => ((roundedInput i j).weight e : ℝ≥0∞)) u v) := by ac_rfl
    _ ≤ ENNReal.ofReal (1 + i.accuracy / 16) * ENNReal.ofReal (d + i.n * delta i j) := hmul2
    _ = _ := by rw [← ENNReal.ofReal_mul (by have he := hi.2.2.2.1; positivity), delta_vertex_product]
lemma scaled_eligible_accuracy (i : Input) (hi : i.Valid) (j : ℕ)
    (active : Finset (Fin i.k)) (u v : Fin i.n) (B : ℝ≥0∞) (d : ℝ)
    (hd : 0 ≤ d) (hdist : distance i.graph active (fun e => (i.weight e : ℝ≥0∞)) u v = ENNReal.ofReal d)
    (hr : Reachable i.graph active u v) (hscale : scale j ≤ 2 * d)
    (hlower : distance (roundedInput i j).graph (scaleActive i j active)
      (fun e => ((roundedInput i j).weight e : ℝ≥0∞)) u v ≤ B)
    (hupper : B ≤ ENNReal.ofReal (1 + i.accuracy / 16) *
      distance (roundedInput i j).graph (scaleActive i j active) (fun e => ((roundedInput i j).weight e : ℝ≥0∞)) u v)
    (heligible : ENNReal.ofReal (delta i j) * B ≤ ENNReal.ofReal (2 * scale j)) :
    ENNReal.ofReal d ≤ ENNReal.ofReal (delta i j) * B ∧
      ENNReal.ofReal (delta i j) * B ≤ ENNReal.ofReal ((1 + i.accuracy / 8) * d) := by
  have hl := (rounded_distance_lower i hi j active u v).trans (mul_le_mul_right hlower _)
  have hcut := hl.trans heligible
  obtain ⟨d', hd', hdist', hu⟩ := scaled_estimate_upper i hi j active u v B hr hcut hupper
  have hdd : d' = d := by
    have heq : ENNReal.ofReal d' = ENNReal.ofReal d := hdist'.symm.trans hdist
    exact (ENNReal.ofReal_eq_ofReal_iff hd' hd).mp heq
  subst d'
  refine ⟨by rwa [hdist] at hl, hu.trans ?_⟩
  apply ENNReal.ofReal_le_ofReal
  exact rounding_factor_bound hi.2.2.2.1 hi.2.2.2.2.1 hd hscale
end DecrAlmostLinearSSSP.Decremental
end s207
section s208
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
lemma Walk.active_mono {n k : ℕ} {g : Digraph n k} {a b : Finset (Fin k)}
    (hab : a ⊆ b) {u v : Fin n} {es : List (Fin k)} (h : Walk g a u v es) : Walk g b u v es := by
  induction h with
  | nil v => exact .nil v
  | cons e he h ih => exact .cons (u := g.tail e) e (hab he) ih
lemma distance_active_antitone {n k : ℕ} (g : Digraph n k) {a b : Finset (Fin k)}
    (hab : a ⊆ b) (w : Fin k → ℝ≥0∞) (u v : Fin n) :
    distance g b w u v ≤ distance g a w u v := by
  apply le_iInf
  intro es
  apply le_iInf
  intro hes
  exact distance_le_walk (hes.active_mono hab) w
lemma historical_readout_of_walk (i : Input) (hi : i.Valid) (j : ℕ)
    (current past : Finset (Fin i.k)) (hactive : current ⊆ past)
    {u v : Fin i.n} {es : List (Fin i.k)} (hwalk : Walk i.graph current u v es)
    (hcut : ∀ e ∈ es, (i.weight e : ℝ) ≤ 2 * scale j) (B : ℝ≥0∞)
    (hb : B ≤ ENNReal.ofReal (1 + i.accuracy / 16) *
      distance (roundedInput i j).graph (scaleActive i j past)
        (fun e => ((roundedInput i j).weight e : ℝ≥0∞)) u v) :
    ENNReal.ofReal (delta i j) * B ≤ ENNReal.ofReal ((1 + i.accuracy / 16) *
      ((es.map (fun e => (i.weight e : ℝ))).sum + es.length * delta i j)) := by
  have hp := rounded_distance_upper_of_walk i hi j past (hwalk.active_mono hactive) hcut
  calc
    ENNReal.ofReal (delta i j) * B ≤ ENNReal.ofReal (delta i j) *
      (ENNReal.ofReal (1 + i.accuracy / 16) * distance (roundedInput i j).graph (scaleActive i j past)
        (fun e => ((roundedInput i j).weight e : ℝ≥0∞)) u v) := mul_le_mul_right hb _
    _ = ENNReal.ofReal (1 + i.accuracy / 16) * (ENNReal.ofReal (delta i j) *
      distance (roundedInput i j).graph (scaleActive i j past)
        (fun e => ((roundedInput i j).weight e : ℝ≥0∞)) u v) := by ac_rfl
    _ ≤ ENNReal.ofReal (1 + i.accuracy / 16) *
      ENNReal.ofReal ((es.map (fun e => (i.weight e : ℝ))).sum + es.length * delta i j) := mul_le_mul_right hp _
    _ = _ := by rw [← ENNReal.ofReal_mul (by have he := hi.2.2.2.1; positivity)]
lemma scaled_max_bound (delta : ℝ≥0∞) (x y bound : ℝ≥0∞)
    (hx : delta * x ≤ bound) (hy : delta * y ≤ bound) : delta * max x y ≤ bound := by
  rcases le_total x y with h | h
  · rwa [max_eq_right h]
  · rwa [max_eq_left h]
lemma historical_readout_finite_family (i : Input) (hi : i.Valid) (j : ℕ)
    {ι : Type} (S : Finset ι) (past : ι → Finset (Fin i.k))
    (current : Finset (Fin i.k)) (hactive : ∀ t ∈ S, current ⊆ past t)
    {u v : Fin i.n} {es : List (Fin i.k)} (hwalk : Walk i.graph current u v es)
    (hcut : ∀ e ∈ es, (i.weight e : ℝ) ≤ 2 * scale j) (B : ι → ℝ≥0∞)
    (hb : ∀ t ∈ S, B t ≤ ENNReal.ofReal (1 + i.accuracy / 16) *
      distance (roundedInput i j).graph (scaleActive i j (past t))
        (fun e => ((roundedInput i j).weight e : ℝ≥0∞)) u v) :
    ENNReal.ofReal (delta i j) * S.sup B ≤ ENNReal.ofReal ((1 + i.accuracy / 16) *
      ((es.map (fun e => (i.weight e : ℝ))).sum + es.length * delta i j)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert t S ht ih =>
    rw [Finset.sup_insert]
    exact scaled_max_bound _ _ _ _
      (historical_readout_of_walk i hi j current (past t) (hactive t (Finset.mem_insert_self _ _)) hwalk hcut (B t) (hb t (Finset.mem_insert_self _ _)))
      (ih (fun r hr => hactive r (Finset.mem_insert_of_mem hr)) (fun r hr => hb r (Finset.mem_insert_of_mem hr)))
end DecrAlmostLinearSSSP.Decremental
end s208
section s209
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
lemma barrier_historical_readout_of_walk (i : Input) (hi : i.Valid) (j : ℕ)
    (current past : Finset (Fin i.k)) (hactive : current ⊆ past)
    {u v : Fin i.n} {es : List (Fin i.k)} (hwalk : Walk i.graph current u v es)
    (hcut : ∀ e ∈ es, (i.weight e : ℝ) ≤ 2 * scale j) (B : ℝ≥0∞)
    (hb : B ≤ ENNReal.ofReal (1 + i.accuracy / 16) *
      distance (barrierInput i j).graph past
        (fun e => ((barrierInput i j).weight e : ℝ≥0∞)) u v) :
    ENNReal.ofReal (delta i j) * B ≤ ENNReal.ofReal ((1 + i.accuracy / 16) *
      ((es.map (fun e => (i.weight e : ℝ))).sum + es.length * delta i j)) := by
  have hp := barrier_distance_upper_of_walk i hi j past (hwalk.active_mono hactive) hcut
  calc
    ENNReal.ofReal (delta i j) * B ≤ ENNReal.ofReal (delta i j) *
      (ENNReal.ofReal (1 + i.accuracy / 16) * distance (barrierInput i j).graph past
        (fun e => ((barrierInput i j).weight e : ℝ≥0∞)) u v) := mul_le_mul_right hb _
    _ = ENNReal.ofReal (1 + i.accuracy / 16) * (ENNReal.ofReal (delta i j) *
      distance (barrierInput i j).graph past
        (fun e => ((barrierInput i j).weight e : ℝ≥0∞)) u v) := by ac_rfl
    _ ≤ ENNReal.ofReal (1 + i.accuracy / 16) *
      ENNReal.ofReal ((es.map (fun e => (i.weight e : ℝ))).sum + es.length * delta i j) := mul_le_mul_right hp _
    _ = _ := by rw [← ENNReal.ofReal_mul (by have he := hi.2.2.2.1; positivity)]
lemma barrier_historical_readout_finite_family (i : Input) (hi : i.Valid) (j : ℕ)
    {ι : Type} (S : Finset ι) (past : ι → Finset (Fin i.k))
    (current : Finset (Fin i.k)) (hactive : ∀ t ∈ S, current ⊆ past t)
    {u v : Fin i.n} {es : List (Fin i.k)} (hwalk : Walk i.graph current u v es)
    (hcut : ∀ e ∈ es, (i.weight e : ℝ) ≤ 2 * scale j) (B : ι → ℝ≥0∞)
    (hb : ∀ t ∈ S, B t ≤ ENNReal.ofReal (1 + i.accuracy / 16) *
      distance (barrierInput i j).graph (past t)
        (fun e => ((barrierInput i j).weight e : ℝ≥0∞)) u v) :
    ENNReal.ofReal (delta i j) * S.sup B ≤ ENNReal.ofReal ((1 + i.accuracy / 16) *
      ((es.map (fun e => (i.weight e : ℝ))).sum + es.length * delta i j)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert t S ht ih =>
    rw [Finset.sup_insert]
    exact scaled_max_bound _ _ _ _
      (barrier_historical_readout_of_walk i hi j current (past t) (hactive t (Finset.mem_insert_self _ _)) hwalk hcut (B t) (hb t (Finset.mem_insert_self _ _)))
      (ih (fun r hr => hactive r (Finset.mem_insert_of_mem hr)) (fun r hr => hb r (Finset.mem_insert_of_mem hr)))
end DecrAlmostLinearSSSP.Decremental
end s209
section s210
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
lemma eligible_iff (i : Input) (b : Fin (scaleCount i) → Fin i.n → ℝ≥0∞)
    (v : Fin i.n) (j : Fin (scaleCount i)) :
    eligible i b v j.val = true ↔ ENNReal.ofReal (delta i j.val) * b j v ≤ ENNReal.ofReal (2 * scale j.val) := by
  simp only [eligible, dif_pos j.isLt, decide_eq_true_eq]
lemma pointer_finite_readout (i : Input) (hi : i.Valid)
    (b : Fin (scaleCount i) → Fin i.n → ℝ≥0∞) (v : Fin i.n) (p : ℕ) (d : ℝ)
    (hp : PointerValid i b v p) (hd : 1 ≤ d) (hbound : d ≤ (i.n : ℝ) * i.W)
    (hlower : ∀ j, ENNReal.ofReal d ≤ ENNReal.ofReal (delta i j.val) * b j v)
    (hupper : ∀ j : Fin (scaleCount i), ENNReal.ofReal d ≤ ENNReal.ofReal (2 * scale j.val) →
      ENNReal.ofReal (delta i j.val) * b j v ≤
        ENNReal.ofReal ((1 + i.accuracy / 16) * (d + i.accuracy * scale j.val / 128))) :
    ∃ h : p < scaleCount i,
      ENNReal.ofReal d ≤ ENNReal.ofReal (delta i p) * b ⟨p,h⟩ v ∧
      ENNReal.ofReal (delta i p) * b ⟨p,h⟩ v ≤ ENNReal.ofReal ((1 + i.accuracy / 8) * d) := by
  classical
  have hd0 : 0 ≤ d := le_trans zero_le_one hd
  obtain ⟨j, hjlo, hjhi⟩ := scale_covers_distance i d hd hbound
  have hjcut : ENNReal.ofReal d ≤ ENNReal.ofReal (2 * scale j.val) :=
    ENNReal.ofReal_le_ofReal (by have hs := scale_positive j.val; linarith)
  have hje : eligible i b v j.val = true := by
    apply (eligible_iff i b v j).mpr
    apply (hupper j hjcut).trans
    apply ENNReal.ofReal_le_ofReal
    have hr := rounding_factor_bound hi.2.2.2.1 hi.2.2.2.2.1 hd0 hjhi
    have he := hi.2.2.2.2.1
    nlinarith only [hr, mul_le_mul_of_nonneg_right he hd0, hjlo, hd0]
  have hpj : p ≤ j.val := by
    by_contra hh
    have hf := hp.2.1 j.val (by omega)
    rw [hje] at hf
    contradiction
  have hpn : p < scaleCount i := lt_of_le_of_lt hpj j.isLt
  let q : Fin (scaleCount i) := ⟨p,hpn⟩
  have hqscale : scale q.val ≤ 2 * d := by
    have hpow : scale q.val ≤ scale j.val := by
      unfold scale
      gcongr
      norm_num
    exact hpow.trans hjhi
  have hqeligible : ENNReal.ofReal (delta i q.val) * b q v ≤ ENNReal.ofReal (2 * scale q.val) :=
    (eligible_iff i b v q).mp (hp.2.2 hpn)
  have hqcut := (hlower q).trans hqeligible
  refine ⟨hpn, hlower q, (hupper q hqcut).trans ?_⟩
  exact ENNReal.ofReal_le_ofReal (rounding_factor_bound hi.2.2.2.1 hi.2.2.2.2.1 hd0 hqscale)
lemma pointer_infinite_readout (i : Input)
    (b : Fin (scaleCount i) → Fin i.n → ℝ≥0∞) (v : Fin i.n) (p : ℕ)
    (hp : PointerValid i b v p)
    (hlower : ∀ j, (⊤ : ℝ≥0∞) ≤ ENNReal.ofReal (delta i j.val) * b j v) : p = scaleCount i := by
  apply le_antisymm hp.1
  by_contra hh
  have hpn : p < scaleCount i := by omega
  let j : Fin (scaleCount i) := ⟨p,hpn⟩
  have he := (eligible_iff i b v j).mp (hp.2.2 hpn)
  have ht := (hlower j).trans he
  exact ENNReal.ofReal_ne_top (top_le_iff.mp ht)
end DecrAlmostLinearSSSP.Decremental
end s210
section s211
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
lemma pointer_finite_readout_guarded (i : Input) (hi : i.Valid)
    (b : Fin (scaleCount i) → Fin i.n → ℝ≥0∞) (v : Fin i.n) (p : ℕ) (d : ℝ)
    (hp : PointerValid i b v p) (hd : 1 ≤ d) (hbound : d ≤ (i.n : ℝ) * i.W)
    (hlower : ∀ j : Fin (scaleCount i), eligible i b v j.val = true →
      ENNReal.ofReal d ≤ ENNReal.ofReal (delta i j.val) * b j v)
    (hupper : ∀ j : Fin (scaleCount i), ENNReal.ofReal d ≤ ENNReal.ofReal (2 * scale j.val) →
      ENNReal.ofReal (delta i j.val) * b j v ≤
        ENNReal.ofReal ((1 + i.accuracy / 16) * (d + i.accuracy * scale j.val / 128))) :
    ∃ h : p < scaleCount i,
      ENNReal.ofReal d ≤ ENNReal.ofReal (delta i p) * b ⟨p,h⟩ v ∧
      ENNReal.ofReal (delta i p) * b ⟨p,h⟩ v ≤ ENNReal.ofReal ((1 + i.accuracy / 8) * d) := by
  classical
  have hd0 : 0 ≤ d := le_trans zero_le_one hd
  obtain ⟨j, hjlo, hjhi⟩ := scale_covers_distance i d hd hbound
  have hjcut : ENNReal.ofReal d ≤ ENNReal.ofReal (2 * scale j.val) :=
    ENNReal.ofReal_le_ofReal (by have hs := scale_positive j.val; linarith)
  have hje : eligible i b v j.val = true := by
    apply (eligible_iff i b v j).mpr
    apply (hupper j hjcut).trans
    apply ENNReal.ofReal_le_ofReal
    have hr := rounding_factor_bound hi.2.2.2.1 hi.2.2.2.2.1 hd0 hjhi
    have he := hi.2.2.2.2.1
    nlinarith only [hr, mul_le_mul_of_nonneg_right he hd0, hjlo, hd0]
  have hpj : p ≤ j.val := by
    by_contra hh
    have hf := hp.2.1 j.val (by omega)
    rw [hje] at hf
    contradiction
  have hpn : p < scaleCount i := lt_of_le_of_lt hpj j.isLt
  let q : Fin (scaleCount i) := ⟨p,hpn⟩
  have hqscale : scale q.val ≤ 2 * d := by
    have hpow : scale q.val ≤ scale j.val := by
      unfold scale
      gcongr
      norm_num
    exact hpow.trans hjhi
  have hqeligible : ENNReal.ofReal (delta i q.val) * b q v ≤ ENNReal.ofReal (2 * scale q.val) :=
    (eligible_iff i b v q).mp (hp.2.2 hpn)
  have hqlower := hlower q (hp.2.2 hpn)
  have hqcut := hqlower.trans hqeligible
  refine ⟨hpn, hqlower, (hupper q hqcut).trans ?_⟩
  exact ENNReal.ofReal_le_ofReal (rounding_factor_bound hi.2.2.2.1 hi.2.2.2.2.1 hd0 hqscale)
lemma pointer_infinite_readout_guarded (i : Input)
    (b : Fin (scaleCount i) → Fin i.n → ℝ≥0∞) (v : Fin i.n) (p : ℕ)
    (hp : PointerValid i b v p)
    (hlower : ∀ j : Fin (scaleCount i), eligible i b v j.val = true →
      (⊤ : ℝ≥0∞) ≤ ENNReal.ofReal (delta i j.val) * b j v) : p = scaleCount i := by
  apply le_antisymm hp.1
  by_contra hh
  have hpn : p < scaleCount i := by omega
  let j : Fin (scaleCount i) := ⟨p,hpn⟩
  have he := (eligible_iff i b v j).mp (hp.2.2 hpn)
  have ht := (hlower j (hp.2.2 hpn)).trans he
  exact ENNReal.ofReal_ne_top (top_le_iff.mp ht)
end DecrAlmostLinearSSSP.Decremental
end s211
section s212
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
lemma singleton_halt (c : Machine) (hc : c.pc = 0) (hh : c.halted = false)
    (hf : c.fault = false) : Ends singletonProgram c (haltState c) := by
  refine ⟨1, ?_, rfl, hf⟩
  change step singletonProgram c = _
  simp [step, singletonProgram, haltState, hc, hh]
lemma distance_self {n k : ℕ} (g : Digraph n k) (active : Finset (Fin k))
    (w : Fin k → ℝ≥0∞) (s : Fin n) : distance g active w s s = 0 := by
  apply le_antisymm _ bot_le
  exact iInf_le_of_le [] (iInf_le_of_le (Walk.nil s) (by simp))
lemma singleton_vertex (i : Input) (hn : i.n = 1) (v : Fin i.n) : v = i.source := by
  apply Fin.ext
  have hv := v.isLt
  have hs := i.source.isLt
  have hv0 : v.val = 0 := by omega
  have hs0 : i.source.val = 0 := by omega
  omega
lemma singleton_input_memory (i : Input) (v : Fin i.n) :
    (initialMachine singletonProgram i).natMem v.val = 0 := by
  simp only [initialMachine]
  have hh : ¬ (i.n ≤ v.val ∧ (v.val - i.n) / 3 < i.k) := fun h => (not_le.mpr v.isLt) h.1
  simp only [dif_neg hh]
lemma singleton_online (i : Input) (ds : List (Fin i.k)) :
    ∃ (cs : List Machine) (c : Machine), OnlineRun singletonProgram i ds cs ∧
      cs.length = ds.length + 1 ∧ cs.getLast? = some c ∧ c.work = ds.length + 1 ∧
      (∀ d ∈ cs, (∀ v : Fin i.n, d.natMem v.val = 0) ∧ d.realMem = fun _ => 0) := by
  classical
  induction ds using List.reverseRecOn with
  | nil =>
    let c := haltState (initialMachine singletonProgram i)
    refine ⟨[c], c, .init (singleton_halt _ rfl rfl rfl), rfl, rfl, rfl, ?_⟩
    intro d hd
    simp only [List.mem_singleton] at hd
    subst d
    exact ⟨singleton_input_memory i, rfl⟩
  | append_singleton ds e ih =>
    obtain ⟨cs, c, hr, hl, hc, hw, hm⟩ := ih
    let start := deletionMachine singletonProgram c e.val
    let d := haltState start
    have hd : Ends singletonProgram start d := singleton_halt start rfl rfl rfl
    have hc_mem : c ∈ cs := List.mem_of_getLast? hc
    obtain ⟨hcm, hcr⟩ := hm c hc_mem
    refine ⟨cs ++ [d], d, .next hr hc e hd, ?_, ?_, ?_, ?_⟩
    · simp only [List.length_append, List.length_singleton, hl]
    · simp
    · simpa only [d, haltState, start, deletionMachine, resume, List.length_append, List.length_singleton] using congrArg (· + 1) hw
    · intro z hz
      rcases List.mem_append.mp hz with hz | hz
      · exact hm z hz
      · simp only [List.mem_singleton] at hz
        subst z
        exact ⟨hcm, hcr⟩
lemma singleton_maintains (i : Input) (hi : i.Valid) (hn : i.n = 1) :
    Maintains singletonProgram 8 (fun _ => 1) 9 false i := by
  classical
  intro ds hd
  obtain ⟨cs, last, hr, hl, hlast, hw, hm⟩ := singleton_online i ds
  refine ⟨cs, hr, hl, ?_, ?_, ?_⟩
  · intro j c hc
    obtain ⟨hcm, hcr⟩ := hm c (List.mem_of_getElem? hc)
    have hstored (v : Fin i.n) : stored c v.val = 0 := by simp [stored, hcm v, hcr]
    refine ⟨hstored i.source, ?_, ?_⟩
    · intro v
      refine ⟨by rw [hcm v]; omega, ?_⟩
      intro _
      rw [hcr]
    · intro v
      have hv := singleton_vertex i hn v
      have hdist : i.dist (ds.take j) v = 0 := by rw [hv]; exact distance_self _ _ _ _
      have hreach : Reachable i.graph (live (ds.take j)) i.source v := by rw [hv]; exact ⟨[], .nil _⟩
      simp [hdist, hstored v, hreach]
  · intro c hc
    have heq : c = last := Option.some.inj (hc.symm.trans hlast)
    subst c
    rw [hw]
    have hlen : ds.length ≤ i.size := by
      have hh := hd.length_le_card
      simp only [Fintype.card_fin] at hh
      exact hh.trans hi.2.1
    have hmpos : 1 ≤ i.size := by rw [← hn]; exact hi.1
    have ha : 0 < i.accuracy := hi.2.2.2.1
    have heps : i.accuracy ≤ 1 := hi.2.2.2.2.1
    simp only [Bool.false_eq_true, if_false, mul_one]
    apply (le_div_iff₀ ha).mpr
    push_cast
    have hln : (ds.length : ℝ) ≤ i.size := by exact_mod_cast hlen
    have hmn : (1 : ℝ) ≤ i.size := by exact_mod_cast hmpos
    have hp : 0 ≤ (ds.length : ℝ) + 1 + 6 * ds.length := by positivity
    nlinarith
  · intro c hc v
    exact ram_query_nine singletonProgram rfl rfl rfl c v.val
end DecrAlmostLinearSSSP.Decremental
end s212
section s213
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
lemma selected_accuracy_guarded (i : Input) (hi : i.Valid) (active : Finset (Fin i.k))
    (b : Fin (scaleCount i) → Fin i.n → ℝ≥0∞) (p : Fin i.n → ℕ)
    (hp : ∀ v, PointerValid i b v (p v))
    (hlower : ∀ v (j : Fin (scaleCount i)), eligible i b v j.val = true →
      distance i.graph active (fun e => (i.weight e : ℝ≥0∞)) i.source v ≤
        ENNReal.ofReal (delta i j.val) * b j v)
    (hupper : ∀ v (j : Fin (scaleCount i)) (d : ℝ), 1 ≤ d →
      distance i.graph active (fun e => (i.weight e : ℝ≥0∞)) i.source v = ENNReal.ofReal d →
      ENNReal.ofReal d ≤ ENNReal.ofReal (2 * scale j.val) →
      ENNReal.ofReal (delta i j.val) * b j v ≤
        ENNReal.ofReal ((1 + i.accuracy / 16) * (d + i.accuracy * scale j.val / 128))) :
    ∀ v, distance i.graph active (fun e => (i.weight e : ℝ≥0∞)) i.source v ≤ selected i b p v ∧
      selected i b p v ≤ ENNReal.ofReal (1 + i.accuracy) *
        distance i.graph active (fun e => (i.weight e : ℝ≥0∞)) i.source v ∧
      (selected i b p v = ⊤ ↔ ¬ Reachable i.graph active i.source v) := by
  classical
  intro v
  by_cases hv : v = i.source
  · subst v
    have hr : Reachable i.graph active i.source i.source := ⟨[], .nil _⟩
    simp [selected, distance_self, hr]
  · by_cases hr : Reachable i.graph active i.source v
    · obtain ⟨d, hd, hdhi, hdist⟩ := input_reachable_distance_bounds i hi active v hr hv
      have hlo : ∀ j : Fin (scaleCount i), eligible i b v j.val = true →
          ENNReal.ofReal d ≤ ENNReal.ofReal (delta i j.val) * b j v := by
        intro j hj
        rw [← hdist]
        exact hlower v j hj
      obtain ⟨hpn, hl, hu⟩ := pointer_finite_readout_guarded i hi b v (p v) d (hp v) hd hdhi hlo
        (fun j hj => hupper v j d hd hdist hj)
      have hout : selected i b p v = ENNReal.ofReal (delta i (p v)) * b ⟨p v,hpn⟩ v := by
        simp only [selected, if_neg hv, dif_pos hpn]
      rw [hout, hdist]
      refine ⟨hl, ?_, ?_⟩
      · have he : 0 ≤ 1 + i.accuracy := by have hh := hi.2.2.2.1; positivity
        rw [← ENNReal.ofReal_mul he]
        apply hu.trans
        apply ENNReal.ofReal_le_ofReal
        have hd0 : 0 ≤ d := le_trans zero_le_one hd
        have heps := hi.2.2.2.1
        nlinarith only [mul_nonneg heps.le hd0]
      · have hfin : ENNReal.ofReal (delta i (p v)) * b ⟨p v,hpn⟩ v ≠ ⊤ :=
          ne_top_of_le_ne_top ENNReal.ofReal_ne_top hu
        simp only [hfin, hr, not_true_eq_false]
    · have hdist := distance_top_of_unreachable i.graph active (fun e => (i.weight e : ℝ≥0∞)) i.source v hr
      have hlo : ∀ j : Fin (scaleCount i), eligible i b v j.val = true →
          (⊤ : ℝ≥0∞) ≤ ENNReal.ofReal (delta i j.val) * b j v := by
        intro j hj
        rw [← hdist]
        exact hlower v j hj
      have hpn := pointer_infinite_readout_guarded i b v (p v) (hp v) hlo
      have hout : selected i b p v = ⊤ := by simp [selected, hv, hpn]
      have hpos : ENNReal.ofReal (1 + i.accuracy) ≠ 0 := by
        have he := hi.2.2.2.1
        exact (ENNReal.ofReal_pos.mpr (by linarith)).ne'
      simp [hout, hdist, hr, ENNReal.mul_top hpos]
end DecrAlmostLinearSSSP.Decremental
end s213
section s214
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
lemma barrier_readout_lower_guarded (i : Input) (hi : i.Valid) (j : ℕ)
    (active : Finset (Fin i.k)) (u v : Fin i.n) (B : ℝ≥0∞)
    (hB : distance (barrierInput i j).graph active
      (fun e => ((barrierInput i j).weight e : ℝ≥0∞)) u v ≤ B)
    (hguard : ENNReal.ofReal (delta i j)*B ≤ ENNReal.ofReal (2*scale j)) :
    distance i.graph active (fun e => (i.weight e : ℝ≥0∞)) u v ≤ ENNReal.ofReal (delta i j)*B := by
  have hh := mul_le_mul_right hB (ENNReal.ofReal (delta i j))
  exact (barrier_distance_lower_guarded i hi j active u v (hh.trans hguard)).trans hh
lemma barrier_historical_shortest_upper (i : Input) (hi : i.Valid) (j : ℕ)
    {ι : Type} (S : Finset ι) (past : ι → Finset (Fin i.k))
    (current : Finset (Fin i.k)) (hactive : ∀ t ∈ S, current ⊆ past t)
    (u v : Fin i.n) (d : ℝ) (hd : 1 ≤ d)
    (hdist : distance i.graph current (fun e => (i.weight e : ℝ≥0∞)) u v = ENNReal.ofReal d)
    (hcut : ENNReal.ofReal d ≤ ENNReal.ofReal (2*scale j)) (B : ι → ℝ≥0∞)
    (hb : ∀ t ∈ S, B t ≤ ENNReal.ofReal (1+i.accuracy/16)*
      distance (barrierInput i j).graph (past t)
        (fun e => ((barrierInput i j).weight e : ℝ≥0∞)) u v) :
    ENNReal.ofReal (delta i j)*S.sup B ≤
      ENNReal.ofReal ((1+i.accuracy/16)*(d+i.accuracy*scale j/128)) := by
  have hs := scale_positive j
  have hd0 : 0 ≤ d := le_trans zero_le_one hd
  have hr : Reachable i.graph current u v := by
    by_contra hn
    have ht := distance_top_of_unreachable i.graph current (fun e => (i.weight e : ℝ≥0∞)) u v hn
    rw [ht] at hdist
    exact ENNReal.ofReal_ne_top hdist.symm
  obtain ⟨es,hes,hlen,heq⟩ := distance_min_weight i.graph current
    (fun e => (i.weight e : ℝ)) (fun e => Nat.cast_nonneg _) u v hr
  have hsum : (es.map (fun e => (i.weight e : ℝ))).sum = d := by
    have hn : 0 ≤ (es.map (fun e => (i.weight e : ℝ))).sum := List.sum_nonneg (by
      intro x hx
      obtain ⟨e,_,rfl⟩ := List.mem_map.mp hx
      exact Nat.cast_nonneg _)
    have heq' : ENNReal.ofReal ((es.map (fun e => (i.weight e : ℝ))).sum) = ENNReal.ofReal d := by
      rw [← hdist]
      simpa only [ENNReal.ofReal_natCast] using heq.symm
    exact le_antisymm ((ENNReal.ofReal_le_ofReal_iff hd0).mp heq'.le)
      ((ENNReal.ofReal_le_ofReal_iff hn).mp heq'.symm.le)
  have hdb : d ≤ 2*scale j := (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ 2*scale j)).mp hcut
  have hwalkcut : ∀ e ∈ es, (i.weight e : ℝ) ≤ 2*scale j := by
    intro e he
    have hh := real_weight_le_walk_sum i.weight es e he
    rw [hsum] at hh
    exact hh.trans hdb
  have hh := barrier_historical_readout_finite_family i hi j S past current hactive hes hwalkcut B hb
  apply hh.trans
  apply ENNReal.ofReal_le_ofReal
  have hlenR : (es.length : ℝ) ≤ i.n := by exact_mod_cast hlen.le
  have hdelt := delta_positive i hi j
  have herror : (i.n : ℝ)*delta i j = i.accuracy*scale j/128 := by
    have hn : (0 : ℝ) < i.n := by exact_mod_cast input_vertex_positive i
    unfold delta
    field_simp
  rw [hsum]
  apply mul_le_mul_of_nonneg_left _ (by have he := hi.2.2.2.1; positivity)
  have he := mul_le_mul_of_nonneg_right hlenR hdelt.le
  rw [herror] at he
  linarith
end DecrAlmostLinearSSSP.Decremental
end s214
section s215
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
lemma barrier_cache_selected_accuracy (i : Input) (hi : i.Valid) {ι : Type}
    (S : Finset ι) (past : ι → Finset (Fin i.k)) (current : Finset (Fin i.k))
    (hactive : ∀ t ∈ S, current ⊆ past t)
    (B : Fin (scaleCount i) → ι → Fin i.n → ℝ≥0∞)
    (cache : Fin (scaleCount i) → Fin i.n → ℝ≥0∞)
    (hcurrent : ∀ (j : Fin (scaleCount i)) (v : Fin i.n),
      distance (barrierInput i j.val).graph current
        (fun e => ((barrierInput i j.val).weight e : ℝ≥0∞)) i.source v ≤ cache j v)
    (hcache : ∀ j v, cache j v ≤ S.sup (fun t => B j t v))
    (hhistory : ∀ (j : Fin (scaleCount i)) t, t ∈ S → ∀ v : Fin i.n,
      B j t v ≤ ENNReal.ofReal (1+i.accuracy/16)*
        distance (barrierInput i j.val).graph (past t)
          (fun e => ((barrierInput i j.val).weight e : ℝ≥0∞)) i.source v)
    (p : Fin i.n → ℕ) (hp : ∀ v, PointerValid i cache v (p v)) :
    ∀ v, distance i.graph current (fun e => (i.weight e : ℝ≥0∞)) i.source v ≤ selected i cache p v ∧
      selected i cache p v ≤ ENNReal.ofReal (1+i.accuracy)*
        distance i.graph current (fun e => (i.weight e : ℝ≥0∞)) i.source v ∧
      (selected i cache p v = ⊤ ↔ ¬Reachable i.graph current i.source v) := by
  apply selected_accuracy_guarded i hi current cache p hp
  · intro v j hj
    exact barrier_readout_lower_guarded i hi j.val current i.source v (cache j v) (hcurrent j v)
      ((eligible_iff i cache v j).mp hj)
  · intro v j d hd hdist hcut
    apply (mul_le_mul_right (hcache j v) (ENNReal.ofReal (delta i j.val))).trans
    exact barrier_historical_shortest_upper i hi j.val S past current hactive i.source v d hd hdist hcut
      (fun t => B j t v) (fun t ht => hhistory j t ht v)
end DecrAlmostLinearSSSP.Decremental
end s215
section s216
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
lemma initial_selected_accuracy (i : Input) (hi : i.Valid) (p : Program) (C : ℝ) (a : ℕ → ℝ)
    (f : Fin (scaleCount i) → Machine) (hf : ∀ q, InitialFacts p C a i q.val (f q)) :
    ∀ v : Fin i.n, i.dist [] v ≤ selected i (fun q v => stored (f q) v.val)
        (initialPointers i (fun q v => stored (f q) v.val)) v ∧
      selected i (fun q v => stored (f q) v.val) (initialPointers i (fun q v => stored (f q) v.val)) v ≤
        ENNReal.ofReal (1+i.accuracy)*i.dist [] v ∧
      (selected i (fun q v => stored (f q) v.val) (initialPointers i (fun q v => stored (f q) v.val)) v = ⊤ ↔
        ¬Reachable i.graph (live []) i.source v) := by
  classical
  let b : Fin (scaleCount i) → Fin i.n → ℝ≥0∞ := fun q v => stored (f q) v.val
  have hcurrent : ∀ (q : Fin (scaleCount i)) (v : Fin i.n),
      distance (barrierInput i q.val).graph Finset.univ
        (fun e => ((barrierInput i q.val).weight e : ℝ≥0∞)) i.source v ≤ b q v := by
    intro q v
    have hh := ((hf q).accurate v).1
    unfold Input.dist at hh
    rw [show live ([] : List (Fin (barrierInput i q.val).k)) = Finset.univ by simp only [live,List.toFinset_nil,Finset.sdiff_empty]] at hh
    simpa only [b,barrierInput] using hh
  have hhistory : ∀ (q : Fin (scaleCount i)) (t : Unit), t ∈ ({()} : Finset Unit) → ∀ v : Fin i.n,
      b q v ≤ ENNReal.ofReal (1+i.accuracy/16)*distance (barrierInput i q.val).graph Finset.univ
        (fun e => ((barrierInput i q.val).weight e : ℝ≥0∞)) i.source v := by
    intro q t ht v
    have hh := ((hf q).accurate v).2.1
    unfold Input.dist at hh
    rw [show live ([] : List (Fin (barrierInput i q.val).k)) = Finset.univ by simp only [live,List.toFinset_nil,Finset.sdiff_empty]] at hh
    simpa only [b,barrierInput] using hh
  have hp : ∀ v, PointerValid i b v (initialPointers i b v) := by
    intro v
    simpa only [initialPointers,adapterInitialize] using adapterInitialize_pointer_valid i b v
  have hh := barrier_cache_selected_accuracy i hi ({()} : Finset Unit) (fun _ : Unit => Finset.univ) Finset.univ
    (fun _ _ => Finset.Subset.refl _) (fun q (_ : Unit) v => b q v) b hcurrent
    (by intro q v;simp) hhistory (initialPointers i b) hp
  simpa only [Input.dist,live,List.toFinset_nil,Finset.sdiff_empty] using hh
end DecrAlmostLinearSSSP.Decremental.Native
end s216
section s217
set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Native
open Structured
lemma initDone_scanTable (i : Input) (p : Program) (B reserve : ℕ) (f : Fin (scaleCount i) → Machine)
    (s : Data) (h : InitDone i p B reserve f s) :
    ScanTable i (pointerLayout B i.n (scaleCount i) reserve (registerBound p.code)).record
      (pointerLayout B i.n (scaleCount i) reserve (registerBound p.code)).cache (2*registerBound p.code+8)
      (fun q v => stored (f q) v.val) s := by
  constructor
  · dsimp [pointerLayout,scaleLayout,Layout.addresses]
    omega
  · intro q
    exact (h.completed q).metadata
  · intro q
    exact (h.completed q).cache
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
theorem solution : (((((((DecrAlmostLinearSSSP.Decremental.Structured.NoMemory DecrAlmostLinearSSSP.Decremental.Native.pointerStart) ∧ (DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame DecrAlmostLinearSSSP.Decremental.Native.pointerStart)) ∧ ((∀ {record pointer flags list cost : Nat} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.PointerBases record pointer flags list s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Native.pointerStart s cost t →
      DecrAlmostLinearSSSP.Decremental.Native.PointerBases record pointer flags list t) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B reserve N : Nat}
  {b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.PointerPrefix i B reserve N b i.n s →
    @DecrAlmostLinearSSSP.Decremental.DirtyMark.View i.n
      (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i)
          reserve N).flags
      (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i)
          reserve N).list
      (List.finRange i.n) s))) ∧ (((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (B reserve N : Nat)
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
                  i.n s t)))) ∧ (DecrAlmostLinearSSSP.Decremental.TailFrame DecrAlmostLinearSSSP.Decremental.Native.pointerStart)) ∧ ((DecrAlmostLinearSSSP.Decremental.TailFrame DecrAlmostLinearSSSP.Decremental.Native.buildPointers) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
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
              (And (@Eq.{1} (Nat → Real) t.realMem s.realMem) (@Eq.{1} (Nat → Nat) t.natMem s.natMem)))))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    ∃ cost t,
      And (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.PointerRead.code s cost t)
        (And (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
          (And
            (@Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.ExtendedMax.incoming t)
              (@ite.{1} ENNReal
                (@Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.PointerRead.pointer s)
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                (instDecidableEqNat (DecrAlmostLinearSSSP.Decremental.PointerRead.pointer s)
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                (@Top.top.{0} ENNReal ENNReal.instTop)
                (DecrAlmostLinearSSSP.Decremental.ExtendedMax.cell s
                  (DecrAlmostLinearSSSP.Decremental.PointerRead.cellAddress s))))
            (And (@Eq.{1} (Nat → Real) t.realMem s.realMem) (@Eq.{1} (Nat → Nat) t.natMem s.natMem))))))))) ∧ ((((DecrAlmostLinearSSSP.Decremental.Structured.NoMemory DecrAlmostLinearSSSP.Decremental.PointerRead.code) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.SelectedRead.prefixCode s
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    (DecrAlmostLinearSSSP.Decremental.SelectedRead.prefixData s))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
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
            @Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.SelectedRead.prefixData s).natReg k) (s.natReg k)))) ∧ (DecrAlmostLinearSSSP.Decremental.Structured.NoMemory DecrAlmostLinearSSSP.Decremental.SelectedRead.code))) ∧ (((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    ∃ cost t,
      And
        (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.SelectedRead.chooseCode s
          cost t)
        (And (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))
          (@Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.ExtendedMax.incoming t)
            (@ite.{1} ENNReal
              (@Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94))))
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72)))))
              (instDecidableEqNat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94))))
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72)))))
              (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero))
              (@ite.{1} ENNReal
                (@Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.PointerRead.pointer s)
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                (instDecidableEqNat (DecrAlmostLinearSSSP.Decremental.PointerRead.pointer s)
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                (@Top.top.{0} ENNReal ENNReal.instTop)
                (DecrAlmostLinearSSSP.Decremental.ExtendedMax.cell s
                  (DecrAlmostLinearSSSP.Decremental.PointerRead.cellAddress s))))))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    ∃ cost t,
      And (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.SelectedRead.code s cost t)
        (And (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11))))
          (And
            (@Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.ExtendedMax.incoming t)
              (DecrAlmostLinearSSSP.Decremental.SelectedRead.value s))
            (And (@Eq.{1} (Nat → Real) t.realMem s.realMem) (@Eq.{1} (Nat → Nat) t.natMem s.natMem)))))) ∧ ((∀ {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {cost : Nat},
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.SelectedRead.chooseCode s cost t →
      And
        (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))))
          (@ite.{1} Nat
            (@Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94))))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72)))))
            (instDecidableEqNat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94))))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72)))))
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@ite.{1} Nat
              (@Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.PointerRead.pointer s)
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (instDecidableEqNat (DecrAlmostLinearSSSP.Decremental.PointerRead.pointer s)
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (s.natMem (DecrAlmostLinearSSSP.Decremental.PointerRead.cellAddress s)))))
        (@Eq.{1} Real (t.realReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))))
          (@ite.{1} Real
            (@Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94))))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72)))))
            (instDecidableEqNat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94))))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72)))))
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (@ite.{1} Real
              (@Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.PointerRead.pointer s)
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (instDecidableEqNat (DecrAlmostLinearSSSP.Decremental.PointerRead.pointer s)
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              (s.realMem (DecrAlmostLinearSSSP.Decremental.PointerRead.cellAddress s)))))) ∧ ((∀ {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {cost : Nat},
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.SelectedRead.code s cost t →
      And
        (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))))
          (DecrAlmostLinearSSSP.Decremental.SelectedRead.flag s))
        (@Eq.{1} Real (t.realReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))))
          (DecrAlmostLinearSSSP.Decremental.SelectedRead.realValue s))) ∧ (∀ {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {cost : Nat},
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
                (t.realReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))))))))))) ∧ (((((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 38) (instOfNatNat (nat_lit 38))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 196) (instOfNatNat (nat_lit 196))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 44) (instOfNatNat (nat_lit 44))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) →
              DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.SelectedRead.code k) ∧ (∀ {n : Nat} {l : DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout n}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  @DecrAlmostLinearSSSP.Decremental.AnswerTable.Image n l s →
    (∀ (address : Nat),
        @DecrAlmostLinearSSSP.Decremental.AnswerTable.Protected n l address →
          And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
            (@Eq.{1} Real (t.realMem address) (s.realMem address))) →
      @DecrAlmostLinearSSSP.Decremental.AnswerTable.Image n l t)) ∧ ((∀ {n : Nat} (l : DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout n)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (v : Fin n),
  @DecrAlmostLinearSSSP.Decremental.AnswerTable.Image n l s →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 96) (instOfNatNat (nat_lit 96))))
        (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.pointerBase n l) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72))))
          (@Fin.val n (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.source n l)) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94)))) (@Fin.val n v) →
          And
            (@Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.SelectedRead.flag s)
              (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.flag n l v))
            (@Eq.{1} Real (DecrAlmostLinearSSSP.Decremental.SelectedRead.realValue s)
              (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.realValue n l v))) ∧ (∀ {n : Nat} {l : DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout n}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  @DecrAlmostLinearSSSP.Decremental.AnswerTable.Image n l s →
    @Eq.{1} (Nat → Nat) t.natMem s.natMem →
      @Eq.{1} (Nat → Real) t.realMem s.realMem → @DecrAlmostLinearSSSP.Decremental.AnswerTable.Image n l t))) ∧ (((∀ {n : Nat} (l : DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout n),
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
              (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.realValue n l v))) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {base stride j : Nat},
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) base →
    Iff
      (@Ne.{1} Nat (DecrAlmostLinearSSSP.Decremental.Native.scanRecord i base stride j)
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@LT.lt.{0} Nat instLTNat j (DecrAlmostLinearSSSP.Decremental.scaleCount i)))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (recordBase cacheBase stride pointerBase : Nat) (p : Fin i.n → Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data)
  (b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal),
  DecrAlmostLinearSSSP.Decremental.Native.ScanTable i recordBase cacheBase stride b s →
    (∀ (v : Fin i.n),
        @Eq.{1} Nat
          (s.natMem
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pointerBase
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val i.n v))))
          (DecrAlmostLinearSSSP.Decremental.Native.scanRecord i recordBase stride (p v))) →
      @DecrAlmostLinearSSSP.Decremental.AnswerTable.Image i.n
        (DecrAlmostLinearSSSP.Decremental.Native.answerLayout i recordBase cacheBase stride pointerBase p s) s) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (recordBase cacheBase stride pointerBase : Nat) (p : Fin i.n → Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data)
  (b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal),
  DecrAlmostLinearSSSP.Decremental.Native.ScanTable i recordBase cacheBase stride b s →
    ∀ (v : Fin i.n),
      And
        (@LE.le.{0} Nat instLENat
          (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.flag i.n
            (DecrAlmostLinearSSSP.Decremental.Native.answerLayout i recordBase cacheBase stride pointerBase p s) v)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@Eq.{1} Nat
            (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.flag i.n
              (DecrAlmostLinearSSSP.Decremental.Native.answerLayout i recordBase cacheBase stride pointerBase p s) v)
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
          @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.realValue i.n
              (DecrAlmostLinearSSSP.Decremental.Native.answerLayout i recordBase cacheBase stride pointerBase p s) v))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (recordBase cacheBase stride pointerBase : Nat) (p : Fin i.n → Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data)
  (b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal),
  DecrAlmostLinearSSSP.Decremental.Native.ScanTable i recordBase cacheBase stride b s →
    ∀ (v : Fin i.n),
      @Eq.{1} ENNReal
        (@ite.{1} ENNReal
          (@Eq.{1} Nat
            (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.flag i.n
              (DecrAlmostLinearSSSP.Decremental.Native.answerLayout i recordBase cacheBase stride pointerBase p s) v)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (instDecidableEqNat
            (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.flag i.n
              (DecrAlmostLinearSSSP.Decremental.Native.answerLayout i recordBase cacheBase stride pointerBase p s) v)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@Top.top.{0} ENNReal ENNReal.instTop)
          (ENNReal.ofReal
            (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.realValue i.n
              (DecrAlmostLinearSSSP.Decremental.Native.answerLayout i recordBase cacheBase stride pointerBase p s) v)))
        (DecrAlmostLinearSSSP.Decremental.selected i b p v)))))) ∧ ((((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (B reserve N : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data)
  (b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal) (p : Fin i.n → Nat),
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
    @LE.le.{0} Nat instLENat i.n B →
      ∀ (address : Nat),
        @DecrAlmostLinearSSSP.Decremental.AnswerTable.Protected i.n
            (DecrAlmostLinearSSSP.Decremental.Native.answerLayout i
              (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                  (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).record
              (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                  (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).cache
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) N)
                (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
              (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                  (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).pointer
              p s)
            address →
          And (@LE.le.{0} Nat instLENat i.n address)
            (∀ (v : Fin i.n),
              @Ne.{1} Nat address
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                      (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).flags
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val i.n v))))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.DirtyCommit.suffix s
    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
    (DecrAlmostLinearSSSP.Decremental.DirtyCommit.afterStores s))) ∧ ((∀ {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {cost : Nat},
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.SelectedRead.code s cost t →
    ∀ (k : Nat),
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 38) (instOfNatNat (nat_lit 38))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 196) (instOfNatNat (nat_lit 196))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 44) (instOfNatNat (nat_lit 44))) →
              @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) →
                @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) →
                  @Eq.{1} Nat (t.natReg k) (s.natReg k)) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
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
                                  (@Eq.{1} Real (t.realMem address) (s.realMem address)))))))))) ∧ (∀ (k : Nat),
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
                        DecrAlmostLinearSSSP.Decremental.DirtyCommit.body k)))) ∧ (((∀ {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {cost : Nat},
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.DirtyCommit.body s cost t →
    And
      (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))))
      (And
        (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26)))))
        (And
          (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56)))))
          (And
            (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72))))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72)))))
            (And
              (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 96) (instOfNatNat (nat_lit 96))))
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 96) (instOfNatNat (nat_lit 96)))))
              (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 98) (instOfNatNat (nat_lit 98))))
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 98) (instOfNatNat (nat_lit 98)))))))))) ∧ (∀ {n : Nat} (l : DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout n) (flagBase listBase : Nat),
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
        ∀ (xs : List.{0} (Fin n)) (readBase : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
          @LE.le.{0} Nat instLENat listBase readBase →
            @DecrAlmostLinearSSSP.Decremental.AnswerTable.Image n l s →
              @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 96) (instOfNatNat (nat_lit 96))))
                  (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.pointerBase n l) →
                @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72))))
                    (@Fin.val n (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.source n l)) →
                  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 98) (instOfNatNat (nat_lit 98)))) flagBase →
                    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 192) (instOfNatNat (nat_lit 192))))
                              readBase →
                            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 194) (instOfNatNat (nat_lit 194))))
                                (@List.length.{0} (Fin n) xs) →
                              (∀ (j : Nat) (hj : @LT.lt.{0} Nat instLTNat j (@List.length.{0} (Fin n) xs)),
                                  @Eq.{1} Nat
                                    (s.natMem
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) readBase
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
                                    (@Fin.val n
                                      (@GetElem.getElem.{0, 0, 0} (List.{0} (Fin n)) Nat (Fin n)
                                        (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} (Fin n) as))
                                        (@List.instGetElemNatLtLength.{0} (Fin n)) xs j hj))) →
                                ∃ cost t,
                                  And
                                    (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                      DecrAlmostLinearSSSP.Decremental.DirtyCommit.loop s cost t)
                                    (And
                                      (@LE.le.{0} Nat instLENat cost
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))
                                            (@List.length.{0} (Fin n) xs))
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                      (And
                                        (@Eq.{1} Nat
                                          (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 192) (instOfNatNat (nat_lit 192))))
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) readBase
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                              (@List.length.{0} (Fin n) xs))))
                                        (And
                                          (@Eq.{1} Nat
                                            (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 194) (instOfNatNat (nat_lit 194))))
                                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                          (And (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Image n l t)
                                            (And
                                              (∀ (v : Fin n),
                                                @Membership.mem.{0, 0} (Fin n) (List.{0} (Fin n))
                                                    (@List.instMembership.{0} (Fin n)) xs v →
                                                  And
                                                    (@Eq.{1} Nat (t.natMem (@Fin.val n v))
                                                      (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.flag n l v))
                                                    (And
                                                      (@Eq.{1} Real (t.realMem (@Fin.val n v))
                                                        (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.realValue
                                                          n l v))
                                                      (@Eq.{1} Nat
                                                        (t.natMem
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat) flagBase
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                (instOfNatNat (nat_lit 2)))
                                                              (@Fin.val n v))))
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
                                              (∀ (address : Nat),
                                                (∀ (v : Fin n),
                                                    @Membership.mem.{0, 0} (Fin n) (List.{0} (Fin n))
                                                        (@List.instMembership.{0} (Fin n)) xs v →
                                                      And (@Ne.{1} Nat address (@Fin.val n v))
                                                        (@Ne.{1} Nat address
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat) flagBase
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                (instOfNatNat (nat_lit 2)))
                                                              (@Fin.val n v))))) →
                                                  And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                                    (@Eq.{1} Real (t.realMem address) (s.realMem address)))))))))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.DirtyCommit.beginCode s
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    (DecrAlmostLinearSSSP.Decremental.DirtyCommit.beginData s)) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.DirtyCommit.endCode s
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    (DecrAlmostLinearSSSP.Decremental.DirtyCommit.endData s)) ∧ (∀ (k : Nat),
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
                        DecrAlmostLinearSSSP.Decremental.DirtyCommit.loop k))))))) ∧ ((((((∀ {n : Nat} (l : DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout n) (flagBase listBase : Nat),
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
                                                (@Eq.{1} Real (t.realMem address) (s.realMem address)))))))) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.SelectedRead.code k)) ∧ ((∀ (k : Nat),
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
                            DecrAlmostLinearSSSP.Decremental.DirtyCommit.code k) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.DirtyCommit.code k))) ∧ (((DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame DecrAlmostLinearSSSP.Decremental.DirtyCommit.code) ∧ (DecrAlmostLinearSSSP.Decremental.TailFrame DecrAlmostLinearSSSP.Decremental.DirtyCommit.code)) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (B reserve N : Nat)
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
                        i.n s t)))))))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (j : Nat) (es : List.{0} (Fin i.k)),
      (∀ (e : Fin i.k),
          @Membership.mem.{0, 0} (Fin i.k) (List.{0} (Fin i.k)) (@List.instMembership.{0} (Fin i.k)) es e →
            @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast (i.weight e))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                (DecrAlmostLinearSSSP.Decremental.scale j))) →
        And
          (@LE.le.{0} Real Real.instLE
            (@List.sum.{0} Real Real.instAdd Real.instZero
              (@List.map.{0, 0} (Fin i.k) Real (fun e => @Nat.cast.{0} Real Real.instNatCast (i.weight e)) es))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (DecrAlmostLinearSSSP.Decremental.delta i j)
              (@List.sum.{0} Real Real.instAdd Real.instZero
                (@List.map.{0, 0} (Fin i.k) Real
                  (fun e => @Nat.cast.{0} Real Real.instNatCast (DecrAlmostLinearSSSP.Decremental.barrierWeight i j e))
                  es))))
          (@LE.le.{0} Real Real.instLE
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (DecrAlmostLinearSSSP.Decremental.delta i j)
              (@List.sum.{0} Real Real.instAdd Real.instZero
                (@List.map.{0, 0} (Fin i.k) Real
                  (fun e => @Nat.cast.{0} Real Real.instNatCast (DecrAlmostLinearSSSP.Decremental.barrierWeight i j e))
                  es)))
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@List.sum.{0} Real Real.instAdd Real.instZero
                (@List.map.{0, 0} (Fin i.k) Real (fun e => @Nat.cast.{0} Real Real.instNatCast (i.weight e)) es))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@Nat.cast.{0} Real Real.instNatCast (@List.length.{0} (Fin i.k) es))
                (DecrAlmostLinearSSSP.Decremental.delta i j))))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
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
              (@DecrAlmostLinearSSSP.Decremental.distance (DecrAlmostLinearSSSP.Decremental.barrierInput i j).n
                (DecrAlmostLinearSSSP.Decremental.barrierInput i j).k
                (DecrAlmostLinearSSSP.Decremental.barrierInput i j).graph active
                (fun e =>
                  @Nat.cast.{0} ENNReal
                    (@AddMonoidWithOne.toNatCast.{0} ENNReal
                      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                    ((DecrAlmostLinearSSSP.Decremental.barrierInput i j).weight e))
                u v))
            (ENNReal.ofReal
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@List.sum.{0} Real Real.instAdd Real.instZero
                  (@List.map.{0, 0} (Fin i.k) Real (fun e => @Nat.cast.{0} Real Real.instNatCast (i.weight e)) es))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@Nat.cast.{0} Real Real.instNatCast (@List.length.{0} (Fin i.k) es))
                  (DecrAlmostLinearSSSP.Decremental.delta i j))))))))) ∧ ((((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (j : Nat) (active : Finset.{0} (Fin i.k)) (u v : Fin i.n),
      @LE.le.{0} ENNReal ENNReal.instLE
          (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
            (@instHMul.{0} ENNReal
              (@Distrib.toMul.{0} ENNReal
                (@instDistribOfSemiring.{0} ENNReal (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
            (ENNReal.ofReal (DecrAlmostLinearSSSP.Decremental.delta i j))
            (@DecrAlmostLinearSSSP.Decremental.distance (DecrAlmostLinearSSSP.Decremental.barrierInput i j).n
              (DecrAlmostLinearSSSP.Decremental.barrierInput i j).k
              (DecrAlmostLinearSSSP.Decremental.barrierInput i j).graph active
              (fun e =>
                @Nat.cast.{0} ENNReal
                  (@AddMonoidWithOne.toNatCast.{0} ENNReal
                    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                  ((DecrAlmostLinearSSSP.Decremental.barrierInput i j).weight e))
              u v))
          (ENNReal.ofReal
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              (DecrAlmostLinearSSSP.Decremental.scale j))) →
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
            (@DecrAlmostLinearSSSP.Decremental.distance (DecrAlmostLinearSSSP.Decremental.barrierInput i j).n
              (DecrAlmostLinearSSSP.Decremental.barrierInput i j).k
              (DecrAlmostLinearSSSP.Decremental.barrierInput i j).graph active
              (fun e =>
                @Nat.cast.{0} ENNReal
                  (@AddMonoidWithOne.toNatCast.{0} ENNReal
                    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                  ((DecrAlmostLinearSSSP.Decremental.barrierInput i j).weight e))
              u v))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (j : Nat),
  @Eq.{1} Real
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (@Nat.cast.{0} Real Real.instNatCast i.n)
      (DecrAlmostLinearSSSP.Decremental.delta i j))
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) i.accuracy
        (DecrAlmostLinearSSSP.Decremental.scale j))
      (@OfNat.ofNat.{0} Real (nat_lit 128)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 128) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 127) (instOfNatNat (nat_lit 127)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 126) (instOfNatNat (nat_lit 126)))))))))) ∧ ((∀ {epsilon d L : Real},
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) epsilon →
    @LE.le.{0} Real Real.instLE epsilon (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) d →
        @LE.le.{0} Real Real.instLE L
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              d) →
          @LE.le.{0} Real Real.instLE
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) epsilon
                  (@OfNat.ofNat.{0} Real (nat_lit 16)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))))))))
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) d
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) epsilon L)
                  (@OfNat.ofNat.{0} Real (nat_lit 128)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 128) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 127) (instOfNatNat (nat_lit 127)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 126) (instOfNatNat (nat_lit 126))))))))))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) epsilon
                  (@OfNat.ofNat.{0} Real (nat_lit 8)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))))
              d)) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (j : Nat) (active : Finset.{0} (Fin i.k)) (u v : Fin i.n) (B : ENNReal),
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
          @LE.le.{0} ENNReal ENNReal.instLE B
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
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))))))))
                (@DecrAlmostLinearSSSP.Decremental.distance (DecrAlmostLinearSSSP.Decremental.roundedInput i j).n
                  (DecrAlmostLinearSSSP.Decremental.roundedInput i j).k
                  (DecrAlmostLinearSSSP.Decremental.roundedInput i j).graph
                  (DecrAlmostLinearSSSP.Decremental.scaleActive i j active)
                  (fun e =>
                    @Nat.cast.{0} ENNReal
                      (@AddMonoidWithOne.toNatCast.{0} ENNReal
                        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                      ((DecrAlmostLinearSSSP.Decremental.roundedInput i j).weight e))
                  u v)) →
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
                      (ENNReal.ofReal (DecrAlmostLinearSSSP.Decremental.delta i j)) B)
                    (ENNReal.ofReal
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) i.accuracy
                            (@OfNat.ofNat.{0} Real (nat_lit 16)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))))))))
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) d
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) i.accuracy
                              (DecrAlmostLinearSSSP.Decremental.scale j))
                            (@OfNat.ofNat.{0} Real (nat_lit 128)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 128) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 127) (instOfNatNat (nat_lit 127)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 126) (instOfNatNat (nat_lit 126)))))))))))))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (j : Nat) (active : Finset.{0} (Fin i.k)) (u v : Fin i.n) (B : ENNReal) (d : Real),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) d →
        @Eq.{1} ENNReal
            (@DecrAlmostLinearSSSP.Decremental.distance i.n i.k i.graph active
              (fun e =>
                @Nat.cast.{0} ENNReal
                  (@AddMonoidWithOne.toNatCast.{0} ENNReal
                    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                  (i.weight e))
              u v)
            (ENNReal.ofReal d) →
          @DecrAlmostLinearSSSP.Decremental.Reachable i.n i.k i.graph active u v →
            @LE.le.{0} Real Real.instLE (DecrAlmostLinearSSSP.Decremental.scale j)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                  d) →
              @LE.le.{0} ENNReal ENNReal.instLE
                  (@DecrAlmostLinearSSSP.Decremental.distance (DecrAlmostLinearSSSP.Decremental.roundedInput i j).n
                    (DecrAlmostLinearSSSP.Decremental.roundedInput i j).k
                    (DecrAlmostLinearSSSP.Decremental.roundedInput i j).graph
                    (DecrAlmostLinearSSSP.Decremental.scaleActive i j active)
                    (fun e =>
                      @Nat.cast.{0} ENNReal
                        (@AddMonoidWithOne.toNatCast.{0} ENNReal
                          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                        ((DecrAlmostLinearSSSP.Decremental.roundedInput i j).weight e))
                    u v)
                  B →
                @LE.le.{0} ENNReal ENNReal.instLE B
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
                      (@DecrAlmostLinearSSSP.Decremental.distance (DecrAlmostLinearSSSP.Decremental.roundedInput i j).n
                        (DecrAlmostLinearSSSP.Decremental.roundedInput i j).k
                        (DecrAlmostLinearSSSP.Decremental.roundedInput i j).graph
                        (DecrAlmostLinearSSSP.Decremental.scaleActive i j active)
                        (fun e =>
                          @Nat.cast.{0} ENNReal
                            (@AddMonoidWithOne.toNatCast.{0} ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                            ((DecrAlmostLinearSSSP.Decremental.roundedInput i j).weight e))
                        u v)) →
                  @LE.le.{0} ENNReal ENNReal.instLE
                      (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                        (@instHMul.{0} ENNReal
                          (@Distrib.toMul.{0} ENNReal
                            (@instDistribOfSemiring.{0} ENNReal
                              (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                        (ENNReal.ofReal (DecrAlmostLinearSSSP.Decremental.delta i j)) B)
                      (ENNReal.ofReal
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@OfNat.ofNat.{0} Real (nat_lit 2)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                          (DecrAlmostLinearSSSP.Decremental.scale j))) →
                    And
                      (@LE.le.{0} ENNReal ENNReal.instLE (ENNReal.ofReal d)
                        (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                          (@instHMul.{0} ENNReal
                            (@Distrib.toMul.{0} ENNReal
                              (@instDistribOfSemiring.{0} ENNReal
                                (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                          (ENNReal.ofReal (DecrAlmostLinearSSSP.Decremental.delta i j)) B))
                      (@LE.le.{0} ENNReal ENNReal.instLE
                        (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                          (@instHMul.{0} ENNReal
                            (@Distrib.toMul.{0} ENNReal
                              (@instDistribOfSemiring.{0} ENNReal
                                (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                          (ENNReal.ofReal (DecrAlmostLinearSSSP.Decremental.delta i j)) B)
                        (ENNReal.ofReal
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) i.accuracy
                                (@OfNat.ofNat.{0} Real (nat_lit 8)
                                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
                                    (@Nat.instAtLeastTwoHAddOfNat
                                      (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                                      (@Nat.instNeZeroSucc
                                        (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))))
                            d))))))) ∧ (((∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {a b : Finset.{0} (Fin k)},
  @LE.le.{0} (Finset.{0} (Fin k))
      (@Preorder.toLE.{0} (Finset.{0} (Fin k))
        (@PartialOrder.toPreorder.{0} (Finset.{0} (Fin k)) (@Finset.instPartialOrder.{0} (Fin k))))
      a b →
    ∀ {u v : Fin n} {es : List.{0} (Fin k)},
      @DecrAlmostLinearSSSP.Decremental.Walk n k g a u v es → @DecrAlmostLinearSSSP.Decremental.Walk n k g b u v es) ∧ (∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) {a b : Finset.{0} (Fin k)},
  @LE.le.{0} (Finset.{0} (Fin k))
      (@Preorder.toLE.{0} (Finset.{0} (Fin k))
        (@PartialOrder.toPreorder.{0} (Finset.{0} (Fin k)) (@Finset.instPartialOrder.{0} (Fin k))))
      a b →
    ∀ (w : Fin k → ENNReal) (u v : Fin n),
      @LE.le.{0} ENNReal ENNReal.instLE (@DecrAlmostLinearSSSP.Decremental.distance n k g b w u v)
        (@DecrAlmostLinearSSSP.Decremental.distance n k g a w u v))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (j : Nat) (current past : Finset.{0} (Fin i.k)),
      @LE.le.{0} (Finset.{0} (Fin i.k))
          (@Preorder.toLE.{0} (Finset.{0} (Fin i.k))
            (@PartialOrder.toPreorder.{0} (Finset.{0} (Fin i.k)) (@Finset.instPartialOrder.{0} (Fin i.k))))
          current past →
        ∀ {u v : Fin i.n} {es : List.{0} (Fin i.k)},
          @DecrAlmostLinearSSSP.Decremental.Walk i.n i.k i.graph current u v es →
            (∀ (e : Fin i.k),
                @Membership.mem.{0, 0} (Fin i.k) (List.{0} (Fin i.k)) (@List.instMembership.{0} (Fin i.k)) es e →
                  @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast (i.weight e))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@OfNat.ofNat.{0} Real (nat_lit 2)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                      (DecrAlmostLinearSSSP.Decremental.scale j))) →
              ∀ (B : ENNReal),
                @LE.le.{0} ENNReal ENNReal.instLE B
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
                      (@DecrAlmostLinearSSSP.Decremental.distance (DecrAlmostLinearSSSP.Decremental.roundedInput i j).n
                        (DecrAlmostLinearSSSP.Decremental.roundedInput i j).k
                        (DecrAlmostLinearSSSP.Decremental.roundedInput i j).graph
                        (DecrAlmostLinearSSSP.Decremental.scaleActive i j past)
                        (fun e =>
                          @Nat.cast.{0} ENNReal
                            (@AddMonoidWithOne.toNatCast.{0} ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                            ((DecrAlmostLinearSSSP.Decremental.roundedInput i j).weight e))
                        u v)) →
                  @LE.le.{0} ENNReal ENNReal.instLE
                    (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                      (@instHMul.{0} ENNReal
                        (@Distrib.toMul.{0} ENNReal
                          (@instDistribOfSemiring.{0} ENNReal
                            (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                      (ENNReal.ofReal (DecrAlmostLinearSSSP.Decremental.delta i j)) B)
                    (ENNReal.ofReal
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) i.accuracy
                            (@OfNat.ofNat.{0} Real (nat_lit 16)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))))))))
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@List.sum.{0} Real Real.instAdd Real.instZero
                            (@List.map.{0, 0} (Fin i.k) Real (fun e => @Nat.cast.{0} Real Real.instNatCast (i.weight e))
                              es))
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@Nat.cast.{0} Real Real.instNatCast (@List.length.{0} (Fin i.k) es))
                            (DecrAlmostLinearSSSP.Decremental.delta i j)))))) ∧ ((∀ (delta x y bound : ENNReal),
  @LE.le.{0} ENNReal ENNReal.instLE
      (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
        (@instHMul.{0} ENNReal
          (@Distrib.toMul.{0} ENNReal
            (@instDistribOfSemiring.{0} ENNReal (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
        delta x)
      bound →
    @LE.le.{0} ENNReal ENNReal.instLE
        (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
          (@instHMul.{0} ENNReal
            (@Distrib.toMul.{0} ENNReal
              (@instDistribOfSemiring.{0} ENNReal (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
          delta y)
        bound →
      @LE.le.{0} ENNReal ENNReal.instLE
        (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
          (@instHMul.{0} ENNReal
            (@Distrib.toMul.{0} ENNReal
              (@instDistribOfSemiring.{0} ENNReal (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
          delta (@Max.max.{0} ENNReal ENNReal.instMax x y))
        bound) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (j : Nat) {ι : Type} (S : Finset.{0} ι) (past : ι → Finset.{0} (Fin i.k)) (current : Finset.{0} (Fin i.k)),
      (∀ (t : ι),
          @Membership.mem.{0, 0} ι (Finset.{0} ι)
              (@SetLike.instMembership.{0, 0} (Finset.{0} ι) ι (@Finset.instSetLike.{0} ι)) S t →
            @LE.le.{0} (Finset.{0} (Fin i.k))
              (@Preorder.toLE.{0} (Finset.{0} (Fin i.k))
                (@PartialOrder.toPreorder.{0} (Finset.{0} (Fin i.k)) (@Finset.instPartialOrder.{0} (Fin i.k))))
              current (past t)) →
        ∀ {u v : Fin i.n} {es : List.{0} (Fin i.k)},
          @DecrAlmostLinearSSSP.Decremental.Walk i.n i.k i.graph current u v es →
            (∀ (e : Fin i.k),
                @Membership.mem.{0, 0} (Fin i.k) (List.{0} (Fin i.k)) (@List.instMembership.{0} (Fin i.k)) es e →
                  @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast (i.weight e))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@OfNat.ofNat.{0} Real (nat_lit 2)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                      (DecrAlmostLinearSSSP.Decremental.scale j))) →
              ∀ (B : ι → ENNReal),
                (∀ (t : ι),
                    @Membership.mem.{0, 0} ι (Finset.{0} ι)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} ι) ι (@Finset.instSetLike.{0} ι)) S t →
                      @LE.le.{0} ENNReal ENNReal.instLE (B t)
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
                            (DecrAlmostLinearSSSP.Decremental.roundedInput i j).n
                            (DecrAlmostLinearSSSP.Decremental.roundedInput i j).k
                            (DecrAlmostLinearSSSP.Decremental.roundedInput i j).graph
                            (DecrAlmostLinearSSSP.Decremental.scaleActive i j (past t))
                            (fun e =>
                              @Nat.cast.{0} ENNReal
                                (@AddMonoidWithOne.toNatCast.{0} ENNReal
                                  (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal
                                    ENNReal.instAddCommMonoidWithOne))
                                ((DecrAlmostLinearSSSP.Decremental.roundedInput i j).weight e))
                            u v))) →
                  @LE.le.{0} ENNReal ENNReal.instLE
                    (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                      (@instHMul.{0} ENNReal
                        (@Distrib.toMul.{0} ENNReal
                          (@instDistribOfSemiring.{0} ENNReal
                            (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                      (ENNReal.ofReal (DecrAlmostLinearSSSP.Decremental.delta i j))
                      (@Finset.sup.{0, 0} ENNReal ι ENNReal.instSemilatticeSup ENNReal.instOrderBot S B))
                    (ENNReal.ofReal
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) i.accuracy
                            (@OfNat.ofNat.{0} Real (nat_lit 16)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))))))))
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@List.sum.{0} Real Real.instAdd Real.instZero
                            (@List.map.{0, 0} (Fin i.k) Real (fun e => @Nat.cast.{0} Real Real.instNatCast (i.weight e))
                              es))
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@Nat.cast.{0} Real Real.instNatCast (@List.length.{0} (Fin i.k) es))
                            (DecrAlmostLinearSSSP.Decremental.delta i j))))))))))) ∧ (((((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (j : Nat) (current past : Finset.{0} (Fin i.k)),
      @LE.le.{0} (Finset.{0} (Fin i.k))
          (@Preorder.toLE.{0} (Finset.{0} (Fin i.k))
            (@PartialOrder.toPreorder.{0} (Finset.{0} (Fin i.k)) (@Finset.instPartialOrder.{0} (Fin i.k))))
          current past →
        ∀ {u v : Fin i.n} {es : List.{0} (Fin i.k)},
          @DecrAlmostLinearSSSP.Decremental.Walk i.n i.k i.graph current u v es →
            (∀ (e : Fin i.k),
                @Membership.mem.{0, 0} (Fin i.k) (List.{0} (Fin i.k)) (@List.instMembership.{0} (Fin i.k)) es e →
                  @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast (i.weight e))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@OfNat.ofNat.{0} Real (nat_lit 2)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                      (DecrAlmostLinearSSSP.Decremental.scale j))) →
              ∀ (B : ENNReal),
                @LE.le.{0} ENNReal ENNReal.instLE B
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
                      (@DecrAlmostLinearSSSP.Decremental.distance (DecrAlmostLinearSSSP.Decremental.barrierInput i j).n
                        (DecrAlmostLinearSSSP.Decremental.barrierInput i j).k
                        (DecrAlmostLinearSSSP.Decremental.barrierInput i j).graph past
                        (fun e =>
                          @Nat.cast.{0} ENNReal
                            (@AddMonoidWithOne.toNatCast.{0} ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                            ((DecrAlmostLinearSSSP.Decremental.barrierInput i j).weight e))
                        u v)) →
                  @LE.le.{0} ENNReal ENNReal.instLE
                    (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                      (@instHMul.{0} ENNReal
                        (@Distrib.toMul.{0} ENNReal
                          (@instDistribOfSemiring.{0} ENNReal
                            (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                      (ENNReal.ofReal (DecrAlmostLinearSSSP.Decremental.delta i j)) B)
                    (ENNReal.ofReal
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) i.accuracy
                            (@OfNat.ofNat.{0} Real (nat_lit 16)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))))))))
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@List.sum.{0} Real Real.instAdd Real.instZero
                            (@List.map.{0, 0} (Fin i.k) Real (fun e => @Nat.cast.{0} Real Real.instNatCast (i.weight e))
                              es))
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@Nat.cast.{0} Real Real.instNatCast (@List.length.{0} (Fin i.k) es))
                            (DecrAlmostLinearSSSP.Decremental.delta i j)))))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (j : Nat) {ι : Type} (S : Finset.{0} ι) (past : ι → Finset.{0} (Fin i.k)) (current : Finset.{0} (Fin i.k)),
      (∀ (t : ι),
          @Membership.mem.{0, 0} ι (Finset.{0} ι)
              (@SetLike.instMembership.{0, 0} (Finset.{0} ι) ι (@Finset.instSetLike.{0} ι)) S t →
            @LE.le.{0} (Finset.{0} (Fin i.k))
              (@Preorder.toLE.{0} (Finset.{0} (Fin i.k))
                (@PartialOrder.toPreorder.{0} (Finset.{0} (Fin i.k)) (@Finset.instPartialOrder.{0} (Fin i.k))))
              current (past t)) →
        ∀ {u v : Fin i.n} {es : List.{0} (Fin i.k)},
          @DecrAlmostLinearSSSP.Decremental.Walk i.n i.k i.graph current u v es →
            (∀ (e : Fin i.k),
                @Membership.mem.{0, 0} (Fin i.k) (List.{0} (Fin i.k)) (@List.instMembership.{0} (Fin i.k)) es e →
                  @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast (i.weight e))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@OfNat.ofNat.{0} Real (nat_lit 2)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                      (DecrAlmostLinearSSSP.Decremental.scale j))) →
              ∀ (B : ι → ENNReal),
                (∀ (t : ι),
                    @Membership.mem.{0, 0} ι (Finset.{0} ι)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} ι) ι (@Finset.instSetLike.{0} ι)) S t →
                      @LE.le.{0} ENNReal ENNReal.instLE (B t)
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
                            (DecrAlmostLinearSSSP.Decremental.barrierInput i j).n
                            (DecrAlmostLinearSSSP.Decremental.barrierInput i j).k
                            (DecrAlmostLinearSSSP.Decremental.barrierInput i j).graph (past t)
                            (fun e =>
                              @Nat.cast.{0} ENNReal
                                (@AddMonoidWithOne.toNatCast.{0} ENNReal
                                  (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal
                                    ENNReal.instAddCommMonoidWithOne))
                                ((DecrAlmostLinearSSSP.Decremental.barrierInput i j).weight e))
                            u v))) →
                  @LE.le.{0} ENNReal ENNReal.instLE
                    (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                      (@instHMul.{0} ENNReal
                        (@Distrib.toMul.{0} ENNReal
                          (@instDistribOfSemiring.{0} ENNReal
                            (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                      (ENNReal.ofReal (DecrAlmostLinearSSSP.Decremental.delta i j))
                      (@Finset.sup.{0, 0} ENNReal ι ENNReal.instSemilatticeSup ENNReal.instOrderBot S B))
                    (ENNReal.ofReal
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) i.accuracy
                            (@OfNat.ofNat.{0} Real (nat_lit 16)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))))))))
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@List.sum.{0} Real Real.instAdd Real.instZero
                            (@List.map.{0, 0} (Fin i.k) Real (fun e => @Nat.cast.{0} Real Real.instNatCast (i.weight e))
                              es))
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@Nat.cast.{0} Real Real.instNatCast (@List.length.{0} (Fin i.k) es))
                            (DecrAlmostLinearSSSP.Decremental.delta i j))))))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input)
  (b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal) (v : Fin i.n)
  (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
  Iff
    (@Eq.{1} Bool
      (DecrAlmostLinearSSSP.Decremental.eligible i b v (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j))
      Bool.true)
    (@LE.le.{0} ENNReal ENNReal.instLE
      (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
        (@instHMul.{0} ENNReal
          (@Distrib.toMul.{0} ENNReal
            (@instDistribOfSemiring.{0} ENNReal (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
        (ENNReal.ofReal
          (DecrAlmostLinearSSSP.Decremental.delta i (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)))
        (b j v))
      (ENNReal.ofReal
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
          (DecrAlmostLinearSSSP.Decremental.scale (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)))))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal) (v : Fin i.n) (p : Nat) (d : Real),
      DecrAlmostLinearSSSP.Decremental.PointerValid i b v p →
        @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) d →
          @LE.le.{0} Real Real.instLE d
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@Nat.cast.{0} Real Real.instNatCast i.n) (@Nat.cast.{0} Real Real.instNatCast i.W)) →
            (∀ (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
                @LE.le.{0} ENNReal ENNReal.instLE (ENNReal.ofReal d)
                  (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                    (@instHMul.{0} ENNReal
                      (@Distrib.toMul.{0} ENNReal
                        (@instDistribOfSemiring.{0} ENNReal
                          (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                    (ENNReal.ofReal
                      (DecrAlmostLinearSSSP.Decremental.delta i
                        (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)))
                    (b j v))) →
              (∀ (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
                  @LE.le.{0} ENNReal ENNReal.instLE (ENNReal.ofReal d)
                      (ENNReal.ofReal
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@OfNat.ofNat.{0} Real (nat_lit 2)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                          (DecrAlmostLinearSSSP.Decremental.scale
                            (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)))) →
                    @LE.le.{0} ENNReal ENNReal.instLE
                      (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                        (@instHMul.{0} ENNReal
                          (@Distrib.toMul.{0} ENNReal
                            (@instDistribOfSemiring.{0} ENNReal
                              (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                        (ENNReal.ofReal
                          (DecrAlmostLinearSSSP.Decremental.delta i
                            (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)))
                        (b j v))
                      (ENNReal.ofReal
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                            (@HDiv.hDiv.{0, 0, 0} Real Real Real
                              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) i.accuracy
                              (@OfNat.ofNat.{0} Real (nat_lit 16)
                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                                    (@Nat.instNeZeroSucc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))))))))
                          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) d
                            (@HDiv.hDiv.{0, 0, 0} Real Real Real
                              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) i.accuracy
                                (DecrAlmostLinearSSSP.Decremental.scale
                                  (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)))
                              (@OfNat.ofNat.{0} Real (nat_lit 128)
                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 128) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 127) (instOfNatNat (nat_lit 127)))
                                    (@Nat.instNeZeroSucc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 126) (instOfNatNat (nat_lit 126)))))))))))) →
                ∃ (h : @LT.lt.{0} Nat instLTNat p (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
                  And
                    (@LE.le.{0} ENNReal ENNReal.instLE (ENNReal.ofReal d)
                      (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                        (@instHMul.{0} ENNReal
                          (@Distrib.toMul.{0} ENNReal
                            (@instDistribOfSemiring.{0} ENNReal
                              (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                        (ENNReal.ofReal (DecrAlmostLinearSSSP.Decremental.delta i p))
                        (b (@Fin.mk (DecrAlmostLinearSSSP.Decremental.scaleCount i) p h) v)))
                    (@LE.le.{0} ENNReal ENNReal.instLE
                      (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                        (@instHMul.{0} ENNReal
                          (@Distrib.toMul.{0} ENNReal
                            (@instDistribOfSemiring.{0} ENNReal
                              (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                        (ENNReal.ofReal (DecrAlmostLinearSSSP.Decremental.delta i p))
                        (b (@Fin.mk (DecrAlmostLinearSSSP.Decremental.scaleCount i) p h) v))
                      (ENNReal.ofReal
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                            (@HDiv.hDiv.{0, 0, 0} Real Real Real
                              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) i.accuracy
                              (@OfNat.ofNat.{0} Real (nat_lit 8)
                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                                    (@Nat.instNeZeroSucc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))))
                          d)))))) ∧ (((∀ (i : DecrAlmostLinearSSSP.Decremental.Input)
  (b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal) (v : Fin i.n) (p : Nat),
  DecrAlmostLinearSSSP.Decremental.PointerValid i b v p →
    (∀ (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
        @LE.le.{0} ENNReal ENNReal.instLE (@Top.top.{0} ENNReal ENNReal.instTop)
          (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
            (@instHMul.{0} ENNReal
              (@Distrib.toMul.{0} ENNReal
                (@instDistribOfSemiring.{0} ENNReal (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
            (ENNReal.ofReal
              (DecrAlmostLinearSSSP.Decremental.delta i (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)))
            (b j v))) →
      @Eq.{1} Nat p (DecrAlmostLinearSSSP.Decremental.scaleCount i)) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal) (v : Fin i.n) (p : Nat) (d : Real),
      DecrAlmostLinearSSSP.Decremental.PointerValid i b v p →
        @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) d →
          @LE.le.{0} Real Real.instLE d
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@Nat.cast.{0} Real Real.instNatCast i.n) (@Nat.cast.{0} Real Real.instNatCast i.W)) →
            (∀ (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
                @Eq.{1} Bool
                    (DecrAlmostLinearSSSP.Decremental.eligible i b v
                      (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j))
                    Bool.true →
                  @LE.le.{0} ENNReal ENNReal.instLE (ENNReal.ofReal d)
                    (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                      (@instHMul.{0} ENNReal
                        (@Distrib.toMul.{0} ENNReal
                          (@instDistribOfSemiring.{0} ENNReal
                            (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                      (ENNReal.ofReal
                        (DecrAlmostLinearSSSP.Decremental.delta i
                          (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)))
                      (b j v))) →
              (∀ (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
                  @LE.le.{0} ENNReal ENNReal.instLE (ENNReal.ofReal d)
                      (ENNReal.ofReal
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@OfNat.ofNat.{0} Real (nat_lit 2)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                          (DecrAlmostLinearSSSP.Decremental.scale
                            (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)))) →
                    @LE.le.{0} ENNReal ENNReal.instLE
                      (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                        (@instHMul.{0} ENNReal
                          (@Distrib.toMul.{0} ENNReal
                            (@instDistribOfSemiring.{0} ENNReal
                              (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                        (ENNReal.ofReal
                          (DecrAlmostLinearSSSP.Decremental.delta i
                            (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)))
                        (b j v))
                      (ENNReal.ofReal
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                            (@HDiv.hDiv.{0, 0, 0} Real Real Real
                              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) i.accuracy
                              (@OfNat.ofNat.{0} Real (nat_lit 16)
                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                                    (@Nat.instNeZeroSucc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))))))))
                          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) d
                            (@HDiv.hDiv.{0, 0, 0} Real Real Real
                              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) i.accuracy
                                (DecrAlmostLinearSSSP.Decremental.scale
                                  (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)))
                              (@OfNat.ofNat.{0} Real (nat_lit 128)
                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 128) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 127) (instOfNatNat (nat_lit 127)))
                                    (@Nat.instNeZeroSucc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 126) (instOfNatNat (nat_lit 126)))))))))))) →
                ∃ (h : @LT.lt.{0} Nat instLTNat p (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
                  And
                    (@LE.le.{0} ENNReal ENNReal.instLE (ENNReal.ofReal d)
                      (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                        (@instHMul.{0} ENNReal
                          (@Distrib.toMul.{0} ENNReal
                            (@instDistribOfSemiring.{0} ENNReal
                              (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                        (ENNReal.ofReal (DecrAlmostLinearSSSP.Decremental.delta i p))
                        (b (@Fin.mk (DecrAlmostLinearSSSP.Decremental.scaleCount i) p h) v)))
                    (@LE.le.{0} ENNReal ENNReal.instLE
                      (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                        (@instHMul.{0} ENNReal
                          (@Distrib.toMul.{0} ENNReal
                            (@instDistribOfSemiring.{0} ENNReal
                              (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                        (ENNReal.ofReal (DecrAlmostLinearSSSP.Decremental.delta i p))
                        (b (@Fin.mk (DecrAlmostLinearSSSP.Decremental.scaleCount i) p h) v))
                      (ENNReal.ofReal
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                            (@HDiv.hDiv.{0, 0, 0} Real Real Real
                              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) i.accuracy
                              (@OfNat.ofNat.{0} Real (nat_lit 8)
                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                                    (@Nat.instNeZeroSucc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))))
                          d))))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input)
  (b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal) (v : Fin i.n) (p : Nat),
  DecrAlmostLinearSSSP.Decremental.PointerValid i b v p →
    (∀ (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
        @Eq.{1} Bool
            (DecrAlmostLinearSSSP.Decremental.eligible i b v
              (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j))
            Bool.true →
          @LE.le.{0} ENNReal ENNReal.instLE (@Top.top.{0} ENNReal ENNReal.instTop)
            (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
              (@instHMul.{0} ENNReal
                (@Distrib.toMul.{0} ENNReal
                  (@instDistribOfSemiring.{0} ENNReal (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
              (ENNReal.ofReal
                (DecrAlmostLinearSSSP.Decremental.delta i (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)))
              (b j v))) →
      @Eq.{1} Nat p (DecrAlmostLinearSSSP.Decremental.scaleCount i)) ∧ ((∀ (c : DecrAlmostLinearSSSP.Decremental.Machine),
  @Eq.{1} Nat c.pc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Bool c.halted Bool.false →
      @Eq.{1} Bool c.fault Bool.false →
        DecrAlmostLinearSSSP.Decremental.Ends DecrAlmostLinearSSSP.Decremental.singletonProgram c
          (DecrAlmostLinearSSSP.Decremental.haltState c)) ∧ (∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (active : Finset.{0} (Fin k)) (w : Fin k → ENNReal)
  (s : Fin n),
  @Eq.{1} ENNReal (@DecrAlmostLinearSSSP.Decremental.distance n k g active w s s)
    (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero))))))) ∧ ((((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  @Eq.{1} Nat i.n (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
    ∀ (v : Fin i.n), @Eq.{1} (Fin i.n) v i.source) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (v : Fin i.n),
  @Eq.{1} Nat
    ((DecrAlmostLinearSSSP.Decremental.initialMachine DecrAlmostLinearSSSP.Decremental.singletonProgram i).natMem
      (@Fin.val i.n v))
    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (ds : List.{0} (Fin i.k)),
  ∃ cs c,
    And (DecrAlmostLinearSSSP.Decremental.OnlineRun DecrAlmostLinearSSSP.Decremental.singletonProgram i ds cs)
      (And
        (@Eq.{1} Nat (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Machine cs)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (And
          (@Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Machine)
            (@List.getLast?.{0} DecrAlmostLinearSSSP.Decremental.Machine cs)
            (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Machine c))
          (And
            (@Eq.{1} Nat c.work
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (∀ (d : DecrAlmostLinearSSSP.Decremental.Machine),
              @Membership.mem.{0, 0} DecrAlmostLinearSSSP.Decremental.Machine
                  (List.{0} DecrAlmostLinearSSSP.Decremental.Machine)
                  (@List.instMembership.{0} DecrAlmostLinearSSSP.Decremental.Machine) cs d →
                And
                  (∀ (v : Fin i.n),
                    @Eq.{1} Nat (d.natMem (@Fin.val i.n v))
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (@Eq.{1} (Nat → Real) d.realMem fun x =>
                    @OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    @Eq.{1} Nat i.n (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      DecrAlmostLinearSSSP.Decremental.Maintains DecrAlmostLinearSSSP.Decremental.singletonProgram
        (@OfNat.ofNat.{0} Real (nat_lit 8)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))
        (fun x => @OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) Bool.false i) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (active : Finset.{0} (Fin i.k)) (b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal)
      (p : Fin i.n → Nat),
      (∀ (v : Fin i.n), DecrAlmostLinearSSSP.Decremental.PointerValid i b v (p v)) →
        (∀ (v : Fin i.n) (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
            @Eq.{1} Bool
                (DecrAlmostLinearSSSP.Decremental.eligible i b v
                  (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j))
                Bool.true →
              @LE.le.{0} ENNReal ENNReal.instLE
                (@DecrAlmostLinearSSSP.Decremental.distance i.n i.k i.graph active
                  (fun e =>
                    @Nat.cast.{0} ENNReal
                      (@AddMonoidWithOne.toNatCast.{0} ENNReal
                        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                      (i.weight e))
                  i.source v)
                (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                  (@instHMul.{0} ENNReal
                    (@Distrib.toMul.{0} ENNReal
                      (@instDistribOfSemiring.{0} ENNReal
                        (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                  (ENNReal.ofReal
                    (DecrAlmostLinearSSSP.Decremental.delta i
                      (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)))
                  (b j v))) →
          (∀ (v : Fin i.n) (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (d : Real),
              @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) d →
                @Eq.{1} ENNReal
                    (@DecrAlmostLinearSSSP.Decremental.distance i.n i.k i.graph active
                      (fun e =>
                        @Nat.cast.{0} ENNReal
                          (@AddMonoidWithOne.toNatCast.{0} ENNReal
                            (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                          (i.weight e))
                      i.source v)
                    (ENNReal.ofReal d) →
                  @LE.le.{0} ENNReal ENNReal.instLE (ENNReal.ofReal d)
                      (ENNReal.ofReal
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@OfNat.ofNat.{0} Real (nat_lit 2)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                          (DecrAlmostLinearSSSP.Decremental.scale
                            (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)))) →
                    @LE.le.{0} ENNReal ENNReal.instLE
                      (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                        (@instHMul.{0} ENNReal
                          (@Distrib.toMul.{0} ENNReal
                            (@instDistribOfSemiring.{0} ENNReal
                              (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                        (ENNReal.ofReal
                          (DecrAlmostLinearSSSP.Decremental.delta i
                            (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)))
                        (b j v))
                      (ENNReal.ofReal
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                            (@HDiv.hDiv.{0, 0, 0} Real Real Real
                              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) i.accuracy
                              (@OfNat.ofNat.{0} Real (nat_lit 16)
                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                                    (@Nat.instNeZeroSucc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))))))))
                          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) d
                            (@HDiv.hDiv.{0, 0, 0} Real Real Real
                              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) i.accuracy
                                (DecrAlmostLinearSSSP.Decremental.scale
                                  (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)))
                              (@OfNat.ofNat.{0} Real (nat_lit 128)
                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 128) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 127) (instOfNatNat (nat_lit 127)))
                                    (@Nat.instNeZeroSucc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 126) (instOfNatNat (nat_lit 126)))))))))))) →
            ∀ (v : Fin i.n),
              And
                (@LE.le.{0} ENNReal ENNReal.instLE
                  (@DecrAlmostLinearSSSP.Decremental.distance i.n i.k i.graph active
                    (fun e =>
                      @Nat.cast.{0} ENNReal
                        (@AddMonoidWithOne.toNatCast.{0} ENNReal
                          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                        (i.weight e))
                    i.source v)
                  (DecrAlmostLinearSSSP.Decremental.selected i b p v))
                (And
                  (@LE.le.{0} ENNReal ENNReal.instLE (DecrAlmostLinearSSSP.Decremental.selected i b p v)
                    (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                      (@instHMul.{0} ENNReal
                        (@Distrib.toMul.{0} ENNReal
                          (@instDistribOfSemiring.{0} ENNReal
                            (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                      (ENNReal.ofReal
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) i.accuracy))
                      (@DecrAlmostLinearSSSP.Decremental.distance i.n i.k i.graph active
                        (fun e =>
                          @Nat.cast.{0} ENNReal
                            (@AddMonoidWithOne.toNatCast.{0} ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                            (i.weight e))
                        i.source v)))
                  (Iff
                    (@Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.selected i b p v)
                      (@Top.top.{0} ENNReal ENNReal.instTop))
                    (Not (@DecrAlmostLinearSSSP.Decremental.Reachable i.n i.k i.graph active i.source v)))))))) ∧ (((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (j : Nat) (active : Finset.{0} (Fin i.k)) (u v : Fin i.n) (B : ENNReal),
      @LE.le.{0} ENNReal ENNReal.instLE
          (@DecrAlmostLinearSSSP.Decremental.distance (DecrAlmostLinearSSSP.Decremental.barrierInput i j).n
            (DecrAlmostLinearSSSP.Decremental.barrierInput i j).k
            (DecrAlmostLinearSSSP.Decremental.barrierInput i j).graph active
            (fun e =>
              @Nat.cast.{0} ENNReal
                (@AddMonoidWithOne.toNatCast.{0} ENNReal
                  (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                ((DecrAlmostLinearSSSP.Decremental.barrierInput i j).weight e))
            u v)
          B →
        @LE.le.{0} ENNReal ENNReal.instLE
            (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
              (@instHMul.{0} ENNReal
                (@Distrib.toMul.{0} ENNReal
                  (@instDistribOfSemiring.{0} ENNReal (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
              (ENNReal.ofReal (DecrAlmostLinearSSSP.Decremental.delta i j)) B)
            (ENNReal.ofReal
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                (DecrAlmostLinearSSSP.Decremental.scale j))) →
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
              (ENNReal.ofReal (DecrAlmostLinearSSSP.Decremental.delta i j)) B)) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (j : Nat) {ι : Type} (S : Finset.{0} ι) (past : ι → Finset.{0} (Fin i.k)) (current : Finset.{0} (Fin i.k)),
      (∀ (t : ι),
          @Membership.mem.{0, 0} ι (Finset.{0} ι)
              (@SetLike.instMembership.{0, 0} (Finset.{0} ι) ι (@Finset.instSetLike.{0} ι)) S t →
            @LE.le.{0} (Finset.{0} (Fin i.k))
              (@Preorder.toLE.{0} (Finset.{0} (Fin i.k))
                (@PartialOrder.toPreorder.{0} (Finset.{0} (Fin i.k)) (@Finset.instPartialOrder.{0} (Fin i.k))))
              current (past t)) →
        ∀ (u v : Fin i.n) (d : Real),
          @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) d →
            @Eq.{1} ENNReal
                (@DecrAlmostLinearSSSP.Decremental.distance i.n i.k i.graph current
                  (fun e =>
                    @Nat.cast.{0} ENNReal
                      (@AddMonoidWithOne.toNatCast.{0} ENNReal
                        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                      (i.weight e))
                  u v)
                (ENNReal.ofReal d) →
              @LE.le.{0} ENNReal ENNReal.instLE (ENNReal.ofReal d)
                  (ENNReal.ofReal
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@OfNat.ofNat.{0} Real (nat_lit 2)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                      (DecrAlmostLinearSSSP.Decremental.scale j))) →
                ∀ (B : ι → ENNReal),
                  (∀ (t : ι),
                      @Membership.mem.{0, 0} ι (Finset.{0} ι)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} ι) ι (@Finset.instSetLike.{0} ι)) S t →
                        @LE.le.{0} ENNReal ENNReal.instLE (B t)
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
                              (DecrAlmostLinearSSSP.Decremental.barrierInput i j).n
                              (DecrAlmostLinearSSSP.Decremental.barrierInput i j).k
                              (DecrAlmostLinearSSSP.Decremental.barrierInput i j).graph (past t)
                              (fun e =>
                                @Nat.cast.{0} ENNReal
                                  (@AddMonoidWithOne.toNatCast.{0} ENNReal
                                    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal
                                      ENNReal.instAddCommMonoidWithOne))
                                  ((DecrAlmostLinearSSSP.Decremental.barrierInput i j).weight e))
                              u v))) →
                    @LE.le.{0} ENNReal ENNReal.instLE
                      (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                        (@instHMul.{0} ENNReal
                          (@Distrib.toMul.{0} ENNReal
                            (@instDistribOfSemiring.{0} ENNReal
                              (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                        (ENNReal.ofReal (DecrAlmostLinearSSSP.Decremental.delta i j))
                        (@Finset.sup.{0, 0} ENNReal ι ENNReal.instSemilatticeSup ENNReal.instOrderBot S B))
                      (ENNReal.ofReal
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                            (@HDiv.hDiv.{0, 0, 0} Real Real Real
                              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) i.accuracy
                              (@OfNat.ofNat.{0} Real (nat_lit 16)
                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                                    (@Nat.instNeZeroSucc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))))))))
                          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) d
                            (@HDiv.hDiv.{0, 0, 0} Real Real Real
                              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) i.accuracy
                                (DecrAlmostLinearSSSP.Decremental.scale j))
                              (@OfNat.ofNat.{0} Real (nat_lit 128)
                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 128) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 127) (instOfNatNat (nat_lit 127)))
                                    (@Nat.instNeZeroSucc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 126) (instOfNatNat (nat_lit 126))))))))))))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
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
                            (Not (@DecrAlmostLinearSSSP.Decremental.Reachable i.n i.k i.graph current i.source v))))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
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
                    (@DecrAlmostLinearSSSP.Decremental.live i.k (@List.nil.{0} (Fin i.k))) i.source v))))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (p : DecrAlmostLinearSSSP.Decremental.Program) (B reserve : Nat)
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
      (fun q v => DecrAlmostLinearSSSP.Decremental.stored (f q) (@Fin.val i.n v)) s)))))))) := by
  exact ⟨⟨⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Native.pointerStart_no_memory,DecrAlmostLinearSSSP.Decremental.Native.globalFrame_pointerStart⟩,⟨DecrAlmostLinearSSSP.Decremental.Native.PointerBases.start,DecrAlmostLinearSSSP.Decremental.Native.PointerPrefix.dirty_view⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Native.buildPointers_eval,DecrAlmostLinearSSSP.Decremental.Native.tailFrame_pointerStart⟩,⟨DecrAlmostLinearSSSP.Decremental.Native.tailFrame_buildPointers,⟨DecrAlmostLinearSSSP.Decremental.PointerRead.eval_code,DecrAlmostLinearSSSP.Decremental.PointerRead.incoming_value⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.PointerRead.no_memory,DecrAlmostLinearSSSP.Decremental.SelectedRead.prefix_eval⟩,⟨DecrAlmostLinearSSSP.Decremental.SelectedRead.prefix_fields,DecrAlmostLinearSSSP.Decremental.SelectedRead.no_memory⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.SelectedRead.choose_eval,DecrAlmostLinearSSSP.Decremental.SelectedRead.eval_code⟩,⟨DecrAlmostLinearSSSP.Decremental.SelectedRead.choose_fields,⟨DecrAlmostLinearSSSP.Decremental.SelectedRead.fields,DecrAlmostLinearSSSP.Decremental.SelectedRead.normalized⟩⟩⟩⟩⟩,⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.SelectedRead.nat_frame,DecrAlmostLinearSSSP.Decremental.AnswerTable.Image.frame⟩,⟨DecrAlmostLinearSSSP.Decremental.AnswerTable.read_fields,DecrAlmostLinearSSSP.Decremental.AnswerTable.Image.same_memory⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.AnswerTable.normalized,DecrAlmostLinearSSSP.Decremental.Native.scanRecord_nonzero⟩,⟨DecrAlmostLinearSSSP.Decremental.Native.answerLayout_image,⟨DecrAlmostLinearSSSP.Decremental.Native.answerLayout_normal,DecrAlmostLinearSSSP.Decremental.Native.answerLayout_value⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Native.answerLayout_protected,DecrAlmostLinearSSSP.Decremental.DirtyCommit.suffix_eval⟩,⟨DecrAlmostLinearSSSP.Decremental.DirtyCommit.read_reg_frame,⟨DecrAlmostLinearSSSP.Decremental.DirtyCommit.body_eval,DecrAlmostLinearSSSP.Decremental.DirtyCommit.nat_frame⟩⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.DirtyCommit.body_fixed,DecrAlmostLinearSSSP.Decremental.DirtyCommit.eval_loop⟩,⟨DecrAlmostLinearSSSP.Decremental.DirtyCommit.begin_eval,⟨DecrAlmostLinearSSSP.Decremental.DirtyCommit.end_eval,DecrAlmostLinearSSSP.Decremental.DirtyCommit.loop_frame⟩⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.DirtyCommit.eval_code,DecrAlmostLinearSSSP.Decremental.SelectedRead.real_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.DirtyCommit.code_nat_frame,DecrAlmostLinearSSSP.Decremental.DirtyCommit.code_real_frame⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Native.globalFrame_commit,DecrAlmostLinearSSSP.Decremental.Native.tailFrame_commit⟩,⟨DecrAlmostLinearSSSP.Decremental.Native.commit_initial_pointers,⟨DecrAlmostLinearSSSP.Decremental.barrier_walk_cost,DecrAlmostLinearSSSP.Decremental.barrier_distance_upper_of_walk⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.barrier_distance_lower_guarded,DecrAlmostLinearSSSP.Decremental.delta_vertex_product⟩,⟨DecrAlmostLinearSSSP.Decremental.rounding_factor_bound,⟨DecrAlmostLinearSSSP.Decremental.scaled_estimate_upper,DecrAlmostLinearSSSP.Decremental.scaled_eligible_accuracy⟩⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Walk.active_mono,DecrAlmostLinearSSSP.Decremental.distance_active_antitone⟩,⟨DecrAlmostLinearSSSP.Decremental.historical_readout_of_walk,⟨DecrAlmostLinearSSSP.Decremental.scaled_max_bound,DecrAlmostLinearSSSP.Decremental.historical_readout_finite_family⟩⟩⟩⟩⟩,⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.barrier_historical_readout_of_walk,DecrAlmostLinearSSSP.Decremental.barrier_historical_readout_finite_family⟩,⟨DecrAlmostLinearSSSP.Decremental.eligible_iff,DecrAlmostLinearSSSP.Decremental.pointer_finite_readout⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.pointer_infinite_readout,DecrAlmostLinearSSSP.Decremental.pointer_finite_readout_guarded⟩,⟨DecrAlmostLinearSSSP.Decremental.pointer_infinite_readout_guarded,⟨DecrAlmostLinearSSSP.Decremental.singleton_halt,DecrAlmostLinearSSSP.Decremental.distance_self⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.singleton_vertex,DecrAlmostLinearSSSP.Decremental.singleton_input_memory⟩,⟨DecrAlmostLinearSSSP.Decremental.singleton_online,⟨DecrAlmostLinearSSSP.Decremental.singleton_maintains,DecrAlmostLinearSSSP.Decremental.selected_accuracy_guarded⟩⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.barrier_readout_lower_guarded,DecrAlmostLinearSSSP.Decremental.barrier_historical_shortest_upper⟩,⟨DecrAlmostLinearSSSP.Decremental.barrier_cache_selected_accuracy,⟨DecrAlmostLinearSSSP.Decremental.Native.initial_selected_accuracy,DecrAlmostLinearSSSP.Decremental.Native.initDone_scanTable⟩⟩⟩⟩⟩⟩⟩
