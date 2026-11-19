-- Prove2me | solution 1 for DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T11:22:22.603119+00:00
-- url     : https://prove2.me/submissions/3b532bef-2371-4668-a737-d71165b446d4

import Definitions.Def_DecrAlmostLinearSSSP_RAMFoundation
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_1
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_2
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_3
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_4
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_5
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_7
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_8
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
open scoped ENNReal NNReal
attribute [local instance] Classical.propDecidable
theorem DecrAlmostLinearSSSP.Decremental.machine_ext : ∀ {c d : DecrAlmostLinearSSSP.Decremental.Machine},
  @Eq.{1} Nat c.pc d.pc →
    @Eq.{1} (Nat → Real) c.realReg d.realReg →
      @Eq.{1} (Nat → Nat) c.natReg d.natReg →
        @Eq.{1} (Nat → Real) c.realMem d.realMem →
          @Eq.{1} (Nat → Nat) c.natMem d.natMem →
            @Eq.{1} Bool c.halted d.halted →
              @Eq.{1} Bool c.fault d.fault →
                @Eq.{1} Nat c.work d.work → @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine c d := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_1.1.2.1.1.2.2
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
theorem DecrAlmostLinearSSSP.Decremental.execute_add : ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (a b : Nat),
  @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
    (DecrAlmostLinearSSSP.Decremental.execute p c (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a b))
    (DecrAlmostLinearSSSP.Decremental.execute p (DecrAlmostLinearSSSP.Decremental.execute p c a) b) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_1.2.1.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.host_jump : ∀ (host : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (target : Nat),
  @Eq.{1} Bool c.halted Bool.false →
    @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
          DecrAlmostLinearSSSP.Decremental.Instruction
          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code c.pc)
        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
          (DecrAlmostLinearSSSP.Decremental.Instruction.jump target)) →
      @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
        (DecrAlmostLinearSSSP.Decremental.execute host c (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        { pc := target, realReg := c.realReg, natReg := c.natReg, realMem := c.realMem, natMem := c.natMem,
          halted := c.halted, fault := c.fault,
          work :=
            @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) } := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_1.2.1.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.embedded_header_exact : ∀ (host : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (pc : Nat),
  @Eq.{1} Bool c.halted Bool.false →
    @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
            DecrAlmostLinearSSSP.Decremental.Instruction
            (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
            (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code c.pc)
          (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
            (DecrAlmostLinearSSSP.Decremental.Instruction.natural
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pc
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
          @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
            (DecrAlmostLinearSSSP.Decremental.execute host c
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (DecrAlmostLinearSSSP.Decremental.headerState c pc) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_1.2.1.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.host_natural_jump : ∀ (host : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine)
  (reg value target : Nat),
  @Eq.{1} Bool c.halted Bool.false →
    @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
          DecrAlmostLinearSSSP.Decremental.Instruction
          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code c.pc)
        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
          (DecrAlmostLinearSSSP.Decremental.Instruction.natural reg value)) →
      @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
            DecrAlmostLinearSSSP.Decremental.Instruction
            (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
            (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
            (DecrAlmostLinearSSSP.Decremental.Instruction.jump target)) →
        @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
          (DecrAlmostLinearSSSP.Decremental.execute host c
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          { pc := target, realReg := c.realReg,
            natReg := @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat c.natReg reg value,
            realMem := c.realMem, natMem := c.natMem, halted := c.halted, fault := c.fault,
            work :=
              @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) } := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_1.2.1.2.1.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.branch_effect : ∀ (natural : Bool) (c : DecrAlmostLinearSSSP.Decremental.Machine) (a b target : Nat),
  @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
    (DecrAlmostLinearSSSP.Decremental.instructionEffect
      (DecrAlmostLinearSSSP.Decremental.branchInstruction natural a b target) c)
    (@ite.{1} DecrAlmostLinearSSSP.Decremental.Machine (DecrAlmostLinearSSSP.Decremental.branchTest natural c a b)
      (Classical.propDecidable (DecrAlmostLinearSSSP.Decremental.branchTest natural c a b))
      { pc := target, realReg := c.realReg, natReg := c.natReg, realMem := c.realMem, natMem := c.natMem,
        halted := c.halted, fault := c.fault, work := c.work }
      c) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_1.2.1.2.2.2.2.2
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
theorem DecrAlmostLinearSSSP.Decremental.step_straight : ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine)
  (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
  @Eq.{1} Bool c.halted Bool.false →
    @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
          DecrAlmostLinearSSSP.Decremental.Instruction
          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code c.pc)
        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins) →
      DecrAlmostLinearSSSP.Decremental.Straight ins →
        And
          (@Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.step p c).pc
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (And (@Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.step p c).halted Bool.false)
            (@Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.step p c).work
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.1.1.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.straight_prefix : ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (n : Nat),
  @Eq.{1} Bool c.halted Bool.false →
    (∀ (j : Nat),
        @LT.lt.{0} Nat instLTNat j n →
          ∃ ins,
            And
              (@Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                  DecrAlmostLinearSSSP.Decremental.Instruction
                  (fun as i =>
                    @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                  (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc j))
                (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins))
              (DecrAlmostLinearSSSP.Decremental.Straight ins)) →
      ∀ (j : Nat),
        @LE.le.{0} Nat instLENat j n →
          And
            (@Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.execute p c j).pc
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc j))
            (And (@Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.execute p c j).halted Bool.false)
              (@Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.execute p c j).work
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work j))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.1.1.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image.count : ∀ {s : DecrAlmostLinearSSSP.Decremental.Structured.Data} {height : Nat}
  {tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie height},
  @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image s height tree →
    @Ne.{1} Nat (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root height tree)
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
      @Eq.{1} Nat (s.natMem (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root height tree))
        (@DecrAlmostLinearSSSP.Decremental.RadixQueue.count height
          (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.abstract height tree)) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.1.1.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.Structured.jump_step : ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (target : Nat),
  @Eq.{1} Bool c.halted Bool.false →
    @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
          DecrAlmostLinearSSSP.Decremental.Instruction
          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code c.pc)
        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
          (DecrAlmostLinearSSSP.Decremental.Instruction.jump target)) →
      And
        (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Structured.Data
          (DecrAlmostLinearSSSP.Decremental.Structured.data
            (DecrAlmostLinearSSSP.Decremental.execute p c
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (DecrAlmostLinearSSSP.Decremental.Structured.data c))
        (And
          (@Eq.{1} Nat
            (DecrAlmostLinearSSSP.Decremental.execute p c
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).pc
            target)
          (And
            (@Eq.{1} Bool
              (DecrAlmostLinearSSSP.Decremental.execute p c
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).halted
              Bool.false)
            (@Eq.{1} Nat
              (DecrAlmostLinearSSSP.Decremental.execute p c
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).work
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.1.2.2.2.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.Structured.eval_nadd : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (d a b : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.nadd d a b) s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    { realReg := s.realReg,
      natReg :=
        @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natReg d
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (s.natReg a) (s.natReg b)),
      realMem := s.realMem, natMem := s.natMem } := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.1.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Structured.eval_sequence_atoms : ∀ (atoms : List.{0} DecrAlmostLinearSSSP.Decremental.Structured.Atom)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval
    (DecrAlmostLinearSSSP.Decremental.Structured.sequence
      (@List.map.{0, 0} DecrAlmostLinearSSSP.Decremental.Structured.Atom DecrAlmostLinearSSSP.Decremental.Structured.Cmd
        DecrAlmostLinearSSSP.Decremental.Structured.Cmd.atom atoms))
    s (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Structured.Atom atoms)
    (@List.foldl.{0, 0} DecrAlmostLinearSSSP.Decremental.Structured.Data
      DecrAlmostLinearSSSP.Decremental.Structured.Atom (fun t a => a.effect t) s atoms) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.2.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.step_nat_frame : ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine)
  (ins : DecrAlmostLinearSSSP.Decremental.Instruction) (k : Nat),
  @Eq.{1} Bool c.halted Bool.false →
    @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
          DecrAlmostLinearSSSP.Decremental.Instruction
          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code c.pc)
        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins) →
      Not (DecrAlmostLinearSSSP.Decremental.writesNat ins k) →
        @Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.step p c).natReg k) (c.natReg k) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.2.1.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.step_real_frame : ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine)
  (ins : DecrAlmostLinearSSSP.Decremental.Instruction) (k : Nat),
  @Eq.{1} Bool c.halted Bool.false →
    @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
          DecrAlmostLinearSSSP.Decremental.Instruction
          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code c.pc)
        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins) →
      Not (DecrAlmostLinearSSSP.Decremental.writesReal ins k) →
        @Eq.{1} Real ((DecrAlmostLinearSSSP.Decremental.step p c).realReg k) (c.realReg k) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.TriePop.choose_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    ∃ c,
      And
        (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePop.choose s c
          (DecrAlmostLinearSSSP.Decremental.Exact.TriePop.chosen s))
        (@LE.le.{0} Nat instLENat c (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_3.2.2.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.Powers.Prefix.step : ∀ {bound base d : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Powers.Prefix bound base d s →
    DecrAlmostLinearSSSP.Decremental.Exact.Powers.Prefix bound base
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (DecrAlmostLinearSSSP.Decremental.Exact.Powers.advanced s) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.1.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.bankAddress_injective : ∀ {base j k a b : Nat},
  @Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.bankAddress base j a)
      (DecrAlmostLinearSSSP.Decremental.bankAddress base k b) →
    And (@Eq.{1} Nat j k) (@Eq.{1} Nat a b) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.guest_bank_above : ∀ (base j a : Nat), @LT.lt.{0} Nat instLTNat base (DecrAlmostLinearSSSP.Decremental.bankAddress base j a) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.1.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.guest_bank_ne_host : ∀ (base j a b : Nat),
  @Ne.{1} Nat (DecrAlmostLinearSSSP.Decremental.bankAddress base j a)
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.1.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.scaled_less : ∀ (F a b : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) F →
    Iff
      (@LT.lt.{0} Nat instLTNat (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F a)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F b))
      (@LT.lt.{0} Nat instLTNat a b) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.2.1.1.2.1
theorem DecrAlmostLinearSSSP.Decremental.shadowReg_ne_meta : ∀ (j k : Nat),
  @LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) →
    @Ne.{1} Nat (DecrAlmostLinearSSSP.Decremental.shadowReg j) k := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.ShadowRep.host_clock : ∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    ∀ (pc work : Nat),
      DecrAlmostLinearSSSP.Decremental.ShadowRep base F
        { pc := pc, realReg := c.realReg, natReg := c.natReg, realMem := c.realMem, natMem := c.natMem,
          halted := c.halted, fault := c.fault, work := work }
        g := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.2.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.ShadowRep.nat_register : ∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
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
          natMem := g.natMem, halted := g.halted, fault := g.fault, work := g.work } := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.2.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.ShadowRep.scratch : ∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    ∀ (x : Nat),
      DecrAlmostLinearSSSP.Decremental.ShadowRep base F
        { pc := c.pc, realReg := c.realReg,
          natReg :=
            @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat c.natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) x,
          realMem := c.realMem, natMem := c.natMem, halted := c.halted, fault := c.fault, work := c.work }
        g := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.2.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.shadow_scalar : ∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    ∀ (ins tr : DecrAlmostLinearSSSP.Decremental.Instruction),
      @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (DecrAlmostLinearSSSP.Decremental.shadowScalarTranslation ins)
          (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction tr) →
        DecrAlmostLinearSSSP.Decremental.ShadowRep base F (DecrAlmostLinearSSSP.Decremental.instructionEffect tr c)
          (DecrAlmostLinearSSSP.Decremental.instructionEffect ins g) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.2.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.shadow_cast : ∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
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
              g) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.shadow_load : ∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
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
          (DecrAlmostLinearSSSP.Decremental.instructionEffect (DecrAlmostLinearSSSP.Decremental.Instruction.load d a) g) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.shadow_loadN : ∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
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
            g) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.2.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.shadow_store : ∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) F →
      ∀ (a d : Nat),
        @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (g.natReg a))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
          DecrAlmostLinearSSSP.Decremental.ShadowRep base F
            (DecrAlmostLinearSSSP.Decremental.instructionEffect
              (DecrAlmostLinearSSSP.Decremental.Instruction.store
                (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                (DecrAlmostLinearSSSP.Decremental.shadowReg d))
              c)
            (DecrAlmostLinearSSSP.Decremental.instructionEffect (DecrAlmostLinearSSSP.Decremental.Instruction.store a d)
              g) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.1.1.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.shadow_storeN : ∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) F →
      ∀ (a d : Nat),
        @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (g.natReg a))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
          DecrAlmostLinearSSSP.Decremental.ShadowRep base F
            (DecrAlmostLinearSSSP.Decremental.instructionEffect
              (DecrAlmostLinearSSSP.Decremental.Instruction.storeN
                (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                (DecrAlmostLinearSSSP.Decremental.shadowReg d))
              c)
            (DecrAlmostLinearSSSP.Decremental.instructionEffect
              (DecrAlmostLinearSSSP.Decremental.Instruction.storeN a d) g) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.1.1.1.1.1.2
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
theorem DecrAlmostLinearSSSP.Decremental.ShadowRep.pc_update : ∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    ∀ (pc : Nat),
      DecrAlmostLinearSSSP.Decremental.ShadowRep base F
        { pc := c.pc, realReg := c.realReg,
          natReg :=
            @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat c.natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) pc,
          realMem := c.realMem, natMem := c.natMem, halted := c.halted, fault := c.fault, work := c.work }
        { pc := pc, realReg := g.realReg, natReg := g.natReg, realMem := g.realMem, natMem := g.natMem,
          halted := g.halted, fault := g.fault, work := g.work } := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.1.1.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.ShadowRep.halt_update : ∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    DecrAlmostLinearSSSP.Decremental.ShadowRep base F
      { pc := c.pc, realReg := c.realReg,
        natReg :=
          @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat c.natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))),
        realMem := c.realMem, natMem := c.natMem, halted := c.halted, fault := c.fault, work := c.work }
      { pc := g.pc, realReg := g.realReg, natReg := g.natReg, realMem := g.realMem, natMem := g.natMem,
        halted := Bool.true, fault := g.fault, work := g.work } := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.1.1.1.2.1.2
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
theorem DecrAlmostLinearSSSP.Decremental.Reachable.trans : ∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {u v w : Fin n},
  @DecrAlmostLinearSSSP.Decremental.Reachable n k g active u v →
    @DecrAlmostLinearSSSP.Decremental.Reachable n k g active v w →
      @DecrAlmostLinearSSSP.Decremental.Reachable n k g active u w := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.2.1.2.2.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.OnlineRun.length : ∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {i : DecrAlmostLinearSSSP.Decremental.Input} {ds : List.{0} (Fin i.k)}
  {cs : List.{0} DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.OnlineRun p i ds cs →
    @Eq.{1} Nat (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Machine cs)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_8.2.2.1.2.2.2.2
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
lemma loop_bounded (test : Test) (body : Cmd) (invariant : Data → Prop) (rank : Data → ℕ) (B : ℕ)
    (hbody : ∀ s,invariant s → test.holds s → ∃ t cost,Eval body s cost t ∧
      invariant t ∧ rank t < rank s ∧ cost ≤ B) :
    ∀ s,invariant s → ∃ t cost,Eval (.loop test body) s cost t ∧
      invariant t ∧ cost ≤ (B+2)*rank s+2 := by
  classical
  suffices ∀ n,∀ s,rank s = n → invariant s → ∃ t cost,Eval (.loop test body) s cost t ∧
      invariant t ∧ cost ≤ (B+2)*rank s+2 by intro s hs;exact this (rank s) s rfl hs
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro s hr hs
    by_cases htest : test.holds s
    · obtain ⟨t,cost,hst,ht,hrt,hcost⟩ := hbody s hs htest
      obtain ⟨u,rest,htu,hu,hrest⟩ := ih (rank t) (by omega) t rfl ht
      have hmul := Nat.mul_le_mul_left (B+2) (Nat.succ_le_of_lt hrt)
      rw [Nat.mul_succ] at hmul
      exact ⟨u,cost+rest+2,.loopYes htest hst htu,hu,by omega⟩
    · exact ⟨s,2,.loopNo s htest,hs,by omega⟩
lemma loop_amortized (test : Test) (body : Cmd) (invariant : Data → Prop)
    (rank budget : Data → ℕ)
    (hbody : ∀ s,invariant s → test.holds s → ∃ t cost,Eval body s cost t ∧
      invariant t ∧ rank t < rank s ∧ cost+2+budget t ≤ budget s) :
    ∀ s,invariant s → ∃ t cost,Eval (.loop test body) s cost t ∧
      invariant t ∧ cost+budget t ≤ budget s+2 := by
  classical
  suffices ∀ n,∀ s,rank s = n → invariant s → ∃ t cost,Eval (.loop test body) s cost t ∧
      invariant t ∧ cost+budget t ≤ budget s+2 by intro s hs;exact this (rank s) s rfl hs
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro s hr hs
    by_cases htest : test.holds s
    · obtain ⟨t,cost,hst,ht,hrt,hcost⟩ := hbody s hs htest
      obtain ⟨u,rest,htu,hu,hrest⟩ := ih (rank t) (by omega) t rfl ht
      exact ⟨u,cost+rest+2,.loopYes htest hst htu,hu,by omega⟩
    · exact ⟨s,2,.loopNo s htest,hs,by omega⟩
lemma eval_loop_stops (test : Test) (body : Cmd) (cost : ℕ) :
    ∀ s t,Eval (.loop test body) s cost t → ¬test.holds t := by
  induction cost using Nat.strong_induction_on with
  | h cost ih =>
    intro s t he
    cases he with
    | loopNo s hc => exact hc
    | @loopYes _ _ _ mid _ first rest hc hb hr =>
      exact ih rest (by omega) mid t hr
end DecrAlmostLinearSSSP.Decremental.Structured
end s37
section s38
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.ScaledCeiling
open Structured
attribute [local instance] Classical.propDecidable
lemma initial_eval (s : Data) : Eval (sequence (initAtoms.map Cmd.atom)) s 8 (initial s) := eval_sequence_atoms initAtoms s
lemma build_eval (s : Data) : Eval buildBody s 5 (buildStep s) := eval_sequence_atoms buildAtoms s
lemma choose_eval (s : Data) : Eval chooseBody s 2 (chooseStep s) := eval_sequence_atoms chooseAtoms s
lemma greedy_eval (s : Data) : ∃ cost ≤ 7,Eval greedyBody s cost (greedyStep s) := by
  classical
  have hp := eval_sequence_atoms greedyPrefixAtoms s
  by_cases hc : chooseTest.holds (greedyPrefix s)
  · refine ⟨7,le_rfl,?_⟩
    change Eval (.seq _ _) s 7 (if chooseTest.holds (greedyPrefix s) then _ else _)
    rw [if_pos hc]
    exact .seq hp (.branchYes hc (choose_eval _))
  · refine ⟨6,by omega,?_⟩
    change Eval (.seq _ _) s 6 (if chooseTest.holds (greedyPrefix s) then _ else _)
    rw [if_neg hc]
    exact .seq hp (.branchNo hc (.skip _))
lemma initial_invariant (s : Data) (N : ℕ) : BuildInvariant (s.natReg 0) (s.realReg 0) N (initial s) := by
  constructor
  · constructor <;> simp [initial,runAtoms,initAtoms,Atom.effect,data,Data.machine,instructionEffect]
  all_goals simp [initial,runAtoms,initAtoms,Atom.effect,data,Data.machine,instructionEffect,StackCorrect]
end DecrAlmostLinearSSSP.Decremental.ScaledCeiling
end s38
section s39
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.ScaledCeiling
open Structured
lemma buildStep_fields (s : Data) :
    (buildStep s).natReg 1 = s.natReg 1+s.natReg 4 ∧
    (buildStep s).realReg 1 = s.realReg 1+s.realReg 1 ∧
    (buildStep s).natReg 2 = s.natReg 2+s.natReg 2 ∧
    (buildStep s).realReg 2 = s.realReg 2 ∧ (buildStep s).natReg 3 = s.natReg 3 ∧
    (buildStep s).realMem = Function.update s.realMem (s.natReg 1) (s.realReg 1) ∧
    (buildStep s).natMem = Function.update s.natMem (s.natReg 1) (s.natReg 2) := by
  simp [buildStep,runAtoms,buildAtoms,Atom.effect,data,Data.machine,instructionEffect]
lemma buildStep_constants {P : ℕ} {x : ℝ} {s : Data} (h : Constants P x s) : Constants P x (buildStep s) := by
  constructor <;> simp [buildStep,runAtoms,buildAtoms,Atom.effect,data,Data.machine,instructionEffect,
    h.factor,h.input,h.one,h.zeroN,h.zeroR]
lemma buildStep_invariant {P N : ℕ} {x : ℝ} {s : Data} (h : BuildInvariant P x N s)
    (hupper : x ≤ (2 : ℝ)^N) (htest : buildTest.holds s) :
    BuildInvariant P x N (buildStep s) ∧ N-(buildStep s).natReg 1 < N-s.natReg 1 := by
  obtain ⟨hd,hp,hprod,hlower,hsum,hrmem,hnmem⟩ := buildStep_fields s
  rw [h.one] at hd
  have ht : (2 : ℝ)^(s.natReg 1) < x := by simpa only [buildTest,Test.holds,h.input,h.power] using htest
  have hdlt : s.natReg 1 < N := by
    by_contra hn
    have heq : s.natReg 1 = N := Nat.le_antisymm h.depth (Nat.le_of_not_gt hn)
    rw [heq] at ht
    exact (not_lt_of_ge hupper) ht
  refine ⟨?_,by omega⟩
  constructor
  · exact buildStep_constants h.toConstants
  · rw [hd]
    omega
  · rw [hp,hd,h.power,pow_succ]
    ring
  · rw [hprod,hd,h.product,pow_succ]
    ring
  · rw [hlower,h.lower]
  · rw [hsum,h.sum]
  · intro j hj
    rw [hd] at hj
    by_cases heq : j = s.natReg 1
    · subst j
      rw [hrmem,hnmem,Function.update_self,Function.update_self]
      exact ⟨h.power,h.product⟩
    · have hjold : j < s.natReg 1 := by omega
      rw [hrmem,hnmem,Function.update_of_ne heq,Function.update_of_ne heq]
      exact h.stack j hjold
lemma build_terminates {P N : ℕ} {x : ℝ} {s : Data} (h : BuildInvariant P x N s)
    (hupper : x ≤ (2 : ℝ)^N) :
    ∃ t cost,Eval buildLoop s cost t ∧ BuildInvariant P x N t ∧
      ¬buildTest.holds t ∧ cost ≤ 7*(N-s.natReg 1)+2 := by
  have hbody : ∀ u,BuildInvariant P x N u → buildTest.holds u →
      ∃ v cost,Eval buildBody u cost v ∧ BuildInvariant P x N v ∧
        N-v.natReg 1 < N-u.natReg 1 ∧ cost ≤ 5 := by
    intro u hu ht
    obtain ⟨hv,hrank⟩ := buildStep_invariant hu hupper ht
    exact ⟨buildStep u,5,build_eval u,hv,hrank,le_rfl⟩
  obtain ⟨t,cost,he,ht,hcost⟩ := loop_bounded buildTest buildBody (BuildInvariant P x N)
    (fun u => N-u.natReg 1) 5 hbody s h
  exact ⟨t,cost,he,ht,eval_loop_stops buildTest buildBody cost s t he,hcost⟩
end DecrAlmostLinearSSSP.Decremental.ScaledCeiling
end s39
section s40
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.ScaledCeiling
open Structured
lemma greedyPrefix_fields (s : Data) :
    (greedyPrefix s).natReg 1 = s.natReg 1-s.natReg 4 ∧
    (greedyPrefix s).realReg 2 = s.realReg 2 ∧
    (greedyPrefix s).realReg 4 = s.realReg 2+s.realMem (s.natReg 1-s.natReg 4) ∧
    (greedyPrefix s).natReg 3 = s.natReg 3 ∧
    (greedyPrefix s).natReg 6 = s.natMem (s.natReg 1-s.natReg 4) ∧
    (greedyPrefix s).realMem = s.realMem ∧ (greedyPrefix s).natMem = s.natMem := by
  simp [greedyPrefix,runAtoms,greedyPrefixAtoms,Atom.effect,data,Data.machine,instructionEffect]
lemma greedyPrefix_constants {P : ℕ} {x : ℝ} {s : Data} (h : Constants P x s) : Constants P x (greedyPrefix s) := by
  constructor <;> simp [greedyPrefix,runAtoms,greedyPrefixAtoms,Atom.effect,data,Data.machine,instructionEffect,
    h.factor,h.input,h.one,h.zeroN,h.zeroR]
lemma chooseStep_constants {P : ℕ} {x : ℝ} {s : Data} (h : Constants P x s) : Constants P x (chooseStep s) := by
  constructor <;> simp [chooseStep,runAtoms,chooseAtoms,Atom.effect,data,Data.machine,instructionEffect,
    h.factor,h.input,h.one,h.zeroN,h.zeroR]
lemma chooseStep_fields (s : Data) :
    (chooseStep s).natReg 1 = s.natReg 1 ∧
    (chooseStep s).realReg 2 = s.realReg 4+s.realReg 5 ∧
    (chooseStep s).natReg 3 = s.natReg 3+s.natReg 6 ∧
    (chooseStep s).realMem = s.realMem ∧ (chooseStep s).natMem = s.natMem := by
  simp [chooseStep,runAtoms,chooseAtoms,Atom.effect,data,Data.machine,instructionEffect]
lemma greedyStep_invariant {P : ℕ} {x : ℝ} {s : Data} (h : GreedyInvariant P x s)
    (htest : greedyTest.holds s) :
    GreedyInvariant P x (greedyStep s) ∧ (greedyStep s).natReg 1 < s.natReg 1 := by
  classical
  have hdpos : 0 < s.natReg 1 := by simpa only [greedyTest,Test.holds,h.zeroN] using htest
  let k := s.natReg 1-1
  have hd : s.natReg 1 = k+1 := by dsimp [k];omega
  have hk : k < s.natReg 1 := by omega
  obtain ⟨hrpow,hnpow⟩ := h.stack k hk
  obtain ⟨q,hq,hprod,hqx,hx⟩ := h.lower
  obtain ⟨hpd,hpq,hpc,hps,hpl,hpmr,hpmn⟩ := greedyPrefix_fields s
  rw [h.one] at hpd hpc hpl
  have hprefix : Constants P x (greedyPrefix s) := greedyPrefix_constants h.toConstants
  have hpval : (greedyPrefix s).realReg 4 = (q : ℝ)+(2 : ℝ)^k := by rw [hpc,hq];exact congrArg ((q : ℝ)+·) hrpow
  have hpProd : (greedyPrefix s).natReg 6 = P*2^k := by rw [hpl];exact hnpow
  have hdouble : (2 : ℝ)^(s.natReg 1) = (2 : ℝ)^k+(2 : ℝ)^k := by rw [hd,pow_succ];ring
  by_cases hc : chooseTest.holds (greedyPrefix s)
  · rw [greedyStep,if_pos hc]
    obtain ⟨hcd,hcq,hcs,hcmr,hcmn⟩ := chooseStep_fields (greedyPrefix s)
    have hnewdepth : (chooseStep (greedyPrefix s)).natReg 1 = k := hcd.trans hpd
    refine ⟨?_,by rw [hnewdepth];exact hk⟩
    constructor
    · exact chooseStep_constants hprefix
    · intro j hj
      rw [hnewdepth] at hj
      have hold := h.stack j (by omega)
      rw [hcmr,hcmn,hpmr,hpmn]
      exact hold
    · refine ⟨q+2^k,?_,?_,?_,?_⟩
      · rw [hcq,hprefix.zeroR,Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat,hpval]
        simp
      · rw [hcs,hps,hprod,hpProd]
        ring
      · have hlt : (greedyPrefix s).realReg 4 < x := by simpa only [chooseTest,Test.holds,hprefix.input] using hc
        rw [hpval] at hlt
        simpa only [Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat] using hlt
      · rw [hnewdepth,Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat]
        rw [hdouble] at hx
        linarith
  · rw [greedyStep,if_neg hc]
    have hnewdepth : (greedyPrefix s).natReg 1 = k := hpd
    refine ⟨?_,by rw [hnewdepth];exact hk⟩
    constructor
    · exact hprefix
    · intro j hj
      rw [hnewdepth] at hj
      rw [hpmr,hpmn]
      exact h.stack j (by omega)
    · refine ⟨q,hpq.trans hq,hps.trans hprod,hqx,?_⟩
      have hle : x ≤ (greedyPrefix s).realReg 4 := by
        have hh : ¬(greedyPrefix s).realReg 4 < x := by simpa only [chooseTest,Test.holds,hprefix.input] using hc
        exact le_of_not_gt hh
      rw [hpval] at hle
      rwa [hnewdepth]
lemma greedy_terminates {P : ℕ} {x : ℝ} {s : Data} (h : GreedyInvariant P x s) :
    ∃ t cost,Eval greedyLoop s cost t ∧ GreedyInvariant P x t ∧
      ¬greedyTest.holds t ∧ cost ≤ 9*s.natReg 1+2 := by
  have hbody : ∀ u,GreedyInvariant P x u → greedyTest.holds u →
      ∃ v cost,Eval greedyBody u cost v ∧ GreedyInvariant P x v ∧
        v.natReg 1 < u.natReg 1 ∧ cost ≤ 7 := by
    intro u hu ht
    obtain ⟨cost,hcost,he⟩ := greedy_eval u
    obtain ⟨hv,hrank⟩ := greedyStep_invariant hu ht
    exact ⟨greedyStep u,cost,he,hv,hrank,hcost⟩
  obtain ⟨t,cost,he,ht,hcost⟩ := loop_bounded greedyTest greedyBody (GreedyInvariant P x)
    (fun u => u.natReg 1) 7 hbody s h
  exact ⟨t,cost,he,ht,eval_loop_stops greedyTest greedyBody cost s t he,hcost⟩
end DecrAlmostLinearSSSP.Decremental.ScaledCeiling
end s40
section s41
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.ScaledCeiling
open Structured
lemma greedy_output {P : ℕ} {x : ℝ} {s : Data} (h : GreedyInvariant P x s)
    (hstop : ¬greedyTest.holds s) :
    s.natReg 3+s.natReg 0 = P*⌈x⌉₊ := by
  have hd0 : s.natReg 1 = 0 := by
    have hh : ¬0 < s.natReg 1 := by simpa only [greedyTest,Test.holds,h.zeroN] using hstop
    omega
  obtain ⟨q,hq,hsum,hqx,hx⟩ := h.lower
  rw [hd0,pow_zero] at hx
  have hceil : ⌈x⌉₊ = q+1 := (Nat.ceil_eq_iff (by omega : q+1 ≠ 0)).mpr (by
    simpa only [Nat.add_sub_cancel_right,Nat.cast_add,Nat.cast_one] using And.intro hqx hx)
  rw [hsum,h.factor,hceil]
  ring
lemma routine_correct (s : Data) (N : ℕ) (hnonneg : 0 ≤ s.realReg 0) (hupper : s.realReg 0 ≤ (2 : ℝ)^N) :
    ∃ t cost,Eval routine s cost t ∧ t.natReg 3 = s.natReg 0*⌈s.realReg 0⌉₊ ∧ cost ≤ 16*N+14 := by
  classical
  let P := s.natReg 0
  let x := s.realReg 0
  have hinit : BuildInvariant P x N (initial s) := initial_invariant s N
  by_cases hx : 0 < x
  · have htest : (Test.realLess 5 0).holds (initial s) := by
      simpa only [Test.holds,hinit.zeroR,hinit.input] using hx
    obtain ⟨b,buildCost,hbuild,hb,hbStop,hbuildCost⟩ := build_terminates hinit hupper
    have hbound : x ≤ (2 : ℝ)^(b.natReg 1) := by
      have hh : ¬(2 : ℝ)^(b.natReg 1) < x := by simpa only [buildTest,Test.holds,hb.power,hb.input] using hbStop
      exact le_of_not_gt hh
    have hgreedy : GreedyInvariant P x b := by
      constructor
      · exact hb.toConstants
      · exact hb.stack
      · exact ⟨0,by simpa using hb.lower,by simpa using hb.sum,by simpa only [Nat.cast_zero] using hx,by simpa using hbound⟩
    obtain ⟨c,greedyCost,hgc,hc,hcStop,hgcCost⟩ := greedy_terminates hgreedy
    let t : Data := {c with natReg := Function.update c.natReg 3 (c.natReg 3+c.natReg 0)}
    have hadd : Eval (nadd 3 3 0) c 1 t := eval_nadd c 3 3 0
    have hcalc : Eval calculation (initial s) (buildCost+greedyCost+1) t := by
      have hh := Eval.seq hbuild (Eval.seq hgc (Eval.seq hadd (Eval.skip t)))
      simpa only [calculation,Structured.sequence,Nat.add_zero,Nat.add_assoc] using hh
    have hroutine : Eval routine s (buildCost+greedyCost+10) t := by
      have hh := Eval.seq (initial_eval s) (Eval.branchYes (no := natural 3 0) htest hcalc)
      simpa only [routine,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
    refine ⟨t,buildCost+greedyCost+10,hroutine,?_,?_⟩
    · change c.natReg 3+c.natReg 0 = _
      exact greedy_output hc hcStop
    · have hiDepth : (initial s).natReg 1 = 0 := by simp [initial,runAtoms,initAtoms,Atom.effect,data,Data.machine,instructionEffect]
      rw [hiDepth,Nat.sub_zero] at hbuildCost
      have hdepth := hb.depth
      omega
  · have hx0 : x = 0 := le_antisymm (le_of_not_gt hx) hnonneg
    have htest : ¬(Test.realLess 5 0).holds (initial s) := by
      simpa only [Test.holds,hinit.zeroR,hinit.input] using hx
    let t : Data := {initial s with natReg := Function.update (initial s).natReg 3 0}
    have hz : Eval (natural 3 0) (initial s) 1 t := eval_natural _ 3 0
    have hroutine : Eval routine s 11 t := Eval.seq (initial_eval s) (Eval.branchNo (yes := calculation) htest hz)
    refine ⟨t,11,hroutine,?_,by omega⟩
    · change 0 = P*⌈x⌉₊
      rw [hx0]
      simp
lemma routine_ends (c : Machine) (N : ℕ)
    (hpc : c.pc = 0) (hh : c.halted = false) (hf : c.fault = false)
    (hnonneg : 0 ≤ c.realReg 0) (hupper : c.realReg 0 ≤ (2 : ℝ)^N) :
    ∃ d,Ends (program routine .skip) c d ∧ d.natReg 3 = c.natReg 0*⌈c.realReg 0⌉₊ ∧
      d.work ≤ c.work+16*N+15 := by
  obtain ⟨s,cost,he,hs,hcost⟩ := routine_correct (data c) N hnonneg hupper
  obtain ⟨d,hd,hdData,hdWork⟩ := command_ends he (program routine .skip) 0 c (program_init routine .skip)
    hpc rfl hh hf (program_init_halt routine .skip)
  refine ⟨d,hd,?_,by omega⟩
  have hobs := congrArg (fun u : Data => u.natReg 3) hdData
  exact hobs.trans hs
end DecrAlmostLinearSSSP.Decremental.ScaledCeiling
end s41
section s42
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma repeated_nadd (p : Program) (c : Machine) (d factor count : ℕ)
    (hne : factor ≠ d) (hh : c.halted = false)
    (hcode : ∀ j < count, p.code[c.pc + j]? = some (.nadd d d factor)) :
    execute p c count = {c with
      pc := c.pc + count
      work := c.work + count
      natReg := Function.update c.natReg d (c.natReg d + count * c.natReg factor)} := by
  classical
  induction count with
  | zero => simp [execute]
  | succ count ih =>
    have hi := ih (fun j hj => hcode j (by omega))
    rw [execute_add, hi]
    change step p _ = _
    simp only [step, hh, Bool.false_eq_true, if_false, hcode count (by omega),
      Function.update_self, Function.update_of_ne hne, Function.update_idem]
    apply machine_ext
    · rfl
    · rfl
    · congr 1
      ring
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
lemma constantProductCode_length (d factor q : ℕ) : (constantProductCode d factor q).length = q + 1 := by
  simp [constantProductCode]
lemma constant_product_run (p : Program) (c : Machine) (d factor q : ℕ)
    (hne : factor ≠ d) (hh : c.halted = false)
    (h0 : p.code[c.pc]? = some (.natural d 0))
    (hcode : ∀ j < q, p.code[c.pc + 1 + j]? = some (.nadd d d factor)) :
    execute p c (q + 1) = {c with
      pc := c.pc + (q + 1)
      work := c.work + (q + 1)
      natReg := Function.update c.natReg d (q * c.natReg factor)} := by
  classical
  let b : Machine := {c with pc := c.pc + 1, work := c.work + 1, natReg := Function.update c.natReg d 0}
  have hb : execute p c 1 = b := by
    change step p c = b
    simp [step, b, hh, h0]
  have hr := repeated_nadd p b d factor q hne hh hcode
  rw [show q + 1 = 1 + q by omega, execute_add, hb, hr]
  simp only [b, Function.update_self, Function.update_of_ne hne, Nat.zero_add, Function.update_idem]
  congr 1 <;> omega
end DecrAlmostLinearSSSP.Decremental
end s42
section s43
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma shadowBlock_length (width offset returnPC pc : ℕ) (ins : Instruction)
    (hwidth : 8 ≤ width) (hconst : naturalConstant ins + 4 ≤ width) :
    (shadowBlock width offset returnPC pc ins).length = width := by
  cases ins <;> simp only [shadowBlock, List.length_append, List.length_cons, List.length_nil,
    List.length_replicate, constantProductCode_length, naturalConstant] at * <;> omega
lemma source_constant_bound (code : List Instruction) (ins : Instruction) (hins : ins ∈ code) :
    naturalConstant ins + 4 ≤ shadowWidth code := by
  have hh : naturalConstant ins ≤ (code.map naturalConstant).sum :=
    List.single_le_sum (fun x _ => Nat.zero_le x) (naturalConstant ins) (List.mem_map.mpr ⟨ins,hins,rfl⟩)
  unfold shadowWidth
  omega
lemma shadowWidth_positive (code : List Instruction) : 8 ≤ shadowWidth code := by unfold shadowWidth; omega
lemma shadowCodeAux_length (width offset returnPC start : ℕ) (code : List Instruction)
    (hw : 8 ≤ width) (hc : ∀ ins ∈ code, naturalConstant ins + 4 ≤ width) :
    (shadowCodeAux width offset returnPC start code).length = width * code.length := by
  induction code generalizing start with
  | nil => rfl
  | cons ins rest ih =>
    simp only [shadowCodeAux, List.length_append, shadowBlock_length width offset returnPC start ins hw
      (hc ins (List.mem_cons_self)), List.length_cons]
    rw [ih (start + 1) (fun tr htr => hc tr (List.mem_cons_of_mem ins htr))]
    ring
lemma shadowCode_length (offset returnPC : ℕ) (code : List Instruction) :
    (shadowCode offset returnPC code).length = shadowWidth code * code.length :=
  shadowCodeAux_length _ _ _ _ _ (shadowWidth_positive code) (source_constant_bound code)
end DecrAlmostLinearSSSP.Decremental
end s43
section s44
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma ShadowRep.header {base F : ℕ} {c g : Machine} (h : ShadowRep base F c g)
    (host : Program) (hh : c.halted = false) (hone : c.natReg 1 = 1)
    (h0 : host.code[c.pc]? = some (.natural 2 (g.pc + 1)))
    (h1 : host.code[c.pc + 1]? = some (.nadd 3 3 1)) :
    ShadowRep base F (execute host c 2) {g with pc := g.pc + 1, work := g.work + 1} := by
  rw [embedded_header_exact host c g.pc hh hone h0 h1]
  have hr := (h.metadata (g.pc + 1) (g.work + 1)).host_clock (c.pc + 2) (c.work + 2)
  simpa only [headerState, h.work] using hr
lemma ShadowRep.scalar_step {base F : ℕ} {c g : Machine} (h : ShadowRep base F c g)
    (host : Program) (ins tr : Instruction) (ht : shadowScalarTranslation ins = some tr)
    (hh : c.halted = false) (hc : host.code[c.pc]? = some tr) :
    ShadowRep base F (step host c) (instructionEffect ins g) := by
  rw [step_eq_effect host c tr hh hc]
  exact shadow_scalar (h.host_clock (c.pc + 1) (c.work + 1)) ins tr ht
lemma ShadowRep.jump_step {base F : ℕ} {c g : Machine} (h : ShadowRep base F c g)
    (host : Program) (target : ℕ) (hh : c.halted = false)
    (hc : host.code[c.pc]? = some (.jump target)) : ShadowRep base F (step host c) g := by
  have he := host_jump host c target hh hc
  change ShadowRep base F (execute host c 1) g
  rw [he]
  exact h.host_clock target (c.work + 1)
lemma ShadowRep.constant_run {base F : ℕ} {c g : Machine} (h : ShadowRep base F c g)
    (host : Program) (d q : ℕ) (hfactor : c.natReg 7 = F) (hh : c.halted = false)
    (h0 : host.code[c.pc]? = some (.natural (shadowReg d) 0))
    (hcode : ∀ j < q, host.code[c.pc + 1 + j]? = some (.nadd (shadowReg d) (shadowReg d) 7)) :
    ShadowRep base F (execute host c (q + 1)) (instructionEffect (.natural d q) g) := by
  rw [constant_product_run host c (shadowReg d) 7 q (shadowReg_ne_meta d 7 (by omega)).symm hh h0 hcode]
  rw [hfactor, Nat.mul_comm q F]
  exact (h.nat_register d q).host_clock (c.pc + (q + 1)) (c.work + (q + 1))
end DecrAlmostLinearSSSP.Decremental
end s44
section s45
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma shadowBlock_reserved (width offset returnPC pc : ℕ) (ins : Instruction) :
    ∀ tr ∈ shadowBlock width offset returnPC pc ins, ReservedSafe tr := by
  cases ins <;> simp [shadowBlock, constantProductCode, ReservedSafe, writesNat, writesReal, shadowReg]
  all_goals try omega
  constructor
  · omega
  · intro tr htr
    rcases htr with ⟨_, rfl⟩ | rfl | ⟨_, rfl⟩
    all_goals simp <;> omega
lemma shadowCodeAux_reserved (width offset returnPC start : ℕ) (code : List Instruction) :
    ∀ tr ∈ shadowCodeAux width offset returnPC start code, ReservedSafe tr := by
  induction code generalizing start with
  | nil => simp [shadowCodeAux]
  | cons ins rest ih =>
    intro tr htr
    rcases List.mem_append.mp htr with htr | htr
    · exact shadowBlock_reserved width offset returnPC start ins tr htr
    · exact ih (start + 1) tr htr
lemma write_preserves_other_bank {α : Type} (mem : ℕ → α) (base j k a b : ℕ) (value : α)
    (hjk : j ≠ k) :
    Function.update mem (bankAddress base j a) value (bankAddress base k b) = mem (bankAddress base k b) := by
  classical
  apply Function.update_of_ne
  intro heq
  exact hjk ((bankAddress_injective heq).1).symm
lemma write_preserves_host_bank {α : Type} (mem : ℕ → α) (base j a b : ℕ) (value : α) :
    Function.update mem (bankAddress base j a) value (base + (2 * b + 1)) = mem (base + (2 * b + 1)) := by
  classical
  exact Function.update_of_ne (guest_bank_ne_host base j a b).symm _ _
lemma write_preserves_public_prefix {α : Type} (mem : ℕ → α) (base j a b : ℕ) (value : α)
    (hb : b ≤ base) : Function.update mem (bankAddress base j a) value b = mem b := by
  classical
  apply Function.update_of_ne
  have hp := guest_bank_above base j a
  omega
end DecrAlmostLinearSSSP.Decremental
end s45
section s46
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma shadowScalar_reserved (ins tr : Instruction) (ht : shadowScalarTranslation ins = some tr) : ReservedSafe tr := by
  cases ins <;> simp only [shadowScalarTranslation] at ht
  all_goals cases ht
  all_goals simp [ReservedSafe, writesNat, writesReal, shadowReg] <;> omega
lemma host_shadow_scalar {base F : ℕ} {c g : Machine} (hr : ShadowRep base F c g)
    (host : Program) (ins tr : Instruction) (ht : shadowScalarTranslation ins = some tr)
    (hh : c.halted = false) (hc : host.code[c.pc]? = some tr) :
    ShadowRep base F (execute host c 1) (instructionEffect ins g) ∧
      (execute host c 1).pc = c.pc + 1 ∧ (execute host c 1).work = c.work + 1 ∧
      (execute host c 1).halted = false ∧
      (execute host c 1).natReg 0 = c.natReg 0 ∧ (execute host c 1).natReg 1 = c.natReg 1 ∧
      (execute host c 1).natReg 7 = c.natReg 7 ∧ (execute host c 1).realReg 7 = c.realReg 7 := by
  have hs := shadowScalar_reserved ins tr ht
  refine ⟨hr.scalar_step host ins tr ht hh hc, ?_, ?_, ?_,
    step_nat_frame host c tr 0 hh hc hs.1,
    step_nat_frame host c tr 1 hh hc hs.2.1,
    step_nat_frame host c tr 7 hh hc hs.2.2.1,
    step_real_frame host c tr 7 hh hc hs.2.2.2⟩
  all_goals cases ins <;> simp only [shadowScalarTranslation] at ht
  all_goals cases ht
  all_goals simp only [execute, Function.iterate_one, step, hh, Bool.false_eq_true, if_false, hc]
lemma shadow_simple_macro {base F : ℕ} {c g : Machine} (hr : ShadowRep base F c g)
    (host : Program) (width offset : ℕ) (ins tr : Instruction) (ht : shadowScalarTranslation ins = some tr)
    (hh : c.halted = false) (hone : c.natReg 1 = 1)
    (h0 : host.code[c.pc]? = some (.natural 2 (g.pc + 1)))
    (h1 : host.code[c.pc + 1]? = some (.nadd 3 3 1))
    (h2 : host.code[c.pc + 2]? = some tr)
    (h3 : host.code[c.pc + 3]? = some (.jump (offset + width * (g.pc + 1)))) :
    ∃ d, execute host c 4 = d ∧
      ShadowRep base F d (instructionEffect ins {g with pc := g.pc + 1, work := g.work + 1}) ∧
      d.pc = offset + width * (g.pc + 1) ∧ d.work = c.work + 4 ∧ d.halted = false ∧
      d.natReg 0 = c.natReg 0 ∧ d.natReg 1 = c.natReg 1 ∧
      d.natReg 7 = c.natReg 7 ∧ d.realReg 7 = c.realReg 7 := by
  let b := headerState c g.pc
  have hb : execute host c 2 = b := embedded_header_exact host c g.pc hh hone h0 h1
  have hbrep : ShadowRep base F b {g with pc := g.pc + 1, work := g.work + 1} := by
    rw [← hb]
    exact hr.header host hh hone h0 h1
  obtain ⟨hrep, hpc, hw, hhalt, hm0, hm1, hm7, hreal7⟩ := host_shadow_scalar hbrep host ins tr ht hh h2
  let t := execute host b 1
  have hjc : host.code[t.pc]? = some (.jump (offset + width * (g.pc + 1))) := by
    change host.code[(execute host b 1).pc]? = _
    rw [hpc]
    simpa [b, headerState, Nat.add_assoc] using h3
  have hj := host_jump host t (offset + width * (g.pc + 1)) hhalt hjc
  let d : Machine := {t with pc := offset + width * (g.pc + 1), work := t.work + 1}
  refine ⟨d, ?_, hrep.host_clock _ _, rfl, ?_, hhalt, hm0, hm1, hm7, hreal7⟩
  · rw [show 4 = 2 + (1 + 1) by omega, execute_add, hb, execute_add]
    exact hj
  · change (execute host b 1).work + 1 = c.work + 4
    rw [hw]
    rfl
end DecrAlmostLinearSSSP.Decremental
end s46
section s47
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma shadow_jump_macro {base F : ℕ} {c g : Machine} (hr : ShadowRep base F c g)
    (host : Program) (width offset target : ℕ)
    (hh : c.halted = false) (hone : c.natReg 1 = 1)
    (h0 : host.code[c.pc]? = some (.natural 2 (g.pc + 1)))
    (h1 : host.code[c.pc + 1]? = some (.nadd 3 3 1))
    (h2 : host.code[c.pc + 2]? = some (.natural 2 target))
    (h3 : host.code[c.pc + 3]? = some (.jump (offset + width * target))) :
    ∃ d, execute host c 4 = d ∧
      ShadowRep base F d (instructionEffect (.jump target) {g with pc := g.pc + 1, work := g.work + 1}) ∧
      d.pc = offset + width * target ∧ d.work = c.work + 4 ∧ d.halted = false ∧
      d.natReg 0 = c.natReg 0 ∧ d.natReg 1 = c.natReg 1 ∧
      d.natReg 7 = c.natReg 7 ∧ d.realReg 7 = c.realReg 7 := by
  let b := headerState c g.pc
  have hb : execute host c 2 = b := embedded_header_exact host c g.pc hh hone h0 h1
  have hbrep : ShadowRep base F b {g with pc := g.pc + 1, work := g.work + 1} := by
    rw [← hb]
    exact hr.header host hh hone h0 h1
  let d : Machine := {b with pc := offset + width * target, work := b.work + 2, natReg := Function.update b.natReg 2 target}
  have hd : execute host b 2 = d := host_natural_jump host b 2 target (offset + width * target) hh h2 (by simpa [b, headerState, Nat.add_assoc] using h3)
  refine ⟨d, ?_, (hbrep.pc_update target).host_clock _ _, rfl, rfl, hh, rfl, rfl, rfl, rfl⟩
  rw [show 4 = 2 + 2 by omega, execute_add, hb, hd]
lemma shadow_halt_macro {base F : ℕ} {c g : Machine} (hr : ShadowRep base F c g)
    (host : Program) (returnPC : ℕ)
    (hh : c.halted = false) (hone : c.natReg 1 = 1)
    (h0 : host.code[c.pc]? = some (.natural 2 (g.pc + 1)))
    (h1 : host.code[c.pc + 1]? = some (.nadd 3 3 1))
    (h2 : host.code[c.pc + 2]? = some (.natural 4 1))
    (h3 : host.code[c.pc + 3]? = some (.jump returnPC)) :
    ∃ d, execute host c 4 = d ∧
      ShadowRep base F d (instructionEffect .halt {g with pc := g.pc + 1, work := g.work + 1}) ∧
      d.pc = returnPC ∧ d.work = c.work + 4 ∧ d.halted = false ∧
      d.natReg 0 = c.natReg 0 ∧ d.natReg 1 = c.natReg 1 ∧
      d.natReg 7 = c.natReg 7 ∧ d.realReg 7 = c.realReg 7 := by
  let b := headerState c g.pc
  have hb : execute host c 2 = b := embedded_header_exact host c g.pc hh hone h0 h1
  have hbrep : ShadowRep base F b {g with pc := g.pc + 1, work := g.work + 1} := by
    rw [← hb]
    exact hr.header host hh hone h0 h1
  let d : Machine := {b with pc := returnPC, work := b.work + 2, natReg := Function.update b.natReg 4 1}
  have hd : execute host b 2 = d := host_natural_jump host b 4 1 returnPC hh h2 (by simpa [b, headerState, Nat.add_assoc] using h3)
  refine ⟨d, ?_, hbrep.halt_update.host_clock _ _, rfl, rfl, hh, rfl, rfl, rfl, rfl⟩
  rw [show 4 = 2 + 2 by omega, execute_add, hb, hd]
end DecrAlmostLinearSSSP.Decremental
end s47
section s48
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
attribute [local instance] Classical.propDecidable
lemma host_shadow_branch {base F : ℕ} {c g : Machine} (hr : ShadowRep base F c g)
    (host : Program) (hF : 0 < F) (natural : Bool) (a b target : ℕ)
    (hh : c.halted = false)
    (hc : host.code[c.pc]? = some (branchInstruction natural (shadowReg a) (shadowReg b) target)) :
    execute host c 1 = {c with
      pc := if branchTest natural g a b then target else c.pc + 1
      work := c.work + 1} := by
  cases natural <;> simp [execute, step, branchInstruction, branchTest, hh, hc, hr.realReg, hr.natReg, scaled_less F _ _ hF]
  all_goals split_ifs <;> rfl
lemma shadow_branch_macro {base F : ℕ} {c g : Machine} (hr : ShadowRep base F c g)
    (host : Program) (width offset target : ℕ) (hF : 0 < F)
    (natural : Bool) (a b : ℕ)
    (hh : c.halted = false) (hone : c.natReg 1 = 1)
    (h0 : host.code[c.pc]? = some (.natural 2 (g.pc + 1)))
    (h1 : host.code[c.pc + 1]? = some (.nadd 3 3 1))
    (h2 : host.code[c.pc + 2]? = some (branchInstruction natural (shadowReg a) (shadowReg b) (c.pc + 5)))
    (h3 : host.code[c.pc + 3]? = some (.jump (offset + width * (g.pc + 1))))
    (h5 : host.code[c.pc + 5]? = some (.natural 2 target))
    (h6 : host.code[c.pc + 6]? = some (.jump (offset + width * target))) :
    ∃ (steps : ℕ) (d : Machine), steps ≤ 5 ∧ execute host c steps = d ∧
      ShadowRep base F d (instructionEffect (branchInstruction natural a b target) {g with pc := g.pc + 1, work := g.work + 1}) ∧
      d.pc = (if branchTest natural g a b then offset + width * target else offset + width * (g.pc + 1)) ∧
      d.work = c.work + steps ∧ d.halted = false ∧
      d.natReg 0 = c.natReg 0 ∧ d.natReg 1 = c.natReg 1 ∧
      d.natReg 7 = c.natReg 7 ∧ d.realReg 7 = c.realReg 7 ∧
      steps = (if branchTest natural g a b then 5 else 4) := by
  classical
  let s := headerState c g.pc
  let g' : Machine := {g with pc := g.pc + 1, work := g.work + 1}
  have hs : execute host c 2 = s := embedded_header_exact host c g.pc hh hone h0 h1
  have hsrep : ShadowRep base F s g' := by
    rw [← hs]
    exact hr.header host hh hone h0 h1
  have heffect : instructionEffect (branchInstruction natural a b target) g' =
      if branchTest natural g a b then {g' with pc := target} else g' := by
    rw [branch_effect]
    cases natural <;> rfl
  by_cases htake : branchTest natural g a b
  · let t : Machine := {s with pc := c.pc + 5, work := s.work + 1}
    have ht : execute host s 1 = t := by
      rw [host_shadow_branch hsrep host hF natural a b (c.pc + 5) hh h2]
      have he : branchTest natural g' a b = branchTest natural g a b := by cases natural <;> rfl
      rw [he, if_pos htake]
    let d : Machine := {t with pc := offset + width * target, work := t.work + 2, natReg := Function.update t.natReg 2 target}
    have hd : execute host t 2 = d := host_natural_jump host t 2 target (offset + width * target) hh h5 (by simpa [t, Nat.add_assoc] using h6)
    refine ⟨5, d, le_rfl, ?_, ?_, by simp only [if_pos htake]; rfl, rfl, hh, rfl, rfl, rfl, rfl, by simp only [if_pos htake]⟩
    · rw [show 5 = 2 + (1 + 2) by omega, execute_add, hs, execute_add, ht, hd]
    · rw [show instructionEffect (branchInstruction natural a b target) {g with pc := g.pc + 1, work := g.work + 1} = {g' with pc := target} from heffect.trans (if_pos htake)]
      have htrep : ShadowRep base F t g' := hsrep.host_clock _ _
      exact (htrep.pc_update target).host_clock _ _
  · let t : Machine := {s with pc := c.pc + 3, work := s.work + 1}
    have ht : execute host s 1 = t := by
      rw [host_shadow_branch hsrep host hF natural a b (c.pc + 5) hh h2]
      have he : branchTest natural g' a b = branchTest natural g a b := by cases natural <;> rfl
      rw [he, if_neg htake]
      simp [t, s, headerState, Nat.add_assoc]
    let d : Machine := {t with pc := offset + width * (g.pc + 1), work := t.work + 1}
    have hd : execute host t 1 = d := host_jump host t (offset + width * (g.pc + 1)) hh h3
    refine ⟨4, d, by omega, ?_, ?_, by simp only [if_neg htake]; rfl, rfl, hh, rfl, rfl, rfl, rfl, by simp only [if_neg htake]⟩
    · rw [show 4 = 2 + (1 + 1) by omega, execute_add, hs, execute_add, ht, hd]
    · rw [show instructionEffect (branchInstruction natural a b target) {g with pc := g.pc + 1, work := g.work + 1} = g' from heffect.trans (if_neg htake)]
      exact hsrep.host_clock _ _
end DecrAlmostLinearSSSP.Decremental
end s48
section s49
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma shadow_natural_macro {base F : ℕ} {c g : Machine} (hr : ShadowRep base F c g)
    (host : Program) (width offset d q : ℕ)
    (hh : c.halted = false) (hone : c.natReg 1 = 1) (hfactor : c.natReg 7 = F)
    (h0 : host.code[c.pc]? = some (.natural 2 (g.pc + 1)))
    (h1 : host.code[c.pc + 1]? = some (.nadd 3 3 1))
    (h2 : host.code[c.pc + 2]? = some (.natural (shadowReg d) 0))
    (hadds : ∀ j < q, host.code[c.pc + 3 + j]? = some (.nadd (shadowReg d) (shadowReg d) 7))
    (hjump : host.code[c.pc + (q + 3)]? = some (.jump (offset + width * (g.pc + 1)))) :
    ∃ finish, execute host c (q + 4) = finish ∧
      ShadowRep base F finish (instructionEffect (.natural d q) {g with pc := g.pc + 1, work := g.work + 1}) ∧
      finish.pc = offset + width * (g.pc + 1) ∧ finish.work = c.work + (q + 4) ∧ finish.halted = false ∧
      finish.natReg 0 = c.natReg 0 ∧ finish.natReg 1 = c.natReg 1 ∧
      finish.natReg 7 = c.natReg 7 ∧ finish.realReg 7 = c.realReg 7 := by
  classical
  let b := headerState c g.pc
  have hb : execute host c 2 = b := embedded_header_exact host c g.pc hh hone h0 h1
  have hbrep : ShadowRep base F b {g with pc := g.pc + 1, work := g.work + 1} := by
    rw [← hb]
    exact hr.header host hh hone h0 h1
  let t : Machine := {b with pc := b.pc + (q + 1), work := b.work + (q + 1), natReg := Function.update b.natReg (shadowReg d) (q * F)}
  have ht : execute host b (q + 1) = t := by
    rw [constant_product_run host b (shadowReg d) 7 q (shadowReg_ne_meta d 7 (by omega)).symm hh h2
      (fun j hj => by simpa [b, headerState, Nat.add_assoc] using hadds j hj)]
    rw [show b.natReg 7 = F from hfactor]
  have htrep : ShadowRep base F t (instructionEffect (.natural d q) {g with pc := g.pc + 1, work := g.work + 1}) := by
    rw [← ht]
    exact hbrep.constant_run host d q hfactor hh h2
      (fun j hj => by simpa [b, headerState, Nat.add_assoc] using hadds j hj)
  have hth : t.halted = false := hh
  have hjc : host.code[t.pc]? = some (.jump (offset + width * (g.pc + 1))) := by
    simpa [t, b, headerState, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hjump
  let finish : Machine := {t with pc := offset + width * (g.pc + 1), work := t.work + 1}
  have hlast := host_jump host t (offset + width * (g.pc + 1)) hth hjc
  refine ⟨finish, ?_, htrep.host_clock _ _, rfl, ?_, hth, ?_, ?_, ?_, rfl⟩
  · rw [show q + 4 = 2 + ((q + 1) + 1) by omega, execute_add, hb, execute_add, ht]
    exact hlast
  · change c.work + 2 + (q + 1) + 1 = c.work + (q + 4)
    omega
  · change Function.update b.natReg (shadowReg d) (q * F) 0 = c.natReg 0
    rw [Function.update_of_ne (shadowReg_ne_meta d 0 (by omega)).symm]
    rfl
  · change Function.update b.natReg (shadowReg d) (q * F) 1 = c.natReg 1
    rw [Function.update_of_ne (shadowReg_ne_meta d 1 (by omega)).symm]
    rfl
  · change Function.update b.natReg (shadowReg d) (q * F) 7 = c.natReg 7
    rw [Function.update_of_ne (shadowReg_ne_meta d 7 (by omega)).symm]
    rfl
lemma shadow_cast_run {base F : ℕ} {c g : Machine} (hr : ShadowRep base F c g)
    (host : Program) (hF : 0 < F) (d a : ℕ) (hh : c.halted = false)
    (hfactor : c.realReg 7 = (F : ℝ))
    (h0 : host.code[c.pc]? = some (.cast (shadowReg d) (shadowReg a)))
    (h1 : host.code[c.pc + 1]? = some (.div (shadowReg d) (shadowReg d) 7)) :
    ∃ finish, execute host c 2 = finish ∧ ShadowRep base F finish (instructionEffect (.cast d a) g) ∧
      finish.pc = c.pc + 2 ∧ finish.work = c.work + 2 ∧ finish.halted = false ∧
      finish.natReg = c.natReg ∧ finish.realReg 7 = c.realReg 7 := by
  classical
  let b := instructionEffect (.cast (shadowReg d) (shadowReg a)) c
  let t := instructionEffect (.div (shadowReg d) (shadowReg d) 7) b
  let finish : Machine := {t with pc := c.pc + 2, work := c.work + 2}
  have hs1 : step host c = {b with pc := c.pc + 1, work := c.work + 1} := by simp [step, hh, h0, b, instructionEffect]
  have hs2 : step host {b with pc := c.pc + 1, work := c.work + 1} = finish := by
    simp [step, b, t, finish, instructionEffect, hh, h1]
  have hrep := (shadow_cast hr hF d a hfactor).host_clock (c.pc + 2) (c.work + 2)
  refine ⟨finish, ?_, hrep, rfl, rfl, hh, rfl, ?_⟩
  · change step host (step host c) = finish
    rw [hs1, hs2]
  · have hne : (7 : ℕ) ≠ shadowReg d := (shadowReg_ne_meta d 7 (by omega)).symm
    simp only [finish, t, b, instructionEffect, Function.update_of_ne hne]
lemma shadow_cast_macro {base F : ℕ} {c g : Machine} (hr : ShadowRep base F c g)
    (host : Program) (width offset : ℕ) (hF : 0 < F) (d a : ℕ)
    (hh : c.halted = false) (hone : c.natReg 1 = 1) (hfactor : c.realReg 7 = (F : ℝ))
    (h0 : host.code[c.pc]? = some (.natural 2 (g.pc + 1)))
    (h1 : host.code[c.pc + 1]? = some (.nadd 3 3 1))
    (h2 : host.code[c.pc + 2]? = some (.cast (shadowReg d) (shadowReg a)))
    (h3 : host.code[c.pc + 3]? = some (.div (shadowReg d) (shadowReg d) 7))
    (h4 : host.code[c.pc + 4]? = some (.jump (offset + width * (g.pc + 1)))) :
    ∃ finish, execute host c 5 = finish ∧
      ShadowRep base F finish (instructionEffect (.cast d a) {g with pc := g.pc + 1, work := g.work + 1}) ∧
      finish.pc = offset + width * (g.pc + 1) ∧ finish.work = c.work + 5 ∧ finish.halted = false ∧
      finish.natReg 0 = c.natReg 0 ∧ finish.natReg 1 = c.natReg 1 ∧
      finish.natReg 7 = c.natReg 7 ∧ finish.realReg 7 = c.realReg 7 := by
  let b := headerState c g.pc
  have hb : execute host c 2 = b := embedded_header_exact host c g.pc hh hone h0 h1
  have hbrep : ShadowRep base F b {g with pc := g.pc + 1, work := g.work + 1} := by
    rw [← hb]
    exact hr.header host hh hone h0 h1
  obtain ⟨t, ht, htrep, htpc, htw, hth, htnat, htr7⟩ :=
    shadow_cast_run hbrep host hF d a hh hfactor h2 (by simpa [b, headerState, Nat.add_assoc] using h3)
  have hjc : host.code[t.pc]? = some (.jump (offset + width * (g.pc + 1))) := by
    rw [htpc]
    simpa [b, headerState, Nat.add_assoc] using h4
  have hj := host_jump host t (offset + width * (g.pc + 1)) hth hjc
  let finish : Machine := {t with pc := offset + width * (g.pc + 1), work := t.work + 1}
  refine ⟨finish, ?_, htrep.host_clock _ _, rfl, ?_, hth, ?_, ?_, ?_, htr7⟩
  · rw [show 5 = 2 + (2 + 1) by omega, execute_add, hb, execute_add, ht]
    exact hj
  · change t.work + 1 = c.work + 5
    rw [htw]
    rfl
  · change t.natReg 0 = c.natReg 0
    rw [htnat]
    rfl
  · change t.natReg 1 = c.natReg 1
    rw [htnat]
    rfl
  · change t.natReg 7 = c.natReg 7
    rw [htnat]
    rfl
end DecrAlmostLinearSSSP.Decremental
end s49
section s50
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma shadow_address_run {base F : ℕ} {c g : Machine} (hr : ShadowRep base F c g)
    (host : Program) (a : ℕ) (hh : c.halted = false)
    (hbase : c.natReg 0 = base) (hfactor : c.natReg 7 = F)
    (h0 : host.code[c.pc]? = some (.nadd 6 (shadowReg a) (shadowReg a)))
    (h1 : host.code[c.pc + 1]? = some (.nadd 6 6 0))
    (h2 : host.code[c.pc + 2]? = some (.nadd 6 6 7)) :
    ∃ d, execute host c 3 = d ∧ ShadowRep base F d g ∧
      d.natReg 6 = base + F * (2 * g.natReg a + 1) ∧
      d.pc = c.pc + 3 ∧ d.work = c.work + 3 ∧ d.halted = false ∧
      d.natReg 0 = c.natReg 0 ∧ d.natReg 1 = c.natReg 1 ∧
      d.natReg 7 = c.natReg 7 ∧ d.realReg 7 = c.realReg 7 := by
  classical
  let c1 : Machine := {c with pc := c.pc + 1, work := c.work + 1, natReg := Function.update c.natReg 6 (c.natReg (shadowReg a) + c.natReg (shadowReg a))}
  let c2 : Machine := {c1 with pc := c.pc + 2, work := c.work + 2, natReg := Function.update c1.natReg 6 (c1.natReg 6 + c1.natReg 0)}
  let c3 : Machine := {c2 with pc := c.pc + 3, work := c.work + 3, natReg := Function.update c2.natReg 6 (c2.natReg 6 + c2.natReg 7)}
  have hs1 : step host c = c1 := by simp [step, c1, hh, h0]
  have hs2 : step host c1 = c2 := by simp [step, c1, c2, hh, h1]
  have hs3 : step host c2 = c3 := by simp [step, c1, c2, c3, hh, h2]
  have hr1 : ShadowRep base F c1 g := (hr.scratch _).host_clock _ _
  have hr2 : ShadowRep base F c2 g := (hr1.scratch _).host_clock _ _
  have hr3 : ShadowRep base F c3 g := (hr2.scratch _).host_clock _ _
  refine ⟨c3, ?_, hr3, ?_, rfl, rfl, hh, rfl, rfl, rfl, rfl⟩
  · change step host (step host (step host c)) = c3
    rw [hs1, hs2, hs3]
  · simp only [c3, c2, c1, Function.update_self, Function.update_of_ne (by omega : (0 : ℕ) ≠ 6),
      Function.update_of_ne (by omega : (7 : ℕ) ≠ 6), hbase, hfactor, hr.natReg]
    ring
end DecrAlmostLinearSSSP.Decremental
end s50
section s51
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma shadowMemory_reserved (ins tr : Instruction) (a : ℕ)
    (ht : shadowMemoryTranslation ins = some (tr,a)) : ReservedSafe tr := by
  cases ins <;> simp only [shadowMemoryTranslation] at ht
  all_goals cases ht
  all_goals simp [ReservedSafe, writesNat, writesReal, shadowReg] <;> omega
lemma host_shadow_memory {base F : ℕ} {c g : Machine} (hr : ShadowRep base F c g)
    (host : Program) (hF : 0 < F) (ins tr : Instruction) (a : ℕ)
    (ht : shadowMemoryTranslation ins = some (tr,a))
    (ha : c.natReg 6 = base + F * (2 * g.natReg a + 1))
    (hh : c.halted = false) (hc : host.code[c.pc]? = some tr) :
    ShadowRep base F (execute host c 1) (instructionEffect ins g) ∧
      (execute host c 1).pc = c.pc + 1 ∧ (execute host c 1).work = c.work + 1 ∧
      (execute host c 1).halted = false ∧
      (execute host c 1).natReg 0 = c.natReg 0 ∧ (execute host c 1).natReg 1 = c.natReg 1 ∧
      (execute host c 1).natReg 7 = c.natReg 7 ∧ (execute host c 1).realReg 7 = c.realReg 7 := by
  have hs := shadowMemory_reserved ins tr a ht
  have hrep : ShadowRep base F (execute host c 1) (instructionEffect ins g) := by
    change ShadowRep base F (step host c) _
    rw [step_eq_effect host c tr hh hc]
    have hr' := hr.host_clock (c.pc + 1) (c.work + 1)
    cases ins <;> simp only [shadowMemoryTranslation] at ht
    all_goals cases ht
    · exact shadow_load hr' _ _ ha
    · exact shadow_store hr' hF _ _ ha
    · exact shadow_loadN hr' _ _ ha
    · exact shadow_storeN hr' hF _ _ ha
  refine ⟨hrep, ?_, ?_, ?_,
    step_nat_frame host c tr 0 hh hc hs.1,
    step_nat_frame host c tr 1 hh hc hs.2.1,
    step_nat_frame host c tr 7 hh hc hs.2.2.1,
    step_real_frame host c tr 7 hh hc hs.2.2.2⟩
  all_goals cases ins <;> simp only [shadowMemoryTranslation] at ht
  all_goals cases ht
  all_goals simp only [execute, Function.iterate_one, step, hh, Bool.false_eq_true, if_false, hc]
lemma shadow_memory_macro {base F : ℕ} {c g : Machine} (hr : ShadowRep base F c g)
    (host : Program) (width offset : ℕ) (hF : 0 < F) (ins tr : Instruction) (a : ℕ)
    (ht : shadowMemoryTranslation ins = some (tr,a))
    (hh : c.halted = false) (hone : c.natReg 1 = 1)
    (hbase : c.natReg 0 = base) (hfactor : c.natReg 7 = F)
    (h0 : host.code[c.pc]? = some (.natural 2 (g.pc + 1)))
    (h1 : host.code[c.pc + 1]? = some (.nadd 3 3 1))
    (h2 : host.code[c.pc + 2]? = some (.nadd 6 (shadowReg a) (shadowReg a)))
    (h3 : host.code[c.pc + 3]? = some (.nadd 6 6 0))
    (h4 : host.code[c.pc + 4]? = some (.nadd 6 6 7))
    (h5 : host.code[c.pc + 5]? = some tr)
    (h6 : host.code[c.pc + 6]? = some (.jump (offset + width * (g.pc + 1)))) :
    ∃ d, execute host c 7 = d ∧
      ShadowRep base F d (instructionEffect ins {g with pc := g.pc + 1, work := g.work + 1}) ∧
      d.pc = offset + width * (g.pc + 1) ∧ d.work = c.work + 7 ∧ d.halted = false ∧
      d.natReg 0 = c.natReg 0 ∧ d.natReg 1 = c.natReg 1 ∧
      d.natReg 7 = c.natReg 7 ∧ d.realReg 7 = c.realReg 7 := by
  let b := headerState c g.pc
  have hb : execute host c 2 = b := embedded_header_exact host c g.pc hh hone h0 h1
  have hbrep : ShadowRep base F b {g with pc := g.pc + 1, work := g.work + 1} := by
    rw [← hb]
    exact hr.header host hh hone h0 h1
  obtain ⟨t, htRun, htrep, hta, htpc, htw, hth, ht0, ht1, ht7, htr7⟩ :=
    shadow_address_run hbrep host a hh hbase hfactor h2
      (by simpa [b, headerState, Nat.add_assoc] using h3)
      (by simpa [b, headerState, Nat.add_assoc] using h4)
  have htc : host.code[t.pc]? = some tr := by rw [htpc]; simpa [b, headerState, Nat.add_assoc] using h5
  obtain ⟨hrep, hpc, hw, hhalt, hm0, hm1, hm7, hreal7⟩ := host_shadow_memory htrep host hF ins tr a ht hta hth htc
  let u := execute host t 1
  have hjc : host.code[u.pc]? = some (.jump (offset + width * (g.pc + 1))) := by
    change host.code[(execute host t 1).pc]? = _
    rw [hpc, htpc]
    simpa [b, headerState, Nat.add_assoc] using h6
  have hj := host_jump host u (offset + width * (g.pc + 1)) hhalt hjc
  let d : Machine := {u with pc := offset + width * (g.pc + 1), work := u.work + 1}
  refine ⟨d, ?_, hrep.host_clock _ _, rfl, ?_, hhalt, hm0.trans ht0, hm1.trans ht1, hm7.trans ht7, hreal7.trans htr7⟩
  · rw [show 7 = 2 + (3 + (1 + 1)) by omega, execute_add, hb, execute_add, htRun, execute_add]
    exact hj
  · change (execute host t 1).work + 1 = c.work + 7
    rw [hw, htw]
    rfl
end DecrAlmostLinearSSSP.Decremental
end s51
section s52
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma shadowCodeAux_get (width offset returnPC start : ℕ) (code : List Instruction)
    (hw : 8 ≤ width) (hc : ∀ ins ∈ code, naturalConstant ins + 4 ≤ width)
    (pc slot : ℕ) (ins : Instruction) (hslot : slot < width) (hins : code[pc]? = some ins) :
    (shadowCodeAux width offset returnPC start code)[width * pc + slot]? =
      (shadowBlock width offset returnPC (start + pc) ins)[slot]? := by
  induction code generalizing start pc with
  | nil => simp at hins
  | cons first rest ih =>
    have hfirst : (shadowBlock width offset returnPC start first).length = width :=
      shadowBlock_length _ _ _ _ _ hw (hc first List.mem_cons_self)
    cases pc with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hins
      subst ins
      simp only [shadowCodeAux, Nat.mul_zero, Nat.zero_add, Nat.add_zero]
      rw [List.getElem?_append_left (by rwa [hfirst])]
    | succ pc =>
      simp only [List.getElem?_cons_succ] at hins
      rw [shadowCodeAux, List.getElem?_append_right (by rw [hfirst, Nat.mul_succ]; omega)]
      have hidx : width * (pc + 1) + slot - width = width * pc + slot := by rw [Nat.mul_succ]; omega
      rw [hfirst, hidx]
      have hh := ih (start + 1) (fun tr htr => hc tr (List.mem_cons_of_mem first htr)) pc hins
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
lemma shadowCode_get (offset returnPC : ℕ) (code : List Instruction)
    (pc slot : ℕ) (ins : Instruction) (hslot : slot < shadowWidth code) (hins : code[pc]? = some ins) :
    (shadowCode offset returnPC code)[shadowWidth code * pc + slot]? =
      (shadowBlock (shadowWidth code) offset returnPC pc ins)[slot]? := by
  simpa only [shadowCode, Nat.zero_add] using
    shadowCodeAux_get (shadowWidth code) offset returnPC 0 code (shadowWidth_positive code)
      (source_constant_bound code) pc slot ins hslot hins
end DecrAlmostLinearSSSP.Decremental
end s52
section s53
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma shadowBlock_header (width offset returnPC pc : ℕ) (ins : Instruction) :
    (shadowBlock width offset returnPC pc ins)[0]? = some (.natural 2 (pc + 1)) ∧
    (shadowBlock width offset returnPC pc ins)[1]? = some (.nadd 3 3 1) := by
  cases ins <;> exact ⟨rfl,rfl⟩
lemma shadowBlock_natural_add (width offset returnPC pc d q j : ℕ) (hj : j < q) :
    (shadowBlock width offset returnPC pc (.natural d q))[3 + j]? =
      some (.nadd (shadowReg d) (shadowReg d) 7) := by
  simp only [shadowBlock, constantProductCode, List.cons_append, List.nil_append, List.append_assoc]
  have heq : 3 + j = j + 1 + 1 + 1 := by omega
  rw [heq]
  simp only [List.getElem?_cons_succ]
  rw [List.getElem?_append_left (by simpa only [List.length_replicate] using hj)]
  simp only [List.getElem?_replicate, if_pos hj]
lemma shadowBlock_natural_jump (width offset returnPC pc d q : ℕ) :
    (shadowBlock width offset returnPC pc (.natural d q))[q + 3]? =
      some (.jump (offset + width * (pc + 1))) := by
  simp only [shadowBlock, constantProductCode, List.cons_append, List.nil_append, List.append_assoc]
  have heq : q + 3 = q + 1 + 1 + 1 := by omega
  rw [heq]
  simp only [List.getElem?_cons_succ]
  rw [List.getElem?_append_right (by simp only [List.length_replicate]; omega)]
  simp
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
lemma shadowScalar_control (ins tr : Instruction) (ht : shadowScalarTranslation ins = some tr)
    (g : Machine) : (instructionEffect ins g).pc = g.pc ∧ (instructionEffect ins g).halted = g.halted := by
  cases ins <;> simp only [shadowScalarTranslation] at ht
  all_goals cases ht
  all_goals exact ⟨rfl,rfl⟩
lemma shadowMemory_control (ins tr : Instruction) (a : ℕ) (ht : shadowMemoryTranslation ins = some (tr,a))
    (g : Machine) : (instructionEffect ins g).pc = g.pc ∧ (instructionEffect ins g).halted = g.halted := by
  cases ins <;> simp only [shadowMemoryTranslation] at ht
  all_goals cases ht
  all_goals exact ⟨rfl,rfl⟩
lemma shadow_macro {base F : ℕ} {c g : Machine} (hr : ShadowRep base F c g)
    (host : Program) (width offset returnPC : ℕ) (hwidth : 8 ≤ width)
    (hF : 0 < F) (ins : Instruction) (hconst : naturalConstant ins + 4 ≤ width)
    (hh : c.halted = false) (hone : c.natReg 1 = 1) (hgh : g.halted = false)
    (hbase : c.natReg 0 = base) (hfactor : c.natReg 7 = F) (hrealFactor : c.realReg 7 = (F : ℝ))
    (hpos : c.pc = offset + width * g.pc)
    (hcode : ∀ slot < width, host.code[c.pc + slot]? = (shadowBlock width offset returnPC g.pc ins)[slot]?) :
    ∃ (steps : ℕ) (d : Machine), steps ≤ width ∧ execute host c steps = d ∧
      ShadowRep base F d (instructionEffect ins {g with pc := g.pc + 1, work := g.work + 1}) ∧
      d.pc = shadowDestination width offset returnPC (instructionEffect ins {g with pc := g.pc + 1, work := g.work + 1}) ∧
      d.work = c.work + steps ∧ d.halted = false ∧
      d.natReg 0 = c.natReg 0 ∧ d.natReg 1 = c.natReg 1 ∧
      d.natReg 7 = c.natReg 7 ∧ d.realReg 7 = c.realReg 7 ∧ steps = shadowSteps ins g := by
  classical
  have h0 : host.code[c.pc]? = some (.natural 2 (g.pc + 1)) := by
    simpa only [Nat.add_zero] using (hcode 0 (by omega)).trans (shadowBlock_header width offset returnPC g.pc ins).1
  have h1 : host.code[c.pc + 1]? = some (.nadd 3 3 1) :=
    (hcode 1 (by omega)).trans (shadowBlock_header width offset returnPC g.pc ins).2
  let g' : Machine := {g with pc := g.pc + 1, work := g.work + 1}
  by_cases hscalar : ∃ tr, shadowScalarTranslation ins = some tr
  · obtain ⟨tr,ht⟩ := hscalar
    have h2 : host.code[c.pc + 2]? = some tr := by
      rw [hcode 2 (by omega)]
      cases ins <;> simp only [shadowScalarTranslation] at ht
      all_goals cases ht
      all_goals rfl
    have h3 : host.code[c.pc + 3]? = some (.jump (offset + width * (g.pc + 1))) := by
      rw [hcode 3 (by omega)]
      cases ins <;> simp only [shadowScalarTranslation] at ht
      all_goals cases ht
      all_goals rfl
    obtain ⟨d,hd,hrep,hpc,hw,hhalt,hm0,hm1,hm7,hr7⟩ := shadow_simple_macro hr host width offset ins tr ht hh hone h0 h1 h2 h3
    refine ⟨4,d,by omega,hd,hrep,?_,hw,hhalt,hm0,hm1,hm7,hr7,?count⟩
    case count =>
      cases ins <;> simp only [shadowScalarTranslation] at ht
      all_goals cases ht
      all_goals rfl
    rw [hpc]
    change offset + width * (g.pc + 1) = shadowDestination width offset returnPC (instructionEffect ins g')
    have hctrl := shadowScalar_control ins tr ht g'
    simp only [shadowDestination,hctrl.1,hctrl.2]
    simp [g',hgh]
  · by_cases hmemory : ∃ tr a, shadowMemoryTranslation ins = some (tr,a)
    · obtain ⟨tr,a,ht⟩ := hmemory
      have h2 : host.code[c.pc + 2]? = some (.nadd 6 (shadowReg a) (shadowReg a)) := by
        rw [hcode 2 (by omega)]
        cases ins <;> simp only [shadowMemoryTranslation] at ht
        all_goals cases ht
        all_goals rfl
      have h3 : host.code[c.pc + 3]? = some (.nadd 6 6 0) := by
        rw [hcode 3 (by omega)]
        cases ins <;> simp only [shadowMemoryTranslation] at ht
        all_goals cases ht
        all_goals rfl
      have h4 : host.code[c.pc + 4]? = some (.nadd 6 6 7) := by
        rw [hcode 4 (by omega)]
        cases ins <;> simp only [shadowMemoryTranslation] at ht
        all_goals cases ht
        all_goals rfl
      have h5 : host.code[c.pc + 5]? = some tr := by
        rw [hcode 5 (by omega)]
        cases ins <;> simp only [shadowMemoryTranslation] at ht
        all_goals cases ht
        all_goals rfl
      have h6 : host.code[c.pc + 6]? = some (.jump (offset + width * (g.pc + 1))) := by
        rw [hcode 6 (by omega)]
        cases ins <;> simp only [shadowMemoryTranslation] at ht
        all_goals cases ht
        all_goals rfl
      obtain ⟨d,hd,hrep,hpc,hw,hhalt,hm0,hm1,hm7,hr7⟩ := shadow_memory_macro hr host width offset hF ins tr a ht hh hone hbase hfactor h0 h1 h2 h3 h4 h5 h6
      refine ⟨7,d,by omega,hd,hrep,?_,hw,hhalt,hm0,hm1,hm7,hr7,?count⟩
      case count =>
        cases ins <;> simp only [shadowMemoryTranslation] at ht
        all_goals cases ht
        all_goals rfl
      rw [hpc]
      change offset + width * (g.pc + 1) = shadowDestination width offset returnPC (instructionEffect ins g')
      have hctrl := shadowMemory_control ins tr a ht g'
      simp only [shadowDestination,hctrl.1,hctrl.2]
      simp [g',hgh]
    · cases ins with
      | natural d q =>
        change q + 4 ≤ width at hconst
        have h2 : host.code[c.pc + 2]? = some (.natural (shadowReg d) 0) := by simpa [shadowBlock,constantProductCode] using hcode 2 (by omega)
        have hadds : ∀ j < q, host.code[c.pc + 3 + j]? = some (.nadd (shadowReg d) (shadowReg d) 7) := by
          intro j hj
          rw [show c.pc + 3 + j = c.pc + (3 + j) by omega,hcode (3+j) (by omega)]
          exact shadowBlock_natural_add width offset returnPC g.pc d q j hj
        have hjump : host.code[c.pc + (q+3)]? = some (.jump (offset + width * (g.pc + 1))) := by
          rw [hcode (q+3) (by omega)]
          exact shadowBlock_natural_jump width offset returnPC g.pc d q
        obtain ⟨finish,hd,hrep,hpc,hw,hhalt,hm0,hm1,hm7,hr7⟩ := shadow_natural_macro hr host width offset d q hh hone hfactor h0 h1 h2 hadds hjump
        refine ⟨q+4,finish,hconst,hd,hrep,?_,hw,hhalt,hm0,hm1,hm7,hr7,?count⟩
        case count => rfl
        rw [hpc]
        simp [shadowDestination,instructionEffect,hgh]
      | cast d a =>
        have h2 : host.code[c.pc + 2]? = some (.cast (shadowReg d) (shadowReg a)) := by simpa [shadowBlock] using hcode 2 (by omega)
        have h3 : host.code[c.pc + 3]? = some (.div (shadowReg d) (shadowReg d) 7) := by simpa [shadowBlock] using hcode 3 (by omega)
        have h4 : host.code[c.pc + 4]? = some (.jump (offset + width * (g.pc + 1))) := by simpa [shadowBlock] using hcode 4 (by omega)
        obtain ⟨finish,hd,hrep,hpc,hw,hhalt,hm0,hm1,hm7,hr7⟩ := shadow_cast_macro hr host width offset hF d a hh hone hrealFactor h0 h1 h2 h3 h4
        refine ⟨5,finish,by omega,hd,hrep,?_,hw,hhalt,hm0,hm1,hm7,hr7,?count⟩
        case count => rfl
        rw [hpc]
        simp [shadowDestination,instructionEffect,hgh]
      | jump target =>
        have h2 : host.code[c.pc + 2]? = some (.natural 2 target) := by simpa [shadowBlock] using hcode 2 (by omega)
        have h3 : host.code[c.pc + 3]? = some (.jump (offset + width * target)) := by simpa [shadowBlock] using hcode 3 (by omega)
        obtain ⟨d,hd,hrep,hpc,hw,hhalt,hm0,hm1,hm7,hr7⟩ := shadow_jump_macro hr host width offset target hh hone h0 h1 h2 h3
        refine ⟨4,d,by omega,hd,hrep,?_,hw,hhalt,hm0,hm1,hm7,hr7,?count⟩
        case count => rfl
        rw [hpc]
        simp [shadowDestination,instructionEffect,hgh]
      | halt =>
        have h2 : host.code[c.pc + 2]? = some (.natural 4 1) := by simpa [shadowBlock] using hcode 2 (by omega)
        have h3 : host.code[c.pc + 3]? = some (.jump returnPC) := by simpa [shadowBlock] using hcode 3 (by omega)
        obtain ⟨d,hd,hrep,hpc,hw,hhalt,hm0,hm1,hm7,hr7⟩ := shadow_halt_macro hr host returnPC hh hone h0 h1 h2 h3
        refine ⟨4,d,by omega,hd,hrep,?_,hw,hhalt,hm0,hm1,hm7,hr7,?count⟩
        case count => rfl
        rw [hpc]
        simp [shadowDestination,instructionEffect]
      | less a b target =>
        have h2 : host.code[c.pc + 2]? = some (branchInstruction false (shadowReg a) (shadowReg b) (c.pc + 5)) := by
          simpa [shadowBlock,branchInstruction,hpos] using hcode 2 (by omega)
        have h3 : host.code[c.pc + 3]? = some (.jump (offset + width * (g.pc + 1))) := by simpa [shadowBlock] using hcode 3 (by omega)
        have h5 : host.code[c.pc + 5]? = some (.natural 2 target) := by simpa [shadowBlock] using hcode 5 (by omega)
        have h6 : host.code[c.pc + 6]? = some (.jump (offset + width * target)) := by simpa [shadowBlock] using hcode 6 (by omega)
        obtain ⟨t,d,ht,hd,hrep,hpc,hw,hhalt,hm0,hm1,hm7,hr7,htsteps⟩ := shadow_branch_macro hr host width offset target hF false a b hh hone h0 h1 h2 h3 h5 h6
        refine ⟨t,d,by omega,hd,hrep,?_,hw,hhalt,hm0,hm1,hm7,hr7,?count⟩
        case count => simpa [shadowSteps,branchTest] using htsteps
        rw [hpc]
        change _ = shadowDestination width offset returnPC (instructionEffect (branchInstruction false a b target) g')
        rw [branch_effect]
        have he : branchTest false g' a b = branchTest false g a b := rfl
        rw [he]
        split_ifs <;> simp [shadowDestination,g',hgh]
      | lessN a b target =>
        have h2 : host.code[c.pc + 2]? = some (branchInstruction true (shadowReg a) (shadowReg b) (c.pc + 5)) := by
          simpa [shadowBlock,branchInstruction,hpos] using hcode 2 (by omega)
        have h3 : host.code[c.pc + 3]? = some (.jump (offset + width * (g.pc + 1))) := by simpa [shadowBlock] using hcode 3 (by omega)
        have h5 : host.code[c.pc + 5]? = some (.natural 2 target) := by simpa [shadowBlock] using hcode 5 (by omega)
        have h6 : host.code[c.pc + 6]? = some (.jump (offset + width * target)) := by simpa [shadowBlock] using hcode 6 (by omega)
        obtain ⟨t,d,ht,hd,hrep,hpc,hw,hhalt,hm0,hm1,hm7,hr7,htsteps⟩ := shadow_branch_macro hr host width offset target hF true a b hh hone h0 h1 h2 h3 h5 h6
        refine ⟨t,d,by omega,hd,hrep,?_,hw,hhalt,hm0,hm1,hm7,hr7,?count⟩
        case count => simpa [shadowSteps,branchTest] using htsteps
        rw [hpc]
        change _ = shadowDestination width offset returnPC (instructionEffect (branchInstruction true a b target) g')
        rw [branch_effect]
        have he : branchTest true g' a b = branchTest true g a b := rfl
        rw [he]
        split_ifs <;> simp [shadowDestination,g',hgh]
      | _ => simp_all [shadowScalarTranslation,shadowMemoryTranslation]
end DecrAlmostLinearSSSP.Decremental
end s55
section s56
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma shadow_single_step {base F : ℕ} {c g : Machine} (hr : ShadowRep base F c g)
    (host guest : Program) (width offset returnPC : ℕ) (hw : 8 ≤ width)
    (hc : ∀ ins ∈ guest.code, naturalConstant ins + 4 ≤ width)
    (hcode : ShadowEmbedsCode host guest width offset returnPC) (hF : 0 < F)
    (hh : c.halted = false) (hone : c.natReg 1 = 1) (hgh : g.halted = false)
    (hbase : c.natReg 0 = base) (hfactor : c.natReg 7 = F) (hrealFactor : c.realReg 7 = (F : ℝ))
    (hpos : c.pc = shadowDestination width offset returnPC g)
    (ins : Instruction) (hins : guest.code[g.pc]? = some ins) :
    ∃ (steps : ℕ) (d : Machine), steps ≤ width ∧ execute host c steps = d ∧
      ShadowRep base F d (step guest g) ∧ d.pc = shadowDestination width offset returnPC (step guest g) ∧
      d.work = c.work + steps ∧ d.halted = false ∧
      d.natReg 0 = c.natReg 0 ∧ d.natReg 1 = c.natReg 1 ∧
      d.natReg 7 = c.natReg 7 ∧ d.realReg 7 = c.realReg 7 := by
  have hp : c.pc = offset + width * g.pc := by simpa [shadowDestination,hgh] using hpos
  have hconst := hc ins (List.mem_of_getElem? hins)
  obtain ⟨steps,d,hs,hd,hrep,hdpc,hdw,hdh,hd0,hd1,hd7,hdr7,_hsteps⟩ :=
    shadow_macro hr host width offset returnPC hw hF ins hconst hh hone hgh hbase hfactor hrealFactor hp
      (fun slot hslot => by rw [hp]; exact hcode _ _ hins slot hslot)
  rw [← step_eq_effect guest g ins hgh hins] at hrep hdpc
  exact ⟨steps,d,hs,hd,hrep,hdpc,hdw,hdh,hd0,hd1,hd7,hdr7⟩
lemma shadow_execution (host guest : Program) (width offset returnPC : ℕ)
    (hw : 8 ≤ width) (hc : ∀ ins ∈ guest.code, naturalConstant ins + 4 ≤ width)
    (hcode : ShadowEmbedsCode host guest width offset returnPC)
    (base F : ℕ) (hF : 0 < F) (t : ℕ) (c g : Machine) (hr : ShadowRep base F c g)
    (hh : c.halted = false) (hone : c.natReg 1 = 1)
    (hbase : c.natReg 0 = base) (hfactor : c.natReg 7 = F) (hrealFactor : c.realReg 7 = (F : ℝ))
    (hpos : c.pc = shadowDestination width offset returnPC g)
    (hvalid : ∀ j < t, (execute guest g j).halted = false → ∃ ins, guest.code[(execute guest g j).pc]? = some ins) :
    ∃ (steps : ℕ) (d : Machine), steps ≤ width * t ∧ execute host c steps = d ∧
      ShadowRep base F d (execute guest g t) ∧ d.pc = shadowDestination width offset returnPC (execute guest g t) ∧
      d.work = c.work + steps ∧ d.halted = false ∧
      d.natReg 0 = c.natReg 0 ∧ d.natReg 1 = c.natReg 1 ∧
      d.natReg 7 = c.natReg 7 ∧ d.realReg 7 = c.realReg 7 := by
  induction t generalizing c g with
  | zero => exact ⟨0,c,le_rfl,rfl,hr,hpos,rfl,hh,rfl,rfl,rfl,rfl⟩
  | succ t ih =>
    by_cases hgh : g.halted = true
    · refine ⟨0,c,Nat.zero_le _,rfl,?_,?_,rfl,hh,rfl,rfl,rfl,rfl⟩
      · rwa [execute_halted guest g hgh]
      · rwa [execute_halted guest g hgh]
    · have hghfalse := Bool.eq_false_iff.mpr hgh
      obtain ⟨ins,hins⟩ := hvalid 0 (by omega) hghfalse
      obtain ⟨s,b,hs,hb,hbrep,hbpc,hbw,hbh,hb0,hb1,hb7,hbr7⟩ :=
        shadow_single_step hr host guest width offset returnPC hw hc hcode hF hh hone hghfalse hbase hfactor hrealFactor hpos ins hins
      have hbvalid : ∀ j < t, (execute guest (step guest g) j).halted = false →
          ∃ ins, guest.code[(execute guest (step guest g) j).pc]? = some ins := by
        intro j hj hhj
        rw [← execute_succ_front] at hhj ⊢
        exact hvalid (j+1) (by omega) hhj
      obtain ⟨r,d,hrcost,hd,hdrep,hdpc,hdw,hdh,hd0,hd1,hd7,hdr7⟩ :=
        ih b (step guest g) hbrep hbh (hb1.trans hone) (hb0.trans hbase) (hb7.trans hfactor) (hbr7.trans hrealFactor) hbpc hbvalid
      refine ⟨s+r,d,?_,?_,?_,?_,?_,hdh,hd0.trans hb0,hd1.trans hb1,hd7.trans hb7,hdr7.trans hbr7⟩
      · rw [Nat.mul_succ]
        omega
      · rw [execute_add,hb,hd]
      · rwa [execute_succ_front]
      · rwa [execute_succ_front]
      · omega
lemma shadow_ends (host guest : Program) (offset returnPC : ℕ)
    (hcode : ShadowEmbedsCode host guest (shadowWidth guest.code) offset returnPC)
    (base F : ℕ) (hF : 0 < F) (c g final : Machine) (hr : ShadowRep base F c g)
    (hh : c.halted = false) (hone : c.natReg 1 = 1)
    (hbase : c.natReg 0 = base) (hfactor : c.natReg 7 = F) (hrealFactor : c.realReg 7 = (F : ℝ))
    (hpos : c.pc = shadowDestination (shadowWidth guest.code) offset returnPC g)
    (he : Ends guest g final) :
    ∃ (steps : ℕ) (d : Machine), execute host c steps = d ∧ ShadowRep base F d final ∧
      d.pc = returnPC ∧ d.work ≤ c.work + shadowWidth guest.code * (final.work - g.work) ∧
      d.halted = false ∧ d.natReg 0 = c.natReg 0 ∧ d.natReg 1 = c.natReg 1 ∧
      d.natReg 7 = c.natReg 7 ∧ d.realReg 7 = c.realReg 7 := by
  obtain ⟨t,ht,hhalt,hfault⟩ := he
  have hhalt' : (execute guest g t).halted = true := by rwa [ht]
  obtain ⟨r,_,hrun,hrwork⟩ := terminating_prefix guest g t hhalt'
  have hrfinal : execute guest g r = final := hrun.trans ht
  have hrfault : (execute guest g r).fault = false := by rwa [hrfinal]
  obtain ⟨s,d,hs,hd,hdrep,hdpc,hdw,hdh,hd0,hd1,hd7,hdr7⟩ :=
    shadow_execution host guest (shadowWidth guest.code) offset returnPC (shadowWidth_positive guest.code)
      (source_constant_bound guest.code) hcode base F hF r c g hr hh hone hbase hfactor hrealFactor hpos
      (execution_valid_code guest g r hrfault)
  refine ⟨s,d,hd,?_,?_,?_,hdh,hd0,hd1,hd7,hdr7⟩
  · rwa [hrfinal] at hdrep
  · rw [hdpc,hrfinal]
    simp [shadowDestination,hhalt]
  · rw [ht] at hrwork
    rw [hdw, ← hrwork]
    omega
end DecrAlmostLinearSSSP.Decremental
end s56
section s57
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
attribute [local instance] Classical.propDecidable
lemma shadowSteps_bound (width : ℕ) (ins : Instruction) (g : Machine)
    (hw : 8 ≤ width) (hc : naturalConstant ins + 4 ≤ width) : shadowSteps ins g ≤ width := by
  cases ins <;> simp only [shadowSteps,naturalConstant] at *
  all_goals try omega
  all_goals split_ifs <;> omega
lemma shadow_body_straight (width offset returnPC pc : ℕ) (ins : Instruction) (g : Machine)
    (hn : ¬ IsBranch ins) : ∀ slot < shadowSteps ins g - 1,
      ∃ tr, (shadowBlock width offset returnPC pc ins)[slot]? = some tr ∧ Straight tr := by
  classical
  cases ins with
  | natural d q =>
    intro slot hslot
    by_cases h0 : slot = 0
    · subst slot; exact ⟨_,rfl,trivial⟩
    by_cases h1 : slot = 1
    · subst slot; exact ⟨_,rfl,trivial⟩
    by_cases h2 : slot = 2
    · subst slot; exact ⟨_,rfl,trivial⟩
    have hq : slot - 3 < q := by simp only [shadowSteps] at hslot; omega
    have hs : slot = 3 + (slot - 3) := by omega
    rw [hs]
    exact ⟨_,shadowBlock_natural_add width offset returnPC pc d q (slot-3) hq,trivial⟩
  | less a b target | lessN a b target => all_goals exact False.elim (hn trivial)
  | _ =>
    all_goals intro slot hslot
    all_goals simp only [shadowSteps] at hslot
    all_goals interval_cases slot <;> exact ⟨_,rfl,trivial⟩
lemma shadow_nonbranch_prefix (host : Program) (c g : Machine) (width offset returnPC : ℕ)
    (ins : Instruction) (hw : 8 ≤ width) (hc : naturalConstant ins + 4 ≤ width)
    (hn : ¬ IsBranch ins) (hh : c.halted = false)
    (hcode : ∀ slot < width, host.code[c.pc + slot]? = (shadowBlock width offset returnPC g.pc ins)[slot]?) :
    ∀ j < shadowSteps ins g, (execute host c j).pc = c.pc + j ∧
      (execute host c j).halted = false ∧ (execute host c j).work = c.work+j := by
  intro j hj
  have hs := shadowSteps_bound width ins g hw hc
  apply straight_prefix host c (shadowSteps ins g - 1) hh _ j (by omega)
  intro slot hslot
  obtain ⟨tr,htr,hstraight⟩ := shadow_body_straight width offset returnPC g.pc ins g hn slot hslot
  exact ⟨tr,(hcode slot (by omega)).trans htr,hstraight⟩
end DecrAlmostLinearSSSP.Decremental
end s57
section s58
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
attribute [local instance] Classical.propDecidable
lemma shadow_branch_residence {base F : ℕ} {c g : Machine} (hr : ShadowRep base F c g)
    (host : Program) (width : ℕ) (hw : 8 ≤ width) (hF : 0 < F)
    (natural : Bool) (a b target : ℕ)
    (hh : c.halted = false) (hone : c.natReg 1 = 1)
    (h0 : host.code[c.pc]? = some (.natural 2 (g.pc + 1)))
    (h1 : host.code[c.pc + 1]? = some (.nadd 3 3 1))
    (h2 : host.code[c.pc + 2]? = some (branchInstruction natural (shadowReg a) (shadowReg b) (c.pc + 5)))
    (h5 : host.code[c.pc + 5]? = some (.natural 2 target)) :
    ∀ j < (if branchTest natural g a b then 5 else 4),
      ∃ slot < width, (execute host c j).pc = c.pc + slot := by
  classical
  let s := headerState c g.pc
  let g' : Machine := {g with pc := g.pc + 1, work := g.work + 1}
  have hs : execute host c 2 = s := embedded_header_exact host c g.pc hh hone h0 h1
  have hsrep : ShadowRep base F s g' := by rw [← hs]; exact hr.header host hh hone h0 h1
  have he : branchTest natural g' a b = branchTest natural g a b := by cases natural <;> rfl
  intro j hj
  by_cases htake : branchTest natural g a b
  · rw [if_pos htake] at hj
    let t : Machine := {s with pc := c.pc + 5, work := s.work + 1}
    have ht : execute host s 1 = t := by rw [host_shadow_branch hsrep host hF natural a b (c.pc+5) hh h2,he,if_pos htake]
    interval_cases j
    · exact ⟨0,by omega,rfl⟩
    · refine ⟨1,by omega,?_⟩
      exact (step_straight host c _ hh h0 trivial).1
    · exact ⟨2,by omega,congrArg Machine.pc hs⟩
    · refine ⟨5,by omega,?_⟩
      rw [show 3 = 2+1 by omega,execute_add,hs,ht]
    · refine ⟨6,by omega,?_⟩
      rw [show 4 = 2+(1+1) by omega,execute_add,hs,execute_add,ht]
      change (step host t).pc = _
      have hp := (step_straight host t (.natural 2 target) hh h5 trivial).1
      rw [hp]
  · rw [if_neg htake] at hj
    let t : Machine := {s with pc := c.pc+3, work := s.work+1}
    have ht : execute host s 1 = t := by
      rw [host_shadow_branch hsrep host hF natural a b (c.pc+5) hh h2,he,if_neg htake]
      simp [t,s,headerState,Nat.add_assoc]
    interval_cases j
    · exact ⟨0,by omega,rfl⟩
    · exact ⟨1,by omega,(step_straight host c _ hh h0 trivial).1⟩
    · exact ⟨2,by omega,congrArg Machine.pc hs⟩
    · refine ⟨3,by omega,?_⟩
      rw [show 3 = 2+1 by omega,execute_add,hs,ht]
end DecrAlmostLinearSSSP.Decremental
end s58
section s59
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma shadow_residence {base F : ℕ} {c g : Machine} (hr : ShadowRep base F c g)
    (host : Program) (width offset returnPC : ℕ) (hw : 8 ≤ width)
    (hF : 0 < F) (ins : Instruction) (hc : naturalConstant ins + 4 ≤ width)
    (hh : c.halted = false) (hone : c.natReg 1 = 1)
    (hpos : c.pc = offset + width * g.pc)
    (hcode : ∀ slot < width, host.code[c.pc+slot]? = (shadowBlock width offset returnPC g.pc ins)[slot]?) :
    ∀ j < shadowSteps ins g, ∃ slot < width, (execute host c j).pc = c.pc+slot := by
  classical
  by_cases hn : ¬ IsBranch ins
  · intro j hj
    refine ⟨j,lt_of_lt_of_le hj (shadowSteps_bound width ins g hw hc),?_⟩
    exact (shadow_nonbranch_prefix host c g width offset returnPC ins hw hc hn hh hcode j hj).1
  · have h0 : host.code[c.pc]? = some (.natural 2 (g.pc+1)) := by
      simpa only [Nat.add_zero] using (hcode 0 (by omega)).trans (shadowBlock_header width offset returnPC g.pc ins).1
    have h1 : host.code[c.pc+1]? = some (.nadd 3 3 1) :=
      (hcode 1 (by omega)).trans (shadowBlock_header width offset returnPC g.pc ins).2
    cases ins with
    | less a b target =>
      have h2 : host.code[c.pc+2]? = some (branchInstruction false (shadowReg a) (shadowReg b) (c.pc+5)) := by
        simpa [shadowBlock,branchInstruction,hpos] using hcode 2 (by omega)
      have h5 : host.code[c.pc+5]? = some (.natural 2 target) := by simpa [shadowBlock] using hcode 5 (by omega)
      simpa [shadowSteps,branchTest] using shadow_branch_residence hr host width hw hF false a b target hh hone h0 h1 h2 h5
    | lessN a b target =>
      have h2 : host.code[c.pc+2]? = some (branchInstruction true (shadowReg a) (shadowReg b) (c.pc+5)) := by
        simpa [shadowBlock,branchInstruction,hpos] using hcode 2 (by omega)
      have h5 : host.code[c.pc+5]? = some (.natural 2 target) := by simpa [shadowBlock] using hcode 5 (by omega)
      simpa [shadowSteps,branchTest] using shadow_branch_residence hr host width hw hF true a b target hh hone h0 h1 h2 h5
    | _ => simp [IsBranch] at hn
end DecrAlmostLinearSSSP.Decremental
end s59
section s60
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma shadowBlock_memory_origin (width offset returnPC pc : ℕ) (ins : Instruction) :
    ∀ tr ∈ shadowBlock width offset returnPC pc ins, ModifiesMemory tr → ModifiesMemory ins := by
  cases ins <;> simp [shadowBlock,constantProductCode,ModifiesMemory]
  intro tr htr
  rcases htr with ⟨_,rfl⟩ | rfl | ⟨_,rfl⟩
  all_goals simp
lemma shadowBlock_store_slot (width offset returnPC pc a d slot : ℕ) (hslot : slot < 7)
    (tr : Instruction) (htr : (shadowBlock width offset returnPC pc (.store a d))[slot]? = some tr)
    (hm : ModifiesMemory tr) : slot = 5 ∧ tr = .store 6 (shadowReg d) := by
  interval_cases slot <;> simp [shadowBlock] at htr
  all_goals subst tr
  all_goals simp only [ModifiesMemory] at hm
  all_goals try contradiction
  exact ⟨rfl,rfl⟩
lemma shadowBlock_storeN_slot (width offset returnPC pc a d slot : ℕ) (hslot : slot < 7)
    (tr : Instruction) (htr : (shadowBlock width offset returnPC pc (.storeN a d))[slot]? = some tr)
    (hm : ModifiesMemory tr) : slot = 5 ∧ tr = .storeN 6 (shadowReg d) := by
  interval_cases slot <;> simp [shadowBlock] at htr
  all_goals subst tr
  all_goals simp only [ModifiesMemory] at hm
  all_goals try contradiction
  exact ⟨rfl,rfl⟩
end DecrAlmostLinearSSSP.Decremental
end s60
section s61
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma no_address_write_of_no_memory (ins : Instruction) (c : Machine) (address : ℕ)
    (h : ¬ ModifiesMemory ins) : ¬ WritesAddress ins c address := by
  cases ins <;> simp_all [ModifiesMemory,WritesAddress]
lemma step_address_frame (p : Program) (c : Machine) (ins : Instruction) (address : ℕ)
    (hh : c.halted = false) (hc : p.code[c.pc]? = some ins) (hw : ¬ WritesAddress ins c address) :
    (step p c).realMem address = c.realMem address ∧ (step p c).natMem address = c.natMem address := by
  classical
  cases ins <;> simp only [WritesAddress] at hw
  all_goals simp only [step,hh,Bool.false_eq_true,if_false,hc]
  all_goals try exact ⟨rfl,rfl⟩
  all_goals try simp only [Function.update_of_ne (Ne.symm hw),true_and,and_true]
  all_goals try trivial
  all_goals split_ifs <;> simp
lemma execute_address_frame (p : Program) (c : Machine) (t address : ℕ)
    (hcode : ∀ j < t, ∀ ins, p.code[(execute p c j).pc]? = some ins →
      ¬ WritesAddress ins (execute p c j) address) :
    (execute p c t).realMem address = c.realMem address ∧
      (execute p c t).natMem address = c.natMem address := by
  induction t with
  | zero => exact ⟨rfl,rfl⟩
  | succ t ih =>
    have hi := ih (fun j hj ins hc => hcode j (by omega) ins hc)
    rw [execute_add]
    change (step p (execute p c t)).realMem address = _ ∧ (step p (execute p c t)).natMem address = _
    by_cases hh : (execute p c t).halted = true
    · rwa [step_of_halted p _ hh]
    · have hhalt := Bool.eq_false_iff.mpr hh
      cases hc : p.code[(execute p c t).pc]? with
      | none => simpa only [step,hhalt,Bool.false_eq_true,if_false,hc] using hi
      | some ins =>
        have hs := step_address_frame p _ ins address hhalt hc (hcode t (by omega) ins hc)
        exact ⟨hs.1.trans hi.1,hs.2.trans hi.2⟩
end DecrAlmostLinearSSSP.Decremental
end s61
section s62
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma memory_of_write (ins : Instruction) (c : Machine) (address : ℕ)
    (h : WritesAddress ins c address) : ModifiesMemory ins := by
  cases ins <;> simp only [WritesAddress,ModifiesMemory] at *
  all_goals first | trivial | contradiction
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
theorem solution : (((((((∀ (test : DecrAlmostLinearSSSP.Decremental.Structured.Test) (body : DecrAlmostLinearSSSP.Decremental.Structured.Cmd)
  (invariant : DecrAlmostLinearSSSP.Decremental.Structured.Data → Prop)
  (rank : DecrAlmostLinearSSSP.Decremental.Structured.Data → Nat) (B : Nat),
  (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
      invariant s →
        test.holds s →
          ∃ t cost,
            And (DecrAlmostLinearSSSP.Decremental.Structured.Eval body s cost t)
              (And (invariant t)
                (And (@LT.lt.{0} Nat instLTNat (rank t) (rank s)) (@LE.le.{0} Nat instLENat cost B)))) →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
      invariant s →
        ∃ t cost,
          And
            (DecrAlmostLinearSSSP.Decremental.Structured.Eval
              (DecrAlmostLinearSSSP.Decremental.Structured.Cmd.loop test body) s cost t)
            (And (invariant t)
              (@LE.le.{0} Nat instLENat cost
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (rank s))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))) ∧ (∀ (test : DecrAlmostLinearSSSP.Decremental.Structured.Test) (body : DecrAlmostLinearSSSP.Decremental.Structured.Cmd)
  (invariant : DecrAlmostLinearSSSP.Decremental.Structured.Data → Prop)
  (rank budget : DecrAlmostLinearSSSP.Decremental.Structured.Data → Nat),
  (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
      invariant s →
        test.holds s →
          ∃ t cost,
            And (DecrAlmostLinearSSSP.Decremental.Structured.Eval body s cost t)
              (And (invariant t)
                (And (@LT.lt.{0} Nat instLTNat (rank t) (rank s))
                  (@LE.le.{0} Nat instLENat
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cost
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (budget t))
                    (budget s))))) →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
      invariant s →
        ∃ t cost,
          And
            (DecrAlmostLinearSSSP.Decremental.Structured.Eval
              (DecrAlmostLinearSSSP.Decremental.Structured.Cmd.loop test body) s cost t)
            (And (invariant t)
              (@LE.le.{0} Nat instLENat
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cost (budget t))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (budget s)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))) ∧ ((∀ (test : DecrAlmostLinearSSSP.Decremental.Structured.Test) (body : DecrAlmostLinearSSSP.Decremental.Structured.Cmd)
  (cost : Nat) (s t : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.Cmd.loop test body) s
      cost t →
    Not (test.holds t)) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval
    (DecrAlmostLinearSSSP.Decremental.Structured.sequence
      (@List.map.{0, 0} DecrAlmostLinearSSSP.Decremental.Structured.Atom DecrAlmostLinearSSSP.Decremental.Structured.Cmd
        DecrAlmostLinearSSSP.Decremental.Structured.Cmd.atom DecrAlmostLinearSSSP.Decremental.ScaledCeiling.initAtoms))
    s (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
    (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.initial s)))) ∧ (((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.ScaledCeiling.buildBody s
    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
    (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.buildStep s)) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.ScaledCeiling.chooseBody s
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.chooseStep s))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  ∃ cost,
    And (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
      (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.ScaledCeiling.greedyBody s cost
        (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.greedyStep s))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (N : Nat),
  DecrAlmostLinearSSSP.Decremental.ScaledCeiling.BuildInvariant
    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) N
    (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.initial s)) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  And
    (@Eq.{1} Nat
      ((DecrAlmostLinearSSSP.Decremental.ScaledCeiling.buildStep s).natReg
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
    (And
      (@Eq.{1} Real
        ((DecrAlmostLinearSSSP.Decremental.ScaledCeiling.buildStep s).realReg
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (And
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.ScaledCeiling.buildStep s).natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
        (And
          (@Eq.{1} Real
            ((DecrAlmostLinearSSSP.Decremental.ScaledCeiling.buildStep s).realReg
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (And
            (@Eq.{1} Nat
              ((DecrAlmostLinearSSSP.Decremental.ScaledCeiling.buildStep s).natReg
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
            (And
              (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.buildStep s).realMem
                (@Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realMem
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
              (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.buildStep s).natMem
                (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natMem
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))))))))) ∧ ((((∀ {P : Nat} {x : Real} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.ScaledCeiling.Constants P x s →
    DecrAlmostLinearSSSP.Decremental.ScaledCeiling.Constants P x
      (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.buildStep s)) ∧ (∀ {P N : Nat} {x : Real} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.ScaledCeiling.BuildInvariant P x N s →
    @LE.le.{0} Real Real.instLE x
        (@HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
          N) →
      DecrAlmostLinearSSSP.Decremental.ScaledCeiling.buildTest.holds s →
        And
          (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.BuildInvariant P x N
            (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.buildStep s))
          (@LT.lt.{0} Nat instLTNat
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N
              ((DecrAlmostLinearSSSP.Decremental.ScaledCeiling.buildStep s).natReg
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))) ∧ ((∀ {P N : Nat} {x : Real} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.ScaledCeiling.BuildInvariant P x N s →
    @LE.le.{0} Real Real.instLE x
        (@HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
          N) →
      ∃ t cost,
        And
          (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.ScaledCeiling.buildLoop s
            cost t)
          (And (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.BuildInvariant P x N t)
            (And (Not (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.buildTest.holds t))
              (@LE.le.{0} Nat instLENat cost
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N
                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  And
    (@Eq.{1} Nat
      ((DecrAlmostLinearSSSP.Decremental.ScaledCeiling.greedyPrefix s).natReg
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
    (And
      (@Eq.{1} Real
        ((DecrAlmostLinearSSSP.Decremental.ScaledCeiling.greedyPrefix s).realReg
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (And
        (@Eq.{1} Real
          ((DecrAlmostLinearSSSP.Decremental.ScaledCeiling.greedyPrefix s).realReg
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (s.realMem
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))))
        (And
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.ScaledCeiling.greedyPrefix s).natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
          (And
            (@Eq.{1} Nat
              ((DecrAlmostLinearSSSP.Decremental.ScaledCeiling.greedyPrefix s).natReg
                (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
              (s.natMem
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))
            (And
              (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.greedyPrefix s).realMem s.realMem)
              (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.greedyPrefix s).natMem s.natMem))))))))) ∧ (((∀ {P : Nat} {x : Real} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.ScaledCeiling.Constants P x s →
    DecrAlmostLinearSSSP.Decremental.ScaledCeiling.Constants P x
      (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.greedyPrefix s)) ∧ (∀ {P : Nat} {x : Real} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.ScaledCeiling.Constants P x s →
    DecrAlmostLinearSSSP.Decremental.ScaledCeiling.Constants P x
      (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.chooseStep s))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  And
    (@Eq.{1} Nat
      ((DecrAlmostLinearSSSP.Decremental.ScaledCeiling.chooseStep s).natReg
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (And
      (@Eq.{1} Real
        ((DecrAlmostLinearSSSP.Decremental.ScaledCeiling.chooseStep s).realReg
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
          (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))
      (And
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.ScaledCeiling.chooseStep s).natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))))
        (And (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.chooseStep s).realMem s.realMem)
          (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.chooseStep s).natMem s.natMem))))) ∧ ((∀ {P : Nat} {x : Real} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.ScaledCeiling.GreedyInvariant P x s →
    DecrAlmostLinearSSSP.Decremental.ScaledCeiling.greedyTest.holds s →
      And
        (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.GreedyInvariant P x
          (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.greedyStep s))
        (@LT.lt.{0} Nat instLTNat
          ((DecrAlmostLinearSSSP.Decremental.ScaledCeiling.greedyStep s).natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) ∧ (∀ {P : Nat} {x : Real} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.ScaledCeiling.GreedyInvariant P x s →
    ∃ t cost,
      And
        (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.ScaledCeiling.greedyLoop s
          cost t)
        (And (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.GreedyInvariant P x t)
          (And (Not (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.greedyTest.holds t))
            (@LE.le.{0} Nat instLENat cost
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))))) ∧ (((((∀ {P : Nat} {x : Real} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.ScaledCeiling.GreedyInvariant P x s →
    Not (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.greedyTest.holds s) →
      @Eq.{1} Nat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) P
          (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
            (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing) x))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (N : Nat),
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
    @LE.le.{0} Real Real.instLE (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
          N) →
      ∃ t cost,
        And
          (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.ScaledCeiling.routine s
            cost t)
          (And
            (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
                  (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing)
                  (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
            (@LE.le.{0} Nat instLENat cost
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16))) N)
                (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))))))) ∧ ((∀ (c : DecrAlmostLinearSSSP.Decremental.Machine) (N : Nat),
  @Eq.{1} Nat c.pc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Bool c.halted Bool.false →
      @Eq.{1} Bool c.fault Bool.false →
        @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (c.realReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
          @LE.le.{0} Real Real.instLE (c.realReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                N) →
            ∃ d,
              And
                (DecrAlmostLinearSSSP.Decremental.Ends
                  (DecrAlmostLinearSSSP.Decremental.Structured.program
                    DecrAlmostLinearSSSP.Decremental.ScaledCeiling.routine
                    DecrAlmostLinearSSSP.Decremental.Structured.Cmd.skip)
                  c d)
                (And
                  (@Eq.{1} Nat (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                      (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
                        (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing)
                        (c.realReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                  (@LE.le.{0} Nat instLENat d.work
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16))) N))
                      (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15))))))) ∧ (∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (d factor count : Nat),
  @Ne.{1} Nat factor d →
    @Eq.{1} Bool c.halted Bool.false →
      (∀ (j : Nat),
          @LT.lt.{0} Nat instLTNat j count →
            @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
              (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                DecrAlmostLinearSSSP.Decremental.Instruction
                (fun as i =>
                  @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc j))
              (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                (DecrAlmostLinearSSSP.Decremental.Instruction.nadd d d factor))) →
        @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine (DecrAlmostLinearSSSP.Decremental.execute p c count)
          { pc := @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc count, realReg := c.realReg,
            natReg :=
              @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat c.natReg d
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (c.natReg d)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) count (c.natReg factor))),
            realMem := c.realMem, natMem := c.natMem, halted := c.halted, fault := c.fault,
            work := @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work count }))) ∧ (((∀ (d factor q : Nat),
  @Eq.{1} Nat
    (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction
      (DecrAlmostLinearSSSP.Decremental.constantProductCode d factor q))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) q
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) ∧ (∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (d factor q : Nat),
  @Ne.{1} Nat factor d →
    @Eq.{1} Bool c.halted Bool.false →
      @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
            DecrAlmostLinearSSSP.Decremental.Instruction
            (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
            (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code c.pc)
          (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
            (DecrAlmostLinearSSSP.Decremental.Instruction.natural d
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) →
        (∀ (j : Nat),
            @LT.lt.{0} Nat instLTNat j q →
              @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                  DecrAlmostLinearSSSP.Decremental.Instruction
                  (fun as i =>
                    @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                  (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    j))
                (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                  (DecrAlmostLinearSSSP.Decremental.Instruction.nadd d d factor))) →
          @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
            (DecrAlmostLinearSSSP.Decremental.execute p c
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) q
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            {
              pc :=
                @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) q
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))),
              realReg := c.realReg,
              natReg :=
                @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat c.natReg d
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) q (c.natReg factor)),
              realMem := c.realMem, natMem := c.natMem, halted := c.halted, fault := c.fault,
              work :=
                @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) q
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) })) ∧ ((∀ (width offset returnPC pc : Nat) (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) width →
    @LE.le.{0} Nat instLENat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (DecrAlmostLinearSSSP.Decremental.naturalConstant ins)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        width →
      @Eq.{1} Nat
        (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction
          (DecrAlmostLinearSSSP.Decremental.shadowBlock width offset returnPC pc ins))
        width) ∧ ((∀ (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
  @Membership.mem.{0, 0} DecrAlmostLinearSSSP.Decremental.Instruction
      (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
      (@List.instMembership.{0} DecrAlmostLinearSSSP.Decremental.Instruction) code ins →
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (DecrAlmostLinearSSSP.Decremental.naturalConstant ins)
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
      (DecrAlmostLinearSSSP.Decremental.shadowWidth code)) ∧ (∀ (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
    (DecrAlmostLinearSSSP.Decremental.shadowWidth code)))))) ∧ ((((∀ (width offset returnPC start : Nat) (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) width →
    (∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
        @Membership.mem.{0, 0} DecrAlmostLinearSSSP.Decremental.Instruction
            (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
            (@List.instMembership.{0} DecrAlmostLinearSSSP.Decremental.Instruction) code ins →
          @LE.le.{0} Nat instLENat
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (DecrAlmostLinearSSSP.Decremental.naturalConstant ins)
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            width) →
      @Eq.{1} Nat
        (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction
          (DecrAlmostLinearSSSP.Decremental.shadowCodeAux width offset returnPC start code))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) width
          (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction code))) ∧ (∀ (offset returnPC : Nat) (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction),
  @Eq.{1} Nat
    (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction
      (DecrAlmostLinearSSSP.Decremental.shadowCode offset returnPC code))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (DecrAlmostLinearSSSP.Decremental.shadowWidth code)
      (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction code)))) ∧ ((∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
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
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) }) ∧ ((∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    ∀ (host : DecrAlmostLinearSSSP.Decremental.Program) (ins tr : DecrAlmostLinearSSSP.Decremental.Instruction),
      @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (DecrAlmostLinearSSSP.Decremental.shadowScalarTranslation ins)
          (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction tr) →
        @Eq.{1} Bool c.halted Bool.false →
          @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
              (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                DecrAlmostLinearSSSP.Decremental.Instruction
                (fun as i =>
                  @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code c.pc)
              (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction tr) →
            DecrAlmostLinearSSSP.Decremental.ShadowRep base F (DecrAlmostLinearSSSP.Decremental.step host c)
              (DecrAlmostLinearSSSP.Decremental.instructionEffect ins g)) ∧ (∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    ∀ (host : DecrAlmostLinearSSSP.Decremental.Program) (target : Nat),
      @Eq.{1} Bool c.halted Bool.false →
        @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
            (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
              DecrAlmostLinearSSSP.Decremental.Instruction
              (fun as i =>
                @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
              (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code c.pc)
            (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
              (DecrAlmostLinearSSSP.Decremental.Instruction.jump target)) →
          DecrAlmostLinearSSSP.Decremental.ShadowRep base F (DecrAlmostLinearSSSP.Decremental.step host c) g)))) ∧ (((∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    ∀ (host : DecrAlmostLinearSSSP.Decremental.Program) (d q : Nat),
      @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) F →
        @Eq.{1} Bool c.halted Bool.false →
          @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
              (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                DecrAlmostLinearSSSP.Decremental.Instruction
                (fun as i =>
                  @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code c.pc)
              (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                (DecrAlmostLinearSSSP.Decremental.Instruction.natural (DecrAlmostLinearSSSP.Decremental.shadowReg d)
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) →
            (∀ (j : Nat),
                @LT.lt.{0} Nat instLTNat j q →
                  @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                    (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                      DecrAlmostLinearSSSP.Decremental.Instruction
                      (fun as i =>
                        @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                      (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        j))
                    (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                      (DecrAlmostLinearSSSP.Decremental.Instruction.nadd (DecrAlmostLinearSSSP.Decremental.shadowReg d)
                        (DecrAlmostLinearSSSP.Decremental.shadowReg d)
                        (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))) →
              DecrAlmostLinearSSSP.Decremental.ShadowRep base F
                (DecrAlmostLinearSSSP.Decremental.execute host c
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) q
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (DecrAlmostLinearSSSP.Decremental.instructionEffect
                  (DecrAlmostLinearSSSP.Decremental.Instruction.natural d q) g)) ∧ (∀ (width offset returnPC pc : Nat) (ins tr : DecrAlmostLinearSSSP.Decremental.Instruction),
  @Membership.mem.{0, 0} DecrAlmostLinearSSSP.Decremental.Instruction
      (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
      (@List.instMembership.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
      (DecrAlmostLinearSSSP.Decremental.shadowBlock width offset returnPC pc ins) tr →
    DecrAlmostLinearSSSP.Decremental.ReservedSafe tr)) ∧ ((∀ (width offset returnPC start : Nat) (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
  (tr : DecrAlmostLinearSSSP.Decremental.Instruction),
  @Membership.mem.{0, 0} DecrAlmostLinearSSSP.Decremental.Instruction
      (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
      (@List.instMembership.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
      (DecrAlmostLinearSSSP.Decremental.shadowCodeAux width offset returnPC start code) tr →
    DecrAlmostLinearSSSP.Decremental.ReservedSafe tr) ∧ ((∀ {α : Type} (mem : Nat → α) (base j k a b : Nat) (value : α),
  @Ne.{1} Nat j k →
    @Eq.{1} α
      (@Function.update.{1, 1} Nat (fun a => α) instDecidableEqNat mem
        (DecrAlmostLinearSSSP.Decremental.bankAddress base j a) value
        (DecrAlmostLinearSSSP.Decremental.bankAddress base k b))
      (mem (DecrAlmostLinearSSSP.Decremental.bankAddress base k b))) ∧ (∀ {α : Type} (mem : Nat → α) (base j a b : Nat) (value : α),
  @Eq.{1} α
    (@Function.update.{1, 1} Nat (fun a => α) instDecidableEqNat mem
      (DecrAlmostLinearSSSP.Decremental.bankAddress base j a) value
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (mem
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))))))) ∧ ((((((∀ {α : Type} (mem : Nat → α) (base j a b : Nat) (value : α),
  @LE.le.{0} Nat instLENat b base →
    @Eq.{1} α
      (@Function.update.{1, 1} Nat (fun a => α) instDecidableEqNat mem
        (DecrAlmostLinearSSSP.Decremental.bankAddress base j a) value b)
      (mem b)) ∧ (∀ (ins tr : DecrAlmostLinearSSSP.Decremental.Instruction),
  @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
      (DecrAlmostLinearSSSP.Decremental.shadowScalarTranslation ins)
      (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction tr) →
    DecrAlmostLinearSSSP.Decremental.ReservedSafe tr)) ∧ ((∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    ∀ (host : DecrAlmostLinearSSSP.Decremental.Program) (ins tr : DecrAlmostLinearSSSP.Decremental.Instruction),
      @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (DecrAlmostLinearSSSP.Decremental.shadowScalarTranslation ins)
          (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction tr) →
        @Eq.{1} Bool c.halted Bool.false →
          @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
              (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                DecrAlmostLinearSSSP.Decremental.Instruction
                (fun as i =>
                  @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code c.pc)
              (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction tr) →
            And
              (DecrAlmostLinearSSSP.Decremental.ShadowRep base F
                (DecrAlmostLinearSSSP.Decremental.execute host c
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (DecrAlmostLinearSSSP.Decremental.instructionEffect ins g))
              (And
                (@Eq.{1} Nat
                  (DecrAlmostLinearSSSP.Decremental.execute host c
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).pc
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (And
                  (@Eq.{1} Nat
                    (DecrAlmostLinearSSSP.Decremental.execute host c
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).work
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (And
                    (@Eq.{1} Bool
                      (DecrAlmostLinearSSSP.Decremental.execute host c
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).halted
                      Bool.false)
                    (And
                      (@Eq.{1} Nat
                        ((DecrAlmostLinearSSSP.Decremental.execute host c
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).natReg
                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                        (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                      (And
                        (@Eq.{1} Nat
                          ((DecrAlmostLinearSSSP.Decremental.execute host c
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).natReg
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        (And
                          (@Eq.{1} Nat
                            ((DecrAlmostLinearSSSP.Decremental.execute host c
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).natReg
                              (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                            (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                          (@Eq.{1} Real
                            ((DecrAlmostLinearSSSP.Decremental.execute host c
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).realReg
                              (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                            (c.realReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))))))))) ∧ (∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    ∀ (host : DecrAlmostLinearSSSP.Decremental.Program) (width offset : Nat)
      (ins tr : DecrAlmostLinearSSSP.Decremental.Instruction),
      @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (DecrAlmostLinearSSSP.Decremental.shadowScalarTranslation ins)
          (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction tr) →
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
                @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                    (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                      DecrAlmostLinearSSSP.Decremental.Instruction
                      (fun as i =>
                        @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                      (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction tr) →
                  @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                      (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                        DecrAlmostLinearSSSP.Decremental.Instruction
                        (fun as i =>
                          @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                        (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                      (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                        (DecrAlmostLinearSSSP.Decremental.Instruction.jump
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) width
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.pc
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))) →
                    ∃ d,
                      And
                        (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                          (DecrAlmostLinearSSSP.Decremental.execute host c
                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                          d)
                        (And
                          (DecrAlmostLinearSSSP.Decremental.ShadowRep base F d
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
                          (And
                            (@Eq.{1} Nat d.pc
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) width
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.pc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                            (And
                              (@Eq.{1} Nat d.work
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
                              (And (@Eq.{1} Bool d.halted Bool.false)
                                (And
                                  (@Eq.{1} Nat (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                    (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                                  (And
                                    (@Eq.{1} Nat
                                      (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                      (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                    (And
                                      (@Eq.{1} Nat
                                        (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                                        (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                                      (@Eq.{1} Real
                                        (d.realReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                                        (c.realReg
                                          (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))))))))))))) ∧ (((∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    ∀ (host : DecrAlmostLinearSSSP.Decremental.Program) (width offset target : Nat),
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
              @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                  (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                    DecrAlmostLinearSSSP.Decremental.Instruction
                    (fun as i =>
                      @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                    (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                    (DecrAlmostLinearSSSP.Decremental.Instruction.natural
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) target)) →
                @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                    (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                      DecrAlmostLinearSSSP.Decremental.Instruction
                      (fun as i =>
                        @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                      (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                    (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                      (DecrAlmostLinearSSSP.Decremental.Instruction.jump
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) width target)))) →
                  ∃ d,
                    And
                      (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                        (DecrAlmostLinearSSSP.Decremental.execute host c
                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                        d)
                      (And
                        (DecrAlmostLinearSSSP.Decremental.ShadowRep base F d
                          (DecrAlmostLinearSSSP.Decremental.instructionEffect
                            (DecrAlmostLinearSSSP.Decremental.Instruction.jump target)
                            {
                              pc :=
                                @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.pc
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))),
                              realReg := g.realReg, natReg := g.natReg, realMem := g.realMem, natMem := g.natMem,
                              halted := g.halted, fault := g.fault,
                              work :=
                                @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.work
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) }))
                        (And
                          (@Eq.{1} Nat d.pc
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) width target)))
                          (And
                            (@Eq.{1} Nat d.work
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
                            (And (@Eq.{1} Bool d.halted Bool.false)
                              (And
                                (@Eq.{1} Nat (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                  (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                                (And
                                  (@Eq.{1} Nat (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                    (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                  (And
                                    (@Eq.{1} Nat
                                      (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                                      (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                                    (@Eq.{1} Real
                                      (d.realReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                                      (c.realReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))))))))))) ∧ (∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    ∀ (host : DecrAlmostLinearSSSP.Decremental.Program) (returnPC : Nat),
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
              @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                  (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                    DecrAlmostLinearSSSP.Decremental.Instruction
                    (fun as i =>
                      @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                    (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                    (DecrAlmostLinearSSSP.Decremental.Instruction.natural
                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                    (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                      DecrAlmostLinearSSSP.Decremental.Instruction
                      (fun as i =>
                        @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                      (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                    (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                      (DecrAlmostLinearSSSP.Decremental.Instruction.jump returnPC)) →
                  ∃ d,
                    And
                      (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                        (DecrAlmostLinearSSSP.Decremental.execute host c
                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                        d)
                      (And
                        (DecrAlmostLinearSSSP.Decremental.ShadowRep base F d
                          (DecrAlmostLinearSSSP.Decremental.instructionEffect
                            DecrAlmostLinearSSSP.Decremental.Instruction.halt
                            {
                              pc :=
                                @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.pc
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))),
                              realReg := g.realReg, natReg := g.natReg, realMem := g.realMem, natMem := g.natMem,
                              halted := g.halted, fault := g.fault,
                              work :=
                                @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.work
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) }))
                        (And (@Eq.{1} Nat d.pc returnPC)
                          (And
                            (@Eq.{1} Nat d.work
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
                            (And (@Eq.{1} Bool d.halted Bool.false)
                              (And
                                (@Eq.{1} Nat (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                  (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                                (And
                                  (@Eq.{1} Nat (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                    (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                  (And
                                    (@Eq.{1} Nat
                                      (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                                      (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                                    (@Eq.{1} Real
                                      (d.realReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                                      (c.realReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))))))))))) ∧ ((∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    ∀ (host : DecrAlmostLinearSSSP.Decremental.Program),
      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) F →
        ∀ (natural : Bool) (a b target : Nat),
          @Eq.{1} Bool c.halted Bool.false →
            @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                  DecrAlmostLinearSSSP.Decremental.Instruction
                  (fun as i =>
                    @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                  (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code c.pc)
                (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                  (DecrAlmostLinearSSSP.Decremental.branchInstruction natural
                    (DecrAlmostLinearSSSP.Decremental.shadowReg a) (DecrAlmostLinearSSSP.Decremental.shadowReg b)
                    target)) →
              @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                (DecrAlmostLinearSSSP.Decremental.execute host c
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                {
                  pc :=
                    @ite.{1} Nat (DecrAlmostLinearSSSP.Decremental.branchTest natural g a b)
                      (Classical.propDecidable (DecrAlmostLinearSSSP.Decremental.branchTest natural g a b)) target
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))),
                  realReg := c.realReg, natReg := c.natReg, realMem := c.realMem, natMem := c.natMem,
                  halted := c.halted, fault := c.fault,
                  work :=
                    @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) }) ∧ ((∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    ∀ (host : DecrAlmostLinearSSSP.Decremental.Program) (width offset target : Nat),
      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) F →
        ∀ (natural : Bool) (a b : Nat),
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
                  @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                      (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                        DecrAlmostLinearSSSP.Decremental.Instruction
                        (fun as i =>
                          @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                        (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                        (DecrAlmostLinearSSSP.Decremental.branchInstruction natural
                          (DecrAlmostLinearSSSP.Decremental.shadowReg a) (DecrAlmostLinearSSSP.Decremental.shadowReg b)
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                            (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))) →
                    @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                          DecrAlmostLinearSSSP.Decremental.Instruction
                          (fun as i =>
                            @LT.lt.{0} Nat instLTNat i
                              (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                          (DecrAlmostLinearSSSP.Decremental.Instruction.jump
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) width
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.pc
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))) →
                      @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                          (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                            DecrAlmostLinearSSSP.Decremental.Instruction
                            (fun as i =>
                              @LT.lt.{0} Nat instLTNat i
                                (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                            (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                              (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))
                          (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                            (DecrAlmostLinearSSSP.Decremental.Instruction.natural
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) target)) →
                        @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                            (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                              DecrAlmostLinearSSSP.Decremental.Instruction
                              (fun as i =>
                                @LT.lt.{0} Nat instLTNat i
                                  (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                              (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                                (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
                            (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                              (DecrAlmostLinearSSSP.Decremental.Instruction.jump
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) width target)))) →
                          ∃ steps d,
                            And
                              (@LE.le.{0} Nat instLENat steps
                                (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                              (And
                                (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                                  (DecrAlmostLinearSSSP.Decremental.execute host c steps) d)
                                (And
                                  (DecrAlmostLinearSSSP.Decremental.ShadowRep base F d
                                    (DecrAlmostLinearSSSP.Decremental.instructionEffect
                                      (DecrAlmostLinearSSSP.Decremental.branchInstruction natural a b target)
                                      {
                                        pc :=
                                          @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.pc
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))),
                                        realReg := g.realReg, natReg := g.natReg, realMem := g.realMem,
                                        natMem := g.natMem, halted := g.halted, fault := g.fault,
                                        work :=
                                          @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.work
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) }))
                                  (And
                                    (@Eq.{1} Nat d.pc
                                      (@ite.{1} Nat (DecrAlmostLinearSSSP.Decremental.branchTest natural g a b)
                                        (Classical.propDecidable
                                          (DecrAlmostLinearSSSP.Decremental.branchTest natural g a b))
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) width
                                            target))
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) width
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.pc
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))
                                    (And
                                      (@Eq.{1} Nat d.work
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work steps))
                                      (And (@Eq.{1} Bool d.halted Bool.false)
                                        (And
                                          (@Eq.{1} Nat
                                            (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                            (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                                          (And
                                            (@Eq.{1} Nat
                                              (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                              (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (And
                                              (@Eq.{1} Nat
                                                (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                                                (c.natReg
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                                              (And
                                                (@Eq.{1} Real
                                                  (d.realReg
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                                                  (c.realReg
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                                                (@Eq.{1} Nat steps
                                                  (@ite.{1} Nat
                                                    (DecrAlmostLinearSSSP.Decremental.branchTest natural g a b)
                                                    (Classical.propDecidable
                                                      (DecrAlmostLinearSSSP.Decremental.branchTest natural g a b))
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                      (instOfNatNat (nat_lit 4))))))))))))))) ∧ (∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    ∀ (host : DecrAlmostLinearSSSP.Decremental.Program) (width offset d q : Nat),
      @Eq.{1} Bool c.halted Bool.false →
        @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
          @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) F →
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
                @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                    (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                      DecrAlmostLinearSSSP.Decremental.Instruction
                      (fun as i =>
                        @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                      (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                      (DecrAlmostLinearSSSP.Decremental.Instruction.natural
                        (DecrAlmostLinearSSSP.Decremental.shadowReg d)
                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) →
                  (∀ (j : Nat),
                      @LT.lt.{0} Nat instLTNat j q →
                        @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                          (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                            DecrAlmostLinearSSSP.Decremental.Instruction
                            (fun as i =>
                              @LT.lt.{0} Nat instLTNat i
                                (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                            (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                              j))
                          (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                            (DecrAlmostLinearSSSP.Decremental.Instruction.nadd
                              (DecrAlmostLinearSSSP.Decremental.shadowReg d)
                              (DecrAlmostLinearSSSP.Decremental.shadowReg d)
                              (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))) →
                    @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                          DecrAlmostLinearSSSP.Decremental.Instruction
                          (fun as i =>
                            @LT.lt.{0} Nat instLTNat i
                              (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) q
                              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                          (DecrAlmostLinearSSSP.Decremental.Instruction.jump
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) width
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.pc
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))) →
                      ∃ finish,
                        And
                          (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                            (DecrAlmostLinearSSSP.Decremental.execute host c
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) q
                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
                            finish)
                          (And
                            (DecrAlmostLinearSSSP.Decremental.ShadowRep base F finish
                              (DecrAlmostLinearSSSP.Decremental.instructionEffect
                                (DecrAlmostLinearSSSP.Decremental.Instruction.natural d q)
                                {
                                  pc :=
                                    @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.pc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))),
                                  realReg := g.realReg, natReg := g.natReg, realMem := g.realMem, natMem := g.natMem,
                                  halted := g.halted, fault := g.fault,
                                  work :=
                                    @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.work
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) }))
                            (And
                              (@Eq.{1} Nat finish.pc
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) width
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.pc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                              (And
                                (@Eq.{1} Nat finish.work
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) q
                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
                                (And (@Eq.{1} Bool finish.halted Bool.false)
                                  (And
                                    (@Eq.{1} Nat
                                      (finish.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                      (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                                    (And
                                      (@Eq.{1} Nat
                                        (finish.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                        (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                      (And
                                        (@Eq.{1} Nat
                                          (finish.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                                          (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                                        (@Eq.{1} Real
                                          (finish.realReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                                          (c.realReg
                                            (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))))))))))))))) ∧ ((((∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    ∀ (host : DecrAlmostLinearSSSP.Decremental.Program),
      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) F →
        ∀ (d a : Nat),
          @Eq.{1} Bool c.halted Bool.false →
            @Eq.{1} Real (c.realReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                (@Nat.cast.{0} Real Real.instNatCast F) →
              @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                  (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                    DecrAlmostLinearSSSP.Decremental.Instruction
                    (fun as i =>
                      @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                    (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code c.pc)
                  (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                    (DecrAlmostLinearSSSP.Decremental.Instruction.cast (DecrAlmostLinearSSSP.Decremental.shadowReg d)
                      (DecrAlmostLinearSSSP.Decremental.shadowReg a))) →
                @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                    (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                      DecrAlmostLinearSSSP.Decremental.Instruction
                      (fun as i =>
                        @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                      (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                      (DecrAlmostLinearSSSP.Decremental.Instruction.div (DecrAlmostLinearSSSP.Decremental.shadowReg d)
                        (DecrAlmostLinearSSSP.Decremental.shadowReg d)
                        (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))) →
                  ∃ finish,
                    And
                      (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                        (DecrAlmostLinearSSSP.Decremental.execute host c
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        finish)
                      (And
                        (DecrAlmostLinearSSSP.Decremental.ShadowRep base F finish
                          (DecrAlmostLinearSSSP.Decremental.instructionEffect
                            (DecrAlmostLinearSSSP.Decremental.Instruction.cast d a) g))
                        (And
                          (@Eq.{1} Nat finish.pc
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                          (And
                            (@Eq.{1} Nat finish.work
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                            (And (@Eq.{1} Bool finish.halted Bool.false)
                              (And (@Eq.{1} (Nat → Nat) finish.natReg c.natReg)
                                (@Eq.{1} Real
                                  (finish.realReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                                  (c.realReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))))))))) ∧ (∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    ∀ (host : DecrAlmostLinearSSSP.Decremental.Program) (width offset : Nat),
      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) F →
        ∀ (d a : Nat),
          @Eq.{1} Bool c.halted Bool.false →
            @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
              @Eq.{1} Real (c.realReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                  (@Nat.cast.{0} Real Real.instNatCast F) →
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
                    @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                          DecrAlmostLinearSSSP.Decremental.Instruction
                          (fun as i =>
                            @LT.lt.{0} Nat instLTNat i
                              (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                          (DecrAlmostLinearSSSP.Decremental.Instruction.cast
                            (DecrAlmostLinearSSSP.Decremental.shadowReg d)
                            (DecrAlmostLinearSSSP.Decremental.shadowReg a))) →
                      @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                          (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                            DecrAlmostLinearSSSP.Decremental.Instruction
                            (fun as i =>
                              @LT.lt.{0} Nat instLTNat i
                                (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                            (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                          (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                            (DecrAlmostLinearSSSP.Decremental.Instruction.div
                              (DecrAlmostLinearSSSP.Decremental.shadowReg d)
                              (DecrAlmostLinearSSSP.Decremental.shadowReg d)
                              (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))) →
                        @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                            (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                              DecrAlmostLinearSSSP.Decremental.Instruction
                              (fun as i =>
                                @LT.lt.{0} Nat instLTNat i
                                  (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                              (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
                            (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                              (DecrAlmostLinearSSSP.Decremental.Instruction.jump
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) width
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.pc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))) →
                          ∃ finish,
                            And
                              (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                                (DecrAlmostLinearSSSP.Decremental.execute host c
                                  (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                                finish)
                              (And
                                (DecrAlmostLinearSSSP.Decremental.ShadowRep base F finish
                                  (DecrAlmostLinearSSSP.Decremental.instructionEffect
                                    (DecrAlmostLinearSSSP.Decremental.Instruction.cast d a)
                                    {
                                      pc :=
                                        @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.pc
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))),
                                      realReg := g.realReg, natReg := g.natReg, realMem := g.realMem,
                                      natMem := g.natMem, halted := g.halted, fault := g.fault,
                                      work :=
                                        @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.work
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) }))
                                (And
                                  (@Eq.{1} Nat finish.pc
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) width
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.pc
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                                  (And
                                    (@Eq.{1} Nat finish.work
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                                        (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))
                                    (And (@Eq.{1} Bool finish.halted Bool.false)
                                      (And
                                        (@Eq.{1} Nat
                                          (finish.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                          (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                                        (And
                                          (@Eq.{1} Nat
                                            (finish.natReg
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                            (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                          (And
                                            (@Eq.{1} Nat
                                              (finish.natReg
                                                (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                                              (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                                            (@Eq.{1} Real
                                              (finish.realReg
                                                (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                                              (c.realReg
                                                (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))))))))))) ∧ ((∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    ∀ (host : DecrAlmostLinearSSSP.Decremental.Program) (a : Nat),
      @Eq.{1} Bool c.halted Bool.false →
        @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) base →
          @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) F →
            @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                  DecrAlmostLinearSSSP.Decremental.Instruction
                  (fun as i =>
                    @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                  (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code c.pc)
                (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                  (DecrAlmostLinearSSSP.Decremental.Instruction.nadd
                    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                    (DecrAlmostLinearSSSP.Decremental.shadowReg a) (DecrAlmostLinearSSSP.Decremental.shadowReg a))) →
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
                      (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                      (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) →
                @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                    (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                      DecrAlmostLinearSSSP.Decremental.Instruction
                      (fun as i =>
                        @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                      (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                      (DecrAlmostLinearSSSP.Decremental.Instruction.nadd
                        (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))) →
                  ∃ d,
                    And
                      (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                        (DecrAlmostLinearSSSP.Decremental.execute host c
                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                        d)
                      (And (DecrAlmostLinearSSSP.Decremental.ShadowRep base F d g)
                        (And
                          (@Eq.{1} Nat (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (g.natReg a))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                          (And
                            (@Eq.{1} Nat d.pc
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                            (And
                              (@Eq.{1} Nat d.work
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                              (And (@Eq.{1} Bool d.halted Bool.false)
                                (And
                                  (@Eq.{1} Nat (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                    (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                                  (And
                                    (@Eq.{1} Nat
                                      (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                      (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                    (And
                                      (@Eq.{1} Nat
                                        (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                                        (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                                      (@Eq.{1} Real
                                        (d.realReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                                        (c.realReg
                                          (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))))))))))) ∧ ((∀ (ins tr : DecrAlmostLinearSSSP.Decremental.Instruction) (a : Nat),
  @Eq.{1} (Option.{0} (Prod.{0, 0} DecrAlmostLinearSSSP.Decremental.Instruction Nat))
      (DecrAlmostLinearSSSP.Decremental.shadowMemoryTranslation ins)
      (@Option.some.{0} (Prod.{0, 0} DecrAlmostLinearSSSP.Decremental.Instruction Nat)
        (@Prod.mk.{0, 0} DecrAlmostLinearSSSP.Decremental.Instruction Nat tr a)) →
    DecrAlmostLinearSSSP.Decremental.ReservedSafe tr) ∧ (∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    ∀ (host : DecrAlmostLinearSSSP.Decremental.Program),
      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) F →
        ∀ (ins tr : DecrAlmostLinearSSSP.Decremental.Instruction) (a : Nat),
          @Eq.{1} (Option.{0} (Prod.{0, 0} DecrAlmostLinearSSSP.Decremental.Instruction Nat))
              (DecrAlmostLinearSSSP.Decremental.shadowMemoryTranslation ins)
              (@Option.some.{0} (Prod.{0, 0} DecrAlmostLinearSSSP.Decremental.Instruction Nat)
                (@Prod.mk.{0, 0} DecrAlmostLinearSSSP.Decremental.Instruction Nat tr a)) →
            @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (g.natReg a))
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
              @Eq.{1} Bool c.halted Bool.false →
                @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                    (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                      DecrAlmostLinearSSSP.Decremental.Instruction
                      (fun as i =>
                        @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                      (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code c.pc)
                    (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction tr) →
                  And
                    (DecrAlmostLinearSSSP.Decremental.ShadowRep base F
                      (DecrAlmostLinearSSSP.Decremental.execute host c
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      (DecrAlmostLinearSSSP.Decremental.instructionEffect ins g))
                    (And
                      (@Eq.{1} Nat
                        (DecrAlmostLinearSSSP.Decremental.execute host c
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).pc
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (And
                        (@Eq.{1} Nat
                          (DecrAlmostLinearSSSP.Decremental.execute host c
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).work
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        (And
                          (@Eq.{1} Bool
                            (DecrAlmostLinearSSSP.Decremental.execute host c
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).halted
                            Bool.false)
                          (And
                            (@Eq.{1} Nat
                              ((DecrAlmostLinearSSSP.Decremental.execute host c
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).natReg
                                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                              (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                            (And
                              (@Eq.{1} Nat
                                ((DecrAlmostLinearSSSP.Decremental.execute host c
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).natReg
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                              (And
                                (@Eq.{1} Nat
                                  ((DecrAlmostLinearSSSP.Decremental.execute host c
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).natReg
                                    (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                                  (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                                (@Eq.{1} Real
                                  ((DecrAlmostLinearSSSP.Decremental.execute host c
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).realReg
                                    (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                                  (c.realReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))))))))))))) ∧ (((∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    ∀ (host : DecrAlmostLinearSSSP.Decremental.Program) (width offset : Nat),
      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) F →
        ∀ (ins tr : DecrAlmostLinearSSSP.Decremental.Instruction) (a : Nat),
          @Eq.{1} (Option.{0} (Prod.{0, 0} DecrAlmostLinearSSSP.Decremental.Instruction Nat))
              (DecrAlmostLinearSSSP.Decremental.shadowMemoryTranslation ins)
              (@Option.some.{0} (Prod.{0, 0} DecrAlmostLinearSSSP.Decremental.Instruction Nat)
                (@Prod.mk.{0, 0} DecrAlmostLinearSSSP.Decremental.Instruction Nat tr a)) →
            @Eq.{1} Bool c.halted Bool.false →
              @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) base →
                  @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) F →
                    @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                          DecrAlmostLinearSSSP.Decremental.Instruction
                          (fun as i =>
                            @LT.lt.{0} Nat instLTNat i
                              (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                          c.pc)
                        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                          (DecrAlmostLinearSSSP.Decremental.Instruction.natural
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.pc
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
                      @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                          (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                            DecrAlmostLinearSSSP.Decremental.Instruction
                            (fun as i =>
                              @LT.lt.{0} Nat instLTNat i
                                (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                            (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                          (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                            (DecrAlmostLinearSSSP.Decremental.Instruction.nadd
                              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                        @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                            (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                              DecrAlmostLinearSSSP.Decremental.Instruction
                              (fun as i =>
                                @LT.lt.{0} Nat instLTNat i
                                  (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                              (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                            (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                              (DecrAlmostLinearSSSP.Decremental.Instruction.nadd
                                (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                                (DecrAlmostLinearSSSP.Decremental.shadowReg a)
                                (DecrAlmostLinearSSSP.Decremental.shadowReg a))) →
                          @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                              (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                                DecrAlmostLinearSSSP.Decremental.Instruction
                                (fun as i =>
                                  @LT.lt.{0} Nat instLTNat i
                                    (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                                (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                                host.code
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                              (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                                (DecrAlmostLinearSSSP.Decremental.Instruction.nadd
                                  (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) →
                            @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                                (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                                  Nat DecrAlmostLinearSSSP.Decremental.Instruction
                                  (fun as i =>
                                    @LT.lt.{0} Nat instLTNat i
                                      (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                                  (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                                  host.code
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
                                (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                                  (DecrAlmostLinearSSSP.Decremental.Instruction.nadd
                                    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))) →
                              @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                                  (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                                    Nat DecrAlmostLinearSSSP.Decremental.Instruction
                                    (fun as i =>
                                      @LT.lt.{0} Nat instLTNat i
                                        (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                                    (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                                    host.code
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))
                                  (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction tr) →
                                @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                                    (@GetElem?.getElem?.{0, 0, 0}
                                      (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                                      DecrAlmostLinearSSSP.Decremental.Instruction
                                      (fun as i =>
                                        @LT.lt.{0} Nat instLTNat i
                                          (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                                      (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                                      host.code
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                                        (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
                                    (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                                      (DecrAlmostLinearSSSP.Decremental.Instruction.jump
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) width
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.pc
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))) →
                                  ∃ d,
                                    And
                                      (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                                        (DecrAlmostLinearSSSP.Decremental.execute host c
                                          (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                                        d)
                                      (And
                                        (DecrAlmostLinearSSSP.Decremental.ShadowRep base F d
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
                                        (And
                                          (@Eq.{1} Nat d.pc
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) width
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.pc
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                                          (And
                                            (@Eq.{1} Nat d.work
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                                                (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                                            (And (@Eq.{1} Bool d.halted Bool.false)
                                              (And
                                                (@Eq.{1} Nat
                                                  (d.natReg
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                  (c.natReg
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                                                (And
                                                  (@Eq.{1} Nat
                                                    (d.natReg
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                                    (c.natReg
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                  (And
                                                    (@Eq.{1} Nat
                                                      (d.natReg
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                                                      (c.natReg
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                                                    (@Eq.{1} Real
                                                      (d.realReg
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                                                      (c.realReg
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 7)
                                                          (instOfNatNat (nat_lit 7))))))))))))) ∧ (∀ (width offset returnPC start : Nat) (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) width →
    (∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
        @Membership.mem.{0, 0} DecrAlmostLinearSSSP.Decremental.Instruction
            (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
            (@List.instMembership.{0} DecrAlmostLinearSSSP.Decremental.Instruction) code ins →
          @LE.le.{0} Nat instLENat
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (DecrAlmostLinearSSSP.Decremental.naturalConstant ins)
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            width) →
      ∀ (pc slot : Nat) (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
        @LT.lt.{0} Nat instLTNat slot width →
          @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
              (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                DecrAlmostLinearSSSP.Decremental.Instruction
                (fun as i =>
                  @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) code pc)
              (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins) →
            @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
              (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                DecrAlmostLinearSSSP.Decremental.Instruction
                (fun as i =>
                  @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                (DecrAlmostLinearSSSP.Decremental.shadowCodeAux width offset returnPC start code)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) width pc) slot))
              (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                DecrAlmostLinearSSSP.Decremental.Instruction
                (fun as i =>
                  @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                (DecrAlmostLinearSSSP.Decremental.shadowBlock width offset returnPC
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start pc) ins)
                slot))) ∧ ((∀ (offset returnPC : Nat) (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (pc slot : Nat)
  (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
  @LT.lt.{0} Nat instLTNat slot (DecrAlmostLinearSSSP.Decremental.shadowWidth code) →
    @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
          DecrAlmostLinearSSSP.Decremental.Instruction
          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) code pc)
        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins) →
      @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
          DecrAlmostLinearSSSP.Decremental.Instruction
          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (DecrAlmostLinearSSSP.Decremental.shadowCode offset returnPC code)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (DecrAlmostLinearSSSP.Decremental.shadowWidth code) pc)
            slot))
        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
          DecrAlmostLinearSSSP.Decremental.Instruction
          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (DecrAlmostLinearSSSP.Decremental.shadowBlock (DecrAlmostLinearSSSP.Decremental.shadowWidth code) offset
            returnPC pc ins)
          slot)) ∧ ((∀ (width offset returnPC pc : Nat) (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
  And
    (@Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
      (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
        DecrAlmostLinearSSSP.Decremental.Instruction
        (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
        (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (DecrAlmostLinearSSSP.Decremental.shadowBlock width offset returnPC pc ins)
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
        (DecrAlmostLinearSSSP.Decremental.Instruction.natural
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pc
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
      (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
        DecrAlmostLinearSSSP.Decremental.Instruction
        (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
        (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (DecrAlmostLinearSSSP.Decremental.shadowBlock width offset returnPC pc ins)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
        (DecrAlmostLinearSSSP.Decremental.Instruction.nadd (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) ∧ (∀ (width offset returnPC pc d q j : Nat),
  @LT.lt.{0} Nat instLTNat j q →
    @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
      (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
        DecrAlmostLinearSSSP.Decremental.Instruction
        (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
        (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (DecrAlmostLinearSSSP.Decremental.shadowBlock width offset returnPC pc
          (DecrAlmostLinearSSSP.Decremental.Instruction.natural d q))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j))
      (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
        (DecrAlmostLinearSSSP.Decremental.Instruction.nadd (DecrAlmostLinearSSSP.Decremental.shadowReg d)
          (DecrAlmostLinearSSSP.Decremental.shadowReg d) (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))))))))) ∧ (((((∀ (width offset returnPC pc d q : Nat),
  @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
    (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
      DecrAlmostLinearSSSP.Decremental.Instruction
      (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
      (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
      (DecrAlmostLinearSSSP.Decremental.shadowBlock width offset returnPC pc
        (DecrAlmostLinearSSSP.Decremental.Instruction.natural d q))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) q
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
      (DecrAlmostLinearSSSP.Decremental.Instruction.jump
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) width
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pc
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))) ∧ (∀ (ins tr : DecrAlmostLinearSSSP.Decremental.Instruction),
  @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
      (DecrAlmostLinearSSSP.Decremental.shadowScalarTranslation ins)
      (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction tr) →
    ∀ (g : DecrAlmostLinearSSSP.Decremental.Machine),
      And (@Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.instructionEffect ins g).pc g.pc)
        (@Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.instructionEffect ins g).halted g.halted))) ∧ ((∀ (ins tr : DecrAlmostLinearSSSP.Decremental.Instruction) (a : Nat),
  @Eq.{1} (Option.{0} (Prod.{0, 0} DecrAlmostLinearSSSP.Decremental.Instruction Nat))
      (DecrAlmostLinearSSSP.Decremental.shadowMemoryTranslation ins)
      (@Option.some.{0} (Prod.{0, 0} DecrAlmostLinearSSSP.Decremental.Instruction Nat)
        (@Prod.mk.{0, 0} DecrAlmostLinearSSSP.Decremental.Instruction Nat tr a)) →
    ∀ (g : DecrAlmostLinearSSSP.Decremental.Machine),
      And (@Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.instructionEffect ins g).pc g.pc)
        (@Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.instructionEffect ins g).halted g.halted)) ∧ (∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    ∀ (host : DecrAlmostLinearSSSP.Decremental.Program) (width offset returnPC : Nat),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) width →
        @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) F →
          ∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
            @LE.le.{0} Nat instLENat
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (DecrAlmostLinearSSSP.Decremental.naturalConstant ins)
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                width →
              @Eq.{1} Bool c.halted Bool.false →
                @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                  @Eq.{1} Bool g.halted Bool.false →
                    @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) base →
                      @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) F →
                        @Eq.{1} Real (c.realReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                            (@Nat.cast.{0} Real Real.instNatCast F) →
                          @Eq.{1} Nat c.pc
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) width g.pc)) →
                            (∀ (slot : Nat),
                                @LT.lt.{0} Nat instLTNat slot width →
                                  @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                                    (@GetElem?.getElem?.{0, 0, 0}
                                      (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                                      DecrAlmostLinearSSSP.Decremental.Instruction
                                      (fun as i =>
                                        @LT.lt.{0} Nat instLTNat i
                                          (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                                      (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                                      host.code
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc slot))
                                    (@GetElem?.getElem?.{0, 0, 0}
                                      (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                                      DecrAlmostLinearSSSP.Decremental.Instruction
                                      (fun as i =>
                                        @LT.lt.{0} Nat instLTNat i
                                          (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                                      (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                                      (DecrAlmostLinearSSSP.Decremental.shadowBlock width offset returnPC g.pc ins)
                                      slot)) →
                              ∃ steps d,
                                And (@LE.le.{0} Nat instLENat steps width)
                                  (And
                                    (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                                      (DecrAlmostLinearSSSP.Decremental.execute host c steps) d)
                                    (And
                                      (DecrAlmostLinearSSSP.Decremental.ShadowRep base F d
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
                                      (And
                                        (@Eq.{1} Nat d.pc
                                          (DecrAlmostLinearSSSP.Decremental.shadowDestination width offset returnPC
                                            (DecrAlmostLinearSSSP.Decremental.instructionEffect ins
                                              {
                                                pc :=
                                                  @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.pc
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))),
                                                realReg := g.realReg, natReg := g.natReg, realMem := g.realMem,
                                                natMem := g.natMem, halted := g.halted, fault := g.fault,
                                                work :=
                                                  @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.work
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) })))
                                        (And
                                          (@Eq.{1} Nat d.work
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                                              steps))
                                          (And (@Eq.{1} Bool d.halted Bool.false)
                                            (And
                                              (@Eq.{1} Nat
                                                (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                (c.natReg
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                                              (And
                                                (@Eq.{1} Nat
                                                  (d.natReg
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                                  (c.natReg
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                (And
                                                  (@Eq.{1} Nat
                                                    (d.natReg
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                                                    (c.natReg
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                                                  (And
                                                    (@Eq.{1} Real
                                                      (d.realReg
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                                                      (c.realReg
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                                                    (@Eq.{1} Nat steps
                                                      (DecrAlmostLinearSSSP.Decremental.shadowSteps ins g)))))))))))))) ∧ (((∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    ∀ (host guest : DecrAlmostLinearSSSP.Decremental.Program) (width offset returnPC : Nat),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) width →
        (∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
            @Membership.mem.{0, 0} DecrAlmostLinearSSSP.Decremental.Instruction
                (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                (@List.instMembership.{0} DecrAlmostLinearSSSP.Decremental.Instruction) guest.code ins →
              @LE.le.{0} Nat instLENat
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (DecrAlmostLinearSSSP.Decremental.naturalConstant ins)
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                width) →
          DecrAlmostLinearSSSP.Decremental.ShadowEmbedsCode host guest width offset returnPC →
            @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) F →
              @Eq.{1} Bool c.halted Bool.false →
                @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                  @Eq.{1} Bool g.halted Bool.false →
                    @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) base →
                      @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) F →
                        @Eq.{1} Real (c.realReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                            (@Nat.cast.{0} Real Real.instNatCast F) →
                          @Eq.{1} Nat c.pc
                              (DecrAlmostLinearSSSP.Decremental.shadowDestination width offset returnPC g) →
                            ∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
                              @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                                  (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                                    Nat DecrAlmostLinearSSSP.Decremental.Instruction
                                    (fun as i =>
                                      @LT.lt.{0} Nat instLTNat i
                                        (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                                    (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                                    guest.code g.pc)
                                  (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins) →
                                ∃ steps d,
                                  And (@LE.le.{0} Nat instLENat steps width)
                                    (And
                                      (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                                        (DecrAlmostLinearSSSP.Decremental.execute host c steps) d)
                                      (And
                                        (DecrAlmostLinearSSSP.Decremental.ShadowRep base F d
                                          (DecrAlmostLinearSSSP.Decremental.step guest g))
                                        (And
                                          (@Eq.{1} Nat d.pc
                                            (DecrAlmostLinearSSSP.Decremental.shadowDestination width offset returnPC
                                              (DecrAlmostLinearSSSP.Decremental.step guest g)))
                                          (And
                                            (@Eq.{1} Nat d.work
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                                                steps))
                                            (And (@Eq.{1} Bool d.halted Bool.false)
                                              (And
                                                (@Eq.{1} Nat
                                                  (d.natReg
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                  (c.natReg
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                                                (And
                                                  (@Eq.{1} Nat
                                                    (d.natReg
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                                    (c.natReg
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                  (And
                                                    (@Eq.{1} Nat
                                                      (d.natReg
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                                                      (c.natReg
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                                                    (@Eq.{1} Real
                                                      (d.realReg
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                                                      (c.realReg
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 7)
                                                          (instOfNatNat (nat_lit 7)))))))))))))) ∧ (∀ (host guest : DecrAlmostLinearSSSP.Decremental.Program) (width offset returnPC : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) width →
    (∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
        @Membership.mem.{0, 0} DecrAlmostLinearSSSP.Decremental.Instruction
            (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
            (@List.instMembership.{0} DecrAlmostLinearSSSP.Decremental.Instruction) guest.code ins →
          @LE.le.{0} Nat instLENat
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (DecrAlmostLinearSSSP.Decremental.naturalConstant ins)
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            width) →
      DecrAlmostLinearSSSP.Decremental.ShadowEmbedsCode host guest width offset returnPC →
        ∀ (base F : Nat),
          @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) F →
            ∀ (t : Nat) (c g : DecrAlmostLinearSSSP.Decremental.Machine),
              DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
                @Eq.{1} Bool c.halted Bool.false →
                  @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                    @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) base →
                      @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) F →
                        @Eq.{1} Real (c.realReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                            (@Nat.cast.{0} Real Real.instNatCast F) →
                          @Eq.{1} Nat c.pc
                              (DecrAlmostLinearSSSP.Decremental.shadowDestination width offset returnPC g) →
                            (∀ (j : Nat),
                                @LT.lt.{0} Nat instLTNat j t →
                                  @Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.execute guest g j).halted Bool.false →
                                    ∃ ins,
                                      @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                                        (@GetElem?.getElem?.{0, 0, 0}
                                          (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                                          DecrAlmostLinearSSSP.Decremental.Instruction
                                          (fun as i =>
                                            @LT.lt.{0} Nat instLTNat i
                                              (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                                          (@List.instGetElem?NatLtLength.{0}
                                            DecrAlmostLinearSSSP.Decremental.Instruction)
                                          guest.code (DecrAlmostLinearSSSP.Decremental.execute guest g j).pc)
                                        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins)) →
                              ∃ steps d,
                                And
                                  (@LE.le.{0} Nat instLENat steps
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) width t))
                                  (And
                                    (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                                      (DecrAlmostLinearSSSP.Decremental.execute host c steps) d)
                                    (And
                                      (DecrAlmostLinearSSSP.Decremental.ShadowRep base F d
                                        (DecrAlmostLinearSSSP.Decremental.execute guest g t))
                                      (And
                                        (@Eq.{1} Nat d.pc
                                          (DecrAlmostLinearSSSP.Decremental.shadowDestination width offset returnPC
                                            (DecrAlmostLinearSSSP.Decremental.execute guest g t)))
                                        (And
                                          (@Eq.{1} Nat d.work
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                                              steps))
                                          (And (@Eq.{1} Bool d.halted Bool.false)
                                            (And
                                              (@Eq.{1} Nat
                                                (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                (c.natReg
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                                              (And
                                                (@Eq.{1} Nat
                                                  (d.natReg
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                                  (c.natReg
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                (And
                                                  (@Eq.{1} Nat
                                                    (d.natReg
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                                                    (c.natReg
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                                                  (@Eq.{1} Real
                                                    (d.realReg
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                                                    (c.realReg
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 7)
                                                        (instOfNatNat (nat_lit 7))))))))))))))) ∧ ((∀ (host guest : DecrAlmostLinearSSSP.Decremental.Program) (offset returnPC : Nat),
  DecrAlmostLinearSSSP.Decremental.ShadowEmbedsCode host guest (DecrAlmostLinearSSSP.Decremental.shadowWidth guest.code)
      offset returnPC →
    ∀ (base F : Nat),
      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) F →
        ∀ (c g final : DecrAlmostLinearSSSP.Decremental.Machine),
          DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
            @Eq.{1} Bool c.halted Bool.false →
              @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) base →
                  @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) F →
                    @Eq.{1} Real (c.realReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                        (@Nat.cast.{0} Real Real.instNatCast F) →
                      @Eq.{1} Nat c.pc
                          (DecrAlmostLinearSSSP.Decremental.shadowDestination
                            (DecrAlmostLinearSSSP.Decremental.shadowWidth guest.code) offset returnPC g) →
                        DecrAlmostLinearSSSP.Decremental.Ends guest g final →
                          ∃ steps d,
                            And
                              (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                                (DecrAlmostLinearSSSP.Decremental.execute host c steps) d)
                              (And (DecrAlmostLinearSSSP.Decremental.ShadowRep base F d final)
                                (And (@Eq.{1} Nat d.pc returnPC)
                                  (And
                                    (@LE.le.{0} Nat instLENat d.work
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (DecrAlmostLinearSSSP.Decremental.shadowWidth guest.code)
                                          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) final.work
                                            g.work))))
                                    (And (@Eq.{1} Bool d.halted Bool.false)
                                      (And
                                        (@Eq.{1} Nat
                                          (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                          (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                                        (And
                                          (@Eq.{1} Nat
                                            (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                            (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                          (And
                                            (@Eq.{1} Nat
                                              (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                                              (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                                            (@Eq.{1} Real
                                              (d.realReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                                              (c.realReg
                                                (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))))))))))) ∧ ((∀ (width : Nat) (ins : DecrAlmostLinearSSSP.Decremental.Instruction) (g : DecrAlmostLinearSSSP.Decremental.Machine),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) width →
    @LE.le.{0} Nat instLENat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (DecrAlmostLinearSSSP.Decremental.naturalConstant ins)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        width →
      @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.shadowSteps ins g) width) ∧ (∀ (width offset returnPC pc : Nat) (ins : DecrAlmostLinearSSSP.Decremental.Instruction)
  (g : DecrAlmostLinearSSSP.Decremental.Machine),
  Not (DecrAlmostLinearSSSP.Decremental.IsBranch ins) →
    ∀ (slot : Nat),
      @LT.lt.{0} Nat instLTNat slot
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
            (DecrAlmostLinearSSSP.Decremental.shadowSteps ins g)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
        ∃ tr,
          And
            (@Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
              (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                DecrAlmostLinearSSSP.Decremental.Instruction
                (fun as i =>
                  @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                (DecrAlmostLinearSSSP.Decremental.shadowBlock width offset returnPC pc ins) slot)
              (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction tr))
            (DecrAlmostLinearSSSP.Decremental.Straight tr)))))) ∧ ((((∀ (host : DecrAlmostLinearSSSP.Decremental.Program) (c g : DecrAlmostLinearSSSP.Decremental.Machine)
  (width offset returnPC : Nat) (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) width →
    @LE.le.{0} Nat instLENat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (DecrAlmostLinearSSSP.Decremental.naturalConstant ins)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        width →
      Not (DecrAlmostLinearSSSP.Decremental.IsBranch ins) →
        @Eq.{1} Bool c.halted Bool.false →
          (∀ (slot : Nat),
              @LT.lt.{0} Nat instLTNat slot width →
                @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                  (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                    DecrAlmostLinearSSSP.Decremental.Instruction
                    (fun as i =>
                      @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                    (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc slot))
                  (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                    DecrAlmostLinearSSSP.Decremental.Instruction
                    (fun as i =>
                      @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                    (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                    (DecrAlmostLinearSSSP.Decremental.shadowBlock width offset returnPC g.pc ins) slot)) →
            ∀ (j : Nat),
              @LT.lt.{0} Nat instLTNat j (DecrAlmostLinearSSSP.Decremental.shadowSteps ins g) →
                And
                  (@Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.execute host c j).pc
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc j))
                  (And (@Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.execute host c j).halted Bool.false)
                    (@Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.execute host c j).work
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work j)))) ∧ (∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    ∀ (host : DecrAlmostLinearSSSP.Decremental.Program) (width : Nat),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) width →
        @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) F →
          ∀ (natural : Bool) (a b target : Nat),
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
                    @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                          DecrAlmostLinearSSSP.Decremental.Instruction
                          (fun as i =>
                            @LT.lt.{0} Nat instLTNat i
                              (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                          (DecrAlmostLinearSSSP.Decremental.branchInstruction natural
                            (DecrAlmostLinearSSSP.Decremental.shadowReg a)
                            (DecrAlmostLinearSSSP.Decremental.shadowReg b)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                              (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))) →
                      @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                          (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                            DecrAlmostLinearSSSP.Decremental.Instruction
                            (fun as i =>
                              @LT.lt.{0} Nat instLTNat i
                                (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                            (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                              (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))
                          (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                            (DecrAlmostLinearSSSP.Decremental.Instruction.natural
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) target)) →
                        ∀ (j : Nat),
                          @LT.lt.{0} Nat instLTNat j
                              (@ite.{1} Nat (DecrAlmostLinearSSSP.Decremental.branchTest natural g a b)
                                (Classical.propDecidable (DecrAlmostLinearSSSP.Decremental.branchTest natural g a b))
                                (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) →
                            ∃ slot,
                              And (@LT.lt.{0} Nat instLTNat slot width)
                                (@Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.execute host c j).pc
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc slot)))) ∧ ((∀ {base F : Nat} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowRep base F c g →
    ∀ (host : DecrAlmostLinearSSSP.Decremental.Program) (width offset returnPC : Nat),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) width →
        @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) F →
          ∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
            @LE.le.{0} Nat instLENat
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (DecrAlmostLinearSSSP.Decremental.naturalConstant ins)
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                width →
              @Eq.{1} Bool c.halted Bool.false →
                @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                  @Eq.{1} Nat c.pc
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) width g.pc)) →
                    (∀ (slot : Nat),
                        @LT.lt.{0} Nat instLTNat slot width →
                          @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                            (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                              DecrAlmostLinearSSSP.Decremental.Instruction
                              (fun as i =>
                                @LT.lt.{0} Nat instLTNat i
                                  (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                              (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc slot))
                            (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                              DecrAlmostLinearSSSP.Decremental.Instruction
                              (fun as i =>
                                @LT.lt.{0} Nat instLTNat i
                                  (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                              (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                              (DecrAlmostLinearSSSP.Decremental.shadowBlock width offset returnPC g.pc ins) slot)) →
                      ∀ (j : Nat),
                        @LT.lt.{0} Nat instLTNat j (DecrAlmostLinearSSSP.Decremental.shadowSteps ins g) →
                          ∃ slot,
                            And (@LT.lt.{0} Nat instLTNat slot width)
                              (@Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.execute host c j).pc
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc slot))) ∧ ((∀ (width offset returnPC pc : Nat) (ins tr : DecrAlmostLinearSSSP.Decremental.Instruction),
  @Membership.mem.{0, 0} DecrAlmostLinearSSSP.Decremental.Instruction
      (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
      (@List.instMembership.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
      (DecrAlmostLinearSSSP.Decremental.shadowBlock width offset returnPC pc ins) tr →
    DecrAlmostLinearSSSP.Decremental.ModifiesMemory tr → DecrAlmostLinearSSSP.Decremental.ModifiesMemory ins) ∧ (∀ (width offset returnPC pc a d slot : Nat),
  @LT.lt.{0} Nat instLTNat slot (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))) →
    ∀ (tr : DecrAlmostLinearSSSP.Decremental.Instruction),
      @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
            DecrAlmostLinearSSSP.Decremental.Instruction
            (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
            (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
            (DecrAlmostLinearSSSP.Decremental.shadowBlock width offset returnPC pc
              (DecrAlmostLinearSSSP.Decremental.Instruction.store a d))
            slot)
          (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction tr) →
        DecrAlmostLinearSSSP.Decremental.ModifiesMemory tr →
          And (@Eq.{1} Nat slot (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
            (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Instruction tr
              (DecrAlmostLinearSSSP.Decremental.Instruction.store
                (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                (DecrAlmostLinearSSSP.Decremental.shadowReg d))))))) ∧ (((∀ (width offset returnPC pc a d slot : Nat),
  @LT.lt.{0} Nat instLTNat slot (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))) →
    ∀ (tr : DecrAlmostLinearSSSP.Decremental.Instruction),
      @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
            DecrAlmostLinearSSSP.Decremental.Instruction
            (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
            (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
            (DecrAlmostLinearSSSP.Decremental.shadowBlock width offset returnPC pc
              (DecrAlmostLinearSSSP.Decremental.Instruction.storeN a d))
            slot)
          (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction tr) →
        DecrAlmostLinearSSSP.Decremental.ModifiesMemory tr →
          And (@Eq.{1} Nat slot (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
            (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Instruction tr
              (DecrAlmostLinearSSSP.Decremental.Instruction.storeN
                (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                (DecrAlmostLinearSSSP.Decremental.shadowReg d)))) ∧ (∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction) (c : DecrAlmostLinearSSSP.Decremental.Machine) (address : Nat),
  Not (DecrAlmostLinearSSSP.Decremental.ModifiesMemory ins) →
    Not (DecrAlmostLinearSSSP.Decremental.WritesAddress ins c address))) ∧ ((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine)
  (ins : DecrAlmostLinearSSSP.Decremental.Instruction) (address : Nat),
  @Eq.{1} Bool c.halted Bool.false →
    @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
          DecrAlmostLinearSSSP.Decremental.Instruction
          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code c.pc)
        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins) →
      Not (DecrAlmostLinearSSSP.Decremental.WritesAddress ins c address) →
        And (@Eq.{1} Real ((DecrAlmostLinearSSSP.Decremental.step p c).realMem address) (c.realMem address))
          (@Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.step p c).natMem address) (c.natMem address))) ∧ ((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (t address : Nat),
  (∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j t →
        ∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
          @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
              (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                DecrAlmostLinearSSSP.Decremental.Instruction
                (fun as i =>
                  @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code
                (DecrAlmostLinearSSSP.Decremental.execute p c j).pc)
              (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins) →
            Not
              (DecrAlmostLinearSSSP.Decremental.WritesAddress ins (DecrAlmostLinearSSSP.Decremental.execute p c j)
                address)) →
    And (@Eq.{1} Real ((DecrAlmostLinearSSSP.Decremental.execute p c t).realMem address) (c.realMem address))
      (@Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.execute p c t).natMem address) (c.natMem address))) ∧ (∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction) (c : DecrAlmostLinearSSSP.Decremental.Machine) (address : Nat),
  DecrAlmostLinearSSSP.Decremental.WritesAddress ins c address → DecrAlmostLinearSSSP.Decremental.ModifiesMemory ins)))))))) := by
  exact ⟨⟨⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Structured.loop_bounded,DecrAlmostLinearSSSP.Decremental.Structured.loop_amortized⟩,⟨DecrAlmostLinearSSSP.Decremental.Structured.eval_loop_stops,DecrAlmostLinearSSSP.Decremental.ScaledCeiling.initial_eval⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.ScaledCeiling.build_eval,DecrAlmostLinearSSSP.Decremental.ScaledCeiling.choose_eval⟩,⟨DecrAlmostLinearSSSP.Decremental.ScaledCeiling.greedy_eval,⟨DecrAlmostLinearSSSP.Decremental.ScaledCeiling.initial_invariant,DecrAlmostLinearSSSP.Decremental.ScaledCeiling.buildStep_fields⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.ScaledCeiling.buildStep_constants,DecrAlmostLinearSSSP.Decremental.ScaledCeiling.buildStep_invariant⟩,⟨DecrAlmostLinearSSSP.Decremental.ScaledCeiling.build_terminates,DecrAlmostLinearSSSP.Decremental.ScaledCeiling.greedyPrefix_fields⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.ScaledCeiling.greedyPrefix_constants,DecrAlmostLinearSSSP.Decremental.ScaledCeiling.chooseStep_constants⟩,⟨DecrAlmostLinearSSSP.Decremental.ScaledCeiling.chooseStep_fields,⟨DecrAlmostLinearSSSP.Decremental.ScaledCeiling.greedyStep_invariant,DecrAlmostLinearSSSP.Decremental.ScaledCeiling.greedy_terminates⟩⟩⟩⟩⟩,⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.ScaledCeiling.greedy_output,DecrAlmostLinearSSSP.Decremental.ScaledCeiling.routine_correct⟩,⟨DecrAlmostLinearSSSP.Decremental.ScaledCeiling.routine_ends,DecrAlmostLinearSSSP.Decremental.repeated_nadd⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.constantProductCode_length,DecrAlmostLinearSSSP.Decremental.constant_product_run⟩,⟨DecrAlmostLinearSSSP.Decremental.shadowBlock_length,⟨DecrAlmostLinearSSSP.Decremental.source_constant_bound,DecrAlmostLinearSSSP.Decremental.shadowWidth_positive⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.shadowCodeAux_length,DecrAlmostLinearSSSP.Decremental.shadowCode_length⟩,⟨DecrAlmostLinearSSSP.Decremental.ShadowRep.header,⟨DecrAlmostLinearSSSP.Decremental.ShadowRep.scalar_step,DecrAlmostLinearSSSP.Decremental.ShadowRep.jump_step⟩⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.ShadowRep.constant_run,DecrAlmostLinearSSSP.Decremental.shadowBlock_reserved⟩,⟨DecrAlmostLinearSSSP.Decremental.shadowCodeAux_reserved,⟨DecrAlmostLinearSSSP.Decremental.write_preserves_other_bank,DecrAlmostLinearSSSP.Decremental.write_preserves_host_bank⟩⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.write_preserves_public_prefix,DecrAlmostLinearSSSP.Decremental.shadowScalar_reserved⟩,⟨DecrAlmostLinearSSSP.Decremental.host_shadow_scalar,DecrAlmostLinearSSSP.Decremental.shadow_simple_macro⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.shadow_jump_macro,DecrAlmostLinearSSSP.Decremental.shadow_halt_macro⟩,⟨DecrAlmostLinearSSSP.Decremental.host_shadow_branch,⟨DecrAlmostLinearSSSP.Decremental.shadow_branch_macro,DecrAlmostLinearSSSP.Decremental.shadow_natural_macro⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.shadow_cast_run,DecrAlmostLinearSSSP.Decremental.shadow_cast_macro⟩,⟨DecrAlmostLinearSSSP.Decremental.shadow_address_run,⟨DecrAlmostLinearSSSP.Decremental.shadowMemory_reserved,DecrAlmostLinearSSSP.Decremental.host_shadow_memory⟩⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.shadow_memory_macro,DecrAlmostLinearSSSP.Decremental.shadowCodeAux_get⟩,⟨DecrAlmostLinearSSSP.Decremental.shadowCode_get,⟨DecrAlmostLinearSSSP.Decremental.shadowBlock_header,DecrAlmostLinearSSSP.Decremental.shadowBlock_natural_add⟩⟩⟩⟩⟩,⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.shadowBlock_natural_jump,DecrAlmostLinearSSSP.Decremental.shadowScalar_control⟩,⟨DecrAlmostLinearSSSP.Decremental.shadowMemory_control,DecrAlmostLinearSSSP.Decremental.shadow_macro⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.shadow_single_step,DecrAlmostLinearSSSP.Decremental.shadow_execution⟩,⟨DecrAlmostLinearSSSP.Decremental.shadow_ends,⟨DecrAlmostLinearSSSP.Decremental.shadowSteps_bound,DecrAlmostLinearSSSP.Decremental.shadow_body_straight⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.shadow_nonbranch_prefix,DecrAlmostLinearSSSP.Decremental.shadow_branch_residence⟩,⟨DecrAlmostLinearSSSP.Decremental.shadow_residence,⟨DecrAlmostLinearSSSP.Decremental.shadowBlock_memory_origin,DecrAlmostLinearSSSP.Decremental.shadowBlock_store_slot⟩⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.shadowBlock_storeN_slot,DecrAlmostLinearSSSP.Decremental.no_address_write_of_no_memory⟩,⟨DecrAlmostLinearSSSP.Decremental.step_address_frame,⟨DecrAlmostLinearSSSP.Decremental.execute_address_frame,DecrAlmostLinearSSSP.Decremental.memory_of_write⟩⟩⟩⟩⟩⟩⟩
