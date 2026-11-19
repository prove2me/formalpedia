-- Prove2me | solution 1 for DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T11:14:36.896252+00:00
-- url     : https://prove2.me/submissions/26a6ca98-edc9-4401-bdb0-c6dc022ff0a4

import Definitions.Def_DecrAlmostLinearSSSP_RAMFoundation
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_1
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
theorem DecrAlmostLinearSSSP.Decremental.execute_halted : ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine),
  @Eq.{1} Bool c.halted Bool.true →
    ∀ (t : Nat), @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine (DecrAlmostLinearSSSP.Decremental.execute p c t) c := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_1.2.2.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.execute_succ_front : ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (t : Nat),
  @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
    (DecrAlmostLinearSSSP.Decremental.execute p c
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (DecrAlmostLinearSSSP.Decremental.execute p (DecrAlmostLinearSSSP.Decremental.step p c) t) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_1.2.2.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.embedded_execution : ∀ (host guest : DecrAlmostLinearSSSP.Decremental.Program) (offset returnPC : Nat),
  DecrAlmostLinearSSSP.Decremental.EmbedsCode host guest offset returnPC →
    ∀ (t : Nat) (c : DecrAlmostLinearSSSP.Decremental.Machine),
      @Eq.{1} Bool c.halted Bool.false →
        @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
          @Eq.{1} Nat c.pc
              (DecrAlmostLinearSSSP.Decremental.embeddedDestination offset returnPC
                (DecrAlmostLinearSSSP.Decremental.decodeGuest c)) →
            (∀ (j : Nat),
                @LT.lt.{0} Nat instLTNat j t →
                  @Eq.{1} Bool
                      (DecrAlmostLinearSSSP.Decremental.execute guest (DecrAlmostLinearSSSP.Decremental.decodeGuest c)
                          j).halted
                      Bool.false →
                    ∃ ins,
                      @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                          DecrAlmostLinearSSSP.Decremental.Instruction
                          (fun as i =>
                            @LT.lt.{0} Nat instLTNat i
                              (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) guest.code
                          (DecrAlmostLinearSSSP.Decremental.execute guest
                              (DecrAlmostLinearSSSP.Decremental.decodeGuest c) j).pc)
                        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins)) →
              ∃ steps d,
                And
                  (@LE.le.{0} Nat instLENat steps
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))) t))
                  (And
                    (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                      (DecrAlmostLinearSSSP.Decremental.execute host c steps) d)
                    (And
                      (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine (DecrAlmostLinearSSSP.Decremental.decodeGuest d)
                        (DecrAlmostLinearSSSP.Decremental.execute guest (DecrAlmostLinearSSSP.Decremental.decodeGuest c)
                          t))
                      (And
                        (@Eq.{1} Nat d.pc
                          (DecrAlmostLinearSSSP.Decremental.embeddedDestination offset returnPC
                            (DecrAlmostLinearSSSP.Decremental.decodeGuest d)))
                        (And
                          (@Eq.{1} Nat d.work
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work steps))
                          (And (@Eq.{1} Bool d.halted Bool.false)
                            (And
                              (@Eq.{1} Nat (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                              (@Eq.{1} Nat (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_1.2.2.2.1.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.step_work : ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine),
  @Eq.{1} Bool c.halted Bool.false →
    @Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.step p c).work
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_1.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.step_of_halted : ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine),
  @Eq.{1} Bool c.halted Bool.true →
    @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine (DecrAlmostLinearSSSP.Decremental.step p c) c := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_1.2.2.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.step_work_mono : ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine),
  @LE.le.{0} Nat instLENat c.work (DecrAlmostLinearSSSP.Decremental.step p c).work := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_1.2.2.2.2.2.2.2
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
lemma execute_work_mono (p : Program) (c : Machine) (t : ℕ) : c.work ≤ (execute p c t).work := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [execute_add]
    exact ih.trans (step_work_mono p _)
lemma terminating_prefix (p : Program) (c : Machine) (t : ℕ)
    (hh : (execute p c t).halted = true) :
    ∃ r ≤ t, execute p c r = execute p c t ∧ r = (execute p c t).work - c.work := by
  induction t generalizing c with
  | zero => exact ⟨0, le_rfl, rfl, by change 0 = c.work - c.work; omega⟩
  | succ t ih =>
    by_cases hch : c.halted = true
    · rw [execute_halted p c hch] at hh ⊢
      exact ⟨0, Nat.zero_le _, rfl, by simp⟩
    · have hchfalse : c.halted = false := Bool.eq_false_iff.mpr hch
      rw [execute_succ_front] at hh
      obtain ⟨r, hr, heq, hw⟩ := ih (step p c) hh
      refine ⟨r + 1, by omega, ?_, ?_⟩
      · rw [execute_succ_front, heq, ← execute_succ_front]
      · rw [execute_succ_front]
        have hstep := step_work p c hchfalse
        have hmono := execute_work_mono p (step p c) t
        omega
lemma embedded_ends (host guest : Program) (offset returnPC : ℕ)
    (hcode : EmbedsCode host guest offset returnPC) (c final : Machine)
    (hh : c.halted = false) (hone : c.natReg 1 = 1)
    (hpos : c.pc = embeddedDestination offset returnPC (decodeGuest c))
    (he : Ends guest (decodeGuest c) final) :
    ∃ (steps : ℕ) (d : Machine), execute host c steps = d ∧ decodeGuest d = final ∧
      d.pc = returnPC ∧ d.work ≤ c.work + 7 * (final.work - (decodeGuest c).work) ∧
      d.halted = false ∧ d.natReg 0 = c.natReg 0 ∧ d.natReg 1 = c.natReg 1 := by
  obtain ⟨t, ht, hhalt, hfault⟩ := he
  have hhalt' : (execute guest (decodeGuest c) t).halted = true := by rwa [ht]
  obtain ⟨r, _, hr, hw⟩ := terminating_prefix guest (decodeGuest c) t hhalt'
  have hrfinal : execute guest (decodeGuest c) r = final := hr.trans ht
  have hrfault : (execute guest (decodeGuest c) r).fault = false := by rwa [hrfinal]
  obtain ⟨s, d, hs, hd, hdec, hdpc, hdw, hdh, hd0, hd1⟩ :=
    embedded_execution host guest offset returnPC hcode r c hh hone hpos
      (execution_valid_code guest (decodeGuest c) r hrfault)
  refine ⟨s, d, hd, hdec.trans hrfinal, ?_, ?_, hdh, hd0, hd1⟩
  · rw [hdpc, hdec, hrfinal]
    simp [embeddedDestination, hhalt]
  · rw [ht] at hw
    omega
end DecrAlmostLinearSSSP.Decremental
end s16
section s17
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma step_straight (p : Program) (c : Machine) (ins : Instruction)
    (hh : c.halted = false) (hc : p.code[c.pc]? = some ins) (hs : Straight ins) :
    (step p c).pc = c.pc + 1 ∧ (step p c).halted = false ∧ (step p c).work = c.work + 1 := by
  cases ins <;> simp only [Straight] at hs
  all_goals try contradiction
  all_goals simp only [step,hh,Bool.false_eq_true,if_false,hc,and_self]
lemma straight_prefix (p : Program) (c : Machine) (n : ℕ) (hh : c.halted = false)
    (hcode : ∀ j < n, ∃ ins, p.code[c.pc+j]? = some ins ∧ Straight ins) :
    ∀ j ≤ n, (execute p c j).pc = c.pc+j ∧ (execute p c j).halted = false ∧
      (execute p c j).work = c.work+j := by
  intro j hj
  induction j with
  | zero => exact ⟨rfl,hh,rfl⟩
  | succ j ih =>
    obtain ⟨hpc,hhalt,hwork⟩ := ih (by omega)
    obtain ⟨ins,hins,hstraight⟩ := hcode j (by omega)
    have hc : p.code[(execute p c j).pc]? = some ins := by rwa [hpc]
    have hs := step_straight p (execute p c j) ins hhalt hc hstraight
    rw [execute_add]
    change (step p (execute p c j)).pc = _ ∧ (step p (execute p c j)).halted = _ ∧ (step p (execute p c j)).work = _
    rw [hs.1,hs.2.1,hs.2.2,hpc,hwork]
    exact ⟨rfl,rfl,rfl⟩
lemma step_memory_frame (p : Program) (c : Machine) (ins : Instruction)
    (hh : c.halted = false) (hc : p.code[c.pc]? = some ins) (hs : ¬ ModifiesMemory ins) :
    (step p c).realMem = c.realMem ∧ (step p c).natMem = c.natMem := by
  cases ins <;> simp only [ModifiesMemory] at hs
  all_goals try contradiction
  all_goals simp only [step,hh,Bool.false_eq_true,if_false,hc]
  all_goals try trivial
  all_goals split_ifs <;> simp
lemma execute_memory_frame (p : Program) (c : Machine) (t : ℕ)
    (hcode : ∀ j < t, ∀ ins, p.code[(execute p c j).pc]? = some ins → ¬ ModifiesMemory ins) :
    (execute p c t).realMem = c.realMem ∧ (execute p c t).natMem = c.natMem := by
  induction t with
  | zero => exact ⟨rfl,rfl⟩
  | succ t ih =>
    have hi := ih (fun j hj ins hc => hcode j (by omega) ins hc)
    rw [execute_add]
    change (step p (execute p c t)).realMem = c.realMem ∧ (step p (execute p c t)).natMem = c.natMem
    by_cases hh : (execute p c t).halted = true
    · rwa [step_of_halted p _ hh]
    · have hhfalse := Bool.eq_false_iff.mpr hh
      cases hc : p.code[(execute p c t).pc]? with
      | none => simpa only [step,hhfalse,Bool.false_eq_true,if_false,hc] using hi
      | some ins =>
        have hs := step_memory_frame p _ ins hhfalse hc (hcode t (by omega) ins hc)
        exact ⟨hs.1.trans hi.1,hs.2.trans hi.2⟩
end DecrAlmostLinearSSSP.Decremental
end s17
section s18
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
attribute [local instance] Classical.propDecidable
lemma compile_length (c : Cmd) (start : ℕ) : (compile c start).length = codeSize c := by
  induction c generalizing start with
  | skip => rfl
  | atom a => rfl
  | seq a b iha ihb => simp only [compile,List.length_append,iha,ihb,codeSize]
  | branch test yes no ihy ihn => simp [compile,ihy,ihn,codeSize] <;> omega
  | loop test body ih => simp [compile,ih,codeSize] <;> omega
lemma atom_step (p : Program) (c : Machine) (a : Atom)
    (hh : c.halted = false) (hc : p.code[c.pc]? = some a.instruction) :
    data (step p c) = a.effect (data c) ∧ (step p c).pc = c.pc+1 ∧
      (step p c).halted = false ∧ (step p c).work = c.work+1 := by
  refine ⟨?_,step_straight p c a.instruction hh hc a.straight⟩
  rw [step_eq_effect p c a.instruction hh hc]
  have ha := a.straight
  cases a with
  | mk ins hstraight =>
    cases ins <;> simp only [Straight] at hstraight
    all_goals try contradiction
    all_goals rfl
lemma test_step (p : Program) (c : Machine) (test : Test) (target : ℕ)
    (hh : c.halted = false) (hc : p.code[c.pc]? = some (test.emit target)) :
    data (step p c) = data c ∧
      (step p c).pc = (if test.holds (data c) then target else c.pc+1) ∧
      (step p c).halted = false ∧ (step p c).work = c.work+1 := by
  classical
  cases test with
  | realLess a b =>
    by_cases h : c.realReg a < c.realReg b
    all_goals simp [step,hh,hc,Test.holds,Test.emit,data,h]
  | natLess a b =>
    by_cases h : c.natReg a < c.natReg b
    all_goals simp [step,hh,hc,Test.holds,Test.emit,data,h]
end DecrAlmostLinearSSSP.Decremental.Structured
end s18
section s19
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact
open Structured
namespace Payload
lemma Image.frame {s t : Data} {items : List (ℕ × ℕ)} (h : Image s items)
    (hf : ∀ address ∈ footprint items, t.natMem address = s.natMem address) : Image t items := by
  induction items with
  | nil => trivial
  | cons item rest ih =>
    rcases item with ⟨address,value⟩
    refine ⟨?_,?_,ih h.2.2 ?_⟩
    · exact (hf address (Finset.mem_union_left _ (Finset.mem_Ico.mpr ⟨le_rfl,by omega⟩))).trans h.1
    · exact (hf (address+1) (Finset.mem_union_left _ (Finset.mem_Ico.mpr ⟨by omega,by omega⟩))).trans h.2.1
    · intro a ha;exact hf a (Finset.mem_union_right _ ha)
end Payload
lemma LocatedTrie.Image.frame {s t : Data} {height : ℕ} {tree : LocatedTrie height} (h : tree.Image s)
    (hf : ∀ address ∈ tree.footprint, t.natMem address = s.natMem address) : tree.Image t := by
  induction tree with
  | empty => trivial
  | leaf address items =>
    refine ⟨?_,?_,h.2.2.frame ?_⟩
    · exact (hf address (Finset.mem_union_left _ (Finset.mem_Ico.mpr ⟨le_rfl,by omega⟩))).trans h.1
    · exact (hf (address+3) (Finset.mem_union_left _ (Finset.mem_Ico.mpr ⟨by omega,by omega⟩))).trans h.2.1
    · intro a ha;exact hf a (Finset.mem_union_right _ ha)
  | node address left right ihl ihr =>
    refine ⟨?_,?_,?_,ihl h.2.2.2.1 ?_,ihr h.2.2.2.2 ?_⟩
    · exact (hf address (Finset.mem_union_left _ (Finset.mem_Ico.mpr ⟨le_rfl,by omega⟩))).trans h.1
    · exact (hf (address+1) (Finset.mem_union_left _ (Finset.mem_Ico.mpr ⟨by omega,by omega⟩))).trans h.2.1
    · exact (hf (address+2) (Finset.mem_union_left _ (Finset.mem_Ico.mpr ⟨by omega,by omega⟩))).trans h.2.2.1
    · intro a ha;exact hf a (Finset.mem_union_right _ (Finset.mem_union_left _ ha))
    · intro a ha;exact hf a (Finset.mem_union_right _ (Finset.mem_union_right _ ha))
lemma LocatedTrie.root_nonzero {height : ℕ} (tree : LocatedTrie height) (h : tree.Separated) :
    tree.root ≠ 0 ↔ tree ≠ .empty := by
  cases tree with
  | empty => simp [LocatedTrie.root]
  | leaf address items => simp [LocatedTrie.root,ne_of_gt h.1]
  | node address left right => simp [LocatedTrie.root,ne_of_gt h.1]
lemma LocatedTrie.Image.count {s : Data} {height : ℕ} {tree : LocatedTrie height}
    (h : tree.Image s) : tree.root ≠ 0 → s.natMem tree.root = RadixQueue.count tree.abstract := by
  cases tree with
  | empty => simp [LocatedTrie.root]
  | leaf address items => intro _;simpa only [LocatedTrie.root,LocatedTrie.abstract,RadixQueue.count,List.length_map] using h.1
  | node address left right => intro _;exact h.1
end DecrAlmostLinearSSSP.Decremental.Exact
end s19
section s20
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact
namespace LocatedTrie
lemma root_mem {height : ℕ} (tree : LocatedTrie height) (h : tree.root ≠ 0) : tree.root ∈ tree.footprint := by
  cases tree with
  | empty => exact False.elim (h rfl)
  | leaf address items | node address left right =>
    all_goals simp only [LocatedTrie.root,LocatedTrie.footprint]
    all_goals exact Finset.mem_union_left _ (Finset.mem_Ico.mpr ⟨le_rfl,by omega⟩)
lemma Bounded.root {height : ℕ} {tree : LocatedTrie height} {low high : ℕ}
    (h : tree.Bounded low high) (hne : tree.root ≠ 0) : low ≤ tree.root ∧ tree.root < high := h _ (root_mem tree hne)
lemma Bounded.mono {height : ℕ} {tree : LocatedTrie height} {low high low' high' : ℕ}
    (h : tree.Bounded low high) (hlow : low' ≤ low) (hhigh : high ≤ high') : tree.Bounded low' high' :=
  fun address ha => ⟨hlow.trans (h address ha).1,(h address ha).2.trans_le hhigh⟩
lemma node_field_mem {height : ℕ} (address : ℕ) (left right : LocatedTrie height) (offset : ℕ) (ho : offset < 4) :
    address+offset ∈ (LocatedTrie.node address left right).footprint :=
  Finset.mem_union_left _ (Finset.mem_Ico.mpr ⟨by omega,by omega⟩)
lemma leaf_field_mem (address : ℕ) (items : List (ℕ × ℕ)) (offset : ℕ) (ho : offset < 4) :
    address+offset ∈ (LocatedTrie.leaf address items).footprint :=
  Finset.mem_union_left _ (Finset.mem_Ico.mpr ⟨by omega,by omega⟩)
lemma node_left_subset {height : ℕ} (address : ℕ) (left right : LocatedTrie height) :
    left.footprint ⊆ (LocatedTrie.node address left right).footprint := by
  intro a ha;exact Finset.mem_union_right _ (Finset.mem_union_left _ ha)
lemma node_right_subset {height : ℕ} (address : ℕ) (left right : LocatedTrie height) :
    right.footprint ⊆ (LocatedTrie.node address left right).footprint := by
  intro a ha;exact Finset.mem_union_right _ (Finset.mem_union_right _ ha)
lemma leaf_payload_subset (address : ℕ) (items : List (ℕ × ℕ)) :
    Payload.footprint items ⊆ (LocatedTrie.leaf address items).footprint := by
  intro a ha;exact Finset.mem_union_right _ ha
lemma Separated.left_field {height : ℕ} {address : ℕ} {left right : LocatedTrie height}
    (h : (LocatedTrie.node address left right).Separated) (offset : ℕ) (ho : offset < 4) :
    address+offset ∉ left.footprint := by
  intro hm
  exact Finset.disjoint_left.mp h.2.1 (Finset.mem_Ico.mpr ⟨by omega,by omega⟩) (Finset.mem_union_left _ hm)
lemma Separated.right_field {height : ℕ} {address : ℕ} {left right : LocatedTrie height}
    (h : (LocatedTrie.node address left right).Separated) (offset : ℕ) (ho : offset < 4) :
    address+offset ∉ right.footprint := by
  intro hm
  exact Finset.disjoint_left.mp h.2.1 (Finset.mem_Ico.mpr ⟨by omega,by omega⟩) (Finset.mem_union_right _ hm)
end LocatedTrie
lemma disjoint_fresh_interval (old : Finset ℕ) (fresh length : ℕ) (h : ∀ address ∈ old, address < fresh) :
    Disjoint old (Finset.Ico fresh (fresh+length)) := by
  apply Finset.disjoint_left.mpr
  intro address ha hb
  have hh := (Finset.mem_Ico.mp hb).1
  have ht := h address ha
  omega
end DecrAlmostLinearSSSP.Decremental.Exact
end s20
section s21
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
lemma CodeAt.left {p : Program} {start : ℕ} {a b : List Instruction}
    (h : CodeAt p start (a++b)) : CodeAt p start a := by
  intro j hj
  rw [h j (by simp only [List.length_append];omega),List.getElem?_append_left hj]
lemma CodeAt.right {p : Program} {start : ℕ} {a b : List Instruction}
    (h : CodeAt p start (a++b)) : CodeAt p (start+a.length) b := by
  intro j hj
  have hh := h (a.length+j) (by simp only [List.length_append];omega)
  rw [List.getElem?_append_right (by omega)] at hh
  simpa only [Nat.add_sub_cancel_left,Nat.add_assoc] using hh
lemma CodeAt.head {p : Program} {start : ℕ} {ins : Instruction} {rest : List Instruction}
    (h : CodeAt p start (ins::rest)) : p.code[start]? = some ins := by
  simpa only [Nat.add_zero,List.getElem?_cons_zero] using h 0 (by simp)
lemma CodeAt.tail {p : Program} {start : ℕ} {ins : Instruction} {rest : List Instruction}
    (h : CodeAt p start (ins::rest)) : CodeAt p (start+1) rest := by
  intro j hj
  have hh := h (j+1) (by simp only [List.length_cons];omega)
  simpa only [List.getElem?_cons_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
lemma CodeAt.of_assembled (codePrefix code suffix : List Instruction) (p : Program)
    (hc : p.code = codePrefix++(code++suffix)) : CodeAt p codePrefix.length code := by
  intro j hj
  rw [hc,List.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left hj]
end DecrAlmostLinearSSSP.Decremental.Structured
end s21
section s22
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
lemma compile_seq_parts (p : Program) (start : ℕ) (a b : Cmd)
    (h : CodeAt p start (compile (.seq a b) start)) :
    CodeAt p start (compile a start) ∧ CodeAt p (start+codeSize a) (compile b (start+codeSize a)) := by
  exact ⟨CodeAt.left h,by simpa only [compile_length] using CodeAt.right h⟩
lemma compile_branch_parts (p : Program) (start : ℕ) (test : Test) (yes no : Cmd)
    (h : CodeAt p start (compile (.branch test yes no) start)) :
    p.code[start]? = some (test.emit (start+codeSize no+2)) ∧
      CodeAt p (start+1) (compile no (start+1)) ∧
      p.code[start+1+codeSize no]? = some (.jump (start+codeSize no+codeSize yes+2)) ∧
      CodeAt p (start+codeSize no+2) (compile yes (start+codeSize no+2)) := by
  change CodeAt p start (test.emit (start+codeSize no+2) ::
    (compile no (start+1) ++ (.jump (start+codeSize no+codeSize yes+2) :: compile yes (start+codeSize no+2)))) at h
  have ht := CodeAt.tail h
  have hr := CodeAt.right ht
  refine ⟨CodeAt.head h,CodeAt.left ht,?_,?_⟩
  · simpa only [compile_length] using CodeAt.head hr
  · simpa only [compile_length, show start+1+codeSize no+1 = start+codeSize no+2 by omega] using CodeAt.tail hr
lemma compile_loop_parts (p : Program) (start : ℕ) (test : Test) (body : Cmd)
    (h : CodeAt p start (compile (.loop test body) start)) :
    p.code[start]? = some (test.emit (start+2)) ∧
      p.code[start+1]? = some (.jump (start+codeSize body+3)) ∧
      CodeAt p (start+2) (compile body (start+2)) ∧
      p.code[start+2+codeSize body]? = some (.jump start) := by
  change CodeAt p start (test.emit (start+2) :: .jump (start+codeSize body+3) ::
    (compile body (start+2) ++ [.jump start])) at h
  have ht := CodeAt.tail h
  have hb := CodeAt.tail ht
  refine ⟨CodeAt.head h,CodeAt.head ht,CodeAt.left hb,?_⟩
  simpa only [compile_length] using CodeAt.head (CodeAt.right hb)
lemma data_clock (c : Machine) (pc work : ℕ) : data {c with pc := pc,work := work} = data c := rfl
lemma jump_step (p : Program) (c : Machine) (target : ℕ) (hh : c.halted = false)
    (hc : p.code[c.pc]? = some (.jump target)) :
    data (execute p c 1) = data c ∧ (execute p c 1).pc = target ∧
      (execute p c 1).halted = false ∧ (execute p c 1).work = c.work+1 := by
  rw [host_jump p c target hh hc]
  exact ⟨rfl,rfl,hh,rfl⟩
end DecrAlmostLinearSSSP.Decremental.Structured
end s22
section s23
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
lemma eval_compiles {cmd : Cmd} {s t : Data} {cost : ℕ} (he : Eval cmd s cost t) :
    ∀ (p : Program) (start : ℕ) (c : Machine), CodeAt p start (compile cmd start) →
      c.pc = start → data c = s → c.halted = false →
      data (execute p c cost) = t ∧ (execute p c cost).pc = start+codeSize cmd ∧
        (execute p c cost).halted = false ∧ (execute p c cost).work = c.work+cost := by
  classical
  induction he with
  | skip s =>
    intro p start c hcode hpc hdata hhalt
    exact ⟨hdata,by change c.pc = start;exact hpc,hhalt,rfl⟩
  | atom a s =>
    intro p start c hcode hpc hdata hhalt
    have hfetch : p.code[c.pc]? = some a.instruction := by rw [hpc];exact CodeAt.head hcode
    obtain ⟨hd,hp,hh,hw⟩ := atom_step p c a hhalt hfetch
    rw [hdata] at hd
    rw [hpc] at hp
    exact ⟨hd,hp,hh,hw⟩
  | @seq a b s t u ta tb ha hb iha ihb =>
    intro p start c hcode hpc hdata hhalt
    obtain ⟨hca,hcb⟩ := compile_seq_parts p start a b hcode
    obtain ⟨hda,hpa,hha,hwa⟩ := iha p start c hca hpc hdata hhalt
    obtain ⟨hdb,hpb,hhb,hwb⟩ := ihb p (start+codeSize a) (execute p c ta) hcb hpa hda hha
    rw [execute_add]
    refine ⟨hdb,?_,hhb,?_⟩
    · simpa only [codeSize,Nat.add_assoc] using hpb
    · rw [hwb,hwa,Nat.add_assoc]
  | @branchYes test yes no s t amount hcond he ih =>
    intro p start c hcode hpc hdata hhalt
    obtain ⟨hctest,hcno,hcjump,hcyes⟩ := compile_branch_parts p start test yes no hcode
    have hc : p.code[c.pc]? = some (test.emit (start+codeSize no+2)) := by rwa [hpc]
    obtain ⟨hd1,hp1,hh1,hw1⟩ := test_step p c test _ hhalt hc
    have htake : test.holds (data c) := by rwa [hdata]
    rw [if_pos htake] at hp1
    let c1 := step p c
    obtain ⟨hd2,hp2,hh2,hw2⟩ := ih p (start+codeSize no+2) c1 hcyes hp1 (hd1.trans hdata) hh1
    rw [show amount+1 = 1+amount by omega,execute_add]
    change data (execute p c1 amount) = _ ∧ (execute p c1 amount).pc = _ ∧
      (execute p c1 amount).halted = _ ∧ (execute p c1 amount).work = _
    refine ⟨hd2,?_,hh2,?_⟩
    · simp only [codeSize] at *
      omega
    · rw [hw2]
      change (step p c).work+amount = _
      rw [hw1]
      omega
  | @branchNo test yes no s t amount hcond he ih =>
    intro p start c hcode hpc hdata hhalt
    obtain ⟨hctest,hcno,hcjump,hcyes⟩ := compile_branch_parts p start test yes no hcode
    have hc : p.code[c.pc]? = some (test.emit (start+codeSize no+2)) := by rwa [hpc]
    obtain ⟨hd1,hp1,hh1,hw1⟩ := test_step p c test _ hhalt hc
    have htake : ¬test.holds (data c) := by rwa [hdata]
    rw [if_neg htake,hpc] at hp1
    let c1 := step p c
    obtain ⟨hd2,hp2,hh2,hw2⟩ := ih p (start+1) c1 hcno hp1 (hd1.trans hdata) hh1
    let c2 := execute p c1 amount
    have hc2 : p.code[c2.pc]? = some (.jump (start+codeSize no+codeSize yes+2)) := by rw [hp2];exact hcjump
    obtain ⟨hd3,hp3,hh3,hw3⟩ := jump_step p c2 _ hh2 hc2
    rw [show amount+2 = 1+(amount+1) by omega,execute_add,execute_add]
    change data (execute p c2 1) = _ ∧ (execute p c2 1).pc = _ ∧
      (execute p c2 1).halted = _ ∧ (execute p c2 1).work = _
    refine ⟨hd3.trans hd2,?_,hh3,?_⟩
    · simpa only [codeSize,Nat.add_assoc] using hp3
    · rw [hw3,hw2]
      change (step p c).work+amount+1 = _
      rw [hw1]
      omega
  | @loopNo test body s hcond =>
    intro p start c hcode hpc hdata hhalt
    obtain ⟨hctest,hcjump,hcbody,hcback⟩ := compile_loop_parts p start test body hcode
    have hc : p.code[c.pc]? = some (test.emit (start+2)) := by rwa [hpc]
    obtain ⟨hd1,hp1,hh1,hw1⟩ := test_step p c test _ hhalt hc
    have htake : ¬test.holds (data c) := by rwa [hdata]
    rw [if_neg htake,hpc] at hp1
    let c1 := step p c
    have hc1 : p.code[c1.pc]? = some (.jump (start+codeSize body+3)) := by rw [hp1];exact hcjump
    obtain ⟨hd2,hp2,hh2,hw2⟩ := jump_step p c1 _ hh1 hc1
    rw [show 2 = 1+1 by omega,execute_add]
    change data (execute p c1 1) = _ ∧ (execute p c1 1).pc = _ ∧
      (execute p c1 1).halted = _ ∧ (execute p c1 1).work = _
    refine ⟨hd2.trans (hd1.trans hdata),?_,hh2,?_⟩
    · simpa only [codeSize,Nat.add_assoc] using hp2
    · rw [hw2]
      change (step p c).work+1 = _
      rw [hw1]
  | @loopYes test body s t u first rest hcond he hloop ihbody ihloop =>
    intro p start c hcode hpc hdata hhalt
    obtain ⟨hctest,hcjump,hcbody,hcback⟩ := compile_loop_parts p start test body hcode
    have hc : p.code[c.pc]? = some (test.emit (start+2)) := by rwa [hpc]
    obtain ⟨hd1,hp1,hh1,hw1⟩ := test_step p c test _ hhalt hc
    have htake : test.holds (data c) := by rwa [hdata]
    rw [if_pos htake] at hp1
    let c1 := step p c
    obtain ⟨hd2,hp2,hh2,hw2⟩ := ihbody p (start+2) c1 hcbody hp1 (hd1.trans hdata) hh1
    let c2 := execute p c1 first
    have hc2 : p.code[c2.pc]? = some (.jump start) := by rw [hp2];exact hcback
    obtain ⟨hd3,hp3,hh3,hw3⟩ := jump_step p c2 start hh2 hc2
    let c3 := execute p c2 1
    obtain ⟨hd4,hp4,hh4,hw4⟩ := ihloop p start c3 hcode hp3 (hd3.trans hd2) hh3
    rw [show first+rest+2 = 1+(first+(1+rest)) by omega,execute_add,execute_add,execute_add]
    change data (execute p c3 rest) = _ ∧ (execute p c3 rest).pc = _ ∧
      (execute p c3 rest).halted = _ ∧ (execute p c3 rest).work = _
    refine ⟨hd4,hp4,hh4,?_⟩
    rw [hw4,hw3,hw2]
    change (step p c).work+first+1+rest = _
    rw [hw1]
    omega
end DecrAlmostLinearSSSP.Decremental.Structured
end s23
section s24
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma fault_well_formed_step (p : Program) (c : Machine) (hc : FaultWellFormed c) :
    FaultWellFormed (step p c) := by
  classical
  by_cases hh : c.halted = true
  · rw [step_of_halted p c hh]
    exact Or.inr hh
  · have hhalt : c.halted = false := Bool.eq_false_iff.mpr hh
    have hfault : c.fault = false := hc.resolve_right hh
    unfold step
    rw [hhalt]
    simp only [Bool.false_eq_true,if_false]
    cases hcode : p.code[c.pc]? with
    | none => exact Or.inr rfl
    | some ins =>
      cases ins <;> simp only [FaultWellFormed]
      all_goals try exact Or.inl hfault
      all_goals split_ifs <;> exact Or.inl hfault
lemma fault_well_formed_execute (p : Program) (c : Machine) (t : ℕ) (hc : FaultWellFormed c) :
    FaultWellFormed (execute p c t) := by
  induction t with
  | zero => exact hc
  | succ t ih =>
    rw [execute_add]
    exact fault_well_formed_step p _ ih
lemma running_execution_no_fault (p : Program) (c : Machine) (t : ℕ)
    (hc : c.fault = false) (hh : (execute p c t).halted = false) :
    (execute p c t).fault = false := by
  have hi := fault_well_formed_execute p c t (Or.inl hc)
  exact hi.resolve_right (by rw [hh]; decide)
end DecrAlmostLinearSSSP.Decremental
end s24
section s25
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
lemma ram_query_nine (p : Program)
    (h0 : p.code[p.query]? = some (.loadN 6 5))
    (h1 : p.code[p.query + 1]? = some (.load 1 5))
    (h2 : p.code[p.query + 2]? = some .halt)
    (c : Machine) (v : ℕ) :
    ∃ d, Ends p {resume c p.query with natReg := Function.update c.natReg 5 v} d ∧
      d.work + 6 ≤ c.work + 9 ∧ d.natReg 6 = c.natMem v ∧ d.realReg 1 = c.realMem v ∧
      d.realMem = c.realMem ∧ d.natMem = c.natMem := by
  classical
  let start : Machine := {resume c p.query with natReg := Function.update c.natReg 5 v}
  let c1 : Machine := { start with pc := p.query + 1, natReg := Function.update start.natReg 6 (c.natMem v), work := c.work + 1 }
  let c2 : Machine := { c1 with pc := p.query + 2, realReg := Function.update c.realReg 1 (c.realMem v), work := c.work + 2 }
  let finish : Machine := { c2 with pc := p.query + 3, halted := true, work := c.work + 3 }
  have hs1 : step p start = c1 := by
    simp [step, start, c1, resume, h0]
  have hs2 : step p c1 = c2 := by
    simp [step, start, c1, c2, resume, h1]
  have hs3 : step p c2 = finish := by
    simp [step, start, c1, c2, finish, resume, h2]
  have hex : execute p start 3 = finish := by
    change step p (step p (step p start)) = finish
    rw [hs1, hs2, hs3]
  refine ⟨finish, ⟨3, hex, rfl, rfl⟩, ?_, ?_, ?_, rfl, rfl⟩
  · change c.work + 3 + 6 ≤ c.work + 9
    omega
  · simp [finish, c2, c1, start]
  · simp [finish, c2]
end DecrAlmostLinearSSSP.Decremental
end s25
section s26
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
lemma program_init (init update : Cmd) : CodeAt (program init update) 0 (compile init 0) := by
  have h := CodeAt.of_assembled [] (compile init 0) (.halt :: (compile update (codeSize init+1) ++ [.halt,.loadN 6 5,.load 1 5,.halt]))
    (program init update) rfl
  exact h
lemma program_init_halt (init update : Cmd) : (program init update).code[codeSize init]? = some .halt := by
  change (compile init 0 ++ (.halt :: (compile update (codeSize init+1) ++ [.halt,.loadN 6 5,.load 1 5,.halt])))[codeSize init]? = _
  rw [List.getElem?_append_right (by rw [compile_length]),compile_length,Nat.sub_self]
  rfl
lemma program_update (init update : Cmd) :
    CodeAt (program init update) (codeSize init+1) (compile update (codeSize init+1)) := by
  have h := CodeAt.of_assembled (compile init 0 ++ [.halt]) (compile update (codeSize init+1))
    [.halt,.loadN 6 5,.load 1 5,.halt] (program init update) (by simp [program,List.append_assoc])
  simpa only [List.length_append,compile_length,List.length_singleton] using h
lemma program_update_halt (init update : Cmd) :
    (program init update).code[codeSize init+1+codeSize update]? = some .halt := by
  change (compile init 0 ++ (.halt :: (compile update (codeSize init+1) ++ [.halt,.loadN 6 5,.load 1 5,.halt])))[_]? = _
  rw [List.getElem?_append_right (by rw [compile_length];omega),compile_length]
  have hi : codeSize init+1+codeSize update-codeSize init = codeSize update+1 := by omega
  rw [hi,List.getElem?_cons_succ,List.getElem?_append_right (by rw [compile_length]),compile_length,Nat.sub_self]
  rfl
lemma program_query_code (init update : Cmd) :
    CodeAt (program init update) (program init update).query [.loadN 6 5,.load 1 5,.halt] := by
  let codePrefix := compile init 0 ++ [.halt] ++ compile update (codeSize init+1) ++ [.halt]
  have h := CodeAt.of_assembled codePrefix [.loadN 6 5,.load 1 5,.halt] [] (program init update)
    (by simp [codePrefix,program,List.append_assoc])
  have hlen : codePrefix.length = (program init update).query := by
    change codePrefix.length = codeSize init+codeSize update+2
    simp only [codePrefix,List.length_append,List.length_singleton,compile_length]
    omega
  rwa [hlen] at h
lemma program_query_nine (init update : Cmd) (c : Machine) (v : ℕ) :
    ∃ d,Ends (program init update) {resume c (program init update).query with natReg := Function.update c.natReg 5 v} d ∧
      d.work+6 ≤ c.work+9 ∧ d.natReg 6 = c.natMem v ∧ d.realReg 1 = c.realMem v ∧
      d.realMem = c.realMem ∧ d.natMem = c.natMem := by
  have h := program_query_code init update
  exact ram_query_nine (program init update) (CodeAt.head h) (CodeAt.head (CodeAt.tail h))
    (CodeAt.head (CodeAt.tail (CodeAt.tail h))) c v
lemma command_ends {cmd : Cmd} {s t : Data} {cost : ℕ} (he : Eval cmd s cost t)
    (p : Program) (start : ℕ) (c : Machine)
    (hcode : CodeAt p start (compile cmd start)) (hpc : c.pc = start) (hdata : data c = s)
    (hhalt : c.halted = false) (hfault : c.fault = false)
    (hend : p.code[start+codeSize cmd]? = some .halt) :
    ∃ d,Ends p c d ∧ data d = t ∧ d.work = c.work+cost+1 := by
  obtain ⟨hd,hp,hh,hw⟩ := eval_compiles he p start c hcode hpc hdata hhalt
  let b := execute p c cost
  have hbf : b.fault = false := running_execution_no_fault p c cost hfault hh
  let d : Machine := {b with pc := b.pc+1,work := b.work+1,halted := true}
  have hc : p.code[b.pc]? = some .halt := by rw [hp];exact hend
  have hs : step p b = d := by simp [step,d,show b.halted = false from hh,hc]
  refine ⟨d,⟨cost+1,?_,rfl,hbf⟩,hd,?_⟩
  · rw [execute_add]
    exact hs
  · change b.work+1 = c.work+cost+1
    rw [hw]
end DecrAlmostLinearSSSP.Decremental.Structured
end s26
section s27
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
lemma eval_natural (s : Data) (d q : ℕ) : Eval (natural d q) s 1 {s with natReg := Function.update s.natReg d q} := .atom _ _
lemma eval_rational (s : Data) (d : ℕ) (q : ℚ) : Eval (rational d q) s 1 {s with realReg := Function.update s.realReg d (q : ℝ)} := .atom _ _
lemma eval_cast (s : Data) (d a : ℕ) : Eval (cast d a) s 1 {s with realReg := Function.update s.realReg d (s.natReg a : ℝ)} := .atom _ _
lemma eval_add (s : Data) (d a b : ℕ) : Eval (add d a b) s 1 {s with realReg := Function.update s.realReg d (s.realReg a+s.realReg b)} := .atom _ _
lemma eval_sub (s : Data) (d a b : ℕ) : Eval (sub d a b) s 1 {s with realReg := Function.update s.realReg d (s.realReg a-s.realReg b)} := .atom _ _
lemma eval_mul (s : Data) (d a b : ℕ) : Eval (mul d a b) s 1 {s with realReg := Function.update s.realReg d (s.realReg a*s.realReg b)} := .atom _ _
lemma eval_div (s : Data) (d a b : ℕ) : Eval (div d a b) s 1 {s with realReg := Function.update s.realReg d (s.realReg a/s.realReg b)} := .atom _ _
lemma eval_nadd (s : Data) (d a b : ℕ) : Eval (nadd d a b) s 1 {s with natReg := Function.update s.natReg d (s.natReg a+s.natReg b)} := .atom _ _
lemma eval_nsub (s : Data) (d a b : ℕ) : Eval (nsub d a b) s 1 {s with natReg := Function.update s.natReg d (s.natReg a-s.natReg b)} := .atom _ _
lemma eval_load (s : Data) (d a : ℕ) : Eval (load d a) s 1 {s with realReg := Function.update s.realReg d (s.realMem (s.natReg a))} := .atom _ _
lemma eval_store (s : Data) (a d : ℕ) : Eval (store a d) s 1 {s with realMem := Function.update s.realMem (s.natReg a) (s.realReg d)} := .atom _ _
lemma eval_loadN (s : Data) (d a : ℕ) : Eval (loadN d a) s 1 {s with natReg := Function.update s.natReg d (s.natMem (s.natReg a))} := .atom _ _
lemma eval_storeN (s : Data) (a d : ℕ) : Eval (storeN a d) s 1 {s with natMem := Function.update s.natMem (s.natReg a) (s.natReg d)} := .atom _ _
lemma eval_sequence_atoms (atoms : List Atom) (s : Data) :
    Eval (sequence (atoms.map Cmd.atom)) s atoms.length (atoms.foldl (fun t a => a.effect t) s) := by
  induction atoms generalizing s with
  | nil => exact .skip s
  | cons a atoms ih =>
    have hh := Eval.seq (Eval.atom a s) (ih (a.effect s))
    simpa only [List.map_cons,sequence,List.length_cons,List.foldl_cons,Nat.add_comm] using hh
end DecrAlmostLinearSSSP.Decremental.Structured
end s27
section s28
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma step_nat_frame (p : Program) (c : Machine) (ins : Instruction) (k : ℕ)
    (hh : c.halted = false) (hc : p.code[c.pc]? = some ins) (hwrite : ¬ writesNat ins k) :
    (step p c).natReg k = c.natReg k := by
  classical
  rw [step_eq_effect p c ins hh hc]
  cases ins <;> simp only [writesNat, instructionEffect] at hwrite ⊢
  all_goals try rfl
  all_goals try exact Function.update_of_ne (Ne.symm hwrite) _ _
  all_goals split_ifs <;> rfl
lemma step_real_frame (p : Program) (c : Machine) (ins : Instruction) (k : ℕ)
    (hh : c.halted = false) (hc : p.code[c.pc]? = some ins) (hwrite : ¬ writesReal ins k) :
    (step p c).realReg k = c.realReg k := by
  classical
  rw [step_eq_effect p c ins hh hc]
  cases ins <;> simp only [writesReal, instructionEffect] at hwrite ⊢
  all_goals try rfl
  all_goals try exact Function.update_of_ne (Ne.symm hwrite) _ _
  all_goals split_ifs <;> rfl
lemma execute_nat_frame (p : Program) (c : Machine) (t k : ℕ)
    (hcode : ∀ j < t, ∀ ins, p.code[(execute p c j).pc]? = some ins → ¬ writesNat ins k) :
    (execute p c t).natReg k = c.natReg k := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hi := ih (fun j hj ins hc => hcode j (by omega) ins hc)
    rw [execute_add]
    change (step p (execute p c t)).natReg k = _
    by_cases hh : (execute p c t).halted = true
    · rwa [step_of_halted p _ hh]
    · have hhfalse := Bool.eq_false_iff.mpr hh
      cases hc : p.code[(execute p c t).pc]? with
      | none => simpa only [step, hhfalse, Bool.false_eq_true, if_false, hc] using hi
      | some ins => rw [step_nat_frame p _ ins k hhfalse hc (hcode t (by omega) ins hc), hi]
lemma execute_real_frame (p : Program) (c : Machine) (t k : ℕ)
    (hcode : ∀ j < t, ∀ ins, p.code[(execute p c j).pc]? = some ins → ¬ writesReal ins k) :
    (execute p c t).realReg k = c.realReg k := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hi := ih (fun j hj ins hc => hcode j (by omega) ins hc)
    rw [execute_add]
    change (step p (execute p c t)).realReg k = _
    by_cases hh : (execute p c t).halted = true
    · rwa [step_of_halted p _ hh]
    · have hhfalse := Bool.eq_false_iff.mpr hh
      cases hc : p.code[(execute p c t).pc]? with
      | none => simpa only [step, hhfalse, Bool.false_eq_true, if_false, hc] using hi
      | some ins => rw [step_real_frame p _ ins k hhfalse hc (hcode t (by omega) ins hc), hi]
end DecrAlmostLinearSSSP.Decremental
end s28
section s29
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
lemma atom_nat_frame (a : Atom) (s : Data) (k : ℕ) (h : ¬writesNat a.instruction k) :
    (a.effect s).natReg k = s.natReg k := by
  cases a with
  | mk ins hs =>
    cases ins <;> simp only [writesNat] at h
    all_goals simp only [Straight] at hs
    all_goals try contradiction
    all_goals try rfl
    all_goals exact Function.update_of_ne (Ne.symm h) _ _
lemma atom_real_frame (a : Atom) (s : Data) (k : ℕ) (h : ¬writesReal a.instruction k) :
    (a.effect s).realReg k = s.realReg k := by
  cases a with
  | mk ins hs =>
    cases ins <;> simp only [writesReal] at h
    all_goals simp only [Straight] at hs
    all_goals try contradiction
    all_goals try rfl
    all_goals exact Function.update_of_ne (Ne.symm h) _ _
lemma Eval.nat_frame {cmd : Cmd} {s t : Data} {cost k : ℕ}
    (he : Eval cmd s cost t) (h : NatFrame cmd k) : t.natReg k = s.natReg k := by
  induction he with
  | skip => rfl
  | atom a s => exact atom_nat_frame a s k h
  | seq ha hb iha ihb => exact (ihb h.2).trans (iha h.1)
  | branchYes ht he ih => exact ih h.1
  | branchNo ht he ih => exact ih h.2
  | loopNo => rfl
  | loopYes ht ha hb iha ihb => exact (ihb h).trans (iha h)
lemma Eval.real_frame {cmd : Cmd} {s t : Data} {cost k : ℕ}
    (he : Eval cmd s cost t) (h : RealFrame cmd k) : t.realReg k = s.realReg k := by
  induction he with
  | skip => rfl
  | atom a s => exact atom_real_frame a s k h
  | seq ha hb iha ihb => exact (ihb h.2).trans (iha h.1)
  | branchYes ht he ih => exact ih h.1
  | branchNo ht he ih => exact ih h.2
  | loopNo => rfl
  | loopYes ht ha hb iha ihb => exact (ihb h).trans (iha h)
end DecrAlmostLinearSSSP.Decremental.Structured
end s29
section s30
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Allocate
open Structured
lemma node_eval (s : Data) : Eval node s 10 (nodeData s) := eval_sequence_atoms nodeAtoms s
lemma node_values (s : Data) (hz : s.natReg 56 = 0) (h1 : s.natReg 26 = 1) :
    (nodeData s).natReg 272 = s.natReg 244 ∧ (nodeData s).natReg 244 = s.natReg 244+4 ∧
      NodeImage (nodeData s) (s.natReg 244) ⟨0,0,0,0⟩ ∧ (nodeData s).realMem = s.realMem ∧
      (∀ address, address < s.natReg 244 ∨ s.natReg 244+4 ≤ address →
        (nodeData s).natMem address = s.natMem address) := by
  have hmem : (nodeData s).natMem = Function.update (Function.update (Function.update
      (Function.update s.natMem (s.natReg 244) 0) (s.natReg 244+1) 0) (s.natReg 244+2) 0) (s.natReg 244+3) 0 := by
    simp [nodeData,nodeAtoms,Atom.effect,instructionEffect,data,Data.machine,hz,h1]
  refine ⟨?_,?_,?_,rfl,?_⟩
  · simp [nodeData,nodeAtoms,Atom.effect,instructionEffect,data,Data.machine,hz,h1]
  · simp [nodeData,nodeAtoms,Atom.effect,instructionEffect,data,Data.machine,hz,h1]
  · unfold NodeImage
    rw [hmem]
    simp
  · intro address ha
    rw [hmem]
    repeat' rw [Function.update_of_ne (by omega)]
lemma node_nat_frame (k : ℕ) (h272 : k ≠ 272) (h274 : k ≠ 274) (h244 : k ≠ 244) : NatFrame node k := by
  simp [node,nodeAtoms,Structured.sequence,NatFrame,writesNat,Ne.symm h272,Ne.symm h274,Ne.symm h244]
lemma node_real_frame (k : ℕ) : RealFrame node k := by simp [node,nodeAtoms,Structured.sequence,RealFrame,writesReal]
lemma item_eval (s : Data) : Eval item s 5 (itemData s) := eval_sequence_atoms itemAtoms s
lemma item_values (s : Data) (hz : s.natReg 56 = 0) (h1 : s.natReg 26 = 1) :
    (itemData s).natReg 272 = s.natReg 244 ∧ (itemData s).natReg 244 = s.natReg 244+2 ∧
      (itemData s).natMem (s.natReg 244) = s.natReg 262 ∧
      (itemData s).natMem (s.natReg 244+1) = s.natReg 276 ∧ (itemData s).realMem = s.realMem ∧
      (∀ address, address < s.natReg 244 ∨ s.natReg 244+2 ≤ address →
        (itemData s).natMem address = s.natMem address) := by
  have hmem : (itemData s).natMem = Function.update (Function.update s.natMem (s.natReg 244) (s.natReg 262))
      (s.natReg 244+1) (s.natReg 276) := by
    simp [itemData,itemAtoms,Atom.effect,instructionEffect,data,Data.machine,hz,h1]
  refine ⟨?_,?_,?_,?_,rfl,?_⟩
  · simp [itemData,itemAtoms,Atom.effect,instructionEffect,data,Data.machine,hz,h1]
  · simp [itemData,itemAtoms,Atom.effect,instructionEffect,data,Data.machine,hz,h1]
  · rw [hmem];simp
  · rw [hmem,Function.update_self]
  · intro address ha
    rw [hmem,Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
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
theorem solution : (((((((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (t : Nat),
  @LE.le.{0} Nat instLENat c.work (DecrAlmostLinearSSSP.Decremental.execute p c t).work) ∧ (∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (t : Nat),
  @Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.execute p c t).halted Bool.true →
    ∃ r,
      And (@LE.le.{0} Nat instLENat r t)
        (And
          (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine (DecrAlmostLinearSSSP.Decremental.execute p c r)
            (DecrAlmostLinearSSSP.Decremental.execute p c t))
          (@Eq.{1} Nat r
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (DecrAlmostLinearSSSP.Decremental.execute p c t).work c.work))))) ∧ ((∀ (host guest : DecrAlmostLinearSSSP.Decremental.Program) (offset returnPC : Nat),
  DecrAlmostLinearSSSP.Decremental.EmbedsCode host guest offset returnPC →
    ∀ (c final : DecrAlmostLinearSSSP.Decremental.Machine),
      @Eq.{1} Bool c.halted Bool.false →
        @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
          @Eq.{1} Nat c.pc
              (DecrAlmostLinearSSSP.Decremental.embeddedDestination offset returnPC
                (DecrAlmostLinearSSSP.Decremental.decodeGuest c)) →
            DecrAlmostLinearSSSP.Decremental.Ends guest (DecrAlmostLinearSSSP.Decremental.decodeGuest c) final →
              ∃ steps d,
                And
                  (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                    (DecrAlmostLinearSSSP.Decremental.execute host c steps) d)
                  (And
                    (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine (DecrAlmostLinearSSSP.Decremental.decodeGuest d)
                      final)
                    (And (@Eq.{1} Nat d.pc returnPC)
                      (And
                        (@LE.le.{0} Nat instLENat d.work
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) final.work
                                (DecrAlmostLinearSSSP.Decremental.decodeGuest c).work))))
                        (And (@Eq.{1} Bool d.halted Bool.false)
                          (And
                            (@Eq.{1} Nat (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                              (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                            (@Eq.{1} Nat (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))))) ∧ (∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine)
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
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))) ∧ (((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (n : Nat),
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
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work j)))) ∧ (∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine)
  (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
  @Eq.{1} Bool c.halted Bool.false →
    @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
          DecrAlmostLinearSSSP.Decremental.Instruction
          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code c.pc)
        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins) →
      Not (DecrAlmostLinearSSSP.Decremental.ModifiesMemory ins) →
        And (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.step p c).realMem c.realMem)
          (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.step p c).natMem c.natMem))) ∧ ((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (t : Nat),
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
            Not (DecrAlmostLinearSSSP.Decremental.ModifiesMemory ins)) →
    And (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.execute p c t).realMem c.realMem)
      (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.execute p c t).natMem c.natMem)) ∧ ((∀ (c : DecrAlmostLinearSSSP.Decremental.Structured.Cmd) (start : Nat),
  @Eq.{1} Nat
    (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction
      (DecrAlmostLinearSSSP.Decremental.Structured.compile c start))
    (DecrAlmostLinearSSSP.Decremental.Structured.codeSize c)) ∧ (∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine)
  (a : DecrAlmostLinearSSSP.Decremental.Structured.Atom),
  @Eq.{1} Bool c.halted Bool.false →
    @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
          DecrAlmostLinearSSSP.Decremental.Instruction
          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code c.pc)
        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction a.instruction) →
      And
        (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Structured.Data
          (DecrAlmostLinearSSSP.Decremental.Structured.data (DecrAlmostLinearSSSP.Decremental.step p c))
          (a.effect (DecrAlmostLinearSSSP.Decremental.Structured.data c)))
        (And
          (@Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.step p c).pc
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (And (@Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.step p c).halted Bool.false)
            (@Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.step p c).work
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))))) ∧ ((((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine)
  (test : DecrAlmostLinearSSSP.Decremental.Structured.Test) (target : Nat),
  @Eq.{1} Bool c.halted Bool.false →
    @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
          DecrAlmostLinearSSSP.Decremental.Instruction
          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code c.pc)
        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction (test.emit target)) →
      And
        (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Structured.Data
          (DecrAlmostLinearSSSP.Decremental.Structured.data (DecrAlmostLinearSSSP.Decremental.step p c))
          (DecrAlmostLinearSSSP.Decremental.Structured.data c))
        (And
          (@Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.step p c).pc
            (@ite.{1} Nat (test.holds (DecrAlmostLinearSSSP.Decremental.Structured.data c))
              (Classical.propDecidable (test.holds (DecrAlmostLinearSSSP.Decremental.Structured.data c))) target
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
          (And (@Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.step p c).halted Bool.false)
            (@Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.step p c).work
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))) ∧ (∀ {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {items : List.{0} (Prod.{0, 0} Nat Nat)},
  DecrAlmostLinearSSSP.Decremental.Exact.Payload.Image s items →
    (∀ (address : Nat),
        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
            (DecrAlmostLinearSSSP.Decremental.Exact.Payload.footprint items) address →
          @Eq.{1} Nat (t.natMem address) (s.natMem address)) →
      DecrAlmostLinearSSSP.Decremental.Exact.Payload.Image t items)) ∧ ((∀ {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {height : Nat}
  {tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie height},
  @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image s height tree →
    (∀ (address : Nat),
        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
            (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint height tree) address →
          @Eq.{1} Nat (t.natMem address) (s.natMem address)) →
      @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image t height tree) ∧ (∀ {height : Nat} (tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie height),
  @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Separated height tree →
    Iff
      (@Ne.{1} Nat (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root height tree)
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@Ne.{1} (DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie height) tree
        (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.empty height))))) ∧ (((∀ {s : DecrAlmostLinearSSSP.Decremental.Structured.Data} {height : Nat}
  {tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie height},
  @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image s height tree →
    @Ne.{1} Nat (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root height tree)
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
      @Eq.{1} Nat (s.natMem (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root height tree))
        (@DecrAlmostLinearSSSP.Decremental.RadixQueue.count height
          (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.abstract height tree))) ∧ (∀ {height : Nat} (tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie height),
  @Ne.{1} Nat (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root height tree)
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint height tree)
      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root height tree))) ∧ ((∀ {height : Nat} {tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie height} {low high : Nat},
  @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Bounded height tree low high →
    @Ne.{1} Nat (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root height tree)
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
      And (@LE.le.{0} Nat instLENat low (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root height tree))
        (@LT.lt.{0} Nat instLTNat (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root height tree) high)) ∧ ((∀ {height : Nat} {tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie height} {low high low' high' : Nat},
  @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Bounded height tree low high →
    @LE.le.{0} Nat instLENat low' low →
      @LE.le.{0} Nat instLENat high high' →
        @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Bounded height tree low' high') ∧ (∀ {height : Nat} (address : Nat) (left right : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie height)
  (offset : Nat),
  @LT.lt.{0} Nat instLTNat offset (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) height
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.node height address left right))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) address offset))))))) ∧ (((((∀ (address : Nat) (items : List.{0} (Prod.{0, 0} Nat Nat)) (offset : Nat),
  @LT.lt.{0} Nat instLTNat offset (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.leaf address items))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) address offset)) ∧ (∀ {height : Nat} (address : Nat) (left right : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie height),
  @LE.le.{0} (Finset.{0} Nat)
    (@Preorder.toLE.{0} (Finset.{0} Nat)
      (@PartialOrder.toPreorder.{0} (Finset.{0} Nat) (@Finset.instPartialOrder.{0} Nat)))
    (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint height left)
    (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) height
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.node height address left right)))) ∧ ((∀ {height : Nat} (address : Nat) (left right : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie height),
  @LE.le.{0} (Finset.{0} Nat)
    (@Preorder.toLE.{0} (Finset.{0} Nat)
      (@PartialOrder.toPreorder.{0} (Finset.{0} Nat) (@Finset.instPartialOrder.{0} Nat)))
    (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint height right)
    (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) height
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.node height address left right))) ∧ (∀ (address : Nat) (items : List.{0} (Prod.{0, 0} Nat Nat)),
  @LE.le.{0} (Finset.{0} Nat)
    (@Preorder.toLE.{0} (Finset.{0} Nat)
      (@PartialOrder.toPreorder.{0} (Finset.{0} Nat) (@Finset.instPartialOrder.{0} Nat)))
    (DecrAlmostLinearSSSP.Decremental.Exact.Payload.footprint items)
    (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.leaf address items))))) ∧ (((∀ {height address : Nat} {left right : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie height},
  @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Separated
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) height
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.node height address left right) →
    ∀ (offset : Nat),
      @LT.lt.{0} Nat instLTNat offset (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
        @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) address offset ∉
          @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint height left) ∧ (∀ {height address : Nat} {left right : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie height},
  @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Separated
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) height
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.node height address left right) →
    ∀ (offset : Nat),
      @LT.lt.{0} Nat instLTNat offset (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
        @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) address offset ∉
          @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint height right)) ∧ ((∀ (old : Finset.{0} Nat) (fresh length : Nat),
  (∀ (address : Nat),
      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) old address →
        @LT.lt.{0} Nat instLTNat address fresh) →
    @Disjoint.{0} (Finset.{0} Nat) (@Finset.instPartialOrder.{0} Nat) (@Finset.instOrderBot.{0} Nat) old
      (@Finset.Ico.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder fresh
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) fresh length))) ∧ ((∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {start : Nat}
  {a b : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction},
  DecrAlmostLinearSSSP.Decremental.Structured.CodeAt p start
      (@HAppend.hAppend.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (@instHAppendOfAppend.{0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (@List.instAppend.{0} DecrAlmostLinearSSSP.Decremental.Instruction))
        a b) →
    DecrAlmostLinearSSSP.Decremental.Structured.CodeAt p start a) ∧ (∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {start : Nat}
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
      b))))) ∧ ((((∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {start : Nat} {ins : DecrAlmostLinearSSSP.Decremental.Instruction}
  {rest : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction},
  DecrAlmostLinearSSSP.Decremental.Structured.CodeAt p start
      (@List.cons.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins rest) →
    @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
      (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
        DecrAlmostLinearSSSP.Decremental.Instruction
        (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
        (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code start)
      (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins)) ∧ (∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {start : Nat} {ins : DecrAlmostLinearSSSP.Decremental.Instruction}
  {rest : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction},
  DecrAlmostLinearSSSP.Decremental.Structured.CodeAt p start
      (@List.cons.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins rest) →
    DecrAlmostLinearSSSP.Decremental.Structured.CodeAt p
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      rest)) ∧ ((∀ (codePrefix code suffix : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
  (p : DecrAlmostLinearSSSP.Decremental.Program),
  @Eq.{1} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code
      (@HAppend.hAppend.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (@instHAppendOfAppend.{0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (@List.instAppend.{0} DecrAlmostLinearSSSP.Decremental.Instruction))
        codePrefix
        (@HAppend.hAppend.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (@instHAppendOfAppend.{0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
            (@List.instAppend.{0} DecrAlmostLinearSSSP.Decremental.Instruction))
          code suffix)) →
    DecrAlmostLinearSSSP.Decremental.Structured.CodeAt p
      (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction codePrefix) code) ∧ ((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (start : Nat) (a b : DecrAlmostLinearSSSP.Decremental.Structured.Cmd),
  DecrAlmostLinearSSSP.Decremental.Structured.CodeAt p start
      (DecrAlmostLinearSSSP.Decremental.Structured.compile (a.seq b) start) →
    And
      (DecrAlmostLinearSSSP.Decremental.Structured.CodeAt p start
        (DecrAlmostLinearSSSP.Decremental.Structured.compile a start))
      (DecrAlmostLinearSSSP.Decremental.Structured.CodeAt p
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start
          (DecrAlmostLinearSSSP.Decremental.Structured.codeSize a))
        (DecrAlmostLinearSSSP.Decremental.Structured.compile b
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start
            (DecrAlmostLinearSSSP.Decremental.Structured.codeSize a))))) ∧ (∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (start : Nat) (test : DecrAlmostLinearSSSP.Decremental.Structured.Test)
  (yes no : DecrAlmostLinearSSSP.Decremental.Structured.Cmd),
  DecrAlmostLinearSSSP.Decremental.Structured.CodeAt p start
      (DecrAlmostLinearSSSP.Decremental.Structured.compile
        (DecrAlmostLinearSSSP.Decremental.Structured.Cmd.branch test yes no) start) →
    And
      (@Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
          DecrAlmostLinearSSSP.Decremental.Instruction
          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code start)
        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
          (test.emit
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start
                (DecrAlmostLinearSSSP.Decremental.Structured.codeSize no))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
      (And
        (DecrAlmostLinearSSSP.Decremental.Structured.CodeAt p
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (DecrAlmostLinearSSSP.Decremental.Structured.compile no
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (And
          (@Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
            (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
              DecrAlmostLinearSSSP.Decremental.Instruction
              (fun as i =>
                @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
              (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (DecrAlmostLinearSSSP.Decremental.Structured.codeSize no)))
            (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
              (DecrAlmostLinearSSSP.Decremental.Instruction.jump
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start
                      (DecrAlmostLinearSSSP.Decremental.Structured.codeSize no))
                    (DecrAlmostLinearSSSP.Decremental.Structured.codeSize yes))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
          (DecrAlmostLinearSSSP.Decremental.Structured.CodeAt p
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start
                (DecrAlmostLinearSSSP.Decremental.Structured.codeSize no))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (DecrAlmostLinearSSSP.Decremental.Structured.compile yes
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start
                  (DecrAlmostLinearSSSP.Decremental.Structured.codeSize no))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))))) ∧ (((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (start : Nat) (test : DecrAlmostLinearSSSP.Decremental.Structured.Test)
  (body : DecrAlmostLinearSSSP.Decremental.Structured.Cmd),
  DecrAlmostLinearSSSP.Decremental.Structured.CodeAt p start
      (DecrAlmostLinearSSSP.Decremental.Structured.compile
        (DecrAlmostLinearSSSP.Decremental.Structured.Cmd.loop test body) start) →
    And
      (@Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
          DecrAlmostLinearSSSP.Decremental.Instruction
          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code start)
        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
          (test.emit
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
      (And
        (@Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
            DecrAlmostLinearSSSP.Decremental.Instruction
            (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
            (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
            (DecrAlmostLinearSSSP.Decremental.Instruction.jump
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start
                  (DecrAlmostLinearSSSP.Decremental.Structured.codeSize body))
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
        (And
          (DecrAlmostLinearSSSP.Decremental.Structured.CodeAt p
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (DecrAlmostLinearSSSP.Decremental.Structured.compile body
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
          (@Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
            (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
              DecrAlmostLinearSSSP.Decremental.Instruction
              (fun as i =>
                @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
              (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (DecrAlmostLinearSSSP.Decremental.Structured.codeSize body)))
            (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
              (DecrAlmostLinearSSSP.Decremental.Instruction.jump start)))))) ∧ (∀ (c : DecrAlmostLinearSSSP.Decremental.Machine) (pc work : Nat),
  @Eq.{1} DecrAlmostLinearSSSP.Decremental.Structured.Data
    (DecrAlmostLinearSSSP.Decremental.Structured.data
      { pc := pc, realReg := c.realReg, natReg := c.natReg, realMem := c.realMem, natMem := c.natMem,
        halted := c.halted, fault := c.fault, work := work })
    (DecrAlmostLinearSSSP.Decremental.Structured.data c))) ∧ ((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (target : Nat),
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
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))) ∧ ((∀ {cmd : DecrAlmostLinearSSSP.Decremental.Structured.Cmd} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {cost : Nat},
  DecrAlmostLinearSSSP.Decremental.Structured.Eval cmd s cost t →
    ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (start : Nat) (c : DecrAlmostLinearSSSP.Decremental.Machine),
      DecrAlmostLinearSSSP.Decremental.Structured.CodeAt p start
          (DecrAlmostLinearSSSP.Decremental.Structured.compile cmd start) →
        @Eq.{1} Nat c.pc start →
          @Eq.{1} DecrAlmostLinearSSSP.Decremental.Structured.Data (DecrAlmostLinearSSSP.Decremental.Structured.data c)
              s →
            @Eq.{1} Bool c.halted Bool.false →
              And
                (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Structured.Data
                  (DecrAlmostLinearSSSP.Decremental.Structured.data (DecrAlmostLinearSSSP.Decremental.execute p c cost))
                  t)
                (And
                  (@Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.execute p c cost).pc
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start
                      (DecrAlmostLinearSSSP.Decremental.Structured.codeSize cmd)))
                  (And (@Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.execute p c cost).halted Bool.false)
                    (@Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.execute p c cost).work
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work cost))))) ∧ (∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine),
  DecrAlmostLinearSSSP.Decremental.FaultWellFormed c →
    DecrAlmostLinearSSSP.Decremental.FaultWellFormed (DecrAlmostLinearSSSP.Decremental.step p c)))))))) ∧ ((((((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (t : Nat),
  DecrAlmostLinearSSSP.Decremental.FaultWellFormed c →
    DecrAlmostLinearSSSP.Decremental.FaultWellFormed (DecrAlmostLinearSSSP.Decremental.execute p c t)) ∧ (∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (t : Nat),
  @Eq.{1} Bool c.fault Bool.false →
    @Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.execute p c t).halted Bool.false →
      @Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.execute p c t).fault Bool.false)) ∧ ((∀ (p : DecrAlmostLinearSSSP.Decremental.Program),
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
                    (And (@Eq.{1} (Nat → Real) d.realMem c.realMem) (@Eq.{1} (Nat → Nat) d.natMem c.natMem)))))) ∧ (∀ (init update : DecrAlmostLinearSSSP.Decremental.Structured.Cmd),
  DecrAlmostLinearSSSP.Decremental.Structured.CodeAt (DecrAlmostLinearSSSP.Decremental.Structured.program init update)
    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
    (DecrAlmostLinearSSSP.Decremental.Structured.compile init
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))) ∧ (((∀ (init update : DecrAlmostLinearSSSP.Decremental.Structured.Cmd),
  @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
    (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
      DecrAlmostLinearSSSP.Decremental.Instruction
      (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
      (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
      (DecrAlmostLinearSSSP.Decremental.Structured.program init update).code
      (DecrAlmostLinearSSSP.Decremental.Structured.codeSize init))
    (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction DecrAlmostLinearSSSP.Decremental.Instruction.halt)) ∧ (∀ (init update : DecrAlmostLinearSSSP.Decremental.Structured.Cmd),
  DecrAlmostLinearSSSP.Decremental.Structured.CodeAt (DecrAlmostLinearSSSP.Decremental.Structured.program init update)
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (DecrAlmostLinearSSSP.Decremental.Structured.codeSize init)
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (DecrAlmostLinearSSSP.Decremental.Structured.compile update
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (DecrAlmostLinearSSSP.Decremental.Structured.codeSize init)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) ∧ ((∀ (init update : DecrAlmostLinearSSSP.Decremental.Structured.Cmd),
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
    (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction DecrAlmostLinearSSSP.Decremental.Instruction.halt)) ∧ ((∀ (init update : DecrAlmostLinearSSSP.Decremental.Structured.Cmd),
  DecrAlmostLinearSSSP.Decremental.Structured.CodeAt (DecrAlmostLinearSSSP.Decremental.Structured.program init update)
    (DecrAlmostLinearSSSP.Decremental.Structured.program init update).query
    (@List.cons.{0} DecrAlmostLinearSSSP.Decremental.Instruction
      (DecrAlmostLinearSSSP.Decremental.Instruction.loadN (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
        (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
      (@List.cons.{0} DecrAlmostLinearSSSP.Decremental.Instruction
        (DecrAlmostLinearSSSP.Decremental.Instruction.load (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
        (@List.cons.{0} DecrAlmostLinearSSSP.Decremental.Instruction DecrAlmostLinearSSSP.Decremental.Instruction.halt
          (@List.nil.{0} DecrAlmostLinearSSSP.Decremental.Instruction))))) ∧ (∀ (init update : DecrAlmostLinearSSSP.Decremental.Structured.Cmd) (c : DecrAlmostLinearSSSP.Decremental.Machine)
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
            (And (@Eq.{1} (Nat → Real) d.realMem c.realMem) (@Eq.{1} (Nat → Nat) d.natMem c.natMem)))))))))) ∧ ((((∀ {cmd : DecrAlmostLinearSSSP.Decremental.Structured.Cmd} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data}
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
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (d q : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.natural d q) s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    { realReg := s.realReg, natReg := @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natReg d q,
      realMem := s.realMem, natMem := s.natMem })) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (d : Nat) (q : Rat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.rational d q) s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    {
      realReg :=
        @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realReg d
          (@Rat.cast.{0} Real Real.instRatCast q),
      natReg := s.natReg, realMem := s.realMem, natMem := s.natMem }) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (d a : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.cast d a) s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    {
      realReg :=
        @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realReg d
          (@Nat.cast.{0} Real Real.instNatCast (s.natReg a)),
      natReg := s.natReg, realMem := s.realMem, natMem := s.natMem }) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (d a b : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.add d a b) s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    {
      realReg :=
        @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realReg d
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (s.realReg a) (s.realReg b)),
      natReg := s.natReg, realMem := s.realMem, natMem := s.natMem })))) ∧ (((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (d a b : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.sub d a b) s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    {
      realReg :=
        @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realReg d
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (s.realReg a) (s.realReg b)),
      natReg := s.natReg, realMem := s.realMem, natMem := s.natMem }) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (d a b : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.mul d a b) s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    {
      realReg :=
        @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realReg d
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (s.realReg a) (s.realReg b)),
      natReg := s.natReg, realMem := s.realMem, natMem := s.natMem })) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (d a b : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.div d a b) s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    {
      realReg :=
        @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realReg d
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (s.realReg a) (s.realReg b)),
      natReg := s.natReg, realMem := s.realMem, natMem := s.natMem }) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (d a b : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.nadd d a b) s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    { realReg := s.realReg,
      natReg :=
        @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natReg d
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (s.natReg a) (s.natReg b)),
      realMem := s.realMem, natMem := s.natMem }) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (d a b : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.nsub d a b) s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    { realReg := s.realReg,
      natReg :=
        @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natReg d
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (s.natReg a) (s.natReg b)),
      realMem := s.realMem, natMem := s.natMem })))))) ∧ (((((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (d a : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.load d a) s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    { realReg := @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realReg d (s.realMem (s.natReg a)),
      natReg := s.natReg, realMem := s.realMem, natMem := s.natMem }) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (a d : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.store a d) s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    { realReg := s.realReg, natReg := s.natReg,
      realMem := @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realMem (s.natReg a) (s.realReg d),
      natMem := s.natMem })) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (d a : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.loadN d a) s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    { realReg := s.realReg,
      natReg := @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natReg d (s.natMem (s.natReg a)),
      realMem := s.realMem, natMem := s.natMem }) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (a d : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.storeN a d) s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    { realReg := s.realReg, natReg := s.natReg, realMem := s.realMem,
      natMem := @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natMem (s.natReg a) (s.natReg d) }))) ∧ (((∀ (atoms : List.{0} DecrAlmostLinearSSSP.Decremental.Structured.Atom)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval
    (DecrAlmostLinearSSSP.Decremental.Structured.sequence
      (@List.map.{0, 0} DecrAlmostLinearSSSP.Decremental.Structured.Atom DecrAlmostLinearSSSP.Decremental.Structured.Cmd
        DecrAlmostLinearSSSP.Decremental.Structured.Cmd.atom atoms))
    s (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Structured.Atom atoms)
    (@List.foldl.{0, 0} DecrAlmostLinearSSSP.Decremental.Structured.Data
      DecrAlmostLinearSSSP.Decremental.Structured.Atom (fun t a => a.effect t) s atoms)) ∧ (∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine)
  (ins : DecrAlmostLinearSSSP.Decremental.Instruction) (k : Nat),
  @Eq.{1} Bool c.halted Bool.false →
    @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
          DecrAlmostLinearSSSP.Decremental.Instruction
          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code c.pc)
        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins) →
      Not (DecrAlmostLinearSSSP.Decremental.writesNat ins k) →
        @Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.step p c).natReg k) (c.natReg k))) ∧ ((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine)
  (ins : DecrAlmostLinearSSSP.Decremental.Instruction) (k : Nat),
  @Eq.{1} Bool c.halted Bool.false →
    @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
          DecrAlmostLinearSSSP.Decremental.Instruction
          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code c.pc)
        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins) →
      Not (DecrAlmostLinearSSSP.Decremental.writesReal ins k) →
        @Eq.{1} Real ((DecrAlmostLinearSSSP.Decremental.step p c).realReg k) (c.realReg k)) ∧ ((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (t k : Nat),
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
            Not (DecrAlmostLinearSSSP.Decremental.writesNat ins k)) →
    @Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.execute p c t).natReg k) (c.natReg k)) ∧ (∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (t k : Nat),
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
            Not (DecrAlmostLinearSSSP.Decremental.writesReal ins k)) →
    @Eq.{1} Real ((DecrAlmostLinearSSSP.Decremental.execute p c t).realReg k) (c.realReg k)))))) ∧ ((((∀ (a : DecrAlmostLinearSSSP.Decremental.Structured.Atom) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data)
  (k : Nat),
  Not (DecrAlmostLinearSSSP.Decremental.writesNat a.instruction k) → @Eq.{1} Nat ((a.effect s).natReg k) (s.natReg k)) ∧ (∀ (a : DecrAlmostLinearSSSP.Decremental.Structured.Atom) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data)
  (k : Nat),
  Not (DecrAlmostLinearSSSP.Decremental.writesReal a.instruction k) →
    @Eq.{1} Real ((a.effect s).realReg k) (s.realReg k))) ∧ ((∀ {cmd : DecrAlmostLinearSSSP.Decremental.Structured.Cmd} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {cost k : Nat},
  DecrAlmostLinearSSSP.Decremental.Structured.Eval cmd s cost t →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame cmd k → @Eq.{1} Nat (t.natReg k) (s.natReg k)) ∧ ((∀ {cmd : DecrAlmostLinearSSSP.Decremental.Structured.Cmd} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {cost k : Nat},
  DecrAlmostLinearSSSP.Decremental.Structured.Eval cmd s cost t →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame cmd k → @Eq.{1} Real (t.realReg k) (s.realReg k)) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.Allocate.node s
    (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))
    (DecrAlmostLinearSSSP.Decremental.Exact.Allocate.nodeData s))))) ∧ (((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
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
                    (s.natMem address)))))) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 272) (instOfNatNat (nat_lit 272))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 274) (instOfNatNat (nat_lit 274))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))) →
        DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.Allocate.node k)) ∧ ((∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Exact.Allocate.node k) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.Allocate.item s
    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
    (DecrAlmostLinearSSSP.Decremental.Exact.Allocate.itemData s)) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      And
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.Exact.Allocate.itemData s).natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 272) (instOfNatNat (nat_lit 272))))
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))))
        (And
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.Exact.Allocate.itemData s).natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (And
            (@Eq.{1} Nat
              ((DecrAlmostLinearSSSP.Decremental.Exact.Allocate.itemData s).natMem
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 262) (instOfNatNat (nat_lit 262)))))
            (And
              (@Eq.{1} Nat
                ((DecrAlmostLinearSSSP.Decremental.Exact.Allocate.itemData s).natMem
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 276) (instOfNatNat (nat_lit 276)))))
              (And (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.Exact.Allocate.itemData s).realMem s.realMem)
                (∀ (address : Nat),
                  Or
                      (@LT.lt.{0} Nat instLTNat address
                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))))
                      (@LE.le.{0} Nat instLENat
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        address) →
                    @Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.Exact.Allocate.itemData s).natMem address)
                      (s.natMem address)))))))))))))) := by
  exact ⟨⟨⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.execute_work_mono,DecrAlmostLinearSSSP.Decremental.terminating_prefix⟩,⟨DecrAlmostLinearSSSP.Decremental.embedded_ends,DecrAlmostLinearSSSP.Decremental.step_straight⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.straight_prefix,DecrAlmostLinearSSSP.Decremental.step_memory_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.execute_memory_frame,⟨DecrAlmostLinearSSSP.Decremental.Structured.compile_length,DecrAlmostLinearSSSP.Decremental.Structured.atom_step⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Structured.test_step,DecrAlmostLinearSSSP.Decremental.Exact.Payload.Image.frame⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image.frame,DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root_nonzero⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image.count,DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root_mem⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Bounded.root,⟨DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Bounded.mono,DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.node_field_mem⟩⟩⟩⟩⟩,⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.leaf_field_mem,DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.node_left_subset⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.node_right_subset,DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.leaf_payload_subset⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Separated.left_field,DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Separated.right_field⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.disjoint_fresh_interval,⟨DecrAlmostLinearSSSP.Decremental.Structured.CodeAt.left,DecrAlmostLinearSSSP.Decremental.Structured.CodeAt.right⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Structured.CodeAt.head,DecrAlmostLinearSSSP.Decremental.Structured.CodeAt.tail⟩,⟨DecrAlmostLinearSSSP.Decremental.Structured.CodeAt.of_assembled,⟨DecrAlmostLinearSSSP.Decremental.Structured.compile_seq_parts,DecrAlmostLinearSSSP.Decremental.Structured.compile_branch_parts⟩⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Structured.compile_loop_parts,DecrAlmostLinearSSSP.Decremental.Structured.data_clock⟩,⟨DecrAlmostLinearSSSP.Decremental.Structured.jump_step,⟨DecrAlmostLinearSSSP.Decremental.Structured.eval_compiles,DecrAlmostLinearSSSP.Decremental.fault_well_formed_step⟩⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.fault_well_formed_execute,DecrAlmostLinearSSSP.Decremental.running_execution_no_fault⟩,⟨DecrAlmostLinearSSSP.Decremental.ram_query_nine,DecrAlmostLinearSSSP.Decremental.Structured.program_init⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Structured.program_init_halt,DecrAlmostLinearSSSP.Decremental.Structured.program_update⟩,⟨DecrAlmostLinearSSSP.Decremental.Structured.program_update_halt,⟨DecrAlmostLinearSSSP.Decremental.Structured.program_query_code,DecrAlmostLinearSSSP.Decremental.Structured.program_query_nine⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Structured.command_ends,DecrAlmostLinearSSSP.Decremental.Structured.eval_natural⟩,⟨DecrAlmostLinearSSSP.Decremental.Structured.eval_rational,⟨DecrAlmostLinearSSSP.Decremental.Structured.eval_cast,DecrAlmostLinearSSSP.Decremental.Structured.eval_add⟩⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Structured.eval_sub,DecrAlmostLinearSSSP.Decremental.Structured.eval_mul⟩,⟨DecrAlmostLinearSSSP.Decremental.Structured.eval_div,⟨DecrAlmostLinearSSSP.Decremental.Structured.eval_nadd,DecrAlmostLinearSSSP.Decremental.Structured.eval_nsub⟩⟩⟩⟩⟩,⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Structured.eval_load,DecrAlmostLinearSSSP.Decremental.Structured.eval_store⟩,⟨DecrAlmostLinearSSSP.Decremental.Structured.eval_loadN,DecrAlmostLinearSSSP.Decremental.Structured.eval_storeN⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Structured.eval_sequence_atoms,DecrAlmostLinearSSSP.Decremental.step_nat_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.step_real_frame,⟨DecrAlmostLinearSSSP.Decremental.execute_nat_frame,DecrAlmostLinearSSSP.Decremental.execute_real_frame⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Structured.atom_nat_frame,DecrAlmostLinearSSSP.Decremental.Structured.atom_real_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.Structured.Eval.nat_frame,⟨DecrAlmostLinearSSSP.Decremental.Structured.Eval.real_frame,DecrAlmostLinearSSSP.Decremental.Exact.Allocate.node_eval⟩⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Exact.Allocate.node_values,DecrAlmostLinearSSSP.Decremental.Exact.Allocate.node_nat_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.Exact.Allocate.node_real_frame,⟨DecrAlmostLinearSSSP.Decremental.Exact.Allocate.item_eval,DecrAlmostLinearSSSP.Decremental.Exact.Allocate.item_values⟩⟩⟩⟩⟩⟩⟩
