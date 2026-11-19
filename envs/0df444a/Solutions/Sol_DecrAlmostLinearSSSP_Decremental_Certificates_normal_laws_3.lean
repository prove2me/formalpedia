-- Prove2me | solution 1 for DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_3
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T11:22:23.770029+00:00
-- url     : https://prove2.me/submissions/1d9b07eb-4834-4b2a-b1b3-9a73890cd1fc

import Definitions.Def_DecrAlmostLinearSSSP_RAMFoundation
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_2
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_3
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_4
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_5
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_6
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_7
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_8
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_normal_laws_2
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
open scoped ENNReal NNReal
attribute [local instance] Classical.propDecidable
theorem DecrAlmostLinearSSSP.Decremental.Structured.eval_cast : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (d a : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.cast d a) s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    {
      realReg :=
        @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realReg d
          (@Nat.cast.{0} Real Real.instNatCast (s.natReg a)),
      natReg := s.natReg, realMem := s.realMem, natMem := s.natMem } := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.1.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.Structured.eval_add : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (d a b : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.add d a b) s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    {
      realReg :=
        @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realReg d
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (s.realReg a) (s.realReg b)),
      natReg := s.natReg, realMem := s.realMem, natMem := s.natMem } := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.1.2.1.2.2.2
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
theorem DecrAlmostLinearSSSP.Decremental.Structured.eval_store : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (a d : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.store a d) s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    { realReg := s.realReg, natReg := s.natReg,
      realMem := @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realMem (s.natReg a) (s.realReg d),
      natMem := s.natMem } := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.2.1.1.1.2
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
theorem DecrAlmostLinearSSSP.Decremental.execute_nat_frame : ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (t k : Nat),
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
    @Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.execute p c t).natReg k) (c.natReg k) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.execute_real_frame : ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (t k : Nat),
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
    @Eq.{1} Real ((DecrAlmostLinearSSSP.Decremental.execute p c t).realReg k) (c.realReg k) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2.2.2.1.2.2.2.2
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
theorem DecrAlmostLinearSSSP.Decremental.rounded_polynomial_domain : ∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
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
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.1.2.1.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.ceiling_scale_bounds : ∀ {d : Real},
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
          d)) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.1.2.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.logarithm2_nonneg : ∀ {x : Real},
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) x →
    @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (DecrAlmostLinearSSSP.Decremental.logarithm2 x) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.1.2.2.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.Exact.Powers.body_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.Powers.body s
    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
    (DecrAlmostLinearSSSP.Decremental.Exact.Powers.advanced s) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.1.1.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.shadowReg_injective : @Function.Injective.{1, 1} Nat Nat DecrAlmostLinearSSSP.Decremental.shadowReg := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.shadowReg_ne_meta : ∀ (j k : Nat),
  @LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) →
    @Ne.{1} Nat (DecrAlmostLinearSSSP.Decremental.shadowReg j) k := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_4.2.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.ShadowDataRep.effect : ∀ {B F : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine}
  (a : DecrAlmostLinearSSSP.Decremental.Structured.Atom),
  DecrAlmostLinearSSSP.Decremental.ShadowRep B F
      (DecrAlmostLinearSSSP.Decremental.instructionEffect a.instruction s.machine) g →
    DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F (a.effect s) g := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.1.1.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.structuredConstant_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (d factor q : Nat),
  @Ne.{1} Nat factor d →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.structuredConstant d factor q) s
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) q
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      { realReg := s.realReg,
        natReg :=
          @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natReg d
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) q (s.natReg factor)),
        realMem := s.realMem, natMem := s.natMem } := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.1.1.2.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.repeatedAdd_nat_frame : ∀ (d factor q k : Nat),
  @Ne.{1} Nat d k →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.repeatedAdd d factor q) k := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.1.2.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.repeatedAdd_real_frame : ∀ (d factor q k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.repeatedAdd d factor q) k := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_5.1.2.1.1.1.2
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
theorem DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.prepare_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.prepare s
    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
    (DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.prepared s) := DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_6.1.2.2.1.1.1
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
theorem DecrAlmostLinearSSSP.Decremental.PreservesOutside.trans : ∀ {base F : Nat} {c d e : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.PreservesOutside base F c d →
    DecrAlmostLinearSSSP.Decremental.PreservesOutside base F d e →
      DecrAlmostLinearSSSP.Decremental.PreservesOutside base F c e := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_2.1.1.1.1.2.2
theorem DecrAlmostLinearSSSP.Decremental.ScaledCeiling.setup_fields : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
      And
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.ScaledCeiling.setupData s).natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 48) (instOfNatNat (nat_lit 48)))))
        (And
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.ScaledCeiling.setupData s).natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (And
            (@Eq.{1} Nat
              ((DecrAlmostLinearSSSP.Decremental.ScaledCeiling.setupData s).natReg
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
            (And
              (@Eq.{1} Nat
                ((DecrAlmostLinearSSSP.Decremental.ScaledCeiling.setupData s).natReg
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (And
                (@Eq.{1} Nat
                  ((DecrAlmostLinearSSSP.Decremental.ScaledCeiling.setupData s).natReg
                    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                (And
                  (@Eq.{1} Nat
                    ((DecrAlmostLinearSSSP.Decremental.ScaledCeiling.setupData s).natReg
                      (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (And
                    (@Eq.{1} Real
                      ((DecrAlmostLinearSSSP.Decremental.ScaledCeiling.setupData s).realReg
                        (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                    (And
                      (@Eq.{1} Nat
                        ((DecrAlmostLinearSSSP.Decremental.ScaledCeiling.setupData s).natReg
                          (DecrAlmostLinearSSSP.Decremental.shadowReg
                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58)))))
                      (@Eq.{1} Real
                        ((DecrAlmostLinearSSSP.Decremental.ScaledCeiling.setupData s).realReg
                          (DecrAlmostLinearSSSP.Decremental.shadowReg
                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                        (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58)))))))))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_2.2.1.2.1.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.ScaledCeiling.call_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (N : Nat),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58)))) →
        @LE.le.{0} Real Real.instLE (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))))
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              N) →
          ∃ cost t,
            And
              (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.ScaledCeiling.call s
                cost t)
              (And
                (@Eq.{1} Nat
                  (t.natReg
                    (DecrAlmostLinearSSSP.Decremental.shadowReg
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))))
                    (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
                      (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing)
                      (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58)))))))
                (And
                  (@LE.le.{0} Nat instLENat cost
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (DecrAlmostLinearSSSP.Decremental.dispatchCharge
                          DecrAlmostLinearSSSP.Decremental.ScaledCeiling.ceilingProgram.code)
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16))) N)
                        (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))))
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
                          And (@Eq.{1} Nat (t.natReg k) (s.natReg k)) (@Eq.{1} Real (t.realReg k) (s.realReg k)))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_2.2.1.2.2.2.1
theorem DecrAlmostLinearSSSP.Decremental.ScaledCeiling.call_nat_even : ∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.ScaledCeiling.call k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_2.2.1.2.2.2.2.2
theorem DecrAlmostLinearSSSP.Decremental.ScaledCeiling.call_real_even : ∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.ScaledCeiling.call k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_2.2.2.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.ScaledCeiling.polynomialReserve_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (m N B : Nat),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58)))) m →
    @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))))
        (@Nat.cast.{0} Real Real.instNatCast m) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
        @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
            @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast m)
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
                    (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.polynomialReserve B) s cost t)
                  (And
                    (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 60) (instOfNatNat (nat_lit 60))))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) B
                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) m
                            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (And
                      (@LE.le.{0} Nat instLENat cost
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
                                  (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16))) N)
                                (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))))
                            B)
                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
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
                            (@Eq.{1} Nat (t.natMem address) (s.natMem address))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_2.2.2.1.2.1.1
theorem DecrAlmostLinearSSSP.Decremental.ScaledCeiling.countScales_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 66) (instOfNatNat (nat_lit 66)))) i.n →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 70) (instOfNatNat (nat_lit 70)))) i.W →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
          @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
              ∃ cost t,
                And
                  (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                    DecrAlmostLinearSSSP.Decremental.ScaledCeiling.countScales s cost t)
                  (And
                    (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
                      (DecrAlmostLinearSSSP.Decremental.scaleCount i))
                    (And
                      (@LE.le.{0} Nat instLENat cost
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (DecrAlmostLinearSSSP.Decremental.dispatchCharge
                              DecrAlmostLinearSSSP.Decremental.ScaledCeiling.ceilingProgram.code)
                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))
                              (DecrAlmostLinearSSSP.Decremental.scaleCount i))
                            (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))))
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
                            (@Eq.{1} Nat (t.natMem address) (s.natMem address))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_2.2.2.2.1.1.2
theorem DecrAlmostLinearSSSP.Decremental.ScaledCeiling.scaleArea_eval : ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (i : DecrAlmostLinearSSSP.Decremental.Input),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 66) (instOfNatNat (nat_lit 66)))) i.n →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
        (DecrAlmostLinearSSSP.Decremental.scaleCount i) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
        @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
          ∃ cost t,
            And
              (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.ScaledCeiling.scaleArea
                s cost t)
              (And
                (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))))
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) i.n
                    (DecrAlmostLinearSSSP.Decremental.scaleCount i)))
                (And
                  (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
                    (DecrAlmostLinearSSSP.Decremental.scaleCount i))
                  (And
                    (@LE.le.{0} Nat instLENat cost
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (DecrAlmostLinearSSSP.Decremental.dispatchCharge
                            DecrAlmostLinearSSSP.Decremental.ScaledCeiling.ceilingProgram.code)
                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))
                            (DecrAlmostLinearSSSP.Decremental.scaleCount i))
                          (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))))
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
                          (@Eq.{1} Nat (t.natMem address) (s.natMem address)))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_2.2.2.2.1.2.1
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
theorem DecrAlmostLinearSSSP.Decremental.ScaledCeiling.reserve_real_frame : ∀ (B k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
        (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.polynomialReserve B) k := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_2.2.2.2.2.2.2.2
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
lemma count_nat_frame (k : ℕ) (hk : 10 ≤ k) (hev : Even k) (h58 : k ≠ 58) (h80 : k ≠ 80) : NatFrame countScales k := by
  refine ⟨?_,call_nat_even k hk hev,Ne.symm h80⟩
  simp [scaleArgument,scaleArgumentAtoms,Structured.sequence,NatFrame,writesNat,Ne.symm h58]
lemma count_real_frame (k : ℕ) (hk : 10 ≤ k) (hev : Even k)
    (h58 : k ≠ 58) (h80 : k ≠ 80) (h82 : k ≠ 82) (h84 : k ≠ 84) : RealFrame countScales k := by
  refine ⟨?_,call_real_even k hk hev,not_false⟩
  simp [scaleArgument,scaleArgumentAtoms,Structured.sequence,RealFrame,writesReal,
    Ne.symm h58,Ne.symm h80,Ne.symm h82,Ne.symm h84]
lemma area_nat_frame (k : ℕ) (hk : 10 ≤ k) (hev : Even k) (h58 : k ≠ 58) (h82 : k ≠ 82) : NatFrame scaleArea k :=
  ⟨Ne.symm h58,not_false,call_nat_even k hk hev,Ne.symm h82⟩
lemma area_real_frame (k : ℕ) (hk : 10 ≤ k) (hev : Even k) (h58 : k ≠ 58) : RealFrame scaleArea k :=
  ⟨not_false,Ne.symm h58,call_real_even k hk hev,not_false⟩
end ScaledCeiling
namespace Layout
lemma nat_small_frame (stride k : ℕ) (hk : k < 84) (h48 : k ≠ 48) : NatFrame (code stride) k := by
  refine ⟨?_,?_,?_⟩
  · simp only [preAtoms,List.map_cons,List.map_nil,Structured.sequence,NatFrame,writesNat]
    repeat' (first | apply And.intro | omega | trivial)
  · have h86 : 86 ≠ k := by omega
    exact ⟨h86,repeatedAdd_nat_frame 86 80 stride k h86⟩
  · simp only [postAtoms,List.map_cons,List.map_nil,Structured.sequence,NatFrame,writesNat]
    repeat' (first | apply And.intro | omega | trivial)
lemma real_frame (stride k : ℕ) : RealFrame (code stride) k := by
  refine ⟨?_,?_,?_⟩
  · simp [preAtoms,Structured.sequence,RealFrame,writesReal]
  · exact ⟨not_false,repeatedAdd_real_frame _ _ _ _⟩
  · simp [postAtoms,Structured.sequence,RealFrame,writesReal]
end Layout
end DecrAlmostLinearSSSP.Decremental
end s88
section s89
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
lemma barrier_high_positive (i : Input) (hi : i.Valid) : 1 ≤ barrierHigh i := by
  apply Nat.ceil_pos.mpr
  have hn : (0 : ℝ) < i.n := by exact_mod_cast input_vertex_positive i
  have he := hi.2.2.2.1
  positivity
lemma barrier_weight_bounds (i : Input) (hi : i.Valid) (j : ℕ) (e : Fin i.k) :
    1 ≤ barrierWeight i j e ∧ barrierWeight i j e ≤ barrierHigh i := by
  classical
  unfold barrierWeight
  split_ifs with hcut
  · have hd := delta_positive i hi j
    have hn : (0 : ℝ) < i.n := by exact_mod_cast input_vertex_positive i
    have he := hi.2.2.2.1
    have hw : (0 : ℝ) < i.weight e := by exact_mod_cast (hi.2.2.2.2.2 e).1
    refine ⟨Nat.ceil_pos.mpr (div_pos hw hd),?_⟩
    apply Nat.ceil_le_ceil
    have hb := div_le_div_of_nonneg_right hcut hd.le
    have hid : (2*scale j)/delta i j = 256*(i.n : ℝ)/i.accuracy := by
      have hs := scale_positive j
      dsimp [delta]
      field_simp
      <;> ring
    rw [hid] at hb
    apply hb.trans
    exact div_le_div_of_nonneg_right (by nlinarith) he.le
  · exact ⟨barrier_high_positive i hi,le_rfl⟩
lemma barrier_valid (i : Input) (hi : i.Valid) (j : ℕ) : (barrierInput i j).Valid := by
  have he := hi.2.2.2.1
  have he1 := hi.2.2.2.2.1
  refine ⟨?_,?_,barrier_high_positive i hi,by change 0 < i.accuracy/16;positivity,?_,barrier_weight_bounds i hi j⟩
  · change i.n ≤ 64*i.size
    have hh := hi.1
    omega
  · change i.k ≤ 64*i.size
    have hh := hi.2.1
    omega
  · change i.accuracy/16 ≤ 1
    linarith
lemma barrier_polynomial_domain (i : Input) (hi : i.Valid) (hn : 2 ≤ i.n)
    (heps : 1/(i.size : ℝ) < i.accuracy) (j : ℕ) :
    2 ≤ (barrierInput i j).n ∧ (barrierInput i j).W ≤ (barrierInput i j).size^2 ∧
      1/((barrierInput i j).size : ℝ) < (barrierInput i j).accuracy ∧ (barrierInput i j).accuracy < 1 := by
  have hround := rounded_polynomial_domain i hi hn heps j
  have hm : (0 : ℝ) < i.size := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < i.n) hi.1)
  have he := hi.2.2.2.1
  have hmul : 1 < i.accuracy*i.size := (div_lt_iff₀ hm).mp heps
  have hnsize : (i.n : ℝ) ≤ i.size := by exact_mod_cast hi.1
  refine ⟨hn,?_,hround.2.2⟩
  change ⌈512*(i.n : ℝ)/i.accuracy⌉₊ ≤ (64*i.size)^2
  apply Nat.ceil_le.mpr
  norm_num only [Nat.cast_pow,Nat.cast_mul,Nat.cast_ofNat]
  apply (div_le_iff₀ he).mpr
  have hh := mul_lt_mul_of_pos_right hmul hm
  nlinarith only [hh,hnsize,hm]
lemma ceiling_cost_bounds (w : ℕ) (d : ℝ) (hd : 0 < d) :
    (w : ℝ) ≤ d*(⌈(w : ℝ)/d⌉₊ : ℝ) ∧ d*(⌈(w : ℝ)/d⌉₊ : ℝ) ≤ (w : ℝ)+d := by
  constructor
  · have hh := (div_le_iff₀ hd).mp (Nat.le_ceil ((w : ℝ)/d))
    simpa only [mul_comm] using hh
  · have hh := mul_lt_mul_of_pos_left (Nat.ceil_lt_add_one (div_nonneg (Nat.cast_nonneg w) hd.le)) hd
    have hid : d*((w : ℝ)/d+1) = (w : ℝ)+d := by field_simp
    exact (hh.trans_eq hid).le
lemma barrier_low_cost (i : Input) (hi : i.Valid) (j : ℕ) (e : Fin i.k)
    (he : (i.weight e : ℝ) ≤ 2*scale j) :
    (i.weight e : ℝ) ≤ delta i j*(barrierWeight i j e : ℝ) ∧
      delta i j*(barrierWeight i j e : ℝ) ≤ (i.weight e : ℝ)+delta i j := by
  unfold barrierWeight
  rw [if_pos he]
  exact ceiling_cost_bounds _ _ (delta_positive i hi j)
lemma barrier_high_cost (i : Input) (hi : i.Valid) (j : ℕ) (e : Fin i.k)
    (he : ¬(i.weight e : ℝ) ≤ 2*scale j) :
    4*scale j ≤ delta i j*(barrierWeight i j e : ℝ) := by
  unfold barrierWeight
  rw [if_neg he]
  have hd := delta_positive i hi j
  have hn : (0 : ℝ) < i.n := by exact_mod_cast input_vertex_positive i
  have heps := hi.2.2.2.1
  have hh := mul_le_mul_of_nonneg_left (Nat.le_ceil (512*(i.n : ℝ)/i.accuracy)) hd.le
  have hid : delta i j*(512*(i.n : ℝ)/i.accuracy) = 4*scale j := by
    dsimp [delta]
    field_simp
    <;> ring
  rw [hid] at hh
  exact hh
end DecrAlmostLinearSSSP.Decremental
end s89
section s90
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma utilityDepth_power (m : ℕ) : 512*(m : ℝ)^2 ≤ (2 : ℝ)^utilityDepth m := by
  have hm : (1 : ℝ) ≤ (max 2 m : ℕ) := by exact_mod_cast (show 1 ≤ max 2 m from by omega)
  have hh := (ceiling_scale_bounds hm).1
  have hnon : (0 : ℝ) ≤ (2 : ℝ)^⌈logarithm2 (max 2 m : ℕ)⌉₊ := by positivity
  have hsize : (m : ℝ) ≤ (max 2 m : ℕ) := by exact_mod_cast le_max_right 2 m
  have hsquare : (m : ℝ)^2 ≤ ((2 : ℝ)^⌈logarithm2 (max 2 m : ℕ)⌉₊)^2 := by
    change (max 2 m : ℕ) ≤ (2 : ℝ)^⌈logarithm2 (max 2 m : ℕ)⌉₊ at hh
    nlinarith only [hsize,hh,hnon,(show (0 : ℝ) ≤ m from Nat.cast_nonneg m)]
  rw [show utilityDepth m = 10+⌈logarithm2 (max 2 m : ℕ)⌉₊*2 by dsimp [utilityDepth];omega,
    pow_add,pow_mul]
  norm_num only [show (2 : ℝ)^10 = 1024 by norm_num]
  nlinarith only [hsquare,sq_nonneg ((2 : ℝ)^⌈logarithm2 (max 2 m : ℕ)⌉₊)]
lemma utilityDepth_bound (m : ℕ) :
    (utilityDepth m : ℝ) ≤ 12+2*logarithm2 (max 2 m : ℕ) := by
  have hlog := logarithm2_nonneg (show (1 : ℝ) ≤ (max 2 m : ℕ) by exact_mod_cast (show 1 ≤ max 2 m from by omega))
  have hh := (Nat.ceil_lt_add_one hlog).le
  unfold utilityDepth
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  linarith
lemma normal_barrier_argument_bound (i : Input) (hi : i.Valid)
    (heps : 1/(i.size : ℝ) < i.accuracy) :
    0 ≤ 512*(i.n : ℝ)/i.accuracy ∧ 512*(i.n : ℝ)/i.accuracy ≤ (2 : ℝ)^utilityDepth i.size := by
  have he := hi.2.2.2.1
  have hm : (0 : ℝ) < i.size := by exact_mod_cast (lt_of_lt_of_le (input_vertex_positive i) hi.1)
  have hnm : (i.n : ℝ) ≤ i.size := by exact_mod_cast hi.1
  have hmul : 1 < i.accuracy*i.size := (div_lt_iff₀ hm).mp heps
  refine ⟨by positivity,le_trans ?_ (utilityDepth_power i.size)⟩
  apply (div_le_iff₀ he).mpr
  have hh := mul_le_mul_of_nonneg_right hmul.le hm.le
  nlinarith only [hh,hnm]
end DecrAlmostLinearSSSP.Decremental
end s90
section s91
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Prepass
open Structured
open ScaledCeiling
lemma nat_frame (coefficient stride k : ℕ) (hk : 10 ≤ k) (hk' : k < 84) (hev : Even k)
    (h48 : k ≠ 48) (h58 : k ≠ 58) (h60 : k ≠ 60) (h80 : k ≠ 80) (h82 : k ≠ 82) : NatFrame (code coefficient stride) k :=
  ⟨reserve_nat_frame coefficient k hk hev h58 h60,count_nat_frame k hk hev h58 h80,
    area_nat_frame k hk hev h58 h82,Layout.nat_small_frame stride k hk' h48⟩
lemma real_frame (coefficient stride k : ℕ) (hk : 10 ≤ k) (hev : Even k)
    (h58 : k ≠ 58) (h80 : k ≠ 80) (h82 : k ≠ 82) (h84 : k ≠ 84) : RealFrame (code coefficient stride) k :=
  ⟨reserve_real_frame coefficient k hk hev,count_real_frame k hk hev h58 h80 h82 h84,
    area_real_frame k hk hev h58,Layout.real_frame stride k⟩
lemma size_ceiling_bound (i : Input) (hi : i.Valid) : (i.size : ℝ) ≤ (2 : ℝ)^utilityDepth i.size := by
  have hm : (1 : ℝ) ≤ i.size := by exact_mod_cast (lt_of_lt_of_le (input_vertex_positive i) hi.1)
  have hmul := mul_nonneg (le_trans zero_le_one hm) (sub_nonneg.mpr hm)
  apply le_trans _ (utilityDepth_power i.size)
  nlinarith only [hm,hmul]
lemma eval_code (s : Data) (i : Input) (hi : i.Valid) (hc : InputCapture.Captured i s)
    (coefficient stride : ℕ) :
    ∃ cost t, Eval (code coefficient stride) s cost t ∧
      Layout.Represents t (Layout.addresses (i.n+3*i.k+2) i.n (scaleCount i) (coefficient*i.size^3+1) stride) ∧
      t.natReg 60 = coefficient*i.size^3+1 ∧ t.natReg 80 = scaleCount i ∧ t.natReg 82 = i.n*scaleCount i ∧
      cost ≤ 2*(dispatchCharge ceilingProgram.code+3)*(16*utilityDepth i.size+32)+
        2*(dispatchCharge ceilingProgram.code+4)*(16*scaleCount i+32)+coefficient+stride+19 ∧
      ∀ address, (∀ a, address ≠ (i.n+3*i.k+2)+2*a+1) →
        t.realMem address = s.realMem address ∧ t.natMem address = s.natMem address := by
  obtain ⟨rcost,r,hr,hrout,hrcost,hrframe⟩ := polynomialReserve_eval s i.size (utilityDepth i.size) coefficient
    hc.factor hc.argument hc.zeroN hc.zeroR hc.unit (size_ceiling_bound i hi)
  have hrN (k : ℕ) (hk : 10 ≤ k) (hev : Even k) (h58 : k ≠ 58) (h60 : k ≠ 60) : r.natReg k = s.natReg k :=
    hr.nat_frame (reserve_nat_frame coefficient k hk hev h58 h60)
  have hrR (k : ℕ) (hk : 10 ≤ k) (hev : Even k) : r.realReg k = s.realReg k :=
    hr.real_frame (reserve_real_frame coefficient k hk hev)
  have hr66 : r.natReg 66 = i.n := (hrN 66 (by omega) (by decide) (by omega) (by omega)).trans hc.vertices
  have hr70 : r.natReg 70 = i.W := (hrN 70 (by omega) (by decide) (by omega) (by omega)).trans hc.weightBound
  have hr56 : r.natReg 56 = 0 := (hrN 56 (by omega) (by decide) (by omega) (by omega)).trans hc.zeroN
  have hrr56 : r.realReg 56 = 0 := (hrR 56 (by omega) (by decide)).trans hc.zeroR
  have hr26 : r.natReg 26 = 1 := (hrN 26 (by omega) (by decide) (by omega) (by omega)).trans hc.unit
  obtain ⟨ccost,c,hcount,hcout,hccost,hcframe⟩ := countScales_eval r i hi hr66 hr70 hr56 hrr56 hr26
  have hcN (k : ℕ) (hk : 10 ≤ k) (hev : Even k) (h58 : k ≠ 58) (h80 : k ≠ 80) : c.natReg k = r.natReg k :=
    hcount.nat_frame (count_nat_frame k hk hev h58 h80)
  have hcR (k : ℕ) (hk : 10 ≤ k) (hev : Even k) (h58 : k ≠ 58) (h80 : k ≠ 80) (h82 : k ≠ 82) (h84 : k ≠ 84) : c.realReg k = r.realReg k :=
    hcount.real_frame (count_real_frame k hk hev h58 h80 h82 h84)
  have hc66 : c.natReg 66 = i.n := (hcN 66 (by omega) (by decide) (by omega) (by omega)).trans hr66
  have hc56 : c.natReg 56 = 0 := (hcN 56 (by omega) (by decide) (by omega) (by omega)).trans hr56
  have hcr56 : c.realReg 56 = 0 := (hcR 56 (by omega) (by decide) (by omega) (by omega) (by omega) (by omega)).trans hrr56
  obtain ⟨acost,a,harea,haout,haS,hacost,haframe⟩ := scaleArea_eval c i hc66 hcout hc56 hcr56
  have haN (k : ℕ) (hk : 10 ≤ k) (hev : Even k) (h58 : k ≠ 58) (h82 : k ≠ 82) : a.natReg k = c.natReg k :=
    harea.nat_frame (area_nat_frame k hk hev h58 h82)
  have htrans (k : ℕ) (hk : 10 ≤ k) (hev : Even k) (h58 : k ≠ 58) (h60 : k ≠ 60) (h80 : k ≠ 80) (h82 : k ≠ 82) :
      a.natReg k = s.natReg k :=
    ((haN k hk hev h58 h82).trans (hcN k hk hev h58 h80)).trans (hrN k hk hev h58 h60)
  have ha74 : a.natReg 74 = i.n+3*i.k+2 := (htrans 74 (by omega) (by decide) (by omega) (by omega) (by omega) (by omega)).trans hc.base
  have ha66 : a.natReg 66 = i.n := (haN 66 (by omega) (by decide) (by omega) (by omega)).trans hc66
  have ha60 : a.natReg 60 = coefficient*i.size^3+1 :=
    ((haN 60 (by omega) (by decide) (by omega) (by omega)).trans (hcN 60 (by omega) (by decide) (by omega) (by omega))).trans hrout
  have ha26 : a.natReg 26 = 1 := (htrans 26 (by omega) (by decide) (by omega) (by omega) (by omega) (by omega)).trans hc.unit
  obtain ⟨t,hlayout,hlrep,hlr,hln⟩ := Layout.eval_code a (i.n+3*i.k+2) i.n (scaleCount i)
    (coefficient*i.size^3+1) stride ha74 ha66 haS haout ha60 ha26
  have ht60 : t.natReg 60 = coefficient*i.size^3+1 :=
    (hlayout.nat_frame (Layout.nat_small_frame stride 60 (by omega) (by omega))).trans ha60
  have ht80 : t.natReg 80 = scaleCount i :=
    (hlayout.nat_frame (Layout.nat_small_frame stride 80 (by omega) (by omega))).trans haS
  have ht82 : t.natReg 82 = i.n*scaleCount i :=
    (hlayout.nat_frame (Layout.nat_small_frame stride 82 (by omega) (by omega))).trans haout
  refine ⟨rcost+(ccost+(acost+(stride+16))),t,Eval.seq hr (Eval.seq hcount (Eval.seq harea hlayout)),hlrep,ht60,ht80,ht82,?_,?_⟩
  · nlinarith only [hrcost,hccost,hacost]
  · intro address hout
    have hr48 : r.natReg 48 = i.n+3*i.k+2 := (hrN 48 (by omega) (by decide) (by omega) (by omega)).trans hc.utilityBase
    have hc48 : c.natReg 48 = i.n+3*i.k+2 := (hcN 48 (by omega) (by decide) (by omega) (by omega)).trans hr48
    have hfr := hrframe address (by simpa only [hc.utilityBase] using hout)
    have hfc := hcframe address (by simpa only [hr48] using hout)
    have hfa := haframe address (by simpa only [hc48] using hout)
    exact ⟨(congrFun hlr address).trans (hfa.1.trans (hfc.1.trans hfr.1)),
      (congrFun hln address).trans (hfa.2.trans (hfc.2.trans hfr.2))⟩
end DecrAlmostLinearSSSP.Decremental.Prepass
end s91
section s92
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Fill
open Structured
lemma body_eval (s : Data) : Eval body s 4 (next s) := by
  have he := Eval.seq (eval_storeN s 116 124) (Eval.seq (eval_store _ 116 116)
    (Eval.seq (eval_nadd _ 116 116 120) (Eval.seq (eval_nsub _ 118 118 26) (Eval.skip _))))
  simpa only [body,Structured.sequence,next,
    Function.update_of_ne (by decide : (118 : ℕ) ≠ 116),Function.update_of_ne (by decide : (26 : ℕ) ≠ 116)] using he
lemma eval_code (n base stride value : ℕ) (realValue : ℝ) (s : Data)
    (hstride : 0 < stride) (hp : s.natReg 116 = base) (hn : s.natReg 118 = n)
    (hd : s.natReg 120 = stride) (hz : s.natReg 122 = 0) (hv : s.natReg 124 = value)
    (hr : s.realReg 116 = realValue) (h1 : s.natReg 26 = 1) :
    ∃ t, Eval code s (6*n+2) t ∧ t.natReg 116 = base+stride*n ∧ t.natReg 118 = 0 ∧
      (∀ j < n, t.natMem (base+stride*j) = value ∧ t.realMem (base+stride*j) = realValue) ∧
      (∀ address, (∀ j < n, address ≠ base+stride*j) →
        t.natMem address = s.natMem address ∧ t.realMem address = s.realMem address) := by
  induction n generalizing base s with
  | zero =>
    have ht : ¬(Test.natLess 122 118).holds s := by simp [Test.holds,hz,hn]
    exact ⟨s,Eval.loopNo s ht,by simpa using hp,hn,by simp,fun _ _ => ⟨rfl,rfl⟩⟩
  | succ n ih =>
    have htest : (Test.natLess 122 118).holds s := by simp [Test.holds,hz,hn]
    have hb := body_eval s
    have hp' : (next s).natReg 116 = base+stride := by simp [next,hp,hd]
    have hn' : (next s).natReg 118 = n := by simp [next,hn,h1]
    have hd' : (next s).natReg 120 = stride := by simp [next,hd]
    have hz' : (next s).natReg 122 = 0 := by simp [next,hz]
    have hv' : (next s).natReg 124 = value := by simp [next,hv]
    have hr' : (next s).realReg 116 = realValue := hr
    have h1' : (next s).natReg 26 = 1 := by simp [next,h1]
    obtain ⟨t,ht,htp,htn,htvals,htframe⟩ := ih (base+stride) (next s) hp' hn' hd' hz' hv' hr' h1'
    refine ⟨t,?_,?_,htn,?_,?_⟩
    · have heq : 4+(6*n+2)+2 = 6*(n+1)+2 := by omega
      rw [← heq]
      exact Eval.loopYes htest hb ht
    · rw [htp]
      ring
    · intro j hj
      by_cases hj0 : j = 0
      · subst j
        have hout : ∀ k < n, base+stride*0 ≠ base+stride+stride*k := by
          intro k hk
          have hh : 0 < stride+stride*k := by positivity
          omega
        have hf := htframe (base+stride*0) hout
        simpa [next,hp,hv,hr] using hf
      · obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
        have hk : k < n := by omega
        have heq : base+stride+stride*k = base+stride*(k+1) := by ring
        simpa only [heq] using htvals k hk
    · intro address hout
      have htail : ∀ k < n, address ≠ base+stride+stride*k := by
        intro k hk
        have heq : base+stride+stride*k = base+stride*(k+1) := by ring
        rw [heq]
        exact hout (k+1) (by omega)
      have hf := htframe address htail
      have hhead : address ≠ s.natReg 116 := by rw [hp];simpa using hout 0 (by omega)
      refine ⟨hf.1.trans ?_,hf.2.trans ?_⟩
      · exact Function.update_of_ne hhead _ _
      · exact Function.update_of_ne hhead _ _
lemma nat_frame (k : ℕ) (h116 : k ≠ 116) (h118 : k ≠ 118) : NatFrame code k := by
  simp [code,body,Structured.sequence,NatFrame,store,storeN,nadd,nsub,writesNat,Ne.symm h116,Ne.symm h118]
lemma real_frame (k : ℕ) : RealFrame code k := by
  simp [code,body,Structured.sequence,RealFrame,store,storeN,nadd,nsub,writesReal]
end DecrAlmostLinearSSSP.Decremental.Fill
end s92
section s93
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.SnapshotFill
open Structured
lemma setup_fields (N : ℕ) (s : Data) (hz : s.natReg 56 = 0) (h2 : s.natReg 14 = 2) :
    (setupData N s).natReg 116 = s.natReg 50 ∧ (setupData N s).natReg 118 = N ∧
    (setupData N s).natReg 120 = 2 ∧ (setupData N s).natReg 122 = 0 ∧
    (setupData N s).natReg 124 = 0 ∧ (setupData N s).realReg 116 = 0 ∧
    (setupData N s).natReg 26 = s.natReg 26 := by
  simp [setupData,setupAtoms,Atom.effect,instructionEffect,data,Data.machine,hz,h2]
lemma eval_code (N : ℕ) (s : Data) (hz : s.natReg 56 = 0) (h2 : s.natReg 14 = 2) (h1 : s.natReg 26 = 1) :
    ∃ t, Eval (code N) s (6*N+8) t ∧
      (∀ j < N, t.natMem (s.natReg 50+2*j) = 0 ∧ t.realMem (s.natReg 50+2*j) = 0) ∧
      (∀ address, (∀ j < N, address ≠ s.natReg 50+2*j) →
        t.natMem address = s.natMem address ∧ t.realMem address = s.realMem address) := by
  have hs : Eval (setup N) s 6 (setupData N s) := eval_sequence_atoms (setupAtoms N) s
  obtain ⟨hp,hn,hd,hz',hv,hr,h26⟩ := setup_fields N s hz h2
  obtain ⟨t,ht,_,_,hvalues,hframe⟩ := Fill.eval_code N (s.natReg 50) 2 0 0 (setupData N s)
    (by omega) hp hn hd hz' hv hr (h26.trans h1)
  refine ⟨t,?_,hvalues,hframe⟩
  have heq : 6+(6*N+2) = 6*N+8 := by omega
  simpa only [code,heq] using Eval.seq hs ht
lemma nat_frame (N k : ℕ) (h116 : k ≠ 116) (h118 : k ≠ 118) (h120 : k ≠ 120)
    (h122 : k ≠ 122) (h124 : k ≠ 124) : NatFrame (code N) k := by
  refine ⟨?_,Fill.nat_frame k h116 h118⟩
  simp [setup,setupAtoms,Structured.sequence,NatFrame,writesNat,
    Ne.symm h116,Ne.symm h118,Ne.symm h120,Ne.symm h122,Ne.symm h124]
lemma real_frame (N k : ℕ) (h116 : k ≠ 116) : RealFrame (code N) k := by
  refine ⟨?_,Fill.real_frame k⟩
  simp [setup,setupAtoms,Structured.sequence,RealFrame,writesReal,Ne.symm h116]
end DecrAlmostLinearSSSP.Decremental.SnapshotFill
end s93
section s94
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.ScaledCeiling
open Structured
lemma productReal_eval (s : Data) (d p x N : ℕ)
    (hz : s.natReg 56 = 0) (hrz : s.realReg 56 = 0)
    (hnonneg : 0 ≤ s.realReg x) (hupper : s.realReg x ≤ (2 : ℝ)^N) :
    ∃ cost t, Eval (productReal d p x) s cost t ∧
      t.natReg d = s.natReg p*⌈s.realReg x⌉₊ ∧
      cost ≤ (dispatchCharge ceilingProgram.code+3)*(16*N+32)+3 ∧
      (∀ address, (∀ a, address ≠ s.natReg 48+2*a+1) →
        t.realMem address = s.realMem address ∧ t.natMem address = s.natMem address) ∧
      (∀ k, 10 ≤ k → Even k → k ≠ d → k ≠ 58 →
        t.natReg k = s.natReg k ∧ t.realReg k = s.realReg k) := by
  let a : Data := {s with natReg := Function.update s.natReg 58 (s.natReg p+s.natReg 56)}
  let b : Data := {a with realReg := Function.update a.realReg 58 (a.realReg x+a.realReg 56)}
  have ha : Eval (nadd 58 p 56) s 1 a := eval_nadd s 58 p 56
  have hb : Eval (add 58 x 56) a 1 b := eval_add a 58 x 56
  have hbP : b.natReg 58 = s.natReg p := by simp [b,a,hz]
  have hbX : b.realReg 58 = s.realReg x := by simp [b,a,hrz]
  have hbN : b.natReg 56 = 0 := by simp [b,a,hz]
  have hbR : b.realReg 56 = 0 := by simp [b,a,hrz]
  obtain ⟨c,u,hu,hout,hcost,hmem,hregs⟩ := call_eval b N hbN hbR (by rwa [hbX]) (by rwa [hbX])
  have hu56 : u.natReg 56 = 0 := (hregs 56 (by omega) (by decide)).1.trans hbN
  let t : Data := {u with natReg := Function.update u.natReg d (u.natReg (shadowReg 3)+u.natReg 56)}
  have ht : Eval (nadd d (shadowReg 3) 56) u 1 t := eval_nadd u d (shadowReg 3) 56
  refine ⟨1+(1+(c+1)),t,Eval.seq ha (Eval.seq hb (Eval.seq hu ht)),?_,by omega,?_,?_⟩
  · simp [t,hout,hbP,hbX,hu56]
  · intro address haddr
    exact hmem address (by simpa only [b,a,Function.update_of_ne (by decide : (48 : ℕ) ≠ 58)] using haddr)
  · intro k hk heven hkd hk58
    have hh := hregs k hk heven
    simpa [t,b,a,Function.update_of_ne hkd,Function.update_of_ne hk58] using hh
lemma productReal_nat_frame (d p x k : ℕ) (hk : 10 ≤ k) (heven : Even k)
    (hd : k ≠ d) (h58 : k ≠ 58) : NatFrame (productReal d p x) k := by
  exact ⟨Ne.symm h58,not_false,call_nat_even k hk heven,Ne.symm hd⟩
lemma productReal_real_frame (d p x k : ℕ) (hk : 10 ≤ k) (heven : Even k)
    (h58 : k ≠ 58) : RealFrame (productReal d p x) k := by
  exact ⟨not_false,Ne.symm h58,call_real_even k hk heven,not_false⟩
lemma productNat_eval (s : Data) (d p x N : ℕ)
    (hz : s.natReg 56 = 0) (hrz : s.realReg 56 = 0)
    (hupper : (s.natReg x : ℝ) ≤ (2 : ℝ)^N) :
    ∃ cost t, Eval (productNat d p x) s cost t ∧
      t.natReg d = s.natReg p*s.natReg x ∧
      cost ≤ (dispatchCharge ceilingProgram.code+3)*(16*N+32)+4 ∧
      (∀ address, (∀ a, address ≠ s.natReg 48+2*a+1) →
        t.realMem address = s.realMem address ∧ t.natMem address = s.natMem address) := by
  let a : Data := {s with realReg := Function.update s.realReg 200 (s.natReg x : ℝ)}
  have ha : Eval (cast 200 x) s 1 a := eval_cast s 200 x
  obtain ⟨c,t,ht,hout,hcost,hmem,_⟩ := productReal_eval a d p 200 N hz
    (by simpa [a] using hrz) (by simp [a]) (by simpa [a] using hupper)
  refine ⟨1+c,t,Eval.seq ha ht,?_,by omega,hmem⟩
  simpa only [a,Function.update_self,Nat.ceil_natCast] using hout
lemma productNat_nat_frame (d p x k : ℕ) (hk : 10 ≤ k) (heven : Even k)
    (hd : k ≠ d) (h58 : k ≠ 58) : NatFrame (productNat d p x) k :=
  ⟨not_false,productReal_nat_frame d p 200 k hk heven hd h58⟩
lemma productNat_real_frame (d p x k : ℕ) (hk : 10 ≤ k) (heven : Even k)
    (h58 : k ≠ 58) (h200 : k ≠ 200) : RealFrame (productNat d p x) k :=
  ⟨Ne.symm h200,productReal_real_frame d p 200 k hk heven h58⟩
end DecrAlmostLinearSSSP.Decremental.ScaledCeiling
end s94
section s95
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.ScaledCeiling
open Structured
lemma batch_nat_frame (ops : List (ℕ × ℕ)) (k : ℕ) (hk : 10 ≤ k) (heven : Even k)
    (h58 : k ≠ 58) (hops : ∀ op ∈ ops, k ≠ op.1) : NatFrame (batch ops) k := by
  induction ops with
  | nil => trivial
  | cons op ops ih =>
    exact ⟨productNat_nat_frame op.1 112 op.2 k hk heven (hops op (by simp)) h58,
      ih (fun other hm => hops other (by simp [hm]))⟩
lemma batch_real_frame (ops : List (ℕ × ℕ)) (k : ℕ) (hk : 10 ≤ k) (heven : Even k)
    (h58 : k ≠ 58) (h200 : k ≠ 200) : RealFrame (batch ops) k := by
  induction ops with
  | nil => trivial
  | cons op ops ih => exact ⟨productNat_real_frame op.1 112 op.2 k hk heven h58 h200,ih⟩
lemma batch_eval (ops : List (ℕ × ℕ)) (s : Data) (N : ℕ) (hvalid : BatchValid ops)
    (hz : s.natReg 56 = 0) (hrz : s.realReg 56 = 0)
    (hupper : ∀ op ∈ ops, (s.natReg op.2 : ℝ) ≤ (2 : ℝ)^N) :
    ∃ cost t, Eval (batch ops) s cost t ∧
      cost ≤ ops.length*((dispatchCharge ceilingProgram.code+3)*(16*N+32)+4) ∧
      (∀ op ∈ ops, t.natReg op.1 = s.natReg 112*s.natReg op.2) ∧
      (∀ address, (∀ a, address ≠ s.natReg 48+2*a+1) →
        t.realMem address = s.realMem address ∧ t.natMem address = s.natMem address) := by
  induction ops generalizing s with
  | nil => exact ⟨0,s,Eval.skip s,by simp,by simp,fun _ _ => ⟨rfl,rfl⟩⟩
  | cons op ops ih =>
    obtain ⟨hnd,hd,hi⟩ := hvalid
    obtain ⟨hd10,hdeven,hd58,hd48,hd56,hd112⟩ := hd op (by simp)
    have hi0 := hi op (by simp)
    obtain ⟨hnotmem,hndtail⟩ := List.nodup_cons.mp hnd
    have hvtail : BatchValid ops := ⟨hndtail,
      fun other hm => hd other (by simp [hm]),fun other hm =>
        ⟨(hi other (by simp [hm])).1,(hi other (by simp [hm])).2.1,
        (hi other (by simp [hm])).2.2.1,fun third ht => (hi other (by simp [hm])).2.2.2 third (by simp [ht])⟩⟩
    obtain ⟨c,u,hu,hout,hcost,hframe⟩ := productNat_eval s op.1 112 op.2 N hz hrz (hupper op (by simp))
    have hu56 : u.natReg 56 = 0 := (hu.nat_frame (productNat_nat_frame _ _ _ 56 (by omega) (by decide) (Ne.symm hd56) (by omega))).trans hz
    have hur56 : u.realReg 56 = 0 := (hu.real_frame (productNat_real_frame _ _ _ 56 (by omega) (by decide) (by omega) (by omega))).trans hrz
    have hu48 : u.natReg 48 = s.natReg 48 := hu.nat_frame (productNat_nat_frame _ _ _ 48 (by omega) (by decide) (Ne.symm hd48) (by omega))
    have hu112 : u.natReg 112 = s.natReg 112 := hu.nat_frame (productNat_nat_frame _ _ _ 112 (by omega) (by decide) (Ne.symm hd112) (by omega))
    have huinput : ∀ other ∈ ops, u.natReg other.2 = s.natReg other.2 := by
      intro other hm
      have hh := hi other (by simp [hm])
      exact hu.nat_frame (productNat_nat_frame _ _ _ other.2 hh.1 hh.2.1 (hh.2.2.2 op (by simp)) hh.2.2.1)
    obtain ⟨rest,t,ht,hrest,htout,htframe⟩ := ih u hvtail hu56 hur56
      (fun other hm => by rw [huinput other hm];exact hupper other (by simp [hm]))
    refine ⟨c+rest,t,Eval.seq hu ht,?_,?_,?_⟩
    · simp only [List.length_cons]
      nlinarith only [hcost,hrest]
    · intro other hm
      rcases List.mem_cons.mp hm with heq | hm
      · subst other
        have hkeep : NatFrame (batch ops) op.1 := by
          apply batch_nat_frame ops op.1 hd10 hdeven hd58
          intro other hm
          intro heq
          exact hnotmem (List.mem_map.mpr ⟨other,hm,heq.symm⟩)
        rw [ht.nat_frame hkeep,hout]
      · rw [htout other hm,hu112,huinput other hm]
    · intro address ha
      have hh := htframe address (by simpa only [hu48] using ha)
      have hg := hframe address ha
      exact ⟨hh.1.trans hg.1,hh.2.trans hg.2⟩
end DecrAlmostLinearSSSP.Decremental.ScaledCeiling
end s95
section s96
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.ScaleParameters
open Structured
lemma ordinary_valid : ScaledCeiling.BatchValid ordinaryOps := by
  norm_num [ScaledCeiling.BatchValid,ordinaryOps,List.pairwise_cons]
lemma ordinary_eval (s : Data) (i : Input) (hi : i.Valid)
    (hm : s.natReg 64 = i.size) (hn : s.natReg 66 = i.n) (hk : s.natReg 68 = i.k)
    (hs : s.natReg 72 = i.source.val) (hF : s.natReg 112 = bankFactor (s.natReg 110))
    (hz : s.natReg 56 = 0) (hrz : s.realReg 56 = 0) :
    ∃ cost t, Eval ordinary s cost t ∧
      cost ≤ 4*((dispatchCharge ScaledCeiling.ceilingProgram.code+3)*(16*utilityDepth i.size+32)+4)+65 ∧
      t.natReg 154 = bankFactor (s.natReg 110)*i.n ∧
      t.natReg 156 = bankFactor (s.natReg 110)*i.k ∧
      t.natReg 158 = bankFactor (s.natReg 110)*(64*i.size) ∧
      t.natReg 160 = bankFactor (s.natReg 110)*i.source.val ∧
      (∀ address, (∀ a, address ≠ s.natReg 48+2*a+1) →
        t.realMem address = s.realMem address ∧ t.natMem address = s.natMem address) := by
  let a : Data := {s with natReg := Function.update s.natReg 204 (64*s.natReg 64)}
  have ha : Eval (structuredConstant 204 64 64) s 65 a := structuredConstant_eval s 204 64 64 (by decide)
  have ha56 : a.natReg 56 = 0 := by simpa [a] using hz
  have har56 : a.realReg 56 = 0 := hrz
  have hmpos : 1 ≤ i.size := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (lt_of_lt_of_le (input_vertex_positive i) hi.1))
  have hsmall : (64*i.size : ℕ) ≤ 512*i.size^2 := by nlinarith
  have hbound : ((64*i.size : ℕ) : ℝ) ≤ (2 : ℝ)^utilityDepth i.size := by
    apply le_trans (show ((64*i.size : ℕ) : ℝ) ≤ 512*(i.size : ℝ)^2 by exact_mod_cast hsmall)
    exact utilityDepth_power i.size
  have hsrc : i.source.val ≤ 64*i.size := by have hh := i.source.isLt;have hh' := hi.1;omega
  have hnsize : i.n ≤ 64*i.size := by have hh := hi.1;omega
  have hksize : i.k ≤ 64*i.size := by have hh := hi.2.1;omega
  have hupper : ∀ op ∈ ordinaryOps, (a.natReg op.2 : ℝ) ≤ (2 : ℝ)^utilityDepth i.size := by
    intro op hop
    simp only [ordinaryOps,List.mem_cons,List.not_mem_nil,or_false] at hop
    rcases hop with rfl | rfl | rfl | rfl
    · have hh : (a.natReg 66 : ℝ) ≤ ((64*i.size : ℕ) : ℝ) := by exact_mod_cast (show a.natReg 66 ≤ 64*i.size by simpa [a,hn] using hnsize)
      exact hh.trans hbound
    · have hh : (a.natReg 68 : ℝ) ≤ ((64*i.size : ℕ) : ℝ) := by exact_mod_cast (show a.natReg 68 ≤ 64*i.size by simpa [a,hk] using hksize)
      exact hh.trans hbound
    · simpa [a,hm] using hbound
    · have hh : (a.natReg 72 : ℝ) ≤ ((64*i.size : ℕ) : ℝ) := by exact_mod_cast (show a.natReg 72 ≤ 64*i.size by simpa [a,hs] using hsrc)
      exact hh.trans hbound
  obtain ⟨c,t,ht,hc,hout,hframe⟩ := ScaledCeiling.batch_eval ordinaryOps a (utilityDepth i.size) ordinary_valid ha56 har56 hupper
  refine ⟨65+c,t,Eval.seq ha ht,?_,?_,?_,?_,?_,?_⟩
  · have hlen : ordinaryOps.length = 4 := rfl
    rw [hlen] at hc
    omega
  · simpa [a,hn,hF] using hout (154,66) (by simp [ordinaryOps])
  · simpa [a,hk,hF] using hout (156,68) (by simp [ordinaryOps])
  · simpa [a,hm,hF] using hout (158,204) (by simp [ordinaryOps])
  · simpa [a,hs,hF] using hout (160,72) (by simp [ordinaryOps])
  · intro address hh
    exact hframe address (by simpa [a] using hh)
end DecrAlmostLinearSSSP.Decremental.ScaleParameters
end s96
section s97
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.ScaleParameters
open Structured
lemma high_fields (s : Data) :
    (highData s).realReg 202 = 512*(s.natReg 66 : ℝ)/s.realReg 64 ∧
    (highData s).natReg = s.natReg ∧
    (highData s).realMem = s.realMem ∧ (highData s).natMem = s.natMem := by
  simp [highData,highAtoms,Atom.effect,instructionEffect,data,Data.machine]
lemma high_eval (s : Data) (i : Input) (hi : i.Valid)
    (heps : 1/(i.size : ℝ) < i.accuracy)
    (hn : s.natReg 66 = i.n) (he : s.realReg 64 = i.accuracy)
    (hz : s.natReg 56 = 0) (hrz : s.realReg 56 = 0) :
    ∃ cost t, Eval high s cost t ∧
      cost ≤ (dispatchCharge ScaledCeiling.ceilingProgram.code+3)*(16*utilityDepth i.size+32)+7 ∧
      t.natReg 152 = s.natReg 112*barrierHigh i ∧
      (∀ address, (∀ a, address ≠ s.natReg 48+2*a+1) →
        t.realMem address = s.realMem address ∧ t.natMem address = s.natMem address) := by
  have ha : Eval highCode s 4 (highData s) := eval_sequence_atoms highAtoms s
  obtain ⟨hx,hnat,hrmem,hnmem⟩ := high_fields s
  have hx' : (highData s).realReg 202 = 512*(i.n : ℝ)/i.accuracy := by simpa only [hn,he] using hx
  obtain ⟨hpos,hbound⟩ := normal_barrier_argument_bound i hi heps
  have haz : (highData s).natReg 56 = 0 := by rwa [hnat]
  have harz : (highData s).realReg 56 = 0 := by
    simpa [highData,highAtoms,Atom.effect,instructionEffect,data,Data.machine] using hrz
  obtain ⟨c,t,ht,hout,hcost,hframe,_⟩ := ScaledCeiling.productReal_eval (highData s) 152 112 202
    (utilityDepth i.size) haz harz (by rwa [hx']) (by rwa [hx'])
  refine ⟨4+c,t,Eval.seq ha ht,by omega,?_,?_⟩
  · simpa only [hnat,hx',barrierHigh] using hout
  · intro address haddr
    have hh := hframe address (by simpa only [hnat] using haddr)
    exact ⟨hh.1.trans (congrFun hrmem address),hh.2.trans (congrFun hnmem address)⟩
lemma ordinary_nat_frame (k : ℕ) (hk : 10 ≤ k) (heven : Even k)
    (h204 : k ≠ 204) (h58 : k ≠ 58)
    (h154 : k ≠ 154) (h156 : k ≠ 156) (h158 : k ≠ 158) (h160 : k ≠ 160) : NatFrame ordinary k := by
  refine ⟨?_,ScaledCeiling.batch_nat_frame ordinaryOps k hk heven h58 ?_⟩
  · exact ⟨Ne.symm h204,repeatedAdd_nat_frame _ _ _ _ (Ne.symm h204)⟩
  · intro op hop
    simp only [ordinaryOps,List.mem_cons,List.not_mem_nil,or_false] at hop
    rcases hop with rfl | rfl | rfl | rfl <;> assumption
lemma ordinary_real_frame (k : ℕ) (hk : 10 ≤ k) (heven : Even k)
    (h58 : k ≠ 58) (h200 : k ≠ 200) : RealFrame ordinary k := by
  refine ⟨?_,ScaledCeiling.batch_real_frame ordinaryOps k hk heven h58 h200⟩
  exact ⟨not_false,repeatedAdd_real_frame _ _ _ _⟩
lemma high_nat_frame (k : ℕ) (hk : 10 ≤ k) (heven : Even k)
    (h58 : k ≠ 58) (h152 : k ≠ 152) : NatFrame high k := by
  refine ⟨?_,ScaledCeiling.productReal_nat_frame _ _ _ k hk heven h152 h58⟩
  simp [highCode,highAtoms,Structured.sequence,NatFrame,writesNat]
lemma high_real_frame (k : ℕ) (hk : 10 ≤ k) (heven : Even k)
    (h58 : k ≠ 58) (h202 : k ≠ 202) (h204 : k ≠ 204) : RealFrame high k := by
  refine ⟨?_,ScaledCeiling.productReal_real_frame _ _ _ k hk heven h58⟩
  simp [highCode,highAtoms,Structured.sequence,RealFrame,writesReal,Ne.symm h202,Ne.symm h204]
lemma prepare_nat_frame (k : ℕ) (hk : 10 ≤ k) (heven : Even k)
    (h204 : k ≠ 204) (h58 : k ≠ 58) (h154 : k ≠ 154) (h156 : k ≠ 156)
    (h158 : k ≠ 158) (h160 : k ≠ 160) (h152 : k ≠ 152) : NatFrame prepare k :=
  ⟨ordinary_nat_frame k hk heven h204 h58 h154 h156 h158 h160,high_nat_frame k hk heven h58 h152⟩
lemma prepare_real_frame (k : ℕ) (hk : 10 ≤ k) (heven : Even k)
    (h58 : k ≠ 58) (h200 : k ≠ 200) (h202 : k ≠ 202) (h204 : k ≠ 204) : RealFrame prepare k :=
  ⟨ordinary_real_frame k hk heven h58 h200,high_real_frame k hk heven h58 h202 h204⟩
lemma prepare_eval (s : Data) (i : Input) (hi : i.Valid)
    (heps : 1/(i.size : ℝ) < i.accuracy)
    (hm : s.natReg 64 = i.size) (hn : s.natReg 66 = i.n) (hk : s.natReg 68 = i.k)
    (hs : s.natReg 72 = i.source.val) (he : s.realReg 64 = i.accuracy)
    (hF : s.natReg 112 = bankFactor (s.natReg 110))
    (hz : s.natReg 56 = 0) (hrz : s.realReg 56 = 0) :
    ∃ cost t, Eval prepare s cost t ∧
      cost ≤ 5*((dispatchCharge ScaledCeiling.ceilingProgram.code+3)*(16*utilityDepth i.size+32))+88 ∧
      t.natReg 154 = bankFactor (s.natReg 110)*i.n ∧
      t.natReg 156 = bankFactor (s.natReg 110)*i.k ∧
      t.natReg 158 = bankFactor (s.natReg 110)*(64*i.size) ∧
      t.natReg 160 = bankFactor (s.natReg 110)*i.source.val ∧
      t.natReg 152 = bankFactor (s.natReg 110)*barrierHigh i ∧
      (∀ address, (∀ a, address ≠ s.natReg 48+2*a+1) →
        t.realMem address = s.realMem address ∧ t.natMem address = s.natMem address) := by
  obtain ⟨first,u,hu,hcost,hun,huk,hum,hus,huframe⟩ := ordinary_eval s i hi hm hn hk hs hF hz hrz
  have hnat (k : ℕ) (hk10 : 10 ≤ k) (hev : Even k) (h204 : k ≠ 204) (h58 : k ≠ 58)
      (h154 : k ≠ 154) (h156 : k ≠ 156) (h158 : k ≠ 158) (h160 : k ≠ 160) :
      u.natReg k = s.natReg k := hu.nat_frame (ordinary_nat_frame k hk10 hev h204 h58 h154 h156 h158 h160)
  have hu66 : u.natReg 66 = i.n := (hnat 66 (by omega) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hn
  have hu56 : u.natReg 56 = 0 := (hnat 56 (by omega) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hz
  have hu112 : u.natReg 112 = s.natReg 112 := hnat 112 (by omega) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hu48 : u.natReg 48 = s.natReg 48 := hnat 48 (by omega) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hur64 : u.realReg 64 = i.accuracy := (hu.real_frame (ordinary_real_frame 64 (by omega) (by decide) (by omega) (by omega))).trans he
  have hur56 : u.realReg 56 = 0 := (hu.real_frame (ordinary_real_frame 56 (by omega) (by decide) (by omega) (by omega))).trans hrz
  obtain ⟨last,t,ht,htcost,hthigh,htframe⟩ := high_eval u i hi heps hu66 hur64 hu56 hur56
  have hkeep (k : ℕ) (hk10 : 10 ≤ k) (hev : Even k) (h58 : k ≠ 58) (h152 : k ≠ 152) :
      t.natReg k = u.natReg k := ht.nat_frame (high_nat_frame k hk10 hev h58 h152)
  refine ⟨first+last,t,Eval.seq hu ht,by omega,?_,?_,?_,?_,?_,?_⟩
  · exact (hkeep 154 (by omega) (by decide) (by omega) (by omega)).trans hun
  · exact (hkeep 156 (by omega) (by decide) (by omega) (by omega)).trans huk
  · exact (hkeep 158 (by omega) (by decide) (by omega) (by omega)).trans hum
  · exact (hkeep 160 (by omega) (by decide) (by omega) (by omega)).trans hus
  · simpa only [hu112,hF] using hthigh
  · intro address haddr
    have hh := htframe address (by simpa only [hu48] using haddr)
    have hg := huframe address haddr
    exact ⟨hh.1.trans hg.1,hh.2.trans hg.2⟩
end DecrAlmostLinearSSSP.Decremental.ScaleParameters
end s97
section s98
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.ScaleParameters
open Structured
lemma fields_eval (s : Data) : Eval writeFields s 13 (fieldData s) := eval_sequence_atoms fieldAtoms s
lemma fields_values (s : Data) (hz : s.natReg 56 = 0) (h2 : s.natReg 14 = 2) :
    (fieldData s).natMem (s.natReg 50) = s.natReg 154 ∧
    (fieldData s).natMem (s.natReg 50+2) = s.natReg 156 ∧
    (fieldData s).natMem (s.natReg 50+4) = s.natReg 158 ∧
    (fieldData s).natMem (s.natReg 50+6) = s.natReg 152 ∧
    (fieldData s).natMem (s.natReg 50+8) = s.natReg 160 ∧
    (fieldData s).realMem (s.natReg 50) = s.realReg 64/16 := by
  simp [fieldData,fieldAtoms,Atom.effect,instructionEffect,data,Data.machine,hz,h2,Nat.add_assoc]
lemma fields_memory_frame (s : Data) (hz : s.natReg 56 = 0) (h2 : s.natReg 14 = 2)
    (address : ℕ) (h0 : address ≠ s.natReg 50) (h2' : address ≠ s.natReg 50+2)
    (h4 : address ≠ s.natReg 50+4) (h6 : address ≠ s.natReg 50+6) (h8 : address ≠ s.natReg 50+8) :
    (fieldData s).natMem address = s.natMem address ∧ (fieldData s).realMem address = s.realMem address := by
  simp [fieldData,fieldAtoms,Atom.effect,instructionEffect,data,Data.machine,hz,h2,Nat.add_assoc,
    Function.update_of_ne h0,Function.update_of_ne h2',Function.update_of_ne h4,
    Function.update_of_ne h6,Function.update_of_ne h8]
lemma fields_real_frame (k : ℕ) (h208 : k ≠ 208) : RealFrame writeFields k := by
  simp [writeFields,fieldAtoms,Structured.sequence,RealFrame,writesReal,Ne.symm h208]
lemma fields_nat_frame (k : ℕ) (h206 : k ≠ 206) : NatFrame writeFields k := by
  simp [writeFields,fieldAtoms,Structured.sequence,NatFrame,writesNat,Ne.symm h206]
end DecrAlmostLinearSSSP.Decremental.ScaleParameters
end s98
section s99
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.ScaleParameters
open Structured
lemma fields_real_memory (s : Data) : (fieldData s).realMem =
    Function.update s.realMem (s.natReg 50) (s.realReg 64/16) := by
  simp [fieldData,fieldAtoms,Atom.effect,instructionEffect,data,Data.machine]
lemma initial_snapshot (s : Data) (i : Input) (p : Program) (scaleIndex F N : ℕ)
    (hz : s.natReg 56 = 0) (h2 : s.natReg 14 = 2)
    (hn : s.natReg 154 = F*i.n) (hk : s.natReg 156 = F*i.k)
    (hm : s.natReg 158 = F*(64*i.size)) (hW : s.natReg 152 = F*barrierHigh i)
    (hs : s.natReg 160 = F*i.source.val) (he : s.realReg 64 = i.accuracy)
    (hzeroNat : ∀ j, j < N → 5 ≤ j → s.natMem (s.natReg 50+2*j) = 0)
    (hzeroReal : ∀ j, j < N → s.realMem (s.natReg 50+2*j) = 0) :
    (∀ j, j < N → (fieldData s).natMem (s.natReg 50+2*j) =
      F*(initialMachine p (barrierInput i scaleIndex)).natReg j) ∧
    (∀ j, j < N → (fieldData s).realMem (s.natReg 50+2*j) =
      (initialMachine p (barrierInput i scaleIndex)).realReg j) := by
  obtain ⟨h0,h2',h4,h6,h8,hr0⟩ := fields_values s hz h2
  constructor
  · intro j hjN
    by_cases hj : j < 5
    · interval_cases j
      · simpa only [Nat.mul_zero,Nat.add_zero,initialMachine,barrierInput,ite_true] using h0.trans hn
      · simpa [initialMachine,barrierInput] using h2'.trans hk
      · simpa [initialMachine,barrierInput] using h4.trans hm
      · simpa [initialMachine,barrierInput] using h6.trans hW
      · simpa [initialMachine,barrierInput] using h8.trans hs
    · have hj5 : 5 ≤ j := by omega
      have hf := fields_memory_frame s hz h2 (s.natReg 50+2*j)
        (by omega) (by omega) (by omega) (by omega) (by omega)
      rw [hf.1,hzeroNat j hjN hj5]
      simp [initialMachine,show j ≠ 0 by omega,show j ≠ 1 by omega,
        show j ≠ 2 by omega,show j ≠ 3 by omega,show j ≠ 4 by omega]
  · intro j hjN
    by_cases hj : j = 0
    · subst j
      simpa [initialMachine,barrierInput,he] using hr0
    · rw [fields_real_memory,Function.update_of_ne (show s.natReg 50+2*j ≠ s.natReg 50 by omega),hzeroReal j hjN]
      simp [initialMachine,hj]
end DecrAlmostLinearSSSP.Decremental.ScaleParameters
end s99
section s100
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.ScaleParameters
open Structured
lemma initializeSnapshot_eval (N : ℕ) (s : Data) (p : Program) (i : Input) (hi : i.Valid)
    (heps : 1/(i.size : ℝ) < i.accuracy) (hN : 5 ≤ N)
    (hm : s.natReg 64 = i.size) (hn : s.natReg 66 = i.n) (hk : s.natReg 68 = i.k)
    (hs : s.natReg 72 = i.source.val) (he : s.realReg 64 = i.accuracy)
    (hF : s.natReg 112 = bankFactor (s.natReg 110))
    (hz : s.natReg 56 = 0) (hrz : s.realReg 56 = 0) (h2 : s.natReg 14 = 2) (h1 : s.natReg 26 = 1)
    (hbefore : ∀ j < N, s.natReg 50+2*j < s.natReg 48) :
    ∃ cost t, Eval (initializeSnapshot N) s cost t ∧
      cost ≤ 6*N+5*((dispatchCharge ScaledCeiling.ceilingProgram.code+3)*(16*utilityDepth i.size+32))+109 ∧
      t.natReg 50 = s.natReg 50 ∧
      t.natReg 154 = bankFactor (s.natReg 110)*i.n ∧
      t.natReg 152 = bankFactor (s.natReg 110)*barrierHigh i ∧
      (∀ j < N, t.natMem (t.natReg 50+2*j) =
        bankFactor (s.natReg 110)*(initialMachine p (barrierInput i (s.natReg 110))).natReg j ∧
        t.realMem (t.natReg 50+2*j) = (initialMachine p (barrierInput i (s.natReg 110))).realReg j) ∧
      (∀ address, (∀ j < N, address ≠ s.natReg 50+2*j) →
        (∀ a, address ≠ s.natReg 48+2*a+1) →
        t.natMem address = s.natMem address ∧ t.realMem address = s.realMem address) := by
  obtain ⟨b,hb,hfilled,hfillframe⟩ := SnapshotFill.eval_code N s hz h2 h1
  have hbn (k : ℕ) (h116 : k ≠ 116) (h118 : k ≠ 118) (h120 : k ≠ 120) (h122 : k ≠ 122) (h124 : k ≠ 124) : b.natReg k = s.natReg k :=
    hb.nat_frame (SnapshotFill.nat_frame N k h116 h118 h120 h122 h124)
  have hbr (k : ℕ) (h116 : k ≠ 116) : b.realReg k = s.realReg k := hb.real_frame (SnapshotFill.real_frame N k h116)
  have hb64 : b.natReg 64 = i.size := (hbn 64 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hm
  have hb66 : b.natReg 66 = i.n := (hbn 66 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hn
  have hb68 : b.natReg 68 = i.k := (hbn 68 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hk
  have hb72 : b.natReg 72 = i.source.val := (hbn 72 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hs
  have hb110 : b.natReg 110 = s.natReg 110 := hbn 110 (by omega) (by omega) (by omega) (by omega) (by omega)
  have hbF : b.natReg 112 = bankFactor (b.natReg 110) := by
    rw [hbn 112 (by omega) (by omega) (by omega) (by omega) (by omega),hb110,hF]
  have hbz : b.natReg 56 = 0 := (hbn 56 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hz
  have hbrz : b.realReg 56 = 0 := (hbr 56 (by omega)).trans hrz
  have hbe : b.realReg 64 = i.accuracy := (hbr 64 (by omega)).trans he
  have hb50 : b.natReg 50 = s.natReg 50 := hbn 50 (by omega) (by omega) (by omega) (by omega) (by omega)
  have hb48 : b.natReg 48 = s.natReg 48 := hbn 48 (by omega) (by omega) (by omega) (by omega) (by omega)
  obtain ⟨prep,c,hc,hcost,hcn,hck,hcm,hcs,hcW,hprepframe⟩ := prepare_eval b i hi heps hb64 hb66 hb68 hb72 hbe hbF hbz hbrz
  have hcnat (k : ℕ) (hk10 : 10 ≤ k) (hev : Even k) (h204 : k ≠ 204) (h58 : k ≠ 58)
      (h154 : k ≠ 154) (h156 : k ≠ 156) (h158 : k ≠ 158) (h160 : k ≠ 160) (h152 : k ≠ 152) : c.natReg k = b.natReg k :=
    hc.nat_frame (prepare_nat_frame k hk10 hev h204 h58 h154 h156 h158 h160 h152)
  have hcz : c.natReg 56 = 0 := (hcnat 56 (by omega) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hbz
  have hc2 : c.natReg 14 = 2 := (hcnat 14 (by omega) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans
    ((hbn 14 (by omega) (by omega) (by omega) (by omega) (by omega)).trans h2)
  have hc50 : c.natReg 50 = s.natReg 50 := (hcnat 50 (by omega) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hb50
  have hce : c.realReg 64 = i.accuracy := (hc.real_frame (prepare_real_frame 64 (by omega) (by decide) (by omega) (by omega) (by omega) (by omega))).trans hbe
  have hzero (j : ℕ) (hj : j < N) : c.natMem (c.natReg 50+2*j) = 0 ∧ c.realMem (c.natReg 50+2*j) = 0 := by
    rw [hc50]
    have hh := hprepframe (s.natReg 50+2*j) (by
      intro a
      rw [hb48]
      have ht := hbefore j hj
      omega)
    exact ⟨hh.2.trans (hfilled j hj).1,hh.1.trans (hfilled j hj).2⟩
  have hn' : c.natReg 154 = bankFactor (s.natReg 110)*i.n := by simpa only [hb110] using hcn
  have hk' : c.natReg 156 = bankFactor (s.natReg 110)*i.k := by simpa only [hb110] using hck
  have hm' : c.natReg 158 = bankFactor (s.natReg 110)*(64*i.size) := by simpa only [hb110] using hcm
  have hs' : c.natReg 160 = bankFactor (s.natReg 110)*i.source.val := by simpa only [hb110] using hcs
  have hW' : c.natReg 152 = bankFactor (s.natReg 110)*barrierHigh i := by simpa only [hb110] using hcW
  obtain ⟨hns,hrs⟩ := initial_snapshot c i p (s.natReg 110) (bankFactor (s.natReg 110)) N hcz hc2 hn' hk' hm' hW' hs' hce
    (fun j hj _ => (hzero j hj).1) (fun j hj => (hzero j hj).2)
  let t := fieldData c
  have hfields := fields_eval c
  have ht50 : t.natReg 50 = s.natReg 50 := (hfields.nat_frame (fields_nat_frame 50 (by omega))).trans hc50
  refine ⟨(6*N+8)+(prep+13),t,Eval.seq hb (Eval.seq hc hfields),by omega,ht50,?_,?_,?_,?_⟩
  · exact (hfields.nat_frame (fields_nat_frame 154 (by omega))).trans hn'
  · exact (hfields.nat_frame (fields_nat_frame 152 (by omega))).trans hW'
  · intro j hj
    have hbase : t.natReg 50 = c.natReg 50 := hfields.nat_frame (fields_nat_frame 50 (by omega))
    rw [hbase]
    exact ⟨hns j hj,hrs j hj⟩
  · intro address hout hbank
    have hf := fields_memory_frame c hcz hc2 address
      (by rw [hc50];simpa using hout 0 (by omega))
      (by rw [hc50];simpa using hout 1 (by omega))
      (by rw [hc50];simpa using hout 2 (by omega))
      (by rw [hc50];simpa using hout 3 (by omega))
      (by rw [hc50];simpa using hout 4 (by omega))
    have hpref := hprepframe address (by simpa only [hb48] using hbank)
    have hff := hfillframe address hout
    exact ⟨hf.1.trans (hpref.2.trans hff.1),hf.2.trans (hpref.1.trans hff.2)⟩
end DecrAlmostLinearSSSP.Decremental.ScaleParameters
end s100
section s101
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma registerBound_ge (code : List Instruction) : 8 ≤ registerBound code := by unfold registerBound;omega
lemma register_operand_bound (code : List Instruction) (ins : Instruction) (hi : ins ∈ code)
    (j : ℕ) (hj : j ∈ instructionRegisters ins) : j < registerBound code := by
  have hmem : j ∈ code.flatMap instructionRegisters := List.mem_flatMap.mpr ⟨ins,hi,hj⟩
  have hle := List.single_le_sum (fun x _ => Nat.zero_le x) j hmem
  unfold registerBound
  omega
lemma writesNat_operand (ins : Instruction) (j : ℕ) (h : writesNat ins j) : j ∈ instructionRegisters ins := by
  cases ins <;> simp only [writesNat] at h
  all_goals try contradiction
  all_goals subst j; simp [instructionRegisters]
lemma writesReal_operand (ins : Instruction) (j : ℕ) (h : writesReal ins j) : j ∈ instructionRegisters ins := by
  cases ins <;> simp only [writesReal] at h
  all_goals try contradiction
  all_goals subst j; simp [instructionRegisters]
lemma execute_nat_tail (p : Program) (c : Machine) (t j : ℕ) (hj : registerBound p.code ≤ j) :
    (execute p c t).natReg j = c.natReg j := by
  apply execute_nat_frame
  intro n hn ins hins hwrite
  have hmem := List.mem_of_getElem? hins
  have hbound := register_operand_bound p.code ins hmem j (writesNat_operand ins j hwrite)
  omega
lemma execute_real_tail (p : Program) (c : Machine) (t j : ℕ) (hj : registerBound p.code ≤ j) :
    (execute p c t).realReg j = c.realReg j := by
  apply execute_real_frame
  intro n hn ins hins hwrite
  have hmem := List.mem_of_getElem? hins
  have hbound := register_operand_bound p.code ins hmem j (writesReal_operand ins j hwrite)
  omega
lemma ZeroRegisterTail.execute {p : Program} {c : Machine} (h : ZeroRegisterTail (registerBound p.code) c) (t : ℕ) :
    ZeroRegisterTail (registerBound p.code) (execute p c t) := by
  intro j hj
  rw [execute_nat_tail p c t j hj,execute_real_tail p c t j hj]
  exact h j hj
lemma ZeroRegisterTail.ends {p : Program} {c d : Machine} (h : ZeroRegisterTail (registerBound p.code) c)
    (he : Ends p c d) : ZeroRegisterTail (registerBound p.code) d := by
  obtain ⟨t,rfl,_,_⟩ := he
  exact h.execute t
lemma initialMachine_zero_tail (p : Program) (i : Input) : ZeroRegisterTail (registerBound p.code) (initialMachine p i) := by
  intro j hj
  have hb := registerBound_ge p.code
  have h0 : j ≠ 0 := by omega
  have h1 : j ≠ 1 := by omega
  have h2 : j ≠ 2 := by omega
  have h3 : j ≠ 3 := by omega
  have h4 : j ≠ 4 := by omega
  simp [initialMachine,h0,h1,h2,h3,h4]
lemma ZeroRegisterTail.deletion {p : Program} {c : Machine} (h : ZeroRegisterTail (registerBound p.code) c)
    (e : ℕ) : ZeroRegisterTail (registerBound p.code) (deletionMachine p c e) := by
  intro j hj
  have hb := registerBound_ge p.code
  have h5 : j ≠ 5 := by omega
  simpa only [deletionMachine,resume,Function.update_of_ne h5] using h j hj
lemma OnlineRun.zero_register_tail {p : Program} {i : Input} {ds : List (Fin i.k)} {cs : List Machine}
    (h : OnlineRun p i ds cs) : ∀ c ∈ cs, ZeroRegisterTail (registerBound p.code) c := by
  induction h with
  | @init c he =>
    intro d hd
    have hd' : d = c := by simpa using hd
    subst d
    exact (initialMachine_zero_tail p i).ends he
  | @next ds cs c d hrun hlast e hend ih =>
    intro z hz
    rcases List.mem_append.mp hz with hz|hz
    · exact ih z hz
    · have hz' : z = d := by simpa using hz
      subst z
      exact ((ih c (List.mem_of_getLast? hlast)).deletion e.val).ends hend
end DecrAlmostLinearSSSP.Decremental
end s101
section s102
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
lemma shadowAction_nat_source_frame (ins : Instruction) (j : ℕ) (hw : ¬writesNat ins j) :
    NatFrame (shadowAction ins) (shadowReg j) := by
  have h2 : 2 ≠ shadowReg j := Ne.symm (shadowReg_ne_meta j 2 (by omega))
  have h4 : 4 ≠ shadowReg j := Ne.symm (shadowReg_ne_meta j 4 (by omega))
  have h6 : 6 ≠ shadowReg j := Ne.symm (shadowReg_ne_meta j 6 (by omega))
  cases ins with
  | natural d q =>
    have hne : d ≠ j := hw
    have hs := shadowReg_injective.ne hne
    exact ⟨hs,repeatedAdd_nat_frame _ _ _ _ hs⟩
  | _ =>
    all_goals simp only [writesNat] at hw
    all_goals simp [shadowAction,NatFrame,Structured.natural,rational,Structured.cast,add,sub,mul,Structured.div,
      logarithm,nadd,nsub,load,loadN,store,storeN,Structured.sequence,writesNat,
      shadowReg_injective.eq_iff,hw,h2,h4,h6]
lemma shadowAction_real_source_frame (ins : Instruction) (j : ℕ) (hw : ¬writesReal ins j) :
    RealFrame (shadowAction ins) (shadowReg j) := by
  cases ins with
  | natural d q => exact ⟨not_false,repeatedAdd_real_frame _ _ _ _⟩
  | _ =>
    all_goals simp only [writesReal] at hw
    all_goals simp [shadowAction,RealFrame,Structured.natural,rational,Structured.cast,add,sub,mul,Structured.div,
      logarithm,nadd,nsub,load,loadN,store,storeN,Structured.sequence,writesReal,
      shadowReg_injective.eq_iff,hw]
lemma dispatchAux_nat_source_frame (code : List Instruction) (pc j : ℕ)
    (hw : ∀ ins ∈ code, ¬writesNat ins j) : NatFrame (dispatchAux pc code) (shadowReg j) := by
  have h2 : 2 ≠ shadowReg j := Ne.symm (shadowReg_ne_meta j 2 (by omega))
  have h3 : 3 ≠ shadowReg j := Ne.symm (shadowReg_ne_meta j 3 (by omega))
  have h4 : 4 ≠ shadowReg j := Ne.symm (shadowReg_ne_meta j 4 (by omega))
  have h5 : 5 ≠ shadowReg j := Ne.symm (shadowReg_ne_meta j 5 (by omega))
  have h8 : 8 ≠ shadowReg j := Ne.symm (shadowReg_ne_meta j 8 (by omega))
  induction code generalizing pc with
  | nil => exact ⟨h5,h4⟩
  | cons ins rest ih =>
    exact ⟨h8,⟨⟨h2,h3⟩,shadowAction_nat_source_frame ins j (hw ins List.mem_cons_self)⟩,
      ih (pc+1) (fun tr htr => hw tr (List.mem_cons_of_mem ins htr))⟩
lemma dispatchAux_real_source_frame (code : List Instruction) (pc j : ℕ)
    (hw : ∀ ins ∈ code, ¬writesReal ins j) : RealFrame (dispatchAux pc code) (shadowReg j) := by
  induction code generalizing pc with
  | nil => exact ⟨not_false,not_false⟩
  | cons ins rest ih =>
    exact ⟨not_false,⟨⟨not_false,not_false⟩,shadowAction_real_source_frame ins j (hw ins List.mem_cons_self)⟩,
      ih (pc+1) (fun tr htr => hw tr (List.mem_cons_of_mem ins htr))⟩
end DecrAlmostLinearSSSP.Decremental
end s102
section s103
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
lemma registersBelow_spec (code : List Instruction) (bound : ℕ) :
    registersBelow code bound = true ↔ ∀ ins ∈ code, ∀ j ∈ instructionRegisters ins, j < bound := by
  simp [registersBelow,List.all_eq_true]
lemma registerBound_below (code : List Instruction) : registersBelow code (registerBound code) = true :=
  (registersBelow_spec _ _).mpr (register_operand_bound code)
lemma interpreter_nat_tail_frame (code : List Instruction) (bound j : ℕ)
    (hb : registersBelow code bound = true) (hj : bound ≤ j) : NatFrame (shadowInterpreter code) (shadowReg j) := by
  apply dispatchAux_nat_source_frame
  intro ins hi hw
  have hh := (registersBelow_spec code bound).mp hb ins hi j (writesNat_operand ins j hw)
  omega
lemma interpreter_real_tail_frame (code : List Instruction) (bound j : ℕ)
    (hb : registersBelow code bound = true) (hj : bound ≤ j) : RealFrame (shadowInterpreter code) (shadowReg j) := by
  apply dispatchAux_real_source_frame
  intro ins hi hw
  have hh := (registersBelow_spec code bound).mp hb ins hi j (writesReal_operand ins j hw)
  omega
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
theorem solution : (((((((∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
            DecrAlmostLinearSSSP.Decremental.ScaledCeiling.countScales k) ∧ (∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 84) (instOfNatNat (nat_lit 84))) →
              DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
                DecrAlmostLinearSSSP.Decremental.ScaledCeiling.countScales k)) ∧ ((∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.ScaledCeiling.scaleArea
            k) ∧ (∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
        DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.ScaledCeiling.scaleArea k))) ∧ (((∀ (stride k : Nat),
  @LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 84) (instOfNatNat (nat_lit 84))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 48) (instOfNatNat (nat_lit 48))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.Layout.code stride) k) ∧ (∀ (stride k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.Layout.code stride) k)) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (DecrAlmostLinearSSSP.Decremental.barrierHigh i)) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (j : Nat) (e : Fin i.k),
      And
        (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (DecrAlmostLinearSSSP.Decremental.barrierWeight i j e))
        (@LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.barrierWeight i j e)
          (DecrAlmostLinearSSSP.Decremental.barrierHigh i))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid → ∀ (j : Nat), (DecrAlmostLinearSSSP.Decremental.barrierInput i j).Valid))))) ∧ ((((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
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
              (DecrAlmostLinearSSSP.Decremental.barrierInput i j).n)
            (And
              (@LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.barrierInput i j).W
                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                  (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                  (DecrAlmostLinearSSSP.Decremental.barrierInput i j).size
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              (And
                (@LT.lt.{0} Real Real.instLT
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                    (@Nat.cast.{0} Real Real.instNatCast (DecrAlmostLinearSSSP.Decremental.barrierInput i j).size))
                  (DecrAlmostLinearSSSP.Decremental.barrierInput i j).accuracy)
                (@LT.lt.{0} Real Real.instLT (DecrAlmostLinearSSSP.Decremental.barrierInput i j).accuracy
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))) ∧ (∀ (w : Nat) (d : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) d →
    And
      (@LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast w)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) d
          (@Nat.cast.{0} Real Real.instNatCast
            (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
              (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing)
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@Nat.cast.{0} Real Real.instNatCast w) d)))))
      (@LE.le.{0} Real Real.instLE
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) d
          (@Nat.cast.{0} Real Real.instNatCast
            (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
              (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing)
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@Nat.cast.{0} Real Real.instNatCast w) d))))
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast w)
          d)))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
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
              (@Nat.cast.{0} Real Real.instNatCast (i.weight e)) (DecrAlmostLinearSSSP.Decremental.delta i j)))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
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
            (@Nat.cast.{0} Real Real.instNatCast (DecrAlmostLinearSSSP.Decremental.barrierWeight i j e)))))) ∧ (((∀ (m : Nat),
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
      (DecrAlmostLinearSSSP.Decremental.utilityDepth m))) ∧ (∀ (m : Nat),
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
            (@Max.max.{0} Nat Nat.instMax (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))))))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
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
            (DecrAlmostLinearSSSP.Decremental.utilityDepth i.size)))) ∧ ((∀ (coefficient stride k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 84) (instOfNatNat (nat_lit 84))) →
      @Even.{0} Nat instAddNat k →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 48) (instOfNatNat (nat_lit 48))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 60) (instOfNatNat (nat_lit 60))) →
              @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))) →
                @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))) →
                  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
                    (DecrAlmostLinearSSSP.Decremental.Prepass.code coefficient stride) k) ∧ (∀ (coefficient stride k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 84) (instOfNatNat (nat_lit 84))) →
              DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
                (DecrAlmostLinearSSSP.Decremental.Prepass.code coefficient stride) k)))))) ∧ (((((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast i.size)
      (@HPow.hPow.{0, 0, 0} Real Nat Real
        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (DecrAlmostLinearSSSP.Decremental.utilityDepth i.size))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (i : DecrAlmostLinearSSSP.Decremental.Input),
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
                            (@Eq.{1} Nat (t.natMem address) (s.natMem address)))))))))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Fill.body s
    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (DecrAlmostLinearSSSP.Decremental.Fill.next s)) ∧ (∀ (n base stride value : Nat) (realValue : Real) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
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
                                  (@Eq.{1} Real (t.realMem address) (s.realMem address))))))))) ∧ (((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 116) (instOfNatNat (nat_lit 116))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 118) (instOfNatNat (nat_lit 118))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Fill.code k) ∧ (∀ (k : Nat), DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Fill.code k)) ∧ ((∀ (N : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
      And
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.SnapshotFill.setupData N s).natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 116) (instOfNatNat (nat_lit 116))))
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50)))))
        (And
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.SnapshotFill.setupData N s).natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 118) (instOfNatNat (nat_lit 118))))
            N)
          (And
            (@Eq.{1} Nat
              ((DecrAlmostLinearSSSP.Decremental.SnapshotFill.setupData N s).natReg
                (@OfNat.ofNat.{0} Nat (nat_lit 120) (instOfNatNat (nat_lit 120))))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (And
              (@Eq.{1} Nat
                ((DecrAlmostLinearSSSP.Decremental.SnapshotFill.setupData N s).natReg
                  (@OfNat.ofNat.{0} Nat (nat_lit 122) (instOfNatNat (nat_lit 122))))
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (And
                (@Eq.{1} Nat
                  ((DecrAlmostLinearSSSP.Decremental.SnapshotFill.setupData N s).natReg
                    (@OfNat.ofNat.{0} Nat (nat_lit 124) (instOfNatNat (nat_lit 124))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                (And
                  (@Eq.{1} Real
                    ((DecrAlmostLinearSSSP.Decremental.SnapshotFill.setupData N s).realReg
                      (@OfNat.ofNat.{0} Nat (nat_lit 116) (instOfNatNat (nat_lit 116))))
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
                  (@Eq.{1} Nat
                    ((DecrAlmostLinearSSSP.Decremental.SnapshotFill.setupData N s).natReg
                      (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))))))))) ∧ ((∀ (N : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
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
                    (@Eq.{1} Real (t.realMem address) (s.realMem address))))) ∧ (∀ (N k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 116) (instOfNatNat (nat_lit 116))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 118) (instOfNatNat (nat_lit 118))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 120) (instOfNatNat (nat_lit 120))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 122) (instOfNatNat (nat_lit 122))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 124) (instOfNatNat (nat_lit 124))) →
            DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.SnapshotFill.code N)
              k))))) ∧ ((((∀ (N k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 116) (instOfNatNat (nat_lit 116))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.SnapshotFill.code N) k) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (d p x N : Nat),
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
                              And (@Eq.{1} Nat (t.natReg k) (s.natReg k)) (@Eq.{1} Real (t.realReg k) (s.realReg k)))))))) ∧ ((∀ (d p x k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k d →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
            (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.productReal d p x) k) ∧ ((∀ (d p x k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
        DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
          (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.productReal d p x) k) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (d p x N : Nat),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
      @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast (s.natReg x))
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
              (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.productNat d p x) s cost t)
            (And
              (@Eq.{1} Nat (t.natReg d)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (s.natReg p) (s.natReg x)))
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
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
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
                      (@Eq.{1} Nat (t.natMem address) (s.natMem address))))))))) ∧ (((∀ (d p x k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k d →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
            (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.productNat d p x) k) ∧ (∀ (d p x k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 200) (instOfNatNat (nat_lit 200))) →
          DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
            (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.productNat d p x) k)) ∧ ((∀ (ops : List.{0} (Prod.{0, 0} Nat Nat)) (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
        (∀ (op : Prod.{0, 0} Nat Nat),
            @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (List.{0} (Prod.{0, 0} Nat Nat))
                (@List.instMembership.{0} (Prod.{0, 0} Nat Nat)) ops op →
              @Ne.{1} Nat k (@Prod.fst.{0, 0} Nat Nat op)) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
            (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.batch ops) k) ∧ ((∀ (ops : List.{0} (Prod.{0, 0} Nat Nat)) (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 200) (instOfNatNat (nat_lit 200))) →
          DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
            (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.batch ops) k) ∧ (∀ (ops : List.{0} (Prod.{0, 0} Nat Nat)) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (N : Nat),
  DecrAlmostLinearSSSP.Decremental.ScaledCeiling.BatchValid ops →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
      @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
        (∀ (op : Prod.{0, 0} Nat Nat),
            @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (List.{0} (Prod.{0, 0} Nat Nat))
                (@List.instMembership.{0} (Prod.{0, 0} Nat Nat)) ops op →
              @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast (s.natReg (@Prod.snd.{0, 0} Nat Nat op)))
                (@HPow.hPow.{0, 0, 0} Real Nat Real
                  (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                  N)) →
          ∃ cost t,
            And
              (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.batch ops) s cost t)
              (And
                (@LE.le.{0} Nat instLENat cost
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@List.length.{0} (Prod.{0, 0} Nat Nat) ops)
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
                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
                (And
                  (∀ (op : Prod.{0, 0} Nat Nat),
                    @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (List.{0} (Prod.{0, 0} Nat Nat))
                        (@List.instMembership.{0} (Prod.{0, 0} Nat Nat)) ops op →
                      @Eq.{1} Nat (t.natReg (@Prod.fst.{0, 0} Nat Nat op))
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))))
                          (s.natReg (@Prod.snd.{0, 0} Nat Nat op))))
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
                        (@Eq.{1} Nat (t.natMem address) (s.natMem address)))))))))))) ∧ ((((((DecrAlmostLinearSSSP.Decremental.ScaledCeiling.BatchValid DecrAlmostLinearSSSP.Decremental.ScaleParameters.ordinaryOps) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64)))) i.size →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 66) (instOfNatNat (nat_lit 66)))) i.n →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68)))) i.k →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72))))
              (@Fin.val i.n i.source) →
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
                        DecrAlmostLinearSSSP.Decremental.ScaleParameters.ordinary s cost t)
                      (And
                        (@LE.le.{0} Nat instLENat cost
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (DecrAlmostLinearSSSP.Decremental.dispatchCharge
                                      DecrAlmostLinearSSSP.Decremental.ScaledCeiling.ceilingProgram.code)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))
                                      (DecrAlmostLinearSSSP.Decremental.utilityDepth i.size))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))))
                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
                            (@OfNat.ofNat.{0} Nat (nat_lit 65) (instOfNatNat (nat_lit 65)))))
                        (And
                          (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 154) (instOfNatNat (nat_lit 154))))
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (DecrAlmostLinearSSSP.Decremental.bankFactor
                                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 110) (instOfNatNat (nat_lit 110)))))
                              i.n))
                          (And
                            (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 156) (instOfNatNat (nat_lit 156))))
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (DecrAlmostLinearSSSP.Decremental.bankFactor
                                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 110) (instOfNatNat (nat_lit 110)))))
                                i.k))
                            (And
                              (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 158) (instOfNatNat (nat_lit 158))))
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
                                      (@Eq.{1} Nat (t.natMem address) (s.natMem address)))))))))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  And
    (@Eq.{1} Real
      ((DecrAlmostLinearSSSP.Decremental.ScaleParameters.highData s).realReg
        (@OfNat.ofNat.{0} Nat (nat_lit 202) (instOfNatNat (nat_lit 202))))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real (nat_lit 512)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 512) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 511) (instOfNatNat (nat_lit 511)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 510) (instOfNatNat (nat_lit 510)))))))
          (@Nat.cast.{0} Real Real.instNatCast
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 66) (instOfNatNat (nat_lit 66))))))
        (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64))))))
    (And (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.ScaleParameters.highData s).natReg s.natReg)
      (And (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.ScaleParameters.highData s).realMem s.realMem)
        (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.ScaleParameters.highData s).natMem s.natMem)))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    @LT.lt.{0} Real Real.instLT
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@Nat.cast.{0} Real Real.instNatCast i.size))
        i.accuracy →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 66) (instOfNatNat (nat_lit 66)))) i.n →
        @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64)))) i.accuracy →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
            @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
              ∃ cost t,
                And
                  (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                    DecrAlmostLinearSSSP.Decremental.ScaleParameters.high s cost t)
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
                              (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))
                              (DecrAlmostLinearSSSP.Decremental.utilityDepth i.size))
                            (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                    (And
                      (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 152) (instOfNatNat (nat_lit 152))))
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))))
                          (DecrAlmostLinearSSSP.Decremental.barrierHigh i)))
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
                            (@Eq.{1} Nat (t.natMem address) (s.natMem address)))))))) ∧ (((∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 204) (instOfNatNat (nat_lit 204))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 154) (instOfNatNat (nat_lit 154))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 156) (instOfNatNat (nat_lit 156))) →
              @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 158) (instOfNatNat (nat_lit 158))) →
                @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 160) (instOfNatNat (nat_lit 160))) →
                  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
                    DecrAlmostLinearSSSP.Decremental.ScaleParameters.ordinary k) ∧ (∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 200) (instOfNatNat (nat_lit 200))) →
          DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
            DecrAlmostLinearSSSP.Decremental.ScaleParameters.ordinary k)) ∧ ((∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 152) (instOfNatNat (nat_lit 152))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.ScaleParameters.high k) ∧ ((∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 202) (instOfNatNat (nat_lit 202))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 204) (instOfNatNat (nat_lit 204))) →
            DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.ScaleParameters.high
              k) ∧ (∀ (k : Nat),
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
                      DecrAlmostLinearSSSP.Decremental.ScaleParameters.prepare k))))) ∧ ((((∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 200) (instOfNatNat (nat_lit 200))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 202) (instOfNatNat (nat_lit 202))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 204) (instOfNatNat (nat_lit 204))) →
              DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
                DecrAlmostLinearSSSP.Decremental.ScaleParameters.prepare k) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (i : DecrAlmostLinearSSSP.Decremental.Input),
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
                                            (@Eq.{1} Nat (t.natMem address) (s.natMem address))))))))))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.ScaleParameters.writeFields s
    (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
    (DecrAlmostLinearSSSP.Decremental.ScaleParameters.fieldData s)) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
      And
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.ScaleParameters.fieldData s).natMem
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50)))))
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 154) (instOfNatNat (nat_lit 154)))))
        (And
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.ScaleParameters.fieldData s).natMem
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 156) (instOfNatNat (nat_lit 156)))))
          (And
            (@Eq.{1} Nat
              ((DecrAlmostLinearSSSP.Decremental.ScaleParameters.fieldData s).natMem
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 158) (instOfNatNat (nat_lit 158)))))
            (And
              (@Eq.{1} Nat
                ((DecrAlmostLinearSSSP.Decremental.ScaleParameters.fieldData s).natMem
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 152) (instOfNatNat (nat_lit 152)))))
              (And
                (@Eq.{1} Nat
                  ((DecrAlmostLinearSSSP.Decremental.ScaleParameters.fieldData s).natMem
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 160) (instOfNatNat (nat_lit 160)))))
                (@Eq.{1} Real
                  ((DecrAlmostLinearSSSP.Decremental.ScaleParameters.fieldData s).realMem
                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50)))))
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64))))
                    (@OfNat.ofNat.{0} Real (nat_lit 16)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))))))))))))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
      ∀ (address : Nat),
        @Ne.{1} Nat address (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50)))) →
          @Ne.{1} Nat address
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
            @Ne.{1} Nat address
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) →
              @Ne.{1} Nat address
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))) →
                @Ne.{1} Nat address
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) →
                  And
                    (@Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.ScaleParameters.fieldData s).natMem address)
                      (s.natMem address))
                    (@Eq.{1} Real ((DecrAlmostLinearSSSP.Decremental.ScaleParameters.fieldData s).realMem address)
                      (s.realMem address)))))) ∧ (((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 208) (instOfNatNat (nat_lit 208))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.ScaleParameters.writeFields k) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 206) (instOfNatNat (nat_lit 206))) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.ScaleParameters.writeFields k)) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.ScaleParameters.fieldData s).realMem
    (@Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realMem
      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64))))
        (@OfNat.ofNat.{0} Real (nat_lit 16)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))))))))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (i : DecrAlmostLinearSSSP.Decremental.Input)
  (p : DecrAlmostLinearSSSP.Decremental.Program) (scaleIndex F N : Nat),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 154) (instOfNatNat (nat_lit 154))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F i.n) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 156) (instOfNatNat (nat_lit 156))))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F i.k) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 158) (instOfNatNat (nat_lit 158))))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64))) i.size)) →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 152) (instOfNatNat (nat_lit 152))))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
                  (DecrAlmostLinearSSSP.Decremental.barrierHigh i)) →
              @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 160) (instOfNatNat (nat_lit 160))))
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F (@Fin.val i.n i.source)) →
                @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64)))) i.accuracy →
                  (∀ (j : Nat),
                      @LT.lt.{0} Nat instLTNat j N →
                        @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) j →
                          @Eq.{1} Nat
                            (s.natMem
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
                    (∀ (j : Nat),
                        @LT.lt.{0} Nat instLTNat j N →
                          @Eq.{1} Real
                            (s.realMem
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
                            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) →
                      And
                        (∀ (j : Nat),
                          @LT.lt.{0} Nat instLTNat j N →
                            @Eq.{1} Nat
                              ((DecrAlmostLinearSSSP.Decremental.ScaleParameters.fieldData s).natMem
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
                                ((DecrAlmostLinearSSSP.Decremental.initialMachine p
                                      (DecrAlmostLinearSSSP.Decremental.barrierInput i scaleIndex)).natReg
                                  j)))
                        (∀ (j : Nat),
                          @LT.lt.{0} Nat instLTNat j N →
                            @Eq.{1} Real
                              ((DecrAlmostLinearSSSP.Decremental.ScaleParameters.fieldData s).realMem
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
                              ((DecrAlmostLinearSSSP.Decremental.initialMachine p
                                    (DecrAlmostLinearSSSP.Decremental.barrierInput i scaleIndex)).realReg
                                j))) ∧ (∀ (N : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (p : DecrAlmostLinearSSSP.Decremental.Program)
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
                                                    (@Eq.{1} Real (t.realMem address) (s.realMem address)))))))))))))) ∧ (((((∀ (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
    (DecrAlmostLinearSSSP.Decremental.registerBound code)) ∧ (∀ (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
  @Membership.mem.{0, 0} DecrAlmostLinearSSSP.Decremental.Instruction
      (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
      (@List.instMembership.{0} DecrAlmostLinearSSSP.Decremental.Instruction) code ins →
    ∀ (j : Nat),
      @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat)
          (DecrAlmostLinearSSSP.Decremental.instructionRegisters ins) j →
        @LT.lt.{0} Nat instLTNat j (DecrAlmostLinearSSSP.Decremental.registerBound code))) ∧ ((∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction) (j : Nat),
  DecrAlmostLinearSSSP.Decremental.writesNat ins j →
    @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat)
      (DecrAlmostLinearSSSP.Decremental.instructionRegisters ins) j) ∧ (∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction) (j : Nat),
  DecrAlmostLinearSSSP.Decremental.writesReal ins j →
    @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat)
      (DecrAlmostLinearSSSP.Decremental.instructionRegisters ins) j))) ∧ (((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (t j : Nat),
  @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.registerBound p.code) j →
    @Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.execute p c t).natReg j) (c.natReg j)) ∧ (∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (t j : Nat),
  @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.registerBound p.code) j →
    @Eq.{1} Real ((DecrAlmostLinearSSSP.Decremental.execute p c t).realReg j) (c.realReg j))) ∧ ((∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {c : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail (DecrAlmostLinearSSSP.Decremental.registerBound p.code) c →
    ∀ (t : Nat),
      DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail (DecrAlmostLinearSSSP.Decremental.registerBound p.code)
        (DecrAlmostLinearSSSP.Decremental.execute p c t)) ∧ ((∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {c d : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail (DecrAlmostLinearSSSP.Decremental.registerBound p.code) c →
    DecrAlmostLinearSSSP.Decremental.Ends p c d →
      DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail (DecrAlmostLinearSSSP.Decremental.registerBound p.code) d) ∧ (∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (i : DecrAlmostLinearSSSP.Decremental.Input),
  DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail (DecrAlmostLinearSSSP.Decremental.registerBound p.code)
    (DecrAlmostLinearSSSP.Decremental.initialMachine p i)))))) ∧ ((((∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {c : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail (DecrAlmostLinearSSSP.Decremental.registerBound p.code) c →
    ∀ (e : Nat),
      DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail (DecrAlmostLinearSSSP.Decremental.registerBound p.code)
        (DecrAlmostLinearSSSP.Decremental.deletionMachine p c e)) ∧ (∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {i : DecrAlmostLinearSSSP.Decremental.Input} {ds : List.{0} (Fin i.k)}
  {cs : List.{0} DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.OnlineRun p i ds cs →
    ∀ (c : DecrAlmostLinearSSSP.Decremental.Machine),
      @Membership.mem.{0, 0} DecrAlmostLinearSSSP.Decremental.Machine
          (List.{0} DecrAlmostLinearSSSP.Decremental.Machine)
          (@List.instMembership.{0} DecrAlmostLinearSSSP.Decremental.Machine) cs c →
        DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail (DecrAlmostLinearSSSP.Decremental.registerBound p.code) c)) ∧ ((∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction) (j : Nat),
  Not (DecrAlmostLinearSSSP.Decremental.writesNat ins j) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.shadowAction ins)
      (DecrAlmostLinearSSSP.Decremental.shadowReg j)) ∧ ((∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction) (j : Nat),
  Not (DecrAlmostLinearSSSP.Decremental.writesReal ins j) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.shadowAction ins)
      (DecrAlmostLinearSSSP.Decremental.shadowReg j)) ∧ (∀ (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (pc j : Nat),
  (∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
      @Membership.mem.{0, 0} DecrAlmostLinearSSSP.Decremental.Instruction
          (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (@List.instMembership.{0} DecrAlmostLinearSSSP.Decremental.Instruction) code ins →
        Not (DecrAlmostLinearSSSP.Decremental.writesNat ins j)) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.dispatchAux pc code)
      (DecrAlmostLinearSSSP.Decremental.shadowReg j))))) ∧ (((∀ (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (pc j : Nat),
  (∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
      @Membership.mem.{0, 0} DecrAlmostLinearSSSP.Decremental.Instruction
          (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (@List.instMembership.{0} DecrAlmostLinearSSSP.Decremental.Instruction) code ins →
        Not (DecrAlmostLinearSSSP.Decremental.writesReal ins j)) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.dispatchAux pc code)
      (DecrAlmostLinearSSSP.Decremental.shadowReg j)) ∧ (∀ (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (bound : Nat),
  Iff (@Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.registersBelow code bound) Bool.true)
    (∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
      @Membership.mem.{0, 0} DecrAlmostLinearSSSP.Decremental.Instruction
          (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (@List.instMembership.{0} DecrAlmostLinearSSSP.Decremental.Instruction) code ins →
        ∀ (j : Nat),
          @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat)
              (DecrAlmostLinearSSSP.Decremental.instructionRegisters ins) j →
            @LT.lt.{0} Nat instLTNat j bound))) ∧ ((∀ (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction),
  @Eq.{1} Bool
    (DecrAlmostLinearSSSP.Decremental.registersBelow code (DecrAlmostLinearSSSP.Decremental.registerBound code))
    Bool.true) ∧ ((∀ (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (bound j : Nat),
  @Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.registersBelow code bound) Bool.true →
    @LE.le.{0} Nat instLENat bound j →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.shadowInterpreter code)
        (DecrAlmostLinearSSSP.Decremental.shadowReg j)) ∧ (∀ (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (bound j : Nat),
  @Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.registersBelow code bound) Bool.true →
    @LE.le.{0} Nat instLENat bound j →
      DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.shadowInterpreter code)
        (DecrAlmostLinearSSSP.Decremental.shadowReg j))))))))) := by
  exact ⟨⟨⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.ScaledCeiling.count_nat_frame,DecrAlmostLinearSSSP.Decremental.ScaledCeiling.count_real_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.ScaledCeiling.area_nat_frame,DecrAlmostLinearSSSP.Decremental.ScaledCeiling.area_real_frame⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Layout.nat_small_frame,DecrAlmostLinearSSSP.Decremental.Layout.real_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.barrier_high_positive,⟨DecrAlmostLinearSSSP.Decremental.barrier_weight_bounds,DecrAlmostLinearSSSP.Decremental.barrier_valid⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.barrier_polynomial_domain,DecrAlmostLinearSSSP.Decremental.ceiling_cost_bounds⟩,⟨DecrAlmostLinearSSSP.Decremental.barrier_low_cost,DecrAlmostLinearSSSP.Decremental.barrier_high_cost⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.utilityDepth_power,DecrAlmostLinearSSSP.Decremental.utilityDepth_bound⟩,⟨DecrAlmostLinearSSSP.Decremental.normal_barrier_argument_bound,⟨DecrAlmostLinearSSSP.Decremental.Prepass.nat_frame,DecrAlmostLinearSSSP.Decremental.Prepass.real_frame⟩⟩⟩⟩⟩,⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.Prepass.size_ceiling_bound,DecrAlmostLinearSSSP.Decremental.Prepass.eval_code⟩,⟨DecrAlmostLinearSSSP.Decremental.Fill.body_eval,DecrAlmostLinearSSSP.Decremental.Fill.eval_code⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.Fill.nat_frame,DecrAlmostLinearSSSP.Decremental.Fill.real_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.SnapshotFill.setup_fields,⟨DecrAlmostLinearSSSP.Decremental.SnapshotFill.eval_code,DecrAlmostLinearSSSP.Decremental.SnapshotFill.nat_frame⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.SnapshotFill.real_frame,DecrAlmostLinearSSSP.Decremental.ScaledCeiling.productReal_eval⟩,⟨DecrAlmostLinearSSSP.Decremental.ScaledCeiling.productReal_nat_frame,⟨DecrAlmostLinearSSSP.Decremental.ScaledCeiling.productReal_real_frame,DecrAlmostLinearSSSP.Decremental.ScaledCeiling.productNat_eval⟩⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.ScaledCeiling.productNat_nat_frame,DecrAlmostLinearSSSP.Decremental.ScaledCeiling.productNat_real_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.ScaledCeiling.batch_nat_frame,⟨DecrAlmostLinearSSSP.Decremental.ScaledCeiling.batch_real_frame,DecrAlmostLinearSSSP.Decremental.ScaledCeiling.batch_eval⟩⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.ScaleParameters.ordinary_valid,DecrAlmostLinearSSSP.Decremental.ScaleParameters.ordinary_eval⟩,⟨DecrAlmostLinearSSSP.Decremental.ScaleParameters.high_fields,DecrAlmostLinearSSSP.Decremental.ScaleParameters.high_eval⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.ScaleParameters.ordinary_nat_frame,DecrAlmostLinearSSSP.Decremental.ScaleParameters.ordinary_real_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.ScaleParameters.high_nat_frame,⟨DecrAlmostLinearSSSP.Decremental.ScaleParameters.high_real_frame,DecrAlmostLinearSSSP.Decremental.ScaleParameters.prepare_nat_frame⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.ScaleParameters.prepare_real_frame,DecrAlmostLinearSSSP.Decremental.ScaleParameters.prepare_eval⟩,⟨DecrAlmostLinearSSSP.Decremental.ScaleParameters.fields_eval,⟨DecrAlmostLinearSSSP.Decremental.ScaleParameters.fields_values,DecrAlmostLinearSSSP.Decremental.ScaleParameters.fields_memory_frame⟩⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.ScaleParameters.fields_real_frame,DecrAlmostLinearSSSP.Decremental.ScaleParameters.fields_nat_frame⟩,⟨DecrAlmostLinearSSSP.Decremental.ScaleParameters.fields_real_memory,⟨DecrAlmostLinearSSSP.Decremental.ScaleParameters.initial_snapshot,DecrAlmostLinearSSSP.Decremental.ScaleParameters.initializeSnapshot_eval⟩⟩⟩⟩⟩,⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.registerBound_ge,DecrAlmostLinearSSSP.Decremental.register_operand_bound⟩,⟨DecrAlmostLinearSSSP.Decremental.writesNat_operand,DecrAlmostLinearSSSP.Decremental.writesReal_operand⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.execute_nat_tail,DecrAlmostLinearSSSP.Decremental.execute_real_tail⟩,⟨DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail.execute,⟨DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail.ends,DecrAlmostLinearSSSP.Decremental.initialMachine_zero_tail⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail.deletion,DecrAlmostLinearSSSP.Decremental.OnlineRun.zero_register_tail⟩,⟨DecrAlmostLinearSSSP.Decremental.shadowAction_nat_source_frame,⟨DecrAlmostLinearSSSP.Decremental.shadowAction_real_source_frame,DecrAlmostLinearSSSP.Decremental.dispatchAux_nat_source_frame⟩⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.dispatchAux_real_source_frame,DecrAlmostLinearSSSP.Decremental.registersBelow_spec⟩,⟨DecrAlmostLinearSSSP.Decremental.registerBound_below,⟨DecrAlmostLinearSSSP.Decremental.interpreter_nat_tail_frame,DecrAlmostLinearSSSP.Decremental.interpreter_real_tail_frame⟩⟩⟩⟩⟩⟩⟩
