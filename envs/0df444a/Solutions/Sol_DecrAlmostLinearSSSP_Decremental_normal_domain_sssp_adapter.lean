-- Prove2me | solution 1 for DecrAlmostLinearSSSP.Decremental.normal_domain_sssp_adapter
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T11:24:16.650006+00:00
-- url     : https://prove2.me/submissions/3c6fcd5f-4648-4192-9ea4-eccc0606d498

import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_normal_laws_10
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_normal_laws_13
set_option autoImplicit false
open scoped ENNReal NNReal
theorem DecrAlmostLinearSSSP.Decremental.Native.choose_reserve_coefficient : ∀ (C : Real),
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
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_13.2.2.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.Native.normalProgramConstant_positive : ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (coefficient : Nat) (C : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C →
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (DecrAlmostLinearSSSP.Decremental.Native.normalProgramConstant p coefficient C) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_13.2.2.2.1.2
theorem DecrAlmostLinearSSSP.Decremental.normalWrapperOverhead_subpolynomial : ∀ (a : Nat → Real),
  DecrAlmostLinearSSSP.Decremental.Subpolynomial a →
    DecrAlmostLinearSSSP.Decremental.Subpolynomial (DecrAlmostLinearSSSP.Decremental.normalWrapperOverhead a) := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_10.1.2.1.1.1.1
theorem DecrAlmostLinearSSSP.Decremental.Native.normalProgram_maintains : ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (C : Real),
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
                        (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) Bool.true i := DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_13.2.2.2.2.2.2
open DecrAlmostLinearSSSP.Decremental

theorem solution (p : Program) (C : ℝ) (a : ℕ → ℝ) (queryBound : ℕ)
    (hC : 0 < C) (ha : Subpolynomial a)
    (hpoly : ∀ x : Input, x.Valid → 2 ≤ x.n → x.W ≤ x.size^2 →
      1/(x.size : ℝ) < x.accuracy → x.accuracy < 1 → Maintains p C a queryBound false x) :
    ∃ (host : Program) (D : ℝ) (b : ℕ → ℝ), 0 < D ∧ Subpolynomial b ∧
      ∀ i : Input, i.Valid → 2 ≤ i.n → 1/(i.size : ℝ) < i.accuracy → Maintains host D b 9 true i := by
  obtain ⟨coefficient,_,henvelope⟩ := Native.choose_reserve_coefficient C hC a ha
  exact ⟨Native.normalProgram coefficient p,Native.normalProgramConstant p coefficient C,normalWrapperOverhead a,
    Native.normalProgramConstant_positive p coefficient C hC,normalWrapperOverhead_subpolynomial a ha,
    Native.normalProgram_maintains p C hC a ha queryBound coefficient hpoly henvelope⟩
