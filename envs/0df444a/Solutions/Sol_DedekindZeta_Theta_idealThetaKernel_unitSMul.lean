-- Prove2me | solution 1 for DedekindZeta.Theta.idealThetaKernel_unitSMul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:14:07.139945+00:00
-- url     : https://prove2.me/submissions/6ac69f68-9d14-4e1a-ad57-63e6d0aba61d

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta

set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
namespace DedekindZeta.Theta
theorem _root_.solution (𝔞 : Ideal (𝓞 K)) (u : (𝓞 K)ˣ)
    (x : mixedEmbedding.mixedSpace K) :
    idealThetaKernel K 𝔞 (u • x) = idealThetaKernel K 𝔞 x := by
  -- Bijection `a ↦ u·a` of the nonzero elements of `𝔞` (`u` is a unit).
  let e : {a : 𝓞 K // a ∈ 𝔞 ∧ a ≠ 0} ≃ {a : 𝓞 K // a ∈ 𝔞 ∧ a ≠ 0} :=
  { toFun := fun a => ⟨(u : 𝓞 K) * a, Ideal.mul_mem_left _ _ a.2.1,
      mul_ne_zero (Units.ne_zero u) a.2.2⟩
    invFun := fun a => ⟨((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * a, Ideal.mul_mem_left _ _ a.2.1,
      mul_ne_zero (Units.ne_zero u⁻¹) a.2.2⟩
    left_inv := fun a => by
      apply Subtype.ext; simp [← mul_assoc]
    right_inv := fun a => by
      apply Subtype.ext; simp [← mul_assoc] }
  rw [idealThetaKernel, idealThetaKernel]
  conv_rhs => rw [← Equiv.tsum_eq e]
  refine tsum_congr (fun a => ?_)
  -- `(u • x) * emb(a) = x * emb(u·a) = x * emb((e a))`
  have hcoe : (((e a : 𝓞 K)) : K) = ((u : 𝓞 K) : K) * ((a : 𝓞 K) : K) := by
    change (((u : 𝓞 K) * a : 𝓞 K) : K) = _
    rw [RingOfIntegers.coe_eq_algebraMap, map_mul,
      ← RingOfIntegers.coe_eq_algebraMap, ← RingOfIntegers.coe_eq_algebraMap]
  congr 1
  congr 1
  rw [unitSMul_smul]
  simp only [← RingOfIntegers.coe_eq_algebraMap]
  rw [hcoe, map_mul]; ring
end DedekindZeta.Theta
