-- Prove2me | solution 1 for DedekindZeta.completedDedekindZeta_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:59:31.17421+00:00
-- url     : https://prove2.me/submissions/36c79965-fa6e-4de4-ab2e-bb511a0c14ad

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_GammaIntegral
import Definitions.Def_DedekindZeta_PerClass
import Theorems.Thm_DedekindZeta_completedPartialZeta_idealClassRep_eq
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
import Theorems.Thm_DedekindZeta_dedekindZeta_eq_tsum_absNorm
import Theorems.Thm_DedekindZeta_sum_class_tsum_absNorm
attribute [local simp] DedekindZeta.Theta.gaussVSchwartz_apply
attribute [local simp] DedekindZeta.Theta.mixedGaussianSchwartz_apply



set_option autoImplicit true
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
open DedekindZeta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
namespace DedekindZeta
theorem _root_.solution {s : ℂ} (hs : 1 < s.re) :
    completedDedekindZeta K s = ZInfty K s * NumberField.dedekindZeta K s := by
  simp only [completedDedekindZeta]
  simp_rw [completedPartialZeta_idealClassRep_eq K hs]
  rw [← Finset.mul_sum]
  -- Reindex the class sum `c ↦ c⁻¹` (an involution of the finite class group) so
  -- the inverse-class fibres become the direct-class fibres.
  rw [show (∑ c : ClassGroup (𝓞 K),
        ∑' 𝔟 : {𝔟 : NonzeroIdeal K // idealClass K 𝔟 = c⁻¹},
          (Ideal.absNorm ((𝔟 : NonzeroIdeal K) : Ideal (𝓞 K)) : ℂ) ^ (-s))
        = ∑ c : ClassGroup (𝓞 K),
            ∑' 𝔟 : {𝔟 : NonzeroIdeal K // idealClass K 𝔟 = c},
              (Ideal.absNorm ((𝔟 : NonzeroIdeal K) : Ideal (𝓞 K)) : ℂ) ^ (-s) from
      Equiv.sum_comp (Equiv.inv (ClassGroup (𝓞 K)))
        (fun c => ∑' 𝔟 : {𝔟 : NonzeroIdeal K // idealClass K 𝔟 = c},
          (Ideal.absNorm ((𝔟 : NonzeroIdeal K) : Ideal (𝓞 K)) : ℂ) ^ (-s))]
  rw [sum_class_tsum_absNorm K hs, ← dedekindZeta_eq_tsum_absNorm K hs]
end DedekindZeta
