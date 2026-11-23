-- Prove2me | solution 1 for DedekindZeta.completedPartialZeta_idealClassRep_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:56:46.009002+00:00
-- url     : https://prove2.me/submissions/8deb9137-2cb3-4af2-adb7-af4e2500b0d1

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_GammaIntegral
import Definitions.Def_DedekindZeta_PerClass
import Theorems.Thm_DedekindZeta_GammaIntegral_completedPartialZeta_eq_normPow_mul_ZInfty_mul_tsum
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
attribute [local simp] DedekindZeta.Theta.gaussVSchwartz_apply
attribute [local simp] DedekindZeta.Theta.mixedGaussianSchwartz_apply



set_option autoImplicit true
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
open DedekindZeta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
namespace DedekindZeta
theorem _root_.solution {s : ℂ} (hs : 1 < s.re)
    (c : ClassGroup (𝓞 K)) :
    completedPartialZeta K (idealClassRep K c) s
      = ZInfty K s * ∑' 𝔟 : {𝔟 : NonzeroIdeal K // idealClass K 𝔟 = c⁻¹},
          (Ideal.absNorm ((𝔟 : NonzeroIdeal K) : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
  classical
  -- The chosen representative `𝔞 = idealClassRep K c`, with `[𝔞] = c` and `𝔞 ≠ 0`.
  set J𝔞 : (Ideal (𝓞 K))⁰ := Function.surjInv ClassGroup.mk0_surjective c with hJ
  have hmkJ : ClassGroup.mk0 J𝔞 = c := Function.surjInv_eq _ _
  rw [show idealClassRep K c = (J𝔞 : Ideal (𝓞 K)) from rfl]
  set 𝔞 : Ideal (𝓞 K) := (J𝔞 : Ideal (𝓞 K)) with h𝔞def
  have h𝔞ne : 𝔞 ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp J𝔞.2
  -- Step 3 intermediate identity (analytic core).
  rw [GammaIntegral.completedPartialZeta_eq_normPow_mul_ZInfty_mul_tsum s hs h𝔞ne]
  -- Splitting `𝔑(m·n)^{-s} = 𝔑(m)^{-s}·𝔑(n)^{-s}` over the casts.
  have hsplit_term : ∀ (m n : ℕ),
      ((m * n : ℕ) : ℂ) ^ (-s) = (m : ℂ) ^ (-s) * (n : ℂ) ^ (-s) := by
    intro m n
    have h := Complex.mul_cpow_ofReal_nonneg (a := (m : ℝ)) (b := (n : ℝ))
      (Nat.cast_nonneg m) (Nat.cast_nonneg n) (-s)
    simpa [Complex.ofReal_natCast, Nat.cast_mul] using h
  -- The reindexing bijection `{𝔟 : [𝔟] = c⁻¹} ≃ {(a) principal : 𝔞 ∣ (a)}`,
  -- realised by `𝔟 ↦ 𝔞 · 𝔟`.
  set f : {𝔟 : NonzeroIdeal K // idealClass K 𝔟 = c⁻¹} →
      {I : (Ideal (𝓞 K))⁰ //
        (𝔞 ∣ (I : Ideal (𝓞 K))) ∧ Submodule.IsPrincipal (I : Ideal (𝓞 K))} :=
    fun 𝔟 =>
      ⟨⟨𝔞 * ((𝔟 : NonzeroIdeal K) : Ideal (𝓞 K)),
          mem_nonZeroDivisors_iff_ne_zero.mpr
            (mul_ne_zero h𝔞ne (𝔟 : NonzeroIdeal K).2)⟩,
        dvd_mul_right _ _,
        (ClassGroup.mk0_eq_one_iff
          (mem_nonZeroDivisors_iff_ne_zero.mpr
            (mul_ne_zero h𝔞ne (𝔟 : NonzeroIdeal K).2))).mp (by
            have hs2 : (⟨𝔞 * ((𝔟 : NonzeroIdeal K) : Ideal (𝓞 K)),
                  mem_nonZeroDivisors_iff_ne_zero.mpr
                    (mul_ne_zero h𝔞ne (𝔟 : NonzeroIdeal K).2)⟩ : (Ideal (𝓞 K))⁰)
                = J𝔞 * ⟨((𝔟 : NonzeroIdeal K) : Ideal (𝓞 K)),
                    mem_nonZeroDivisors_iff_ne_zero.mpr (𝔟 : NonzeroIdeal K).2⟩ := by
              apply Subtype.ext
              simp [Submonoid.coe_mul, h𝔞def]
            rw [hs2, map_mul, hmkJ]
            have hic : ClassGroup.mk0 ⟨((𝔟 : NonzeroIdeal K) : Ideal (𝓞 K)),
                mem_nonZeroDivisors_iff_ne_zero.mpr (𝔟 : NonzeroIdeal K).2⟩
                = idealClass K (𝔟 : NonzeroIdeal K) := rfl
            rw [hic, 𝔟.2, mul_inv_cancel])⟩
    with hf
  have hinj : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    have hh : 𝔞 * ((x : NonzeroIdeal K) : Ideal (𝓞 K))
        = 𝔞 * ((y : NonzeroIdeal K) : Ideal (𝓞 K)) :=
      congrArg
        (fun d : {I : (Ideal (𝓞 K))⁰ //
            (𝔞 ∣ (I : Ideal (𝓞 K))) ∧ Submodule.IsPrincipal (I : Ideal (𝓞 K))} =>
          ((d.1 : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))) h
    exact mul_left_cancel₀ h𝔞ne hh
  have hsurj : Function.Surjective f := by
    rintro ⟨I, hdvd, hprin⟩
    obtain ⟨b, hb⟩ := hdvd
    have hbne : b ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hb
      exact (mem_nonZeroDivisors_iff_ne_zero.mp I.2) hb
    have hbmem : b ∈ (Ideal (𝓞 K))⁰ := mem_nonZeroDivisors_iff_ne_zero.mpr hbne
    have hIsplit : I = J𝔞 * ⟨b, hbmem⟩ := by
      apply Subtype.ext
      simp [Submonoid.coe_mul, h𝔞def, hb]
    have hmkI : ClassGroup.mk0 I = 1 := (ClassGroup.mk0_eq_one_iff I.2).mpr hprin
    rw [hIsplit, map_mul, hmkJ] at hmkI
    have hcl : idealClass K ⟨b, hbne⟩ = c⁻¹ := by
      rw [show idealClass K ⟨b, hbne⟩ = ClassGroup.mk0 ⟨b, hbmem⟩ from rfl,
        eq_inv_iff_mul_eq_one, mul_comm]
      exact hmkI
    refine ⟨⟨⟨b, hbne⟩, hcl⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change 𝔞 * b = (I : Ideal (𝓞 K))
    rw [hb]
  set e : {𝔟 : NonzeroIdeal K // idealClass K 𝔟 = c⁻¹} ≃
      {I : (Ideal (𝓞 K))⁰ //
        (𝔞 ∣ (I : Ideal (𝓞 K))) ∧ Submodule.IsPrincipal (I : Ideal (𝓞 K))} :=
    Equiv.ofBijective f ⟨hinj, hsurj⟩ with he
  -- Reindex the principal-ideal tsum onto the inverse class via `e`.
  have hreindex :
      (∑' I : {I : (Ideal (𝓞 K))⁰ //
            (𝔞 ∣ (I : Ideal (𝓞 K))) ∧ Submodule.IsPrincipal (I : Ideal (𝓞 K))},
          (Ideal.absNorm ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℂ) ^ (-s))
        = ∑' 𝔟 : {𝔟 : NonzeroIdeal K // idealClass K 𝔟 = c⁻¹},
            (Ideal.absNorm 𝔞 : ℂ) ^ (-s)
              * (Ideal.absNorm ((𝔟 : NonzeroIdeal K) : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
    rw [← Equiv.tsum_eq e (fun I => (Ideal.absNorm ((I : (Ideal (𝓞 K))⁰) :
        Ideal (𝓞 K)) : ℂ) ^ (-s))]
    apply tsum_congr
    intro 𝔟
    change (Ideal.absNorm (𝔞 * ((𝔟 : NonzeroIdeal K) : Ideal (𝓞 K))) : ℂ) ^ (-s) = _
    rw [map_mul Ideal.absNorm, hsplit_term]
  rw [hreindex, tsum_mul_left]
  -- Cancel the `𝔑(𝔞)^{±s}` prefactor.
  have hAnat : Ideal.absNorm 𝔞 ≠ 0 := fun h =>
    h𝔞ne (by rw [Ideal.zero_eq_bot]; exact Ideal.absNorm_eq_zero_iff.mp h)
  have hAne : (Ideal.absNorm 𝔞 : ℂ) ≠ 0 := by exact_mod_cast hAnat
  have hcancel : (Ideal.absNorm 𝔞 : ℂ) ^ s * (Ideal.absNorm 𝔞 : ℂ) ^ (-s) = 1 := by
    rw [← Complex.cpow_add _ _ hAne, add_neg_cancel, Complex.cpow_zero]
  calc (Ideal.absNorm 𝔞 : ℂ) ^ s * ZInfty K s
          * ((Ideal.absNorm 𝔞 : ℂ) ^ (-s)
            * ∑' 𝔟 : {𝔟 : NonzeroIdeal K // idealClass K 𝔟 = c⁻¹},
                (Ideal.absNorm ((𝔟 : NonzeroIdeal K) : Ideal (𝓞 K)) : ℂ) ^ (-s))
        = ((Ideal.absNorm 𝔞 : ℂ) ^ s * (Ideal.absNorm 𝔞 : ℂ) ^ (-s))
            * (ZInfty K s
              * ∑' 𝔟 : {𝔟 : NonzeroIdeal K // idealClass K 𝔟 = c⁻¹},
                  (Ideal.absNorm ((𝔟 : NonzeroIdeal K) : Ideal (𝓞 K)) : ℂ) ^ (-s)) := by
          ring
      _ = ZInfty K s
            * ∑' 𝔟 : {𝔟 : NonzeroIdeal K // idealClass K 𝔟 = c⁻¹},
                (Ideal.absNorm ((𝔟 : NonzeroIdeal K) : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
          rw [hcancel, one_mul]
end DedekindZeta
