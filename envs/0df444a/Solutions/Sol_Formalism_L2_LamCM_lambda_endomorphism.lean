-- Prove2me | solution 1 for Formalism.L2.LamCM.lambda_endomorphism
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:18:33.756461+00:00
-- url     : https://prove2.me/submissions/8946b656-7d40-40b6-a735-29f929729ba4

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CoeffMemOfLoc
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_OneLeAbsNormOfLeOne
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_AbsNormSpanGalois
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
private lemma absNorm_le_absNorm_of_le {K : Type} [Field K] [NumberField K] (I J : FractionalIdeal (𝓞 K)⁰ K)
    (hJ : J ≠ 0) (hJI : J ≤ I) : FractionalIdeal.absNorm I ≤ FractionalIdeal.absNorm J := by
  have hI : I ≠ 0 := by
    rintro rfl
    exact hJ (FractionalIdeal.le_zero_iff.mp hJI)
  have h1 : J * I⁻¹ ≤ 1 := by
    rw [← mul_inv_cancel₀ hI, FractionalIdeal.mul_le]
    intro x hx y hy
    exact FractionalIdeal.mul_mem_mul (hJI hx) hy
  obtain ⟨A, hA⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp h1
  have hJeq : J = (A : FractionalIdeal (𝓞 K)⁰ K) * I := by
    rw [hA, mul_assoc, inv_mul_cancel₀ hI, mul_one]
  have hA0 : A ≠ ⊥ := by
    rintro rfl
    apply hJ
    rw [hJeq, FractionalIdeal.coeIdeal_bot, zero_mul]
  have hAn : (1:ℚ) ≤ FractionalIdeal.absNorm (A : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [FractionalIdeal.coeIdeal_absNorm]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hA0)
  have hIn : (0:ℚ) ≤ FractionalIdeal.absNorm I := FractionalIdeal.absNorm_nonneg I
  rw [hJeq, map_mul]
  nlinarith
private lemma prod_norm_embedding_eq_abs_norm {K : Type} [Field K] [NumberField K] (x : K) :
    ∏ σ : K →+* ℂ, ‖σ x‖ = |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ x
  rw [← Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun σ => σ x) (fun τ => τ x) (fun σ => rfl)] at h
  rw [← norm_prod, ← h]
  simp
section cauchy
end cauchy
section loc
variable {K : Type} [Field K] [NumberField K] {p : HeightOneSpectrum (𝓞 K)}
end loc
section galois
variable {K : Type} [Field K] [NumberField K]
end galois
end Formalism.L2.LamCM
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
namespace Formalism.L2.LamCM
theorem _root_.solution : LamEnd := by
  unfold LamEnd
  intro K _ _ NN cf S B hG hcf hmem hS hB hlen
  have hI0 : NN.I ≠ 0 := hG.1
  have hJ0 : FractionalIdeal.spanSingleton (𝓞 K)⁰ cf ≠ 0 := FractionalIdeal.spanSingleton_eq_zero_iff.not.mpr hcf
  have hJI : FractionalIdeal.spanSingleton (𝓞 K)⁰ cf ≤ NN.I := FractionalIdeal.spanSingleton_le_iff_mem.mpr hmem
  have hle := absNorm_le_absNorm_of_le NN.I _ hJ0 hJI
  rw [FractionalIdeal.absNorm_span_singleton] at hle
  have hNpos : (0:ℝ) < ((FractionalIdeal.absNorm NN.I : ℚ) : ℝ) := by
    have h0 : (0:ℚ) < FractionalIdeal.absNorm NN.I :=
      lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg _) (Ne.symm ((map_ne_zero _).mpr hI0))
    exact_mod_cast h0
  have hle' : ((FractionalIdeal.absNorm NN.I : ℚ) : ℝ) ≤ ∏ σ : K →+* ℂ, ‖σ cf‖ := by
    rw [prod_norm_embedding_eq_abs_norm]
    exact_mod_cast hle
  have hσ : ∀ σ : K →+* ℂ, 0 < ‖σ cf‖ := fun σ => norm_pos_iff.mpr ((map_ne_zero σ).mpr hcf)
  have hlog1 : Real.log ((FractionalIdeal.absNorm NN.I : ℚ) : ℝ) ≤ ∑ σ : K →+* ℂ, Real.log ‖σ cf‖ := by
    rw [← Real.log_prod (fun σ _ => (hσ σ).ne')]
    exact Real.log_le_log hNpos hle'
  have hlog2 : ∀ σ : K →+* ℂ, Real.log ‖σ cf‖ + Real.log (NN.n σ) ≤ Real.log (S σ) + Real.log B := by
    intro σ
    rw [← Real.log_mul (hσ σ).ne' (hG.2 σ).ne', ← Real.log_mul (hS σ).ne' hB.ne']
    exact Real.log_le_log (mul_pos (hσ σ) (hG.2 σ)) (hlen σ)
  have hsum := Finset.sum_le_sum (fun σ (_ : σ ∈ Finset.univ) => hlog2 σ)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    NumberField.Embeddings.card K ℂ, nsmul_eq_mul] at hsum
  have e : NN.deg = - Real.log ((FractionalIdeal.absNorm NN.I : ℚ) : ℝ) - ∑ σ, Real.log (NN.n σ) := rfl
  rw [e]
  linarith
end Formalism.L2.LamCM
