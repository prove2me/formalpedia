-- Prove2me | solution 1 for Formalism.L2.LamCM.exists_split_of_isLocGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:38:59.180065+00:00
-- url     : https://prove2.me/submissions/1bac2ecf-7343-4f99-8b36-e1b55e94e0dd

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementP
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CmNumbersLink
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_CountSpanSingletonAlgebraMapEqZero
import Theorems.Thm_Formalism_L2_LamCM_not_le_of_count_eq_zero
import Theorems.Thm_Formalism_L2_LamCM_le_one_of_count_nonneg
import Theorems.Thm_P2M_Formalism_L2_LamCM_spanSingleton_ne_zero__ef0616425764


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
variable {F : Type} [Field F] [NumberField F]
namespace Formalism.L2.LamCM
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) {c : F} {I : FractionalIdeal (𝓞 F)⁰ F} (hI : I ≠ 0)
    (hc : IsLocGen v c I) :
    ∃ A B : Ideal (𝓞 F), ¬ A ≤ v.asIdeal ∧ ¬ B ≤ v.asIdeal ∧
      I * (B : FractionalIdeal (𝓞 F)⁰ F) = FractionalIdeal.spanSingleton (𝓞 F)⁰ c * (A : FractionalIdeal (𝓞 F)⁰ F) := by
  set C := FractionalIdeal.spanSingleton (𝓞 F)⁰ c with hCdef
  have hC : C ≠ 0 := spanSingleton_ne_zero' hc.1
  set D := C⁻¹ * I with hD
  have hD0 : D ≠ 0 := mul_ne_zero (inv_ne_zero hC) hI
  have hDc : FractionalIdeal.count F v D = 0 := by
    rw [hD, FractionalIdeal.count_mul F v (inv_ne_zero hC) hI, FractionalIdeal.count_inv, hc.2]; ring
  obtain ⟨b, J, hb, hDJ⟩ := FractionalIdeal.exists_eq_spanSingleton_mul D
  have hbK : algebraMap (𝓞 F) F b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hb
  set S := FractionalIdeal.spanSingleton (𝓞 F)⁰ (algebraMap (𝓞 F) F b) with hS
  have hS0 : S ≠ 0 := spanSingleton_ne_zero' hbK
  have hJ0 : (J : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hDJ; exact hD0 hDJ
  rw [← FractionalIdeal.spanSingleton_inv] at hDJ
  set P : FractionalIdeal (𝓞 F)⁰ F := (v.asIdeal : FractionalIdeal (𝓞 F)⁰ F) with hP
  have hP0 : P ≠ 0 := by rw [hP, Ne, FractionalIdeal.coeIdeal_eq_zero]; exact v.ne_bot
  set k := FractionalIdeal.count F v (J : FractionalIdeal (𝓞 F)⁰ F) with hk
  have hSk : FractionalIdeal.count F v S = k := by
    have := hDc
    rw [hDJ, FractionalIdeal.count_mul F v (inv_ne_zero hS0) hJ0, FractionalIdeal.count_inv] at this
    omega
  have hSnn : ∀ w : HeightOneSpectrum (𝓞 F), 0 ≤ FractionalIdeal.count F w S := by
    intro w; rw [hS, ← FractionalIdeal.coeIdeal_span_singleton]; exact FractionalIdeal.count_coe_nonneg F w _
  have hPw : ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → FractionalIdeal.count F w P = 0 := fun w hw =>
    FractionalIdeal.count_maximal_coprime F w (Ne.symm hw)
  have hPk0 : P ^ (-k) ≠ 0 := zpow_ne_zero _ hP0
  have cnt : ∀ (X : FractionalIdeal (𝓞 F)⁰ F), X ≠ 0 → (∀ w, 0 ≤ FractionalIdeal.count F w X) →
      FractionalIdeal.count F v X = k →
      ∃ Y : Ideal (𝓞 F), (Y : FractionalIdeal (𝓞 F)⁰ F) = P ^ (-k) * X ∧ ¬ Y ≤ v.asIdeal := by
    intro X hX hXnn hXk
    have hY0 : P ^ (-k) * X ≠ 0 := mul_ne_zero hPk0 hX
    have hcnt : ∀ w, FractionalIdeal.count F w (P ^ (-k) * X) =
        -k * FractionalIdeal.count F w P + FractionalIdeal.count F w X := by
      intro w; rw [FractionalIdeal.count_mul F w hPk0 hX, FractionalIdeal.count_zpow]
    have hle : P ^ (-k) * X ≤ 1 := by
      refine le_one_of_count_nonneg hY0 (fun w => ?_)
      rw [hcnt w]
      by_cases hw : w = v
      · subst hw; rw [hP, FractionalIdeal.count_self, hXk]; ring_nf; exact le_refl _
      · rw [hPw w hw]; simpa using hXnn w
    obtain ⟨Y, hY⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hle
    refine ⟨Y, hY, not_le_of_count_eq_zero v ?_ ?_⟩
    · intro hbot; rw [hbot, FractionalIdeal.coeIdeal_bot] at hY; exact hY0 hY.symm
    · rw [hY, hcnt v, hP, FractionalIdeal.count_self, hXk]; ring
  obtain ⟨A, hA, hAv⟩ := cnt _ hJ0 (fun w => FractionalIdeal.count_coe_nonneg F w J) rfl
  obtain ⟨B, hB, hBv⟩ := cnt _ hS0 hSnn hSk
  refine ⟨A, B, hAv, hBv, ?_⟩
  have hI : I = C * D := by rw [hD, ← mul_assoc, mul_inv_cancel₀ hC, one_mul]
  rw [hA, hB, hI, hDJ]
  have h1 : S⁻¹ * S = 1 := inv_mul_cancel₀ hS0
  calc C * (S⁻¹ * ↑J) * (P ^ (-k) * S) = C * (P ^ (-k) * ↑J) * (S⁻¹ * S) := by ring
    _ = C * (P ^ (-k) * ↑J) := by rw [h1, mul_one]
end Formalism.L2.LamCM
