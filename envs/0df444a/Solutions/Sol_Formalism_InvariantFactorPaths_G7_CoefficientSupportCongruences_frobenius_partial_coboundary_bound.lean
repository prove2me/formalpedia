-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.CoefficientSupportCongruences.frobenius_partial_coboundary_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:02:34.778797+00:00
-- url     : https://prove2.me/submissions/54b5ef8f-5582-45b5-a5b8-a2783f5154cb

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_ThmSUniform
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_FrobeniusPartialCoboundaryBound
import Theorems.Thm_Formalism_G_LogP_hX0
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoboundarySeries_subst_single_var
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_PhiH_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_C
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_add
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_neg
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_sub
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_frob_congr
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_int_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_int_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_map_inVar
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_map_lgF
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_subst_single_var
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FrobeniusSubstitution_constantCoeff_frobVar
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FrobeniusSubstitution_frobVar_X
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FrobeniusSubstitution_frobVar_add
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FrobeniusSubstitution_frobVar_pair
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FrobeniusSubstitution_frobVar_psubst
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FrobeniusSubstitution_frobVar_sub
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FrobeniusSubstitution_hasSubst_pair
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FrobeniusSubstitution_integral_X
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FrobeniusSubstitution_map_derivative
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FrobeniusSubstitution_map_g0F
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FrobeniusSubstitution_map_inVar
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FrobeniusSubstitution_map_lgF
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FrobeniusSubstitution_map_pair
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FrobeniusSubstitution_map_pderiv
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FrobeniusSubstitution_norm_sigma_le
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FrobeniusSubstitution_pair_frobVar
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FrobeniusSubstitution_partial_coboundary_linear
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FrobeniusSubstitution_pderiv_prod
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FrobeniusSubstitution_subst_g_zero_eq_log
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FrobeniusSubstitution_subst_pow_g_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FrobeniusSubstitution_subst_psubst
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FrobeniusSubstitution_subst_single_var
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_integral_X
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_subst_psubst
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_Top_deIntegral
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_Top_divDeriv
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_Top_lawSymm
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_X
import Theorems.Thm_Formalism_LT_InvIntP_key
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_integral_subst__564f1f6f92b9


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open DworkIntegrality (Bd bd_add bd_sub bd_neg bd_mul bd_C int_mul int_pow frob_congr PhiH PhiH_apply)
open Formalism.InvariantFactorPaths.G7.CoefficientSupportCongruences
open FrobeniusSubstitution
namespace Formalism.InvariantFactorPaths.G7.CoefficientSupportCongruences
theorem _root_.solution {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {p : ℕ}
    {σ : K →+* K} (hU : UnrOK K p σ) {F : MvPowerSeries (Fin 2) K} (hF : IsLawOfLog p F)
    {G : MvPowerSeries (Fin 2) K} {c : K} (hc : ‖c‖ ≤ 1) (hDer : DerivIs p G c)
    (hΔ : d1 F (DeS p σ G) =
      MvPowerSeries.C (σ c) * (in3 (cob F (g0F K p)) * at1 2 (lgF K p))) :
    Bd (p : ℝ)⁻¹ (frobVar p (MvPowerSeries.map σ (d1 F G)) -
      MvPowerSeries.C (p : K) * d1 F G) := by
  obtain ⟨hp, -, hnp, -, hσ⟩ := hU
  have hσF : MvPowerSeries.map σ F = F := (Top.lawSymm K p hp hnp F hF).1 σ
  have hδi : Integral (cob F (g0F K p)) := Top.deIntegral K p σ hp hnp hσ F hF
  obtain ⟨hF0, hFi, hFc⟩ := hF
  have hp0 : p ≠ 0 := hp.ne_zero
  have hp2 : 2 ≤ p := hp.two_le
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hpK : (p : K) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnp
    exact (inv_pos.mpr hppos).ne hnp
  have hinv : ‖((p : K)⁻¹)‖ = (p : ℝ) := by rw [norm_inv, hnp, inv_inv]
  have hscale : ∀ f : MvPowerSeries (Fin 3) K, Bd (p : ℝ)⁻¹ f →
      Integral (MvPowerSeries.C ((p : K)⁻¹) * f) := by
    intro f hf n
    rw [MvPowerSeries.coeff_C_mul, norm_mul, hinv]
    calc (p : ℝ) * ‖MvPowerSeries.coeff n f‖ ≤ (p : ℝ) * (p : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_left (hf n) hppos.le
      _ = 1 := mul_inv_cancel₀ hppos.ne'

  have hX0 : ∀ i : Fin 3, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 3) K) = 0 :=
    fun i => by simp
  have hXp0 : ∀ i : Fin 3,
      MvPowerSeries.constantCoeff ((MvPowerSeries.X i : MvPowerSeries (Fin 3) K) ^ p) = 0 :=
    fun i => by simp [hp0]
  have hsX : ∀ i : Fin 3, PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 3) K) :=
    fun i => PowerSeries.HasSubst.X i

  have hin3 : MvPowerSeries.HasSubst
      ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 1] :=
    hasSubst_pair (hX0 0) (hX0 1)
  have hin3c : ∀ i : Fin 2, MvPowerSeries.constantCoeff
      (![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 1] i) = 0 :=
    fun i => by fin_cases i <;> simp
  have hin3i : ∀ i : Fin 2, Integral
      (![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 1] i) := fun i => by
    fin_cases i
    · exact integral_X 0
    · exact integral_X 1
  have hA0 : MvPowerSeries.constantCoeff (in3 F) = 0 :=
    MvPowerSeries.constantCoeff_subst_eq_zero hin3 hin3c hF0
  have hAi : Integral (in3 F) := LogarithmEquivalence.integral_subst' hin3c hin3i hFi
  have hδ3i : Integral (in3 (cob F (g0F K p))) := LogarithmEquivalence.integral_subst' hin3c hin3i hδi
  have hσA : MvPowerSeries.map σ (in3 F) = in3 F := by
    unfold in3
    rw [map_pair σ hin3, hσF, MvPowerSeries.map_X, MvPowerSeries.map_X]
  have hsA : PowerSeries.HasSubst (in3 F) := PowerSeries.HasSubst.of_constantCoeff_zero hA0
  have hAp0 : MvPowerSeries.constantCoeff (in3 F ^ p) = 0 := by
    rw [map_pow, hA0, zero_pow hp0]
  have hfA0 : MvPowerSeries.constantCoeff (frobVar p (in3 F)) = 0 := by
    rw [constantCoeff_frobVar hp0, hA0]

  set r : MvPowerSeries (Fin 3) K :=
    MvPowerSeries.C ((p : K)⁻¹) * (frobVar p (in3 F) - in3 F ^ p) with hr
  have hCC : MvPowerSeries.C (p : K) * MvPowerSeries.C ((p : K)⁻¹) =
      (1 : MvPowerSeries (Fin 3) K) := by
    rw [← map_mul, mul_inv_cancel₀ hpK, map_one]
  have hFr : frobVar p (in3 F) = in3 F ^ p + MvPowerSeries.C (p : K) * r := by
    rw [hr, ← mul_assoc, hCC]
    ring
  have hri : Integral r := by
    refine hscale _ fun n => ?_
    have h := frob_congr (σ := σ) hp hnp hσ (f := in3 F) hAi n
    rw [PhiH_apply, hσA, map_sub, norm_sub_rev, ← map_sub] at h
    exact h
  have hr0 : MvPowerSeries.constantCoeff r = 0 := by
    rw [hr, map_mul, map_sub, hfA0, hAp0, sub_zero, mul_zero]

  have h1 : MvPowerSeries.HasSubst ![in3 F, (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K)] :=
    hasSubst_pair hA0 (hX0 2)
  have h2 : MvPowerSeries.HasSubst
      ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] :=
    hasSubst_pair (hX0 0) (hX0 2)
  have h3 : MvPowerSeries.HasSubst
      ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] :=
    hasSubst_pair (hX0 1) (hX0 2)
  set Gs : MvPowerSeries (Fin 2) K := MvPowerSeries.map σ G with hGs
  have hd1P : d1 F (frobVar p Gs) =
      MvPowerSeries.subst ![in3 F ^ p, (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) ^ p] Gs -
      MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K) ^ p,
        MvPowerSeries.X 2 ^ p] Gs -
      MvPowerSeries.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K) ^ p,
        MvPowerSeries.X 2 ^ p] Gs := by
    unfold d1
    rw [pair_frobVar hp0 h1, pair_frobVar hp0 h2, pair_frobVar hp0 h3]
  have hd1s : frobVar p (MvPowerSeries.map σ (d1 F G)) =
      MvPowerSeries.subst ![frobVar p (in3 F),
        (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) ^ p] Gs -
      MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K) ^ p,
        MvPowerSeries.X 2 ^ p] Gs -
      MvPowerSeries.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K) ^ p,
        MvPowerSeries.X 2 ^ p] Gs := by
    unfold d1
    rw [map_sub, map_sub, map_pair σ h1, map_pair σ h2, map_pair σ h3, hσA, MvPowerSeries.map_X,
      MvPowerSeries.map_X, MvPowerSeries.map_X, frobVar_sub hp0, frobVar_sub hp0,
      frobVar_pair hp0 h1, frobVar_pair hp0 h2, frobVar_pair hp0 h3, frobVar_X hp0, frobVar_X hp0,
      frobVar_X hp0]

  set Φ : MvPowerSeries (Fin 2) K :=
    Gs - MvPowerSeries.C (σ c) * (at1 0 (lgF K p) * at1 1 (g0F K p)) with hΦ
  have hΦi : Integral (MvPowerSeries.pderiv (R := K) 0 Φ) := by
    have e : MvPowerSeries.pderiv (R := K) 0 Φ = MvPowerSeries.map σ
        (MvPowerSeries.pderiv (R := K) 0 G -
          MvPowerSeries.C c * (at1 0 (PowerSeries.derivative K (lgF K p)) * at1 1 (g0F K p))) := by
      rw [hΦ, map_sub, pderiv_prod, map_sub, map_mul, map_mul, MvPowerSeries.map_C, map_inVar,
        map_inVar, map_derivative, map_lgF, map_g0F, map_pderiv]
    rw [e]
    intro n
    rw [MvPowerSeries.coeff_map]
    exact norm_sigma_le hσ hp.one_le (hDer n)
  have hE1 := Top.divDeriv K (Fin 2) (Fin 3) p hp hnp 0 Φ
    ![in3 F ^ p, (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) ^ p] r hΦi
    (fun i => by
      fin_cases i
      · exact hAp0
      · exact hXp0 2)
    (fun i => by
      fin_cases i
      · exact int_pow hAi p
      · exact int_pow (integral_X 2) p) hr0 hri
  have hupd : Function.update ![in3 F ^ p, (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) ^ p] 0
      (![in3 F ^ p, (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) ^ p] 0 +
        MvPowerSeries.C (p : K) * r) =
      ![frobVar p (in3 F), (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) ^ p] := by
    funext i
    fin_cases i
    · simp [hFr]
    · simp
  rw [hupd] at hE1
  have hSΦ : ∀ u v : MvPowerSeries (Fin 3) K, MvPowerSeries.HasSubst ![u, v] →
      MvPowerSeries.subst ![u, v] Φ = MvPowerSeries.subst ![u, v] Gs -
        MvPowerSeries.C (σ c) *
          (PowerSeries.subst u (lgF K p) * PowerSeries.subst v (g0F K p)) := by
    intro u v h
    rw [hΦ, MvPowerSeries.subst_sub h, MvPowerSeries.subst_mul h, MvPowerSeries.subst_mul h,
      MvPowerSeries.subst_C, subst_single_var h, subst_single_var h]
    rfl

  have hlog : PowerSeries.subst F (lgF K p) = at1 0 (lgF K p) + at1 1 (lgF K p) := by
    unfold cob at hFc
    linear_combination hFc
  have hsF : PowerSeries.HasSubst F := PowerSeries.HasSubst.of_constantCoeff_zero hF0
  have hlogA : PowerSeries.subst (in3 F) (lgF K p) =
      (at1 0 (lgF K p) + at1 1 (lgF K p) : MvPowerSeries (Fin 3) K) := by
    have h := congrArg in3 hlog
    unfold in3 at h ⊢
    rw [subst_psubst hin3 hsF, MvPowerSeries.subst_add hin3, subst_single_var hin3, subst_single_var hin3] at h
    exact h
  have hat : ∀ i : Fin 3, at1 i (g0F K p) =
      MvPowerSeries.C ((p : K)⁻¹) * frobVar p (at1 i (lgF K p)) := fun i => by
    unfold at1
    rw [subst_g_zero_eq_log hp2 hpK (hsX i), frobVar_psubst hp0 (hsX i), frobVar_X hp0]
  have hδ : in3 (cob F (g0F K p)) = MvPowerSeries.C ((p : K)⁻¹) *
      (PowerSeries.subst (in3 F ^ p) (lgF K p) -
        PowerSeries.subst (frobVar p (in3 F)) (lgF K p)) := by
    have e : in3 (cob F (g0F K p)) =
        PowerSeries.subst (in3 F) (g0F K p) - at1 0 (g0F K p) - at1 1 (g0F K p) := by
      unfold cob in3
      rw [MvPowerSeries.subst_sub hin3, MvPowerSeries.subst_sub hin3, subst_psubst hin3 hsF,
        subst_single_var hin3, subst_single_var hin3]
      rfl
    rw [e, subst_g_zero_eq_log hp2 hpK hsA, hat, hat, ← frobVar_psubst hp0 hsA, hlogA, frobVar_add hp0]
    ring
  have hgb : PowerSeries.subst ((MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) ^ p) (g0F K p) =
      at1 2 (lgF K p) - MvPowerSeries.X 2 := subst_pow_g_zero hp2 hpK (hsX 2)

  have key : d1 F (DeS p σ G) -
      MvPowerSeries.C (σ c) * (in3 (cob F (g0F K p)) * at1 2 (lgF K p)) =
      MvPowerSeries.C ((p : K)⁻¹) *
        ((frobVar p (MvPowerSeries.map σ (d1 F G)) - MvPowerSeries.C (p : K) * d1 F G) -
          (MvPowerSeries.subst ![frobVar p (in3 F),
              (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) ^ p] Φ -
            MvPowerSeries.subst ![in3 F ^ p,
              (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) ^ p] Φ)) -
        MvPowerSeries.C (σ c) * (in3 (cob F (g0F K p)) * MvPowerSeries.X 2) := by
    unfold DeS
    rw [partial_coboundary_linear hF0, hd1P, hd1s, hSΦ _ _ (hasSubst_pair hfA0 (hXp0 2)),
      hSΦ _ _ (hasSubst_pair hAp0 (hXp0 2)), hgb, hδ]
    ring
  have fin : frobVar p (MvPowerSeries.map σ (d1 F G)) - MvPowerSeries.C (p : K) * d1 F G =
      (MvPowerSeries.subst ![frobVar p (in3 F),
          (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) ^ p] Φ -
        MvPowerSeries.subst ![in3 F ^ p,
          (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) ^ p] Φ) +
      MvPowerSeries.C (p : K) *
        (MvPowerSeries.C (σ c) * (in3 (cob F (g0F K p)) * MvPowerSeries.X 2)) := by
    linear_combination (-(MvPowerSeries.C (p : K))) * key + MvPowerSeries.C (p : K) * hΔ -
      ((frobVar p (MvPowerSeries.map σ (d1 F G)) - MvPowerSeries.C (p : K) * d1 F G) -
          (MvPowerSeries.subst ![frobVar p (in3 F),
              (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) ^ p] Φ -
            MvPowerSeries.subst ![in3 F ^ p,
              (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) ^ p] Φ)) * hCC
  rw [fin]
  refine bd_add hE1 ?_
  have hb := bd_mul (inv_nonneg.mpr hppos.le) zero_le_one
    (bd_C (ι := Fin 3) (inv_nonneg.mpr hppos.le) hnp.le)
    (int_mul (bd_C zero_le_one (norm_sigma_le hσ hp.one_le hc)) (int_mul hδ3i (integral_X 2)))
  rwa [mul_one] at hb
end Formalism.InvariantFactorPaths.G7.CoefficientSupportCongruences
