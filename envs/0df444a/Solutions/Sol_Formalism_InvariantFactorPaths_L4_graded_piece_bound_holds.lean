-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.graded_piece_bound_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:57:02.17611+00:00
-- url     : https://prove2.me/submissions/2b58875c-85ad-4a08-837d-f9dc37ef08b0

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementA
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SmithZp
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_MeanGam
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_PartnerDeterminantHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_partner_determinant_holds
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_grLat_le_int
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_grLat_le_pol
import Theorems.Thm_Formalism_CountingSumsFrames_fockN_monomial_ge
import Theorems.Thm_Formalism_GM_TM_fockBil_apply
import Theorems.Thm_Formalism_GM_TM_mem_intPol_of_norm
import Theorems.Thm_P2M_Formalism_CountingSumsFrames_fockN_smul_right__bfa97ee757de


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M MvPolynomial Finset
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution : GradedPieceBound := by
  intro p _ K r _ LLw q J M ρ w e D c κ hProj hSat hκ k g hli hspan
  classical
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hpQ : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  obtain ⟨Pr, hPr⟩ := hProj
  have key := partner_determinant_holds p (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (Formalism.GM.TM.fockBil LLw LinearMap.id) k g κ hli
    ?_
  · exact key
  intro u hu hprim
  rw [hspan] at hu hprim
  set Gr := grLat p LLw J M ρ w (Fin.last K, ρ) e with hGr
  set XX := grSpan p LLw J M ρ w e with hXX
  have hGX : ∀ x ∈ Gr, x ∈ XX := fun x hx => Submodule.subset_span hx
  have hu0 : u ≠ 0 := by
    intro h0
    have := hprim 0 0 (Submodule.zero_mem _) (by rw [h0, smul_zero])
    exact not_isUnit_zero this
  have huI : u ∈ IntPol p (Fin (K + 1) × Fin r) := grLat_le_int LLw J M ρ w _ e hu
  have huP : u ∈ Pol p r LLw := grLat_le_pol LLw J M ρ w _ e hu
  have hne : u.support.Nonempty := by rwa [Finset.nonempty_iff_ne_empty, Ne, support_eq_empty]
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image u.support (fun m => ‖coeff m u‖) hne
  set a := coeff m u with ha
  have ha0 : a ≠ 0 := mem_support_iff.mp hm
  have han : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  have hmD : MultiDeg LLw m := by
    unfold Pol at huP
    rw [mem_restrictSupport_iff] at huP
    exact huP (Finset.mem_coe.mpr hm)
  set u0 := a⁻¹ • u with hu0def
  have hu0I : u0 ∈ IntPol p (Fin (K + 1) × Fin r) := by
    refine Formalism.GM.TM.mem_intPol_of_norm _ fun m' => ?_
    rw [hu0def, coeff_smul, smul_eq_mul, norm_mul, norm_inv, inv_mul_le_iff₀ han, mul_one]
    by_cases hm' : m' ∈ u.support
    · exact hmax m' hm'
    · rw [notMem_support_iff.mp hm', norm_zero]; exact han.le
  have hu0X : u0 ∈ XX := XX.smul_mem _ (hGX u hu)
  have hu0c : ‖coeff m u0‖ = 1 := by
    rw [hu0def, coeff_smul, smul_eq_mul, ← ha, inv_mul_cancel₀ ha0, norm_one]
  have huu0 : u = a • u0 := by rw [hu0def, smul_smul, mul_inv_cancel₀ ha0, one_smul]
  have hy : ((p : ℚ_[p]) ^ c) • u0 ∈ Gr := hSat u0 hu0X hu0I
  have hpc : ((p : ℚ_[p]) ^ c) ≠ 0 := pow_ne_zero _ hpQ
  have hnpc : ‖(p : ℚ_[p]) ^ c‖ = ((p : ℝ) ^ c)⁻¹ := by rw [norm_pow, Padic.norm_p, inv_pow]
  have hnpD : ‖(p : ℚ_[p]) ^ D‖ = ((p : ℝ) ^ D)⁻¹ := by rw [norm_pow, Padic.norm_p, inv_pow]

  have hage : ((p : ℝ) ^ c)⁻¹ ≤ ‖a‖ := by
    by_contra hlt
    push Not at hlt
    have hb : ‖a / (p : ℚ_[p]) ^ c‖ < 1 := by
      rw [norm_div, hnpc, div_inv_eq_mul]
      have hpc' : (0 : ℝ) < (p : ℝ) ^ c := by positivity
      calc ‖a‖ * (p : ℝ) ^ c < ((p : ℝ) ^ c)⁻¹ * (p : ℝ) ^ c := mul_lt_mul_of_pos_right hlt hpc'
        _ = 1 := inv_mul_cancel₀ hpc'.ne'
    let b : ℤ_[p] := ⟨a / (p : ℚ_[p]) ^ c, hb.le⟩
    have hub : u = b • (((p : ℚ_[p]) ^ c) • u0) := by
      rw [← algebraMap_smul ℚ_[p] b, PadicInt.algebraMap_apply, smul_smul]
      show u = (a / (p : ℚ_[p]) ^ c * (p : ℚ_[p]) ^ c) • u0
      rw [div_mul_cancel₀ _ hpc]; exact huu0
    have hunit := hprim b _ hy hub
    rw [PadicInt.isUnit_iff] at hunit
    have : ‖b‖ = ‖a / (p : ℚ_[p]) ^ c‖ := rfl
    linarith
  obtain ⟨hP1, hP2, hP3⟩ := hPr m hmD
  refine ⟨((p : ℚ_[p]) ^ c) • (((p : ℚ_[p]) ^ D) • Pr (monomial m 1)), ?_, ?_⟩
  · rw [hspan]
    exact hSat _ (XX.smul_mem _ hP1) hP2
  · rw [Formalism.GM.TM.fockBil_apply, LinearMap.id_apply, Formalism.CountingSumsFrames.fockN_smul_right', Formalism.CountingSumsFrames.fockN_smul_right']
    have e1 : fockN p LLw u (Pr (monomial m 1)) = a * fockN p LLw u0 (monomial m 1) := by
      unfold fockN
      rw [hP3 u (hGX u hu)]
      conv_lhs => rw [huu0]
      rw [Formalism.GM.TM.fock_smul_left, mul_div_assoc]
    have e2 := Formalism.CountingSumsFrames.fockN_monomial_ge LLw u0 m hmD hu0c
    rw [e1, norm_mul, norm_mul, norm_mul, hnpc, hnpD]
    have hpc' : (0 : ℝ) < ((p : ℝ) ^ c)⁻¹ := by positivity
    have hpD' : (0 : ℝ) < ((p : ℝ) ^ D)⁻¹ := by positivity
    have h1 : (p : ℝ) ^ (-κ) ≤ (p : ℝ) ^ (-((D + 2 * c : ℕ) : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hp1.le (by linarith)
    have h2 : (p : ℝ) ^ (-((D + 2 * c : ℕ) : ℝ)) = ((p : ℝ) ^ c)⁻¹ * (((p : ℝ) ^ D)⁻¹ * (((p : ℝ) ^ c)⁻¹ * 1)) := by
      rw [Real.rpow_neg hp0.le, Real.rpow_natCast, pow_add, two_mul, pow_add]
      field_simp
    rw [h2] at h1
    refine h1.trans ?_
    gcongr
end Formalism.InvariantFactorPaths.L4
