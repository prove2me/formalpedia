-- Prove2me | solution 1 for Formalism.L2.LamCM.keyDeg_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:27:29.03845+00:00
-- url     : https://prove2.me/submissions/c194b883-d31a-447e-9cfe-f280be5eb693

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementB
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ValuationLeOfEqAlgebraMap
import Theorems.Thm_Formalism_L2_LamCM_isLocGen_pow8_div_pow4
import Theorems.Thm_Formalism_L2_LamCM_valuation_le_of_eq_algebraMap

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
open NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped nonZeroDivisors ComplexOrder
namespace Formalism.L2.LamCM
theorem _root_.solution (hKF : KeyFormula) (K : Type) [Field K] [NumberField K] (x : KeyIn K) (T abelian₂ : MLine K)
    (hT : T.Good) (hL : abelian₂.Good) (hloc : ∀ p, KeyLocAt x T abelian₂ p) (harch : ∀ σ, KeyArchAt x T abelian₂ σ)
    (hN : ∀ k : K, k ≠ 0 → ∑ σ : K →+* ℂ, Real.log ‖σ k‖ =
      Real.log ((FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (𝓞 K)⁰ k) : ℚ) : ℝ))
    (hS : ∀ (I : FractionalIdeal (𝓞 K)⁰ K) (k : K), I ≠ 0 → k ≠ 0 →
      (∀ p : HeightOneSpectrum (𝓞 K), ∃ c : K, IsLocGen p c I ∧ p.valuation K k ≤ p.valuation K c ∧
        p.valuation K k⁻¹ ≤ p.valuation K c⁻¹) → FractionalIdeal.spanSingleton (𝓞 K)⁰ k = I) :
    T.dual.deg = (1 / 2) * abelian₂.dual.deg + (x.P.g : ℝ) / 4 * (Module.finrank ℚ K : ℝ) * Real.log (2 * Real.pi) := by
  obtain ⟨κ, hH, hF, hU1, -, hU2⟩ := hKF
  have hk0 : ((κ K x : Kˣ) : K) ≠ 0 := Units.ne_zero _

  have hloc' : ∀ p : HeightOneSpectrum (𝓞 K), ∃ c : K, IsLocGen p c (T.I ^ 8 * (abelian₂.I ^ 4)⁻¹) ∧
      p.valuation K ((κ K x : Kˣ) : K) ≤ p.valuation K c ∧
      p.valuation K ((κ K x : Kˣ) : K)⁻¹ ≤ p.valuation K c⁻¹ := by
    intro p
    obtain ⟨K', _, _, R, _, _, _, _, _, f, x', a, d, ca, cd, ua, ud, hPB, hInt, hval, ha, hd, hca, hcd⟩ := hloc p
    obtain ⟨th', hth', v', hv', M, xR, hth, hv, hdet, hPBR⟩ := hInt
    have hHx := hH K' x'.P x'.g_pos x'.rig x'.rig_gen x'.th x'.th_ne x'.v x'.basis th' hth' v' hv' a M hth hv
    have hFx := hF K K' f x x' hPB
    obtain ⟨u, hu, -⟩ := hU1 R K' xR _ hPBR
    rw [show (⟨x'.P, x'.g_pos, x'.rig, x'.rig_gen, x'.th, x'.th_ne, x'.v, x'.basis⟩ : KeyIn K') = x' from rfl,
      hFx, hu, hdet, ha, hd] at hHx
    have hc : ca ^ 8 / cd ^ 4 ≠ 0 := div_ne_zero (pow_ne_zero _ hca.1) (pow_ne_zero _ hcd.1)
    have hfca : f ca ≠ 0 := (map_ne_zero f).mpr hca.1
    have hbb : algebraMap R K' (ud : R) * algebraMap R K' ((ud⁻¹ : Rˣ) : R) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have hw : f ((κ K x : Kˣ) / (ca ^ 8 / cd ^ 4)) = algebraMap R K' ((ua ^ 8 * u * ud⁻¹ ^ 4 : Rˣ) : R) := by
      rw [map_div₀, map_div₀, map_pow, map_pow, div_div_eq_mul_div, div_eq_iff (pow_ne_zero _ hfca)]
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow]
      linear_combination (-(algebraMap R K' ((ud⁻¹ : Rˣ) : R)) ^ 4) * hHx -
        f (κ K x : Kˣ) * f cd ^ 4 * (1 + algebraMap R K' (ud : R) * algebraMap R K' ((ud⁻¹ : Rˣ) : R) +
          (algebraMap R K' (ud : R) * algebraMap R K' ((ud⁻¹ : Rˣ) : R)) ^ 2 +
          (algebraMap R K' (ud : R) * algebraMap R K' ((ud⁻¹ : Rˣ) : R)) ^ 3) * hbb
    have hw' : f (((κ K x : Kˣ) : K)⁻¹ / (ca ^ 8 / cd ^ 4)⁻¹) =
        algebraMap R K' (((ua ^ 8 * u * ud⁻¹ ^ 4)⁻¹ : Rˣ) : R) := by
      rw [inv_div_inv, ← inv_div, map_inv₀, hw, map_units_inv]
    exact ⟨ca ^ 8 / cd ^ 4, isLocGen_pow8_div_pow4 hT.1 hL.1 hca hcd,
      valuation_le_of_eq_algebraMap p f hval hc _ hw,
      valuation_le_of_eq_algebraMap p f hval (inv_ne_zero hc) _ hw'⟩
  have hne : T.I ^ 8 * (abelian₂.I ^ 4)⁻¹ ≠ 0 := mul_ne_zero (pow_ne_zero _ hT.1) (inv_ne_zero (pow_ne_zero _ hL.1))
  have hspan := hS _ _ hne hk0 hloc'
  have hNT : ((FractionalIdeal.absNorm T.I : ℚ) : ℝ) ≠ 0 := by exact_mod_cast (map_ne_zero (FractionalIdeal.absNorm : FractionalIdeal (𝓞 K)⁰ K →*₀ ℚ)).mpr hT.1
  have hNL : ((FractionalIdeal.absNorm abelian₂.I : ℚ) : ℝ) ≠ 0 := by exact_mod_cast (map_ne_zero (FractionalIdeal.absNorm : FractionalIdeal (𝓞 K)⁰ K →*₀ ℚ)).mpr hL.1
  have hnorm : ∑ σ : K →+* ℂ, Real.log ‖σ (κ K x : Kˣ)‖ =
      8 * Real.log ((FractionalIdeal.absNorm T.I : ℚ) : ℝ) - 4 * Real.log ((FractionalIdeal.absNorm abelian₂.I : ℚ) : ℝ) := by
    rw [hN _ hk0, hspan, map_mul, map_pow, map_inv₀, map_pow]
    push_cast
    rw [Real.log_mul (pow_ne_zero _ hNT) (inv_ne_zero (pow_ne_zero _ hNL)), Real.log_inv, Real.log_pow, Real.log_pow]
    push_cast
    ring

  have harch' : ∀ σ : K →+* ℂ, Real.log ‖σ (κ K x : Kˣ)‖ + 8 * Real.log (T.n σ) - 4 * Real.log (abelian₂.n σ) =
      2 * (x.P.g : ℝ) * Real.log (2 * Real.pi) := by
    intro σ
    obtain ⟨xσ, u, Hm, W, χ, θ, Fd, hPB, hAH, hRig, hFn, hDiff, hFd, hTn, hLn⟩ := harch σ
    have hFσ := hF K ℂ σ x xσ hPB
    obtain ⟨-, -, -, hg, -⟩ := hPB
    have h2 := hU2 xσ u Hm W χ θ Fd (T.n σ ^ 2) (abelian₂.n σ ^ 2)⁻¹ hAH hRig hFn hDiff hFd hTn
      (by rw [hLn, inv_div])
    rw [hFσ, hg] at h2
    have hk : 0 < ‖σ (κ K x : Kˣ)‖ := norm_pos_iff.mpr ((map_ne_zero σ).mpr hk0)
    have hB : (T.n σ ^ 2) ^ 4 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ (hT.2 σ).ne')
    have hC : ((abelian₂.n σ ^ 2)⁻¹) ^ 2 ≠ 0 := pow_ne_zero _ (inv_ne_zero (pow_ne_zero _ (hL.2 σ).ne'))
    have h3 := congrArg Real.log h2
    rw [Real.log_mul (mul_ne_zero hk.ne' hB) hC, Real.log_mul hk.ne' hB] at h3
    simp only [Real.log_pow, Real.log_inv] at h3
    push_cast at h3
    linarith
  have hsum : ∑ σ : K →+* ℂ, Real.log ‖σ (κ K x : Kˣ)‖ + 8 * ∑ σ : K →+* ℂ, Real.log (T.n σ) -
      4 * ∑ σ : K →+* ℂ, Real.log (abelian₂.n σ) = (Module.finrank ℚ K : ℝ) * (2 * (x.P.g : ℝ) * Real.log (2 * Real.pi)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
      Finset.sum_congr rfl (fun σ _ => harch' σ), Finset.sum_const, Finset.card_univ,
      NumberField.Embeddings.card, nsmul_eq_mul]
  have hdT : T.dual.deg = Real.log ((FractionalIdeal.absNorm T.I : ℚ) : ℝ) + ∑ σ : K →+* ℂ, Real.log (T.n σ) := by
    simp only [MLine.dual, MLine.deg, map_inv₀, Rat.cast_inv, Real.log_inv, Finset.sum_neg_distrib]
    ring
  have hdL : abelian₂.dual.deg = Real.log ((FractionalIdeal.absNorm abelian₂.I : ℚ) : ℝ) + ∑ σ : K →+* ℂ, Real.log (abelian₂.n σ) := by
    simp only [MLine.dual, MLine.deg, map_inv₀, Rat.cast_inv, Real.log_inv, Finset.sum_neg_distrib]
    ring
  rw [hdT, hdL]
  linear_combination (1 / 8 : ℝ) * hsum - (1 / 8 : ℝ) * hnorm
end Formalism.L2.LamCM
