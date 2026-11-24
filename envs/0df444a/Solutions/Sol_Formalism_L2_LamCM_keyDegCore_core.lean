-- Prove2me | solution 1 for Formalism.L2.LamCM.keyDegCore_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:27:27.730337+00:00
-- url     : https://prove2.me/submissions/07ce790e-fa3d-42cb-ab2b-9c3d25fca143

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CmNumbersLink
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_HadamardLoc0
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_DetValuationLeOne
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
theorem _root_.solution (hKF : KeyCore) (K : Type) [Field K] [NumberField K] (x : KeyIn K) (T abelian₂ : MLine K)
    (hT : T.Good) (hL : abelian₂.Good) (hloc : ∀ p, KeyLocAt x T abelian₂ p) (harch : ∀ σ, KeyArchAt x T abelian₂ σ)
    (hN : ∀ k : K, k ≠ 0 → ∑ σ : K →+* ℂ, Real.log ‖σ k‖ =
      Real.log ((FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (𝓞 K)⁰ k) : ℚ) : ℝ))
    (hS : ∀ (I : FractionalIdeal (𝓞 K)⁰ K) (k : K), I ≠ 0 → k ≠ 0 →
      (∀ p : HeightOneSpectrum (𝓞 K), ∃ c : K, IsLocGen p c I ∧ p.valuation K k ≤ p.valuation K c ∧
        p.valuation K k⁻¹ ≤ p.valuation K c⁻¹) → FractionalIdeal.spanSingleton (𝓞 K)⁰ k = I) :
    T.dual.deg = (1 / 2) * abelian₂.dual.deg + (x.P.g : ℝ) / 4 * (Module.finrank ℚ K : ℝ) * Real.log (2 * Real.pi) := by
  obtain ⟨κ, hH, hF, hU1, hU2⟩ := hKF
  set k : K := (κ K x : K) with hkdef
  have hk : k ≠ 0 := (κ K x).ne_zero
  have hloc' : ∀ p : HeightOneSpectrum (𝓞 K), ∃ ca cd : K, IsLocGen p ca T.I ∧ IsLocGen p cd abelian₂.I ∧
      p.valuation K k ≤ p.valuation K (ca ^ 8 / cd ^ 4) ∧ p.valuation K k⁻¹ ≤ p.valuation K (ca ^ 8 / cd ^ 4)⁻¹ := by
    intro p
    obtain ⟨K', _, _, R, _, _, _, _, _, f, x', a, d, ca, cd, ua, ud, hPB, hInt, hval, ha, hd, hca, hcd⟩ := hloc p
    obtain ⟨th', hth', v', hv', M, xR, hth'eq, hv'eq, hMdet, hPBR⟩ := hInt
    have hFx : (κ K' x' : K') = f k := hF K K' f x x' hPB
    have hHx : a ^ 8 * (κ K' ⟨x'.P, x'.g_pos, x'.rig, x'.rig_gen, th', hth', v', hv'⟩ : K') =
        M.det ^ 4 * (κ K' x' : K') :=
      hH K' x'.P x'.g_pos x'.rig x'.rig_gen x'.th x'.th_ne x'.v x'.basis th' hth' v' hv' a M hth'eq hv'eq
    obtain ⟨u, hu⟩ := hU1 R K' xR _ hPBR
    rw [hu, hFx, hMdet, ha, hd] at hHx
    have hfa : f ca ≠ 0 := (map_ne_zero f).2 hca.1
    have hfd : f cd ≠ 0 := (map_ne_zero f).2 hcd.1
    have hD : algebraMap R K' (ud : R) ≠ 0 := (ud.isUnit.map (algebraMap R K')).ne_zero
    have hc : ca ^ 8 / cd ^ 4 ≠ 0 := div_ne_zero (pow_ne_zero _ hca.1) (pow_ne_zero _ hcd.1)
    have hfk : f k = (f ca * algebraMap R K' (ua : R)) ^ 8 * algebraMap R K' (u : R) /
        (f cd * algebraMap R K' (ud : R)) ^ 4 := by
      rw [eq_div_iff (pow_ne_zero _ (mul_ne_zero hfd hD)), hHx]; ring
    have hw : f (k / (ca ^ 8 / cd ^ 4)) = algebraMap R K' ((ua ^ 8 * u * ud⁻¹ ^ 4 : Rˣ) : R) := by
      rw [Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_mul, map_mul,
        map_pow, map_pow, map_units_inv, map_div₀, map_div₀, map_pow, map_pow, hfk]
      field_simp
    have hw' : f (k⁻¹ / (ca ^ 8 / cd ^ 4)⁻¹) = algebraMap R K' (((ua ^ 8 * u * ud⁻¹ ^ 4)⁻¹ : Rˣ) : R) := by
      rw [inv_div_inv, ← inv_div, map_inv₀, hw, map_units_inv]
    exact ⟨ca, cd, hca, hcd, valuation_le_of_eq_algebraMap p f hval hc _ hw,
      valuation_le_of_eq_algebraMap p f hval (inv_ne_zero hc) _ hw'⟩
  have hJ : T.I ^ 8 * (abelian₂.I ^ 4)⁻¹ ≠ 0 := mul_ne_zero (pow_ne_zero _ hT.1) (inv_ne_zero (pow_ne_zero _ hL.1))
  have hspan : FractionalIdeal.spanSingleton (𝓞 K)⁰ k = T.I ^ 8 * (abelian₂.I ^ 4)⁻¹ := hS _ k hJ hk (fun p => by
    obtain ⟨ca, cd, h1, h2, h3, h4⟩ := hloc' p
    exact ⟨_, isLocGen_pow8_div_pow4 hT.1 hL.1 h1 h2, h3, h4⟩)
  have hNT : ((FractionalIdeal.absNorm T.I : ℚ) : ℝ) ≠ 0 := by
    exact_mod_cast (FractionalIdeal.absNorm_eq_zero_iff.not.2 hT.1)
  have hNL : ((FractionalIdeal.absNorm abelian₂.I : ℚ) : ℝ) ≠ 0 := by
    exact_mod_cast (FractionalIdeal.absNorm_eq_zero_iff.not.2 hL.1)
  have hNk : Real.log ((FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (𝓞 K)⁰ k) : ℚ) : ℝ) =
      8 * Real.log ((FractionalIdeal.absNorm T.I : ℚ) : ℝ) - 4 * Real.log ((FractionalIdeal.absNorm abelian₂.I : ℚ) : ℝ) := by
    rw [hspan, map_mul, map_inv₀, map_pow, map_pow]
    push_cast
    rw [Real.log_mul (pow_ne_zero _ hNT) (inv_ne_zero (pow_ne_zero _ hNL)), Real.log_inv, Real.log_pow,
      Real.log_pow]
    push_cast
    ring
  have harch' : ∀ σ : K →+* ℂ, Real.log ‖σ k‖ + 8 * Real.log (T.n σ) - 4 * Real.log (abelian₂.n σ) =
      2 * (x.P.g : ℝ) * Real.log (2 * Real.pi) := by
    intro σ
    obtain ⟨xσ, u, Hm, W, χ, θ, Fd, hPB, hAH, hRig, hFn, hDiff, hFD, hTn, hLn⟩ := harch σ
    have hFσ : (κ ℂ xσ : ℂ) = σ k := hF K ℂ σ x xσ hPB
    obtain ⟨_, _, _, hg, _⟩ := hPB
    have he : (volume Fd).toReal / (Real.pi ^ xσ.P.g * ‖W.det‖ ^ 2) = (abelian₂.n σ ^ 2)⁻¹ := by
      rw [hLn, inv_div]
    have hU := hU2 xσ u Hm W χ θ Fd _ _ hAH hRig hFn hDiff hFD hTn rfl
    rw [he, hFσ, hg] at hU
    have hsk0 : 0 < ‖σ k‖ := norm_pos_iff.2 ((map_ne_zero σ).2 hk)
    have ht := hT.2 σ
    have hl := hL.2 σ
    have h8 : ‖σ k‖ * (T.n σ ^ 2) ^ 4 * ((abelian₂.n σ ^ 2)⁻¹) ^ 2 = ‖σ k‖ * T.n σ ^ 8 * (abelian₂.n σ ^ 4)⁻¹ := by
      field_simp
    rw [h8] at hU
    have := congrArg Real.log hU
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_inv,
      Real.log_pow, Real.log_pow, Real.log_pow] at this
    push_cast at this
    linarith
  have hsum := Finset.sum_congr (s₁ := (Finset.univ : Finset (K →+* ℂ))) rfl (fun σ _ => harch' σ)
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, NumberField.Embeddings.card K ℂ, nsmul_eq_mul, hN k hk, hNk] at hsum
  simp only [MLine.deg, MLine.dual, map_inv₀, Rat.cast_inv, Real.log_inv, Finset.sum_neg_distrib]
  linarith
end Formalism.L2.LamCM
