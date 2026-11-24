-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.ETerm.term_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:35:51.761848+00:00
-- url     : https://prove2.me/submissions/86633b17-5ab1-497e-82c6-f3294b5a6946

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NormNatCastLeOfDvd
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ETerm_jn_inl
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ETerm_lowDeg_jn
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ETerm_lowDeg_sub_le
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ETerm_jetPair_topLow
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ETerm_lin_s_extend_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ETerm_hasseDir_topLow
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ETerm_lowGe_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ETerm_lowGe_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ETerm_lowGe_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ETerm_integral_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ETerm_integral_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ETerm_norm_prod_pow_le_one
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ETerm_closure_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ETerm_norm_natCast_le_of_dvd
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ETerm_fact_dvd
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ETerm_dTot_inl
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ETerm_prod_piece
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_C_mul_right
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_eq_sum
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_sum_right
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_natCast_le_of_dvd
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_mul
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_pow


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
open Formalism.InvariantFactorPaths.G7.ETerm
open Formalism.DworkPowerSeriesWeights (Integral jetPair mfact jetPair_eq_sum jetPair_C_mul_right jetPair_sum_right)
variable {K Tp Lw Φ κ : Type} [NormedField K] [IsUltrametricDist K] [Fintype Tp] [Fintype Lw]
  [Fintype Φ] [Fintype κ]
namespace Formalism.InvariantFactorPaths.G7.ETerm
theorem _root_.solution (h1 : JetPairingHasseIdentity) (h2 : HasseDerivIntegralHomogeneous) (p : ℕ) (Z Y : MvPowerSeries (Tp ⊕ Lw) K)
    (aA : Φ → K) (dA : Φ → Tp →₀ ℕ) (aB : κ → K) (dB : κ → Tp →₀ ℕ) (b : κ → Lw → K)
    (e : Tp →₀ ℕ) (Q : MvPolynomial Lw K) (hp : p.Prime) (hpn : ‖(p : K)‖ = (p : ℝ)⁻¹)
    (haA : ∀ φ, ‖aA φ‖ ≤ 1) (haB : ∀ k, ‖aB k‖ ≤ 1) (hb : ∀ k x, ‖b k x‖ ≤ 1) (hZ : Integral Z)
    (hY : Integral Y) (hZlow : LowGe p Z) (hQ : ∀ n, ‖MvPolynomial.coeff n Q‖ ≤ 1)
    (i : ℕ) (k : Φ ⊕ κ ⊕ Fin 2 → ℕ) (hk : ∑ j, k j = i) (U : MvPowerSeries (Tp ⊕ Lw) K)
    (hU : Integral U) :
    ((p : K) ^ i)⁻¹ * (((Nat.multinomial univ k : ℕ) : K) *
        jetPair (topMonoP e * lowPoly Q) ((∏ j, piece p Z Y aA dA aB dB b j ^ k j) * U)) = 0 ∨
      ∃ w, valid p aA dA aB dB b e Q w ∧
        ‖((p : K) ^ i)⁻¹ * (((Nat.multinomial univ k : ℕ) : K) *
          jetPair (topMonoP e * lowPoly Q) ((∏ j, piece p Z Y aA dA aB dB b j ^ k j) * U))‖ ≤
          bnd K p e w := by
  classical
  set β : κ →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun x => k (Sum.inr (Sum.inl x))) with hβ
  have hβx : ∀ x, β x = k (Sum.inr (Sum.inl x)) := fun x => rfl
  have hlin : ∏ x, lowLin (Tp := Tp) (b x) ^ k (Sum.inr (Sum.inl x)) =
      ∏ x, linS (ext0 (Tp := Tp) b x) ^ β x :=
    Finset.prod_congr rfl fun x _ => by rw [lin_s_extend_zero, hβx]
  rw [prod_piece, hlin, h1 K (Tp ⊕ Lw) κ (ext0 b) β, hasseDir_topLow, jetPair_topLow,
    Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine closure_sum _ _ _ _ fun n hn => ?_
  rw [MvPowerSeries.coeff_monomial_mul]
  split_ifs with hle
  swap
  · left; simp
  set v := MvPowerSeries.coeff (jn e n - dTot dA dB k)
    (Z ^ k (Sum.inr (Sum.inr 0)) * (Y ^ k (Sum.inr (Sum.inr 1)) * U)) with hv
  by_cases hc : cTot p aA aB k * v = 0
  · left; simp [hc]
  right
  have hc1 : cTot p aA aB k ≠ 0 := left_ne_zero_of_mul hc
  have hv1 : v ≠ 0 := right_ne_zero_of_mul hc
  have hsum : ∑ φ, k (Sum.inl φ) + ∑ x, β x + k (Sum.inr (Sum.inr 0)) + k (Sum.inr (Sum.inr 1)) = i := by
    rw [← hk, Fintype.sum_sum_type, Fintype.sum_sum_type, Fin.sum_univ_two]
    simp only [hβx]
    ring
  refine ⟨(fun φ => k (Sum.inl φ), β, k (Sum.inr (Sum.inr 0)), n), ⟨hn, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro φ hφ h0
    apply hc1
    have : ∏ φ, aA φ ^ k (Sum.inl φ) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ φ) (by rw [h0]; exact zero_pow hφ)
    simp [cTot, this]
  · intro x hx h0
    apply hc1
    have : ∏ x, aB x ^ k (Sum.inr (Sum.inl x)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ x) (by rw [h0]; exact zero_pow hx)
    simp [cTot, this]
  · intro τ
    have := hle (Sum.inl τ)
    rw [jn_inl, dTot_inl] at this
    exact this
  · have h3 := lowGe_mul (lowGe_pow hZlow (k (Sum.inr (Sum.inr 0))))
      (lowGe_zero (Y ^ k (Sum.inr (Sum.inr 1)) * U)) _ hv1
    have h4 := lowDeg_sub_le (jn e n) (dTot dA dB k)
    rw [lowDeg_jn] at h4
    show p * k (Sum.inr (Sum.inr 0)) ≤ n.degree
    omega
  · have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    set s := ∑ φ, k (Sum.inl φ) + ∑ x, β x + k (Sum.inr (Sum.inr 0)) with hs
    set cR := MvPolynomial.coeff n (hasseDir b β Q) with hcR
    have hx : ((p : K) ^ i)⁻¹ * (((Nat.multinomial univ k : ℕ) : K) *
        (((∏ x, (β x).factorial : ℕ) : K) * (cR * ((mfact e * mfact n : ℕ) : K) *
          (cTot p aA aB k * v)))) =
        (((p : K) ^ i)⁻¹ * (p : K) ^ k (Sum.inr (Sum.inr 1))) *
          ((Nat.multinomial univ k * ∏ x, (β x).factorial : ℕ) : K) * ((mfact e : ℕ) : K) *
          ((mfact n : ℕ) : K) * (cR * ((∏ φ, aA φ ^ k (Sum.inl φ)) *
            ((∏ x, aB x ^ k (Sum.inr (Sum.inl x))) * v))) := by
      unfold cTot
      push_cast
      ring
    rw [hx]
    have hpp : ‖((p : K) ^ i)⁻¹ * (p : K) ^ k (Sum.inr (Sum.inr 1))‖ = (p : ℝ) ^ s := by
      rw [norm_mul, norm_inv, norm_pow, norm_pow, hpn, ← hsum, pow_add, inv_pow, inv_pow, mul_inv,
        inv_inv, inv_inv, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hp0.ne'), mul_one]
    have hm : ‖((Nat.multinomial univ k * ∏ x, (β x).factorial : ℕ) : K)‖ ≤
        ‖(((∑ x, β x).factorial : ℕ) : K)‖ := norm_natCast_le_of_dvd (fact_dvd k)
    have ht : ‖cR * ((∏ φ, aA φ ^ k (Sum.inl φ)) *
        ((∏ x, aB x ^ k (Sum.inr (Sum.inl x))) * v))‖ ≤ 1 := by
      rw [norm_mul, norm_mul, norm_mul]
      refine mul_le_one₀ ((h2 K Lw κ b β Q).1 hQ hb n) (by positivity) ?_
      refine mul_le_one₀ (norm_prod_pow_le_one _ _ _ haA) (by positivity) ?_
      refine mul_le_one₀ (norm_prod_pow_le_one _ _ _ haB) (norm_nonneg _) ?_
      exact integral_mul (integral_pow hZ _) (integral_mul (integral_pow hY _) hU) _
    rw [norm_mul, norm_mul, norm_mul, norm_mul, hpp]
    unfold bnd
    show _ ≤ (p : ℝ) ^ s * ‖((mfact e : ℕ) : K)‖ * ‖(((∑ x, β x).factorial : ℕ) : K)‖ *
      ‖((mfact n : ℕ) : K)‖
    calc _ ≤ (p : ℝ) ^ s * ‖(((∑ x, β x).factorial : ℕ) : K)‖ * ‖((mfact e : ℕ) : K)‖ *
          ‖((mfact n : ℕ) : K)‖ * 1 := by gcongr
      _ = _ := by ring
end Formalism.InvariantFactorPaths.G7.ETerm
