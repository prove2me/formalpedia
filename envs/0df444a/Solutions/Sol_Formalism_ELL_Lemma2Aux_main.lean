-- Prove2me | solution 1 for Formalism.ELL.Lemma2Aux.main
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:36:59.350799+00:00
-- url     : https://prove2.me/submissions/db1f463d-1599-4d55-ad8a-4634a629cd05

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionWeights
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CompExp
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CoefficientWeightsLemmaTwo
import Theorems.Thm_Formalism_ELL_Lemma2Aux_norm_nat_eq_one
import Theorems.Thm_Formalism_ELL_Lemma2Aux_choose_pow_mul_modEq
import Theorems.Thm_Formalism_ELL_Lemma2Aux_fact_choose_prime_pow
import Theorems.Thm_Formalism_ELL_Lemma2Aux_coeff_X0_add_X1_pow
import Theorems.Thm_Formalism_ELL_Lemma2Aux_add_identity
import Theorems.Thm_Formalism_ELL_Lemma2Aux_log_rescale
import Theorems.Thm_Formalism_ELL_Lemma2Aux_exp_rescale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
open Formalism Formalism.ELL Formalism.ELL.Lemma2Aux
variable {K : Type*} [NormedField K] [IsUltrametricDist K]
open Formalism.G
universe u
namespace Formalism.ELL.Lemma2Aux
theorem _root_.solution (hCE : Formalism.ELL.CompExpWeight.{u}) : Formalism.ELL.EllipticTorsionWeights.{u} := by
  intro K _ _ _ p hp hp0 hp1 F l E g ζ hl hE0 hEl hlE hEb hζ hζu hhom hg0 hH hh _hg1 n
  set D : ℝ := (p : ℝ) ^ 2 - 1 with hD
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hDpos : 0 < D := by rw [hD]; nlinarith
  set c : ℝ := ‖(p : K)‖ ^ (1 / D) with hcdef
  have hc : 0 < c := Real.rpow_pos_of_pos hp0 _
  have hc1 : c ≤ 1 := Real.rpow_le_one (norm_nonneg _) hp1.le (by positivity)
  have cz : ∀ k : ℤ, c ^ k = ‖(p : K)‖ ^ ((k : ℝ) / D) := by
    intro k
    rw [hcdef, ← Real.rpow_intCast, ← Real.rpow_mul (norm_nonneg _)]
    congr 1
    ring
  have hEb' : ∀ n : ℕ, 1 ≤ n → ‖coeff n E‖ ≤ c ^ (1 - (n : ℤ)) := by
    intro m hm
    rw [cz]
    convert hEb m hm using 2
    push_cast
    ring
  set G : PowerSeries K := PowerSeries.subst E g with hGdef
  have hE' : PowerSeries.HasSubst E := PowerSeries.HasSubst.of_constantCoeff_zero' hE0

  have hbin : ∀ i j : ℕ, 1 ≤ i → 1 ≤ j →
      ‖(((i + j).choose i : ℕ) : K)‖ * ‖coeff (i + j) G‖ ≤ c ^ (-((i + j : ℕ) : ℤ)) := by
    intro i j hi hj
    have hS : MvPowerSeries.constantCoeff
        (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
    have hw := hCE K (Fin 2) c hc hc1 E hE0 hEb' _ hH (Finsupp.single 0 i + Finsupp.single 1 j)
    rw [add_identity (FK F).toPowerSeries (FK F).zero_constantCoeff l E g hl.1 hl.2.2 hE0 hEl hlE]
      at hw
    have e1 : MvPowerSeries.coeff (Finsupp.single 0 i + Finsupp.single 1 j)
        (PowerSeries.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) G) =
        (((i + j).choose i : ℕ) : K) * coeff (i + j) G := by
      rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hS),
        finsum_eq_single _ (i + j)]
      · rw [coeff_X0_add_X1_pow, if_pos rfl, smul_eq_mul, mul_comm]
      · intro d hd
        rw [coeff_X0_add_X1_pow, if_neg (Ne.symm hd), smul_zero]
    have e2 : MvPowerSeries.coeff (Finsupp.single 0 i + Finsupp.single 1 j)
        (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) G) = 0 := by
      rw [PowerSeries.coeff_subst_single, if_neg]
      intro h
      have := congrArg (· 1) h
      simp at this
      omega
    have e3 : MvPowerSeries.coeff (Finsupp.single 0 i + Finsupp.single 1 j)
        (PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) G) = 0 := by
      rw [PowerSeries.coeff_subst_single, if_neg]
      intro h
      have := congrArg (· 0) h
      simp at this
      omega
    have edeg : (Finsupp.single (0 : Fin 2) i + Finsupp.single 1 j).degree = i + j := by
      rw [map_add, Finsupp.degree_single, Finsupp.degree_single]
    rw [map_sub, map_sub, e1, e2, e3, sub_zero, sub_zero, norm_mul, edeg] at hw
    exact_mod_cast hw

  have hpq : p < p ^ 2 := by
    rw [sq]; exact Nat.lt_mul_self_iff.2 hp.two_le
  have hq0 : p ^ 2 - 1 ≠ 0 := Nat.sub_ne_zero_of_lt (one_lt_pow' hp.one_lt (by norm_num))
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hq0] at hζ
    exact zero_ne_one hζ
  have hnz : ‖ζ‖ = 1 := by
    have h1 : ‖ζ‖ ^ (p ^ 2 - 1) = 1 := by rw [← norm_pow, hζ, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hq0).1 h1
  have hζbound : ∀ m : ℕ, ‖(ζ ^ m - ζ ^ p) * coeff m G‖ ≤ c ^ (-(m : ℤ)) := by
    intro m
    have hlz := log_rescale (FK F) l ζ hζ0 hl hhom
    have hEz := exp_rescale l E ζ hE0 hl.1 hEl hlE hlz
    have ha : PowerSeries.HasSubst (ζ • X : PowerSeries K) := PowerSeries.HasSubst.smul_X' ζ
    set h' : PowerSeries K := PowerSeries.subst (ζ • X : PowerSeries K) g - ζ ^ p • g with hh'
    have hid : (PowerSeries.subst E h' : PowerSeries K) = PowerSeries.rescale ζ G - ζ ^ p • G := by
      rw [hh', PowerSeries.subst_sub hE', PowerSeries.subst_smul hE',
        PowerSeries.subst_comp_subst_apply ha hE', PowerSeries.subst_smul hE', PowerSeries.subst_X hE',
        PowerSeries.rescale_eq_subst, hGdef, PowerSeries.subst_comp_subst_apply hE' ha, hEz]
    have hint : IntegralMv (ι := Unit) h' := by
      intro d
      have hd : d = Finsupp.single () (d ()) := by
        refine Finsupp.ext fun x => ?_
        cases x
        simp
      rw [hd]
      exact hh (d ())
    have hw := hCE K Unit c hc hc1 E hE0 hEb' h' hint (Finsupp.single () m)
    have hsub : (fun i : Unit => E.subst (MvPowerSeries.X i : MvPowerSeries Unit K)) = fun _ => E := by
      funext i
      cases i
      exact PowerSeries.X_subst E
    rw [hsub, ← PowerSeries.subst_def, hid, Finsupp.degree_single] at hw
    have hcm : MvPowerSeries.coeff (Finsupp.single () m) (PowerSeries.rescale ζ G - ζ ^ p • G) =
        (ζ ^ m - ζ ^ p) * coeff m G := by
      change coeff m (PowerSeries.rescale ζ G - ζ ^ p • G) = _
      rw [map_sub, PowerSeries.coeff_rescale, LinearMap.map_smul_of_tower, smul_eq_mul, sub_mul]
    rw [hcm] at hw
    exact hw
  have strong : ∀ x : K, ‖x‖ ≤ c ^ (-(n : ℤ)) → ‖x‖ ≤ ‖(p : K)‖ ^ (-(n : ℝ) / D) := by
    intro x hx
    rw [cz] at hx
    push_cast at hx
    exact hx
  have weak : ∀ x : K, ‖(p : K)‖ * ‖x‖ ≤ c ^ (-(n : ℤ)) →
      ‖x‖ ≤ ‖(p : K)‖ ^ (-1 - (n : ℝ) / D) := by
    intro x hx
    rw [cz] at hx
    push_cast at hx
    rw [show (-1 - (n : ℝ) / D) = -1 + (-(n : ℝ) / D) by ring, Real.rpow_add hp0, Real.rpow_neg_one,
      le_inv_mul_iff₀ hp0]
    exact hx
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · left
    have h0 : coeff 0 G = 0 := by
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hGdef]
      exact PowerSeries.constantCoeff_subst_eq_zero hE0 g hg0
    rw [h0, norm_zero]
    positivity
  obtain ⟨k, m, hnm, hm⟩ : ∃ k m, p ^ k * m = n ∧ ¬ p ∣ m :=
    ⟨_, _, Nat.ordProj_mul_ordCompl_eq_self n p, Nat.not_dvd_ordCompl hp hn.ne'⟩
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hnm
    omega
  have hpk : 1 ≤ p ^ k := Nat.one_le_pow _ _ hp.pos
  by_cases hm1 : m = 1
  · rw [hm1, mul_one] at hnm
    subst hnm
    rcases Nat.even_or_odd k with hke | hko
    · left
      apply strong
      have hb := hζbound (p ^ k)
      have hunit : ‖ζ ^ (p ^ k) - ζ ^ p‖ = 1 := by
        rcases Nat.eq_zero_or_pos k with rfl | hkpos
        · have hndvd : ¬ (p ^ 2 - 1) ∣ (p - 1) := by
            intro h
            have h3 := Nat.le_of_dvd (by have := hp.two_le; omega) h
            have h4 := hpq
            have h5 := hp.two_le
            generalize p ^ 2 = q at h3 h4
            omega
          rw [pow_zero, pow_one, show ζ ^ p = ζ * ζ ^ (p - 1) by
            rw [← pow_succ', Nat.sub_add_cancel hp.one_le]]
          rw [show ζ - ζ * ζ ^ (p - 1) = -(ζ * (ζ ^ (p - 1) - 1)) by ring, norm_neg, norm_mul, hnz,
            hζu _ hndvd, one_mul]
        · obtain ⟨t, ht⟩ := hke
          have hle : p ≤ p ^ k := Nat.le_self_pow (by omega) p
          have hd1 : (p ^ 2 - 1) ∣ p ^ k - 1 := by
            have := Nat.sub_dvd_pow_sub_pow (p ^ 2) 1 t
            rw [one_pow, ← pow_mul] at this
            rwa [show 2 * t = k by omega] at this
          have hndvd : ¬ (p ^ 2 - 1) ∣ (p ^ k - p) := by
            intro h
            have h2 := Nat.dvd_sub hd1 h
            have hpk' := hpk
            have hle' := hle
            rw [show p ^ k - 1 - (p ^ k - p) = p - 1 by
              generalize p ^ k = r at hpk' hle' ⊢; omega] at h2
            have h3 := Nat.le_of_dvd (by have := hp.two_le; omega) h2
            have h4 := hpq
            have h5 := hp.two_le
            generalize p ^ 2 = q at h3 h4
            omega
          rw [show ζ ^ (p ^ k) = ζ ^ p * ζ ^ (p ^ k - p) by
            rw [← pow_add, Nat.add_sub_cancel' hle]]
          rw [show ζ ^ p * ζ ^ (p ^ k - p) - ζ ^ p = ζ ^ p * (ζ ^ (p ^ k - p) - 1) by ring,
            norm_mul, norm_pow, hnz, one_pow, hζu _ hndvd, one_mul]
      rw [norm_mul, hunit, one_mul] at hb
      exact hb
    · right
      refine ⟨k, hko, rfl, weak _ ?_⟩
      have hk1 : 1 ≤ k := hko.pos
      have hlt : p ^ (k - 1) < p ^ k := Nat.pow_lt_pow_right hp.one_lt (by omega)
      have hN0 : (p ^ k).choose (p ^ (k - 1)) ≠ 0 := (Nat.choose_pos hlt.le).ne'
      have hf := fact_choose_prime_pow hp k hk1
      have hNd : (p ^ k).choose (p ^ (k - 1)) = p * ((p ^ k).choose (p ^ (k - 1)) / p) := by
        have := Nat.ordProj_mul_ordCompl_eq_self ((p ^ k).choose (p ^ (k - 1))) p
        rw [hf, pow_one] at this
        exact this.symm
      have hNp : ¬ p ∣ (p ^ k).choose (p ^ (k - 1)) / p := by
        have := Nat.not_dvd_ordCompl hp hN0
        rwa [hf, pow_one] at this
      have hb := hbin (p ^ (k - 1)) (p ^ k - p ^ (k - 1)) (Nat.one_le_pow _ _ hp.pos) (Nat.sub_pos_of_lt hlt)
      have hs : p ^ (k - 1) + (p ^ k - p ^ (k - 1)) = p ^ k := Nat.add_sub_cancel' hlt.le
      rw [hs, hNd, Nat.cast_mul, norm_mul, norm_nat_eq_one hp hp1 _ hNp, mul_one] at hb
      exact hb
  · left
    apply strong
    have hm2 : 2 ≤ m := by omega
    have hj : 1 ≤ p ^ k * (m - 1) := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (pow_ne_zero _ hp.ne_zero) (by omega))
    have hb := hbin (p ^ k) (p ^ k * (m - 1)) hpk hj
    have hs : p ^ k + p ^ k * (m - 1) = n := by
      rw [← hnm]
      conv_rhs => rw [show m = 1 + (m - 1) by omega]
      ring
    have hch : ¬ p ∣ n.choose (p ^ k) := by
      rw [← hnm]
      intro hd
      have h := choose_pow_mul_modEq hp k m
      unfold Nat.ModEq at h
      rw [Nat.dvd_iff_mod_eq_zero] at hd
      exact hm (Nat.dvd_of_mod_eq_zero (by omega))
    rw [hs, norm_nat_eq_one hp hp1 _ hch, one_mul] at hb
    exact hb
end Formalism.ELL.Lemma2Aux
