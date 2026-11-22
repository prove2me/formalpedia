-- Prove2me | solution 1 for Formalism.HermitianLattices.GenusMassVolumes.log_l_value_field_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:02:01.901736+00:00
-- url     : https://prove2.me/submissions/a639d964-83ef-4d5c-a70f-b23abc17bbb7

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_RankMulPowThreeHalvesLeFourthPower
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SumWeightsOverPrimeLeHalfDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.HermitianLattices.GenusMassVolumes
open Finset NumberField
open Formalism.LogVandermondeBounds.StandardLattice
section alg
variable (K : Type) [Field K] [NumberField K]
private lemma maximal_ideal_ne_bot (P : Ideal (𝓞 K)) (hP : P.IsMaximal) : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (NumberField.RingOfIntegers.not_isField K)
private lemma residue_characteristic_prime (P : Ideal (𝓞 K)) (hP : P.IsMaximal) : (residueCharacteristic K P).Prime := by
  haveI : P.IsMaximal := hP
  haveI : Finite (𝓞 K ⧸ P) := Nat.finite_of_card_ne_zero (by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ne, Ideal.absNorm_eq_zero_iff]
    exact maximal_ideal_ne_bot K P hP)
  letI : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite _
  letI := Ideal.Quotient.field P
  unfold residueCharacteristic
  exact (CharP.char_is_prime_or_zero (𝓞 K ⧸ P) (ringChar (𝓞 K ⧸ P))).resolve_right
    (CharP.char_ne_zero_of_finite (𝓞 K ⧸ P) (ringChar (𝓞 K ⧸ P)))
private lemma residue_characteristic_mem (P : Ideal (𝓞 K)) : ((residueCharacteristic K P : ℕ) : 𝓞 K) ∈ P := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.Nat.cast_ringChar
private lemma prod_norm_dvd_prime_pow_degree (p : ℕ) (T : Finset (Ideal (𝓞 K)))
    (hT : ∀ P ∈ T, P.IsMaximal ∧ (p : 𝓞 K) ∈ P) :
    ∏ P ∈ T, Ideal.absNorm P ∣ p ^ Module.finrank ℚ K := by
  classical
  have hdvd : (∏ P ∈ T, P) ∣ Ideal.span {(p : 𝓞 K)} := by
    apply Finset.prod_dvd_of_coprime
    · intro P hP Q hQ hPQ
      exact Ideal.isCoprime_iff_sup_eq.mpr (Ideal.IsMaximal.coprime_of_ne (hT P hP).1 (hT Q hQ).1 hPQ)
    · intro P hP
      try dsimp only
      rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]
      exact (hT P hP).2
  have h3 : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p ^ Module.finrank ℚ K := by
    rw [Ideal.absNorm_span_singleton]
    have : (p : 𝓞 K) = algebraMap ℤ (𝓞 K) (p : ℤ) := by simp
    rw [this, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank]
    simp [Int.natAbs_pow]
  have := map_dvd Ideal.absNorm hdvd
  rwa [map_prod, h3] at this
private lemma abs_norm_eq_prime_pow (P : Ideal (𝓞 K)) (hP : P.IsMaximal) :
    ∃ k, 1 ≤ k ∧ Ideal.absNorm P = residueCharacteristic K P ^ k := by
  haveI : P.IsMaximal := hP
  letI := Ideal.Quotient.field P
  haveI : Finite (𝓞 K ⧸ P) := Nat.finite_of_card_ne_zero (by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ne, Ideal.absNorm_eq_zero_iff]
    exact maximal_ideal_ne_bot K P hP)
  letI : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite _
  haveI : CharP (𝓞 K ⧸ P) (residueCharacteristic K P) := ringChar.charP _
  obtain ⟨n, -, hn⟩ := FiniteField.card (𝓞 K ⧸ P) (residueCharacteristic K P)
  refine ⟨n, n.one_le, ?_⟩
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card, hn]
private lemma exists_int_congruent_mod_prime (P : Ideal (𝓞 K)) (p : ℕ) (hp : p.Prime) (hN : Ideal.absNorm P = p)
    (x : 𝓞 K) : ∃ n : ℤ, x - (n : 𝓞 K) ∈ P := by
  have hne : P ≠ ⊥ := by
    intro h; rw [h, Ideal.absNorm_bot] at hN; exact hp.ne_zero hN.symm
  have hPr : P.IsPrime := Ideal.isPrime_of_irreducible_absNorm (by rw [hN]; exact hp)
  have hM : P.IsMaximal := hPr.isMaximal hne
  obtain ⟨k, hk1, hk⟩ := abs_norm_eq_prime_pow K P hM
  rw [hN] at hk
  have hpr : residueCharacteristic K P = p := ((Nat.Prime.pow_eq_iff hp).mp hk.symm).1
  haveI : CharP (𝓞 K ⧸ P) p := by rw [← hpr]; exact ringChar.charP _
  haveI : Fact p.Prime := ⟨hp⟩
  letI := Ideal.Quotient.field P
  haveI : Finite (𝓞 K ⧸ P) := Nat.finite_of_card_ne_zero (by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ne, Ideal.absNorm_eq_zero_iff]
    exact hne)
  letI : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite _
  have hinj : Function.Injective (ZMod.castHom (dvd_refl p) (𝓞 K ⧸ P)) :=
    (ZMod.castHom (dvd_refl p) (𝓞 K ⧸ P)).injective
  have hcard : Nat.card (𝓞 K ⧸ P) ≤ Nat.card (ZMod p) := by
    rw [Nat.card_zmod, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, hN]
  obtain ⟨z, hz⟩ := (hinj.bijective_of_nat_card_le hcard).2 (Ideal.Quotient.mk P x)
  refine ⟨(z.val : ℤ), ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← hz, map_intCast, Int.cast_natCast, ZMod.castHom_apply,
    ZMod.natCast_val, sub_self]
variable [StarRing K]
private lemma inert_prime_norm_ge_sq (P : Ideal (𝓞 K)) (hP : P.IsMaximal)
    (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P)
    (hu : ∃ θ t : 𝓞 K, algebraMap (𝓞 K) K t = star (algebraMap (𝓞 K) K θ) ∧ θ - t ∉ P) :
    residueCharacteristic K P ^ 2 ≤ Ideal.absNorm P := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨θ, t, ht, hθt⟩ := hu
  obtain ⟨k, hk1, hk⟩ := abs_norm_eq_prime_pow K P hP
  have hp := residue_characteristic_prime K P hP
  have hk2 : k = 1 := by
    by_contra hne
    have h2k : 2 ≤ k := by omega
    have := Nat.pow_le_pow_right hp.pos h2k
    rw [← hk] at this
    exact absurd this (not_le.mpr hlt)
  rw [hk2, pow_one] at hk
  obtain ⟨n, hn⟩ := exists_int_congruent_mod_prime K P _ hp hk θ
  apply hθt
  have h2 : t - (n : 𝓞 K) ∈ Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by
    apply Ideal.subset_span
    refine ⟨θ - n, hn, ?_⟩
    rw [map_sub, map_sub, ht, star_sub, map_intCast, star_intCast]
  rw [hc] at h2
  have := P.sub_mem hn h2
  rwa [sub_sub_sub_cancel_right] at this
end alg
section ana
private lemma summable_inv_pow_real (M : ℕ) (hM : 2 ≤ M) : Summable (fun n : ℕ => ((n : ℝ)⁻¹) ^ M) := by
  have := Real.summable_nat_pow_inv.mpr (by omega : 1 < M)
  simpa [inv_pow] using this
private lemma tsum_inv_pow_eq_zeta_real (M : ℕ) (hM : 2 ≤ M) : ∑' n : ℕ, ((n : ℝ)⁻¹) ^ M = zetaR M := by
  rw [(summable_inv_pow_real M hM).tsum_eq_zero_add]
  rw [Nat.cast_zero, inv_zero, zero_pow (by omega), zero_add]
  show _ = ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ M
  congr 1
  ext n
  push_cast
  rw [one_div, inv_pow]
private lemma inv_prime_pow_lt_one' (M : ℕ) (hM : 1 ≤ M) (p : ℕ) (hp : p.Prime) :
    ((p : ℝ)⁻¹) ^ M < 1 := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have h1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  exact pow_lt_one₀ (by positivity) h1 (by omega)
private lemma euler_product_le_zeta (M : ℕ) (hM : 2 ≤ M) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∏ p ∈ S, (1 - ((p : ℝ)⁻¹) ^ M)⁻¹ ≤ zetaR M := by
  classical
  have hfv : ∀ n : ℕ, invPowMonoidHomReal M n = ((n : ℝ)⁻¹) ^ M := fun n => rfl
  set N := S.sup id + 1 with hNdef
  have hsub : S ⊆ N.primesBelow := by
    intro p hp
    rw [Nat.mem_primesBelow]
    exact ⟨Nat.lt_succ_of_le (Finset.le_sup (f := id) hp), hS p hp⟩
  have hf : ∀ {p : ℕ}, p.Prime → ‖invPowMonoidHomReal M p‖ < 1 := by
    intro p hp
    rw [hfv, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact inv_prime_pow_lt_one' M (by omega) p hp
  obtain ⟨-, hhs⟩ := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric hf N
  have hsum : Summable (fun n : ℕ => invPowMonoidHomReal M n) := by
    simp only [hfv]; exact summable_inv_pow_real M hM
  have key : ∏ p ∈ N.primesBelow, (1 - invPowMonoidHomReal M p)⁻¹ ≤ ∑' n : ℕ, invPowMonoidHomReal M n := by
    rw [← hhs.tsum_eq]
    exact Summable.tsum_subtype_le (fun n : ℕ => invPowMonoidHomReal M n) _ (fun n => by rw [hfv]; positivity) hsum
  have hfac : ∀ p ∈ N.primesBelow, 1 ≤ (1 - invPowMonoidHomReal M p)⁻¹ := by
    intro p hp
    have hp' := (Nat.mem_primesBelow.mp hp).2
    have h1 := inv_prime_pow_lt_one' M (by omega) p hp'
    have h0 : 0 ≤ ((p : ℝ)⁻¹) ^ M := by positivity
    rw [hfv]
    exact (one_le_inv₀ (by linarith)).mpr (by linarith)
  have hsplit := Finset.prod_sdiff hsub (f := fun p => (1 - invPowMonoidHomReal M p)⁻¹)
  have hrest : 1 ≤ ∏ p ∈ N.primesBelow \ S, (1 - invPowMonoidHomReal M p)⁻¹ :=
    Finset.prod_induction _ (fun x => 1 ≤ x) (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb)
      le_rfl (fun p hp => hfac p (Finset.sdiff_subset hp))
  have hSpos : 0 ≤ ∏ p ∈ S, (1 - invPowMonoidHomReal M p)⁻¹ :=
    Finset.prod_nonneg (fun p hp => by linarith [hfac p (hsub hp)])
  calc ∏ p ∈ S, (1 - ((p : ℝ)⁻¹) ^ M)⁻¹ = ∏ p ∈ S, (1 - invPowMonoidHomReal M p)⁻¹ := rfl
    _ ≤ (∏ p ∈ N.primesBelow \ S, (1 - invPowMonoidHomReal M p)⁻¹) * ∏ p ∈ S, (1 - invPowMonoidHomReal M p)⁻¹ :=
        le_mul_of_one_le_left hSpos hrest
    _ = ∏ p ∈ N.primesBelow, (1 - invPowMonoidHomReal M p)⁻¹ := hsplit
    _ ≤ ∑' n : ℕ, invPowMonoidHomReal M n := key
    _ = zetaR M := by simp only [hfv]; exact tsum_inv_pow_eq_zeta_real M hM
private lemma inv_prime_pow_lt_one (M : ℕ) (hM : 1 ≤ M) (p : ℕ) (hp : p.Prime) : ((p : ℝ)⁻¹) ^ M < 1 := by
  exact inv_prime_pow_lt_one' M hM p hp
private lemma neg_log_one_sub_inv_pow_nonneg (M : ℕ) (hM : 1 ≤ M) (p : ℕ) (hp : p.Prime) : 0 ≤ negLogOneSubInvPow M p := by
  have h := inv_prime_pow_lt_one M hM p hp
  have h0 : 0 ≤ ((p : ℝ)⁻¹) ^ M := by positivity
  unfold negLogOneSubInvPow
  have : Real.log (1 - ((p : ℝ)⁻¹) ^ M) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  linarith
private lemma sum_neg_log_le_log_zeta (M : ℕ) (hM : 2 ≤ M) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∑ p ∈ S, negLogOneSubInvPow M p ≤ Real.log (zetaR M) := by
  have hpos : ∀ p ∈ S, 0 < 1 - ((p : ℝ)⁻¹) ^ M := fun p hp => by
    linarith [inv_prime_pow_lt_one M (by omega) p (hS p hp)]
  have hsum : ∑ p ∈ S, negLogOneSubInvPow M p = Real.log (∏ p ∈ S, (1 - ((p : ℝ)⁻¹) ^ M)⁻¹) := by
    rw [Real.log_prod (fun p hp => (inv_pos.mpr (hpos p hp)).ne')]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [negLogOneSubInvPow, Real.log_inv]
  rw [hsum]
  exact Real.log_le_log (Finset.prod_pos (fun p hp => inv_pos.mpr (hpos p hp))) (euler_product_le_zeta M hM S hS)
private lemma abs_log_inv_one_sub_le_real (s y x : ℝ) (hs : s = 1 ∨ s = -1) (hy : 0 ≤ y) (hyx : y ≤ x) (hx : x < 1) :
    |Real.log ((1 - s * y)⁻¹)| ≤ -Real.log (1 - x) := by
  have hx0 : 0 < 1 - x := by linarith
  rcases hs with rfl | rfl
  · rw [one_mul, Real.log_inv, abs_neg, abs_of_nonpos (Real.log_nonpos (by linarith) (by linarith))]
    have := Real.log_le_log hx0 (by linarith : 1 - x ≤ 1 - y)
    linarith
  · rw [neg_one_mul, sub_neg_eq_add, Real.log_inv, abs_neg,
      abs_of_nonneg (Real.log_nonneg (by linarith))]
    have h1 := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + y)
    have h2 := Real.log_le_sub_one_of_pos hx0
    linarith
private lemma euler_factor_inert_prime_bound (M : ℕ) (hM : 1 ≤ M) (p : ℕ) (hp : p.Prime) (N : ℕ) (hN : p ^ 2 ≤ N) :
    0 < (1 - (-1 : ℝ) ^ M * (Real.sqrt (N : ℝ)) ^ (-(M : ℤ)))⁻¹ ∧
    |Real.log ((1 - (-1 : ℝ) ^ M * (Real.sqrt (N : ℝ)) ^ (-(M : ℤ)))⁻¹)| ≤ negLogOneSubInvPow M p := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hsq : (p : ℝ) ^ 2 ≤ (N : ℝ) := by exact_mod_cast hN
  have hpN : (p : ℝ) ≤ Real.sqrt (N : ℝ) := (le_abs_self _).trans (Real.abs_le_sqrt hsq)
  have hzp : (Real.sqrt (N : ℝ)) ^ (-(M : ℤ)) = ((Real.sqrt (N : ℝ))⁻¹) ^ M := by
    rw [zpow_neg, zpow_natCast, inv_pow]
  have hy0 : 0 ≤ ((Real.sqrt (N : ℝ))⁻¹) ^ M := by positivity
  have hyx : ((Real.sqrt (N : ℝ))⁻¹) ^ M ≤ ((p : ℝ)⁻¹) ^ M :=
    pow_le_pow_left₀ (by positivity) (inv_anti₀ (by linarith) hpN) M
  have hx := inv_prime_pow_lt_one M hM p hp
  have hs := neg_one_pow_eq_or ℝ M
  rw [hzp]
  refine ⟨?_, abs_log_inv_one_sub_le_real _ _ _ hs hy0 hyx hx⟩
  apply inv_pos.mpr
  rcases hs with h | h <;> rw [h] <;> linarith
private lemma euler_factor_split_prime_bound (M : ℕ) (hM : 1 ≤ M) (p : ℕ) (hp : p.Prime) (N : ℕ) (hN : p ≤ N) :
    0 < (1 - (N : ℝ) ^ (-(M : ℤ))) ^ (-(1 : ℝ) / 2) ∧
    |Real.log ((1 - (N : ℝ) ^ (-(M : ℤ))) ^ (-(1 : ℝ) / 2))| ≤ 1 / 2 * negLogOneSubInvPow M p := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpN : (p : ℝ) ≤ N := by exact_mod_cast hN
  have hzp : (N : ℝ) ^ (-(M : ℤ)) = ((N : ℝ)⁻¹) ^ M := by rw [zpow_neg, zpow_natCast, inv_pow]
  rw [hzp]
  have hyx : ((N : ℝ)⁻¹) ^ M ≤ ((p : ℝ)⁻¹) ^ M :=
    pow_le_pow_left₀ (by positivity) (inv_anti₀ (by linarith) hpN) M
  have hy0 : 0 ≤ ((N : ℝ)⁻¹) ^ M := by positivity
  have hx := inv_prime_pow_lt_one M hM p hp
  have hb : 0 < 1 - ((N : ℝ)⁻¹) ^ M := by linarith
  refine ⟨Real.rpow_pos_of_pos hb _, ?_⟩
  rw [Real.log_rpow hb, abs_mul]
  have hl := abs_log_inv_one_sub_le_real 1 _ _ (Or.inl rfl) hy0 hyx hx
  rw [one_mul, Real.log_inv, abs_neg] at hl
  have h12 : |(-(1 : ℝ) / 2)| = 1 / 2 := by norm_num
  rw [h12]
  unfold negLogOneSubInvPow
  linarith
end ana
section main
variable (K : Type) [Field K] [NumberField K]
private lemma log_prime_pos (p : ℕ) (hp : p.Prime) : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
private lemma sum_weights_over_prime_le_half_degree (p : ℕ) (T : Finset {P : Ideal (𝓞 K) // P.IsMaximal})
    (hT : ∀ P ∈ T, residueCharacteristic K P.1 = p) :
    ∑ P ∈ T, idealPrimeWeight K P.1 ≤ (Module.finrank ℚ K : ℝ) / 2 := by
  classical
  rcases T.eq_empty_or_nonempty with rfl | ⟨P0, hP0⟩
  · simp only [Finset.sum_empty]; positivity
  have hp : p.Prime := by rw [← hT P0 hP0]; exact residue_characteristic_prime K P0.1 P0.2
  have hlp := log_prime_pos p hp
  have hdvd : ∏ P ∈ T, Ideal.absNorm P.1 ∣ p ^ Module.finrank ℚ K := by
    have := prod_norm_dvd_prime_pow_degree K p (T.map (Function.Embedding.subtype _)) (by
      intro P hP
      obtain ⟨Q, hQ, rfl⟩ := Finset.mem_map.mp hP
      refine ⟨Q.2, ?_⟩
      have := residue_characteristic_mem K Q.1
      rwa [hT Q hQ] at this)
    simpa [Finset.prod_map] using this
  have hpos : ∀ P ∈ T, 0 < Ideal.absNorm P.1 := fun P _ => Nat.pos_of_ne_zero (by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact maximal_ideal_ne_bot K P.1 P.2)
  have hle : ∏ P ∈ T, Ideal.absNorm P.1 ≤ p ^ Module.finrank ℚ K :=
    Nat.le_of_dvd (pow_pos hp.pos _) hdvd
  have hlog : ∑ P ∈ T, Real.log (Ideal.absNorm P.1 : ℝ) ≤ Module.finrank ℚ K * Real.log p := by
    rw [← Real.log_prod (fun P hP => by exact_mod_cast (hpos P hP).ne'), ← Real.log_pow]
    apply Real.log_le_log (Finset.prod_pos fun P hP => by exact_mod_cast hpos P hP)
    exact_mod_cast hle
  have hlne := hlp.ne'
  calc ∑ P ∈ T, idealPrimeWeight K P.1 = ∑ P ∈ T, Real.log (Ideal.absNorm P.1 : ℝ) / (2 * Real.log p) :=
        Finset.sum_congr rfl (fun P hP => by rw [idealPrimeWeight, hT P hP])
    _ = (∑ P ∈ T, Real.log (Ideal.absNorm P.1 : ℝ)) / (2 * Real.log p) := by rw [Finset.sum_div]
    _ ≤ (Module.finrank ℚ K * Real.log p) / (2 * Real.log p) := by
        apply div_le_div_of_nonneg_right hlog; linarith
    _ = (Module.finrank ℚ K : ℝ) / 2 := by field_simp; try ring
variable [StarRing K]
private lemma euler_factor_log_bound (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (M : ℕ) (hM : 1 ≤ M) (P : Ideal (𝓞 K))
    (hP : P.IsMaximal) :
    0 < Formalism.HermitianLatticesTheory.eulerFac K M P ∧
    |Real.log (Formalism.HermitianLatticesTheory.eulerFac K M P)| ≤ idealPrimeWeight K P * negLogOneSubInvPow M (residueCharacteristic K P) := by
  have hp := residue_characteristic_prime K P hP
  obtain ⟨k, hk1, hk⟩ := abs_norm_eq_prime_pow K P hP
  have hlp := log_prime_pos _ hp
  have hlne := hlp.ne'
  have hc : idealPrimeWeight K P = (k : ℝ) / 2 := by
    rw [idealPrimeWeight, hk, Nat.cast_pow, Real.log_pow]; field_simp; try ring
  have hg := neg_log_one_sub_inv_pow_nonneg M hM _ hp
  unfold Formalism.HermitianLatticesTheory.eulerFac
  split_ifs with hconj
  · have hN := inert_prime_norm_ge_sq K P hP hconj (hK.2.2 P hP)
    obtain ⟨h1, h2⟩ := euler_factor_inert_prime_bound M hM _ hp _ hN
    refine ⟨h1, h2.trans ?_⟩
    have hk2 : 2 ≤ k := by
      by_contra h
      have h1k : k = 1 := by omega
      rw [hk, h1k, pow_one] at hN
      have := hp.two_le
      nlinarith
    rw [hc]
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk2
    nlinarith
  · obtain ⟨h1, h2⟩ := euler_factor_split_prime_bound M hM _ hp (Ideal.absNorm P) (by rw [hk]; exact Nat.le_self_pow (by omega) _)
    refine ⟨h1, h2.trans ?_⟩
    rw [hc]
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    nlinarith
private lemma partial_sums_log_euler_factor_le (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (M : ℕ) (hM : 2 ≤ M)
    (u : Finset {P : Ideal (𝓞 K) // P.IsMaximal}) :
    ∑ P ∈ u, |Real.log (Formalism.HermitianLatticesTheory.eulerFac K M P.1)| ≤
      (Formalism.HermitianLatticesTheory.fDeg K : ℝ) * Real.log (zetaR M) := by
  classical
  have hn : (Formalism.HermitianLatticesTheory.fDeg K : ℝ) = (Module.finrank ℚ K : ℝ) / 2 := by
    haveI := hK.1
    have h1 := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
    have h2 := NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K
    have h3 := NumberField.IsTotallyComplex.nrRealPlaces_eq_zero K
    unfold Formalism.HermitianLatticesTheory.fDeg
    rw [h2, ← h1, h3]; push_cast; ring
  set S := u.image (fun P => residueCharacteristic K P.1) with hSdef
  have hSp : ∀ p ∈ S, p.Prime := by
    intro p hp
    obtain ⟨P, -, rfl⟩ := Finset.mem_image.mp hp
    exact residue_characteristic_prime K P.1 P.2
  calc ∑ P ∈ u, |Real.log (Formalism.HermitianLatticesTheory.eulerFac K M P.1)|
      ≤ ∑ P ∈ u, idealPrimeWeight K P.1 * negLogOneSubInvPow M (residueCharacteristic K P.1) :=
        Finset.sum_le_sum (fun P _ => (euler_factor_log_bound K hK M (by omega) P.1 P.2).2)
    _ = ∑ p ∈ S, ∑ P ∈ u.filter (fun P => residueCharacteristic K P.1 = p),
          idealPrimeWeight K P.1 * negLogOneSubInvPow M (residueCharacteristic K P.1) :=
        (Finset.sum_fiberwise_of_maps_to (fun P hP => Finset.mem_image_of_mem _ hP) _).symm
    _ = ∑ p ∈ S, negLogOneSubInvPow M p * ∑ P ∈ u.filter (fun P => residueCharacteristic K P.1 = p), idealPrimeWeight K P.1 := by
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun P hP => ?_)
        rw [(Finset.mem_filter.mp hP).2]; ring
    _ ≤ ∑ p ∈ S, negLogOneSubInvPow M p * ((Module.finrank ℚ K : ℝ) / 2) := by
        refine Finset.sum_le_sum (fun p hp => ?_)
        exact mul_le_mul_of_nonneg_left
          (sum_weights_over_prime_le_half_degree K p _ (fun P hP => (Finset.mem_filter.mp hP).2))
          (neg_log_one_sub_inv_pow_nonneg M (by omega) p (hSp p hp))
    _ = (Module.finrank ℚ K : ℝ) / 2 * ∑ p ∈ S, negLogOneSubInvPow M p := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
    _ ≤ (Module.finrank ℚ K : ℝ) / 2 * Real.log (zetaR M) :=
        mul_le_mul_of_nonneg_left (sum_neg_log_le_log_zeta M hM S hSp) (by positivity)
    _ = (Formalism.HermitianLatticesTheory.fDeg K : ℝ) * Real.log (zetaR M) := by rw [hn]
end main
end Formalism.HermitianLattices.GenusMassVolumes
end

set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GenusMassVolumes
open Finset NumberField
open Formalism.LogVandermondeBounds.StandardLattice
namespace Formalism.HermitianLattices.GenusMassVolumes
theorem _root_.solution : LogLFunctionEulerBound := by
  intro K _ _ _ hK M hM
  have hM2 : 2 ≤ M := by omega
  have hpos : ∀ P : {P : Ideal (𝓞 K) // P.IsMaximal}, 0 < Formalism.HermitianLatticesTheory.eulerFac K M P.1 :=
    fun P => (euler_factor_log_bound K hK M (by omega) P.1 P.2).1
  have habs : Summable
      (fun P : {P : Ideal (𝓞 K) // P.IsMaximal} => |Real.log (Formalism.HermitianLatticesTheory.eulerFac K M P.1)|) :=
    summable_of_sum_le (fun P => abs_nonneg _) (partial_sums_log_euler_factor_le K hK M hM2)
  have hsum : Summable
      (fun P : {P : Ideal (𝓞 K) // P.IsMaximal} => Real.log (Formalism.HermitianLatticesTheory.eulerFac K M P.1)) :=
    habs.of_abs
  refine ⟨Real.multipliable_of_summable_log hpos hsum, ?_, ?_⟩
  · unfold Formalism.HermitianLatticesTheory.lValEta
    rw [← Real.rexp_tsum_eq_tprod hpos hsum]
    exact Real.exp_pos _
  · unfold Formalism.HermitianLatticesTheory.lValEta
    rw [← Real.rexp_tsum_eq_tprod hpos hsum, Real.log_exp]
    have hn := norm_tsum_le_tsum_norm
      (f := fun P : {P : Ideal (𝓞 K) // P.IsMaximal} => Real.log (Formalism.HermitianLatticesTheory.eulerFac K M P.1))
      (by simpa [Real.norm_eq_abs] using habs)
    simp only [Real.norm_eq_abs] at hn
    exact hn.trans (habs.tsum_le_of_sum_le (partial_sums_log_euler_factor_le K hK M hM2))
end Formalism.HermitianLattices.GenusMassVolumes
