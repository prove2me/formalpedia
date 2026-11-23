-- Prove2me | solution 1 for DedekindZeta.dedekindZeta_eq_tsum_absNorm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:17:44.277786+00:00
-- url     : https://prove2.me/submissions/498a0695-55ea-45d4-821f-1b8cdcd06e90

import Mathlib
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_Statements
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
attribute [local simp] DedekindZeta.Theta.gaussVSchwartz_apply
attribute [local simp] DedekindZeta.Theta.mixedGaussianSchwartz_apply



set_option autoImplicit true
open NumberField NumberField.InfinitePlace IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open Filter Finset Asymptotics Topology
open scoped Real nonZeroDivisors
open DedekindZeta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
namespace DedekindZeta
theorem _root_.solution {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta K s =
      ∑' 𝔞 : NonzeroIdeal K, (Ideal.absNorm (𝔞 : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
  classical
  -- the ideal-counting coefficient
  set g : ℕ → ℂ := fun n ↦ (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ) with hg
  set φ : NonzeroIdeal K → ℕ := fun 𝔞 ↦ Ideal.absNorm (𝔞 : Ideal (𝓞 K)) with hφ
  set h : NonzeroIdeal K → ℂ := fun 𝔞 ↦ (φ 𝔞 : ℂ) ^ (-s) with hh
  set e := Equiv.sigmaFiberEquiv φ with he
  -- finiteness of fibres
  have hfin : ∀ n : ℕ, Finite {a : NonzeroIdeal K // φ a = n} := by
    intro n
    haveI : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
      (Ideal.finite_setOf_absNorm_eq n).to_subtype
    apply Finite.of_injective
      (f := fun c : {a : NonzeroIdeal K // φ a = n} ↦
        (⟨(c.1 : Ideal (𝓞 K)), c.2⟩ : {I : Ideal (𝓞 K) // Ideal.absNorm I = n}))
    intro a b hab
    have : (a.1 : Ideal (𝓞 K)) = (b.1 : Ideal (𝓞 K)) := by
      simpa using congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext this)
  -- card of a fibre over nonzero ideals = card of all ideals of that norm (for n ≠ 0)
  have hcard : ∀ n : ℕ, n ≠ 0 →
      Nat.card {a : NonzeroIdeal K // φ a = n}
        = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} := by
    intro n hn
    refine Nat.card_congr ?_
    refine
      { toFun := fun c ↦ ⟨(c.1 : Ideal (𝓞 K)), c.2⟩
        invFun := fun d ↦ ⟨⟨d.1, ?_⟩, d.2⟩
        left_inv := ?_
        right_inv := ?_ }
    · intro hI0
      apply hn
      have : Ideal.absNorm d.1 = 0 := by rw [hI0]; simp
      rw [← d.2, this]
    · intro c; exact Subtype.ext (Subtype.ext rfl)
    · intro d; exact Subtype.ext rfl
  -- partial-sum identity
  have hpart : ∀ n : ℕ,
      ∑ k ∈ Finset.Icc 1 n, Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k}
        = Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ n} := by
    intro n
    rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
      show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
      show 1 = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} by
        simp [Ideal.absNorm_eq_zero_iff],
      Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
      ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ ↦ Ideal.finite_setOf_absNorm_eq k)]
    simp [Set.coe_eq_subtype]
  -- real coefficient and the big-O bound on partial sums
  set gℝ : ℕ → ℝ := fun n ↦ (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) with hgℝ
  have hbigO : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, gℝ k) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ) := by
    have H := (Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop
    have h2 := (H.isBigO_one ℝ).mul (isBigO_refl (fun n : ℕ ↦ (n : ℝ)) atTop)
    refine h2.congr' ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with n hn
      simp only [Function.comp_apply]
      rw [div_mul_cancel₀ _ (by exact_mod_cast hn.ne')]
      rw [hgℝ, ← Nat.cast_sum, hpart n]
      congr 1
      exact (Nat.card_congr (Equiv.subtypeEquivRight (fun I ↦ by exact_mod_cast Iff.rfl))).symm
    · filter_upwards [eventually_ge_atTop 0] with n hn
      rw [one_mul, Real.rpow_one]
  have hLS : LSeriesSummable g s := by
    have hsum := LSeriesSummable_of_sum_norm_bigO_and_nonneg (f := gℝ)
      hbigO (fun n ↦ Nat.cast_nonneg _) zero_le_one hs
    refine (LSeriesSummable_congr s (fun {n} _ ↦ ?_)).mp hsum
    simp [hgℝ, hg]
  have hnorm : Summable (fun n : ℕ ↦ ‖LSeries.term g s n‖) := summable_norm_iff.mpr hLS
  -- constant tsum over a finite fibre
  have hconst : ∀ (n : ℕ), n ≠ 0 → ∀ z : ℂ,
      (∑' _y : {a : NonzeroIdeal K // φ a = n}, z)
        = (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ) * z := by
    intro n hn z
    haveI := hfin n
    haveI : Fintype {a : NonzeroIdeal K // φ a = n} := Fintype.ofFinite _
    rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Nat.card_eq_fintype_card, hcard n hn]
  -- the term-by-term identity
  have hterm : ∀ n : ℕ, (∑' y : {a : NonzeroIdeal K // φ a = n}, h (e ⟨n, y⟩))
      = LSeries.term g s n := by
    intro n
    by_cases hn : n = 0
    · subst hn
      haveI : IsEmpty {a : NonzeroIdeal K // φ a = 0} := by
        refine ⟨fun a ↦ ?_⟩
        have : Ideal.absNorm (a.1 : Ideal (𝓞 K)) = 0 := a.2
        exact a.1.2 ((Ideal.absNorm_eq_zero_iff).mp this)
      simp [tsum_empty, LSeries.term_zero]
    · have hval : ∀ y : {a : NonzeroIdeal K // φ a = n}, h (e ⟨n, y⟩) = (n : ℂ) ^ (-s) := by
        intro y
        have : e ⟨n, y⟩ = y.1 := rfl
        rw [this, hh]
        simp only
        rw [y.2]
      rw [tsum_congr hval, hconst n hn]
      rw [LSeries.term_of_ne_zero hn, hg]
      simp only
      rw [Complex.cpow_neg, div_eq_mul_inv]
  -- summability of h via the real majorant
  have hsumH : Summable h := by
    apply Summable.of_norm
    have hnormeq : ∀ 𝔞 : NonzeroIdeal K, ‖h 𝔞‖ = (φ 𝔞 : ℝ) ^ (-s.re) := by
      intro 𝔞
      have hpos : 0 < φ 𝔞 := by
        rw [hφ]; simp only
        exact Nat.pos_of_ne_zero (fun hz ↦ 𝔞.2 ((Ideal.absNorm_eq_zero_iff).mp hz))
      rw [hh]; simp only
      rw [Complex.norm_natCast_cpow_of_pos hpos, Complex.neg_re]
    rw [funext hnormeq]
    refine (Equiv.summable_iff e).mp ?_
    change Summable fun p : (Sigma fun n => {a : NonzeroIdeal K // φ a = n}) =>
      (φ (e p) : ℝ) ^ (-s.re)
    rw [summable_sigma_of_nonneg (fun p ↦ Real.rpow_nonneg (by positivity) _)]
    refine ⟨fun n ↦ ?_, ?_⟩
    · haveI := hfin n
      exact Summable.of_finite
    · refine hnorm.congr (fun n ↦ ?_)
      by_cases hn : n = 0
      · subst hn
        haveI : IsEmpty {a : NonzeroIdeal K // φ a = 0} := by
          refine ⟨fun a ↦ ?_⟩
          have : Ideal.absNorm (a.1 : Ideal (𝓞 K)) = 0 := a.2
          exact a.1.2 ((Ideal.absNorm_eq_zero_iff).mp this)
        simp [tsum_empty, LSeries.term_zero]
      · have hval : ∀ y : {a : NonzeroIdeal K // φ a = n},
            (fun p : (Sigma fun n => {a : NonzeroIdeal K // φ a = n}) =>
              (φ (e p) : ℝ) ^ (-s.re)) ⟨n, y⟩ = (n : ℝ) ^ (-s.re) := by
          intro y; simp only; rw [show e ⟨n, y⟩ = y.1 from rfl, y.2]
        rw [tsum_congr hval]
        haveI := hfin n
        haveI : Fintype {a : NonzeroIdeal K // φ a = n} := Fintype.ofFinite _
        rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          ← Nat.card_eq_fintype_card, hcard n hn]
        rw [LSeries.norm_term_eq, if_neg hn, hg]
        simp only [Complex.norm_natCast, Real.rpow_neg (Nat.cast_nonneg _)]
        rw [div_eq_mul_inv]
  -- assemble
  have hsig : Summable (fun p : (Sigma fun n => {a : NonzeroIdeal K // φ a = n}) => h (e p)) :=
    (Equiv.summable_iff e).mpr hsumH
  have key : (∑' 𝔞 : NonzeroIdeal K, h 𝔞) = ∑' n, LSeries.term g s n := by
    rw [← Equiv.tsum_eq e h,
      hsig.tsum_sigma' (fun n => by haveI := hfin n; exact Summable.of_finite)]
    exact tsum_congr hterm
  rw [NumberField.dedekindZeta, LSeries, ← key]
end DedekindZeta
