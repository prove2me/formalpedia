-- Prove2me | solution 1 for FiniteFields.Dwork.norm_artinHasseEvalAt_eta_sub_one_le
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-10-20T06:57:12.953982+00:00
-- url     : https://prove2.me/submissions/40e262be-88a8-462e-b087-e2a015f990b5

import Mathlib
import Definitions.Def_FiniteFields_Dwork_AdditiveCharacter
import Theorems.Thm_FiniteFields_Dwork_dworkPowerSeriesEval_rescale
section
noncomputable section
open Filter Function IsUltrametricDist Metric PowerSeries Set
open scoped NNReal Topology
namespace FiniteFields.Dwork
variable (k : Type*) [Field k]
variable (p : ℕ) [Fact p.Prime] [CharP k p] [Finite k]
theorem dworkSplittingFunction_coeff (n : ℕ) :
    PowerSeries.coeff n (dworkSplittingFunction k p) =
      dworkArtinHasseParameter k p ^ n *
        PowerSeries.coeff n (dworkArtinHasseExponential k p) := by
  rw [dworkSplittingFunction, PowerSeries.coeff_rescale]
@[simp]
theorem dworkSplittingFunction_constantCoeff :
    PowerSeries.constantCoeff (dworkSplittingFunction k p) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    dworkSplittingFunction_coeff]
  simp [dworkArtinHasseExponential, PowerSeries.coeff_map]
end FiniteFields.Dwork
end
end
section
noncomputable section
open PowerSeries
open scoped Classical
namespace FiniteFields.Dwork
section Product
variable {R K : Type*} [CommRing R] [CommRing K] [Algebra ℚ K] (ι : R →+* K) (p : ℕ)
  [Fact p.Prime] (hR : ∀ n, coeff n (artinHasseSeries K p) ∈ Set.range ι)
theorem artinHasseFactor_index_zero (a : R) :
    artinHasseFactor ι p hR a 0 = PowerSeries.rescale a (artinHasseOver ι p hR) := by
  ext n
  rw [artinHasseFactor, PowerSeries.coeff_expand, pow_zero]
  simp
theorem artinHasseWittSeries_teichmuller (hι : Function.Injective ι) {N : ℕ} (hN : 0 < N)
    (a : R) :
    artinHasseWittSeries ι p hR N (WittVector.teichmuller p a)
      = PowerSeries.rescale a (artinHasseOver ι p hR) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  rw [artinHasseWittSeries, Finset.prod_range_succ']
  rw [Finset.prod_eq_one, one_mul, WittVector.teichmuller_coeff_zero,
    artinHasseFactor_index_zero]
  intro i _
  rw [WittVector.teichmuller_coeff_pos p a (i + 1) (Nat.succ_pos i),
    artinHasseFactor_of_zero ι p hR hι]
theorem coeff_artinHasseFactor (a : R) (i n : ℕ) :
    coeff n (artinHasseFactor ι p hR a i)
      = if p ^ i ∣ n then a ^ (n / p ^ i) * coeff (n / p ^ i) (artinHasseOver ι p hR) else 0 := by
  rw [artinHasseFactor, PowerSeries.coeff_expand]
  split_ifs with h
  · rw [PowerSeries.coeff_rescale]
  · rfl
theorem expand_artinHasseFactor (a : R) (i : ℕ) :
    PowerSeries.expand p (Fact.out : Nat.Prime p).ne_zero (artinHasseFactor ι p hR a i)
      = artinHasseFactor ι p hR a (i + 1) := by
  ext n
  rw [PowerSeries.coeff_expand, coeff_artinHasseFactor, coeff_artinHasseFactor, pow_succ' p i]
  by_cases h1 : p ∣ n
  · rw [if_pos h1]
    simp only [Nat.dvd_div_iff_mul_dvd h1, Nat.div_div_eq_div_mul]
  · rw [if_neg h1, if_neg (fun hc => h1 (dvd_trans (Dvd.intro _ rfl) hc))]
theorem expand_artinHasseWittSeries (N : ℕ) (w : WittVector p R) (hι : Function.Injective ι) :
    PowerSeries.expand p (Fact.out : Nat.Prime p).ne_zero (artinHasseWittSeries ι p hR N w)
      = artinHasseWittSeries ι p hR (N + 1) (WittVector.verschiebung w) := by
  rw [artinHasseWittSeries, artinHasseWittSeries, map_prod, Finset.prod_range_succ']
  rw [WittVector.verschiebung_coeff_zero, artinHasseFactor_of_zero ι p hR hι, mul_one]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [WittVector.verschiebung_coeff_succ, expand_artinHasseFactor]
theorem truncatedArtinHasseProduct_teichmuller (hι : Function.Injective ι) (N : ℕ) (a : R) :
    truncatedArtinHasseProduct ι p hR hι N (WittVector.teichmuller p a)
      = TruncatedPrincipalUnit.ofSeries (PowerSeries.rescale a (artinHasseOver ι p hR))
          (constantCoeff_rescale_artinHasseOver ι p hR hι a) := by
  rw [truncatedArtinHasseProduct]
  refine (TruncatedPrincipalUnit.ofSeries_eq_ofSeries_iff _ _).mpr fun m hm => ?_
  rw [artinHasseWittSeries_teichmuller ι p hR hι (show 0 < N by omega) a]
end Product
end FiniteFields.Dwork
end
end
section
noncomputable section
open PowerSeries
namespace FiniteFields.Dwork
namespace FormalPrincipalUnit
variable {R : Type*} [CommRing R]
@[simp] theorem val_pow (a : FormalPrincipalUnit R) (n : ℕ) : (a ^ n).val = a.val ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, val_one]
  | succ n ih => rw [pow_succ, pow_succ, val_mul, ih]
end FormalPrincipalUnit
end FiniteFields.Dwork
end
end
section
noncomputable section
open PowerSeries
namespace FiniteFields.Dwork
section Formal
variable {R K : Type*} [CommRing R] [CommRing K] [Algebra ℚ K] (ι : R →+* K) (p : ℕ)
  [Fact p.Prime] (hR : ∀ n, coeff n (artinHasseSeries K p) ∈ Set.range ι)
theorem formalArtinHasseProduct_teichmuller (hι : Function.Injective ι) (a : R) :
    formalArtinHasseProduct ι p hR hι (WittVector.teichmuller p a)
      = ⟨PowerSeries.rescale a (artinHasseOver ι p hR),
          constantCoeff_rescale_artinHasseOver ι p hR hι a⟩ := by
  refine formalPrincipalUnit_ext fun N => ?_
  rw [formalArtinHasseProduct_truncate, truncatedArtinHasseProduct_teichmuller]
  rfl
theorem formalArtinHasseProduct_nsmul (hι : Function.Injective ι) (n : ℕ)
    (w : WittVector p R) :
    formalArtinHasseProduct ι p hR hι (n • w) = formalArtinHasseProduct ι p hR hι w ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero, formalArtinHasseProduct_zero]
  | succ n ih => rw [succ_nsmul, formalArtinHasseProduct_add, ih, pow_succ]
theorem formalArtinHasseProduct_verschiebung (hι : Function.Injective ι) (w : WittVector p R) :
    (formalArtinHasseProduct ι p hR hι (WittVector.verschiebung w)).val
      = PowerSeries.expand p (Fact.out : Nat.Prime p).ne_zero
          (formalArtinHasseProduct ι p hR hι w).val := by
  refine PowerSeries.ext fun m => ?_
  rw [val_formalArtinHasseProduct, val_formalArtinHasseProduct,
    coeff_formalArtinHasseSeries ι p hR hι _ (N := m + 1 + 1) (by omega),
    ← expand_artinHasseWittSeries ι p hR (m + 1) w hι,
    PowerSeries.coeff_expand, PowerSeries.coeff_expand]
  split_ifs with h
  · refine (coeff_formalArtinHasseSeries ι p hR hι w (N := m + 1) ?_).symm
    have := Nat.div_le_self m p
    omega
  · rfl
end Formal
end FiniteFields.Dwork
end
end
section
noncomputable section
open PowerSeries
namespace FiniteFields.Dwork
section Formal
theorem rescale_C {S : Type*} [CommRing S] (c x : S) :
    PowerSeries.rescale c (PowerSeries.C x) = PowerSeries.C x := by
  refine PowerSeries.ext fun n => ?_
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_C]
  split_ifs with h
  · rw [h, pow_zero, one_mul]
  · rw [mul_zero]
@[simp]
theorem constantCoeff_frobeniusQuotientSeries (K : Type*) [CommRing K] [Algebra ℚ K] (p : ℕ) :
    constantCoeff (frobeniusQuotientSeries K p) = 1 := by
  rw [frobeniusQuotientSeries, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.coeff_map, PowerSeries.coeff_rescale, pow_zero, one_mul,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_exp, map_one]
theorem derivative_frobeniusQuotientSeries (K : Type*) [CommRing K] [Algebra ℚ K] (p : ℕ) :
    PowerSeries.derivative K (frobeniusQuotientSeries K p)
      = frobeniusQuotientSeries K p * PowerSeries.C (p : K) := by
  have hq : PowerSeries.derivative ℚ (PowerSeries.rescale (p : ℚ) (PowerSeries.exp ℚ))
      = PowerSeries.rescale (p : ℚ) (PowerSeries.exp ℚ) * PowerSeries.C (p : ℚ) := by
    rw [derivative_rescale, PowerSeries.derivative_exp]
    ring
  rw [frobeniusQuotientSeries, ← map_derivative, hq, map_mul, PowerSeries.map_C, map_natCast]
section FrobeniusQuotient
variable {R K : Type*} [CommRing R] [CommRing K] [Algebra ℚ K] (ι : R →+* K) (p : ℕ)
  (hE : ∀ n, coeff n (frobeniusQuotientSeries K p) ∈ Set.range ι)
@[simp]
theorem map_frobeniusQuotientOver :
    PowerSeries.map ι (frobeniusQuotientOver ι p hE) = frobeniusQuotientSeries K p := by
  ext n
  rw [PowerSeries.coeff_map, frobeniusQuotientOver, PowerSeries.coeff_mk]
  exact (hE n).choose_spec
@[simp]
theorem constantCoeff_frobeniusQuotientOver (hι : Function.Injective ι) :
    constantCoeff (frobeniusQuotientOver ι p hE) = 1 := by
  refine hι ?_
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← PowerSeries.coeff_map,
    map_frobeniusQuotientOver, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    constantCoeff_frobeniusQuotientSeries, map_one]
theorem derivative_frobeniusQuotientOver (hι : Function.Injective ι) :
    PowerSeries.derivative R (frobeniusQuotientOver ι p hE)
      = frobeniusQuotientOver ι p hE * PowerSeries.C (p : R) := by
  refine powerSeries_ext_of_injective ι hι ?_
  rw [map_derivative, map_frobeniusQuotientOver, map_mul, map_frobeniusQuotientOver,
    PowerSeries.map_C, map_natCast, derivative_frobeniusQuotientSeries]
theorem constantCoeff_rescale_frobeniusQuotientOver (hι : Function.Injective ι) (c : R) :
    constantCoeff (PowerSeries.rescale c (frobeniusQuotientOver ι p hE)) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale, pow_zero,
    one_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    constantCoeff_frobeniusQuotientOver ι p hE hι]
theorem derivative_rescale_frobeniusQuotientOver (hι : Function.Injective ι) (c : R) :
    PowerSeries.derivative R (PowerSeries.rescale c (frobeniusQuotientOver ι p hE))
      = PowerSeries.rescale c (frobeniusQuotientOver ι p hE) * PowerSeries.C ((p : R) * c) := by
  rw [derivative_rescale, derivative_frobeniusQuotientOver ι p hE hι, map_mul, rescale_C, map_mul]
  ring
end FrobeniusQuotient
end Formal
end FiniteFields.Dwork
end
end
section
noncomputable section
open PowerSeries
namespace FiniteFields.Dwork
section Formal
section Frobenius
variable {R K : Type*} [CommRing R] [CommRing K] [Algebra ℚ K] (ι : R →+* K) (p : ℕ)
  [Fact p.Prime] (hR : ∀ n, coeff n (artinHasseSeries K p) ∈ Set.range ι)
  (hE : ∀ n, coeff n (frobeniusQuotientSeries K p) ∈ Set.range ι)
omit hR hE in
theorem ghostComponent_zero_eq (u : WittVector p R) :
    WittVector.ghostComponent 0 u = u.coeff 0 := by
  rw [WittVector.ghostComponent_apply, aeval_wittPolynomial p ℤ u.coeff 0]
  simp
omit hR hE in
theorem ghostComponent_succ_verschiebung_frobenius (u : WittVector p R) (n : ℕ) :
    WittVector.ghostComponent (n + 1)
        (WittVector.verschiebung (WittVector.frobenius u))
      = WittVector.ghostComponent (n + 1) ((p : ℕ) • u) := by
  rw [WittVector.ghostComponent_verschiebung, WittVector.ghostComponent_frobenius, map_nsmul,
    nsmul_eq_mul]
omit hR hE in
theorem ghostComponent_zero_verschiebung_frobenius (u : WittVector p R) :
    WittVector.ghostComponent 0 (WittVector.verschiebung (WittVector.frobenius u))
      = WittVector.ghostComponent 0 ((p : ℕ) • u) - (p : R) * u.coeff 0 := by
  rw [WittVector.ghostComponent_zero_verschiebung, map_nsmul, nsmul_eq_mul,
    ghostComponent_zero_eq, sub_self]
theorem coeff_artinHasseWittLogDeriv_verschiebung_frobenius (N j : ℕ) (hj : j + 1 < N)
    (u : WittVector p R) :
    coeff j (artinHasseWittLogDeriv p N (WittVector.verschiebung (WittVector.frobenius u)))
      = coeff j (artinHasseWittLogDeriv p N ((p : ℕ) • u)
          + PowerSeries.C ((p : R) * u.coeff 0)) := by
  rw [map_add, PowerSeries.coeff_C]
  by_cases h : ∃ n, p ^ n = j + 1
  · obtain ⟨n, hn⟩ := h
    have hlt : n < p ^ n := Nat.lt_pow_self (Fact.out : Nat.Prime p).one_lt
    have hnN : n < N := by omega
    have hj' : p ^ n - 1 = j := by omega
    rcases n with _ | n
    · have hj0 : j = 0 := by
        rw [pow_zero] at hn
        omega
      have hL := coeff_artinHasseWittLogDeriv_pPow p N 0 hnN
        (WittVector.verschiebung (WittVector.frobenius u))
      have hR' := coeff_artinHasseWittLogDeriv_pPow p N 0 hnN ((p : ℕ) • u)
      rw [hj'] at hL hR'
      rw [if_pos hj0, hL, hR', ghostComponent_zero_verschiebung_frobenius p u]
      ring
    · have hjne : j ≠ 0 := by
        have hple : p ≤ p ^ (n + 1) := Nat.le_self_pow (by omega) p
        have hp2 : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
        omega
      have hL := coeff_artinHasseWittLogDeriv_pPow p N (n + 1) hnN
        (WittVector.verschiebung (WittVector.frobenius u))
      have hR' := coeff_artinHasseWittLogDeriv_pPow p N (n + 1) hnN ((p : ℕ) • u)
      rw [hj'] at hL hR'
      rw [if_neg hjne, add_zero, hL, hR', ghostComponent_succ_verschiebung_frobenius p u n]
  · rw [not_exists] at h
    have hjne : j ≠ 0 := by
      intro h0
      exact h 0 (by simp [h0])
    rw [if_neg hjne, add_zero,
      coeff_artinHasseWittLogDeriv_eq_zero p N j h,
      coeff_artinHasseWittLogDeriv_eq_zero p N j h]
theorem truncateSeries_formalArtinHasseSeries (hι : Function.Injective ι) (N : ℕ)
    (w : WittVector p R) :
    truncateSeries R N (formalArtinHasseSeries ι p hR w)
      = truncateSeries R N (artinHasseWittSeries ι p hR N w) :=
  truncateSeries_eq_iff.mpr fun _ hm => coeff_formalArtinHasseSeries ι p hR hι w hm
theorem coeff_artinHasseWittSeries_verschiebung_frobenius (hι : Function.Injective ι) (N : ℕ)
    (u : WittVector p R) (m : ℕ) (hm : m < N) :
    coeff m (artinHasseWittSeries ι p hR N
        (WittVector.verschiebung (WittVector.frobenius u)))
      = coeff m (artinHasseWittSeries ι p hR N ((p : ℕ) • u) *
          PowerSeries.rescale (u.coeff 0) (frobeniusQuotientOver ι p hE)) := by
  have hprod : PowerSeries.derivative R
      (artinHasseWittSeries ι p hR N ((p : ℕ) • u) *
        PowerSeries.rescale (u.coeff 0) (frobeniusQuotientOver ι p hE))
      = artinHasseWittSeries ι p hR N ((p : ℕ) • u) *
          PowerSeries.rescale (u.coeff 0) (frobeniusQuotientOver ι p hE) *
          (artinHasseWittLogDeriv p N ((p : ℕ) • u)
            + PowerSeries.C ((p : R) * u.coeff 0)) := by
    rw [Derivation.leibniz, derivative_artinHasseWittSeries ι p hR hι,
      derivative_rescale_frobeniusQuotientOver ι p hE hι]
    simp only [smul_eq_mul]
    ring
  refine hι ?_
  rw [← PowerSeries.coeff_map, ← PowerSeries.coeff_map]
  refine coeff_eq_of_derivative_eq_mul (N := N)
    (h₁ := PowerSeries.map ι (artinHasseWittLogDeriv p N
      (WittVector.verschiebung (WittVector.frobenius u))))
    (h₂ := PowerSeries.map ι (artinHasseWittLogDeriv p N ((p : ℕ) • u)
      + PowerSeries.C ((p : R) * u.coeff 0))) ?_ ?_ ?_ ?_ m hm
  · rw [← map_derivative, derivative_artinHasseWittSeries ι p hR hι, map_mul]
  · rw [← map_derivative, hprod, map_mul]
  · rw [constantCoeff_map' ι, constantCoeff_map' ι,
      constantCoeff_artinHasseWittSeries ι p hR hι, map_mul,
      constantCoeff_artinHasseWittSeries ι p hR hι,
      constantCoeff_rescale_frobeniusQuotientOver ι p hE hι, one_mul]
  · intro j hj
    rw [PowerSeries.coeff_map, PowerSeries.coeff_map]
    exact congrArg ι (coeff_artinHasseWittLogDeriv_verschiebung_frobenius p N j hj u)
theorem formalArtinHasseHom_frobenius (hι : Function.Injective ι) (u : WittVector p R) :
    PowerSeries.expand p (Fact.out : Nat.Prime p).ne_zero
        (Additive.toMul (formalArtinHasseHom ι p hR hι (WittVector.frobenius u))).val
      = (Additive.toMul (formalArtinHasseHom ι p hR hι u)).val ^ p *
          PowerSeries.rescale (u.coeff 0) (frobeniusQuotientOver ι p hE) := by
  have hp : (formalArtinHasseProduct ι p hR hι u).val ^ p
      = formalArtinHasseSeries ι p hR ((p : ℕ) • u) := by
    rw [← FormalPrincipalUnit.val_pow, ← formalArtinHasseProduct_nsmul ι p hR hι p u,
      val_formalArtinHasseProduct]
  rw [toMul_formalArtinHasseHom, toMul_formalArtinHasseHom,
    ← formalArtinHasseProduct_verschiebung ι p hR hι (WittVector.frobenius u),
    val_formalArtinHasseProduct, hp]
  refine PowerSeries.ext fun m => ?_
  refine truncateSeries_eq_iff.mp ?_ m (Nat.lt_succ_self m)
  rw [truncateSeries_formalArtinHasseSeries ι p hR hι (m + 1)
      (WittVector.verschiebung (WittVector.frobenius u)),
    map_mul, truncateSeries_formalArtinHasseSeries ι p hR hι (m + 1) ((p : ℕ) • u), ← map_mul]
  exact truncateSeries_eq_iff.mpr fun j hj =>
    coeff_artinHasseWittSeries_verschiebung_frobenius ι p hR hE hι (m + 1) u j hj
end Frobenius
end Formal
end FiniteFields.Dwork
end
end
section
noncomputable section
open PowerSeries
namespace FiniteFields.Dwork
section DworkCarrier
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
theorem dworkFormalArtinHasseProduct_teichmuller (a : CoefficientRing k p) :
    dworkFormalArtinHasseProduct k p (WittVector.teichmuller p a)
      = ⟨PowerSeries.rescale a (dworkArtinHasseOver k p),
          constantCoeff_rescale_artinHasseOver _ _ _
            (coefficientRingAlgebraMap_injective k p) a⟩ :=
  formalArtinHasseProduct_teichmuller _ _ _ (coefficientRingAlgebraMap_injective k p) a
theorem dworkFormalArtinHasseProduct_frobenius (u : WittVector p (CoefficientRing k p)) :
    PowerSeries.expand p (Fact.out : Nat.Prime p).ne_zero
        (dworkFormalArtinHasseProduct k p (WittVector.frobenius u)).val
      = (dworkFormalArtinHasseProduct k p u).val ^ p *
          PowerSeries.rescale (u.coeff 0)
            (frobeniusQuotientOver (coefficientRingAlgebraMap k p) p
              (frobeniusQuotientSeries_mem_range_coefficientRingAlgebraMap k p)) :=
  formalArtinHasseHom_frobenius _ _ _
    (frobeniusQuotientSeries_mem_range_coefficientRingAlgebraMap k p)
    (coefficientRingAlgebraMap_injective k p) u
end DworkCarrier
end FiniteFields.Dwork
end
end
section
noncomputable section
open PowerSeries IsUltrametricDist
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
theorem map_dworkArtinHasseOver :
    PowerSeries.map (cyclotomicCoefficientMap k p) (dworkArtinHasseOver k p)
      = dworkArtinHasseExponential k p := by
  refine PowerSeries.ext fun n => ?_
  rw [PowerSeries.coeff_map, dworkArtinHasseOver, cyclotomicCoefficientMap_apply,
    dworkArtinHasseExponential, PowerSeries.coeff_map]
  rw [map_coeff_artinHasseOver (coefficientRingAlgebraMap k p) p
    (artinHasseSeries_mem_range_coefficientRingAlgebraMap k p) n]
  rw [artinHasseSeries, PowerSeries.coeff_map]
  rw [eq_ratCast (algebraMap ℚ (CoefficientField k p)),
    show (algebraMap (CoefficientField k p) (DworkCyclotomicField k p))
        ((coeff n (artinHasseExponential p) : ℚ) : CoefficientField k p)
      = ((coeff n (artinHasseExponential p) : ℚ) : DworkCyclotomicField k p) by
      rw [map_ratCast]]
  rfl
end FiniteFields.Dwork
end
end
section
noncomputable section
open PowerSeries IsUltrametricDist
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
omit [Field k] [CharP k p] [Finite k] in
theorem map_rescale' {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (c : R) (f : R⟦X⟧) :
    PowerSeries.map φ (PowerSeries.rescale c f)
      = PowerSeries.rescale (φ c) (PowerSeries.map φ f) := by
  refine PowerSeries.ext fun n => ?_
  rw [PowerSeries.coeff_map, PowerSeries.coeff_rescale, PowerSeries.coeff_rescale,
    PowerSeries.coeff_map, map_mul, map_pow]
end FiniteFields.Dwork
end
end
section
noncomputable section
open PowerSeries IsUltrametricDist
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
theorem dworkPowerSeriesEval_expand (g : (DworkCyclotomicField k p)⟦X⟧)
    (x : DworkCyclotomicField k p) :
    dworkPowerSeriesEval k p
        (PowerSeries.expand p (Fact.out : Nat.Prime p).ne_zero g) x
      = dworkPowerSeriesEval k p g (x ^ p) := by
  have hp0 : p ≠ 0 := (Fact.out : Nat.Prime p).ne_zero
  have hinj : Function.Injective (fun m : ℕ => p * m) := fun a b hab => by
    simpa [hp0] using hab
  have hzero : ∀ n : ℕ, n ∉ Set.range (fun m : ℕ => p * m) →
      coeff n (PowerSeries.expand p hp0 g) * x ^ n = 0 := by
    intro n hn
    rw [PowerSeries.coeff_expand_of_not_dvd, zero_mul]
    rintro ⟨m, rfl⟩
    exact hn ⟨m, rfl⟩
  have hsupp : Function.support (fun n : ℕ => coeff n (PowerSeries.expand p hp0 g) * x ^ n)
      ⊆ Set.range (fun m : ℕ => p * m) := by
    intro n hn
    by_contra hrange
    exact hn (hzero n hrange)
  show (∑' n : ℕ, coeff n (PowerSeries.expand p hp0 g) * x ^ n)
      = ∑' m : ℕ, coeff m g * (x ^ p) ^ m
  rw [← hinj.tsum_eq hsupp]
  refine tsum_congr fun m => ?_
  show coeff (p * m) (PowerSeries.expand p hp0 g) * x ^ (p * m) = _
  rw [PowerSeries.coeff_expand_mul, pow_mul]
theorem norm_coeff_cyclotomicFrobeniusQuotient_le_one (n : ℕ) :
    ‖coeff n (cyclotomicFrobeniusQuotient k p)‖ ≤ 1 := by
  rw [cyclotomicFrobeniusQuotient, PowerSeries.coeff_map]
  exact norm_cyclotomicCoefficientMap_le_one k p _
theorem norm_coeff_rescale_cyclotomicFrobeniusQuotient_le_one
    (c : CoefficientRing k p) (n : ℕ) :
    ‖coeff n (PowerSeries.rescale (cyclotomicCoefficientMap k p c)
      (cyclotomicFrobeniusQuotient k p))‖ ≤ 1 := by
  rw [PowerSeries.coeff_rescale, norm_mul, norm_pow]
  exact mul_le_one₀
    (pow_le_one₀ (norm_nonneg _) (norm_cyclotomicCoefficientMap_le_one k p c))
    (norm_nonneg _) (norm_coeff_cyclotomicFrobeniusQuotient_le_one k p n)
end FiniteFields.Dwork
end
end
section
noncomputable section
open PowerSeries IsUltrametricDist
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
theorem geom_sum_dworkPrimitiveRoot_eq_zero :
    ∑ i ∈ Finset.range p, dworkPrimitiveRoot k p ^ i = 0 := by
  have hz : dworkPrimitiveRoot k p ^ p = 1 := (dworkPrimitiveRoot_isPrimitiveRoot k p).pow_eq_one
  have h := geom_sum_mul (dworkPrimitiveRoot k p) p
  rw [hz, sub_self] at h
  rcases mul_eq_zero.mp h with h1 | h2
  · exact h1
  · exact absurd h2 (sub_ne_zero.mpr
      ((dworkPrimitiveRoot_isPrimitiveRoot k p).ne_one (Fact.out : Nat.Prime p).one_lt))
theorem dworkRamificationParameter_shifted_relation :
    ∑ i ∈ Finset.range p,
        ((p.choose (i + 1) : DworkCyclotomicField k p)) *
          dworkRamificationParameter k p ^ i = 0 := by
  have h := congrArg (Polynomial.eval (dworkRamificationParameter k p))
    (Polynomial.geom_sum_X_comp_X_add_one_eq_sum (R := DworkCyclotomicField k p) p)
  rw [Polynomial.eval_comp] at h
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one,
    Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_natCast] at h
  rw [dworkRamificationParameter, sub_add_cancel, geom_sum_dworkPrimitiveRoot_eq_zero] at h
  exact h.symm
theorem norm_dworkRamificationParameter_pow_le :
    ‖dworkRamificationParameter k p‖ ^ (p - 1) ≤ ‖(p : DworkCyclotomicField k p)‖ := by
  have hp1 : 1 < p := (Fact.out : Nat.Prime p).one_lt
  have hpm : p - 1 + 1 = p := by omega
  have hlam : ‖dworkRamificationParameter k p‖ ≤ 1 :=
    (dworkRamificationParameter_norm_lt_one k p).le
  have hsplit := Finset.sum_range_succ
    (fun i => ((p.choose (i + 1) : DworkCyclotomicField k p)) *
      dworkRamificationParameter k p ^ i) (p - 1)
  rw [hpm, dworkRamificationParameter_shifted_relation, Nat.choose_self, Nat.cast_one,
    one_mul] at hsplit
  have hval : dworkRamificationParameter k p ^ (p - 1)
      = -∑ i ∈ Finset.range (p - 1),
          ((p.choose (i + 1) : DworkCyclotomicField k p)) *
            dworkRamificationParameter k p ^ i :=
    eq_neg_of_add_eq_zero_right hsplit.symm
  have hterm : ∀ i ∈ Finset.range (p - 1),
      ‖((p.choose (i + 1) : DworkCyclotomicField k p)) *
        dworkRamificationParameter k p ^ i‖ ≤ ‖(p : DworkCyclotomicField k p)‖ := by
    intro i hi
    rw [Finset.mem_range] at hi
    obtain ⟨a, ha⟩ := (Fact.out : Nat.Prime p).dvd_choose_self i.succ_ne_zero (by omega)
    rw [ha, Nat.cast_mul, norm_mul, norm_mul, norm_pow]
    calc ‖(p : DworkCyclotomicField k p)‖ * ‖(a : DworkCyclotomicField k p)‖ *
          ‖dworkRamificationParameter k p‖ ^ i
        ≤ ‖(p : DworkCyclotomicField k p)‖ * 1 * 1 := by
          gcongr
          · exact IsUltrametricDist.norm_natCast_le_one (DworkCyclotomicField k p) a
          · exact pow_le_one₀ (norm_nonneg _) hlam
      _ = ‖(p : DworkCyclotomicField k p)‖ := by rw [mul_one, mul_one]
  calc ‖dworkRamificationParameter k p‖ ^ (p - 1)
      = ‖dworkRamificationParameter k p ^ (p - 1)‖ := (norm_pow _ _).symm
    _ = ‖∑ i ∈ Finset.range (p - 1),
          ((p.choose (i + 1) : DworkCyclotomicField k p)) *
            dworkRamificationParameter k p ^ i‖ := by rw [hval, norm_neg]
    _ ≤ ‖(p : DworkCyclotomicField k p)‖ :=
        IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) hterm
theorem norm_dworkArtinHasseParameter_le :
    ‖dworkArtinHasseParameter k p‖ ≤ ‖dworkRamificationParameter k p‖ :=
  (existsUnique_dworkArtinHasseParameter k p).choose_spec.1.1
theorem norm_dworkArtinHasseParameter_pow_le :
    ‖dworkArtinHasseParameter k p‖ ^ (p - 1) ≤ ‖(p : DworkCyclotomicField k p)‖ :=
  le_trans (pow_le_pow_left₀ (norm_nonneg _) (norm_dworkArtinHasseParameter_le k p) (p - 1))
    (norm_dworkRamificationParameter_pow_le k p)
end FiniteFields.Dwork
end
end
section
noncomputable section
open PowerSeries IsUltrametricDist
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
theorem norm_dworkPowerSeriesEval_sub_one_le (f : (DworkCyclotomicField k p)⟦X⟧)
    (hf : ∀ n, ‖coeff n f‖ ≤ 1) (hc : PowerSeries.constantCoeff f = 1)
    {z : DworkCyclotomicField k p} (hz : ‖z‖ < 1) :
    ‖dworkPowerSeriesEval k p f z - 1‖ ≤ ‖z‖ := by
  have hsum := hasSum_dworkPowerSeriesEval k p f z hf hz
  have hsplit := (hsum.summable).tsum_eq_zero_add
  have hzero : coeff 0 f * z ^ 0 = 1 := by
    rw [pow_zero, mul_one, PowerSeries.coeff_zero_eq_constantCoeff_apply, hc]
  have hval : dworkPowerSeriesEval k p f z
      = 1 + ∑' n : ℕ, coeff (n + 1) f * z ^ (n + 1) := by
    rw [hsum.tsum_eq] at hsplit
    rw [hsplit, hzero]
  rw [hval, add_sub_cancel_left]
  refine norm_tsum_le_of_forall_le_of_nonneg (norm_nonneg _) ?_
  intro n
  rw [norm_mul, norm_pow]
  calc ‖coeff (n + 1) f‖ * ‖z‖ ^ (n + 1)
      ≤ 1 * ‖z‖ ^ (n + 1) := mul_le_mul_of_nonneg_right (hf _) (by positivity)
    _ = ‖z‖ ^ (n + 1) := one_mul _
    _ ≤ ‖z‖ ^ 1 := pow_le_pow_of_le_one (norm_nonneg _) hz.le (by omega)
    _ = ‖z‖ := pow_one _
theorem dworkArtinHasseExponential_constantCoeff :
    PowerSeries.constantCoeff (dworkArtinHasseExponential k p) = 1 := by
  have h := dworkSplittingFunction_coeff k p 0
  rw [pow_zero, one_mul] at h
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← h,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, dworkSplittingFunction_constantCoeff]
theorem norm_coeff_artinHasse_le_one (u : WittVector p (CoefficientRing k p)) (n : ℕ) :
    ‖coeff n (mapFormalPrincipalUnitToCyclotomic k p
      (dworkFormalArtinHasseProduct k p u)).val‖ ≤ 1 :=
  norm_coeff_mapFormalPrincipalUnitToCyclotomic_le_one k p _ n
theorem artinHasseEvalAt_add (u v : WittVector p (CoefficientRing k p))
    {z : DworkCyclotomicField k p} (hz : ‖z‖ < 1) :
    artinHasseEvalAt k p (u + v) z = artinHasseEvalAt k p u z * artinHasseEvalAt k p v z := by
  have h := dworkPowerSeriesEval_mul k p z hz
    ⟨_, norm_coeff_artinHasse_le_one k p u⟩ ⟨_, norm_coeff_artinHasse_le_one k p v⟩
  rw [artinHasseEvalAt, dworkFormalArtinHasseProduct_add,
    mapFormalPrincipalUnitToCyclotomic_mul, FormalPrincipalUnit.val_mul]
  exact h
theorem artinHasseEvalAt_teichmuller (a : CoefficientRing k p)
    (z : DworkCyclotomicField k p) :
    artinHasseEvalAt k p (WittVector.teichmuller p a) z
      = dworkPowerSeriesEval k p (dworkArtinHasseExponential k p)
          (cyclotomicCoefficientMap k p a * z) := by
  rw [artinHasseEvalAt, dworkFormalArtinHasseProduct_teichmuller,
    val_mapFormalPrincipalUnitToCyclotomic]
  show dworkPowerSeriesEval k p (PowerSeries.map (cyclotomicCoefficientMap k p)
      (PowerSeries.rescale a (dworkArtinHasseOver k p))) z = _
  rw [map_rescale', map_dworkArtinHasseOver, dworkPowerSeriesEval_rescale]
theorem artinHasseEvalAt_verschiebung (w : WittVector p (CoefficientRing k p))
    (z : DworkCyclotomicField k p) :
    artinHasseEvalAt k p (WittVector.verschiebung w) z = artinHasseEvalAt k p w (z ^ p) := by
  rw [artinHasseEvalAt, artinHasseEvalAt, val_mapFormalPrincipalUnitToCyclotomic,
    val_mapFormalPrincipalUnitToCyclotomic]
  show dworkPowerSeriesEval k p (PowerSeries.map (cyclotomicCoefficientMap k p)
      (dworkFormalArtinHasseProduct k p (WittVector.verschiebung w)).val) z = _
  rw [dworkFormalArtinHasseProduct, formalArtinHasseProduct_verschiebung
      (coefficientRingAlgebraMap k p) p (artinHasseSeries_mem_range_coefficientRingAlgebraMap k p)
      (coefficientRingAlgebraMap_injective k p) w,
    PowerSeries.map_expand, dworkPowerSeriesEval_expand]
  rfl
omit [Finite k] in
theorem eq_verschiebung_of_coeff_zero {R : Type*} [CommRing R] {v : WittVector p R}
    (hv : v.coeff 0 = 0) :
    v = WittVector.verschiebung (WittVector.mk p fun n => v.coeff (n + 1)) := by
  ext n
  cases n with
  | zero => rw [WittVector.verschiebung_coeff_zero, hv]
  | succ m => rw [WittVector.verschiebung_coeff_succ, WittVector.coeff_mk]
theorem norm_artinHasseEvalAt_sub_one_le (u : WittVector p (CoefficientRing k p))
    {z : DworkCyclotomicField k p} (hz : ‖z‖ < 1) :
    ‖artinHasseEvalAt k p u z - 1‖
      ≤ max (‖cyclotomicCoefficientMap k p (u.coeff 0)‖ * ‖z‖) (‖z‖ ^ p) := by
  set ι := cyclotomicCoefficientMap k p with hι
  have hnorm : ‖ι (u.coeff 0)‖ ≤ 1 := norm_cyclotomicCoefficientMap_le_one k p _
  have hzp : ‖z ^ p‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hz (Fact.out : Nat.Prime p).ne_zero
  have hv : (u - WittVector.teichmuller p (u.coeff 0)).coeff 0 = 0 := by
    have h0 : (u - WittVector.teichmuller p (u.coeff 0)).coeff 0
        = WittVector.constantCoeff (u - WittVector.teichmuller p (u.coeff 0)) := rfl
    rw [h0, map_sub]
    show u.coeff 0 - (WittVector.teichmuller p (u.coeff 0)).coeff 0 = 0
    rw [WittVector.teichmuller_coeff_zero, sub_self]
  set w := WittVector.mk p fun n => (u - WittVector.teichmuller p (u.coeff 0)).coeff (n + 1)
    with hw
  have hdecomp : u = WittVector.teichmuller p (u.coeff 0) + WittVector.verschiebung w := by
    rw [hw, ← eq_verschiebung_of_coeff_zero p hv, add_sub_cancel]
  set A := artinHasseEvalAt k p (WittVector.teichmuller p (u.coeff 0)) z with hA
  set B := artinHasseEvalAt k p (WittVector.verschiebung w) z with hB
  have hAbound : ‖A - 1‖ ≤ ‖ι (u.coeff 0)‖ * ‖z‖ := by
    rw [hA, artinHasseEvalAt_teichmuller]
    have hlt : ‖ι (u.coeff 0) * z‖ < 1 := by
      rw [norm_mul]
      calc ‖ι (u.coeff 0)‖ * ‖z‖ ≤ 1 * ‖z‖ :=
            mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
        _ = ‖z‖ := one_mul _
        _ < 1 := hz
    have := norm_dworkPowerSeriesEval_sub_one_le k p (dworkArtinHasseExponential k p)
      (dworkArtinHasseExponential_coeff_norm_le_one k p)
      (dworkArtinHasseExponential_constantCoeff k p) hlt
    rwa [norm_mul] at this
  have hBbound : ‖B - 1‖ ≤ ‖z‖ ^ p := by
    rw [hB, artinHasseEvalAt_verschiebung]
    have := norm_dworkPowerSeriesEval_sub_one_le k p _
      (norm_coeff_artinHasse_le_one k p w)
      (mapFormalPrincipalUnitToCyclotomic k p (dworkFormalArtinHasseProduct k p w)).constantCoeff_val
      hzp
    rwa [norm_pow] at this
  have hBle : ‖B‖ ≤ 1 := by
    have : B = 1 + (B - 1) := by ring
    rw [this]
    refine le_trans (norm_add_le_max _ _) ?_
    rw [norm_one]
    exact max_le le_rfl (hBbound.trans (le_of_lt (by
      rw [← norm_pow]; exact hzp)))
  have hval : artinHasseEvalAt k p u z = A * B := by
    rw [hA, hB, ← artinHasseEvalAt_add k p _ _ hz, ← hdecomp]
  rw [hval]
  have hexp : A * B - 1 = (A - 1) * B + (B - 1) := by ring
  rw [hexp]
  refine le_trans (norm_add_le_max _ _) (max_le_max ?_ hBbound)
  rw [norm_mul]
  calc ‖A - 1‖ * ‖B‖ ≤ (‖ι (u.coeff 0)‖ * ‖z‖) * 1 :=
        mul_le_mul hAbound hBle (norm_nonneg _) (by positivity)
    _ = ‖ι (u.coeff 0)‖ * ‖z‖ := mul_one _
theorem norm_pow_p_sub_one_eq {y : DworkCyclotomicField k p}
    (h : ‖y - 1‖ ^ (p - 1) < ‖(p : DworkCyclotomicField k p)‖) :
    ‖y ^ p - 1‖ = ‖(p : DworkCyclotomicField k p)‖ * ‖y - 1‖ := by
  have hp1 : 1 < p := (Fact.out : Nat.Prime p).one_lt
  have hpm : p - 1 + 1 = p := by omega
  have hpnorm : ‖(p : DworkCyclotomicField k p)‖ ≤ 1 :=
    IsUltrametricDist.norm_natCast_le_one _ p
  set t := y - 1 with ht
  rcases eq_or_ne t 0 with h0 | h0
  · have hy : y = 1 := by rw [← sub_eq_zero, ← ht]; exact h0
    rw [hy, one_pow, sub_self, h0, norm_zero, mul_zero]
  have htpos : 0 < ‖t‖ := norm_pos_iff.mpr h0
  have htlt : ‖t‖ < 1 := by
    by_contra hcon
    rw [not_lt] at hcon
    have h1 : (1 : ℝ) ≤ ‖t‖ ^ (p - 1) := one_le_pow₀ hcon
    linarith
  have hy : y = t + 1 := by rw [ht]; ring
  have h0mem : (0 : ℕ) ∈ Finset.range p := Finset.mem_range.mpr (by omega)
  have hbin : y ^ p - 1
      = (∑ j ∈ (Finset.range p).erase 0,
          (p.choose (j + 1) : DworkCyclotomicField k p) * t ^ (j + 1))
        + (p : DworkCyclotomicField k p) * t := by
    have hexp : (t + 1) ^ p
        = ∑ j ∈ Finset.range (p + 1),
            t ^ j * 1 ^ (p - j) * (p.choose j : DworkCyclotomicField k p) := add_pow t 1 p
    have hstep1 : (t + 1) ^ p
        = (∑ j ∈ Finset.range p,
            (p.choose (j + 1) : DworkCyclotomicField k p) * t ^ (j + 1)) + 1 := by
      rw [hexp, Finset.sum_range_succ']
      simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by ring
    have hpeel := Finset.add_sum_erase (Finset.range p)
      (fun j => (p.choose (j + 1) : DworkCyclotomicField k p) * t ^ (j + 1)) h0mem
    rw [hy, hstep1, ← hpeel]
    simp only [zero_add, Nat.choose_one_right, pow_one]
    ring
  have hppos : 0 < ‖(p : DworkCyclotomicField k p)‖ := lt_of_le_of_lt (by positivity) h
  have hC : max (‖(p : DworkCyclotomicField k p)‖ * ‖t‖ ^ 2) (‖t‖ ^ p)
      < ‖(p : DworkCyclotomicField k p)‖ * ‖t‖ := by
    refine max_lt ?_ ?_
    · have hsq : ‖t‖ ^ 2 < ‖t‖ := by nlinarith
      exact mul_lt_mul_of_pos_left hsq hppos
    · calc ‖t‖ ^ p = ‖t‖ ^ (p - 1) * ‖t‖ := by rw [← pow_succ, hpm]
        _ < ‖(p : DworkCyclotomicField k p)‖ * ‖t‖ := mul_lt_mul_of_pos_right h htpos
  have hterms : ∀ j ∈ (Finset.range p).erase 0,
      ‖(p.choose (j + 1) : DworkCyclotomicField k p) * t ^ (j + 1)‖
        ≤ max (‖(p : DworkCyclotomicField k p)‖ * ‖t‖ ^ 2) (‖t‖ ^ p) := by
    intro j hj
    have hj0 : j ≠ 0 := Finset.ne_of_mem_erase hj
    have hjp : j < p := Finset.mem_range.mp (Finset.mem_of_mem_erase hj)
    rcases eq_or_lt_of_le (show j + 1 ≤ p by omega) with heq | hlt
    · rw [heq, Nat.choose_self, Nat.cast_one, one_mul, norm_pow]
      exact le_max_right _ _
    · obtain ⟨a, ha⟩ := (Fact.out : Nat.Prime p).dvd_choose_self (by omega) hlt
      rw [ha, Nat.cast_mul, norm_mul, norm_mul, norm_pow]
      refine le_trans ?_ (le_max_left _ _)
      calc ‖(p : DworkCyclotomicField k p)‖ * ‖(a : DworkCyclotomicField k p)‖ * ‖t‖ ^ (j + 1)
          ≤ ‖(p : DworkCyclotomicField k p)‖ * 1 * ‖t‖ ^ 2 :=
            mul_le_mul
              (mul_le_mul_of_nonneg_left
                (IsUltrametricDist.norm_natCast_le_one _ a) (norm_nonneg _))
              (pow_le_pow_of_le_one (norm_nonneg _) htlt.le (by omega))
              (by positivity) (by positivity)
        _ = ‖(p : DworkCyclotomicField k p)‖ * ‖t‖ ^ 2 := by rw [mul_one]
  have hsum : ‖∑ j ∈ (Finset.range p).erase 0,
      (p.choose (j + 1) : DworkCyclotomicField k p) * t ^ (j + 1)‖
        < ‖(p : DworkCyclotomicField k p)‖ * ‖t‖ :=
    lt_of_le_of_lt
      (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
        (le_trans (by positivity) (le_max_right _ _)) hterms) hC
  have hne : ‖∑ j ∈ (Finset.range p).erase 0,
      (p.choose (j + 1) : DworkCyclotomicField k p) * t ^ (j + 1)‖
        ≠ ‖(p : DworkCyclotomicField k p) * t‖ := by
    rw [norm_mul]; exact ne_of_lt hsum
  rw [hbin, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_mul]
  exact max_eq_right hsum.le
theorem norm_pow_pPow_sub_one_eq (m : ℕ) {y : DworkCyclotomicField k p}
    (h : ‖y - 1‖ ^ (p - 1) < ‖(p : DworkCyclotomicField k p)‖) :
    ‖y ^ (p ^ m) - 1‖ = ‖(p : DworkCyclotomicField k p)‖ ^ m * ‖y - 1‖ := by
  have hpnorm : ‖(p : DworkCyclotomicField k p)‖ ≤ 1 :=
    IsUltrametricDist.norm_natCast_le_one _ p
  induction m with
  | zero => rw [pow_zero, pow_one, pow_zero, one_mul]
  | succ n ih =>
      have hle : ‖y ^ (p ^ n) - 1‖ ≤ ‖y - 1‖ := by
        rw [ih]
        calc ‖(p : DworkCyclotomicField k p)‖ ^ n * ‖y - 1‖ ≤ 1 * ‖y - 1‖ :=
              mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg _) hpnorm) (norm_nonneg _)
          _ = ‖y - 1‖ := one_mul _
      have hnext : ‖y ^ (p ^ n) - 1‖ ^ (p - 1) < ‖(p : DworkCyclotomicField k p)‖ :=
        lt_of_le_of_lt (pow_le_pow_left₀ (norm_nonneg _) hle (p - 1)) h
      rw [pow_succ, pow_mul, norm_pow_p_sub_one_eq k p hnext, ih, pow_succ]
      ring
end FiniteFields.Dwork
end
end
section
noncomputable section
open PowerSeries IsUltrametricDist
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
theorem norm_pow_sub_one_le {u : DworkCyclotomicField k p} (hu : ‖u‖ ≤ 1) (n : ℕ) :
    ‖u ^ n - 1‖ ≤ ‖u - 1‖ := by
  rw [← geom_sum_mul u n, norm_mul]
  calc ‖∑ i ∈ Finset.range n, u ^ i‖ * ‖u - 1‖
      ≤ 1 * ‖u - 1‖ :=
        mul_le_mul_of_nonneg_right
          (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
            (fun i _ => by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hu)) (norm_nonneg _)
    _ = ‖u - 1‖ := one_mul _
theorem norm_mul_sub_one_le {a b : DworkCyclotomicField k p} (hb : ‖b‖ ≤ 1) :
    ‖a * b - 1‖ ≤ max ‖a - 1‖ ‖b - 1‖ := by
  have hrw : a * b - 1 = (a - 1) * b + (b - 1) := by ring
  rw [hrw]
  refine le_trans (norm_add_le_max _ _) (max_le_max ?_ le_rfl)
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) hb
theorem norm_eq_one_of_norm_sub_one_lt {a : DworkCyclotomicField k p} (h : ‖a - 1‖ < 1) :
    ‖a‖ = 1 :=
  DworkPrincipalUnit.norm_val (⟨a, h⟩ : DworkPrincipalUnit k p)
theorem dworkPowerSeriesEval_mul_bounded (f g : (DworkCyclotomicField k p)⟦X⟧)
    (hf : ∀ n, ‖coeff n f‖ ≤ 1) (hg : ∀ n, ‖coeff n g‖ ≤ 1)
    {z : DworkCyclotomicField k p} (hz : ‖z‖ < 1) :
    dworkPowerSeriesEval k p (f * g) z
      = dworkPowerSeriesEval k p f z * dworkPowerSeriesEval k p g z :=
  dworkPowerSeriesEval_mul k p z hz ⟨f, hf⟩ ⟨g, hg⟩
theorem dworkPowerSeriesEval_pow_bounded (f : (DworkCyclotomicField k p)⟦X⟧)
    (hf : ∀ n, ‖coeff n f‖ ≤ 1) (m : ℕ)
    {z : DworkCyclotomicField k p} (hz : ‖z‖ < 1) :
    dworkPowerSeriesEval k p (f ^ m) z = dworkPowerSeriesEval k p f z ^ m :=
  map_pow (dworkPowerSeriesEvalRingHom k p z hz) ⟨f, hf⟩ m
theorem constantCoeff_cyclotomicFrobeniusQuotient :
    PowerSeries.constantCoeff (cyclotomicFrobeniusQuotient k p) = 1 := by
  rw [cyclotomicFrobeniusQuotient, constantCoeff_map' (cyclotomicCoefficientMap k p),
    constantCoeff_frobeniusQuotientOver _ _ _ (coefficientRingAlgebraMap_injective k p), map_one]
theorem artinHasseEvalAt_frobenius (u : WittVector p (CoefficientRing k p))
    {z : DworkCyclotomicField k p} (hz : ‖z‖ < 1) :
    artinHasseEvalAt k p (WittVector.frobenius u) (z ^ p)
      = artinHasseEvalAt k p u z ^ p *
        dworkPowerSeriesEval k p (cyclotomicFrobeniusQuotient k p)
          (cyclotomicCoefficientMap k p (u.coeff 0) * z) := by
  have hAbase := norm_coeff_artinHasse_le_one k p u
  have hA : ∀ n, ‖coeff n ((mapFormalPrincipalUnitToCyclotomic k p
      (dworkFormalArtinHasseProduct k p u)).val ^ p)‖ ≤ 1 :=
    (BoundedDworkPowerSeries k p).pow_mem hAbase p
  have hB := norm_coeff_rescale_cyclotomicFrobeniusQuotient_le_one k p (u.coeff 0)
  have hmapped := congrArg (PowerSeries.map (cyclotomicCoefficientMap k p))
    (dworkFormalArtinHasseProduct_frobenius k p u)
  rw [PowerSeries.map_expand, map_mul, map_pow, map_rescale'] at hmapped
  have heval := congrArg (fun G => dworkPowerSeriesEval k p G z) hmapped
  rw [dworkPowerSeriesEval_expand] at heval
  simp only [val_mapFormalPrincipalUnitToCyclotomic, cyclotomicFrobeniusQuotient] at hA hB hAbase ⊢
  rw [artinHasseEvalAt, artinHasseEvalAt, val_mapFormalPrincipalUnitToCyclotomic,
    val_mapFormalPrincipalUnitToCyclotomic, heval,
    dworkPowerSeriesEval_mul_bounded k p _ _ hA hB hz,
    dworkPowerSeriesEval_pow_bounded k p _ hAbase p hz, dworkPowerSeriesEval_rescale]
theorem norm_natCast_p_lt_one : ‖(p : DworkCyclotomicField k p)‖ < 1 := by
  rw [show (p : DworkCyclotomicField k p)
      = algebraMap (CoefficientField k p) (DworkCyclotomicField k p) (p : CoefficientField k p) by
        simp,
    dworkCyclotomicField_norm_algebraMap]
  exact coefficientField_norm_p_lt_one k p
theorem natCast_p_ne_zero : (p : DworkCyclotomicField k p) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime p).ne_zero
end FiniteFields.Dwork
end
end
section
noncomputable section
open PowerSeries IsUltrametricDist
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
attribute [local instance] FiniteFields.Dwork.dw4e2TraceLimitResiduePrimeAlgebra
theorem exists_artinHasseEvalAt_pow_factor (D : WittVector p (CoefficientRing k p))
    (hD : WittVector.frobenius D = D) (j : ℕ) :
    ∃ R : DworkCyclotomicField k p,
      artinHasseEvalAt k p D (dworkArtinHasseParameter k p ^ p ^ j)
          = artinHasseEvalAt k p D (dworkArtinHasseParameter k p) ^ p ^ j * R ∧
        ‖R - 1‖ ≤ ‖cyclotomicCoefficientMap k p (D.coeff 0)‖ *
          ‖dworkArtinHasseParameter k p‖ := by
  have he : ‖dworkArtinHasseParameter k p‖ < 1 := dworkArtinHasseParameter_norm_lt_one k p
  have hd : ‖cyclotomicCoefficientMap k p (D.coeff 0)‖ ≤ 1 :=
    norm_cyclotomicCoefficientMap_le_one k p _
  have hde : ‖cyclotomicCoefficientMap k p (D.coeff 0)‖ * ‖dworkArtinHasseParameter k p‖ < 1 := by
    calc ‖cyclotomicCoefficientMap k p (D.coeff 0)‖ * ‖dworkArtinHasseParameter k p‖
        ≤ 1 * ‖dworkArtinHasseParameter k p‖ :=
          mul_le_mul_of_nonneg_right hd (norm_nonneg _)
      _ = ‖dworkArtinHasseParameter k p‖ := one_mul _
      _ < 1 := he
  have hpowlt : ∀ i : ℕ, ‖dworkArtinHasseParameter k p ^ p ^ i‖ < 1 := by
    intro i
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) he (pow_pos (Fact.out : Nat.Prime p).pos i).ne'
  induction j with
  | zero =>
      refine ⟨1, ?_, ?_⟩
      · rw [mul_one, pow_zero, pow_one, pow_one]
      · rw [sub_self, norm_zero]
        positivity
  | succ n ih =>
      obtain ⟨R, hR, hRnorm⟩ := ih
      have hRone : ‖R‖ = 1 :=
        norm_eq_one_of_norm_sub_one_lt k p (lt_of_le_of_lt hRnorm hde)
      have hfrob := artinHasseEvalAt_frobenius k p D (hpowlt n)
      rw [hD, ← pow_mul, ← pow_succ] at hfrob
      set Q := dworkPowerSeriesEval k p (cyclotomicFrobeniusQuotient k p)
        (cyclotomicCoefficientMap k p (D.coeff 0) * dworkArtinHasseParameter k p ^ p ^ n) with hQdef
      have hQpt : ‖cyclotomicCoefficientMap k p (D.coeff 0) *
          dworkArtinHasseParameter k p ^ p ^ n‖
            ≤ ‖cyclotomicCoefficientMap k p (D.coeff 0)‖ * ‖dworkArtinHasseParameter k p‖ := by
        rw [norm_mul, norm_pow]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        calc ‖dworkArtinHasseParameter k p‖ ^ p ^ n
            ≤ ‖dworkArtinHasseParameter k p‖ ^ 1 :=
              pow_le_pow_of_le_one (norm_nonneg _) he.le
                (Nat.one_le_pow _ _ (Fact.out : Nat.Prime p).pos)
          _ = ‖dworkArtinHasseParameter k p‖ := pow_one _
      have hQnorm : ‖Q - 1‖ ≤ ‖cyclotomicCoefficientMap k p (D.coeff 0)‖ *
          ‖dworkArtinHasseParameter k p‖ :=
        le_trans (norm_dworkPowerSeriesEval_sub_one_le k p _
          (norm_coeff_cyclotomicFrobeniusQuotient_le_one k p)
          (constantCoeff_cyclotomicFrobeniusQuotient k p)
          (lt_of_le_of_lt hQpt hde)) hQpt
      have hQone : ‖Q‖ = 1 :=
        norm_eq_one_of_norm_sub_one_lt k p (lt_of_le_of_lt hQnorm hde)
      refine ⟨R ^ p * Q, ?_, ?_⟩
      · rw [hfrob, hR, mul_pow, ← pow_mul, ← pow_succ]
        ring
      · refine le_trans (norm_mul_sub_one_le k p (le_of_eq hQone)) (max_le ?_ hQnorm)
        exact le_trans (norm_pow_sub_one_le k p (le_of_eq hRone) p) hRnorm
omit [Field k] [CharP k p] [Finite k] in
theorem two_mul_le_pow_succ (m : ℕ) : 2 * m * (p - 1) ≤ p ^ (m + 1) := by
  have hp2 : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have hq1 : 1 ≤ q := by omega
  have hbern : ∀ i : ℕ, 1 + i * q ≤ (q + 1) ^ i := by
    intro i
    induction i with
    | zero => simp
    | succ n ih =>
        have hone : 1 ≤ (q + 1) ^ n := Nat.one_le_pow _ _ (by omega)
        calc 1 + (n + 1) * q = (1 + n * q) + q := by ring
          _ ≤ (q + 1) ^ n + q := Nat.add_le_add_right ih q
          _ ≤ (q + 1) ^ n + q * (q + 1) ^ n := by nlinarith
          _ = (q + 1) ^ (n + 1) := by ring
  have hb := Nat.mul_le_mul_left (q + 1) (hbern m)
  rw [← pow_succ'] at hb
  have hpq : p - 1 = q := by omega
  rw [hpq, hq]
  have hh : m * q * 1 ≤ m * q * q := Nat.mul_le_mul_left _ hq1
  have h2 : 2 * m * q ≤ (q + 1) * (1 + m * q) := by nlinarith
  exact le_trans h2 hb
end FiniteFields.Dwork
end
end
open PowerSeries IsUltrametricDist
open FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
attribute [local instance] FiniteFields.Dwork.dw4e2TraceLimitResiduePrimeAlgebra
theorem solution (D : WittVector p (CoefficientRing k p))
    (hD : WittVector.frobenius D = D) (m : ℕ)
    (hD0 : ‖cyclotomicCoefficientMap k p (D.coeff 0)‖
      ≤ ‖(p : DworkCyclotomicField k p)‖ ^ (2 * m + 2)) :
    ‖artinHasseEvalAt k p D (dworkArtinHasseParameter k p) - 1‖
      ≤ ‖(p : DworkCyclotomicField k p)‖ ^ m := by
  have hp2 : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  have he : ‖dworkArtinHasseParameter k p‖ < 1 := dworkArtinHasseParameter_norm_lt_one k p
  have hrho1 : ‖(p : DworkCyclotomicField k p)‖ < 1 := norm_natCast_p_lt_one k p
  have hrho0 : 0 < ‖(p : DworkCyclotomicField k p)‖ :=
    norm_pos_iff.mpr (natCast_p_ne_zero k p)
  have hepow : ‖dworkArtinHasseParameter k p‖ ^ (p - 1)
      ≤ ‖(p : DworkCyclotomicField k p)‖ := norm_dworkArtinHasseParameter_pow_le k p
  set ρ := ‖(p : DworkCyclotomicField k p)‖ with hρ
  set e := ‖dworkArtinHasseParameter k p‖ with hedef
  set d := ‖cyclotomicCoefficientMap k p (D.coeff 0)‖ with hddef
  set y := artinHasseEvalAt k p D (dworkArtinHasseParameter k p) with hy
  have hd2 : d ≤ ρ ^ 2 :=
    le_trans hD0 (pow_le_pow_of_le_one (le_of_lt hrho0) hrho1.le (by omega))
  have hstep0 : ‖y - 1‖ ≤ max (d * e) (e ^ p) := by
    simpa [hy, hddef, hedef] using norm_artinHasseEvalAt_sub_one_le k p D he
  have hsmall : ‖y - 1‖ ^ (p - 1) < ρ := by
    have hmono : ‖y - 1‖ ^ (p - 1) ≤ (max (d * e) (e ^ p)) ^ (p - 1) :=
      pow_le_pow_left₀ (norm_nonneg _) hstep0 (p - 1)
    have hmax : (max (d * e) (e ^ p)) ^ (p - 1) = max ((d * e) ^ (p - 1)) ((e ^ p) ^ (p - 1)) := by
      rcases le_total (d * e) (e ^ p) with hle | hle
      · rw [max_eq_right hle, max_eq_right (pow_le_pow_left₀ (by positivity) hle (p - 1))]
      · rw [max_eq_left hle, max_eq_left (pow_le_pow_left₀ (by positivity) hle (p - 1))]
    have h1 : (d * e) ^ (p - 1) < ρ := by
      calc (d * e) ^ (p - 1) = d ^ (p - 1) * e ^ (p - 1) := mul_pow _ _ _
        _ ≤ (ρ ^ 2) ^ (p - 1) * ρ :=
            mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hd2 (p - 1)) hepow
              (by positivity) (by positivity)
        _ = ρ ^ (2 * (p - 1) + 1) := by rw [← pow_mul, ← pow_succ]
        _ < ρ ^ 1 := pow_lt_pow_right_of_lt_one₀ hrho0 hrho1 (by omega)
        _ = ρ := pow_one _
    have h2 : (e ^ p) ^ (p - 1) < ρ := by
      calc (e ^ p) ^ (p - 1) = e ^ (p * (p - 1)) := (pow_mul e p (p - 1)).symm
        _ = (e ^ (p - 1)) ^ p := by rw [Nat.mul_comm, pow_mul]
        _ ≤ ρ ^ p := pow_le_pow_left₀ (by positivity) hepow p
        _ < ρ ^ 1 := pow_lt_pow_right_of_lt_one₀ hrho0 hrho1 (by omega)
        _ = ρ := pow_one _
    exact lt_of_le_of_lt (le_trans hmono (le_of_eq hmax)) (max_lt h1 h2)
  obtain ⟨R, hR, hRnorm⟩ := exists_artinHasseEvalAt_pow_factor k p D hD m
  have hde : d * e < 1 := by
    calc d * e ≤ 1 * e := mul_le_mul_of_nonneg_right (norm_cyclotomicCoefficientMap_le_one k p _)
          (norm_nonneg _)
      _ = e := one_mul _
      _ < 1 := he
  have hRone : ‖R‖ = 1 := norm_eq_one_of_norm_sub_one_lt k p (lt_of_le_of_lt hRnorm hde)
  have hym : ‖artinHasseEvalAt k p D (dworkArtinHasseParameter k p ^ p ^ m) - 1‖
      ≤ max (d * e) (e ^ p ^ (m + 1)) := by
    have hz : ‖dworkArtinHasseParameter k p ^ p ^ m‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg _) he (pow_pos (Fact.out : Nat.Prime p).pos _).ne'
    have hb := norm_artinHasseEvalAt_sub_one_le k p D hz
    rw [norm_pow] at hb
    refine le_trans hb (max_le_max ?_ (le_of_eq ?_))
    · refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      calc e ^ p ^ m ≤ e ^ 1 :=
            pow_le_pow_of_le_one (norm_nonneg _) he.le
              (Nat.one_le_pow _ _ (Fact.out : Nat.Prime p).pos)
        _ = e := pow_one _
    · rw [← pow_mul, ← pow_succ]
  have hkey : ρ ^ m * ‖y - 1‖ ≤ max (d * e) (e ^ p ^ (m + 1)) := by
    have hexpand : artinHasseEvalAt k p D (dworkArtinHasseParameter k p ^ p ^ m) - 1
        = (y ^ p ^ m - 1) * R + (R - 1) := by rw [hR]; ring
    have hnorm : ‖(y ^ p ^ m - 1) * R‖ ≤ max (d * e) (e ^ p ^ (m + 1)) := by
      have hsub : (y ^ p ^ m - 1) * R
          = (artinHasseEvalAt k p D (dworkArtinHasseParameter k p ^ p ^ m) - 1) - (R - 1) := by
        rw [hexpand]; ring
      rw [hsub, sub_eq_add_neg]
      refine le_trans (norm_add_le_max _ _) ?_
      rw [norm_neg]
      exact max_le hym (le_trans hRnorm (le_max_left _ _))
    rw [norm_mul, hRone, mul_one, norm_pow_pPow_sub_one_eq k p m hsmall] at hnorm
    exact hnorm
  have hbound : max (d * e) (e ^ p ^ (m + 1)) ≤ ρ ^ (2 * m) := by
    refine max_le ?_ ?_
    · calc d * e ≤ ρ ^ (2 * m + 2) * 1 :=
            mul_le_mul hD0 he.le (norm_nonneg _) (by positivity)
        _ = ρ ^ (2 * m + 2) := mul_one _
        _ ≤ ρ ^ (2 * m) := pow_le_pow_of_le_one (le_of_lt hrho0) hrho1.le (by omega)
    · calc e ^ p ^ (m + 1) ≤ e ^ (2 * m * (p - 1)) :=
            pow_le_pow_of_le_one (norm_nonneg _) he.le (two_mul_le_pow_succ p m)
        _ = (e ^ (p - 1)) ^ (2 * m) := by rw [← pow_mul, Nat.mul_comm]
        _ ≤ ρ ^ (2 * m) := pow_le_pow_left₀ (by positivity) hepow (2 * m)
  have hfinal : ρ ^ m * ‖y - 1‖ ≤ ρ ^ m * ρ ^ m := by
    calc ρ ^ m * ‖y - 1‖ ≤ ρ ^ (2 * m) := le_trans hkey hbound
      _ = ρ ^ m * ρ ^ m := by rw [← pow_add, two_mul]
  exact le_of_mul_le_mul_left hfinal (by positivity)
