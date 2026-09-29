-- Prove2me | solution 1 for DrinfeldCurve.LocalChart.branchPrimes_of_sub_drinfeldForm_mem_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/1066ddb0-867e-5245-8744-775237893be7

import Mathlib
import Definitions.Def_DrinfeldCurve_LocalChart
import Theorems.Thm_DrinfeldCurve_LocalChart_card_eq_and_prod_linear_eq_drinfeldForm_and_isUnit_det_of_prod_X_sub_C_eq
import Theorems.Thm_MvPowerSeries_exists_isUnit_mul_prod_eq_of_sub_prod_linear_mem_pow
import Theorems.Thm_MvPowerSeries_span_singleton_isPrime_of_sub_linear_mem_sq
import Theorems.Thm_MvPowerSeries_exists_ringEquiv_quotient_quotient_span_C_of_maximalIdeal_eq_span
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DrinfeldCurve_LocalChart_branchPrimes_of_sub_drinfeldForm_mem_pow

set_option autoImplicit false

namespace ChartBranchesGC7

open MvPowerSeries IsLocalRing

theorem map_residue_surjective (W : Type) [CommRing W] [IsLocalRing W] {σ : Type} :
    Function.Surjective (MvPowerSeries.map (σ := σ) (residue W)) := by
  intro g
  choose p hp using fun e : σ →₀ ℕ => residue_surjective (coeff e g)
  exact ⟨fun e => p e, by ext e; rw [coeff_map]; exact hp e⟩

theorem map_span_X_pow {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (k : ℕ) :
    ((Ideal.span {(X 0 : MvPowerSeries (Fin 2) R), X 1}) ^ k).map (MvPowerSeries.map φ) =
      (Ideal.span {(X 0 : MvPowerSeries (Fin 2) S), X 1}) ^ k := by
  rw [Ideal.map_pow, Ideal.map_span, Set.image_insert_eq, Set.image_singleton, map_X, map_X]

theorem prod_X_sub_C_image_castHom (q : ℕ) [hq : Fact q.Prime] (κ : Type) [Field κ] [DecidableEq κ] [CharP κ q] :
    ∏ t ∈ (Finset.univ.image (ZMod.castHom (dvd_refl q) κ)), (Polynomial.X - Polynomial.C t) =
      (Polynomial.X ^ q - Polynomial.X : Polynomial κ) := by
  classical
  let φ : ZMod q →+* κ := ZMod.castHom (dvd_refl q) κ
  have hφ : Function.Injective φ := φ.injective
  show ∏ t ∈ (Finset.univ.image φ), (Polynomial.X - Polynomial.C t) = _
  rw [Finset.prod_image fun x _ y _ h => hφ h]
  have h1 : (Polynomial.X ^ q - Polynomial.X : Polynomial (ZMod q)) =
      ∏ a : ZMod q, (Polynomial.X - Polynomial.C a) := by
    have hq1 : 1 < q := hq.out.one_lt
    have hm : (Polynomial.X ^ q - Polynomial.X : Polynomial (ZMod q)).Monic :=
      (Polynomial.monic_X_pow q).sub_of_left
        (by rw [Polynomial.degree_X, Polynomial.degree_X_pow]; exact_mod_cast hq1)
    have hr : (Polynomial.X ^ q - Polynomial.X : Polynomial (ZMod q)).roots = Finset.univ.val := by
      have := FiniteField.roots_X_pow_card_sub_X (ZMod q)
      rwa [ZMod.card] at this
    have hcard : Multiset.card (Polynomial.X ^ q - Polynomial.X : Polynomial (ZMod q)).roots =
        (Polynomial.X ^ q - Polynomial.X : Polynomial (ZMod q)).natDegree := by
      rw [hr, FiniteField.X_pow_card_sub_X_natDegree_eq (ZMod q) hq1]
      simp [ZMod.card]
    rw [← Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm hcard, hr,
      Finset.prod_eq_multiset_prod]
  have := congrArg (Polynomial.map φ) h1
  rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_prod] at this
  rw [this]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]

theorem cross_eq_zero_of_parallel {κ : Type} [Field κ] (A B x₁ y₁ x₂ y₂ : κ) (hAB : A ≠ 0 ∨ B ≠ 0)
    (h₁ : A * y₁ - x₁ * B = 0) (h₂ : A * y₂ - x₂ * B = 0) : x₁ * y₂ - x₂ * y₁ = 0 := by
  rcases hAB with hA | hB
  · have : (x₁ * y₂ - x₂ * y₁) * A = 0 := by linear_combination x₁ * h₂ - x₂ * h₁
    exact (mul_eq_zero.mp this).resolve_right hA
  · have : (x₁ * y₂ - x₂ * y₁) * B = 0 := by linear_combination y₁ * h₂ - y₂ * h₁
    exact (mul_eq_zero.mp this).resolve_right hB

end ChartBranchesGC7

open ChartBranchesGC7 MvPowerSeries IsLocalRing in
theorem solution
    (q : ℕ) [Fact q.Prime]
    (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (π : W) (hπ : IsLocalRing.maximalIdeal W = Ideal.span {π})
    (hqW : (q : W) ∈ IsLocalRing.maximalIdeal W)
    (c : W) (hc : c ∈ IsLocalRing.maximalIdeal W) (hc0 : c ≠ 0)
    (f u v : MvPowerSeries (Fin 2) W) (hu : IsUnit u) (hv : IsUnit v)
    (hf : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
      (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (q + 2)) :
    let S := (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C c * v - f * u})
    let mkS : MvPowerSeries (Fin 2) W →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C c * v - f * u})

    (∀ a b : ℤ, ¬ ((q : ℤ) ∣ a ∧ (q : ℤ) ∣ b) →
      ∃ P : Ideal S, P.IsPrime ∧ (mkS (MvPowerSeries.X 0) ∉ P ∨ mkS (MvPowerSeries.X 1) ∉ P) ∧
        mkS (MvPowerSeries.C π) ∈ P ∧
        ∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ 2,
          mkS (MvPowerSeries.C ((a : ℤ) : W) * MvPowerSeries.X 0 + MvPowerSeries.C ((b : ℤ) : W) * MvPowerSeries.X 1 + h) ∈ P) ∧

    (∀ P : Ideal S, P.IsPrime → (mkS (MvPowerSeries.X 0) ∉ P ∨ mkS (MvPowerSeries.X 1) ∉ P) →
      mkS (MvPowerSeries.C π) ∈ P →
        ∃ a b : ℤ, ¬ ((q : ℤ) ∣ a ∧ (q : ℤ) ∣ b) ∧
          ∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ 2,
            mkS (MvPowerSeries.C ((a : ℤ) : W) * MvPowerSeries.X 0 + MvPowerSeries.C ((b : ℤ) : W) * MvPowerSeries.X 1 + h) ∈ P) ∧

    (∀ (a₁ b₁ a₂ b₂ : ℤ) (P₁ P₂ : Ideal S), P₁.IsPrime → P₂.IsPrime →
      (mkS (MvPowerSeries.X 0) ∉ P₁ ∨ mkS (MvPowerSeries.X 1) ∉ P₁) →
      (mkS (MvPowerSeries.X 0) ∉ P₂ ∨ mkS (MvPowerSeries.X 1) ∉ P₂) →
      mkS (MvPowerSeries.C π) ∈ P₁ → mkS (MvPowerSeries.C π) ∈ P₂ →
      (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ 2,
          mkS (MvPowerSeries.C ((a₁ : ℤ) : W) * MvPowerSeries.X 0 + MvPowerSeries.C ((b₁ : ℤ) : W) * MvPowerSeries.X 1 + h) ∈ P₁) →
      (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ 2,
          mkS (MvPowerSeries.C ((a₂ : ℤ) : W) * MvPowerSeries.X 0 + MvPowerSeries.C ((b₂ : ℤ) : W) * MvPowerSeries.X 1 + h) ∈ P₂) →
      ¬ ((q : ℤ) ∣ a₁ ∧ (q : ℤ) ∣ b₁) → ¬ ((q : ℤ) ∣ a₂ ∧ (q : ℤ) ∣ b₂) →
      (P₁ = P₂ ↔ (q : ℤ) ∣ a₁ * b₂ - a₂ * b₁)) ∧

    (∀ P : Ideal S, P.IsPrime → (mkS (MvPowerSeries.X 0) ∉ P ∨ mkS (MvPowerSeries.X 1) ∉ P) →
      mkS (MvPowerSeries.C π) ∈ P →
        ∀ s : S, s ∈ P → ∃ r : S, r ∉ P ∧ ∃ s' : S, r * s = mkS (MvPowerSeries.C π) * s') := by
  intro S mkS
  classical
  obtain ⟨hqprime⟩ := ‹Fact q.Prime›

  haveI : CharP (ResidueField W) q := by
    refine (CharP.charP_iff_prime_eq_zero hqprime).mpr ?_
    rw [← map_natCast (residue W), residue_eq_zero_iff]; exact hqW
  set red : MvPowerSeries (Fin 2) W →+* MvPowerSeries (Fin 2) (ResidueField W) :=
    MvPowerSeries.map (residue W) with hred
  have hredsurj : Function.Surjective red := map_residue_surjective W
  set g : MvPowerSeries (Fin 2) W := C c * v - f * u with hg

  obtain ⟨e, he⟩ := MvPowerSeries.exists_ringEquiv_quotient_quotient_span_C_of_maximalIdeal_eq_span π hπ g
  set πS : S →+* S ⧸ Ideal.span {mkS (C π)} := Ideal.Quotient.mk _ with hπS
  set ρ : MvPowerSeries (Fin 2) (ResidueField W) →+* _ ⧸ Ideal.span {red g} := Ideal.Quotient.mk _ with hρ
  have hΘ : ∀ p, e (πS (mkS p)) = ρ (red p) := he
  have hmkS : Function.Surjective mkS := Ideal.Quotient.mk_surjective
  have hπS' : Function.Surjective πS := Ideal.Quotient.mk_surjective
  have hρ' : Function.Surjective ρ := Ideal.Quotient.mk_surjective
  have hkerπS : RingHom.ker πS = Ideal.span {mkS (C π)} := Ideal.mk_ker
  have hkerρ : RingHom.ker ρ = Ideal.span {red g} := Ideal.mk_ker

  have dict : ∀ P : Ideal S, P.IsPrime → mkS (C π) ∈ P →
      ∃ Q : Ideal (MvPowerSeries (Fin 2) (ResidueField W)), Q.IsPrime ∧ red g ∈ Q ∧
        ∀ x, mkS x ∈ P ↔ red x ∈ Q := by
    intro P hP hπP
    have hk : RingHom.ker πS ≤ P := by
      rw [hkerπS, Ideal.span_singleton_le_iff_mem]; exact hπP
    haveI : (P.map πS).IsPrime := Ideal.map_isPrime_of_surjective hπS' hk
    haveI : ((P.map πS).map e).IsPrime := Ideal.map_isPrime_of_equiv e
    have key : ∀ x, mkS x ∈ P ↔ red x ∈ ((P.map πS).map e).comap ρ := by
      intro x
      rw [Ideal.mem_comap, ← hΘ, Ideal.apply_mem_of_equiv_iff]
      change _ ↔ mkS x ∈ Ideal.comap πS (Ideal.map πS P)
      rw [Ideal.comap_map_of_surjective _ hπS', ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hk]
    refine ⟨((P.map πS).map e).comap ρ, Ideal.comap_isPrime _ _, ?_, key⟩
    have : red g ∈ RingHom.ker ρ := by rw [hkerρ]; exact Ideal.mem_span_singleton_self _
    rw [Ideal.mem_comap, RingHom.mem_ker.mp this]
    exact Ideal.zero_mem _
  have dict' : ∀ Q : Ideal (MvPowerSeries (Fin 2) (ResidueField W)), Q.IsPrime → red g ∈ Q →
      ∃ P : Ideal S, P.IsPrime ∧ mkS (C π) ∈ P ∧ ∀ x, mkS x ∈ P ↔ red x ∈ Q := by
    intro Q hQ hgQ
    have hk : RingHom.ker ρ ≤ Q := by
      rw [hkerρ, Ideal.span_singleton_le_iff_mem]; exact hgQ
    haveI : (Q.map ρ).IsPrime := Ideal.map_isPrime_of_surjective hρ' hk
    refine ⟨(Q.map ρ).comap ((e : _ →+* _).comp πS), Ideal.comap_isPrime _ _, ?_, ?_⟩
    · rw [Ideal.mem_comap, RingHom.comp_apply]
      have : πS (mkS (C π)) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
      rw [this, map_zero]; exact Ideal.zero_mem _
    · intro x
      rw [Ideal.mem_comap, RingHom.comp_apply, RingHom.coe_coe, hΘ]
      change ρ (red x) ∈ Ideal.map ρ Q ↔ _
      rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective _ hρ', ← RingHom.ker_eq_comap_bot,
        sup_eq_left.mpr hk]

  have Pext : ∀ P₁ P₂ : Ideal S, (∀ x, mkS x ∈ P₁ ↔ mkS x ∈ P₂) → P₁ = P₂ := by
    intro P₁ P₂ h; ext s; obtain ⟨x, rfl⟩ := hmkS s; exact h x
  have Qext : ∀ Q₁ Q₂ : Ideal (MvPowerSeries (Fin 2) (ResidueField W)),
      (∀ x, red x ∈ Q₁ ↔ red x ∈ Q₂) → Q₁ = Q₂ := by
    intro Q₁ Q₂ h; ext s; obtain ⟨x, rfl⟩ := hredsurj s; exact h x

  let φ : ZMod q →+* ResidueField W := ZMod.castHom (dvd_refl q) (ResidueField W)
  let T : Finset (ResidueField W) := Finset.univ.image φ
  have hT := prod_X_sub_C_image_castHom q (ResidueField W)
  obtain ⟨hTcard, hprod, hdet⟩ :=
    DrinfeldCurve.LocalChart.card_eq_and_prod_linear_eq_drinfeldForm_and_isUnit_det_of_prod_X_sub_C_eq
      q (ResidueField W) T hT
  have hTu : ∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → IsUnit (t - t') :=
    fun t _ t' _ h => isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr h)
  let A : Option ↥T → ResidueField W := fun i => Option.elim i (1 : ResidueField W) (fun t => -(t : ResidueField W))
  let B : Option ↥T → ResidueField W := fun i => Option.elim i (0 : ResidueField W) (fun _ => (1 : ResidueField W))
  have hAB : ∀ i j : Option ↥T, i ≠ j → A i * B j - A j * B i ≠ 0 := fun i j h => (hdet hTu i j h).ne_zero
  have hAB0 : ∀ i : Option ↥T, A i ≠ 0 ∨ B i ≠ 0 := by
    intro i; cases i
    · exact Or.inl one_ne_zero
    · exact Or.inr one_ne_zero
  have hcard : Fintype.card (Option ↥T) + 1 = q + 2 := by
    rw [Fintype.card_option, Fintype.card_coe, hTcard]
  have hdf : red (DrinfeldCurve.LocalChart.drinfeldForm q W) = DrinfeldCurve.LocalChart.drinfeldForm q (ResidueField W) := by
    show red (X 0 * X 1 ^ q - X 0 ^ q * X 1) = X 0 * X 1 ^ q - X 0 ^ q * X 1
    simp only [map_sub, map_mul, map_pow, MvPowerSeries.map_X, red]
  have hfbar : red f - ∏ i, (C (A i) * X 0 + C (B i) * X 1) ∈
      (Ideal.span {(X 0 : MvPowerSeries (Fin 2) (ResidueField W)), X 1}) ^ (Fintype.card (Option ↥T) + 1) := by
    rw [hcard, hprod, ← hdf, ← map_sub, ← map_span_X_pow (residue W) (q + 2)]
    exact Ideal.mem_map_of_mem _ hf
  obtain ⟨L, w, hw, hL, hfac⟩ := MvPowerSeries.exists_isUnit_mul_prod_eq_of_sub_prod_linear_mem_pow A B hAB (red f) hfbar
  have hR := fun i => MvPowerSeries.span_singleton_isPrime_of_sub_linear_mem_sq (A i) (B i) (hAB0 i) (L i) (hL i)

  have hcbar : residue W c = 0 := (residue_eq_zero_iff c).mpr hc
  have hredg : red g = -(red u * w) * ∏ i, L i := by
    simp only [g, red, map_sub, map_mul, MvPowerSeries.map_C, hcbar, map_zero, zero_mul, zero_sub]
    rw [show (MvPowerSeries.map (residue W)) f = red f from rfl, hfac]; ring
  have hunit : IsUnit (-(red u * w)) := ((hu.map red).mul hw).neg

  have K1 : ∀ Q : Ideal (MvPowerSeries (Fin 2) (ResidueField W)), Q.IsPrime →
      (red g ∈ Q ↔ ∃ i, L i ∈ Q) := by
    intro Q hQ
    rw [hredg, Ideal.unit_mul_mem_iff_mem Q hunit]
    constructor
    · intro h
      obtain ⟨i, -, hi⟩ := (hQ.prod_mem_iff (s := Finset.univ) (x := L)).mp h
      exact ⟨i, hi⟩
    · rintro ⟨i, hi⟩
      obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem L (Finset.mem_univ i)
      rw [hm]; exact Q.mul_mem_right _ hi

  have K3 : ∀ i j, L i ∈ Ideal.span {L j} → i = j := by
    intro i j h
    by_contra hij
    have h4 := (hR j).2.2.2 (A i) (B i) (L i - (C (A i) * X 0 + C (B i) * X 1)) (hL i)
      (by rw [add_sub_cancel]; exact h)
    exact hAB j i (Ne.symm hij) h4

  have K4 : ∀ Q : Ideal (MvPowerSeries (Fin 2) (ResidueField W)), Q.IsPrime → red g ∈ Q →
      ((X 0 : MvPowerSeries (Fin 2) (ResidueField W)) ∉ Q ∨ (X 1 : MvPowerSeries (Fin 2) (ResidueField W)) ∉ Q) →
      ∃ j, Q = Ideal.span {L j} := by
    intro Q hQ hgQ hnm
    obtain ⟨j, hj⟩ := (K1 Q hQ).mp hgQ
    exact ⟨j, (hR j).2.2.1 Q hQ hj hnm⟩

  have lift2 : ∀ hbar ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) (ResidueField W)), X 1}) ^ 2,
      ∃ h ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1}) ^ 2, red h = hbar := by
    intro hbar hh
    rw [← map_span_X_pow (residue W) 2] at hh
    obtain ⟨h, hh1, hh2⟩ := (Ideal.mem_map_iff_of_surjective _ hredsurj).mp hh
    exact ⟨h, hh1, hh2⟩

  have hredlin : ∀ (a b : ℤ) (h : MvPowerSeries (Fin 2) W),
      red (C ((a : ℤ) : W) * X 0 + C ((b : ℤ) : W) * X 1 + h) =
        C ((a : ℤ) : ResidueField W) * X 0 + C ((b : ℤ) : ResidueField W) * X 1 + red h := by
    intro a b h
    simp only [red, map_add, map_mul, MvPowerSeries.map_C, MvPowerSeries.map_X, map_intCast]

  have hφint : ∀ n : ℤ, ((n : ℤ) : ResidueField W) = φ (n : ZMod q) := fun n => (map_intCast φ n).symm
  have hcast0 : ∀ n : ℤ, ((n : ℤ) : ResidueField W) = 0 ↔ (q : ℤ) ∣ n := fun n =>
    CharP.intCast_eq_zero_iff (ResidueField W) q n
  have hredX : ∀ k : Fin 2, red (X k) = X k := fun k => MvPowerSeries.map_X (residue W) k
  have nm_transfer : ∀ (P : Ideal S) (Q : Ideal (MvPowerSeries (Fin 2) (ResidueField W))),
      (∀ x, mkS x ∈ P ↔ red x ∈ Q) → (mkS (X 0) ∉ P ∨ mkS (X 1) ∉ P) →
      ((X 0 : MvPowerSeries (Fin 2) (ResidueField W)) ∉ Q ∨ (X 1 : MvPowerSeries (Fin 2) (ResidueField W)) ∉ Q) := by
    intro P Q hmem hnm
    rcases hnm with h0 | h1
    · left; rwa [hmem, hredX] at h0
    · right; rwa [hmem, hredX] at h1
  have nm_transfer' : ∀ (P : Ideal S) (Q : Ideal (MvPowerSeries (Fin 2) (ResidueField W))),
      (∀ x, mkS x ∈ P ↔ red x ∈ Q) →
      ((X 0 : MvPowerSeries (Fin 2) (ResidueField W)) ∉ Q ∨ (X 1 : MvPowerSeries (Fin 2) (ResidueField W)) ∉ Q) →
      (mkS (X 0) ∉ P ∨ mkS (X 1) ∉ P) := by
    intro P Q hmem hnm
    rcases hnm with h0 | h1
    · left; rwa [hmem, hredX]
    · right; rwa [hmem, hredX]
  have red_mem_sq : ∀ h ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1}) ^ 2,
      red h ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) (ResidueField W)), X 1}) ^ 2 := by
    intro h hh
    rw [← map_span_X_pow (residue W) 2]
    exact Ideal.mem_map_of_mem _ hh
  haveI : NeZero q := ⟨hqprime.ne_zero⟩
  have hq1 : ¬ (q : ℤ) ∣ 1 := by
    intro h
    have h' := Int.eq_one_of_dvd_one (Int.natCast_nonneg q) h
    norm_cast at h'
    exact hqprime.one_lt.ne' h'

  have hrep : ∀ j : Option ↥T, ∃ a b : ℤ, ¬ ((q : ℤ) ∣ a ∧ (q : ℤ) ∣ b) ∧
      ((a : ℤ) : ResidueField W) = A j ∧ ((b : ℤ) : ResidueField W) = B j := by
    intro j
    cases j with
    | none => exact ⟨1, 0, fun h => hq1 h.1, by simp [A], by simp [B]⟩
    | some t =>
      obtain ⟨γ, -, hγ⟩ := Finset.mem_image.mp t.2
      refine ⟨-(γ.val : ℤ), 1, fun h => hq1 h.2, ?_, by simp [B]⟩
      show ((-(γ.val : ℤ) : ℤ) : ResidueField W) = -(t : ResidueField W)
      rw [← hγ, Int.cast_neg, Int.cast_natCast, ZMod.castHom_apply, ZMod.cast_eq_val]

  have Edata : ∀ (P : Ideal S) (j : Option ↥T) (a b : ℤ), (∀ x, mkS x ∈ P ↔ red x ∈ Ideal.span {L j}) →
      (∃ h ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1}) ^ 2,
        mkS (C ((a : ℤ) : W) * X 0 + C ((b : ℤ) : W) * X 1 + h) ∈ P) →
      A j * ((b : ℤ) : ResidueField W) - ((a : ℤ) : ResidueField W) * B j = 0 := by
    intro P j a b hmem hh
    obtain ⟨h, hh, hmemP⟩ := hh
    rw [hmem, hredlin] at hmemP
    exact (hR j).2.2.2 _ _ (red h) (red_mem_sq h hh) hmemP
  refine ⟨?_, ?_, ?_, ?_⟩

  · intro a b hab
    have hne : ((a : ℤ) : ResidueField W) ≠ 0 ∨ ((b : ℤ) : ResidueField W) ≠ 0 := by
      by_contra h
      push Not at h
      exact hab ⟨(hcast0 a).mp h.1, (hcast0 b).mp h.2⟩
    obtain ⟨j, lam, hja, hjb⟩ : ∃ (j : Option ↥T) (lam : ResidueField W),
        ((a : ℤ) : ResidueField W) = lam * A j ∧ ((b : ℤ) : ResidueField W) = lam * B j := by
      by_cases hb0 : ((b : ℤ) : ResidueField W) = 0
      · exact ⟨none, ((a : ℤ) : ResidueField W), by simp [A], by simp [B, hb0]⟩
      · let γ : ZMod q := -((a : ZMod q) * (b : ZMod q)⁻¹)
        have ht : φ γ ∈ T := Finset.mem_image_of_mem φ (Finset.mem_univ γ)
        refine ⟨some ⟨φ γ, ht⟩, ((b : ℤ) : ResidueField W), ?_, by simp [B]⟩
        show ((a : ℤ) : ResidueField W) = ((b : ℤ) : ResidueField W) * -(φ γ)
        simp only [γ, map_neg, map_mul, map_inv₀, ← hφint, neg_neg]
        field_simp
    obtain ⟨P, hP, hπP, hmem⟩ := dict' (Ideal.span {L j}) (hR j).1
      ((K1 _ (hR j).1).mpr ⟨j, Ideal.mem_span_singleton_self _⟩)
    refine ⟨P, hP, nm_transfer' P _ hmem (hR j).2.1, hπP, ?_⟩
    obtain ⟨h, hh, hredh⟩ := lift2 (C lam * (L j - (C (A j) * X 0 + C (B j) * X 1)))
      (Ideal.mul_mem_left _ _ (hL j))
    refine ⟨h, hh, ?_⟩
    rw [hmem, hredlin, hredh, hja, hjb]
    have : C (lam * A j) * X 0 + C (lam * B j) * X 1 + C lam * (L j - (C (A j) * X 0 + C (B j) * X 1)) =
        C lam * L j := by
      simp only [map_mul]; ring
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

  · intro P hP hnm hπP
    obtain ⟨Q, hQ, hgQ, hmem⟩ := dict P hP hπP
    obtain ⟨j, hQj⟩ := K4 Q hQ hgQ (nm_transfer P Q hmem hnm)
    obtain ⟨a, b, hab, hja, hjb⟩ := hrep j
    refine ⟨a, b, hab, ?_⟩
    obtain ⟨h, hh, hredh⟩ := lift2 (L j - (C (A j) * X 0 + C (B j) * X 1)) (hL j)
    refine ⟨h, hh, ?_⟩
    rw [hmem, hredlin, hredh, hja, hjb, add_sub_cancel, hQj]
    exact Ideal.mem_span_singleton_self _

  · intro a₁ b₁ a₂ b₂ P₁ P₂ hP₁ hP₂ hnm₁ hnm₂ hπ₁ hπ₂ hh₁ hh₂ hab₁ hab₂
    obtain ⟨Q₁, hQ₁, hgQ₁, hmem₁⟩ := dict P₁ hP₁ hπ₁
    obtain ⟨Q₂, hQ₂, hgQ₂, hmem₂⟩ := dict P₂ hP₂ hπ₂
    obtain ⟨j₁, hQj₁⟩ := K4 Q₁ hQ₁ hgQ₁ (nm_transfer P₁ Q₁ hmem₁ hnm₁)
    obtain ⟨j₂, hQj₂⟩ := K4 Q₂ hQ₂ hgQ₂ (nm_transfer P₂ Q₂ hmem₂ hnm₂)
    subst hQj₁ hQj₂
    have E1 := Edata P₁ j₁ a₁ b₁ hmem₁ hh₁
    have E2 := Edata P₂ j₂ a₂ b₂ hmem₂ hh₂
    have hne₁ : ((a₁ : ℤ) : ResidueField W) ≠ 0 ∨ ((b₁ : ℤ) : ResidueField W) ≠ 0 := by
      by_contra h; push Not at h; exact hab₁ ⟨(hcast0 a₁).mp h.1, (hcast0 b₁).mp h.2⟩
    have hne₂ : ((a₂ : ℤ) : ResidueField W) ≠ 0 ∨ ((b₂ : ℤ) : ResidueField W) ≠ 0 := by
      by_contra h; push Not at h; exact hab₂ ⟨(hcast0 a₂).mp h.1, (hcast0 b₂).mp h.2⟩
    have hPQ : P₁ = P₂ ↔ j₁ = j₂ := by
      constructor
      · intro hP
        subst hP
        apply K3
        have : Ideal.span {L j₁} = Ideal.span {L j₂} :=
          Qext _ _ fun x => (hmem₁ x).symm.trans (hmem₂ x)
        rw [← this]; exact Ideal.mem_span_singleton_self _
      · intro hj
        subst hj
        exact Pext _ _ fun x => (hmem₁ x).trans (hmem₂ x).symm
    rw [hPQ, ← hcast0, Int.cast_sub, Int.cast_mul, Int.cast_mul]
    constructor
    · intro hj
      subst hj
      exact cross_eq_zero_of_parallel (A j₁) (B j₁) _ _ _ _ (hAB0 j₁) E1 E2
    · intro hpar
      by_contra hj
      apply hAB j₁ j₂ hj

      have F2 : ((a₁ : ℤ) : ResidueField W) * B j₂ - A j₂ * ((b₁ : ℤ) : ResidueField W) = 0 := by
        have G := cross_eq_zero_of_parallel ((a₂ : ℤ) : ResidueField W) ((b₂ : ℤ) : ResidueField W)
          (A j₂) (B j₂) ((a₁ : ℤ) : ResidueField W) ((b₁ : ℤ) : ResidueField W) hne₂
          (by linear_combination (-1 : ResidueField W) * E2) (by linear_combination (-1 : ResidueField W) * hpar)
        linear_combination (-1 : ResidueField W) * G
      have F1 : ((a₁ : ℤ) : ResidueField W) * B j₁ - A j₁ * ((b₁ : ℤ) : ResidueField W) = 0 := by
        linear_combination (-1 : ResidueField W) * E1
      exact cross_eq_zero_of_parallel _ _ (A j₁) (B j₁) (A j₂) (B j₂) hne₁ F1 F2

  · intro P hP hnm hπP s hs
    obtain ⟨Q, hQ, hgQ, hmem⟩ := dict P hP hπP
    obtain ⟨j, hQj⟩ := K4 Q hQ hgQ (nm_transfer P Q hmem hnm)
    subst hQj
    obtain ⟨x, rfl⟩ := hmkS s
    have hx : red x ∈ Ideal.span {L j} := (hmem x).mp hs
    obtain ⟨m, hm⟩ := Ideal.mem_span_singleton'.mp hx
    obtain ⟨y₀, hy₀⟩ := hredsurj (∏ i ∈ Finset.univ.erase j, L i)
    refine ⟨mkS y₀, ?_, ?_⟩
    · rw [hmem, hy₀]
      intro hmemj
      obtain ⟨i, hi, hiL⟩ := ((hR j).1.prod_mem_iff (s := Finset.univ.erase j) (x := L)).mp hmemj
      exact (Finset.mem_erase.mp hi).1 (K3 i j hiL)
    · have hker : mkS (y₀ * x) ∈ Ideal.span {mkS (C π)} := by
        rw [← hkerπS, RingHom.mem_ker, ← e.map_eq_zero_iff, hΘ, ← RingHom.mem_ker, hkerρ, map_mul, hy₀,
          ← hm, hredg, Ideal.span_singleton_mul_left_unit hunit]
        refine Ideal.mem_span_singleton'.mpr ⟨m, ?_⟩
        rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
        ring
      obtain ⟨s', hs'⟩ := Ideal.mem_span_singleton'.mp hker
      exact ⟨s', by rw [← map_mul, ← hs', mul_comm]⟩

end S_DrinfeldCurve_LocalChart_branchPrimes_of_sub_drinfeldForm_mem_pow
end P2MW
export P2MW.S_DrinfeldCurve_LocalChart_branchPrimes_of_sub_drinfeldForm_mem_pow (solution)
