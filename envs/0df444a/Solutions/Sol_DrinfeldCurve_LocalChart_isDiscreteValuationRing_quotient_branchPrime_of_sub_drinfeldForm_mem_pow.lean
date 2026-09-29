-- Prove2me | solution 1 for DrinfeldCurve.LocalChart.isDiscreteValuationRing_quotient_branchPrime_of_sub_drinfeldForm_mem_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/6e3685e7-e6b6-55e0-a752-489a33b7db95

import Mathlib
import Definitions.Def_DrinfeldCurve_LocalChart
import Theorems.Thm_DrinfeldCurve_LocalChart_card_eq_and_prod_linear_eq_drinfeldForm_and_isUnit_det_of_prod_X_sub_C_eq
import Theorems.Thm_MvPowerSeries_exists_isUnit_mul_prod_eq_of_sub_prod_linear_mem_pow
import Theorems.Thm_MvPowerSeries_span_singleton_isPrime_of_sub_linear_mem_sq
import Theorems.Thm_MvPowerSeries_exists_ringEquiv_quotient_quotient_span_C_of_maximalIdeal_eq_span
import Theorems.Thm_MvPowerSeries_mem_span_X_pow_iff_forall_coeff_eq_zero_of_degree_lt
import Theorems.Thm_MvPowerSeries_isNoetherianRing_of_finite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DrinfeldCurve_LocalChart_isDiscreteValuationRing_quotient_branchPrime_of_sub_drinfeldForm_mem_pow

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

namespace B2_node13

open IsLocalRing

theorem maximalIdeal_eq_span_singleton_of_rel {T : Type} [CommRing T] [IsLocalRing T]
    (x y u c h : T) (hu : IsUnit u)
    (hN : Ideal.span {x, y} = maximalIdeal T)
    (hh : h ∈ (Ideal.span {x, y}) ^ 2)
    (hrel : u * x + c * y + h = 0) :
    maximalIdeal T = Ideal.span {y} := by
  have hfg : (Ideal.span {x, y} : Ideal T).FG := Submodule.fg_span ((Set.finite_singleton y).insert x)
  have hIJ : (Ideal.span {x, y} : Ideal T) ≤ Ideal.jacobson ⊥ := hN ▸ maximalIdeal_le_jacobson ⊥
  have hx : x ∈ Ideal.span {y} ⊔ Ideal.span {x, y} • Ideal.span {x, y} := by
    obtain ⟨w, rfl⟩ := hu
    have hx' : (w : T) * x = -(c * y) - h := by linear_combination hrel
    have hxeq : x = (w⁻¹ : Tˣ) * (-(c * y) - h) := by rw [← hx', Units.inv_mul_cancel_left]
    have hmem : ((w⁻¹ : Tˣ) : T) * (-(c * y) - h) ∈ Ideal.span {y} ⊔ Ideal.span {x, y} • Ideal.span {x, y} := by
      refine Ideal.mul_mem_left _ _ (Submodule.sub_mem _ ?_ ?_)
      · exact Submodule.mem_sup_left (Submodule.neg_mem _ (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self y)))
      · apply Submodule.mem_sup_right
        rw [Ideal.smul_eq_mul, ← pow_two]
        exact hh
    rw [← hxeq] at hmem
    exact hmem
  have hNN : (Ideal.span {x, y} : Ideal T) ≤ Ideal.span {y} ⊔ Ideal.span {x, y} • Ideal.span {x, y} := by
    rw [Ideal.span_le]
    rintro z hz
    rcases hz with rfl | hz
    · exact hx
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      exact Submodule.mem_sup_left (Ideal.mem_span_singleton_self _)
  have hle : (Ideal.span {x, y} : Ideal T) ≤ Ideal.span {y} :=
    Submodule.le_of_le_smul_of_le_jacobson_bot hfg hIJ hNN
  rw [← hN]
  refine le_antisymm hle ?_
  rw [Ideal.span_singleton_le_iff_mem]
  exact Ideal.subset_span (by simp)

end B2_node13

open ChartBranchesGC7 MvPowerSeries IsLocalRing in
theorem B2_node13.core
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
    ∀ (P : Ideal S) [P.IsPrime], (mkS (MvPowerSeries.X 0) ∉ P ∨ mkS (MvPowerSeries.X 1) ∉ P) →
      mkS (MvPowerSeries.C π) ∈ P → IsDiscreteValuationRing (S ⧸ P) := by
  intro S mkS P _instP hnm hπP
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

  obtain ⟨Q, hQ, hgQ, hmem⟩ := dict P _instP hπP
  obtain ⟨j, hQj⟩ := K4 Q hQ hgQ (nm_transfer P Q hmem hnm)
  subst hQj
  haveI hLprime : (Ideal.span {L j}).IsPrime := (hR j).1
  haveI : IsNoetherianRing (MvPowerSeries (Fin 2) (ResidueField W)) := MvPowerSeries.isNoetherianRing_of_finite
  haveI : Nontrivial (MvPowerSeries (Fin 2) (ResidueField W) ⧸ Ideal.span {L j}) :=
    Ideal.Quotient.nontrivial_iff.mpr hLprime.ne_top
  haveI : IsLocalRing (MvPowerSeries (Fin 2) (ResidueField W) ⧸ Ideal.span {L j}) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  set mkT : MvPowerSeries (Fin 2) (ResidueField W) →+* MvPowerSeries (Fin 2) (ResidueField W) ⧸ Ideal.span {L j} :=
    Ideal.Quotient.mk _ with hmkT

  set 𝔪 : Ideal (MvPowerSeries (Fin 2) (ResidueField W)) :=
    Ideal.span {(X 0 : MvPowerSeries (Fin 2) (ResidueField W)), X 1} with h𝔪
  have hmem𝔪 : ∀ φ : MvPowerSeries (Fin 2) (ResidueField W), φ ∈ 𝔪 ↔ MvPowerSeries.constantCoeff φ = 0 := by
    intro φ
    have h1 := MvPowerSeries.mem_span_X_pow_iff_forall_coeff_eq_zero_of_degree_lt (ResidueField W) 1 φ
    rw [pow_one] at h1
    rw [h1]
    constructor
    · intro h
      rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact h 0 (by simp)
    · intro h n hn
      have hn0 : n = 0 := by
        ext i
        fin_cases i <;> simp <;> omega
      rw [hn0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact h
  have h𝔪max : 𝔪 = maximalIdeal (MvPowerSeries (Fin 2) (ResidueField W)) := by
    ext φ
    rw [hmem𝔪, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff,
      isUnit_iff_ne_zero, not_not]
  have hX0𝔪 : (X 0 : MvPowerSeries (Fin 2) (ResidueField W)) ∈ 𝔪 := Ideal.subset_span (by simp)
  have hX1𝔪 : (X 1 : MvPowerSeries (Fin 2) (ResidueField W)) ∈ 𝔪 := Ideal.subset_span (by simp)
  have hlin𝔪 : C (A j) * X 0 + C (B j) * X 1 ∈ 𝔪 :=
    Ideal.add_mem _ (Ideal.mul_mem_left _ _ hX0𝔪) (Ideal.mul_mem_left _ _ hX1𝔪)
  have hL𝔪 : L j ∈ 𝔪 := by
    have h1 : L j - (C (A j) * X 0 + C (B j) * X 1) ∈ 𝔪 := Ideal.pow_le_self two_ne_zero (hL j)
    have h2 := Ideal.add_mem _ h1 hlin𝔪
    rwa [sub_add_cancel] at h2

  have hnf : ¬ IsField (MvPowerSeries (Fin 2) (ResidueField W) ⧸ Ideal.span {L j}) := by
    intro hF
    have hmax : (Ideal.span {L j}).IsMaximal := (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mpr hF
    have heq : Ideal.span {L j} = 𝔪 := by rw [h𝔪max]; exact IsLocalRing.eq_maximalIdeal hmax
    rcases (hR j).2.1 with h0 | h1
    · exact h0 (by rw [heq]; exact hX0𝔪)
    · exact h1 (by rw [heq]; exact hX1𝔪)

  have hmT : Ideal.span {mkT (X 0), mkT (X 1)} = maximalIdeal (MvPowerSeries (Fin 2) (ResidueField W) ⧸ Ideal.span {L j}) := by
    have hmap : 𝔪.map mkT = Ideal.span {mkT (X 0), mkT (X 1)} := by
      rw [h𝔪, Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
    rw [← hmap]
    apply IsLocalRing.eq_maximalIdeal
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective mkT Ideal.Quotient.mk_surjective
      (I := 𝔪) (h𝔪max ▸ IsLocalRing.maximalIdeal.isMaximal _) with htop | hmax
    · exfalso
      have h1 := Ideal.comap_map_of_surjective mkT Ideal.Quotient.mk_surjective 𝔪
      rw [htop, Ideal.comap_top, ← RingHom.ker_eq_comap_bot, hmkT, Ideal.mk_ker,
        sup_eq_left.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hL𝔪)] at h1
      exact (h𝔪max ▸ IsLocalRing.maximalIdeal.isMaximal _).ne_top h1.symm
    · exact hmax

  have hrelT : mkT (C (A j)) * mkT (X 0) + mkT (C (B j)) * mkT (X 1) +
      mkT (L j - (C (A j) * X 0 + C (B j) * X 1)) = 0 := by
    rw [← map_mul, ← map_mul, ← map_add, ← map_add,
      show C (A j) * X 0 + C (B j) * X 1 + (L j - (C (A j) * X 0 + C (B j) * X 1)) = L j by ring]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have hhT : mkT (L j - (C (A j) * X 0 + C (B j) * X 1)) ∈ (Ideal.span {mkT (X 0), mkT (X 1)}) ^ 2 := by
    have hmap : 𝔪.map mkT = Ideal.span {mkT (X 0), mkT (X 1)} := by
      rw [h𝔪, Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
    rw [← hmap, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ (hL j)

  have hgen : ∃ y, maximalIdeal (MvPowerSeries (Fin 2) (ResidueField W) ⧸ Ideal.span {L j}) = Ideal.span {y} := by
    rcases hAB0 j with ha | hb
    · refine ⟨mkT (X 1), B2_node13.maximalIdeal_eq_span_singleton_of_rel (mkT (X 0)) (mkT (X 1)) (mkT (C (A j)))
        (mkT (C (B j))) _ ?_ hmT hhT hrelT⟩
      exact ((MvPowerSeries.isUnit_iff_constantCoeff.mpr (by rw [MvPowerSeries.constantCoeff_C]; exact isUnit_iff_ne_zero.mpr ha)).map mkT)
    · refine ⟨mkT (X 0), B2_node13.maximalIdeal_eq_span_singleton_of_rel (mkT (X 1)) (mkT (X 0)) (mkT (C (B j)))
        (mkT (C (A j))) _ ?_ (by rw [Set.pair_comm]; exact hmT) (by rw [Set.pair_comm]; exact hhT)
        (by rw [← hrelT]; ring)⟩
      exact ((MvPowerSeries.isUnit_iff_constantCoeff.mpr (by rw [MvPowerSeries.constantCoeff_C]; exact isUnit_iff_ne_zero.mpr hb)).map mkT)
  have hprinc : (maximalIdeal (MvPowerSeries (Fin 2) (ResidueField W) ⧸ Ideal.span {L j})).IsPrincipal := by
    obtain ⟨y, hy⟩ := hgen
    rw [hy]
    exact ⟨⟨y, rfl⟩⟩
  haveI hDVR : IsDiscreteValuationRing (MvPowerSeries (Fin 2) (ResidueField W) ⧸ Ideal.span {L j}) :=
    ((IsDiscreteValuationRing.TFAE (MvPowerSeries (Fin 2) (ResidueField W) ⧸ Ideal.span {L j}) hnf).out 0 4).mpr hprinc

  have hle : Ideal.span {red g} ≤ Ideal.span {L j} := by
    rw [Ideal.span_singleton_le_iff_mem]; exact hgQ
  let Φ : S →+* MvPowerSeries (Fin 2) (ResidueField W) ⧸ Ideal.span {L j} :=
    (Ideal.Quotient.factor hle).comp ((e : _ →+* _).comp πS)
  have hΦ : ∀ p, Φ (mkS p) = mkT (red p) := by
    intro p
    show Ideal.Quotient.factor hle (e (πS (mkS p))) = mkT (red p)
    rw [hΘ]
    exact Ideal.Quotient.factor_mk hle (red p)
  have hΦsurj : Function.Surjective Φ := by
    intro t
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective t
    obtain ⟨p, rfl⟩ := hredsurj y
    exact ⟨mkS p, hΦ p⟩
  have hker : RingHom.ker Φ = P := by
    ext s
    obtain ⟨p, rfl⟩ := hmkS s
    rw [RingHom.mem_ker, hΦ, hmem p]
    exact Ideal.Quotient.eq_zero_iff_mem
  let Ψ : (S ⧸ P) ≃+* (MvPowerSeries (Fin 2) (ResidueField W) ⧸ Ideal.span {L j}) :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hΦsurj)
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing Ψ.symm

theorem solution
    (q : ℕ) [Fact q.Prime]
    (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (π : W) (hπ : IsLocalRing.maximalIdeal W = Ideal.span {π})
    (hqW : (q : W) ∈ IsLocalRing.maximalIdeal W)
    (c : W) (hc : c ∈ IsLocalRing.maximalIdeal W) (hc0 : c ≠ 0)
    (f u v : MvPowerSeries (Fin 2) W) (hu : IsUnit u) (hv : IsUnit v)
    (hf : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
      (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (q + 2))
    (P : Ideal (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C c * v - f * u})) [P.IsPrime]
    (hPX : Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C c * v - f * u}) (MvPowerSeries.X 0) ∉ P ∨
      Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C c * v - f * u}) (MvPowerSeries.X 1) ∉ P)
    (hPπ : Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C c * v - f * u}) (MvPowerSeries.C π) ∈ P) :
    IsDiscreteValuationRing ((MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C c * v - f * u}) ⧸ P) :=
  B2_node13.core q W π hπ hqW c hc hc0 f u v hu hv hf P hPX hPπ

end S_DrinfeldCurve_LocalChart_isDiscreteValuationRing_quotient_branchPrime_of_sub_drinfeldForm_mem_pow
end P2MW
export P2MW.S_DrinfeldCurve_LocalChart_isDiscreteValuationRing_quotient_branchPrime_of_sub_drinfeldForm_mem_pow (solution)
