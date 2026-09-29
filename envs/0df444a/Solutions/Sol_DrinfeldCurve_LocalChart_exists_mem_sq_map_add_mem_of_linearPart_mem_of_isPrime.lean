-- Prove2me | solution 1 for DrinfeldCurve.LocalChart.exists_mem_sq_map_add_mem_of_linearPart_mem_of_isPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/19687a57-c2dd-5519-bd2f-e5e0a8337a62

import Mathlib
import Definitions.Def_DrinfeldCurve_LocalChart
import Theorems.Thm_MvPowerSeries_exists_isUnit_mul_prod_eq_of_sub_prod_linear_mem_pow
import Theorems.Thm_DrinfeldCurve_LocalChart_card_eq_and_prod_linear_eq_drinfeldForm_and_isUnit_det_of_prod_X_sub_C_eq
import Theorems.Thm_MvPowerSeries_mem_span_X_pow_iff_forall_coeff_eq_zero_of_degree_lt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DrinfeldCurve_LocalChart_exists_mem_sq_map_add_mem_of_linearPart_mem_of_isPrime

set_option autoImplicit false

open MvPowerSeries IsLocalRing

namespace WBRSolution

open MvPowerSeries

theorem constantCoeff_eq_zero_of_mem_span_X {R : Type} [CommRing R] {h : MvPowerSeries (Fin 2) R}
    (hh : h ∈ Ideal.span {(X 0 : MvPowerSeries (Fin 2) R), X 1}) : constantCoeff h = 0 := by
  have hle : Ideal.span {(X 0 : MvPowerSeries (Fin 2) R), X 1} ≤ RingHom.ker (constantCoeff (σ := Fin 2) (R := R)) := by
    rw [Ideal.span_le]
    intro x hx
    rcases hx with rfl | rfl <;> simp [RingHom.mem_ker]
  exact hle hh

theorem exists_eq_X_mul_add_of_mem_sq {R : Type} [CommRing R] {h : MvPowerSeries (Fin 2) R}
    (hh : h ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) R), X 1}) ^ 2) :
    ∃ p ∈ Ideal.span {(X 0 : MvPowerSeries (Fin 2) R), X 1},
      ∃ r ∈ Ideal.span {(X 0 : MvPowerSeries (Fin 2) R), X 1}, h = X 0 * p + X 1 * r := by
  rw [pow_two] at hh
  have hsplit : Ideal.span {(X 0 : MvPowerSeries (Fin 2) R), X 1} * Ideal.span {(X 0 : MvPowerSeries (Fin 2) R), X 1} =
      Ideal.span {(X 0 : MvPowerSeries (Fin 2) R)} * Ideal.span {(X 0 : MvPowerSeries (Fin 2) R), X 1} ⊔
      Ideal.span {(X 1 : MvPowerSeries (Fin 2) R)} * Ideal.span {(X 0 : MvPowerSeries (Fin 2) R), X 1} := by
    rw [show Ideal.span {(X 0 : MvPowerSeries (Fin 2) R), X 1} =
        Ideal.span {(X 0 : MvPowerSeries (Fin 2) R)} ⊔ Ideal.span {X 1} from Ideal.span_insert _ _, Ideal.sup_mul]
  rw [hsplit, Submodule.mem_sup] at hh
  obtain ⟨y, hy, z, hz, rfl⟩ := hh
  obtain ⟨p, hp, rfl⟩ := Ideal.mem_span_singleton_mul.mp hy
  obtain ⟨r, hr, rfl⟩ := Ideal.mem_span_singleton_mul.mp hz
  exact ⟨p, hp, r, hr, rfl⟩

theorem X_mem_of_linearParts {R : Type} [CommRing R] (Q : Ideal (MvPowerSeries (Fin 2) R))
    (α β γ δ : R) (hdet : IsUnit (α * δ - β * γ))
    (h₁ h₂ : MvPowerSeries (Fin 2) R)
    (hh₁ : h₁ ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) R), X 1}) ^ 2)
    (hh₂ : h₂ ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) R), X 1}) ^ 2)
    (hℓ₁ : C α * X 0 + C β * X 1 + h₁ ∈ Q) (hℓ₂ : C γ * X 0 + C δ * X 1 + h₂ ∈ Q) :
    (X 0 : MvPowerSeries (Fin 2) R) ∈ Q ∧ (X 1 : MvPowerSeries (Fin 2) R) ∈ Q := by
  obtain ⟨p₁, hp₁, r₁, hr₁, rfl⟩ := exists_eq_X_mul_add_of_mem_sq hh₁
  obtain ⟨p₂, hp₂, r₂, hr₂, rfl⟩ := exists_eq_X_mul_add_of_mem_sq hh₂
  set A : MvPowerSeries (Fin 2) R := C α + p₁
  set B : MvPowerSeries (Fin 2) R := C β + r₁
  set Γ : MvPowerSeries (Fin 2) R := C γ + p₂
  set Δ : MvPowerSeries (Fin 2) R := C δ + r₂
  have e₁ : C α * X 0 + C β * X 1 + (X 0 * p₁ + X 1 * r₁) = A * X 0 + B * X 1 := by simp only [A, B]; ring
  have e₂ : C γ * X 0 + C δ * X 1 + (X 0 * p₂ + X 1 * r₂) = Γ * X 0 + Δ * X 1 := by simp only [Γ, Δ]; ring
  rw [e₁] at hℓ₁
  rw [e₂] at hℓ₂
  set D : MvPowerSeries (Fin 2) R := A * Δ - B * Γ
  have hD : IsUnit D := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff]
    have : constantCoeff D = α * δ - β * γ := by
      simp only [D, A, B, Γ, Δ, map_sub, map_mul, map_add, constantCoeff_C,
        constantCoeff_eq_zero_of_mem_span_X hp₁, constantCoeff_eq_zero_of_mem_span_X hr₁,
        constantCoeff_eq_zero_of_mem_span_X hp₂, constantCoeff_eq_zero_of_mem_span_X hr₂, add_zero]
    rw [this]; exact hdet
  obtain ⟨Dinv, hDinv⟩ := hD.exists_left_inv
  have hX0 : D * X 0 ∈ Q := by
    have : D * X 0 = Δ * (A * X 0 + B * X 1) - B * (Γ * X 0 + Δ * X 1) := by simp only [D]; ring
    rw [this]
    exact Q.sub_mem (Q.mul_mem_left _ hℓ₁) (Q.mul_mem_left _ hℓ₂)
  have hX1 : D * X 1 ∈ Q := by
    have : D * X 1 = A * (Γ * X 0 + Δ * X 1) - Γ * (A * X 0 + B * X 1) := by simp only [D]; ring
    rw [this]
    exact Q.sub_mem (Q.mul_mem_left _ hℓ₂) (Q.mul_mem_left _ hℓ₁)
  constructor
  · have : (X 0 : MvPowerSeries (Fin 2) R) = Dinv * (D * X 0) := by rw [← mul_assoc, hDinv, one_mul]
    rw [this]; exact Q.mul_mem_left _ hX0
  · have : (X 1 : MvPowerSeries (Fin 2) R) = Dinv * (D * X 1) := by rw [← mul_assoc, hDinv, one_mul]
    rw [this]; exact Q.mul_mem_left _ hX1

theorem exists_map_eq_of_surjective {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) (G : MvPowerSeries (Fin 2) S) :
    ∃ G' : MvPowerSeries (Fin 2) R, map f G' = G ∧ ∀ m, coeff m G = 0 → coeff m G' = 0 := by
  classical
  refine ⟨fun m => if coeff m G = 0 then 0 else (hf (coeff m G)).choose, ?_, ?_⟩
  · ext m
    rw [coeff_map]
    show f (if coeff m G = 0 then 0 else (hf (coeff m G)).choose) = coeff m G
    split_ifs with h
    · rw [map_zero, h]
    · exact (hf (coeff m G)).choose_spec
  · intro m hm
    show (if coeff m G = 0 then 0 else (hf (coeff m G)).choose) = 0
    rw [if_pos hm]

theorem map_mem_span_X_pow {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ)
    {g : MvPowerSeries (Fin 2) R} (hg : g ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) R), X 1}) ^ n) :
    map f g ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) S), X 1}) ^ n := by
  have h := Ideal.mem_map_of_mem (map f) hg
  rw [Ideal.map_pow, Ideal.map_span, Set.image_insert_eq, Set.image_singleton, map_X, map_X] at h
  exact h

theorem isUnit_intCast_of_not_dvd {R : Type} [CommRing R] [IsLocalRing R] (q : ℕ) (hq : q.Prime)
    (hqR : (q : R) ∈ maximalIdeal R) (n : ℤ) (hn : ¬ (q : ℤ) ∣ n) : IsUnit (n : R) := by
  haveI : CharP (ResidueField R) q := by
    apply (CharP.charP_iff_prime_eq_zero hq).mpr
    have h := (residue_eq_zero_iff (q : R)).mpr hqR
    rwa [map_natCast] at h
  rw [← IsLocalRing.notMem_maximalIdeal, ← residue_eq_zero_iff, map_intCast]
  intro h
  exact hn ((CharP.intCast_eq_zero_iff (ResidueField R) q n).mp h)

theorem exists_eq_C_mul_of_forall_coeff_mem {R : Type} [CommRing R] (π : R) (D : MvPowerSeries (Fin 2) R)
    (hD : ∀ m, coeff m D ∈ Ideal.span {π}) : ∃ E : MvPowerSeries (Fin 2) R, D = C π * E := by
  have h : ∀ m, ∃ e : R, coeff m D = π * e := fun m => by
    obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.mp (hD m)
    exact ⟨e, by rw [← he, mul_comm]⟩
  refine ⟨fun m => (h m).choose, ?_⟩
  ext m
  rw [coeff_C_mul]
  exact (h m).choose_spec

theorem map_drinfeldForm {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (q : ℕ) [Fact q.Prime] :
    map f (DrinfeldCurve.LocalChart.drinfeldForm q R) = DrinfeldCurve.LocalChart.drinfeldForm q S := by
  simp [DrinfeldCurve.LocalChart.drinfeldForm, map_sub, map_mul, map_pow, map_X]

theorem main
    (q : ℕ) [Fact q.Prime]
    (W₀ W : Type) [CommRing W₀] [IsLocalRing W₀] [CommRing W] [IsLocalRing W] (ψ : W₀ →+* W)
    (π₀ : W₀) (hπ₀ : maximalIdeal W₀ = Ideal.span {π₀})
    (hqW₀ : (q : W₀) ∈ maximalIdeal W₀) (hqW : (q : W) ∈ maximalIdeal W)
    (f₀ u₀ v₀ : MvPowerSeries (Fin 2) W₀) (hu₀ : IsUnit u₀)
    (hf₀ : f₀ - DrinfeldCurve.LocalChart.drinfeldForm q W₀ ∈
      (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W₀), X 1}) ^ (q + 2))
    (Q : Ideal (MvPowerSeries (Fin 2) W)) (hQ : Q.IsPrime)
    (hQg : MvPowerSeries.map ψ (C π₀ * v₀ - f₀ * u₀) ∈ Q)
    (hQX : (X 0 : MvPowerSeries (Fin 2) W) ∉ Q ∨ (X 1 : MvPowerSeries (Fin 2) W) ∉ Q)
    (hQπ : (C (ψ π₀) : MvPowerSeries (Fin 2) W) ∈ Q)
    (a b : ℤ)
    (hab : ∃ h ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1}) ^ 2,
      C ((a : ℤ) : W) * X 0 + C ((b : ℤ) : W) * X 1 + h ∈ Q) :
    ∃ h₀ ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W₀), X 1}) ^ 2,
      MvPowerSeries.map ψ (C ((a : ℤ) : W₀) * X 0 + C ((b : ℤ) : W₀) * X 1 + h₀) ∈ Q := by
  classical
  have hq : q.Prime := Fact.out
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI := hQ

  haveI hchar : CharP (ResidueField W₀) q := by
    apply (CharP.charP_iff_prime_eq_zero hq).mpr
    have h := (residue_eq_zero_iff (q : W₀)).mpr hqW₀
    rwa [map_natCast] at h

  have hCq : (C (q : W) : MvPowerSeries (Fin 2) W) ∈ Q := by
    have hqmem : (q : W₀) ∈ Ideal.span {π₀} := hπ₀ ▸ hqW₀
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hqmem
    have : (C (q : W) : MvPowerSeries (Fin 2) W) = C (ψ w) * C (ψ π₀) := by
      rw [← map_mul, ← map_mul ψ, hw, map_natCast ψ]
    rw [this]; exact Q.mul_mem_left _ hQπ

  have hf₀Q : MvPowerSeries.map ψ f₀ ∈ Q := by
    have h1 : MvPowerSeries.map ψ (C π₀ * v₀) ∈ Q := by
      rw [map_mul, map_C]; exact Q.mul_mem_right _ hQπ
    have h2 : MvPowerSeries.map ψ f₀ * MvPowerSeries.map ψ u₀ ∈ Q := by
      have := Q.sub_mem h1 hQg
      rwa [← map_sub, sub_sub_cancel, map_mul] at this
    rcases hQ.mem_or_mem h2 with h | h
    · exact h
    · exact absurd (Ideal.eq_top_of_isUnit_mem _ h (hu₀.map (MvPowerSeries.map ψ))) hQ.ne_top

  set ζ : ZMod q →+* ResidueField W₀ := ZMod.castHom (dvd_refl q) (ResidueField W₀) with hζ
  have hζinj : Function.Injective ζ := ZMod.castHom_injective (ResidueField W₀)
  set T : Finset (ResidueField W₀) := Finset.univ.image ζ with hTdef
  have hT : ∏ t ∈ T, (Polynomial.X - Polynomial.C t) =
      (Polynomial.X ^ q - Polynomial.X : Polynomial (ResidueField W₀)) := by
    rw [hTdef, Finset.prod_image (fun x _ y _ h => hζinj h)]
    have hroots := FiniteField.roots_X_pow_card_sub_X (ZMod q)
    rw [ZMod.card] at hroots
    have hmonic : (Polynomial.X ^ q - Polynomial.X : Polynomial (ZMod q)).Monic :=
      Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; exact_mod_cast hq.one_lt)
    have hdeg : (Polynomial.X ^ q - Polynomial.X : Polynomial (ZMod q)).natDegree = q :=
      FiniteField.X_pow_card_sub_X_natDegree_eq (ZMod q) hq.one_lt
    have hprod := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic
      (by rw [hroots, hdeg]; simp [ZMod.card])
    rw [hroots] at hprod
    have hprod' : ∏ s : ZMod q, (Polynomial.X - Polynomial.C s) = Polynomial.X ^ q - Polynomial.X := hprod
    have := congrArg (Polynomial.map ζ) hprod'
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X] at this
    rw [← this, ← Polynomial.coe_mapRingHom, map_prod]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [Polynomial.coe_mapRingHom, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  obtain ⟨hcard, hprodT, hdetT⟩ :=
    DrinfeldCurve.LocalChart.card_eq_and_prod_linear_eq_drinfeldForm_and_isUnit_det_of_prod_X_sub_C_eq
      q (ResidueField W₀) T hT
  set a' : Option ↥T → ResidueField W₀ := fun i => Option.elim i (1 : ResidueField W₀) (fun t => -(t : ResidueField W₀)) with ha'
  set b' : Option ↥T → ResidueField W₀ := fun i => Option.elim i (0 : ResidueField W₀) (fun _ => (1 : ResidueField W₀)) with hb'
  have hab' : ∀ i j : Option ↥T, i ≠ j → a' i * b' j - a' j * b' i ≠ 0 := by
    intro i j hij
    have hu := hdetT (fun t _ t' _ htt' => isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr htt')) i j hij
    exact hu.ne_zero

  set F : MvPowerSeries (Fin 2) (ResidueField W₀) := map (residue W₀) f₀ with hFdef
  have hcardι : Fintype.card (Option ↥T) + 1 = q + 2 := by
    rw [Fintype.card_option, Fintype.card_coe, hcard]
  have hF : F - ∏ i, (C (a' i) * X 0 + C (b' i) * X 1) ∈
      (Ideal.span {(X 0 : MvPowerSeries (Fin 2) (ResidueField W₀)), X 1}) ^ (Fintype.card (Option ↥T) + 1) := by
    rw [hcardι]
    have hp : ∏ i, (C (a' i) * X 0 + C (b' i) * X 1) = DrinfeldCurve.LocalChart.drinfeldForm q (ResidueField W₀) := by
      rw [← hprodT]
    rw [hp, hFdef, ← map_drinfeldForm (residue W₀) q, ← map_sub]
    exact map_mem_span_X_pow (residue W₀) (q + 2) hf₀
  obtain ⟨L, w, hw, hL, hFeq⟩ :=
    MvPowerSeries.exists_isUnit_mul_prod_eq_of_sub_prod_linear_mem_pow a' b' hab' F hF

  have hrep : ∀ t : ↥T, ∃ s : ZMod q, ζ s = (t : ResidueField W₀) := by
    intro t
    have ht : (t : ResidueField W₀) ∈ Finset.univ.image ζ := t.2
    obtain ⟨s, -, hs⟩ := Finset.mem_image.mp ht
    exact ⟨s, hs⟩
  choose sOf hsOf using hrep
  set A : Option ↥T → ℤ := fun i => Option.elim i (1 : ℤ) (fun t => -((sOf t).val : ℤ)) with hAdef
  set B : Option ↥T → ℤ := fun i => Option.elim i (0 : ℤ) (fun _ => (1 : ℤ)) with hBdef
  have hA : ∀ i, ((A i : ℤ) : ResidueField W₀) = a' i := by
    intro i
    cases i with
    | none => simp [hAdef, ha']
    | some t =>
      show (((-((sOf t).val : ℤ)) : ℤ) : ResidueField W₀) = -(t : ResidueField W₀)
      rw [Int.cast_neg, Int.cast_natCast, ZMod.natCast_val, ← hsOf t, hζ, ZMod.castHom_apply]
  have hB : ∀ i, ((B i : ℤ) : ResidueField W₀) = b' i := by
    intro i
    cases i with
    | none => simp [hBdef, hb']
    | some t => simp [hBdef, hb']

  have hsurj : Function.Surjective (residue W₀) := Ideal.Quotient.mk_surjective
  have hlift : ∀ i, ∃ H : MvPowerSeries (Fin 2) W₀,
      map (residue W₀) H = L i - (C (a' i) * X 0 + C (b' i) * X 1) ∧
      H ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W₀), X 1}) ^ 2 := by
    intro i
    obtain ⟨H, hH, hH0⟩ := exists_map_eq_of_surjective (residue W₀) hsurj (L i - (C (a' i) * X 0 + C (b' i) * X 1))
    refine ⟨H, hH, ?_⟩
    rw [MvPowerSeries.mem_span_X_pow_iff_forall_coeff_eq_zero_of_degree_lt]
    intro n hn
    apply hH0
    exact (MvPowerSeries.mem_span_X_pow_iff_forall_coeff_eq_zero_of_degree_lt _ 2 _).mp (hL i) n hn
  choose Hs hHs using hlift
  set Lt : Option ↥T → MvPowerSeries (Fin 2) W₀ :=
    fun i => C ((A i : ℤ) : W₀) * X 0 + C ((B i : ℤ) : W₀) * X 1 + Hs i with hLtdef
  have hLt : ∀ i, map (residue W₀) (Lt i) = L i := by
    intro i
    simp only [hLtdef, map_add, map_mul, MvPowerSeries.map_C, MvPowerSeries.map_X, (hHs i).1]
    rw [map_intCast (residue W₀) (A i), map_intCast (residue W₀) (B i), hA i, hB i]
    ring
  obtain ⟨wt, hwt, -⟩ := exists_map_eq_of_surjective (residue W₀) hsurj w
  have hwtU : IsUnit (MvPowerSeries.map ψ wt) := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff, constantCoeff_map]
    apply IsUnit.map
    rw [← IsLocalRing.notMem_maximalIdeal, ← residue_eq_zero_iff, ← constantCoeff_map, hwt]
    exact (MvPowerSeries.isUnit_iff_constantCoeff.mp hw).ne_zero

  set D : MvPowerSeries (Fin 2) W₀ := f₀ - wt * ∏ i, Lt i with hDdef
  have hD0 : map (residue W₀) D = 0 := by
    rw [hDdef, map_sub, map_mul, map_prod, hwt]
    simp only [hLt]
    rw [← hFdef, hFeq, sub_self]
  have hDcoeff : ∀ m, coeff m D ∈ Ideal.span {π₀} := by
    intro m
    rw [← hπ₀, ← residue_eq_zero_iff, ← coeff_map, hD0]
    rfl
  obtain ⟨E, hE⟩ := exists_eq_C_mul_of_forall_coeff_mem π₀ D hDcoeff
  have hprodQ : ∏ i, MvPowerSeries.map ψ (Lt i) ∈ Q := by
    have h1 : MvPowerSeries.map ψ wt * ∏ i, MvPowerSeries.map ψ (Lt i) ∈ Q := by
      have e : MvPowerSeries.map ψ wt * ∏ i, MvPowerSeries.map ψ (Lt i) =
          MvPowerSeries.map ψ f₀ - C (ψ π₀) * MvPowerSeries.map ψ E := by
        rw [← map_prod, ← map_mul, ← map_C, ← map_mul, ← map_sub, ← hE, hDdef, sub_sub_cancel]
      rw [e]
      exact Q.sub_mem hf₀Q (Q.mul_mem_right _ hQπ)
    rcases hQ.mem_or_mem h1 with h | h
    · exact absurd (Ideal.eq_top_of_isUnit_mem _ h hwtU) hQ.ne_top
    · exact h
  obtain ⟨i, -, hiQ⟩ := Ideal.IsPrime.prod_mem_iff.mp hprodQ

  have hHsW : MvPowerSeries.map ψ (Hs i) ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1}) ^ 2 :=
    map_mem_span_X_pow ψ 2 (hHs i).2
  have hLi : MvPowerSeries.map ψ (Lt i) =
      C ((A i : ℤ) : W) * X 0 + C ((B i : ℤ) : W) * X 1 + MvPowerSeries.map ψ (Hs i) := by
    simp only [hLtdef, map_add, map_mul, MvPowerSeries.map_C, MvPowerSeries.map_X]
    rw [map_intCast ψ (A i), map_intCast ψ (B i)]
  rw [hLi] at hiQ
  obtain ⟨h, hh, hℓ⟩ := hab
  by_cases hdiv : (q : ℤ) ∣ a * B i - b * A i
  ·
    have hlin : ∃ lam m₀ m₁ : ℤ, a = lam * A i + q * m₀ ∧ b = lam * B i + q * m₁ := by
      cases i with
      | none =>
        obtain ⟨m, hm⟩ := hdiv
        refine ⟨a, 0, -m, ?_, ?_⟩
        · simp [hAdef]
        · simp only [hBdef, hAdef, Option.elim] at hm ⊢
          linarith
      | some t =>
        obtain ⟨m, hm⟩ := hdiv
        refine ⟨b, m, 0, ?_, ?_⟩
        · simp only [hBdef, hAdef, Option.elim] at hm ⊢
          linarith
        · simp [hBdef]
    obtain ⟨lam, m₀, m₁, hlam_a, hlam_b⟩ := hlin
    refine ⟨C ((lam : ℤ) : W₀) * Hs i, Ideal.mul_mem_left _ _ (hHs i).2, ?_⟩
    have ha' : ((a : ℤ) : W) = ((lam : ℤ) : W) * ((A i : ℤ) : W) + (q : W) * ((m₀ : ℤ) : W) := by
      rw [hlam_a]; push_cast; ring
    have hb'' : ((b : ℤ) : W) = ((lam : ℤ) : W) * ((B i : ℤ) : W) + (q : W) * ((m₁ : ℤ) : W) := by
      rw [hlam_b]; push_cast; ring
    have key : MvPowerSeries.map ψ (C ((a : ℤ) : W₀) * X 0 + C ((b : ℤ) : W₀) * X 1 + C ((lam : ℤ) : W₀) * Hs i) =
        C ((lam : ℤ) : W) * (C ((A i : ℤ) : W) * X 0 + C ((B i : ℤ) : W) * X 1 + MvPowerSeries.map ψ (Hs i)) +
        C (q : W) * (C ((m₀ : ℤ) : W) * X 0 + C ((m₁ : ℤ) : W) * X 1) := by
      simp only [map_add, map_mul, MvPowerSeries.map_C, MvPowerSeries.map_X]
      rw [map_intCast ψ a, map_intCast ψ b, map_intCast ψ lam, ha', hb'']
      simp only [map_add, map_mul]
      ring
    rw [key]
    exact Q.add_mem (Q.mul_mem_left _ hiQ) (Q.mul_mem_right _ hCq)
  ·
    have hunit : IsUnit (((a * B i - b * A i : ℤ)) : W) := isUnit_intCast_of_not_dvd q hq hqW _ hdiv
    push_cast at hunit
    obtain ⟨hX0, hX1⟩ := X_mem_of_linearParts Q ((a : ℤ) : W) ((b : ℤ) : W) ((A i : ℤ) : W) ((B i : ℤ) : W)
      hunit h (MvPowerSeries.map ψ (Hs i)) hh hHsW hℓ hiQ
    rcases hQX with h0 | h1
    · exact (h0 hX0).elim
    · exact (h1 hX1).elim

end WBRSolution

theorem solution
    (q : ℕ) [Fact q.Prime]
    (W₀ W : Type) [CommRing W₀] [IsLocalRing W₀] [CommRing W] [IsLocalRing W] (ψ : W₀ →+* W)
    (π₀ : W₀) (hπ₀ : maximalIdeal W₀ = Ideal.span {π₀})
    (hqW₀ : (q : W₀) ∈ maximalIdeal W₀) (hqW : (q : W) ∈ maximalIdeal W)
    (f₀ u₀ v₀ : MvPowerSeries (Fin 2) W₀) (hu₀ : IsUnit u₀)
    (hf₀ : f₀ - DrinfeldCurve.LocalChart.drinfeldForm q W₀ ∈
      (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W₀), X 1}) ^ (q + 2))

    (Q : Ideal (MvPowerSeries (Fin 2) W)) (hQ : Q.IsPrime)
    (hQg : MvPowerSeries.map ψ (C π₀ * v₀ - f₀ * u₀) ∈ Q)

    (hQX : (X 0 : MvPowerSeries (Fin 2) W) ∉ Q ∨ (X 1 : MvPowerSeries (Fin 2) W) ∉ Q)

    (hQπ : (C (ψ π₀) : MvPowerSeries (Fin 2) W) ∈ Q)

    (a b : ℤ)
    (hab : ∃ h ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1}) ^ 2,
      C ((a : ℤ) : W) * X 0 + C ((b : ℤ) : W) * X 1 + h ∈ Q) :

    ∃ h₀ ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W₀), X 1}) ^ 2,
      MvPowerSeries.map ψ (C ((a : ℤ) : W₀) * X 0 + C ((b : ℤ) : W₀) * X 1 + h₀) ∈ Q :=
  WBRSolution.main q W₀ W ψ π₀ hπ₀ hqW₀ hqW f₀ u₀ v₀ hu₀ hf₀ Q hQ hQg hQX hQπ a b hab

end S_DrinfeldCurve_LocalChart_exists_mem_sq_map_add_mem_of_linearPart_mem_of_isPrime
end P2MW
export P2MW.S_DrinfeldCurve_LocalChart_exists_mem_sq_map_add_mem_of_linearPart_mem_of_isPrime (solution)
