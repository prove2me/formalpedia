-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_monoidHom_generalLinearGroup_finrank_kerAlgebra_eq_pow_of_hasHeight
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/0155a95c-9582-512c-ad59-6a27884142ff

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_MvPowerSeries_span_range_X_eq_ker_constantCoeff
import Theorems.Thm_MvFormalGroup_finrank_quotient_span_nthSeries_pow_eq_pow
import Theorems.Thm_MvFormalGroup_Hom_exists_finrank_quotient_span_range_map_eq_prime_pow_of_isComm
import Theorems.Thm_MvPowerSeries_finite_and_finrank_quotient_span_range_subst_eq_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_monoidHom_generalLinearGroup_finrank_kerAlgebra_eq_pow_of_hasHeight
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

universe u

noncomputable section

open MvPowerSeries
open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalODModule

namespace R4HeightHom

section Series

variable {R : Type u} [CommRing R] {n : ℕ}

theorem subst_mem_span_range {a : Fin n → MvPowerSeries (Fin n) R}
    (ha0 : ∀ i, constantCoeff (a i) = 0) (g : MvPowerSeries (Fin n) R) (hg : constantCoeff g = 0) :
    subst a g ∈ Ideal.span (Set.range a) := by
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero ha0
  have hmem : g ∈ Ideal.span (Set.range (X : Fin n → MvPowerSeries (Fin n) R)) := by
    rw [MvPowerSeries.span_range_X_eq_ker_constantCoeff, RingHom.mem_ker]
    exact hg
  have hmap : (Ideal.span (Set.range (X : Fin n → MvPowerSeries (Fin n) R))).map (substAlgHom ha) =
      Ideal.span (Set.range a) := by
    rw [Ideal.map_span]
    congr 1
    ext y
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, by rw [substAlgHom_apply, subst_X ha]⟩
    · rintro ⟨i, rfl⟩
      exact ⟨X i, ⟨i, rfl⟩, by rw [substAlgHom_apply, subst_X ha]⟩
  have := Ideal.mem_map_of_mem (substAlgHom ha) hmem
  rw [hmap, substAlgHom_apply] at this
  exact this

theorem span_range_subst_le {a : Fin n → MvPowerSeries (Fin n) R}
    (ha0 : ∀ i, constantCoeff (a i) = 0) (g : Fin n → MvPowerSeries (Fin n) R)
    (hg : ∀ i, constantCoeff (g i) = 0) :
    Ideal.span (Set.range fun i => subst a (g i)) ≤ Ideal.span (Set.range a) := by
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact subst_mem_span_range ha0 (g i) (hg i)

end Series

section Frame

variable {r : ℕ} [hr : Fact r.Prime] {K : Type u} [Field K] [CharP K r]
variable (Φ : FormalODModule r K)

abbrev Λ : Subring (MvFormalGroup.End Φ.F) := Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})

variable {Φ}

abbrev ser (e : Λ Φ) : Series K := (e : MvFormalGroup.End Φ.F).toPowerSeries

theorem ser_constantCoeff (e : Λ Φ) (i : Fin 2) : constantCoeff (ser e i) = 0 :=
  (e : MvFormalGroup.End Φ.F).constantCoeff_eq_zero i

theorem ser_mul (e e' : Λ Φ) : ser (e * e') = fun i => subst (ser e') (ser e i) := rfl

theorem ser_natCast (n : ℕ) : ser ((n : Λ Φ)) = Φ.F.nthSeries n := by
  show ((((n : Λ Φ)) : MvFormalGroup.End Φ.F)).toPowerSeries = _
  rw [SubringClass.coe_natCast]
  exact MvFormalGroup.End.toPowerSeries_natCast Φ.F n

theorem span_ser_natCast (n : ℕ) :
    Ideal.span (Set.range (ser ((n : Λ Φ)))) = Ideal.span (Set.range (Φ.F.nthSeries n)) := by
  rw [ser_natCast]

abbrev Ker (e : Λ Φ) : Type u := KerAlgebra (ser e)

theorem finrank_ker_natCast_pow (hΦ4 : Φ.HasHeight 4) (N : ℕ) :
    Module.finrank K (Ker ((r ^ N : ℕ) : Λ Φ)) = r ^ (N * 4) := by
  have h4 := hΦ4.2.2 K (RingHom.id K)
  rw [Series.map_ringHom_id, act_natCast] at h4
  have := MvFormalGroup.finrank_quotient_span_nthSeries_pow_eq_pow r Φ.F 4 h4 N
  show Module.finrank K (MvPowerSeries (Fin 2) K ⧸ Ideal.span (Set.range (ser ((r ^ N : ℕ) : Λ Φ)))) = _
  rw [← this]
  exact (Ideal.quotientEquivAlgOfEq K (span_ser_natCast (Φ := Φ) (r ^ N))).toLinearEquiv.finrank_eq

theorem finite_ker_natCast_pow (hΦ4 : Φ.HasHeight 4) (N : ℕ) :
    Module.Finite K (Ker ((r ^ N : ℕ) : Λ Φ)) :=
  Module.finite_of_finrank_pos (by
    rw [finrank_ker_natCast_pow hΦ4 N]
    exact pow_pos hr.out.pos _)

theorem finite_ker_of_mul_eq (hΦ4 : Φ.HasHeight 4) (e f : Λ Φ) (N : ℕ)
    (h : f * e = ((r ^ N : ℕ) : Λ Φ)) : Module.Finite K (Ker e) := by
  haveI := finite_ker_natCast_pow (Φ := Φ) hΦ4 N
  have hle : Ideal.span (Set.range (ser ((r ^ N : ℕ) : Λ Φ))) ≤ Ideal.span (Set.range (ser e)) := by
    rw [← h]
    exact span_range_subst_le (ser_constantCoeff e) (ser f) (ser_constantCoeff f)
  exact Module.Finite.of_surjective (Ideal.Quotient.factorₐ K hle).toLinearMap
    (Ideal.Quotient.factor_surjective hle)

def hgt (e : Λ Φ) : ℕ := Nat.log r (Module.finrank K (Ker e))

theorem finrank_fibre (e : Λ Φ) (hfin : Module.Finite K (Ker e))
    (κ : Type u) [Field κ] (f : K →+* κ) :
    Module.finrank κ (KerAlgebra (Series.map f (ser e))) = r ^ hgt e := by
  obtain ⟨h, hh⟩ :=
    MvFormalGroup.Hom.exists_finrank_quotient_span_range_map_eq_prime_pow_of_isComm r K Φ.F Φ.F
      (e : MvFormalGroup.End Φ.F) hfin
  have hK : Module.finrank K (KerAlgebra (Series.map (RingHom.id K) (ser e))) = r ^ h :=
    hh K (RingHom.id K)
  rw [Series.map_ringHom_id] at hK
  have hlog : hgt e = h := by
    rw [hgt, hK, Nat.log_pow hr.out.one_lt]
  rw [hlog]
  exact hh κ f

theorem finrank_ker (e : Λ Φ) (hfin : Module.Finite K (Ker e)) :
    Module.finrank K (Ker e) = r ^ hgt e := by
  have := finrank_fibre e hfin K (RingHom.id K)
  rwa [Series.map_ringHom_id] at this

theorem finite_and_hgt_mul (e e' : Λ Φ) (he : Module.Finite K (Ker e))
    (he' : Module.Finite K (Ker e')) :
    Module.Finite K (Ker (e * e')) ∧ hgt (e * e') = hgt e + hgt e' := by
  have hm := MvPowerSeries.finite_and_finrank_quotient_span_range_subst_eq_mul (ser e) (ser e')
    (ser_constantCoeff e) (ser_constantCoeff e') he he'
  have hfin : Module.Finite K (Ker (e * e')) := hm.1
  refine ⟨hfin, ?_⟩
  have h1 := finrank_ker (e * e') hfin
  have h2 : Module.finrank K (Ker (e * e')) = r ^ hgt e * r ^ hgt e' := by
    rw [← finrank_ker e he, ← finrank_ker e' he']
    exact hm.2
  rw [← pow_add] at h2
  exact Nat.pow_right_injective hr.out.two_le (h1.symm.trans h2)

theorem hgt_natCast_pow (hΦ4 : Φ.HasHeight 4) (N : ℕ) : hgt ((r ^ N : ℕ) : Λ Φ) = N * 4 := by
  rw [hgt, finrank_ker_natCast_pow hΦ4 N, Nat.log_pow hr.out.one_lt]

variable (E : Λ Φ →+* Matrix (Fin 2) (Fin 2) ℚ_[r]) (hinj : Function.Injective E) (m : ℕ)
  (hm : ∀ A : Matrix (Fin 2) (Fin 2) ℤ_[r], ∃ e, E e = (r : ℚ_[r]) ^ m • A.map ((↑) : ℤ_[r] → ℚ_[r]))
  (hΦ4 : Φ.HasHeight 4)

theorem natCast_matrix (n : ℕ) :
    ((n : ℕ) : Matrix (Fin 2) (Fin 2) ℚ_[r]) = (n : ℚ_[r]) • (1 : Matrix (Fin 2) (Fin 2) ℚ_[r]) := by
  rw [Nat.cast_smul_eq_nsmul, nsmul_one]

theorem E_natCast_pow (n : ℕ) :
    E ((r ^ n : ℕ) : Λ Φ) = (r : ℚ_[r]) ^ n • (1 : Matrix (Fin 2) (Fin 2) ℚ_[r]) := by
  rw [map_natCast, natCast_matrix, Nat.cast_pow]

theorem rpow_ne_zero (n : ℕ) : (r : ℚ_[r]) ^ n ≠ 0 :=
  pow_ne_zero _ (Nat.cast_ne_zero.2 hr.out.ne_zero)

theorem isUnit_pow_smul {M : Matrix (Fin 2) (Fin 2) ℚ_[r]} (hM : IsUnit M) (n : ℕ) :
    IsUnit ((r : ℚ_[r]) ^ n • M) := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_smul, isUnit_iff_ne_zero]
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at hM
  exact mul_ne_zero (pow_ne_zero _ (rpow_ne_zero n)) hM

include hm in

theorem exists_apply_eq_pow_smul (M : Matrix (Fin 2) (Fin 2) ℚ_[r]) :
    ∃ (e : Λ Φ) (n : ℕ), E e = (r : ℚ_[r]) ^ n • M := by

  have hden : ∀ x : ℚ_[r], ∃ j : ℕ, ‖(r : ℚ_[r]) ^ j * x‖ ≤ 1 := by
    intro x
    by_cases hx : x = 0
    · exact ⟨0, by simp [hx]⟩
    have hr1 : (1 : ℝ) < r := by exact_mod_cast hr.out.one_lt
    obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt ‖x‖ hr1
    refine ⟨j, ?_⟩
    rw [norm_mul, norm_pow, Padic.norm_p, inv_pow, ← div_eq_inv_mul, div_le_one (by positivity)]
    exact hj.le
  choose j hj using hden
  set J : ℕ := ∑ i, ∑ i', j (M i i') with hJ
  have hle : ∀ i i', j (M i i') ≤ J := fun i i' =>
    (Finset.single_le_sum (f := fun i'' => j (M i i'')) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i')).trans
      (Finset.single_le_sum (f := fun i'' => ∑ i', j (M i'' i')) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i))
  have hint : ∀ i i', ‖(r : ℚ_[r]) ^ J * M i i'‖ ≤ 1 := by
    intro i i'
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (hle i i')
    rw [hd, add_comm, pow_add, mul_assoc, norm_mul, norm_pow, Padic.norm_p]
    calc (r : ℝ)⁻¹ ^ d * ‖(r : ℚ_[r]) ^ j (M i i') * M i i'‖ ≤ 1 ^ d * 1 := by
          gcongr
          · exact inv_le_one_of_one_le₀ (by exact_mod_cast hr.out.one_lt.le)
          · exact hj _
      _ = 1 := by rw [one_pow, one_mul]
  let A : Matrix (Fin 2) (Fin 2) ℤ_[r] := fun i i' => ⟨(r : ℚ_[r]) ^ J * M i i', hint i i'⟩
  obtain ⟨e, he⟩ := hm A
  refine ⟨e, m + J, ?_⟩
  rw [he, pow_add, mul_smul]
  congr 1

include hinj hm hΦ4 in

theorem finite_ker_of_isUnit (e : Λ Φ) (hu : IsUnit (E e)) : Module.Finite K (Ker e) := by
  obtain ⟨g, hg⟩ := hu
  obtain ⟨f, n, hf⟩ := exists_apply_eq_pow_smul E m hm ((g⁻¹ : (Matrix (Fin 2) (Fin 2) ℚ_[r])ˣ) :
    Matrix (Fin 2) (Fin 2) ℚ_[r])
  have hfe : f * e = ((r ^ n : ℕ) : Λ Φ) := hinj (by
    rw [map_mul, hf, ← hg, E_natCast_pow, smul_mul_assoc, Units.inv_mul])
  exact finite_ker_of_mul_eq hΦ4 e f n hfe

include hinj hm hΦ4 in

theorem hgt_sub_eq (e e' : Λ Φ) (n n' : ℕ) (M : Matrix (Fin 2) (Fin 2) ℚ_[r]) (hM : IsUnit M)
    (he : E e = (r : ℚ_[r]) ^ n • M) (he' : E e' = (r : ℚ_[r]) ^ n' • M) :
    (hgt e : ℤ) - 4 * n = (hgt e' : ℤ) - 4 * n' := by
  have hprod : ((r ^ n' : ℕ) : Λ Φ) * e = ((r ^ n : ℕ) : Λ Φ) * e' := hinj (by
    rw [map_mul, map_mul, E_natCast_pow, E_natCast_pow, he, he', smul_mul_assoc, smul_mul_assoc,
      one_mul, one_mul, smul_smul, smul_smul, ← pow_add, ← pow_add, add_comm])
  have hfe : Module.Finite K (Ker e) := finite_ker_of_isUnit E hinj m hm hΦ4 e (he ▸ isUnit_pow_smul hM n)
  have hfe' : Module.Finite K (Ker e') :=
    finite_ker_of_isUnit E hinj m hm hΦ4 e' (he' ▸ isUnit_pow_smul hM n')
  have h1 := (finite_and_hgt_mul _ e (finite_ker_natCast_pow hΦ4 n') hfe).2
  have h2 := (finite_and_hgt_mul _ e' (finite_ker_natCast_pow hΦ4 n) hfe').2
  rw [hgt_natCast_pow hΦ4] at h1 h2
  have key : n' * 4 + hgt e = n * 4 + hgt e' := by rw [← h1, ← h2, hprod]
  omega

include hm in

theorem exists_rep (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r]) :
    ∃ q : Λ Φ × ℕ, E q.1 = (r : ℚ_[r]) ^ q.2 • (g : Matrix (Fin 2) (Fin 2) ℚ_[r]) := by
  obtain ⟨e, n, h⟩ := exists_apply_eq_pow_smul E m hm (g : Matrix (Fin 2) (Fin 2) ℚ_[r])
  exact ⟨(e, n), h⟩

def rep (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r]) : Λ Φ × ℕ :=
  Classical.choose (exists_rep E m hm g)

theorem rep_spec (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r]) :
    E (rep E m hm g).1 = (r : ℚ_[r]) ^ (rep E m hm g).2 • (g : Matrix (Fin 2) (Fin 2) ℚ_[r]) :=
  Classical.choose_spec (exists_rep E m hm g)

def ν₀ (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r]) : ℤ :=
  (hgt (rep E m hm g).1 : ℤ) - 4 * (rep E m hm g).2

include hinj hΦ4 in

theorem ν₀_eq (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r]) (e : Λ Φ) (n : ℕ)
    (he : E e = (r : ℚ_[r]) ^ n • (g : Matrix (Fin 2) (Fin 2) ℚ_[r])) :
    ν₀ E m hm g = (hgt e : ℤ) - 4 * n :=
  hgt_sub_eq E hinj m hm hΦ4 _ e _ n _ (Units.isUnit g) (rep_spec E m hm g) he

include hinj hΦ4 in
theorem ν₀_mul (g₁ g₂ : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r]) :
    ν₀ E m hm (g₁ * g₂) = ν₀ E m hm g₁ + ν₀ E m hm g₂ := by
  have h₁ := rep_spec E m hm g₁
  have h₂ := rep_spec E m hm g₂
  set e₁ := (rep E m hm g₁).1
  set n₁ := (rep E m hm g₁).2
  set e₂ := (rep E m hm g₂).1
  set n₂ := (rep E m hm g₂).2
  have h12 : E (e₁ * e₂) = (r : ℚ_[r]) ^ (n₁ + n₂) •
      ((g₁ * g₂ : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r]) : Matrix (Fin 2) (Fin 2) ℚ_[r]) := by
    rw [map_mul, h₁, h₂, Units.val_mul, smul_mul_assoc, mul_smul_comm, smul_smul, ← pow_add, add_comm]
  have hu₁ : IsUnit (E e₁) := h₁ ▸ isUnit_pow_smul (Units.isUnit g₁) n₁
  have hu₂ : IsUnit (E e₂) := h₂ ▸ isUnit_pow_smul (Units.isUnit g₂) n₂
  have hadd := (finite_and_hgt_mul e₁ e₂ (finite_ker_of_isUnit E hinj m hm hΦ4 e₁ hu₁)
    (finite_ker_of_isUnit E hinj m hm hΦ4 e₂ hu₂)).2
  rw [ν₀_eq E hinj m hm hΦ4 (g₁ * g₂) (e₁ * e₂) (n₁ + n₂) h12, hadd]
  show ((hgt e₁ + hgt e₂ : ℕ) : ℤ) - 4 * ((n₁ + n₂ : ℕ) : ℤ) =
    ((hgt e₁ : ℤ) - 4 * n₁) + ((hgt e₂ : ℤ) - 4 * n₂)
  push_cast
  ring

include hinj hΦ4 in

def ν : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r] →* Multiplicative ℤ :=
  MonoidHom.mk' (fun g => Multiplicative.ofAdd (ν₀ E m hm g)) fun a b => by
    simp only [ν₀_mul E hinj m hm hΦ4, ofAdd_add]

theorem ν_apply (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r]) :
    ν E hinj m hm hΦ4 g = Multiplicative.ofAdd (ν₀ E m hm g) := rfl

include hinj hΦ4 in

theorem ν₀_scalar (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r])
    (hg : (g : Matrix (Fin 2) (Fin 2) ℚ_[r]) = (r : ℚ_[r]) • (1 : Matrix (Fin 2) (Fin 2) ℚ_[r])) :
    ν₀ E m hm g = 4 := by
  have he : E ((r ^ 1 : ℕ) : Λ Φ) = (r : ℚ_[r]) ^ 0 • (g : Matrix (Fin 2) (Fin 2) ℚ_[r]) := by
    rw [E_natCast_pow, pow_one, pow_zero, one_smul, hg]
  rw [ν₀_eq E hinj m hm hΦ4 g _ 0 he, hgt_natCast_pow hΦ4]
  norm_num

include hinj hΦ4 in

theorem ν₀_coe (e : Λ Φ) (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r])
    (hg : (g : Matrix (Fin 2) (Fin 2) ℚ_[r]) = E e) :
    ν₀ E m hm g = hgt e ∧ Module.Finite K (Ker e) ∧
      ∀ (κ : Type u) [Field κ] (f : K →+* κ),
        Module.finrank κ (KerAlgebra (Series.map f (ser e))) = r ^ hgt e := by
  have he : E e = (r : ℚ_[r]) ^ 0 • (g : Matrix (Fin 2) (Fin 2) ℚ_[r]) := by rw [pow_zero, one_smul, hg]
  have hfin : Module.Finite K (Ker e) := finite_ker_of_isUnit E hinj m hm hΦ4 e (hg ▸ Units.isUnit g)
  refine ⟨?_, hfin, fun κ _ f => finrank_fibre e hfin κ f⟩
  rw [ν₀_eq E hinj m hm hΦ4 g e 0 he]
  simp

end Frame

theorem main {r : ℕ} [Fact r.Prime] (K : Type u) [Field K] [CharP K r]
    (Φ : FormalODModule r K) (hΦ4 : Φ.HasHeight 4)
    (E : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) ℚ_[r])
    (hE : Function.Injective E ∧
      ∃ m : ℕ,
        (∀ A : Matrix (Fin 2) (Fin 2) ℤ_[r], ∃ e, E e = (r : ℚ_[r]) ^ m • A.map ((↑) : ℤ_[r] → ℚ_[r])) ∧
        (∀ e, ∃ A : Matrix (Fin 2) (Fin 2) ℤ_[r], (r : ℚ_[r]) ^ m • E e = A.map ((↑) : ℤ_[r] → ℚ_[r]))) :
    ∃ ν : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r] →* Multiplicative ℤ,
      (∀ g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r],
        (g : Matrix (Fin 2) (Fin 2) ℚ_[r]) = (r : ℚ_[r]) • (1 : Matrix (Fin 2) (Fin 2) ℚ_[r]) →
          ν g = Multiplicative.ofAdd (4 : ℤ)) ∧
      ∀ (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}))
        (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r]), (g : Matrix (Fin 2) (Fin 2) ℚ_[r]) = E e →
        ∃ h : ℕ, ν g = Multiplicative.ofAdd (h : ℤ) ∧
          Module.Finite K (FormalODModule.KerAlgebra (e : MvFormalGroup.End Φ.F).toPowerSeries) ∧
          ∀ (κ : Type u) [Field κ] (f : K →+* κ),
            Module.finrank κ
              (FormalODModule.KerAlgebra (Series.map f (e : MvFormalGroup.End Φ.F).toPowerSeries)) =
              r ^ h := by
  obtain ⟨hinj, m, hm, -⟩ := hE
  refine ⟨ν E hinj m hm hΦ4, fun g hg => ?_, fun e g hg => ?_⟩
  · rw [ν_apply, ν₀_scalar E hinj m hm hΦ4 g hg]
  · obtain ⟨h1, h2, h3⟩ := ν₀_coe E hinj m hm hΦ4 e g hg
    exact ⟨hgt e, by rw [ν_apply, h1], h2, h3⟩

end R4HeightHom

end

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal in
theorem solution
    {r : ℕ} [Fact r.Prime] (K : Type u) [Field K] [CharP K r]
    (Φ : FormalODModule r K) (hΦ4 : Φ.HasHeight 4)
    (E : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) ℚ_[r])
    (hE : Function.Injective E ∧
      ∃ m : ℕ,
        (∀ A : Matrix (Fin 2) (Fin 2) ℤ_[r], ∃ e, E e = (r : ℚ_[r]) ^ m • A.map ((↑) : ℤ_[r] → ℚ_[r])) ∧
        (∀ e, ∃ A : Matrix (Fin 2) (Fin 2) ℤ_[r], (r : ℚ_[r]) ^ m • E e = A.map ((↑) : ℤ_[r] → ℚ_[r]))) :
    ∃ ν : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r] →* Multiplicative ℤ,
      (∀ g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r],
        (g : Matrix (Fin 2) (Fin 2) ℚ_[r]) = (r : ℚ_[r]) • (1 : Matrix (Fin 2) (Fin 2) ℚ_[r]) →
          ν g = Multiplicative.ofAdd (4 : ℤ)) ∧
      ∀ (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}))
        (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r]), (g : Matrix (Fin 2) (Fin 2) ℚ_[r]) = E e →
        ∃ h : ℕ, ν g = Multiplicative.ofAdd (h : ℤ) ∧
          Module.Finite K (FormalODModule.KerAlgebra (e : MvFormalGroup.End Φ.F).toPowerSeries) ∧
          ∀ (κ : Type u) [Field κ] (f : K →+* κ),
            Module.finrank κ
              (FormalODModule.KerAlgebra (Series.map f (e : MvFormalGroup.End Φ.F).toPowerSeries)) =
              r ^ h :=
  R4HeightHom.main K Φ hΦ4 E hE

end S_CerednikDrinfeld_FormalODModule_exists_monoidHom_generalLinearGroup_finrank_kerAlgebra_eq_pow_of_hasHeight
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_monoidHom_generalLinearGroup_finrank_kerAlgebra_eq_pow_of_hasHeight (solution)
