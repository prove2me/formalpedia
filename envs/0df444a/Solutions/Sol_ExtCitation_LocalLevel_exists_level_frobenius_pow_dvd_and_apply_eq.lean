-- Prove2me | solution 1 for ExtCitation.LocalLevel.exists_level_frobenius_pow_dvd_and_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/bca0858b-bce7-5c0a-b286-0fb4d4da71a8

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_ExtCitation_InertiaKummerCharacter
import Theorems.Thm_ExtCitation_exists_level_dvd_of_frobenius_pow_mem_inertia_sup
import Theorems.Thm_ExtCitation_exists_frobenius_pow_inv_mul_mem_inertia_sup_level
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_LocalLevel_exists_level_frobenius_pow_dvd_and_apply_eq
p2m_attr_erase "instance" "instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete"

set_option autoImplicit false

open ExtCitation

namespace P2mS17LB

variable (q : Nat.Primes)

noncomputable abbrev H (F : IntermediateField ℚ (AlgebraicClosure ℚ)) : Subgroup (primeLocalGaloisGroup q) :=
  ((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q) ⊔ (F.fixingSubgroup).comap (primeLocalToGlobal q)

theorem H_anti {F F' : IntermediateField ℚ (AlgebraicClosure ℚ)} (h : F ≤ F') : H q F' ≤ H q F :=
  sup_le_sup_left (Subgroup.comap_mono (IntermediateField.fixingSubgroup_le h)) _

theorem apply_eq_of_mem_H {F : IntermediateField ℚ (AlgebraicClosure ℚ)} {ζ : AlgebraicClosure ℚ} {n : ℕ}
    (hqn : ¬ (q : ℕ) ∣ n) (hζn : ζ ^ n = 1) (hζF : ζ ∈ F) {g : primeLocalGaloisGroup q} (hg : g ∈ H q F) :
    primeLocalToGlobal q g ζ = ζ := by
  let S : Subgroup (primeLocalGaloisGroup q) :=
    (MulAction.stabilizer (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ζ).comap (primeLocalToGlobal q)
  have h1 : ((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q) ≤ S := fun i hi =>
    inertiaPullback_smul_eq_of_pow_eq_one q hi hqn hζn
  have h2 : (F.fixingSubgroup).comap (primeLocalToGlobal q) ≤ S := fun u hu =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).mp (Subgroup.mem_comap.mp hu) ζ hζF
  exact (sup_le h1 h2) hg

theorem pow_apply_eq {g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} {ζ α : AlgebraicClosure ℚ} {c : ℕ}
    (hgζ : g ζ = ζ) (hgα : g α = ζ ^ c * α) (a : ℕ) : (g ^ a) α = ζ ^ (a * c) * α := by
  induction a with
  | zero => rw [pow_zero, AlgEquiv.one_apply, zero_mul, pow_zero, one_mul]
  | succ a ih =>
    have hζa : (g ^ a) ζ = ζ := by
      clear ih
      induction a with
      | zero => rw [pow_zero, AlgEquiv.one_apply]
      | succ a ih => rw [pow_succ, AlgEquiv.mul_apply, hgζ, ih]
    rw [pow_succ, AlgEquiv.mul_apply, hgα, map_mul, map_pow, hζa, ih, ← mul_assoc, ← pow_add, Nat.succ_mul,
      add_comm]

theorem main (φ : primeLocalGaloisGroup q) (hφ : (primeLocalPlace q).IsFrobeniusAt (primeLocalToGlobal q φ) q)
    (F₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F₀]
    (n d : ℕ) (hn : 0 < n) (hd : 0 < d) (hqn : ¬ (q : ℕ) ∣ n)
    {ζ α : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ n) (hα : α ^ n = ((q : ℕ) : AlgebraicClosure ℚ)) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F₀ ≤ F ∧ FiniteDimensional ℚ F ∧ IsGalois ℚ F ∧ ζ ∈ F ∧ α ∈ F ∧
      ∀ m : ℕ, φ ^ m ∈ H q F → n * d ∣ m ∧ primeLocalToGlobal q (φ ^ m) α = α := by
  classical
  haveI : Fact (q : ℕ).Prime := ⟨q.2⟩
  haveI : Normal ℚ (AlgebraicClosure ℚ) := by
    convert @IsAlgClosure.normal ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) inferInstance
    rfl
  have hq0 : ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.2.ne_zero
  have hα0 : α ≠ 0 := by rintro rfl; rw [zero_pow hn.ne'] at hα; exact hq0 hα.symm

  let Fz : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.adjoin ℚ ({ζ, α} : Set (AlgebraicClosure ℚ))
  haveI : FiniteDimensional ℚ Fz :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hζFz : ζ ∈ Fz := IntermediateField.subset_adjoin ℚ _ (Set.mem_insert ζ {α})
  have hαFz : α ∈ Fz := IntermediateField.subset_adjoin ℚ _ (Set.mem_insert_of_mem ζ rfl)
  let F₀' : IntermediateField ℚ (AlgebraicClosure ℚ) := F₀ ⊔ Fz
  haveI : FiniteDimensional ℚ F₀' := IntermediateField.finiteDimensional_sup F₀ Fz

  obtain ⟨F₁, h01, hF₁fd, hK1⟩ :=
    exists_level_dvd_of_frobenius_pow_mem_inertia_sup q φ hφ F₀' (n * d) (Nat.mul_pos hn hd)
  haveI := hF₁fd

  obtain ⟨k, hk⟩ := exists_frobenius_pow_inv_mul_mem_inertia_sup_level q φ hφ F₁ φ⁻¹
  set f₁ : ℕ := k + 1 with hf₁def
  have hψ : φ ^ f₁ ∈ H q F₁ := by
    have : (φ ^ k)⁻¹ * φ⁻¹ = (φ ^ f₁)⁻¹ := by rw [hf₁def, pow_succ', mul_inv_rev]
    rw [this] at hk
    exact (Subgroup.inv_mem_iff _).mp hk
  have hf₁ : 0 < f₁ := Nat.succ_pos k

  obtain ⟨F₂, h12, hF₂fd, hK2⟩ :=
    exists_level_dvd_of_frobenius_pow_mem_inertia_sup q φ hφ F₁ (n * f₁) (Nat.mul_pos hn hf₁)
  haveI := hF₂fd
  let F : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.normalClosure ℚ F₂ (AlgebraicClosure ℚ)
  have h2F : F₂ ≤ F := IntermediateField.le_normalClosure F₂
  haveI : FiniteDimensional ℚ F := normalClosure.is_finiteDimensional ℚ F₂ (AlgebraicClosure ℚ)
  haveI : Normal ℚ F := normalClosure.normal ℚ F₂ (AlgebraicClosure ℚ)
  haveI : IsGalois ℚ F := IsGalois.mk
  have h0F : F₀' ≤ F := h01.trans (h12.trans h2F)
  refine ⟨F, le_sup_left.trans h0F, inferInstance, inferInstance, h0F (le_sup_right (b := Fz) hζFz),
    h0F (le_sup_right (b := Fz) hαFz), fun m hm => ?_⟩
  have hm2 : φ ^ m ∈ H q F₂ := H_anti q h2F hm
  have hm1 : φ ^ m ∈ H q F₁ := H_anti q h12 hm2
  have hm0 : φ ^ m ∈ H q F₀' := H_anti q h01 hm1
  refine ⟨hK1 m hm1, ?_⟩

  obtain ⟨c', hc'⟩ := hK2 m hm2
  set ψ := primeLocalToGlobal q (φ ^ f₁) with hψdef
  have hψζ : ψ ζ = ζ := apply_eq_of_mem_H q hqn hζ.pow_eq_one (h01 (le_sup_right (b := Fz) hζFz)) hψ
  haveI : NeZero n := ⟨hn.ne'⟩
  obtain ⟨c, -, hc⟩ : ∃ c : ℕ, c < n ∧ ψ α = ζ ^ c * α := by
    have h1 : (ψ α * α⁻¹) ^ n = 1 := by
      rw [mul_pow, ← map_pow, hα, map_natCast, inv_pow, hα, mul_inv_cancel₀ hq0]
    obtain ⟨c, hc, hζc⟩ := hζ.eq_pow_of_pow_eq_one h1
    exact ⟨c, hc, by rw [hζc, inv_mul_cancel_right₀ hα0]⟩
  have hφm : primeLocalToGlobal q (φ ^ m) = ψ ^ (n * c') := by
    rw [hc', show n * f₁ * c' = f₁ * (n * c') by ring, pow_mul, map_pow]
  rw [hφm, pow_apply_eq hψζ hc (n * c'), show n * c' * c = n * (c' * c) by ring, pow_mul, hζ.pow_eq_one, one_pow,
    one_mul]

end P2mS17LB

theorem solution (q : Nat.Primes)
    (φ : primeLocalGaloisGroup q) (hφ : (primeLocalPlace q).IsFrobeniusAt (primeLocalToGlobal q φ) q)
    (F₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F₀]
    (n d : ℕ) (hn : 0 < n) (hd : 0 < d) (hqn : ¬ (q : ℕ) ∣ n)
    {ζ α : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ n) (hα : α ^ n = ((q : ℕ) : AlgebraicClosure ℚ)) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F₀ ≤ F ∧ FiniteDimensional ℚ F ∧ IsGalois ℚ F ∧ ζ ∈ F ∧ α ∈ F ∧
      ∀ m : ℕ, φ ^ m ∈ ((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q)
                        ⊔ (F.fixingSubgroup).comap (primeLocalToGlobal q) →
        n * d ∣ m ∧ primeLocalToGlobal q (φ ^ m) α = α :=
  P2mS17LB.main q φ hφ F₀ n d hn hd hqn hζ hα

end S_ExtCitation_LocalLevel_exists_level_frobenius_pow_dvd_and_apply_eq
end P2MW
export P2MW.S_ExtCitation_LocalLevel_exists_level_frobenius_pow_dvd_and_apply_eq (solution)
