-- Prove2me | solution 1 for FinFlatHopf.inertiaFixed_valuationSubring_dvr_fixer_le_inertia
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/eaa8afbb-7083-575e-95f9-215265a7f66c

import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FieldTheory_RatAlgClosureGalois
import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Theorems.Thm_ValuationSubring_exists_eq_pow_mul_of_forall_mem_inertiaSubgroupIn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FinFlatHopf_inertiaFixed_valuationSubring_dvr_fixer_le_inertia

set_option Elab.async false

open scoped Pointwise

namespace W01aShared

variable {P : ValuationSubring (AlgebraicClosure ℚ)}
variable {B : Subring (AlgebraicClosure ℚ)}

private lemma w01a_fix_inv {x : AlgebraicClosure ℚ}
    (hx : ∀ σ ∈ P.inertiaSubgroupIn ℚ, σ x = x) :
    ∀ σ ∈ P.inertiaSubgroupIn ℚ, σ x⁻¹ = x⁻¹ := fun σ hσ => by
  rw [map_inv₀, hx σ hσ]

private lemma w01a_isUnit_iff
    (hB : ∀ x : AlgebraicClosure ℚ, x ∈ B ↔
      (x ∈ P ∧ ∀ σ ∈ P.inertiaSubgroupIn ℚ, σ x = x))
    {x : AlgebraicClosure ℚ} (hxB : x ∈ B) :
    IsUnit (⟨x, hxB⟩ : B) ↔ x ≠ 0 ∧ x⁻¹ ∈ P := by
  constructor
  · rintro ⟨u, hu⟩
    have hxu : IsUnit (x : AlgebraicClosure ℚ) := by
      have h := u.isUnit.map B.subtype
      rwa [hu] at h
    have hx0 : x ≠ 0 := hxu.ne_zero
    refine ⟨hx0, ?_⟩
    have hinv : ((↑u⁻¹ : B) : AlgebraicClosure ℚ) = x⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      have h := congrArg (fun b : B => (b : AlgebraicClosure ℚ)) u.inv_mul
      push_cast at h
      rw [hu] at h
      exact h
    rw [← hinv]
    exact ((hB _).mp (↑u⁻¹ : B).2).1
  · rintro ⟨hx0, hxinvP⟩
    have hxinvB : x⁻¹ ∈ B :=
      (hB _).mpr ⟨hxinvP, w01a_fix_inv (((hB _).mp hxB).2)⟩
    exact ⟨⟨⟨x, hxB⟩, ⟨x⁻¹, hxinvB⟩,
      Subtype.ext (by push_cast; exact mul_inv_cancel₀ hx0),
      Subtype.ext (by push_cast; exact inv_mul_cancel₀ hx0)⟩, rfl⟩

private lemma w01a_mem_nonunits_iff
    (hB : ∀ x : AlgebraicClosure ℚ, x ∈ B ↔
      (x ∈ P ∧ ∀ σ ∈ P.inertiaSubgroupIn ℚ, σ x = x))
    {x : AlgebraicClosure ℚ} (hxB : x ∈ B) :
    (⟨x, hxB⟩ : B) ∈ nonunits B ↔ x ∈ P.nonunits := by
  rw [mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or, w01a_isUnit_iff hB hxB]
  constructor
  · intro h
    by_cases hx0 : x = 0
    · exact Or.inl hx0
    · right
      intro hxinvP
      exact h ⟨hx0, hxinvP⟩
  · rintro (rfl | hxinvP) ⟨hx0, hinvP⟩
    · exact hx0 rfl
    · exact hxinvP hinvP

end W01aShared

namespace W01cLegs

open W01aShared

private lemma w01c_natCast_fixed (P : ValuationSubring (AlgebraicClosure ℚ)) (n : ℕ) :
    ∀ σ ∈ P.inertiaSubgroupIn ℚ, σ (n : AlgebraicClosure ℚ) = n :=
  fun σ _ => map_natCast (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) n

private lemma w01c_coe_natCast_B (B : Subring (AlgebraicClosure ℚ)) (n : ℕ) :
    ((n : B) : AlgebraicClosure ℚ) = (n : AlgebraicClosure ℚ) :=
  map_natCast (Subring.subtype B) n

private lemma w01c_pQbar_ne_zero (p : ℕ) [Fact p.Prime] :
    ((p : ℕ) : AlgebraicClosure ℚ) ≠ 0 := by
  exact_mod_cast (Fact.out : p.Prime).ne_zero

variable (p : ℕ) [Fact p.Prime]
  (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
  (B : Subring (AlgebraicClosure ℚ))
  (hB : ∀ x : AlgebraicClosure ℚ, x ∈ B ↔
    (x ∈ P ∧ ∀ σ ∈ P.inertiaSubgroupIn ℚ, σ x = x))

include hP hB

omit [Fact p.Prime] hP in

private lemma w01c_natCast_mem_B (n : ℕ) : (n : AlgebraicClosure ℚ) ∈ B :=
  (hB _).mpr ⟨natCast_mem P n, w01c_natCast_fixed P n⟩

omit [Fact p.Prime] in

private lemma w01c_p_mem_nonunits_B : (p : B) ∈ nonunits B := by
  have hpB : (p : AlgebraicClosure ℚ) ∈ B := w01c_natCast_mem_B P B hB p
  have heq : (p : B) = (⟨(p : AlgebraicClosure ℚ), hpB⟩ : B) := by
    ext; exact w01c_coe_natCast_B B p
  rw [heq, w01a_mem_nonunits_iff hB hpB]
  exact hP

private lemma w01c_exists_unit_mul_pow (x : B) (hx : x ≠ 0) :
    ∃ (k : ℕ) (u : Bˣ), x = u * (p : B) ^ k := by
  set c := (x : AlgebraicClosure ℚ) with hc_def
  have hcB : c ∈ B := x.2
  obtain ⟨hcP, hcfix⟩ := (hB c).mp hcB
  have hc0 : c ≠ 0 := fun h => hx (Subtype.ext h)
  obtain ⟨s, u, huP, huinvP, hcu⟩ :=
    ValuationSubring.exists_eq_pow_mul_of_forall_mem_inertiaSubgroupIn p P hP c hcP hc0 hcfix
  have hu0 : u ≠ 0 := by
    rintro rfl; simp only [mul_zero] at hcu; exact hc0 hcu
  have hufix : ∀ σ ∈ P.inertiaSubgroupIn ℚ, σ u = u := by
    intro σ hσ
    have hps0 : ((p : ℕ) : AlgebraicClosure ℚ) ^ s ≠ 0 :=
      pow_ne_zero s (w01c_pQbar_ne_zero p)
    have hσp : σ (((p : ℕ) : AlgebraicClosure ℚ) ^ s) = ((p : ℕ) : AlgebraicClosure ℚ) ^ s := by
      rw [map_pow]; exact congrArg (· ^ s) (w01c_natCast_fixed P p σ hσ)
    have hσcu : σ c = ((p : ℕ) : AlgebraicClosure ℚ) ^ s * σ u := by
      rw [hcu, map_mul, hσp]
    rw [hcfix σ hσ, hcu] at hσcu
    exact (mul_left_cancel₀ hps0 hσcu).symm
  have huB : u ∈ B := (hB u).mpr ⟨huP, hufix⟩
  have hUu : IsUnit (⟨u, huB⟩ : B) := (w01a_isUnit_iff hB huB).mpr ⟨hu0, huinvP⟩
  obtain ⟨U, hU⟩ := hUu
  refine ⟨s, U, ?_⟩
  apply Subtype.ext
  have hUcoe : ((U : B) : AlgebraicClosure ℚ) = u := by rw [hU]
  push_cast
  rw [hUcoe, ← hc_def, hcu]; ring

private lemma w01c_legA :
    (p : B) ∈ nonunits B ∧ ∀ x : B, x ≠ 0 → ∃ (k : ℕ) (u : Bˣ), x = u * (p : B) ^ k :=
  ⟨w01c_p_mem_nonunits_B p P hP B hB, w01c_exists_unit_mul_pow p P hP B hB⟩

omit [Fact p.Prime] hB in

private lemma w01c_coprime_inv_mem_P (n : ℕ) (hn : n.Coprime p) :
    ((n : ℕ) : AlgebraicClosure ℚ)⁻¹ ∈ P := by

  have hpM : (p : P) ∈ IsLocalRing.maximalIdeal (P : Type) := by
    have h := (ValuationSubring.coe_mem_nonunits_iff (A := P) (a := (p : P))).mp ?_
    · exact h
    · have : ((p : P) : AlgebraicClosure ℚ) = (p : AlgebraicClosure ℚ) :=
        map_natCast (algebraMap P (AlgebraicClosure ℚ)) p
      rw [this]; exact hP
  have hnU : IsUnit (n : P) := by
    by_contra hnu
    have hnM : (n : P) ∈ IsLocalRing.maximalIdeal (P : Type) := hnu

    have hcop : IsCoprime ((n : ℤ) : P) ((p : ℤ) : P) := by
      have hZ : IsCoprime (n : ℤ) (p : ℤ) := by
        rw [Int.isCoprime_iff_gcd_eq_one]
        exact_mod_cast hn
      exact hZ.map (Int.castRingHom P)
    obtain ⟨a, b, hab⟩ := hcop
    push_cast at hab
    have h1M : (1 : P) ∈ IsLocalRing.maximalIdeal (P : Type) := by
      rw [← hab]
      exact (IsLocalRing.maximalIdeal (P : Type)).add_mem
        ((IsLocalRing.maximalIdeal (P : Type)).mul_mem_left a hnM)
        ((IsLocalRing.maximalIdeal (P : Type)).mul_mem_left b hpM)
    exact (IsLocalRing.maximalIdeal.isMaximal (P : Type)).ne_top
      ((Ideal.eq_top_iff_one _).mpr h1M)

  obtain ⟨U, hU⟩ := hnU
  have hcoeU : ((U : P) : AlgebraicClosure ℚ) = (n : AlgebraicClosure ℚ) := by
    rw [hU]; exact map_natCast (algebraMap P (AlgebraicClosure ℚ)) n
  have hinv : ((↑U⁻¹ : P) : AlgebraicClosure ℚ) = ((n : ℕ) : AlgebraicClosure ℚ)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    have h := congrArg (fun x : P => (x : AlgebraicClosure ℚ)) U.inv_mul
    push_cast at h
    rw [hcoeU] at h
    exact h
  rw [← hinv]; exact (↑U⁻¹ : P).2

omit [Fact p.Prime] in

private lemma w01c_legB :
    ∀ q : ℚ, q ∈ GaloisRep.ratLocalizedAt p → algebraMap ℚ (AlgebraicClosure ℚ) q ∈ B := by
  intro q hq
  rw [hB]
  refine ⟨?_, fun σ _ => σ.commutes q⟩

  have hcop : q.den.Coprime p := hq
  have hdeninv : ((q.den : ℕ) : AlgebraicClosure ℚ)⁻¹ ∈ P := w01c_coprime_inv_mem_P p P hP q.den hcop
  have hnum : ((q.num : ℤ) : AlgebraicClosure ℚ) ∈ P := intCast_mem P q.num
  have hq_eq : algebraMap ℚ (AlgebraicClosure ℚ) q
      = ((q.num : ℤ) : AlgebraicClosure ℚ) * ((q.den : ℕ) : AlgebraicClosure ℚ)⁻¹ := by
    rw [show algebraMap ℚ (AlgebraicClosure ℚ) q = (q : AlgebraicClosure ℚ) from rfl,
      Rat.cast_def]
    ring
  rw [hq_eq]
  exact P.mul_mem _ _ hnum hdeninv

end W01cLegs

namespace FinFlatHopfW0

section general

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

private theorem w01b_mem_inertiaSubgroupIn_iff (A : ValuationSubring L) (σ : L ≃ₐ[K] L) :
    σ ∈ A.inertiaSubgroupIn K ↔ σ • A = A ∧ ∀ a ∈ A, σ a - a ∈ A.nonunits := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    change (g : L ≃ₐ[K] L) • A = A ∧ ∀ a ∈ A, (g : L ≃ₐ[K] L) a - a ∈ A.nonunits
    have hgD : (g : L ≃ₐ[K] L) • A = A := MulAction.mem_stabilizer_iff.mp g.2
    refine ⟨hgD, fun a ha => ?_⟩
    have h1 : MulSemiringAction.toRingAut (A.decompositionSubgroup K)
        (IsLocalRing.ResidueField A) g = 1 := hg
    have h2 : IsLocalRing.residue A (g • (⟨a, ha⟩ : A)) = IsLocalRing.residue A ⟨a, ha⟩ := by
      rw [IsLocalRing.ResidueField.residue_smul]
      change (MulSemiringAction.toRingAut (A.decompositionSubgroup K)
        (IsLocalRing.ResidueField A) g) (IsLocalRing.residue A ⟨a, ha⟩) = _
      rw [h1]
      rfl
    have h3 : (g • (⟨a, ha⟩ : A)) - ⟨a, ha⟩ ∈ IsLocalRing.maximalIdeal A := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]
      exact h2
    have hga : (g : L ≃ₐ[K] L) a ∈ A := (g • (⟨a, ha⟩ : A)).2
    have hmem : (g : L ≃ₐ[K] L) a - a ∈ A := sub_mem hga ha
    refine (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal).mpr ⟨hmem, ?_⟩
    have heq : (⟨(g : L ≃ₐ[K] L) a - a, hmem⟩ : A) = g • (⟨a, ha⟩ : A) - ⟨a, ha⟩ :=
      Subtype.ext rfl
    rw [heq]
    exact h3
  · rintro ⟨hD, hdisp⟩
    have hσD : σ ∈ A.decompositionSubgroup K := MulAction.mem_stabilizer_iff.mpr hD
    refine ⟨⟨σ, hσD⟩, ?_, rfl⟩
    change MulSemiringAction.toRingAut (A.decompositionSubgroup K)
      (IsLocalRing.ResidueField A) ⟨σ, hσD⟩ = 1
    apply RingEquiv.ext
    intro r
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective r
    change (⟨σ, hσD⟩ : A.decompositionSubgroup K) • IsLocalRing.residue A x = IsLocalRing.residue A x
    rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub,
      IsLocalRing.residue_eq_zero_iff]
    obtain ⟨hx', hmax⟩ := (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal).mp
      (hdisp (x : L) x.2)
    have heq : (⟨σ, hσD⟩ : A.decompositionSubgroup K) • x - x = ⟨σ (x : L) - x, hx'⟩ :=
      Subtype.ext rfl
    rw [heq]
    exact hmax

private theorem w01b_isClosed_inertiaSubgroupIn [Algebra.IsIntegral K L] (A : ValuationSubring L) :
    IsClosed ((A.inertiaSubgroupIn K : Subgroup (L ≃ₐ[K] L)) : Set (L ≃ₐ[K] L)) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro σ₀ hσ₀
  rw [Set.mem_compl_iff, SetLike.mem_coe, w01b_mem_inertiaSubgroupIn_iff] at hσ₀

  have hwit : ∃ x : L, ∀ σ : L ≃ₐ[K] L, σ x = σ₀ x → σ ∉ A.inertiaSubgroupIn K := by
    by_cases hD : σ₀ • A = A
    · have hdisp : ¬ ∀ a ∈ A, σ₀ a - a ∈ A.nonunits := fun h => hσ₀ ⟨hD, h⟩
      simp only [not_forall] at hdisp
      obtain ⟨a, ha, hna⟩ := hdisp
      refine ⟨a, fun σ hσ hσI => hna ?_⟩
      rw [w01b_mem_inertiaSubgroupIn_iff] at hσI
      rw [← hσ]
      exact hσI.2 a ha
    · have hx : ∃ x : L, ¬ (x ∈ σ₀ • A ↔ x ∈ A) := by
        by_contra h
        simp only [not_exists, not_not] at h
        exact hD (SetLike.ext h)
      obtain ⟨x, hx⟩ := hx
      refine ⟨σ₀⁻¹ x, fun σ hσ hσI => hx ?_⟩
      rw [w01b_mem_inertiaSubgroupIn_iff] at hσI
      have hσx : σ⁻¹ x = σ₀⁻¹ x := by
        calc σ⁻¹ x = σ⁻¹ (σ (σ₀⁻¹ x)) := by
                rw [hσ, AlgEquiv.aut_inv σ₀, AlgEquiv.apply_symm_apply]
          _ = σ₀⁻¹ x := by rw [AlgEquiv.aut_inv σ, AlgEquiv.symm_apply_apply]
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, ← hσx,
        ← AlgEquiv.smul_def σ⁻¹ x, ← ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
        hσI.1]
  obtain ⟨x, hx⟩ := hwit
  refine ⟨σ₀ • (MulAction.stabilizer (L ≃ₐ[K] L) x : Set (L ≃ₐ[K] L)), ?_, ?_, ?_⟩
  · rintro σ ⟨τ, hτ, rfl⟩
    refine hx _ ?_
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] at hτ
    change (σ₀ * τ) x = σ₀ x
    rw [AlgEquiv.mul_apply, hτ]
  · exact (stabilizer_isOpen_of_isIntegral x).smul σ₀
  · exact ⟨1, (MulAction.stabilizer (L ≃ₐ[K] L) x).one_mem, mul_one σ₀⟩

end general

private theorem w01b_legC (P : ValuationSubring (AlgebraicClosure ℚ))
    (B : Subring (AlgebraicClosure ℚ))
    (hB : ∀ x : AlgebraicClosure ℚ, x ∈ B ↔
      (x ∈ P ∧ ∀ σ ∈ P.inertiaSubgroupIn ℚ, σ x = x)) :
    ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ B, σ x = x) →
      σ ∈ P.inertiaSubgroupIn ℚ := by
  intro σ hσ
  let Ic : ClosedSubgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
    ⟨P.inertiaSubgroupIn ℚ, w01b_isClosed_inertiaSubgroupIn P⟩
  have key := InfiniteGalois.fixingSubgroup_fixedField Ic
  change σ ∈ Ic.1
  rw [← key, IntermediateField.mem_fixingSubgroup_iff]
  intro t ht
  rw [IntermediateField.mem_fixedField_iff] at ht
  rcases P.mem_or_inv_mem t with htP | htP
  · exact hσ t ((hB t).mpr ⟨htP, ht⟩)
  · have hinv : t⁻¹ ∈ B := (hB _).mpr ⟨htP, fun τ hτ => by rw [map_inv₀, ht τ hτ]⟩
    have h := hσ _ hinv
    rw [map_inv₀] at h
    exact inv_injective h

end FinFlatHopfW0

theorem solution (p : ℕ) [Fact p.Prime]
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (B : Subring (AlgebraicClosure ℚ))
    (hB : ∀ x : AlgebraicClosure ℚ, x ∈ B ↔
      (x ∈ P ∧ ∀ σ ∈ P.inertiaSubgroupIn ℚ, σ x = x)) :
    ((p : B) ∈ nonunits B ∧ ∀ x : B, x ≠ 0 → ∃ (k : ℕ) (u : Bˣ), x = u * (p : B) ^ k) ∧
    (∀ q : ℚ, q ∈ GaloisRep.ratLocalizedAt p → algebraMap ℚ (AlgebraicClosure ℚ) q ∈ B) ∧
    (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ B, σ x = x) →
      σ ∈ P.inertiaSubgroupIn ℚ) :=
  ⟨W01cLegs.w01c_legA p P hP B hB, W01cLegs.w01c_legB p P hP B hB,
    FinFlatHopfW0.w01b_legC P B hB⟩

end S_FinFlatHopf_inertiaFixed_valuationSubring_dvr_fixer_le_inertia
end P2MW
export P2MW.S_FinFlatHopf_inertiaFixed_valuationSubring_dvr_fixer_le_inertia (solution)
