-- Prove2me | solution 1 for ExtCitation.LocalLevel.exists_ramification_inertia_Rw
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/8af56837-7594-5931-8f60-041c2a63a8c3

import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Theorems.Thm_ExtCitation_LocalLevel_mem_Rw_iff_isIntegral
import Theorems.Thm_integralClosure_finite_and_isDiscreteValuationRing_and_isAdicComplete_maximalIdeal
import Theorems.Thm_ExtCitation_LocalLevel_isDiscreteValuationRing_Rw
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_LocalLevel_exists_ramification_inertia_Rw

set_option autoImplicit false
open scoped NNReal
open Polynomial

namespace Ws26T4

open ExtCitation.LocalLevel IsLocalRing

variable (q : ℕ) [Fact q.Prime] (Kw : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] Kw]

scoped instance isScalarTower_int : IsScalarTower ℤ_[q] Kw (PadicAlgCl q) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

theorem mem_Rw_iff_mem_integralClosure (x : Kw) : x ∈ Rw q Kw ↔ x ∈ integralClosure ℤ_[q] Kw := by
  rw [mem_Rw_iff_isIntegral, mem_integralClosure_iff,
    show ((x : Kw) : PadicAlgCl q) = algebraMap Kw (PadicAlgCl q) x from rfl,
    isIntegral_algebraMap_iff (algebraMap Kw (PadicAlgCl q)).injective]

noncomputable def intClosureEquivRw : integralClosure ℤ_[q] Kw ≃+* Rw q Kw where
  toFun x := ⟨x.1, (mem_Rw_iff_mem_integralClosure q Kw x.1).mpr x.2⟩
  invFun x := ⟨x.1, (mem_Rw_iff_mem_integralClosure q Kw x.1).mp x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

@[scoped simp] theorem coe_intClosureEquivRw (x : integralClosure ℤ_[q] Kw) :
    ((intClosureEquivRw q Kw x : Rw q Kw) : Kw) = (x : Kw) := rfl

theorem norm_natCast_q : ‖((q : ℕ) : PadicAlgCl q)‖ = (q : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[q] (PadicAlgCl q)), PadicAlgCl.norm_extends, Padic.norm_p]

theorem norm_eq_one_of_isUnit {x : Rw q Kw} (hx : IsUnit x) : ‖((x : Kw) : PadicAlgCl q)‖ = 1 := by
  obtain ⟨u, hu⟩ := hx.exists_right_inv
  have hx1 : ‖((x : Kw) : PadicAlgCl q)‖ ≤ 1 := by exact_mod_cast (mem_padicIntegers_iff q).mp x.2
  have hu1 : ‖((u : Kw) : PadicAlgCl q)‖ ≤ 1 := by exact_mod_cast (mem_padicIntegers_iff q).mp u.2
  have hprod : ‖((x : Kw) : PadicAlgCl q)‖ * ‖((u : Kw) : PadicAlgCl q)‖ = 1 := by
    rw [← norm_mul]
    have := congrArg (fun t : Rw q Kw => ((t : Kw) : PadicAlgCl q)) hu
    push_cast at this
    rw [this, norm_one]
  nlinarith [norm_nonneg ((x : Kw) : PadicAlgCl q), norm_nonneg ((u : Kw) : PadicAlgCl q)]

theorem natCast_mem_maximalIdeal : ((q : ℕ) : Rw q Kw) ∈ maximalIdeal (Rw q Kw) := by
  rw [mem_maximalIdeal, mem_nonunits_iff]
  intro h
  have h1 := norm_eq_one_of_isUnit q Kw h
  push_cast at h1
  rw [norm_natCast_q] at h1
  have : (1 : ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).one_lt
  rw [inv_eq_one] at h1
  exact absurd h1 (by exact_mod_cast (Fact.out : q.Prime).one_lt.ne')

theorem natCast_ne_zero : ((q : ℕ) : Rw q Kw) ≠ 0 := by
  intro h
  have := congrArg (fun t : Rw q Kw => (t : Kw)) h
  push_cast at this
  exact (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero) this

theorem smodEq_pow_top_iff {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) (x y : R) :
    x ≡ y [SMOD I ^ n • (⊤ : Submodule R R)] ↔ x - y ∈ I ^ n := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]

theorem isAdicComplete_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] (e : A ≃+* B) [IsAdicComplete (maximalIdeal A) A] :
    IsAdicComplete (maximalIdeal B) B := by

  have hmap : Ideal.map (e : A →+* B) (maximalIdeal A) = maximalIdeal B := by
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro z hz
      rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
      rw [mem_maximalIdeal, mem_nonunits_iff] at hz
      intro hu; exact hz (by simpa using hu.map (e.symm : B →+* A))
    · intro z hz
      rw [Ideal.map_comap_of_equiv, Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
      rw [mem_maximalIdeal, mem_nonunits_iff] at hz
      intro hu; exact hz (by simpa using hu.map (e : A →+* B))
  have hmem : ∀ (n : ℕ) (z : B), z ∈ maximalIdeal B ^ n ↔ e.symm z ∈ maximalIdeal A ^ n := by
    intro n z
    rw [← hmap, ← Ideal.map_pow, Ideal.map_comap_of_equiv, Ideal.mem_comap]
  have hA : IsHausdorff (maximalIdeal A) A := inferInstance
  have hA' : IsPrecomplete (maximalIdeal A) A := inferInstance
  haveI : IsHausdorff (maximalIdeal B) B := by
    refine ⟨fun z hz => ?_⟩
    have h0 : e.symm z = 0 := by
      refine IsHausdorff.haus hA _ fun n => ?_
      rw [smodEq_pow_top_iff, sub_zero, ← hmem]
      have := hz n
      rwa [smodEq_pow_top_iff, sub_zero] at this
    simpa using congrArg e h0
  haveI : IsPrecomplete (maximalIdeal B) B := by
    refine ⟨fun f hf => ?_⟩
    have hg : ∀ {m n : ℕ}, m ≤ n →
        e.symm (f m) ≡ e.symm (f n) [SMOD maximalIdeal A ^ m • (⊤ : Submodule A A)] := by
      intro m n hmn
      rw [smodEq_pow_top_iff, ← map_sub, ← hmem]
      exact (smodEq_pow_top_iff (maximalIdeal B) m _ _).mp (hf hmn)
    obtain ⟨L, hL⟩ := IsPrecomplete.prec hA' hg
    refine ⟨e L, fun n => ?_⟩
    rw [smodEq_pow_top_iff, hmem, map_sub, RingEquiv.symm_apply_apply]
    exact (smodEq_pow_top_iff (maximalIdeal A) n _ _).mp (hL n)
  exact IsAdicComplete.mk

theorem isLocalHom_algebraMap_intClosure [IsLocalRing (integralClosure ℤ_[q] Kw)] :
    IsLocalHom (algebraMap ℤ_[q] (integralClosure ℤ_[q] Kw)) := by
  refine ⟨fun z hz => ?_⟩

  have hu : IsUnit (intClosureEquivRw q Kw (algebraMap ℤ_[q] (integralClosure ℤ_[q] Kw) z)) :=
    hz.map (intClosureEquivRw q Kw)
  have h1 := norm_eq_one_of_isUnit q Kw hu
  rw [coe_intClosureEquivRw] at h1
  have h2 : ((algebraMap ℤ_[q] (integralClosure ℤ_[q] Kw) z : Kw) : PadicAlgCl q)
      = algebraMap ℚ_[q] (PadicAlgCl q) (z : ℚ_[q]) := rfl
  rw [h2, PadicAlgCl.norm_extends] at h1
  exact PadicInt.isUnit_iff.mpr h1

end Ws26T4
p2m_reactivate "P2MW.S_ExtCitation_LocalLevel_exists_ramification_inertia_Rw.Ws26T4"

namespace Ws26T4
open ExtCitation.LocalLevel IsLocalRing

variable (q : ℕ) [Fact q.Prime] (Kw : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] Kw]

@[reducible] noncomputable def algInt : Algebra ℤ_[q] (Rw q Kw) :=
  ((intClosureEquivRw q Kw).toRingHom.comp (algebraMap ℤ_[q] (integralClosure ℤ_[q] Kw))).toAlgebra

attribute [local instance] algInt

theorem algebraMap_int_coe (z : ℤ_[q]) :
    (((algebraMap ℤ_[q] (Rw q Kw) z : Rw q Kw) : Kw) : PadicAlgCl q) = algebraMap ℚ_[q] (PadicAlgCl q) z := rfl

scoped instance isScalarTower_int_Rw : IsScalarTower ℤ_[q] (Rw q Kw) Kw :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

scoped instance isLocalHom_algebraMap_Rw : IsLocalHom (algebraMap ℤ_[q] (Rw q Kw)) := by
  refine ⟨fun z hz => ?_⟩
  have h1 := norm_eq_one_of_isUnit q Kw hz
  rw [algebraMap_int_coe, PadicAlgCl.norm_extends] at h1
  exact PadicInt.isUnit_iff.mpr h1

theorem moduleFinite_int_Rw [Module.Finite ℤ_[q] (integralClosure ℤ_[q] Kw)] : Module.Finite ℤ_[q] (Rw q Kw) := by
  let f : integralClosure ℤ_[q] Kw →ₗ[ℤ_[q]] Rw q Kw :=
    { toFun := intClosureEquivRw q Kw
      map_add' := fun x y => map_add _ x y
      map_smul' := fun z x => by
        rw [RingHom.id_apply, Algebra.smul_def, Algebra.smul_def, map_mul]
        rfl }
  exact Module.Finite.of_surjective f (intClosureEquivRw q Kw).surjective

end Ws26T4
p2m_reactivate "P2MW.S_ExtCitation_LocalLevel_exists_ramification_inertia_Rw.Ws26T4"

open Ws26T4 ExtCitation.LocalLevel IsLocalRing in
theorem solution (q : ℕ) [Fact q.Prime]
    (Kw : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] Kw] :
    ∃ e f : ℕ, 0 < e ∧ 0 < f ∧
      Ideal.span {((q : ℕ) : Rw q Kw)} = IsLocalRing.maximalIdeal (Rw q Kw) ^ e ∧
      Nat.card (IsLocalRing.ResidueField (Rw q Kw)) = q ^ f ∧
      e * f = Module.finrank ℚ_[q] Kw := by
  classical
  obtain ⟨hfin, hdvr, -⟩ :=
    integralClosure.finite_and_isDiscreteValuationRing_and_isAdicComplete_maximalIdeal ℤ_[q] ℚ_[q] Kw
  haveI := hdvr
  haveI := hfin
  haveI : IsDiscreteValuationRing (Rw q Kw) := ExtCitation.LocalLevel.isDiscreteValuationRing_Rw q Kw
  letI : Algebra ℤ_[q] (Rw q Kw) := algInt q Kw
  haveI : Module.Finite ℤ_[q] (Rw q Kw) := moduleFinite_int_Rw q Kw
  set p : Ideal ℤ_[q] := maximalIdeal ℤ_[q] with hp_def
  set P : Ideal (Rw q Kw) := maximalIdeal (Rw q Kw) with hP_def
  have hpq : p = Ideal.span {(q : ℤ_[q])} := PadicInt.maximalIdeal_eq_span_p
  have hp0 : p ≠ ⊥ := by
    rw [hpq, Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast (Fact.out : q.Prime).ne_zero

  have hmap : Ideal.map (algebraMap ℤ_[q] (Rw q Kw)) p = Ideal.span {((q : ℕ) : Rw q Kw)} := by
    rw [hpq, Ideal.map_span, Set.image_singleton, map_natCast]
  have hmap0 : Ideal.map (algebraMap ℤ_[q] (Rw q Kw)) p ≠ ⊥ := by
    rw [hmap, Ne, Ideal.span_singleton_eq_bot]; exact natCast_ne_zero q Kw
  have hmapP : Ideal.map (algebraMap ℤ_[q] (Rw q Kw)) p ≤ P := by
    rw [hmap, Ideal.span_singleton_le_iff_mem]; exact natCast_mem_maximalIdeal q Kw
  have hP0 : P ≠ ⊥ := IsDiscreteValuationRing.not_a_field _

  have hfs : IsDedekindDomain.primesOverFinset p (Rw q Kw) = {P} := by
    ext Q
    simp only [Finset.mem_singleton, IsDedekindDomain.primesOverFinset, Multiset.mem_toFinset]
    constructor
    · intro hQ
      have hQp : Prime Q := UniqueFactorizationMonoid.prime_of_factor Q hQ
      exact IsLocalRing.eq_maximalIdeal
        (Ring.DimensionLEOne.maximalOfPrime hQp.ne_zero (Ideal.isPrime_of_prime hQp))
    · rintro rfl
      have hPprime : Prime P := Ideal.prime_of_isPrime hP0 inferInstance
      obtain ⟨Q, hQ, hPQ⟩ := UniqueFactorizationMonoid.exists_mem_factors_of_dvd hmap0 hPprime.irreducible
        (Ideal.dvd_iff_le.mpr hmapP)
      rw [associated_iff_eq.mp hPQ]
      exact hQ
  have hsum := Ideal.sum_ramification_inertia (Rw q Kw) ℚ_[q] (Kw : Type) (p := p) hp0
  rw [hfs, Finset.sum_singleton] at hsum
  set e := p.ramificationIdx' P with he
  set f := p.inertiaDeg' P with hf
  refine ⟨e, f, ?_, ?_, ?_, ?_, hsum⟩
  · exact Nat.pos_of_ne_zero (Ideal.IsDedekindDomain.ramificationIdx_ne_zero hmap0 inferInstance hmapP)
  · exact Ideal.inertiaDeg'_pos p P
  ·
    rw [← hmap]
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Rw q Kw)
    obtain ⟨k, hk⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hmap0 hϖ
    have hPk : Ideal.map (algebraMap ℤ_[q] (Rw q Kw)) p = P ^ k := by
      rw [hk, hP_def, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
    have hek : e = k := by
      rw [he]
      refine Ideal.ramificationIdx_spec hPk.le ?_
      intro hle
      have hlt := Ideal.pow_succ_lt_pow hP0 k
      exact absurd (hPk.symm.le.trans hle) (not_le_of_gt hlt)
    rw [hPk, hek]
  ·
    have hcardp : Nat.card (ResidueField ℤ_[q]) = q :=
      (Nat.card_congr PadicInt.residueField.toEquiv).trans (Nat.card_zmod q)
    have h1 : Nat.card (ResidueField (Rw q Kw))
        = Nat.card (ResidueField ℤ_[q]) ^ Module.finrank (ResidueField ℤ_[q]) (ResidueField (Rw q Kw)) :=
      Module.natCard_eq_pow_finrank
    rw [h1, hcardp, hf, Ideal.inertiaDeg_algebraMap]
    rfl

end S_ExtCitation_LocalLevel_exists_ramification_inertia_Rw
end P2MW
export P2MW.S_ExtCitation_LocalLevel_exists_ramification_inertia_Rw (solution)
