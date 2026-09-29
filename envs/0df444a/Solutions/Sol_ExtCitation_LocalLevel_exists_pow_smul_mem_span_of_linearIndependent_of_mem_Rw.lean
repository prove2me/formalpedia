-- Prove2me | solution 1 for ExtCitation.LocalLevel.exists_pow_smul_mem_span_of_linearIndependent_of_mem_Rw
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/d960b5b3-8feb-5008-8b89-7905a3e9dc06

import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Theorems.Thm_ExtCitation_LocalLevel_mem_Rw_iff_isIntegral
import Theorems.Thm_integralClosure_finite_and_isDiscreteValuationRing_and_isAdicComplete_maximalIdeal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_LocalLevel_exists_pow_smul_mem_span_of_linearIndependent_of_mem_Rw

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1600000
open ExtCitation.LocalLevel

open scoped NNReal

namespace P2mS26D3

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

end P2mS26D3
p2m_reactivate "P2MW.S_ExtCitation_LocalLevel_exists_pow_smul_mem_span_of_linearIndependent_of_mem_Rw.P2mS26D3"

namespace P2mS26D3
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

end P2mS26D3
p2m_reactivate "P2MW.S_ExtCitation_LocalLevel_exists_pow_smul_mem_span_of_linearIndependent_of_mem_Rw.P2mS26D3"

open P2mS26D3 ExtCitation.LocalLevel in
theorem solution
    (q : ℕ) [Fact q.Prime] (Kw : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] Kw]
    {ι : Type*} [Fintype ι] (w : ι → Kw) (hw : LinearIndependent ℚ_[q] w)
    (hcard : Fintype.card ι = Module.finrank ℚ_[q] Kw) :
    ∃ N : ℕ, ∀ x : Kw, x ∈ Rw q Kw →
      ((q : ℚ_[q]) ^ N) • x ∈ Submodule.span ℤ_[q] (Set.range w) := by
  classical
  set Λ := Submodule.span ℤ_[q] (Set.range w) with hΛ

  have hspan : ⊤ ≤ Submodule.span ℚ_[q] (Set.range w) :=
    (hw.span_eq_top_of_card_eq_finrank' hcard).ge
  let bK : Module.Basis ι ℚ_[q] Kw := Module.Basis.mk hw hspan
  have hbK : ∀ σ, bK σ = w σ := fun σ => Module.Basis.mk_apply hw hspan σ

  have hone : ∀ x : Kw, ∃ d : ℤ_[q], d ≠ 0 ∧ (d : ℚ_[q]) • x ∈ Λ := by
    intro x
    obtain ⟨⟨b, hb⟩, hbint⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors ℤ_[q])
      (Finset.univ.image fun σ : ι => bK.repr x σ)
    refine ⟨b, nonZeroDivisors.ne_zero hb, ?_⟩
    have hx : x = ∑ σ, bK.repr x σ • bK σ := (bK.sum_repr x).symm
    rw [hx, Finset.smul_sum]
    refine Submodule.sum_mem _ fun σ _ => ?_
    obtain ⟨z, hz⟩ := hbint (bK.repr x σ) (Finset.mem_image_of_mem _ (Finset.mem_univ σ))
    rw [smul_smul, show (b : ℚ_[q]) * bK.repr x σ = algebraMap ℤ_[q] ℚ_[q] z by
      rw [hz]; rfl, algebraMap_smul, hbK]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨σ, rfl⟩)

  obtain ⟨hfin, hdvr, -⟩ :=
    integralClosure.finite_and_isDiscreteValuationRing_and_isAdicComplete_maximalIdeal ℤ_[q] ℚ_[q] Kw
  haveI := hdvr
  haveI := hfin
  letI : Algebra ℤ_[q] (Rw q Kw) := algInt q Kw
  haveI : Module.Finite ℤ_[q] (Rw q Kw) := moduleFinite_int_Rw q Kw
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := ℤ_[q]) (M := Rw q Kw)
  choose d hd0 hdΛ using hone
  set D : ℤ_[q] := ∏ s ∈ S, d (s : Kw) with hD
  have hD0 : D ≠ 0 := Finset.prod_ne_zero_iff.mpr fun s _ => hd0 _

  have hgen : ∀ s ∈ S, (D : ℚ_[q]) • ((s : Rw q Kw) : Kw) ∈ Λ := by
    intro s hs
    obtain ⟨D', hD'⟩ : d (s : Kw) ∣ D := Finset.dvd_prod_of_mem _ hs
    rw [hD', mul_comm, PadicInt.coe_mul, mul_smul]
    rw [show ((D' : ℤ_[q]) : ℚ_[q]) • ((d (s : Kw) : ℚ_[q]) • ((s : Rw q Kw) : Kw))
        = D' • ((d (s : Kw) : ℚ_[q]) • ((s : Rw q Kw) : Kw)) from (algebraMap_smul ℚ_[q] D' _).symm.trans rfl |>.symm.symm]
    exact Submodule.smul_mem _ _ (hdΛ _)

  have hall : ∀ x : Rw q Kw, (D : ℚ_[q]) • (x : Kw) ∈ Λ := by

    have hsmul : ∀ (z : ℤ_[q]) (y : Rw q Kw), ((z • y : Rw q Kw) : Kw) = z • (y : Kw) := fun z y => by
      rw [Algebra.smul_def, Algebra.smul_def]
      push_cast
      congr 1
    let j : Rw q Kw →ₗ[ℤ_[q]] Kw :=
      { toFun := fun x => (x : Kw), map_add' := fun _ _ => rfl, map_smul' := fun z y => by rw [RingHom.id_apply]; exact hsmul z y }

    let P : Submodule ℤ_[q] Kw := Λ.comap (DistribSMul.toLinearMap ℤ_[q] Kw D)
    have hP : ∀ y : Kw, y ∈ P ↔ (D : ℚ_[q]) • y ∈ Λ := fun y => by
      show D • y ∈ Λ ↔ _
      rw [← algebraMap_smul ℚ_[q] D y]; rfl
    intro x
    have hx : (x : Kw) ∈ Submodule.map j ⊤ := ⟨x, trivial, rfl⟩
    rw [← hS, Submodule.map_span] at hx
    have hle : Submodule.span ℤ_[q] (j '' (S : Set (Rw q Kw))) ≤ P := by
      rw [Submodule.span_le]
      rintro _ ⟨s, hs, rfl⟩
      exact (hP _).mpr (hgen s hs)
    exact (hP _).mp (hle hx)

  refine ⟨D.valuation, fun x hx => ?_⟩
  have hspec := PadicInt.unitCoeff_spec hD0
  set u := PadicInt.unitCoeff hD0
  have h1 : (D : ℚ_[q]) • x ∈ Λ := hall ⟨x, hx⟩
  have hD' : ((u⁻¹ : ℤ_[q]ˣ) : ℤ_[q]) * D = (q : ℤ_[q]) ^ D.valuation := by
    conv_lhs => rw [hspec]
    rw [← mul_assoc, Units.inv_mul, one_mul]
  have h2 : ((u⁻¹ : ℤ_[q]ˣ) : ℤ_[q]) • ((D : ℚ_[q]) • x) = ((q : ℚ_[q]) ^ D.valuation) • x := by
    rw [← algebraMap_smul ℚ_[q] ((u⁻¹ : ℤ_[q]ˣ) : ℤ_[q]), smul_smul]
    congr 1
    rw [show (algebraMap ℤ_[q] ℚ_[q]) ((u⁻¹ : ℤ_[q]ˣ) : ℤ_[q]) = (((u⁻¹ : ℤ_[q]ˣ) : ℤ_[q]) : ℚ_[q]) from rfl,
      ← PadicInt.coe_mul, hD']
    push_cast
    rfl
  rw [← h2]
  exact Submodule.smul_mem _ _ h1

end S_ExtCitation_LocalLevel_exists_pow_smul_mem_span_of_linearIndependent_of_mem_Rw
end P2MW
export P2MW.S_ExtCitation_LocalLevel_exists_pow_smul_mem_span_of_linearIndependent_of_mem_Rw (solution)
