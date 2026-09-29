-- Prove2me | solution 1 for ExtCitation.LocalLevel.isDiscreteValuationRing_Rw
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/d20e4abf-b0a5-50cf-9fcc-69ae5c758053

import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Theorems.Thm_ExtCitation_LocalLevel_mem_Rw_iff_isIntegral
import Theorems.Thm_integralClosure_finite_and_isDiscreteValuationRing_and_isAdicComplete_maximalIdeal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_LocalLevel_isDiscreteValuationRing_Rw

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
p2m_reactivate "P2MW.S_ExtCitation_LocalLevel_isDiscreteValuationRing_Rw.Ws26T4"

open Ws26T4 ExtCitation.LocalLevel in
theorem solution (q : ℕ) [Fact q.Prime]
    (Kw : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] Kw] :
    IsDiscreteValuationRing (Rw q Kw) := by
  obtain ⟨-, hdvr, -⟩ :=
    integralClosure.finite_and_isDiscreteValuationRing_and_isAdicComplete_maximalIdeal ℤ_[q] ℚ_[q] Kw
  haveI := hdvr
  haveI : IsPrincipalIdealRing (Rw q Kw) :=
    IsPrincipalIdealRing.of_surjective (intClosureEquivRw q Kw).toRingHom (intClosureEquivRw q Kw).surjective
  refine IsDiscreteValuationRing.mk ?_
  intro hbot
  have h := natCast_mem_maximalIdeal q Kw
  rw [hbot, Ideal.mem_bot] at h
  exact natCast_ne_zero q Kw h

end S_ExtCitation_LocalLevel_isDiscreteValuationRing_Rw
end P2MW
export P2MW.S_ExtCitation_LocalLevel_isDiscreteValuationRing_Rw (solution)
