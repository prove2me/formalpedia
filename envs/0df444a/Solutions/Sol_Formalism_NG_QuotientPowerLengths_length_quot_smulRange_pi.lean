-- Prove2me | solution 1 for Formalism.NG.QuotientPowerLengths.length_quot_smulRange_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:09:27.865164+00:00
-- url     : https://prove2.me/submissions/1603db8d-5a8a-4441-907d-b7609a1d9025

import Definitions.Def_Formalism_CharacterColumnKernels_StatementN
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LenCokerOfDetNeZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthQuotSmulRangeFree
import Theorems.Thm_Formalism_NG_QuotientPowerLengths_mem_smulRange
import Theorems.Thm_Formalism_NG_QuotientPowerLengths_quot_mono
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module IsDiscreteValuationRing
noncomputable section
namespace Formalism.NG
namespace QuotientPowerLengths
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
private theorem length_quot_span_pow_irreducible {ϖ : O} (hϖ : Irreducible ϖ) (k : ℕ) :
    Module.length O (O ⧸ Ideal.span {ϖ ^ k}) = k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hle : Ideal.span {ϖ ^ (k + 1)} ≤ Ideal.span {ϖ ^ k} := by
      rw [Ideal.span_singleton_le_span_singleton]
      exact pow_dvd_pow ϖ (Nat.le_add_right k 1)
    have hcomap : Ideal.span {ϖ} ≤
        Submodule.comap (LinearMap.mulLeft O (ϖ ^ k)) (Ideal.span {ϖ ^ (k + 1)}) := by
      intro a ha
      rw [Submodule.mem_comap, LinearMap.mulLeft_apply]
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      exact Ideal.mem_span_singleton'.mpr ⟨b, by ring⟩
    let f := Submodule.mapQ (Ideal.span {ϖ}) (Ideal.span {ϖ ^ (k + 1)})
      (LinearMap.mulLeft O (ϖ ^ k)) hcomap
    let g := Submodule.factor hle
    have hf : Function.Injective f := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro z hz
      obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ z
      have h0 : (Submodule.Quotient.mk (ϖ ^ k * a) : O ⧸ Ideal.span {ϖ ^ (k + 1)}) = 0 := hz
      rw [Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton'] at h0
      obtain ⟨b, hb⟩ := h0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton']
      refine ⟨b, ?_⟩
      have hne : ϖ ^ k ≠ 0 := pow_ne_zero _ hϖ.ne_zero
      apply mul_left_cancel₀ hne
      rw [← hb]
      ring
    have hg : Function.Surjective g := Submodule.factor_surjective hle
    have hex : Function.Exact f g := by
      intro z
      constructor
      · intro h0
        obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ z
        have h1 : (Submodule.Quotient.mk a : O ⧸ Ideal.span {ϖ ^ k}) = 0 := h0
        rw [Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton'] at h1
        obtain ⟨b, rfl⟩ := h1
        refine ⟨Submodule.Quotient.mk b, ?_⟩
        show (Submodule.Quotient.mk (ϖ ^ k * b) : O ⧸ Ideal.span {ϖ ^ (k + 1)}) =
          Submodule.Quotient.mk (b * ϖ ^ k)
        rw [mul_comm (ϖ ^ k) b]
      · rintro ⟨y, rfl⟩
        obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective _ y
        show (Submodule.Quotient.mk (ϖ ^ k * b) : O ⧸ Ideal.span {ϖ ^ k}) = 0
        rw [Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton']
        exact ⟨b, mul_comm _ _⟩
    have hlen := Module.length_eq_add_of_exact f g hf hg hex
    have h1 : Module.length O (O ⧸ Ideal.span {ϖ}) = 1 := by
      rw [Module.length_eq_one_iff, isSimpleModule_iff_isCoatom]
      first
        | exact (PrincipalIdealRing.isMaximal_of_irreducible hϖ).out
        | exact Ideal.isMaximal_def.mp (PrincipalIdealRing.isMaximal_of_irreducible hϖ)
    rw [hlen, h1, ih]
    first
      | (push_cast; ring)
      | simp [add_comm]
private theorem length_quot_smulRange_eq_addVal (l : O) :
    Module.length O (O ⧸ smulRange O l) = addVal O l := by
  have hspan : smulRange O l = Ideal.span {l} := by
    ext x
    rw [mem_smulRange, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, by rw [smul_eq_mul, mul_comm]⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, by rw [smul_eq_mul, mul_comm]⟩
  rw [hspan]
  have hirr : ∃ ϖ : O, Irreducible ϖ := by
    first
      | exact IsDiscreteValuationRing.exists_irreducible O
      | exact IsDiscreteValuationRing.exists_irreducible
  obtain ⟨ϖ, hϖ⟩ := hirr
  by_cases hl : l = 0
  · subst hl
    rw [addVal_zero]
    have hbound : ∀ k : ℕ, (k : ℕ∞) ≤ Module.length O (O ⧸ Ideal.span {(0 : O)}) := by
      intro k
      rw [← length_quot_span_pow_irreducible hϖ k]
      apply quot_mono
      rw [Ideal.span_singleton_eq_bot.mpr rfl]
      exact bot_le
    by_contra hne
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hne
    have h := hbound (m + 1)
    rw [← hm] at h
    have h' : m + 1 ≤ m := by exact_mod_cast h
    omega
  · obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl hϖ
    rw [Ideal.span_singleton_mul_left_unit u.isUnit, length_quot_span_pow_irreducible hϖ k, addVal_mul,
      addVal_pow, addVal_uniformizer hϖ, IsDiscreteValuationRing.addVal_eq_zero_of_unit]
    simp
variable {V : Type*} [AddCommGroup V] [Module (FractionRing O) V] [Module O V]
  [IsScalarTower O (FractionRing O) V] [FiniteDimensional (FractionRing O) V]
section Eig
variable {X : Type*} {T : Subalgebra O (X → O)} {act : T →+* Module.End (FractionRing O) V}
end Eig
end QuotientPowerLengths
open QuotientPowerLengths
end Formalism.NG
end
end

set_option autoImplicit false
open Module IsDiscreteValuationRing
noncomputable section
open Formalism Formalism.NG
open Formalism.NG.QuotientPowerLengths
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
namespace Formalism.NG.QuotientPowerLengths
theorem _root_.solution (n : ℕ) (l : O) :
    Module.length O ((Fin n → O) ⧸ smulRange (Fin n → O) l) = n * addVal O l := by
  have hpi : smulRange (Fin n → O) l = Submodule.pi Set.univ (fun _ : Fin n => smulRange O l) := by
    ext x
    rw [mem_smulRange, Submodule.mem_pi]
    constructor
    · rintro ⟨y, rfl⟩ i _
      exact (mem_smulRange l _).mpr ⟨y i, rfl⟩
    · intro h
      choose y hy using fun i => (mem_smulRange l (x i)).mp (h i (Set.mem_univ i))
      exact ⟨y, by ext i; exact hy i⟩
  rw [hpi]
  let e := Submodule.quotientPi (fun _ : Fin n => smulRange O l)
  have hlen : Module.length O ((Fin n → O) ⧸ Submodule.pi Set.univ (fun _ : Fin n => smulRange O l)) =
      Module.length O (Fin n → (O ⧸ smulRange O l)) := by
    first
      | exact e.length_eq
      | exact le_antisymm (Module.length_le_of_injective e.toLinearMap e.injective)
          (Module.length_le_of_injective e.symm.toLinearMap e.symm.injective)
  rw [hlen, Module.length_pi_of_fintype, length_quot_smulRange_eq_addVal l]
  first
    | simp
    | simp [Finset.sum_const, nsmul_eq_mul]
end Formalism.NG.QuotientPowerLengths
