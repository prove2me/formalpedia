-- Prove2me | solution 1 for Deformation.mem_wittHom_of_mem_fontaineKer_of_verschiebung_mem_wittHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/c62fba99-9c8d-5294-90fc-0a7c77d9f1fd

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_Dieudonne_FontaineHodge
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_mem_wittHom_of_mem_fontaineKer_of_verschiebung_mem_wittHom

set_option autoImplicit false

open scoped TensorProduct

universe u v w u'

namespace FontaineCriterion

open Deformation Deformation.TruncWitt

section Core

variable {ℛ : Type u} [CommRing ℛ] {p : ℕ} [hp : Fact p.Prime]
variable {A : Type v} [CommRing A] {π : ℛ →+* A}

omit hp in
theorem natCast_eq_zero_of_ker_eq (hker : RingHom.ker π = Ideal.span {(p : ℛ)}) : (p : A) = 0 := by
  have : (p : ℛ) ∈ RingHom.ker π := hker ▸ Ideal.mem_span_singleton_self _
  rwa [RingHom.mem_ker, map_natCast] at this

theorem eq_zero_of_mem_fontaineKer_of_forall_coeff_castSucc_eq_zero
    (hp' : (p : ℛ) ∈ nonZeroDivisors ℛ) (hker : RingHom.ker π = Ideal.span {(p : ℛ)}) {n : ℕ}
    {a : TruncatedWittVector p (n + 1) A} (ha : a ∈ fontaineKer p (n + 1) π)
    (h0 : ∀ i : Fin n, a.coeff i.castSucc = 0) : a = 0 := by
  obtain ⟨X, rfl, hX⟩ := ha
  rw [Nat.add_sub_cancel] at hX
  have hXi : ∀ i < n, X.coeff i ∈ Ideal.span {(p : ℛ)} := by
    intro i hi
    rw [← hker, RingHom.mem_ker, ← WittVector.map_coeff]
    have := h0 ⟨i, hi⟩
    rwa [WittVector.coeff_truncate] at this
  have hsplit : WittVector.ghostComponent n X =
      (∑ i ∈ Finset.range n, (p : ℛ) ^ i * X.coeff i ^ p ^ (n - i)) + (p : ℛ) ^ n * X.coeff n := by
    rw [WittGhost.ghostComponent_eq_sum, Finset.sum_range_succ, Nat.sub_self, pow_zero, pow_one]
  have hS : (∑ i ∈ Finset.range n, (p : ℛ) ^ i * X.coeff i ^ p ^ (n - i)) ∈
      Ideal.span {(p : ℛ) ^ (n + 1)} :=
    Ideal.sum_mem _ fun i hi => by
      rw [Finset.mem_range] at hi
      exact WittGhost.pow_mul_pow_mem_span_pow (hXi i hi) hi.le
  have hlast : (p : ℛ) ^ n * X.coeff n ∈ Ideal.span {(p : ℛ) ^ (n + 1)} := by
    have : (p : ℛ) ^ n * X.coeff n = WittVector.ghostComponent n X -
        ∑ i ∈ Finset.range n, (p : ℛ) ^ i * X.coeff i ^ p ^ (n - i) := by
      rw [hsplit]; ring
    rw [this]
    exact sub_mem hX hS
  have hXn : X.coeff n ∈ Ideal.span {(p : ℛ)} := by
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 hlast
    have hpn : (p : ℛ) ^ n ∈ nonZeroDivisors ℛ := Submonoid.pow_mem _ hp' n
    have h0 : (X.coeff n - (p : ℛ) * c) * (p : ℛ) ^ n = 0 := by
      rw [sub_mul, mul_comm (X.coeff n), hc]; ring
    have := mem_nonZeroDivisors_iff_right.1 hpn _ h0
    rw [sub_eq_zero] at this
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hpA : (p : A) = 0 := natCast_eq_zero_of_ker_eq hker
  refine TruncatedWittVector.ext fun i => ?_
  rw [TruncatedWittVector.coeff_zero]
  refine Fin.lastCases ?_ (fun j => h0 j) i
  rw [WittVector.coeff_truncate, WittVector.map_coeff, Fin.val_last]
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 hXn
  rw [← hb, map_mul, map_natCast, hpA, mul_zero]

theorem eq_zero_of_mem_fontaineKer_of_verschiebung_eq_zero
    (hp' : (p : ℛ) ∈ nonZeroDivisors ℛ) (hker : RingHom.ker π = Ideal.span {(p : ℛ)}) {n : ℕ}
    {a : TruncatedWittVector p n A} (ha : a ∈ fontaineKer p n π)
    (hV : TruncWitt.verschiebung a = 0) : a = 0 := by
  cases n with
  | zero => exact TruncatedWittVector.ext fun i => i.elim0
  | succ n =>
    refine eq_zero_of_mem_fontaineKer_of_forall_coeff_castSucc_eq_zero hp' hker ha fun i => ?_
    have h := congrArg (TruncatedWittVector.coeff i.succ) hV
    rw [TruncatedWittVector.coeff_zero] at h
    have hi : (i : ℕ) + 1 < n + 1 := by omega
    have h' := coeff_verschiebung_succ a i hi
    rw [show (⟨(i : ℕ) + 1, hi⟩ : Fin (n + 1)) = i.succ from Fin.ext rfl] at h'
    rw [h'] at h
    rw [show i.castSucc = ⟨(i : ℕ), Nat.lt_of_succ_lt hi⟩ from Fin.ext rfl]
    exact h

theorem eq_of_mem_fontaineKer_of_verschiebung_eq
    (hp' : (p : ℛ) ∈ nonZeroDivisors ℛ) (hker : RingHom.ker π = Ideal.span {(p : ℛ)}) {n : ℕ}
    {b c : TruncatedWittVector p n A} (hb : b ∈ fontaineKer p n π) (hc : c ∈ fontaineKer p n π)
    (hV : TruncWitt.verschiebung b = TruncWitt.verschiebung c) : b = c := by
  have hbc : b - c ∈ fontaineKer p n π := sub_mem hb hc
  have hV' : TruncWitt.verschiebung (b - c) = 0 := by rw [map_sub, hV, sub_self]
  exact sub_eq_zero.1 (eq_zero_of_mem_fontaineKer_of_verschiebung_eq_zero hp' hker hbc hV')

end Core

section Abstract

variable {p : ℕ} [hp : Fact p.Prime] {n : ℕ}
variable {k : Type u} [CommRing k] {A : Type v} [CommRing A] [Bialgebra k A]
variable {ℛ : Type w} [CommRing ℛ] {ℛ₂ : Type u'} [CommRing ℛ₂]

theorem mem_wittHom_of_lift (π : ℛ →+* A) (π₂ : ℛ₂ →+* TensorProduct k A A)
    (Δ ι₁ ι₂ : ℛ →+* ℛ₂)
    (hΔ : π₂.comp Δ = (comulRingHom k A).comp π)
    (h₁ : π₂.comp ι₁ =
      (Algebra.TensorProduct.includeLeft : A →ₐ[k] TensorProduct k A A).toRingHom.comp π)
    (h₂ : π₂.comp ι₂ =
      (Algebra.TensorProduct.includeRight : A →ₐ[k] TensorProduct k A A).toRingHom.comp π)
    (hp₂ : (p : ℛ₂) ∈ nonZeroDivisors ℛ₂) (hker₂ : RingHom.ker π₂ = Ideal.span {(p : ℛ₂)})
    {a : TruncatedWittVector p n A} (ha : a ∈ fontaineKer p n π)
    (hVa : TruncWitt.verschiebung a ∈ wittHom k p n A) : a ∈ wittHom k p n A := by
  rw [mem_wittHom_iff] at hVa ⊢
  rw [map_verschiebung, map_verschiebung, map_verschiebung, ← map_add] at hVa
  exact eq_of_mem_fontaineKer_of_verschiebung_eq hp₂ hker₂ (map_mem_fontaineKer Δ _ π₂ hΔ ha)
    (add_mem (map_mem_fontaineKer ι₁ _ π₂ h₁ ha) (map_mem_fontaineKer ι₂ _ π₂ h₂ ha)) hVa

end Abstract

section TwoVariables

variable {𝓞 : Type u} [CommRing 𝓞] (k : Type v) [CommRing k] [Algebra 𝓞 k]
variable (ℛ : Type w) [CommRing ℛ] [Algebra 𝓞 ℛ]

noncomputable def redLeft : ℛ →ₐ[𝓞] (k ⊗[𝓞] ℛ) ⊗[k] (k ⊗[𝓞] ℛ) :=
  (Algebra.TensorProduct.includeLeft (S := 𝓞)).comp Algebra.TensorProduct.includeRight

noncomputable def redRight : ℛ →ₐ[𝓞] (k ⊗[𝓞] ℛ) ⊗[k] (k ⊗[𝓞] ℛ) :=
  ((Algebra.TensorProduct.includeRight :
        k ⊗[𝓞] ℛ →ₐ[k] (k ⊗[𝓞] ℛ) ⊗[k] (k ⊗[𝓞] ℛ)).restrictScalars 𝓞).comp
      Algebra.TensorProduct.includeRight

noncomputable def pi2 : ℛ ⊗[𝓞] ℛ →ₐ[𝓞] (k ⊗[𝓞] ℛ) ⊗[k] (k ⊗[𝓞] ℛ) :=
  Algebra.TensorProduct.lift (redLeft k ℛ) (redRight k ℛ)
    (fun _ _ => Commute.all (S := (k ⊗[𝓞] ℛ) ⊗[k] (k ⊗[𝓞] ℛ)) _ _)

noncomputable def theta : (k ⊗[𝓞] ℛ) ⊗[k] (k ⊗[𝓞] ℛ) →ₐ[k] k ⊗[𝓞] (ℛ ⊗[𝓞] ℛ) :=
  Algebra.TensorProduct.lift
    (Algebra.TensorProduct.map (AlgHom.id k k)
      (Algebra.TensorProduct.includeLeft : ℛ →ₐ[𝓞] ℛ ⊗[𝓞] ℛ))
    ((Algebra.TensorProduct.map (AlgHom.id k k)
      (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] ℛ ⊗[𝓞] ℛ)).restrictScalars k)
    (fun _ _ => Commute.all (S := k ⊗[𝓞] (ℛ ⊗[𝓞] ℛ)) _ _)

variable {k ℛ}

theorem redLeft_apply (r : ℛ) :
    redLeft k ℛ r = ((1 : k) ⊗ₜ[𝓞] r) ⊗ₜ[k] (1 : k ⊗[𝓞] ℛ) := rfl

theorem redRight_apply (r : ℛ) :
    redRight k ℛ r = (1 : k ⊗[𝓞] ℛ) ⊗ₜ[k] ((1 : k) ⊗ₜ[𝓞] r) := rfl

theorem pi2_tmul (r s : ℛ) :
    pi2 k ℛ (r ⊗ₜ[𝓞] s) = ((1 : k) ⊗ₜ[𝓞] r) ⊗ₜ[k] ((1 : k) ⊗ₜ[𝓞] s) := by
  rw [pi2, Algebra.TensorProduct.lift_tmul, redLeft_apply, redRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

theorem theta_pi2 (z : ℛ ⊗[𝓞] ℛ) : theta k ℛ (pi2 k ℛ z) = (1 : k) ⊗ₜ[𝓞] z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, TensorProduct.tmul_zero]
  | tmul r s =>
    rw [pi2_tmul, theta, Algebra.TensorProduct.lift_tmul]
    simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, TensorProduct.tmul_add]

theorem pi2_comp_includeLeft :
    (pi2 (𝓞 := 𝓞) k ℛ).toRingHom.comp
        (Algebra.TensorProduct.includeLeft : ℛ →ₐ[𝓞] ℛ ⊗[𝓞] ℛ).toRingHom =
      (Algebra.TensorProduct.includeLeft :
          k ⊗[𝓞] ℛ →ₐ[k] (k ⊗[𝓞] ℛ) ⊗[k] (k ⊗[𝓞] ℛ)).toRingHom.comp
        (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] k ⊗[𝓞] ℛ).toRingHom := by
  refine RingHom.ext fun r => ?_
  change pi2 k ℛ (r ⊗ₜ 1) = ((1 : k) ⊗ₜ r) ⊗ₜ 1
  rw [pi2_tmul]
  rfl

theorem pi2_comp_includeRight :
    (pi2 (𝓞 := 𝓞) k ℛ).toRingHom.comp
        (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] ℛ ⊗[𝓞] ℛ).toRingHom =
      (Algebra.TensorProduct.includeRight :
          k ⊗[𝓞] ℛ →ₐ[k] (k ⊗[𝓞] ℛ) ⊗[k] (k ⊗[𝓞] ℛ)).toRingHom.comp
        (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] k ⊗[𝓞] ℛ).toRingHom := by
  refine RingHom.ext fun r => ?_
  change pi2 k ℛ (1 ⊗ₜ r) = 1 ⊗ₜ ((1 : k) ⊗ₜ r)
  rw [pi2_tmul]
  rfl

theorem ker_pi2 (hk : Function.Surjective (algebraMap 𝓞 k)) {p : ℕ}
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)}) :
    RingHom.ker (pi2 (𝓞 := 𝓞) k ℛ).toRingHom = Ideal.span {(p : ℛ ⊗[𝓞] ℛ)} := by
  apply le_antisymm
  · intro z hz
    rw [RingHom.mem_ker] at hz
    have h1 : (1 : k) ⊗ₜ[𝓞] z = 0 := by
      rw [← theta_pi2 z]
      change theta k ℛ ((pi2 k ℛ).toRingHom z) = 0
      rw [hz, map_zero]
    have : z ∈ RingHom.ker (SpecialFibre.reduction 𝓞 k (ℛ ⊗[𝓞] ℛ)) := by
      rw [RingHom.mem_ker, SpecialFibre.reduction_apply, h1]
    rwa [SpecialFibre.ker_reduction_eq_span hk hker] at this
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, map_natCast]
    have h := SpecialFibre.natCast_eq_zero (ℛ := ℛ) hk hker
    rw [← map_natCast (algebraMap (k ⊗[𝓞] ℛ) ((k ⊗[𝓞] ℛ) ⊗[k] (k ⊗[𝓞] ℛ))), h, map_zero]

theorem natCast_mem_nonZeroDivisors_tensor [Module.Flat 𝓞 ℛ] {p : ℕ}
    (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞) : (p : ℛ ⊗[𝓞] ℛ) ∈ nonZeroDivisors (ℛ ⊗[𝓞] ℛ) := by
  have hreg : IsSMulRegular (ℛ ⊗[𝓞] ℛ) (p : 𝓞) := Module.Flat.isSMulRegular_of_nonZeroDivisors hp
  refine mem_nonZeroDivisors_iff_right.2 fun x hx => hreg ?_
  change (p : 𝓞) • x = (p : 𝓞) • (0 : ℛ ⊗[𝓞] ℛ)
  rw [smul_zero, Algebra.smul_def, map_natCast, mul_comm, hx]

theorem natCast_mem_nonZeroDivisors [Module.Flat 𝓞 ℛ] {p : ℕ}
    (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞) : (p : ℛ) ∈ nonZeroDivisors ℛ := by
  have hreg : IsSMulRegular ℛ (p : 𝓞) := Module.Flat.isSMulRegular_of_nonZeroDivisors hp
  refine mem_nonZeroDivisors_iff_right.2 fun x hx => hreg ?_
  change (p : 𝓞) • x = (p : 𝓞) • (0 : ℛ)
  rw [smul_zero, Algebra.smul_def, map_natCast, mul_comm, hx]

end TwoVariables

section Comul

variable {𝓞 : Type u} [CommRing 𝓞] {k : Type v} [CommRing k] [Algebra 𝓞 k]
variable {ℛ : Type w} [CommRing ℛ] [Bialgebra 𝓞 ℛ]

theorem comul_one_tmul (r : ℛ) :
    Coalgebra.comul (R := k) ((1 : k) ⊗ₜ[𝓞] r) = pi2 k ℛ (Coalgebra.comul (R := 𝓞) r) := by
  rw [TensorProduct.comul_tmul, CommSemiring.comul_apply k 1]
  induction Coalgebra.comul (R := 𝓞) r using TensorProduct.induction_on with
  | zero => rw [TensorProduct.tmul_zero, LinearEquiv.map_zero, map_zero]
  | tmul x y =>
    rw [pi2_tmul]
    rfl
  | add x y hx hy => rw [TensorProduct.tmul_add, map_add, map_add, hx, hy]

theorem pi2_comp_comul :
    (pi2 (𝓞 := 𝓞) k ℛ).toRingHom.comp (Bialgebra.comulAlgHom 𝓞 ℛ).toRingHom =
      (Bialgebra.comulAlgHom k (k ⊗[𝓞] ℛ)).toRingHom.comp
        (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] k ⊗[𝓞] ℛ).toRingHom := by
  refine RingHom.ext fun r => ?_
  exact (comul_one_tmul r).symm

end Comul

section Criterion

variable {𝓞 : Type u} [CommRing 𝓞] {p : ℕ} [hp : Fact p.Prime]
variable {k : Type v} [CommRing k] [Algebra 𝓞 k]
variable {ℛ : Type w} [CommRing ℛ] [Bialgebra 𝓞 ℛ]

theorem criterion (hp' : (p : 𝓞) ∈ nonZeroDivisors 𝓞) [Module.Flat 𝓞 ℛ]
    (hk : Function.Surjective (algebraMap 𝓞 k))
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)})
    {n : ℕ} {a : TruncatedWittVector p n (k ⊗[𝓞] ℛ)}
    (ha : a ∈ fontaineKer p n
      (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] k ⊗[𝓞] ℛ).toRingHom)
    (hVa : TruncWitt.verschiebung a ∈ wittHom k p n (k ⊗[𝓞] ℛ)) :
    a ∈ wittHom k p n (k ⊗[𝓞] ℛ) := by

  have crit := @mem_wittHom_of_lift p _ n k _ (k ⊗[𝓞] ℛ) inferInstance inferInstance ℛ _
    (ℛ ⊗[𝓞] ℛ) inferInstance
    (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] k ⊗[𝓞] ℛ).toRingHom
    (pi2 (𝓞 := 𝓞) k ℛ).toRingHom
    (Bialgebra.comulAlgHom 𝓞 ℛ).toRingHom
    (Algebra.TensorProduct.includeLeft : ℛ →ₐ[𝓞] ℛ ⊗[𝓞] ℛ).toRingHom
    (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] ℛ ⊗[𝓞] ℛ).toRingHom
  exact crit pi2_comp_comul pi2_comp_includeLeft pi2_comp_includeRight
    (natCast_mem_nonZeroDivisors_tensor hp') (ker_pi2 hk hker) ha hVa

end Criterion

end FontaineCriterion

theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    {k : Type v} [CommRing k] [Algebra 𝓞 k]
    (hk : Function.Surjective (algebraMap 𝓞 k))
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)})
    (ℛ : Type w) [CommRing ℛ] [Bialgebra 𝓞 ℛ] [Module.Flat 𝓞 ℛ]
    {n : ℕ} {a : TruncatedWittVector p n (TensorProduct 𝓞 k ℛ)}
    (ha : a ∈ Deformation.TruncWitt.fontaineKer p n
      (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] TensorProduct 𝓞 k ℛ).toRingHom)
    (hVa : Deformation.TruncWitt.verschiebung a ∈
      Deformation.wittHom k p n (TensorProduct 𝓞 k ℛ)) :
    a ∈ Deformation.wittHom k p n (TensorProduct 𝓞 k ℛ) :=
  FontaineCriterion.criterion hp hk hker ha hVa

end S_Deformation_mem_wittHom_of_mem_fontaineKer_of_verschiebung_mem_wittHom
end P2MW
export P2MW.S_Deformation_mem_wittHom_of_mem_fontaineKer_of_verschiebung_mem_wittHom (solution)
