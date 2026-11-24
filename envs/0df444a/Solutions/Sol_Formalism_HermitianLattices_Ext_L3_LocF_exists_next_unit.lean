-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LocF.exists_next_unit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:29.620812+00:00
-- url     : https://prove2.me/submissions/84d47242-6ee7-48c3-9677-fa59bc36f308

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomFrame
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthUnitFrame

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LocF
open Formalism.HermitianLattices.Ext.L3.WA
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {h : V →ₗ⋆[K] V →ₗ[K] K} {M : AddSubgroup V}
namespace Formalism.HermitianLattices.Ext.L3.LocF
theorem _root_.solution (hS : IsHermSemilocal S)
    (hloc : ∀ a ∈ S, ∀ b ∈ S, star a = a → star b = b → ¬ IsUnitIn S a → ¬ IsUnitIn S b →
      IsUnitIn S (a + b + 1))
    (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0) (hM : IsSelfDualMod S h M)
    {ι : Type*} [DecidableEq ι] (x : ι → V) (s : Finset ι) (hxM : ∀ i ∈ s, x i ∈ M)
    (hxo : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → h (x i) (x j) = 0)
    (hxu : ∀ i ∈ s, IsUnitIn S (h (x i) (x i)))
    (v : V) (hv : v ≠ 0) (hvo : ∀ i ∈ s, h (x i) v = 0) :
    ∃ z ∈ M, IsUnitIn S (h z z) ∧ ∀ i ∈ s, h (x i) z = 0 := by
  have hquad : ∀ (p q : V) (m : K), h (p + m • q) (p + m • q) =
      h p p + m * h p q + star m * h q p + star m * m * h q q := by
    intro p q m
    simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply, map_smul, RingHom.id_apply]
    ring
  obtain ⟨hstar, -, hunram, hprinc, -⟩ := hS
  obtain ⟨hsm, hint, hdual, hspan⟩ := hM
  have hsym : ∀ a b : V, star (h a b) = h b a := fun a b => by
    rw [← starRingEnd_apply]
    exact hs.eq a b
  have hunit : ∀ a : K, IsUnitIn S a ↔ a ≠ 0 ∧ a ∈ S ∧ a⁻¹ ∈ S := fun a => by
    unfold IsUnitIn
    exact Iff.rfl

  obtain ⟨t, ht0, htM⟩ := hspan v
  have hv' : t • v ≠ 0 := smul_ne_zero ht0 hv
  have hvo' : ∀ i ∈ s, h (x i) (t • v) = 0 := fun i hi => by
    rw [map_smul, hvo i hi, smul_zero]

  obtain ⟨α, ⟨m0, hm0, rfl⟩, hα0, hα⟩ := hprinc
    { carrier := {a | ∃ m ∈ M, h m (t • v) = a}
      zero_mem' := ⟨0, M.zero_mem, by simp⟩
      add_mem' := by
        rintro _ _ ⟨m1, hm1, rfl⟩ ⟨m2, hm2, rfl⟩
        exact ⟨m1 + m2, M.add_mem hm1 hm2, by simp [mul_add]⟩
      neg_mem' := by
        rintro _ ⟨m, hm, rfl⟩
        exact ⟨-m, M.neg_mem hm, by simp⟩ }
    (by
      rintro c hc _ ⟨m, hm, rfl⟩
      refine ⟨star c • m, hsm _ (hstar c hc) m hm, ?_⟩
      simp only [map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, star_star, smul_eq_mul,
        RingHom.id_apply]
      try ring)
    ⟨h (t • v) (t • v), ⟨t • v, htM, rfl⟩, fun h0 => hv' (hd _ h0)⟩
    ⟨1, one_ne_zero, by
      rintro _ ⟨m, hm, rfl⟩
      rw [one_mul]
      exact hint m hm _ htM⟩
  set u := h m0 (t • v) with hu

  set w := u⁻¹ • (t • v) with hw
  have hwM : w ∈ M := by
    apply hdual
    intro m hm
    rw [hw, map_smul, smul_eq_mul, mul_comm]
    exact hα _ ⟨m, hm, rfl⟩
  have hm0w : h m0 w = 1 := by
    rw [hw, map_smul, smul_eq_mul, ← hu]
    exact inv_mul_cancel₀ hα0
  have hwo : ∀ i ∈ s, h (x i) w = 0 := fun i hi => by
    rw [hw, map_smul, hvo' i hi, smul_zero]

  set c : ι → K := fun i => h (x i) m0 * (h (x i) (x i))⁻¹ with hc
  set y := m0 - ∑ i ∈ s, c i • x i with hy
  have hcS : ∀ i ∈ s, c i ∈ S := fun i hi =>
    S.mul_mem (hint _ (hxM i hi) _ hm0) ((hunit _).mp (hxu i hi)).2.2
  have hyM : y ∈ M := by
    refine M.sub_mem hm0 (M.sum_mem fun i hi => ?_)
    exact hsm _ (hcS i hi) _ (hxM i hi)
  have hyo : ∀ j ∈ s, h (x j) y = 0 := by
    intro j hj
    rw [hy, map_sub, map_sum]
    simp only [map_smul, smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · have hne : h (x j) (x j) ≠ 0 := ((hunit _).mp (hxu j hj)).1
      simp only [hc]
      rw [inv_mul_cancel_right₀ hne, sub_self]
    · intro i hi hij
      rw [hxo j hj i hi (Ne.symm hij), mul_zero]
    · intro hjs
      exact absurd hj hjs
  have hyw : h y w = 1 := by
    rw [hy, map_sub, map_sum, LinearMap.sub_apply]
    first
      | rw [LinearMap.sum_apply]
      | rw [LinearMap.coe_fn_sum, Finset.sum_apply]
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_zero (fun i hi => by rw [hwo i hi, mul_zero]), hm0w, sub_zero]
  have hwy : h w y = 1 := by
    rw [← hsym, hyw, star_one]

  obtain ⟨θ, hθ, hδ⟩ := hunram
  obtain ⟨hδ0, hδS, hδi⟩ := (hunit _).mp hδ
  set μ := θ * (θ - star θ)⁻¹ with hμ
  have hμS : μ ∈ S := S.mul_mem hθ hδi
  have e1 : μ * (θ - star θ) = θ := by
    rw [hμ]
    exact inv_mul_cancel_right₀ hδ0 θ
  have e2 : star μ * -(θ - star θ) = star θ := by
    have h' := congrArg star e1
    rw [star_mul', star_sub, star_star] at h'
    linear_combination h'
  have hμμ : μ + star μ = 1 := by
    have : (μ + star μ) * (θ - star θ) = 1 * (θ - star θ) := by
      linear_combination e1 - e2
    exact mul_right_cancel₀ hδ0 this
  by_cases ha : IsUnitIn S (h y y)
  · exact ⟨y, hyM, ha, hyo⟩
  by_cases hb : IsUnitIn S (h w w)
  · exact ⟨w, hwM, hb, hwo⟩
  refine ⟨y + μ • w, M.add_mem hyM (hsm _ hμS _ hwM), ?_, ?_⟩
  · have hzz : h (y + μ • w) (y + μ • w) = h y y + star μ * μ * h w w + 1 := by
      rw [hquad, hyw, hwy]
      linear_combination hμμ
    rw [hzz]
    have hwwS : h w w ∈ S := hint _ hwM _ hwM
    have hbS : star μ * μ * h w w ∈ S := S.mul_mem (S.mul_mem (hstar _ hμS) hμS) hwwS
    apply hloc _ (hint _ hyM _ hyM) _ hbS (hsym y y)
    · rw [star_mul', star_mul', star_star, hsym w w]
      ring
    · exact ha
    · intro hbu
      apply hb
      obtain ⟨hb0, -, hbi⟩ := (hunit _).mp hbu
      have hww0 : h w w ≠ 0 := fun h0 => hb0 (by rw [h0, mul_zero])
      have hμ0 : star μ * μ ≠ 0 := fun h0 => hb0 (by rw [h0, zero_mul])
      refine (hunit _).mpr ⟨hww0, hwwS, ?_⟩
      have : (h w w)⁻¹ = star μ * μ * (star μ * μ * h w w)⁻¹ := by
        rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ hμ0, one_mul]
      rw [this]
      exact S.mul_mem (S.mul_mem (hstar _ hμS) hμS) hbi
  · intro i hi
    rw [map_add, map_smul, hyo i hi, hwo i hi, smul_zero, add_zero]
end Formalism.HermitianLattices.Ext.L3.LocF
