-- Prove2me | solution 1 for CuspForm.HasNebentypus.sum_filter_eq_of_sum_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/f03989d3-6d76-52b2-a64a-91f8dd9e5f89

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_HasNebentypus_sum_filter_eq_of_sum_eq

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

noncomputable section

namespace NebentypusDirectSum

theorem eq_zero_of_sum_eq_zero {K V P ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : P → V →ₗ[K] V) (β : ι → P → K) (s : Finset ι) :
    ∀ v : ι → V,
      (∀ i ∈ s, ∀ p, T p (v i) = β i p • v i) →
      (∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∃ p, β i p ≠ β j p) →
      ∑ i ∈ s, v i = 0 → ∀ i ∈ s, v i = 0 := by
  classical
  induction s using Finset.strongInduction with
  | H s ih =>
    intro v hv hdist hsum i₀ hi₀
    by_cases hj : ∃ j ∈ s, j ≠ i₀
    · obtain ⟨j, hj, hji⟩ := hj
      obtain ⟨p, hp⟩ := hdist i₀ hi₀ j hj (Ne.symm hji)

      set v' : ι → V := fun i => (β i p - β j p) • v i with hv'
      have hsum' : ∑ i ∈ s.erase j, v' i = 0 := by
        rw [Finset.sum_erase _ (by simp [hv'])]
        have : ∑ i ∈ s, v' i = T p (∑ i ∈ s, v i) - β j p • ∑ i ∈ s, v i := by
          rw [map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [hv i hi p, ← sub_smul]
        rw [this, hsum, map_zero, smul_zero, sub_zero]
      have hv'eig : ∀ i ∈ s.erase j, ∀ q, T q (v' i) = β i q • v' i := by
        intro i hi q
        rw [hv']
        simp only [map_smul]
        rw [hv i (Finset.mem_of_mem_erase hi) q, smul_comm]
      have hdist' : ∀ i ∈ s.erase j, ∀ i' ∈ s.erase j, i ≠ i' → ∃ q, β i q ≠ β i' q :=
        fun i hi i' hi' hne => hdist i (Finset.mem_of_mem_erase hi) i' (Finset.mem_of_mem_erase hi') hne
      have h0 := ih (s.erase j) (Finset.erase_ssubset hj) v' hv'eig hdist' hsum' i₀
        (Finset.mem_erase.mpr ⟨Ne.symm hji, hi₀⟩)
      rw [hv'] at h0
      exact (smul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hp)
    ·
      push Not at hj
      have hs : s = {i₀} := by
        ext i
        simp only [Finset.mem_singleton]
        exact ⟨fun hi => hj i hi, fun h => h ▸ hi₀⟩
      rw [hs, Finset.sum_singleton] at hsum
      exact hsum

variable {N : ℕ} {k : ℤ}

local notation "Γ₁(" M ")" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

def J (γ : SL(2, ℤ)) (τ : UpperHalfPlane) : ℂ := ((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)

theorem J_ne_zero (γ : SL(2, ℤ)) (τ : UpperHalfPlane) : J γ τ ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  simp only [J, Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul,
    add_zero, Complex.zero_im, UpperHalfPlane.coe_im] at him
  have hc : (γ 1 0 : ℤ) = 0 := by
    have := mul_eq_zero.mp him
    rcases this with h1 | h1
    · exact_mod_cast h1
    · exact absurd h1 τ.im_pos.ne'
  have hre := congrArg Complex.re h
  simp only [J, Complex.intCast_re, zero_mul, Complex.zero_re, hc, Int.cast_zero, zero_add] at hre
  have hd : (γ 1 1 : ℤ) = 0 := by exact_mod_cast hre
  have hdet := γ.det_coe
  rw [Matrix.det_fin_two, hc, hd, mul_zero, mul_zero, sub_zero] at hdet
  exact zero_ne_one hdet

def twist (k : ℤ) (γ : SL(2, ℤ)) : (UpperHalfPlane → ℂ) →ₗ[ℂ] (UpperHalfPlane → ℂ) where
  toFun F := fun τ => (J γ τ ^ k)⁻¹ * F (γ • τ)
  map_add' F G := by funext τ; simp only [Pi.add_apply]; ring
  map_smul' c F := by funext τ; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem twist_apply (γ : SL(2, ℤ)) (F : UpperHalfPlane → ℂ) (τ : UpperHalfPlane) :
    twist k γ F τ = (J γ τ ^ k)⁻¹ * F (γ • τ) := rfl

theorem twist_coe_of_hasNebentypus {ψ : DirichletCharacter ℂ N} {g : CuspForm Γ₁(N) k}
    (hg : CuspForm.HasNebentypus ψ g) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 N) :
    twist k γ ⇑g = ψ ((γ 1 1 : ℤ) : ZMod N) • ⇑g := by
  funext τ
  rw [twist_apply, hg γ hγ τ, Pi.smul_apply, smul_eq_mul]
  have hJ : J γ τ ^ k ≠ 0 := zpow_ne_zero _ (J_ne_zero γ τ)
  change (J γ τ ^ k)⁻¹ * (ψ _ * (J γ τ ^ k * g τ)) = _
  field_simp

theorem exists_gamma0_apply_ne [NeZero N] {ψ ψ' : DirichletCharacter ℂ N} (h : ψ ≠ ψ') :
    ∃ γ : SL(2, ℤ), γ ∈ Gamma0 N ∧ ψ ((γ 1 1 : ℤ) : ZMod N) ≠ ψ' ((γ 1 1 : ℤ) : ZMod N) := by
  by_contra hall
  push Not at hall
  apply h
  refine MulChar.ext fun u => ?_

  set d : ℕ := (u : ZMod N).val with hd
  have hcop : Nat.Coprime d N := ZMod.val_coe_unit_coprime u
  obtain ⟨x, y, hxy⟩ : IsCoprime (d : ℤ) (N : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
  let γ : SL(2, ℤ) := ⟨!![x, -y; (N : ℤ), (d : ℤ)], by
    rw [Matrix.det_fin_two_of]; linear_combination hxy⟩
  have hγ : γ ∈ Gamma0 N := by rw [Gamma0_mem]; simp [γ]
  have hγd : ((γ 1 1 : ℤ) : ZMod N) = (u : ZMod N) := by
    simp [γ, hd]
  have := hall γ hγ
  rwa [hγd] at this

theorem coe_sum {ι : Type*} (s : Finset ι) (g : ι → CuspForm Γ₁(N) k) :
    (⇑(∑ i ∈ s, g i) : UpperHalfPlane → ℂ) = ∑ i ∈ s, ⇑(g i) := by
  have := map_sum (FunLike.coeAddMonoidHom (CuspForm Γ₁(N) k) UpperHalfPlane ℂ) g s
  exact this

theorem main [NeZero N] [DecidableEq (DirichletCharacter ℂ N)] {ι : Type*} (s : Finset ι)
    (χ : ι → DirichletCharacter ℂ N) (g : ι → CuspForm Γ₁(N) k)
    (hg : ∀ i ∈ s, CuspForm.HasNebentypus (χ i) (g i))
    {ε : DirichletCharacter ℂ N} {f : CuspForm Γ₁(N) k} (hf : CuspForm.HasNebentypus ε f)
    (hsum : ∑ i ∈ s, g i = f) :
    ∑ i ∈ s.filter (fun i => χ i = ε), g i = f := by
  classical

  set T : Finset (DirichletCharacter ℂ N) := insert ε (s.image χ) with hT

  set v : DirichletCharacter ℂ N → (UpperHalfPlane → ℂ) :=
    fun ψ => (⇑(∑ i ∈ s.filter (fun i => χ i = ψ), g i) : UpperHalfPlane → ℂ) - if ψ = ε then ⇑f else 0
    with hv

  have hvsum : ∑ ψ ∈ T, v ψ = 0 := by
    rw [hv]
    simp only
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' T ε, if_pos (Finset.mem_insert_self _ _)]
    have h1 : ∑ ψ ∈ T, (⇑(∑ i ∈ s.filter (fun i => χ i = ψ), g i) : UpperHalfPlane → ℂ)
        = ⇑(∑ i ∈ s, g i) := by
      rw [← coe_sum T (fun ψ => ∑ i ∈ s.filter (fun i => χ i = ψ), g i)]
      congr 1
      exact Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_insert_of_mem
        (Finset.mem_image_of_mem χ hi)) g
    rw [h1, hsum, sub_self]

  let P := {γ : SL(2, ℤ) // γ ∈ Gamma0 N}
  let D : P → (UpperHalfPlane → ℂ) →ₗ[ℂ] (UpperHalfPlane → ℂ) := fun γ => twist k γ.1
  let β : DirichletCharacter ℂ N → P → ℂ := fun ψ γ => ψ ((γ.1 1 1 : ℤ) : ZMod N)
  have heig : ∀ ψ ∈ T, ∀ γ : P, D γ (v ψ) = β ψ γ • v ψ := by
    intro ψ _ γ
    rw [hv]
    simp only [D, β, map_sub, smul_sub]
    congr 1
    · rw [coe_sum, map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      obtain ⟨his, hχ⟩ := Finset.mem_filter.mp hi
      rw [← hχ]
      exact twist_coe_of_hasNebentypus (hg i his) γ.1 γ.2
    · split_ifs with hψ
      · rw [hψ]; exact twist_coe_of_hasNebentypus hf γ.1 γ.2
      · rw [map_zero, smul_zero]
  have hdist : ∀ ψ ∈ T, ∀ ψ' ∈ T, ψ ≠ ψ' → ∃ γ : P, β ψ γ ≠ β ψ' γ := by
    intro ψ _ ψ' _ hne
    obtain ⟨γ, hγ, hγne⟩ := exists_gamma0_apply_ne hne
    exact ⟨⟨γ, hγ⟩, hγne⟩
  have hε := eq_zero_of_sum_eq_zero D β T v heig hdist hvsum ε (Finset.mem_insert_self _ _)
  rw [hv] at hε
  simp only [if_true, sub_eq_zero] at hε
  exact DFunLike.coe_injective hε

end NebentypusDirectSum

end

open scoped MatrixGroups in
theorem solution
    {N : ℕ} [NeZero N] {k : ℤ} [DecidableEq (DirichletCharacter ℂ N)] {ι : Type*} (s : Finset ι)
    (χ : ι → DirichletCharacter ℂ N) (g : ι → CuspForm (CongruenceSubgroup.Gamma1 N) k)
    (hg : ∀ i ∈ s, CuspForm.HasNebentypus (χ i) (g i))
    {ε : DirichletCharacter ℂ N} {f : CuspForm (CongruenceSubgroup.Gamma1 N) k}
    (hf : CuspForm.HasNebentypus ε f)
    (hsum : ∑ i ∈ s, g i = f) :
    ∑ i ∈ s.filter (fun i => χ i = ε), g i = f :=
  NebentypusDirectSum.main s χ g hg hf hsum

end S_CuspForm_HasNebentypus_sum_filter_eq_of_sum_eq
end P2MW
export P2MW.S_CuspForm_HasNebentypus_sum_filter_eq_of_sum_eq (solution)
