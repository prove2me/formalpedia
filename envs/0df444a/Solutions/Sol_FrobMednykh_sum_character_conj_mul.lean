-- Prove2me | solution 1 for FrobMednykh.sum_character_conj_mul
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T19:44:55.505179+00:00
-- url     : https://prove2.me/submissions/1c2e8ea0-ccf9-4f27-8fa5-d875b2c1ac6f

import Mathlib
import Definitions.Def_FrobMednykh_defs

open CategoryTheory
open FrobMednykh
theorem fm_schur {G : Type} [Group G] (V : FDRep ℂ G) [Simple V] (T : V →ₗ[ℂ] V)
    (hT : ∀ g, T ∘ₗ V.ρ g = V.ρ g ∘ₗ T) : ∃ c : ℂ, T = c • LinearMap.id := by
  let f : V ⟶ V := ⟨InducedCategory.homMk (ModuleCat.ofHom T), fun g => by
    ext1
    exact hT g⟩
  obtain ⟨c, hc⟩ := endomorphism_simple_eq_smul_id ℂ f
  refine ⟨c, ?_⟩
  have := congrArg (fun φ : V ⟶ V => φ.hom.hom.hom) hc
  exact this.symm.trans rfl

theorem fm_finrank_ne_zero {G : Type} [Group G] (V : FDRep ℂ G) [Simple V] :
    (Module.finrank ℂ V : ℂ) ≠ 0 := by
  intro h
  have h0 : Module.finrank ℂ V = 0 := by exact_mod_cast h
  have hs : Subsingleton V := Module.finrank_zero_iff.mp h0
  apply id_nonzero V
  apply Action.Hom.ext
  apply InducedCategory.hom_ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  exact Subsingleton.elim _ _

theorem fm_scalar {G : Type} [Group G] (V : FDRep ℂ G) [Simple V] (T : V →ₗ[ℂ] V)
    (hT : ∀ g, T ∘ₗ V.ρ g = V.ρ g ∘ₗ T) :
    T = (LinearMap.trace ℂ V T / Module.finrank ℂ V) • LinearMap.id := by
  obtain ⟨c, rfl⟩ := fm_schur V T hT
  rw [map_smul, LinearMap.trace_id, smul_eq_mul, mul_div_assoc, div_self (fm_finrank_ne_zero V),
    mul_one]

theorem fm_conj {G : Type} [Group G] [Fintype G] (V : FDRep ℂ G) [Simple V]
    (x y : G) :
    ∑ a : G, V.character (a * x * a⁻¹ * y) =
      (Fintype.card G : ℂ) / Module.finrank ℂ V * V.character x * V.character y := by
  set T : V →ₗ[ℂ] V := ∑ a : G, V.ρ (a * x * a⁻¹) with hTdef
  have hT : ∀ g, T ∘ₗ V.ρ g = V.ρ g ∘ₗ T := by
    intro g
    rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, hTdef, Finset.sum_mul, Finset.mul_sum]
    rw [← Equiv.sum_comp (Equiv.mulLeft g)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← map_mul, ← map_mul]
    congr 1
    simp only [Equiv.coe_mulLeft, mul_inv_rev]
    group
  have htr : LinearMap.trace ℂ V T = Fintype.card G * V.character x := by
    rw [hTdef, map_sum]
    change ∑ a : G, V.character (a * x * a⁻¹) = _
    simp only [FDRep.char_conj, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have key := fm_scalar V T hT
  have : ∑ a : G, V.character (a * x * a⁻¹ * y) = LinearMap.trace ℂ V (T ∘ₗ V.ρ y) := by
    rw [← Module.End.mul_eq_comp, hTdef, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← map_mul]; rfl
  rw [this, key, htr, LinearMap.smul_comp, LinearMap.id_comp, map_smul, smul_eq_mul]
  change _ * V.character y = _
  ring

open Classical in
theorem fm_conv {G : Type} [Group G] [Fintype G]
    (V W : FDRep ℂ G) [Simple V] [Simple W] (z : G) :
    ∑ x : G, V.character x * W.character (x⁻¹ * z) =
      if Nonempty (V ≅ W) then (Fintype.card G : ℂ) / Module.finrank ℂ V * V.character z
      else 0 := by
  set S : W →ₗ[ℂ] W := ∑ x : G, V.character x • W.ρ x⁻¹ with hSdef
  have hS : ∀ g, S ∘ₗ W.ρ g = W.ρ g ∘ₗ S := by
    intro g
    rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, hSdef, Finset.sum_mul, Finset.mul_sum]
    rw [← Equiv.sum_comp (MulAut.conj g).toEquiv]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [smul_mul_assoc, mul_smul_comm, MulEquiv.toEquiv_eq_coe,
      MulEquiv.coe_toEquiv, MulAut.conj_apply, FDRep.char_conj]
    rw [← map_mul, ← map_mul]
    congr 2
    group
  have hcard : (Nat.card G : ℂ) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]; exact_mod_cast Fintype.card_ne_zero
  have : Invertible (Nat.card G : ℂ) := invertibleOfNonzero hcard
  have horth := FDRep.char_orthonormal V W
  have htr : LinearMap.trace ℂ W S = ∑ x : G, V.character x * W.character x⁻¹ := by
    rw [hSdef, map_sum]
    simp only [map_smul, smul_eq_mul]; rfl
  have key := fm_scalar W S hS
  have : ∑ x : G, V.character x * W.character (x⁻¹ * z) = LinearMap.trace ℂ W (S ∘ₗ W.ρ z) := by
    rw [← Module.End.mul_eq_comp, hSdef, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [smul_mul_assoc, map_smul, smul_eq_mul, ← map_mul]; rfl
  rw [this, key, LinearMap.smul_comp, LinearMap.id_comp, map_smul, smul_eq_mul, htr]
  have hsum : ∑ x : G, V.character x * W.character x⁻¹ =
      (Nat.card G : ℂ) * (if Nonempty (V ≅ W) then 1 else 0) := by
    rw [← horth, ← mul_assoc, mul_inv_cancel₀ hcard, one_mul]
  rw [hsum, Nat.card_eq_fintype_card]
  split_ifs with h
  · obtain ⟨i⟩ := h
    rw [FDRep.char_iso i, LinearEquiv.finrank_eq (FDRep.isoToLinearEquiv i)]
    rw [mul_one]; rfl
  · simp

theorem solution {G : Type} [Group G] [Fintype G] (V : FDRep ℂ G) [Simple V]
    (x y : G) :
    ∑ a : G, V.character (a * x * a⁻¹ * y) =
      (Fintype.card G : ℂ) / Module.finrank ℂ V * V.character x * V.character y := by
  exact fm_conj V x y


