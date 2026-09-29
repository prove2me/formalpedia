-- Prove2me | solution 1 for BostonLenstraRibet.exists_embedding_of_irreducible_of_odd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/d1c3a943-d318-5b85-8a7c-a47ab1b4501c

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_BostonLenstraRibet_exists_embedding_of_irreducible_of_odd

set_option autoImplicit false

open Module

namespace BostonLenstraRibet

variable {k : Type*} [Field k] {G : Type*} [Group G]
  {V : Type*} [AddCommGroup V] [Module k V]
  {ρV : Representation k G V} {ρ : G → Matrix (Fin 2) (Fin 2) k}

theorem sq_eq
    (hCH : ∀ σ : G, ρV σ * ρV σ - (ρ σ).trace • ρV σ
      + (ρ σ).det • (1 : Module.End k V) = 0) (σ : G) :
    ρV σ * ρV σ = (ρ σ).trace • ρV σ - (ρ σ).det • (1 : Module.End k V) := by
  have h := hCH σ
  rw [sub_add_eq_add_sub, sub_eq_zero] at h
  rw [eq_sub_iff_add_eq]
  exact h

theorem det_smul_inv
    (hCH : ∀ σ : G, ρV σ * ρV σ - (ρ σ).trace • ρV σ
      + (ρ σ).det • (1 : Module.End k V) = 0) (σ : G) :
    (ρ σ).det • ρV (σ⁻¹) = (ρ σ).trace • (1 : Module.End k V) - ρV σ := by
  have hinv : ρV σ * ρV (σ⁻¹) = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have hL : (ρV σ * ρV σ) * ρV (σ⁻¹) = ρV σ := by
    rw [mul_assoc, hinv, mul_one]
  have hR : ((ρ σ).trace • ρV σ - (ρ σ).det • (1 : Module.End k V)) * ρV (σ⁻¹)
      = (ρ σ).trace • (1 : Module.End k V) - (ρ σ).det • ρV (σ⁻¹) := by
    rw [sub_mul, smul_mul_assoc, smul_mul_assoc, one_mul, hinv]
  have h : ρV σ = (ρ σ).trace • (1 : Module.End k V) - (ρ σ).det • ρV (σ⁻¹) := by
    rw [← hL, sq_eq hCH σ, hR]
  rw [eq_sub_iff_add_eq] at h ⊢
  rw [add_comm]
  exact h

theorem mul_sq_eq (hρ : ∀ σ τ : G, ρ (σ * τ) = ρ σ * ρ τ)
    (hCH : ∀ σ : G, ρV σ * ρV σ - (ρ σ).trace • ρV σ
      + (ρ σ).det • (1 : Module.End k V) = 0) (σ τ : G) :
    (ρV σ * ρV τ) * (ρV σ * ρV τ) = (ρ σ * ρ τ).trace • (ρV σ * ρV τ)
      - ((ρ σ).det * (ρ τ).det) • (1 : Module.End k V) := by
  have h := sq_eq hCH (σ * τ)
  rw [map_mul, hρ, Matrix.det_mul] at h
  exact h

theorem polarized (hρ : ∀ σ τ : G, ρ (σ * τ) = ρ σ * ρ τ)
    (hCH : ∀ σ : G, ρV σ * ρV σ - (ρ σ).trace • ρV σ
      + (ρ σ).det • (1 : Module.End k V) = 0) (σ τ : G) :
    ρV σ * ρV τ + ρV τ * ρV σ = (ρ σ).trace • ρV τ + (ρ τ).trace • ρV σ
      + ((ρ σ * ρ τ).trace - (ρ σ).trace * (ρ τ).trace) • (1 : Module.End k V) := by
  have hS'S : ρV (σ⁻¹) * ρV σ = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have hTT' : ρV τ * ρV (τ⁻¹) = 1 := by rw [← map_mul, mul_inv_cancel, map_one]

  have key : ρV (σ⁻¹) * ((ρV σ * ρV τ) * (ρV σ * ρV τ)) * ρV (τ⁻¹)
      = (ρ σ * ρ τ).trace • (ρV (σ⁻¹) * (ρV σ * ρV τ) * ρV (τ⁻¹))
        - ((ρ σ).det * (ρ τ).det) • (ρV (σ⁻¹) * ρV (τ⁻¹)) := by
    rw [mul_sq_eq hρ hCH σ τ]
    simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one]

  have lhs_eq : ρV (σ⁻¹) * ((ρV σ * ρV τ) * (ρV σ * ρV τ)) * ρV (τ⁻¹)
      = ρV τ * ρV σ := by
    calc ρV (σ⁻¹) * ((ρV σ * ρV τ) * (ρV σ * ρV τ)) * ρV (τ⁻¹)
        = (ρV (σ⁻¹) * ρV σ) * (ρV τ * ρV σ) * (ρV τ * ρV (τ⁻¹)) := by noncomm_ring
      _ = ρV τ * ρV σ := by rw [hS'S, hTT', one_mul, mul_one]

  have mid_eq : ρV (σ⁻¹) * (ρV σ * ρV τ) * ρV (τ⁻¹) = 1 := by
    calc ρV (σ⁻¹) * (ρV σ * ρV τ) * ρV (τ⁻¹)
        = (ρV (σ⁻¹) * ρV σ) * (ρV τ * ρV (τ⁻¹)) := by noncomm_ring
      _ = 1 := by rw [hS'S, hTT', one_mul]

  have inv_eq : ((ρ σ).det * (ρ τ).det) • (ρV (σ⁻¹) * ρV (τ⁻¹))
      = ((ρ σ).trace • (1 : Module.End k V) - ρV σ)
        * ((ρ τ).trace • (1 : Module.End k V) - ρV τ) := by
    rw [← det_smul_inv hCH σ, ← det_smul_inv hCH τ, smul_mul_assoc, mul_smul_comm,
      smul_smul]

  have expand : ((ρ σ).trace • (1 : Module.End k V) - ρV σ)
      * ((ρ τ).trace • (1 : Module.End k V) - ρV τ)
      = ((ρ σ).trace * (ρ τ).trace) • (1 : Module.End k V)
        - (ρ σ).trace • ρV τ - (ρ τ).trace • ρV σ + ρV σ * ρV τ := by
    have h1 : ((ρ σ).trace • (1 : Module.End k V)) * ((ρ τ).trace • (1 : Module.End k V))
        = ((ρ σ).trace * (ρ τ).trace) • (1 : Module.End k V) := by
      rw [smul_mul_assoc, mul_smul_comm, smul_smul, mul_one]
    have h2 : ((ρ σ).trace • (1 : Module.End k V)) * ρV τ = (ρ σ).trace • ρV τ := by
      rw [smul_mul_assoc, one_mul]
    have h3 : ρV σ * ((ρ τ).trace • (1 : Module.End k V)) = (ρ τ).trace • ρV σ := by
      rw [mul_smul_comm, mul_one]
    rw [sub_mul, mul_sub, mul_sub, h1, h2, h3]
    abel
  rw [lhs_eq, mid_eq, inv_eq, expand] at key

  rw [sub_smul, key]
  abel

omit [Group G] in
theorem trace_eq_entries (τ : G) : (ρ τ).trace = ρ τ 0 0 + ρ τ 1 1 :=
  Matrix.trace_fin_two _

omit [Group G] in
theorem trace_mul_diag {σ₀ : G} {α β : k} (hσ₀ : ρ σ₀ = !![α, 0; 0, β]) (τ : G) :
    (ρ σ₀ * ρ τ).trace = α * ρ τ 0 0 + β * ρ τ 1 1 := by
  rw [hσ₀, Matrix.trace_fin_two]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem entry_mul_00 (hρ : ∀ σ τ : G, ρ (σ * τ) = ρ σ * ρ τ) (τ υ : G) :
    ρ (τ * υ) 0 0 = ρ τ 0 0 * ρ υ 0 0 + ρ τ 0 1 * ρ υ 1 0 := by
  rw [hρ, Matrix.mul_apply, Fin.sum_univ_two]

theorem entry_mul_11 (hρ : ∀ σ τ : G, ρ (σ * τ) = ρ σ * ρ τ) (τ υ : G) :
    ρ (τ * υ) 1 1 = ρ τ 1 0 * ρ υ 0 1 + ρ τ 1 1 * ρ υ 1 1 := by
  rw [hρ, Matrix.mul_apply, Fin.sum_univ_two]

theorem exists_embedding
    (hρ : ∀ σ τ : G, ρ (σ * τ) = ρ σ * ρ τ)
    (hCH : ∀ σ : G, ρV σ * ρV σ - (ρ σ).trace • ρV σ
      + (ρ σ).det • (1 : Module.End k V) = 0)
    {σ₀ : G} {α β : k} (hαβ : α ≠ β) (hσ₀ : ρ σ₀ = !![α, 0; 0, β])
    {τ₀ : G} (hτ₀ : ρ τ₀ 0 1 ≠ 0) {υ₀ : G} (hυ₀ : ρ υ₀ 1 0 ≠ 0)
    (hV : ∃ v : V, v ≠ 0) :
    ∃ φ : (Fin 2 → k) →ₗ[k] V, Function.Injective φ ∧
      ∀ (σ : G) (v : Fin 2 → k), φ ((ρ σ).mulVec v) = ρV σ (φ v) := by
  classical
  have hαβ' : α - β ≠ 0 := sub_ne_zero.mpr hαβ

  have htr₀ : (ρ σ₀).trace = α + β := by
    rw [hσ₀, Matrix.trace_fin_two]
    simp
  have hdet₀ : (ρ σ₀).det = α * β := by
    rw [hσ₀, Matrix.det_fin_two]
    simp

  set e : Module.End k V := (α - β)⁻¹ • (ρV σ₀ - β • 1) with he_def
  set f : Module.End k V := 1 - e with hf_def
  clear_value f e

  have hfactor : (ρV σ₀ - α • 1) * (ρV σ₀ - β • 1) = 0 := by
    have expand : (ρV σ₀ - α • 1) * (ρV σ₀ - β • 1)
        = ρV σ₀ * ρV σ₀ - (α + β) • ρV σ₀ + (α * β) • (1 : Module.End k V) := by
      have h1 : (α • (1 : Module.End k V)) * (β • (1 : Module.End k V))
          = (α * β) • (1 : Module.End k V) := by
        rw [smul_mul_assoc, mul_smul_comm, smul_smul, mul_one]
      have h2 : ρV σ₀ * (β • (1 : Module.End k V)) = β • ρV σ₀ := by
        rw [mul_smul_comm, mul_one]
      have h3 : (α • (1 : Module.End k V)) * ρV σ₀ = α • ρV σ₀ := by
        rw [smul_mul_assoc, one_mul]
      rw [sub_mul, mul_sub, mul_sub, h1, h2, h3, add_smul]
      abel
    rw [expand, ← htr₀, ← hdet₀]
    exact hCH σ₀

  have he : e * e = e := by
    have hX : (ρV σ₀ - β • 1) * (ρV σ₀ - β • 1) = (α - β) • (ρV σ₀ - β • 1) := by
      have h2 : (ρV σ₀ - β • 1) * (ρV σ₀ - β • 1)
          = (ρV σ₀ - α • 1) * (ρV σ₀ - β • 1) + (α - β) • (ρV σ₀ - β • 1) := by
        simp only [sub_mul, smul_mul_assoc, one_mul, sub_smul]
        abel
      rw [h2, hfactor, zero_add]
    rw [he_def, smul_mul_assoc, mul_smul_comm, hX, smul_smul, smul_smul]
    congr 1
    rw [mul_assoc, inv_mul_cancel₀ hαβ', mul_one]

  have hdecomp : ρV σ₀ = α • e + β • f := by
    have h1 : α • e + β • f = (α - β) • e + β • (1 : Module.End k V) := by
      rw [hf_def, smul_sub, sub_smul]
      abel
    rw [h1, he_def, smul_smul, mul_inv_cancel₀ hαβ', one_smul]
    abel

  have hf : f * f = f := by
    rw [hf_def]
    simp only [sub_mul, mul_sub, one_mul, mul_one, he]
    abel
  have hef : e * f = 0 := by
    rw [hf_def, mul_sub, mul_one, he, sub_self]
  have hfe : f * e = 0 := by
    rw [hf_def, sub_mul, one_mul, he, sub_self]
  have hefone : e + f = 1 := by
    rw [hf_def]
    abel

  have hSe : ρV σ₀ * e = α • e := by
    rw [hdecomp, add_mul, smul_mul_assoc, smul_mul_assoc, he, hfe, smul_zero, add_zero]
  have heS : e * ρV σ₀ = α • e := by
    rw [hdecomp, mul_add, mul_smul_comm, mul_smul_comm, he, hef, smul_zero, add_zero]
  have hSf : ρV σ₀ * f = β • f := by
    rw [hdecomp, add_mul, smul_mul_assoc, smul_mul_assoc, hf, hef, smul_zero, zero_add]
  have hfS : f * ρV σ₀ = β • f := by
    rw [hdecomp, mul_add, mul_smul_comm, mul_smul_comm, hf, hfe, smul_zero, zero_add]

  have sandwich_ee : ∀ τ : G, e * ρV τ * e = (ρ τ 0 0) • e := by
    intro τ
    have h1 : e * (ρV σ₀ * ρV τ + ρV τ * ρV σ₀) * e
        = e * ((ρ σ₀).trace • ρV τ + (ρ τ).trace • ρV σ₀
          + ((ρ σ₀ * ρ τ).trace - (ρ σ₀).trace * (ρ τ).trace)
            • (1 : Module.End k V)) * e := by
      rw [polarized hρ hCH σ₀ τ]
    have hL : e * (ρV σ₀ * ρV τ + ρV τ * ρV σ₀) * e
        = α • (e * ρV τ * e) + α • (e * ρV τ * e) := by
      have hL1 : e * (ρV σ₀ * ρV τ) * e = α • (e * ρV τ * e) := by
        rw [← mul_assoc, heS, smul_mul_assoc, smul_mul_assoc]
      have hL2 : e * (ρV τ * ρV σ₀) * e = α • (e * ρV τ * e) := by
        rw [mul_assoc, mul_assoc, hSe, mul_smul_comm, mul_smul_comm, ← mul_assoc]
      rw [mul_add, add_mul, hL1, hL2]
    have hR : e * ((ρ σ₀).trace • ρV τ + (ρ τ).trace • ρV σ₀
          + ((ρ σ₀ * ρ τ).trace - (ρ σ₀).trace * (ρ τ).trace)
            • (1 : Module.End k V)) * e
        = (ρ σ₀).trace • (e * ρV τ * e)
          + ((ρ τ).trace * α
            + ((ρ σ₀ * ρ τ).trace - (ρ σ₀).trace * (ρ τ).trace)) • e := by
      have hR1 : e * ((ρ σ₀).trace • ρV τ) * e = (ρ σ₀).trace • (e * ρV τ * e) := by
        rw [mul_smul_comm, smul_mul_assoc]
      have hR2 : e * ((ρ τ).trace • ρV σ₀) * e = ((ρ τ).trace * α) • e := by
        rw [mul_smul_comm, smul_mul_assoc, mul_assoc, hSe, mul_smul_comm, he, smul_smul]
      have hR3 : e * (((ρ σ₀ * ρ τ).trace - (ρ σ₀).trace * (ρ τ).trace)
            • (1 : Module.End k V)) * e
          = ((ρ σ₀ * ρ τ).trace - (ρ σ₀).trace * (ρ τ).trace) • e := by
        rw [mul_smul_comm, mul_one, smul_mul_assoc, he]
      rw [mul_add, add_mul, mul_add, add_mul, hR1, hR2, hR3, add_smul]
      abel
    rw [hL, hR] at h1

    have h2 : (α + α - (ρ σ₀).trace) • (e * ρV τ * e)
        = ((ρ τ).trace * α
          + ((ρ σ₀ * ρ τ).trace - (ρ σ₀).trace * (ρ τ).trace)) • e := by
      rw [sub_smul, add_smul, h1]
      abel
    have hscalar : (ρ τ).trace * α + ((ρ σ₀ * ρ τ).trace - (ρ σ₀).trace * (ρ τ).trace)
        = (α - β) * ρ τ 0 0 := by
      rw [trace_mul_diag hσ₀ τ, htr₀, trace_eq_entries]
      ring
    rw [hscalar, htr₀, show α + α - (α + β) = α - β from by ring] at h2

    have h4 := congrArg (fun X : Module.End k V => (α - β)⁻¹ • X) h2
    simp only [smul_smul] at h4
    rw [inv_mul_cancel₀ hαβ', one_smul, ← mul_assoc, inv_mul_cancel₀ hαβ', one_mul] at h4
    exact h4

  have sandwich_ff : ∀ τ : G, f * ρV τ * f = (ρ τ 1 1) • f := by
    intro τ
    have h1 : f * (ρV σ₀ * ρV τ + ρV τ * ρV σ₀) * f
        = f * ((ρ σ₀).trace • ρV τ + (ρ τ).trace • ρV σ₀
          + ((ρ σ₀ * ρ τ).trace - (ρ σ₀).trace * (ρ τ).trace)
            • (1 : Module.End k V)) * f := by
      rw [polarized hρ hCH σ₀ τ]
    have hL : f * (ρV σ₀ * ρV τ + ρV τ * ρV σ₀) * f
        = β • (f * ρV τ * f) + β • (f * ρV τ * f) := by
      have hL1 : f * (ρV σ₀ * ρV τ) * f = β • (f * ρV τ * f) := by
        rw [← mul_assoc, hfS, smul_mul_assoc, smul_mul_assoc]
      have hL2 : f * (ρV τ * ρV σ₀) * f = β • (f * ρV τ * f) := by
        rw [mul_assoc, mul_assoc, hSf, mul_smul_comm, mul_smul_comm, ← mul_assoc]
      rw [mul_add, add_mul, hL1, hL2]
    have hR : f * ((ρ σ₀).trace • ρV τ + (ρ τ).trace • ρV σ₀
          + ((ρ σ₀ * ρ τ).trace - (ρ σ₀).trace * (ρ τ).trace)
            • (1 : Module.End k V)) * f
        = (ρ σ₀).trace • (f * ρV τ * f)
          + ((ρ τ).trace * β
            + ((ρ σ₀ * ρ τ).trace - (ρ σ₀).trace * (ρ τ).trace)) • f := by
      have hR1 : f * ((ρ σ₀).trace • ρV τ) * f = (ρ σ₀).trace • (f * ρV τ * f) := by
        rw [mul_smul_comm, smul_mul_assoc]
      have hR2 : f * ((ρ τ).trace • ρV σ₀) * f = ((ρ τ).trace * β) • f := by
        rw [mul_smul_comm, smul_mul_assoc, mul_assoc, hSf, mul_smul_comm, hf, smul_smul]
      have hR3 : f * (((ρ σ₀ * ρ τ).trace - (ρ σ₀).trace * (ρ τ).trace)
            • (1 : Module.End k V)) * f
          = ((ρ σ₀ * ρ τ).trace - (ρ σ₀).trace * (ρ τ).trace) • f := by
        rw [mul_smul_comm, mul_one, smul_mul_assoc, hf]
      rw [mul_add, add_mul, mul_add, add_mul, hR1, hR2, hR3, add_smul]
      abel
    rw [hL, hR] at h1
    have h2 : (β + β - (ρ σ₀).trace) • (f * ρV τ * f)
        = ((ρ τ).trace * β
          + ((ρ σ₀ * ρ τ).trace - (ρ σ₀).trace * (ρ τ).trace)) • f := by
      rw [sub_smul, add_smul, h1]
      abel
    have hscalar : (ρ τ).trace * β + ((ρ σ₀ * ρ τ).trace - (ρ σ₀).trace * (ρ τ).trace)
        = (β - α) * ρ τ 1 1 := by
      rw [trace_mul_diag hσ₀ τ, htr₀, trace_eq_entries]
      ring
    rw [hscalar, htr₀, show β + β - (α + β) = β - α from by ring] at h2
    have hβα' : β - α ≠ 0 := sub_ne_zero.mpr (Ne.symm hαβ)
    have h4 := congrArg (fun X : Module.End k V => (β - α)⁻¹ • X) h2
    simp only [smul_smul] at h4
    rw [inv_mul_cancel₀ hβα', one_smul, ← mul_assoc, inv_mul_cancel₀ hβα', one_mul] at h4
    exact h4

  have sandwich_efe : ∀ τ υ : G,
      (e * ρV τ * f) * (f * ρV υ * e) = (ρ τ 0 1 * ρ υ 1 0) • e := by
    intro τ υ
    have h1 : (e * ρV τ * f) * (f * ρV υ * e)
        = e * (ρV τ * ρV υ) * e - (e * ρV τ * e) * (e * ρV υ * e) := by
      have hcollapse : (e * ρV τ * f) * (f * ρV υ * e)
          = e * ρV τ * (f * (ρV υ * e)) := by
        rw [show (e * ρV τ * f) * (f * ρV υ * e)
            = e * ρV τ * ((f * f) * (ρV υ * e)) from by noncomm_ring, hf]
      have h2 : e * ρV τ * (e * (ρV υ * e)) = (e * ρV τ * e) * (e * ρV υ * e) := by
        rw [show (e * ρV τ * e) * (e * ρV υ * e)
            = e * ρV τ * ((e * e) * (ρV υ * e)) from by noncomm_ring, he]
      rw [hcollapse, hf_def, sub_mul, one_mul, mul_sub, h2]
      noncomm_ring
    rw [h1]
    have h3 : e * (ρV τ * ρV υ) * e = (ρ (τ * υ) 0 0) • e := by
      rw [← map_mul]
      exact sandwich_ee (τ * υ)
    rw [h3, sandwich_ee τ, sandwich_ee υ, smul_mul_assoc, mul_smul_comm, he, smul_smul,
      entry_mul_00 hρ τ υ, ← sub_smul]
    congr 1
    ring

  have sandwich_fef : ∀ υ τ : G,
      (f * ρV υ * e) * (e * ρV τ * f) = (ρ υ 1 0 * ρ τ 0 1) • f := by
    intro υ τ
    have h1 : (f * ρV υ * e) * (e * ρV τ * f)
        = f * (ρV υ * ρV τ) * f - (f * ρV υ * f) * (f * ρV τ * f) := by
      have hcollapse : (f * ρV υ * e) * (e * ρV τ * f)
          = f * ρV υ * (e * (ρV τ * f)) := by
        rw [show (f * ρV υ * e) * (e * ρV τ * f)
            = f * ρV υ * ((e * e) * (ρV τ * f)) from by noncomm_ring, he]
      have h2 : f * ρV υ * (f * (ρV τ * f)) = (f * ρV υ * f) * (f * ρV τ * f) := by
        rw [show (f * ρV υ * f) * (f * ρV τ * f)
            = f * ρV υ * ((f * f) * (ρV τ * f)) from by noncomm_ring, hf]
      have hesub : (e : Module.End k V) = 1 - f := by
        rw [hf_def]
        abel
      rw [hcollapse, hesub, sub_mul, one_mul, mul_sub, h2]
      noncomm_ring
    rw [h1]
    have h3 : f * (ρV υ * ρV τ) * f = (ρ (υ * τ) 1 1) • f := by
      rw [← map_mul]
      exact sandwich_ff (υ * τ)
    rw [h3, sandwich_ff υ, sandwich_ff τ, smul_mul_assoc, mul_smul_comm, hf, smul_smul,
      entry_mul_11 hρ υ τ, ← sub_smul]
    congr 1
    ring

  have he_ne : e ≠ 0 := by
    intro he0
    obtain ⟨v, hv⟩ := hV
    have h1 := sandwich_fef υ₀ τ₀
    rw [he0, mul_zero, zero_mul] at h1

    have h2 := congrArg (fun ψ : Module.End k V => ψ v) h1.symm
    simp only [LinearMap.smul_apply, LinearMap.zero_apply] at h2
    rw [hf_def, he0, sub_zero] at h2
    simp only [Module.End.one_apply] at h2
    rcases smul_eq_zero.mp h2 with h | h
    · exact (mul_ne_zero hυ₀ hτ₀) h
    · exact hv h

  obtain ⟨u, hu⟩ : ∃ u : V, e u ≠ 0 := by
    by_contra hc
    exact he_ne (LinearMap.ext fun u => by simpa using not_exists.mp hc u)
  set m₁ : V := e u with hm₁_def
  have hm₁_ne : m₁ ≠ 0 := hu
  clear_value m₁
  have hem₁ : e m₁ = m₁ := by
    rw [hm₁_def, ← Module.End.mul_apply, he]
  set m₂ : V := (ρ υ₀ 1 0)⁻¹ • ((f * ρV υ₀ * e) m₁) with hm₂_def
  clear_value m₂
  have hffe : f * (f * ρV υ₀ * e) = f * ρV υ₀ * e := by
    rw [show f * (f * ρV υ₀ * e) = (f * f) * ρV υ₀ * e from by noncomm_ring, hf]
  have heffe : e * (f * ρV υ₀ * e) = 0 := by
    rw [show e * (f * ρV υ₀ * e) = (e * f) * ρV υ₀ * e from by noncomm_ring, hef,
      zero_mul, zero_mul]
  have hfm₂ : f m₂ = m₂ := by
    rw [hm₂_def, map_smul, ← Module.End.mul_apply, hffe]
  have hem₂ : e m₂ = 0 := by
    rw [hm₂_def, map_smul, ← Module.End.mul_apply, heffe, LinearMap.zero_apply, smul_zero]

  have key_ef : ∀ τ : G, (e * ρV τ * f) m₂ = (ρ τ 0 1) • m₁ := by
    intro τ
    rw [hm₂_def, map_smul, ← Module.End.mul_apply, sandwich_efe τ υ₀,
      LinearMap.smul_apply, hem₁, smul_smul]
    congr 1
    rw [mul_comm (ρ τ 0 1) (ρ υ₀ 1 0), ← mul_assoc, inv_mul_cancel₀ hυ₀, one_mul]

  have key_fe : ∀ τ : G, (f * ρV τ * e) m₁ = (ρ τ 1 0) • m₂ := by
    intro τ

    have h1 : (e * ρV τ₀ * f) ((f * ρV τ * e) m₁) = (ρ τ₀ 0 1 * ρ τ 1 0) • m₁ := by
      rw [← Module.End.mul_apply, sandwich_efe τ₀ τ, LinearMap.smul_apply, hem₁]
    have h2 : (e * ρV τ₀ * f) ((ρ τ 1 0) • m₂) = (ρ τ 1 0) • ((ρ τ₀ 0 1) • m₁) := by
      rw [map_smul, key_ef τ₀]
    have hkill : (e * ρV τ₀ * f) ((f * ρV τ * e) m₁ - (ρ τ 1 0) • m₂) = 0 := by
      rw [map_sub, h1, h2, smul_smul, mul_comm (ρ τ 1 0) (ρ τ₀ 0 1), sub_self]
    have hffτe : f * (f * ρV τ * e) = f * ρV τ * e := by
      rw [show f * (f * ρV τ * e) = (f * f) * ρV τ * e from by noncomm_ring, hf]
    have hfw : f ((f * ρV τ * e) m₁ - (ρ τ 1 0) • m₂)
        = (f * ρV τ * e) m₁ - (ρ τ 1 0) • m₂ := by
      rw [map_sub, map_smul, hfm₂, ← Module.End.mul_apply, hffτe]
    have hcomp : ((f * ρV υ₀ * e) * (e * ρV τ₀ * f))
        ((f * ρV τ * e) m₁ - (ρ τ 1 0) • m₂) = 0 := by
      rw [Module.End.mul_apply, hkill, map_zero]
    rw [sandwich_fef υ₀ τ₀, LinearMap.smul_apply, hfw] at hcomp
    rcases smul_eq_zero.mp hcomp with h | h
    · exact absurd h (mul_ne_zero hυ₀ hτ₀)
    · exact sub_eq_zero.mp h

  have act_m₁ : ∀ σ : G, ρV σ m₁ = (ρ σ 0 0) • m₁ + (ρ σ 1 0) • m₂ := by
    intro σ
    have h1 : ρV σ m₁ = ((e + f) * ρV σ * e) u := by
      rw [hefone, one_mul, Module.End.mul_apply, ← hm₁_def]
    have h2 : (e * ρV σ * e) u = (ρ σ 0 0) • m₁ := by
      rw [sandwich_ee σ, LinearMap.smul_apply, ← hm₁_def]
    have h3 : (f * ρV σ * e) u = (ρ σ 1 0) • m₂ := by
      have hee : (f * ρV σ * e) * e = f * ρV σ * e := by
        rw [mul_assoc, he]
      have h4 : (f * ρV σ * e) u = (f * ρV σ * e) m₁ := by
        rw [hm₁_def, ← Module.End.mul_apply, hee]
      rw [h4, key_fe σ]
    rw [h1, add_mul, add_mul, LinearMap.add_apply, h2, h3]
  have act_m₂ : ∀ σ : G, ρV σ m₂ = (ρ σ 0 1) • m₁ + (ρ σ 1 1) • m₂ := by
    intro σ
    have h1 : ρV σ m₂ = ((e + f) * ρV σ * f) m₂ := by
      rw [hefone, one_mul, Module.End.mul_apply, hfm₂]
    have h2 : (e * ρV σ * f) m₂ = (ρ σ 0 1) • m₁ := key_ef σ
    have h3 : (f * ρV σ * f) m₂ = (ρ σ 1 1) • m₂ := by
      rw [sandwich_ff σ, LinearMap.smul_apply, hfm₂]
    rw [h1, add_mul, add_mul, LinearMap.add_apply, h2, h3]

  refine ⟨(LinearMap.proj 0).smulRight m₁ + (LinearMap.proj 1).smulRight m₂, ?_, ?_⟩
  ·
    refine (injective_iff_map_eq_zero _).mpr fun v hv0 => ?_
    simp only [LinearMap.add_apply, LinearMap.smulRight_apply, LinearMap.proj_apply] at hv0

    have h1 : v 0 • m₁ = 0 := by
      have h2 := congrArg (fun x : V => e x) hv0
      simp only [map_add, map_smul, map_zero] at h2
      rw [hem₁, hem₂, smul_zero, add_zero] at h2
      exact h2
    have hv00 : v 0 = 0 := by
      rcases smul_eq_zero.mp h1 with h | h
      · exact h
      · exact absurd h hm₁_ne
    rw [hv00, zero_smul, zero_add] at hv0

    have h3 := congrArg (fun x : V => (e * ρV τ₀ * f) x) hv0
    simp only [map_smul, map_zero] at h3
    rw [key_ef τ₀, smul_smul] at h3
    have hv01 : v 1 = 0 := by
      rcases smul_eq_zero.mp h3 with h | h
      · rcases mul_eq_zero.mp h with h' | h'
        · exact h'
        · exact absurd h' hτ₀
      · exact absurd h hm₁_ne
    funext i
    fin_cases i
    · exact hv00
    · exact hv01
  ·
    intro σ v
    simp only [LinearMap.add_apply, LinearMap.smulRight_apply, LinearMap.proj_apply]
    rw [map_add, map_smul, map_smul, act_m₁ σ, act_m₂ σ]
    have hmv : ∀ i, (ρ σ).mulVec v i = ρ σ i 0 * v 0 + ρ σ i 1 * v 1 := by
      intro i
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [hmv 0, hmv 1]
    simp only [smul_add, smul_smul, add_smul]
    module

end BostonLenstraRibet

set_option autoImplicit false

open Module Matrix

namespace BostonLenstraRibet

variable {k : Type*} [Field k] {G : Type*} [Group G]

section Conjugation

variable {P Q : Matrix (Fin 2) (Fin 2) k}

theorem trace_conj (hPQ : P * Q = 1) (A : Matrix (Fin 2) (Fin 2) k) :
    (Q * A * P).trace = A.trace := by
  rw [Matrix.trace_mul_cycle, hPQ, one_mul]

theorem det_conj (hPQ : P * Q = 1) (A : Matrix (Fin 2) (Fin 2) k) :
    (Q * A * P).det = A.det := by
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, ← Matrix.det_mul, hPQ,
    Matrix.det_one, one_mul]

theorem conj_mul {ρ : G → Matrix (Fin 2) (Fin 2) k}
    (hρ : ∀ σ τ : G, ρ (σ * τ) = ρ σ * ρ τ) (hPQ : P * Q = 1) (σ τ : G) :
    Q * ρ (σ * τ) * P = (Q * ρ σ * P) * (Q * ρ τ * P) := by
  rw [hρ]
  calc Q * (ρ σ * ρ τ) * P = Q * ρ σ * (P * Q) * ρ τ * P := by rw [hPQ]; noncomm_ring
    _ = (Q * ρ σ * P) * (Q * ρ τ * P) := by noncomm_ring

end Conjugation

section Involution

variable {A : Matrix (Fin 2) (Fin 2) k}

theorem trace_eq_zero_of_invol (hA2 : A * A = 1) (hdet : A.det = -1) :
    A 0 0 + A 1 1 = 0 := by
  have h00 : A 0 0 * A 0 0 + A 0 1 * A 1 0 = 1 := by
    have := congrFun (congrFun hA2 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using this
  have h01 : A 0 0 * A 0 1 + A 0 1 * A 1 1 = 0 := by
    have := congrFun (congrFun hA2 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using this
  have hd : A 0 0 * A 1 1 - A 0 1 * A 1 0 = -1 := by
    rw [← Matrix.det_fin_two]; exact hdet
  by_contra ht

  have h01' : A 0 1 = 0 := by
    rcases mul_eq_zero.mp (show A 0 1 * (A 0 0 + A 1 1) = 0 by linear_combination h01) with
      h | h
    · exact h
    · exact absurd h ht

  have ha : A 0 0 * A 0 0 = 1 := by linear_combination h00 - A 1 0 * h01'
  have had : A 0 0 * A 1 1 = -1 := by linear_combination hd + A 1 0 * h01'
  exact ht (by linear_combination A 0 0 * had - A 1 1 * ha)

theorem exists_conj_diag_of_invol (hA2 : A * A = 1) (hdet : A.det = -1) (h2 : (2 : k) ≠ 0) :
    ∃ P Q : Matrix (Fin 2) (Fin 2) k,
      Q * P = 1 ∧ P * Q = 1 ∧ Q * A * P = !![(1 : k), 0; 0, -1] := by
  classical

  have hA_ne_neg : A + 1 ≠ 0 := by
    intro h
    have hA : A = -1 := eq_neg_of_add_eq_zero_left h
    rw [hA, Matrix.det_neg, Matrix.det_one, Fintype.card_fin,
      show ((-1 : k)) ^ 2 * 1 = 1 by ring] at hdet
    exact h2 (by linear_combination hdet)
  have hA_ne_one : A - 1 ≠ 0 := by
    intro h
    have hA : A = 1 := sub_eq_zero.mp h
    rw [hA, Matrix.det_one] at hdet
    exact h2 (by linear_combination hdet)

  have hplus : A * (A + 1) = A + 1 := by
    rw [mul_add, hA2, mul_one]; abel
  have hminus : A * (A - 1) = -(A - 1) := by
    rw [mul_sub, hA2, mul_one]; abel

  obtain ⟨wp, hwp⟩ : ∃ w : Fin 2 → k, (A + 1).mulVec w ≠ 0 := by
    by_contra hc
    push Not at hc
    refine hA_ne_neg (Matrix.ext fun i j => ?_)
    have := congrFun (hc (Pi.single j 1)) i
    simpa [Matrix.mulVec_single_one] using this
  obtain ⟨wm, hwm⟩ : ∃ w : Fin 2 → k, (A - 1).mulVec w ≠ 0 := by
    by_contra hc
    push Not at hc
    refine hA_ne_one (Matrix.ext fun i j => ?_)
    have := congrFun (hc (Pi.single j 1)) i
    simpa [Matrix.mulVec_single_one] using this

  set vp : Fin 2 → k := (A + 1).mulVec wp with hvp_def
  set vm : Fin 2 → k := (A - 1).mulVec wm with hvm_def
  have hvp : vp ≠ 0 := hwp
  have hvm : vm ≠ 0 := hwm

  have hAvp : A.mulVec vp = vp := by
    rw [hvp_def, Matrix.mulVec_mulVec, hplus]
  have hAvm : A.mulVec vm = -vm := by
    rw [hvm_def, Matrix.mulVec_mulVec, hminus, Matrix.neg_mulVec]
  clear_value vp vm

  set P : Matrix (Fin 2) (Fin 2) k := !![vp 0, vm 0; vp 1, vm 1] with hP_def
  have hPcol₀ : ∀ i, P i 0 = vp i := by
    intro i; fin_cases i <;> simp [hP_def]
  have hPcol₁ : ∀ i, P i 1 = vm i := by
    intro i; fin_cases i <;> simp [hP_def]

  have hPmulVec : ∀ u : Fin 2 → k, P.mulVec u = u 0 • vp + u 1 • vm := by
    intro u
    funext i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, hPcol₀ i, hPcol₁ i]
    ring

  have hdetP : P.det ≠ 0 := by
    intro h0
    obtain ⟨u, hu, hPu⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    rw [hPmulVec u] at hPu

    have hPu' : u 0 • vp - u 1 • vm = 0 := by
      have h := congrArg A.mulVec hPu
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hAvp, hAvm,
        Matrix.mulVec_zero, smul_neg, ← sub_eq_add_neg] at h
      exact h
    have hu0v : u 0 • vp = 0 := by
      have h2v : (2 : k) • (u 0 • vp) = 0 := by
        have hsum : (u 0 • vp + u 1 • vm) + (u 0 • vp - u 1 • vm) = 0 := by
          rw [hPu, hPu', add_zero]
        rw [two_smul]
        calc u 0 • vp + u 0 • vp
            = (u 0 • vp + u 1 • vm) + (u 0 • vp - u 1 • vm) := by abel
          _ = 0 := hsum
      rcases smul_eq_zero.mp h2v with h | h
      · exact absurd h h2
      · exact h
    have hu1v : u 1 • vm = 0 := by
      have hrw : u 1 • vm = (u 0 • vp + u 1 • vm) - (u 0 • vp) := by abel
      rw [hrw, hPu, hu0v, sub_zero]
    apply hu
    have hu0 : u 0 = 0 := by
      rcases smul_eq_zero.mp hu0v with h | h
      · exact h
      · exact absurd h hvp
    have hu1 : u 1 = 0 := by
      rcases smul_eq_zero.mp hu1v with h | h
      · exact h
      · exact absurd h hvm
    funext i
    fin_cases i
    · exact hu0
    · exact hu1

  have hAvpc : ∀ i, A i 0 * vp 0 + A i 1 * vp 1 = vp i := by
    intro i
    have := congrFun hAvp i
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have hAvmc : ∀ i, A i 0 * vm 0 + A i 1 * vm 1 = -vm i := by
    intro i
    have := congrFun hAvm i
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this

  have hAP : A * P = P * !![(1 : k), 0; 0, -1] := by
    refine Matrix.ext fun i j => ?_
    have hL : (A * P) i j = A i 0 * P 0 j + A i 1 * P 1 j := by
      rw [Matrix.mul_apply, Fin.sum_univ_two]
    have hR : (P * !![(1 : k), 0; 0, -1]) i j
        = P i 0 * !![(1 : k), 0; 0, -1] 0 j + P i 1 * !![(1 : k), 0; 0, -1] 1 j := by
      rw [Matrix.mul_apply, Fin.sum_univ_two]
    rw [hL, hR]
    fin_cases j
    · simpa [hPcol₀] using hAvpc i
    · simpa [hPcol₁] using hAvmc i

  have hdetP' : IsUnit P.det := isUnit_iff_ne_zero.mpr hdetP
  refine ⟨P, P⁻¹, Matrix.nonsing_inv_mul P hdetP', Matrix.mul_nonsing_inv P hdetP', ?_⟩
  calc P⁻¹ * A * P = P⁻¹ * (A * P) := by rw [mul_assoc]
    _ = P⁻¹ * (P * !![(1 : k), 0; 0, -1]) := by rw [hAP]
    _ = (P⁻¹ * P) * !![(1 : k), 0; 0, -1] := by rw [← mul_assoc]
    _ = !![(1 : k), 0; 0, -1] := by rw [Matrix.nonsing_inv_mul P hdetP', one_mul]

end Involution

section Corners

variable {ρ : G → Matrix (Fin 2) (Fin 2) k}

omit [Group G] in

theorem exists_entry_one_zero_ne_zero
    (hirr : ∀ W : Submodule k (Fin 2 → k),
      (∀ g, ∀ v ∈ W, (ρ g).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) :
    ∃ υ₀ : G, ρ υ₀ 1 0 ≠ 0 := by
  by_contra hc
  push Not at hc
  have hstab : ∀ g, ∀ v ∈ Submodule.span k {(![1, 0] : Fin 2 → k)},
      (ρ g).mulVec v ∈ Submodule.span k {(![1, 0] : Fin 2 → k)} := by
    intro g v hv
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hv
    refine Submodule.mem_span_singleton.mpr ⟨a * ρ g 0 0, ?_⟩
    have hv0 : v 0 = a := by rw [← ha]; simp
    have hv1 : v 1 = 0 := by rw [← ha]; simp
    funext i
    fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hv0, hv1, hc g, mul_comm]
  rcases hirr _ hstab with h | h
  ·
    have h0 : (![1, 0] : Fin 2 → k) = 0 := Submodule.span_singleton_eq_bot.mp h
    have h1 := congrFun h0 0
    simp at h1
  ·
    have hmem : (![0, 1] : Fin 2 → k) ∈ Submodule.span k {(![1, 0] : Fin 2 → k)} := by
      rw [h]; trivial
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
    have h1 := congrFun ha 1
    simp at h1

omit [Group G] in

theorem exists_entry_zero_one_ne_zero
    (hirr : ∀ W : Submodule k (Fin 2 → k),
      (∀ g, ∀ v ∈ W, (ρ g).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) :
    ∃ τ₀ : G, ρ τ₀ 0 1 ≠ 0 := by
  by_contra hc
  push Not at hc
  have hstab : ∀ g, ∀ v ∈ Submodule.span k {(![0, 1] : Fin 2 → k)},
      (ρ g).mulVec v ∈ Submodule.span k {(![0, 1] : Fin 2 → k)} := by
    intro g v hv
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hv
    refine Submodule.mem_span_singleton.mpr ⟨a * ρ g 1 1, ?_⟩
    have hv0 : v 0 = 0 := by rw [← ha]; simp
    have hv1 : v 1 = a := by rw [← ha]; simp
    funext i
    fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hv0, hv1, hc g, mul_comm]
  rcases hirr _ hstab with h | h
  · have h0 : (![0, 1] : Fin 2 → k) = 0 := Submodule.span_singleton_eq_bot.mp h
    have h1 := congrFun h0 1
    simp at h1
  · have hmem : (![1, 0] : Fin 2 → k) ∈ Submodule.span k {(![0, 1] : Fin 2 → k)} := by
      rw [h]; trivial
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
    have h1 := congrFun ha 0
    simp at h1

end Corners

section Transport

variable {ρ : G → Matrix (Fin 2) (Fin 2) k} {P Q : Matrix (Fin 2) (Fin 2) k}

omit [Group G] in

theorem irreducible_conj
    (hirr : ∀ W : Submodule k (Fin 2 → k),
      (∀ g, ∀ v ∈ W, (ρ g).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤)
    (hQP : Q * P = 1) (hPQ : P * Q = 1) :
    ∀ W : Submodule k (Fin 2 → k),
      (∀ g, ∀ v ∈ W, (Q * ρ g * P).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤ := by

  have hPinj : Function.Injective P.mulVecLin := by
    intro v w h
    have h' := congrArg Q.mulVec h
    simp only [Matrix.mulVecLin_apply] at h'
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hQP, Matrix.one_mulVec,
      Matrix.one_mulVec] at h'
    exact h'
  have hPsurj : Function.Surjective P.mulVecLin := by
    intro v
    refine ⟨Q.mulVec v, ?_⟩
    simp only [Matrix.mulVecLin_apply]
    rw [Matrix.mulVec_mulVec, hPQ, Matrix.one_mulVec]
  intro W hW

  have hmap : ∀ g, ∀ v ∈ W.map P.mulVecLin, (ρ g).mulVec v ∈ W.map P.mulVecLin := by
    intro g v hv
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
    refine Submodule.mem_map.mpr ⟨(Q * ρ g * P).mulVec w, hW g w hw, ?_⟩
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
    congr 1
    calc P * (Q * ρ g * P) = (P * Q) * ρ g * P := by noncomm_ring
      _ = ρ g * P := by rw [hPQ, one_mul]
  rcases hirr _ hmap with h | h
  · left
    have hbot : W.map P.mulVecLin = (⊥ : Submodule k (Fin 2 → k)).map P.mulVecLin := by
      rw [h, Submodule.map_bot]
    exact Submodule.map_injective_of_injective hPinj hbot
  · right
    have htop : W.map P.mulVecLin = (⊤ : Submodule k (Fin 2 → k)).map P.mulVecLin := by
      rw [h, Submodule.map_top, LinearMap.range_eq_top.mpr hPsurj]
    exact Submodule.map_injective_of_injective hPinj htop

end Transport

section Application

variable {V : Type*} [AddCommGroup V] [Module k V]
  {ρV : Representation k G V} {ρ : G → Matrix (Fin 2) (Fin 2) k}

theorem exists_embedding_of_irreducible_of_odd_aux
    (hρ : ∀ σ τ : G, ρ (σ * τ) = ρ σ * ρ τ)
    (hCH : ∀ σ : G, ρV σ * ρV σ - (ρ σ).trace • ρV σ
      + (ρ σ).det • (1 : Module.End k V) = 0)
    (hirr : ∀ W : Submodule k (Fin 2 → k),
      (∀ g, ∀ v ∈ W, (ρ g).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤)
    {c : G} (hc2 : ρ c * ρ c = 1) (hcdet : (ρ c).det = -1) (h2 : (2 : k) ≠ 0)
    (hV : ∃ v : V, v ≠ 0) :
    ∃ φ : (Fin 2 → k) →ₗ[k] V, Function.Injective φ ∧
      ∀ (σ : G) (v : Fin 2 → k), φ ((ρ σ).mulVec v) = ρV σ (φ v) := by
  classical

  obtain ⟨P, Q, hQP, hPQ, hQAP⟩ := exists_conj_diag_of_invol hc2 hcdet h2

  have h1m1 : (1 : k) ≠ -1 := fun h => h2 (by linear_combination h)

  have hρ'mul : ∀ σ τ : G, Q * ρ (σ * τ) * P = (Q * ρ σ * P) * (Q * ρ τ * P) :=
    conj_mul hρ hPQ

  have hCH' : ∀ σ : G, ρV σ * ρV σ - (Q * ρ σ * P).trace • ρV σ
      + (Q * ρ σ * P).det • (1 : Module.End k V) = 0 := by
    intro σ
    rw [trace_conj hPQ, det_conj hPQ]
    exact hCH σ

  have hirr' := irreducible_conj hirr hQP hPQ

  obtain ⟨τ₀, hτ₀⟩ := exists_entry_zero_one_ne_zero (ρ := fun g => Q * ρ g * P) hirr'
  obtain ⟨υ₀, hυ₀⟩ := exists_entry_one_zero_ne_zero (ρ := fun g => Q * ρ g * P) hirr'

  obtain ⟨φ, hφinj, hφequiv⟩ :=
    exists_embedding (ρ := fun g => Q * ρ g * P) (ρV := ρV) hρ'mul hCH' h1m1 hQAP hτ₀ hυ₀ hV

  refine ⟨φ ∘ₗ Q.mulVecLin, ?_, ?_⟩
  ·
    refine hφinj.comp ?_
    intro v w h
    have h' := congrArg P.mulVec h
    simp only [Matrix.mulVecLin_apply] at h'
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hPQ, Matrix.one_mulVec,
      Matrix.one_mulVec] at h'
    exact h'
  ·
    intro σ v
    have hkey : Q.mulVec ((ρ σ).mulVec v) = (Q * ρ σ * P).mulVec (Q.mulVec v) := by
      have hcollapse : Q * ρ σ * P * Q = Q * ρ σ := by
        rw [mul_assoc (Q * ρ σ) P Q, hPQ, mul_one]
      simp only [Matrix.mulVec_mulVec, hcollapse]
    simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply, hkey]
    exact hφequiv σ (Q.mulVec v)

end Application

end BostonLenstraRibet

theorem solution {k : Type*} [Field k] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module k V]
    {ρV : Representation k G V} {ρ : G → Matrix (Fin 2) (Fin 2) k}
    (hρ : ∀ σ τ : G, ρ (σ * τ) = ρ σ * ρ τ)
    (hCH : ∀ σ : G, ρV σ * ρV σ - (ρ σ).trace • ρV σ
      + (ρ σ).det • (1 : Module.End k V) = 0)
    (hirr : ∀ W : Submodule k (Fin 2 → k),
      (∀ g, ∀ v ∈ W, (ρ g).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤)
    {c : G} (hc2 : ρ c * ρ c = 1) (hcdet : (ρ c).det = -1) (h2 : (2 : k) ≠ 0)
    (hV : ∃ v : V, v ≠ 0) :
    ∃ φ : (Fin 2 → k) →ₗ[k] V, Function.Injective φ ∧
      ∀ (σ : G) (v : Fin 2 → k), φ ((ρ σ).mulVec v) = ρV σ (φ v) :=
  BostonLenstraRibet.exists_embedding_of_irreducible_of_odd_aux hρ hCH hirr hc2 hcdet h2 hV

end S_BostonLenstraRibet_exists_embedding_of_irreducible_of_odd
end P2MW
export P2MW.S_BostonLenstraRibet_exists_embedding_of_irreducible_of_odd (solution)
