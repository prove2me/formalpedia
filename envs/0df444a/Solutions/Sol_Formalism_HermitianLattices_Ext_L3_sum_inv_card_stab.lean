-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.sum_inv_card_stab
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:25:39.831795+00:00
-- url     : https://prove2.me/submissions/4e1a796d-1219-4bc9-94c2-cac3c505075b

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteDimensionalOfOrtho
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_AutFinite
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteRepSetOfOrtho
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
namespace Formalism.HermitianLattices.Ext.L3
theorem _root_.solution {G X : Type*} [Group G] [Finite G] [MulAction G X] (A : Set X)
    [Finite A] (hA : ∀ g : G, ∀ x ∈ A, g • x ∈ A) (T : Finset X) (hTA : ∀ t ∈ T, t ∈ A)
    (hT : ∀ x ∈ A, ∃! t, t ∈ T ∧ ∃ g : G, g • t = x) :
    (Nat.card A : ℝ) / (Nat.card G : ℝ) =
      ∑ t ∈ T, ((Nat.card (MulAction.stabilizer G t) : ℕ) : ℝ)⁻¹ := by
  classical
  have hGpos : (0 : ℝ) < Nat.card G := by exact_mod_cast Nat.card_pos
  have hos : ∀ t : X, (Nat.card (MulAction.orbit G t) : ℝ) =
      Nat.card G / Nat.card (MulAction.stabilizer G t) := by
    intro t
    have h1 := (MulAction.stabilizer G t).card_mul_index
    rw [MulAction.index_stabilizer, ← Nat.card_coe_set_eq] at h1
    have hs : (0 : ℝ) < Nat.card (MulAction.stabilizer G t) := by exact_mod_cast Nat.card_pos
    rw [eq_div_iff hs.ne', ← Nat.cast_mul, mul_comm, h1]
  obtain ⟨A', hA'⟩ : ∃ A' : Finset X, ∀ x, x ∈ A' ↔ x ∈ A :=
    ⟨(Set.toFinite A).toFinset, fun x => Set.Finite.mem_toFinset _⟩
  have hAeq : A = ↑A' := Set.ext fun x => (hA' x).symm
  have hcover : A' = T.biUnion (fun t => A'.filter (fun x => ∃ g : G, g • t = x)) := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_filter]
    constructor
    · intro hx
      obtain ⟨t, ⟨htT, g, hg⟩, -⟩ := hT x ((hA' x).mp hx)
      exact ⟨t, htT, hx, g, hg⟩
    · rintro ⟨t, -, hx, -⟩
      exact hx
  have hdisj : ∀ t₁ ∈ T, ∀ t₂ ∈ T, t₁ ≠ t₂ →
      Disjoint (A'.filter (fun x => ∃ g : G, g • t₁ = x)) (A'.filter (fun x => ∃ g : G, g • t₂ = x)) := by
    intro t₁ h₁ t₂ h₂ hne
    refine Finset.disjoint_left.mpr ?_
    intro x hx1 hx2
    simp only [Finset.mem_filter] at hx1 hx2
    obtain ⟨t, -, huniq⟩ := hT x ((hA' x).mp hx1.1)
    exact hne ((huniq t₁ ⟨h₁, hx1.2⟩).trans (huniq t₂ ⟨h₂, hx2.2⟩).symm)
  have hcard : ∀ t ∈ T, ((A'.filter (fun x => ∃ g : G, g • t = x)).card : ℝ) =
      Nat.card (MulAction.orbit G t) := by
    intro t ht
    have hset : MulAction.orbit G t = ↑(A'.filter (fun x => ∃ g : G, g • t = x)) := by
      ext x
      simp only [MulAction.mem_orbit_iff, Finset.coe_filter, Set.mem_setOf_eq]
      constructor
      · rintro ⟨g, rfl⟩
        exact ⟨(hA' _).mpr (hA g t (hTA t ht)), g, rfl⟩
      · rintro ⟨-, g, rfl⟩
        exact ⟨g, rfl⟩
    rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  have hsum : (A'.card : ℝ) = ∑ t ∈ T, (Nat.card (MulAction.orbit G t) : ℝ) := by
    rw [hcover, Finset.card_biUnion hdisj, Nat.cast_sum]
    exact Finset.sum_congr rfl hcard
  rw [hAeq, Nat.card_coe_set_eq, Set.ncard_coe_finset, hsum, Finset.sum_div]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [hos t, div_div, mul_comm, ← div_div, div_self hGpos.ne', one_div]
end Formalism.HermitianLattices.Ext.L3
