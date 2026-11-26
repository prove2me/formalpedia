-- Prove2me | solution 1 for Erdos338.erdos_338.variants.lowerDensity_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:11:19.062521+00:00
-- url     : https://prove2.me/submissions/673db822-5f39-4d8b-86ee-04d91ddc9e9f

module
public import Mathlib
public import Definitions.Def_Erdos338
public import Definitions.Def_Erdos338_Solution
public import Theorems.Thm_Erdos338Proof_ncard_Iio
public import Theorems.Thm_Erdos338Proof_ncard_inter_Iio
public import Theorems.Thm_Erdos338Proof_residue_of_robust
public import Theorems.Thm_Erdos338Proof_restricted_of_density


set_option autoImplicit true
@[expose] public section
public section
open Filter
open scoped Topology
open Erdos338
namespace Erdos338
namespace erdos_338.variants
theorem _root_.solution :
    ∀ A : Set ℕ, (∀ F : Set ℕ, F.Finite → ∃ h, HasOrder (A \ F) h) → 0 < A.lowerDensity →
      ∃ t, HasRestrictedOrder A t := by
  intro A hrob hpos
  -- `δ = lowerDensity / 2` is eventually a lower bound for `|A ∩ [0, b)| / b`
  obtain ⟨N₀, hN₀⟩ : ∃ N₀, ∀ b ≥ N₀, A.lowerDensity / 2 * b ≤ Erdos338Proof.cnt A b := by
    have hlt : A.lowerDensity / 2 < atTop.liminf fun b : ℕ ↦ A.partialDensity Set.univ b :=
      half_lt_self hpos
    have hev := eventually_lt_of_lt_liminf hlt (isBoundedUnder_of_eventually_ge (a := 0)
      (Eventually.of_forall fun b ↦ div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    refine ⟨N + 1, fun b hb ↦ ?_⟩
    have h := hN b (by omega)
    simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Erdos338Proof.ncard_inter_Iio,
      Erdos338Proof.ncard_Iio] at h
    have hb : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
    rw [lt_div_iff₀ hb] at h
    exact h.le
  obtain ⟨t, ht⟩ := Erdos338Proof.restricted_of_density A
    (fun Q hQ c ↦ Erdos338Proof.residue_of_robust A hrob hQ c) (half_pos hpos) hN₀
  exact ⟨t, ht⟩
end erdos_338.variants
end Erdos338
