-- Prove2me | solution 1 for Formalism.G0.ManyOrbitsP.lengthPart
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:34:02.75281+00:00
-- url     : https://prove2.me/submissions/5d8f2ce4-1d64-457e-8791-2e8e64611cf5

import Definitions.Def_Formalism_SubspaceCounting_StatementC
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_LengthLayers
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_WalkSharp
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ManyOrbits
import Theorems.Thm_Formalism_G0_ManyOrbitsP_allBut_mono
import Theorems.Thm_Formalism_G0_ManyOrbitsP_allBut_comap
import Theorems.Thm_Formalism_G0_ManyOrbitsP_comap_smul_self
import Theorems.Thm_Formalism_G0_ManyOrbitsP_geom_le
import Theorems.Thm_Formalism_G0_lengthBoundOfLayers


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0
open Formalism.G0.ManyOrbitsP
namespace Formalism.G0.ManyOrbitsP
theorem _root_.solution {R X : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [AddCommGroup X] [Module R X] (π : R) (hπ : Irreducible π) (M N : Submodule R X)
    [Module.Free R M] [Module.Finite R M] (d : ℕ) (hd : Module.finrank R M = d)
    (τ S V β₀ : ℕ) (s : ℝ) (hs0 : 0 ≤ s) (hs : s ≤ 1 / 2)
    (h1 : ∀ β ≤ β₀, ∃ C : Finset X, (↑C : Set X) ⊆ M ∧
      (C.card : ℝ) ≤ 2 * d * (s ^ (β + 1) / (β + 1).factorial) ∧
      ∀ x ∈ M, π ^ (τ + β * S) • x ∈ N ⊔ Submodule.span R (↑C : Set X))
    (h2 : AllButLE π M N 0 (V * S)) :
    ∃ ℓ : ℕ, Module.length R (M ⧸ Submodule.comap M.subtype
        (N ⊓ (Ideal.span {π ^ τ}) • M)) = ℓ ∧
      (ℓ : ℝ) ≤ d * (τ + 4 * S * s + V * S * (2 * s ^ (β₀ + 1) / (β₀ + 1).factorial)) := by
  classical
  set gβ : ℕ → ℕ := fun β => ⌊(2 * (d : ℝ) * (s ^ (β + 1) / (β + 1).factorial))⌋₊ with hgβ
  have hA : ∀ β ≤ β₀, AllButLE π (⊤ : Submodule R M) (N.comap M.subtype) (gβ β) (τ + β * S) := by
    intro β hβ
    obtain ⟨C, hCM, hCcard, hC⟩ := h1 β hβ
    exact allBut_comap π M N _ _ ⟨C, hCM, Nat.le_floor hCcard, hC⟩
  have hB : AllButLE π (⊤ : Submodule R M) (N.comap M.subtype) 0 (τ + V * S) :=
    allBut_comap π M N 0 (τ + V * S) (allBut_mono h2 le_rfl (by omega))
  have hL := lengthBoundOfLayers (O := R) (M := M) π hπ (N.comap M.subtype) τ S (V * S) β₀ gβ hA hB
  have hq : Submodule.comap M.subtype (N ⊓ (Ideal.span {π ^ τ}) • M) =
      N.comap M.subtype ⊓ (Ideal.span {π ^ τ}) • (⊤ : Submodule R M) := by
    rw [Submodule.comap_inf, comap_smul_self]
  rw [hd] at hL
  rw [hq]
  have hne : Module.length R (↥M ⧸ (N.comap M.subtype ⊓ (Ideal.span {π ^ τ}) • (⊤ : Submodule R M))) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.coe_ne_top _) hL
  refine ⟨_, (ENat.coe_toNat hne).symm, ?_⟩
  have hnat : (Module.length R (↥M ⧸ (N.comap M.subtype ⊓ (Ideal.span {π ^ τ}) • (⊤ : Submodule R M)))).toNat ≤
      d * τ + S * ∑ β ∈ Finset.range β₀, gβ β + V * S * gβ β₀ := by
    rw [← ENat.coe_le_coe, ENat.coe_toNat hne]
    exact hL
  have hg_le : ∀ β, (gβ β : ℝ) ≤ 2 * (d : ℝ) * (s ^ (β + 1) / (β + 1).factorial) :=
    fun β => Nat.floor_le (by positivity)
  have hterm : ∀ β, 2 * (d : ℝ) * (s ^ (β + 1) / (β + 1).factorial) ≤ 2 * d * s * s ^ β := by
    intro β
    have hf : (1 : ℝ) ≤ (β + 1).factorial := by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)
    calc 2 * (d : ℝ) * (s ^ (β + 1) / (β + 1).factorial) ≤ 2 * d * s ^ (β + 1) :=
          mul_le_mul_of_nonneg_left (div_le_self (pow_nonneg hs0 _) hf) (by positivity)
      _ = 2 * d * s * s ^ β := by ring
  have hsum : (∑ β ∈ Finset.range β₀, (gβ β : ℝ)) ≤ 4 * d * s := by
    calc ∑ β ∈ Finset.range β₀, (gβ β : ℝ) ≤ ∑ β ∈ Finset.range β₀, 2 * (d : ℝ) * s * s ^ β :=
          Finset.sum_le_sum fun β _ => (hg_le β).trans (hterm β)
      _ = 2 * d * s * ∑ β ∈ Finset.range β₀, s ^ β := by rw [Finset.mul_sum]
      _ ≤ 2 * d * s * 2 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith [geom_le s hs0 hs β₀, pow_nonneg hs0 β₀]
      _ = 4 * d * s := by ring
  have hcast : ((Module.length R (↥M ⧸ (N.comap M.subtype ⊓ (Ideal.span {π ^ τ}) •
      (⊤ : Submodule R M)))).toNat : ℝ) ≤
      (d : ℝ) * τ + S * ∑ β ∈ Finset.range β₀, (gβ β : ℝ) + V * S * (gβ β₀ : ℝ) := by
    exact_mod_cast hnat
  calc _ ≤ (d : ℝ) * τ + S * ∑ β ∈ Finset.range β₀, (gβ β : ℝ) + V * S * (gβ β₀ : ℝ) := hcast
    _ ≤ (d : ℝ) * τ + S * (4 * d * s) + V * S * (2 * (d : ℝ) * (s ^ (β₀ + 1) / (β₀ + 1).factorial)) :=
        add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hsum (by positivity)))
          (mul_le_mul_of_nonneg_left (hg_le β₀) (by positivity))
    _ = d * (τ + 4 * S * s + V * S * (2 * s ^ (β₀ + 1) / (β₀ + 1).factorial)) := by ring
end Formalism.G0.ManyOrbitsP
