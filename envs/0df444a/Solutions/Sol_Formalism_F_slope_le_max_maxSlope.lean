-- Prove2me | solution 1 for Formalism.F.slope_le_max_maxSlope
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:20:01.068802+00:00
-- url     : https://prove2.me/submissions/b7aece5a-9cc6-42f6-b9d5-0b31efba2d7d

import Definitions.Def_Formalism_LatticeSlopes_Statement
import Definitions.Def_Formalism_LatticeSlopes_CovolAntiSameRank
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolEqGram
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolPos
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DegQuot
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_GramDetLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_SlopesBdd
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_SlopeLeMuMaxOf
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_SlopeInequality
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_OrthSum
import Theorems.Thm_Formalism_F_degree_le_rank_mul_maxSlope
import Theorems.Thm_Formalism_F_degree_le_rank_mul_maxSlope_of_injective
import Theorems.Thm_Formalism_F_degree_quotient
import Theorems.Thm_Formalism_F_discreteTopology_of_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.F
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
set_option maxHeartbeats 800000
namespace Formalism.F
theorem _root_.solution (L₁ L₂ : Submodule ℤ E) (h1 : DiscreteTopology L₁)
    (h2 : DiscreteTopology L₂) (h : ∀ x ∈ L₁, ∀ y ∈ L₂, inner ℝ x y = 0)
    (hd : DiscreteTopology (L₁ ⊔ L₂ : Submodule ℤ E))
    (N : Submodule ℤ E) (hN : N ≤ L₁ ⊔ L₂) (hN0 : N ≠ ⊥) :
    slope N ≤ max (muMax L₁) (muMax L₂) := by
  haveI := h1
  haveI := h2
  haveI := hd
  haveI hNd : DiscreteTopology N := discreteTopology_of_le hN

  obtain ⟨P, hPdef⟩ : ∃ P : E →L[ℝ] E, P = (span ℝ (L₂ : Set E)).starProjection := ⟨_, rfl⟩
  have hortho : span ℝ (L₁ : Set E) ≤ (span ℝ (L₂ : Set E))ᗮ := by
    rw [← Submodule.isOrtho_iff_le, Submodule.isOrtho_span]
    intro x hx y hy
    exact h x hx y hy
  have hP0 : ∀ x ∈ span ℝ (L₁ : Set E), P x = 0 := fun x hx => by
    rw [hPdef, Submodule.starProjection_apply_eq_zero_iff]
    exact hortho hx
  have hP1 : ∀ x ∈ L₁, P x = 0 := fun x hx => hP0 x (subset_span hx)
  have hP2 : ∀ x ∈ L₂, P x = x := fun x hx => by
    rw [hPdef, Submodule.starProjection_eq_self_iff]
    exact subset_span hx
  have hP3 : ∀ x ∈ L₁ ⊔ L₂, P x ∈ L₂ ∧ x - P x ∈ L₁ := by
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add, hP1 y hy, hP2 z hz, zero_add, add_sub_cancel_right]
    exact ⟨hz, hy⟩
  have hPnorm : ∀ x, ‖P x‖ ≤ ‖x‖ := fun x => by
    rw [hPdef]; exact Submodule.norm_starProjection_apply_le _ x

  set K : Submodule ℤ E := N ⊓ L₁ with hK
  have hKspan : span ℝ (K : Set E) ≤ span ℝ (L₁ : Set E) :=
    Submodule.span_mono (fun x hx => hx.2)
  have hsat : IsSaturated N K := by
    refine ⟨inf_le_left, fun x hx hxs => ⟨hx, ?_⟩⟩
    have h0 : P x = 0 := hP0 x (hKspan hxs)
    have := (hP3 x (hN hx)).2
    rwa [h0, sub_zero] at this
  obtain ⟨hQd, hrk, hdeg⟩ := degree_quotient E N K hNd hsat
  set Q := quot N K with hQ

  have hPR : ∀ x ∈ N, P ((span ℝ (K : Set E))ᗮ.starProjection x) = P x := by
    intro x hx
    rw [Submodule.starProjection_orthogonal_val, map_sub]
    have hS : (span ℝ (K : Set E)).starProjection x ∈ span ℝ (L₁ : Set E) := by
      apply hKspan
      rw [Submodule.starProjection_apply]
      exact SetLike.coe_mem _
    rw [hP0 _ hS, sub_zero]
  have hQmem : ∀ y ∈ Q, P y ∈ L₂ := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    change P ((span ℝ (K : Set E))ᗮ.starProjection x) ∈ L₂
    rw [hPR x hx]
    exact (hP3 x (hN hx)).1
  let ψ : Q →ₗ[ℤ] L₂ := LinearMap.codRestrict L₂
    ((P.toLinearMap.restrictScalars ℤ).comp Q.subtype) (fun y => hQmem y.1 y.2)
  have hψ : ∀ y : Q, ((ψ y : L₂) : E) = P y := fun y => rfl
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro y hy0
    have hPy : P y = 0 := by
      rw [← hψ, hy0]; rfl
    obtain ⟨y, hyQ⟩ := y
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hyQ
    change P ((span ℝ (K : Set E))ᗮ.starProjection x) = 0 at hPy
    rw [hPR x hx] at hPy
    have hx1 : x ∈ L₁ := by
      have := (hP3 x (hN hx)).2
      rwa [hPy, sub_zero] at this
    have hxK : x ∈ span ℝ (K : Set E) := subset_span ⟨hx, hx1⟩
    apply Subtype.ext
    change (span ℝ (K : Set E))ᗮ.starProjection x = 0
    rw [Submodule.starProjection_orthogonal_val, Submodule.starProjection_eq_self_iff.mpr hxK, sub_self]
  have hnorm : ∀ y : Q, ‖((ψ y : L₂) : E)‖ ≤ ‖(y : E)‖ := fun y => by
    rw [hψ]; exact hPnorm _
  have hdK : deg K ≤ rk K * muMax L₁ := degree_le_rank_mul_maxSlope L₁ K h1 inf_le_right
  have hdQ : deg Q ≤ rk Q * muMax L₂ := degree_le_rank_mul_maxSlope_of_injective Q L₂ hQd h2 ψ hinj hnorm
  have hk : 0 < rk N := Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hN0)
  have hk' : (0 : ℝ) < (rk N : ℝ) := by exact_mod_cast hk
  have hK0 : (0 : ℝ) ≤ (rk K : ℝ) := Nat.cast_nonneg _
  have hQ0 : (0 : ℝ) ≤ (rk Q : ℝ) := Nat.cast_nonneg _
  have e1 : (rk K : ℝ) * muMax L₁ ≤ (rk K : ℝ) * max (muMax L₁) (muMax L₂) :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) hK0
  have e2 : (rk Q : ℝ) * muMax L₂ ≤ (rk Q : ℝ) * max (muMax L₁) (muMax L₂) :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) hQ0
  have hrk' : (rk N : ℝ) = (rk K : ℝ) + (rk Q : ℝ) := by exact_mod_cast hrk
  unfold slope
  rw [div_le_iff₀ hk', hdeg, hrk']
  linarith
end Formalism.F
