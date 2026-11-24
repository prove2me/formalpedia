-- Prove2me | solution 1 for Formalism.HN.norm_starProjection_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:36.448803+00:00
-- url     : https://prove2.me/submissions/09c32532-e87c-40a9-9a9f-03f36c137b2a

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module Submodule
noncomputable section
namespace Formalism.HN
section SlopeTestRemainingChoices
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
private lemma le_of_forall_nat_mul_le_mul_add {a b K : ℝ}
    (h : ∀ n : ℕ, 0 < n → (n : ℝ) * a ≤ n * b + K) : a ≤ b := by
  by_contra hab
  push_neg at hab
  have hpos : 0 < a - b := sub_pos.mpr hab
  obtain ⟨n, hn⟩ := exists_nat_gt (K / (a - b))
  have h1 := h (n + 1) n.succ_pos
  push_cast at h1
  have h2 : ((n : ℝ) + 1) * (a - b) ≤ K := by linarith
  have h3 : (n : ℝ) + 1 ≤ K / (a - b) := (le_div_iff₀ hpos).mpr h2
  linarith
private lemma norm_sum_sub_round_smul_le_sum_norm {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {ι : Type*} [Fintype ι] (v : ι → X) (t : ι → ℝ) :
    ‖∑ i, (t i - (round (t i) : ℝ)) • v i‖ ≤ ∑ i, ‖v i‖ := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  have h1 := abs_sub_round (t i)
  have h2 := norm_nonneg (v i)
  have h3 := abs_nonneg (t i - (round (t i) : ℝ))
  nlinarith
end SlopeTestRemainingChoices
universe uR uV uW uE uF
end Formalism.HN
end
end

set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HN
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
namespace Formalism.HN
theorem _root_.solution {G : Type*} [AddCommGroup G] (α : G →+ E) (β : G →+ F) (C : ℝ)
    (h : ∀ g, ‖β g‖ ≤ C * ‖α g‖) (S : Set G) (U' : Submodule ℝ F) (hS : ∀ s ∈ S, β s ∈ U')
    (g : G) :
    ‖U'ᗮ.starProjection (β g)‖ ≤ C * ‖(span ℝ (α '' S))ᗮ.starProjection (α g)‖ := by
  by_cases hC : C < 0
  · have hb : ∀ g, β g = 0 := fun g => by
      have h1 := h g
      have h2 := norm_nonneg (α g)
      exact norm_eq_zero.mp (le_antisymm (by nlinarith) (norm_nonneg _))
    have ha : α g = 0 := by
      have h1 := h g
      rw [hb g, norm_zero] at h1
      have h2 := norm_nonneg (α g)
      exact norm_eq_zero.mp (le_antisymm (by nlinarith) h2)
    rw [hb g, ha, map_zero, map_zero, norm_zero, norm_zero, mul_zero]
  push_neg at hC
  have hw : α g - (span ℝ (α '' S))ᗮ.starProjection (α g) ∈ span ℝ (α '' S) := by
    first
    | exact (Submodule.orthogonal_orthogonal (span ℝ (α '' S))) ▸
        Submodule.sub_starProjection_mem_orthogonal (K := (span ℝ (α '' S))ᗮ) (α g)
    | (have hd := Submodule.starProjection_add_starProjection_orthogonal
          (K := span ℝ (α '' S)) (α g)
       rw [sub_eq_of_eq_add hd.symm]
       first
       | exact Submodule.starProjection_apply_mem _ _
       | exact ((span ℝ (α '' S)).orthogonalProjection (α g)).2
       | simp)
  obtain ⟨n, c, gg, hf⟩ := Submodule.mem_span_set'.mp hw
  have hs : ∀ i, ∃ s ∈ S, α s = (gg i : E) := fun i => (gg i).2
  choose s hsS hsα using hs
  have hrep : ∑ i, c i • α (s i) =
      α g - (span ℝ (α '' S))ᗮ.starProjection (α g) := by
    simp only [hsα]
    exact hf
  apply le_of_forall_nat_mul_le_mul_add (K := C * ∑ i, ‖α (s i)‖)
  intro k _
  have hnn : (0 : ℝ) ≤ k := k.cast_nonneg
  have h0 : ∀ i, U'ᗮ.starProjection (β (s i)) = 0 := fun i =>
    starProjection_orthogonal_apply_eq_zero (hS _ (hsS i))
  have hβ : U'ᗮ.starProjection (β (k • g - ∑ i, round ((k : ℝ) * c i) • s i)) =
      (k : ℝ) • U'ᗮ.starProjection (β g) := by
    simp [map_sub, map_sum, map_zsmul, map_nsmul, h0, Nat.cast_smul_eq_nsmul]
  have hα : α (k • g - ∑ i, round ((k : ℝ) * c i) • s i) =
      (k : ℝ) • (span ℝ (α '' S))ᗮ.starProjection (α g) +
        ∑ i, ((k : ℝ) * c i - (round ((k : ℝ) * c i) : ℝ)) • α (s i) := by
    have hx : α g = (span ℝ (α '' S))ᗮ.starProjection (α g) + ∑ i, c i • α (s i) := by
      rw [hrep]; abel
    rw [map_sub, map_nsmul, map_sum, ← Nat.cast_smul_eq_nsmul ℝ]
    conv_lhs => rw [hx]
    simp only [map_zsmul, smul_add, Finset.smul_sum, sub_smul, Finset.sum_sub_distrib, smul_smul,
      Int.cast_smul_eq_zsmul]
    abel
  have e1 : (k : ℝ) * ‖U'ᗮ.starProjection (β g)‖ =
      ‖U'ᗮ.starProjection (β (k • g - ∑ i, round ((k : ℝ) * c i) • s i))‖ := by
    rw [hβ, norm_smul, Real.norm_of_nonneg hnn]
  have e2 := norm_starProjection_apply_le U'ᗮ (β (k • g - ∑ i, round ((k : ℝ) * c i) • s i))
  have e3 := h (k • g - ∑ i, round ((k : ℝ) * c i) • s i)
  have e4 : ‖α (k • g - ∑ i, round ((k : ℝ) * c i) • s i)‖ ≤
      (k : ℝ) * ‖(span ℝ (α '' S))ᗮ.starProjection (α g)‖ + ∑ i, ‖α (s i)‖ := by
    rw [hα]
    refine (norm_add_le _ _).trans (add_le_add ?_
      (norm_sum_sub_round_smul_le_sum_norm (fun i => α (s i)) (fun i => (k : ℝ) * c i)))
    rw [norm_smul, Real.norm_of_nonneg hnn]
  nlinarith [mul_le_mul_of_nonneg_left e4 hC]
end Formalism.HN
