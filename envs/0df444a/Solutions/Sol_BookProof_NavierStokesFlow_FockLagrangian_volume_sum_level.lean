-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockLagrangian.volume_sum_level
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-18T21:07:19.781661+00:00
-- url     : https://prove2.me/submissions/64ef62cf-cb7a-43c0-ac08-12473515fd1c

-- Generated from ChapterNavierStokesFockParcels.lean — solution of BookProof.NavierStokesFlow.FockLagrangian.volume_sum_level
import Mathlib
import Definitions.Def_ChapterNavierStokesFockParcels
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesFockLagrangian
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockLagrangian



open MeasureTheory



open FullEsa FockContinuum

variable {Ω : Type*} [MeasurableSpace Ω]

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) (hn : 0 < n) (c : ℝ) :
    (volume : Measure (Fin n → ℝ)) {ξ : Fin n → ℝ | ∑ i, ξ i = c} = 0 := by

  classical
  have happ : ∀ ξ : Fin n → ℝ,
      ((∑ i : Fin n, LinearMap.proj i : (Fin n → ℝ) →ₗ[ℝ] ℝ)) ξ = ∑ i, ξ i := by
    intro ξ
    rw [LinearMap.coe_sum, Finset.sum_apply]
    rfl
  obtain ⟨S, hcar⟩ : ∃ S : AffineSubspace ℝ (Fin n → ℝ),
      (S : Set (Fin n → ℝ)) = {ξ : Fin n → ℝ | ∑ i, ξ i = c} := by
    refine ⟨AffineSubspace.comap
      ((∑ i : Fin n, LinearMap.proj i : (Fin n → ℝ) →ₗ[ℝ] ℝ).toAffineMap)
      (AffineSubspace.mk' c (⊥ : Submodule ℝ ℝ)), ?_⟩
    ext ξ
    rw [SetLike.mem_coe, AffineSubspace.mem_comap, AffineSubspace.mem_mk', vsub_eq_sub,
      Submodule.mem_bot, sub_eq_zero, LinearMap.coe_toAffineMap, happ]
    exact Iff.rfl
  have hne : S ≠ ⊤ := by
    intro h
    have hmem : (fun _ => (c + 1) / n : Fin n → ℝ) ∈ S := by rw [h]; trivial
    rw [← SetLike.mem_coe, hcar] at hmem
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    simp only [Set.mem_setOf_eq, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at hmem
    field_simp at hmem
    linarith
  have h0 := Measure.addHaar_affineSubspace (volume : Measure (Fin n → ℝ)) S hne
  rwa [hcar] at h0
