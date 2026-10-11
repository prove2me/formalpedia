-- Prove2me | solution 1 for FredholmBanach.isFredholm_iff_exists_compact_quasiInverse
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T23:46:32.00289+00:00
-- url     : https://prove2.me/submissions/681ec80f-7225-4c2d-9e4d-797019dfdd2b

import Definitions.Def_FredholmBanach_Setting
import Theorems.Thm_FredholmBanach_isFredholm_iff_finiteDimensional
import Theorems.Thm_FredholmBanach_isCompactOperator_of_finiteDimensional_range
import Theorems.Thm_FredholmBanach_isFredholm_index_zero_of_isCompactOperator_id_sub

open Topology LinearMap.FiniteRangeSetoid

theorem solution {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    (u : E →L[𝕜] F) :
    u.IsFredholm ↔ ∃ v : F →L[𝕜] E,
      IsCompactOperator (ContinuousLinearMap.id 𝕜 E - v.comp u) ∧
        IsCompactOperator (ContinuousLinearMap.id 𝕜 F - u.comp v) := by
  constructor
  · intro hu
    obtain ⟨v, hvu, huv⟩ := hu.exists_isQuasiInverse
    simp only [LinearMap.IsLeftQuasiInverse, LinearMap.IsRightQuasiInverse] at hvu huv
    -- `w ≈ id` modulo finite rank makes `id - w` of finite rank, hence compact
    rw [equiv_iff_hasFiniteRange, LinearMap.hasFiniteRange_iff_range] at hvu
    rw [equiv_iff_hasFiniteRange, LinearMap.hasFiniteRange_iff_range] at huv
    refine ⟨v, FredholmBanach.isCompactOperator_of_finiteDimensional_range _ ?_,
      FredholmBanach.isCompactOperator_of_finiteDimensional_range _ ?_⟩
    · have he : ((ContinuousLinearMap.id 𝕜 E - v.comp u : E →L[𝕜] E) : E →ₗ[𝕜] E) =
          -(((v.comp u : E →L[𝕜] E) : E →ₗ[𝕜] E) - LinearMap.id) := by
        ext x; simp
      change FiniteDimensional 𝕜 (LinearMap.range
        ((ContinuousLinearMap.id 𝕜 E - v.comp u : E →L[𝕜] E) : E →ₗ[𝕜] E))
      rw [he, LinearMap.range_neg]
      exact Module.Finite.iff_fg.mpr hvu
    · have he : ((ContinuousLinearMap.id 𝕜 F - u.comp v : F →L[𝕜] F) : F →ₗ[𝕜] F) =
          -(((u.comp v : F →L[𝕜] F) : F →ₗ[𝕜] F) - LinearMap.id) := by
        ext x; simp
      change FiniteDimensional 𝕜 (LinearMap.range
        ((ContinuousLinearMap.id 𝕜 F - u.comp v : F →L[𝕜] F) : F →ₗ[𝕜] F))
      rw [he, LinearMap.range_neg]
      exact Module.Finite.iff_fg.mpr huv
  · rintro ⟨v, h1, h2⟩
    have hvu := (FredholmBanach.isFredholm_iff_finiteDimensional _).1
      (FredholmBanach.isFredholm_index_zero_of_isCompactOperator_id_sub _ h1).1
    have huv := (FredholmBanach.isFredholm_iff_finiteDimensional _).1
      (FredholmBanach.isFredholm_index_zero_of_isCompactOperator_id_sub _ h2).1
    rw [FredholmBanach.isFredholm_iff_finiteDimensional]
    have hk : u.ker ≤ (v.comp u).ker := fun x hx => by
      have hx' : u x = 0 := hx
      show v (u x) = 0
      rw [hx', map_zero]
    have hr : (u.comp v).range ≤ u.range := by
      rintro _ ⟨y, rfl⟩; exact ⟨v y, rfl⟩
    haveI := hvu.1
    haveI := huv.2
    exact ⟨Submodule.finiteDimensional_of_le hk,
      Module.Finite.of_surjective _ (Submodule.factor_surjective hr)⟩
