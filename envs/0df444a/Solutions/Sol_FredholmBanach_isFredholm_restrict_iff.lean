-- Prove2me | solution 1 for FredholmBanach.isFredholm_restrict_iff
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T18:56:33.054099+00:00
-- url     : https://prove2.me/submissions/19be2a74-e9ef-4a30-8618-6f362fc7d2b3

import Definitions.Def_FredholmBanach_Setting
import Theorems.Thm_FredholmBanach_isFredholm_iff_finiteDimensional
import Mathlib.Algebra.Module.LinearMap.Index

open Topology

theorem solution {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    (u : E →L[𝕜] F) (E₁ : Submodule 𝕜 E) (F₁ : Submodule 𝕜 F)
    (hE₁ : IsClosed (E₁ : Set E)) (hF₁ : IsClosed (F₁ : Set F))
    (hE₁f : FiniteDimensional 𝕜 (E ⧸ E₁)) (hF₁f : FiniteDimensional 𝕜 (F ⧸ F₁))
    (h : Set.MapsTo u E₁ F₁) :
    (u.IsFredholm ↔ (u.restrict h).IsFredholm) ∧
      (u.IsFredholm → FredholmBanach.index u - FredholmBanach.index (u.restrict h) =
        (Module.finrank 𝕜 (E ⧸ E₁) : ℤ) - (Module.finrank 𝕜 (F ⧸ F₁) : ℤ)) := by
  haveI : CompleteSpace E₁ := hE₁.completeSpace_coe
  haveI : CompleteSpace F₁ := hF₁.completeSpace_coe
  set L : E →ₗ[𝕜] F := (u : E →ₗ[𝕜] F)
  set L₁ : E₁ →ₗ[𝕜] F₁ := ((u.restrict h : E₁ →L[𝕜] F₁) : E₁ →ₗ[𝕜] F₁)
  have hsq : F₁.subtype ∘ₗ L₁ = L ∘ₗ E₁.subtype := LinearMap.ext fun _ => rfl
  haveI : FiniteDimensional 𝕜 (LinearMap.ker E₁.subtype) := by
    rw [Submodule.ker_subtype]; infer_instance
  haveI : FiniteDimensional 𝕜 (LinearMap.ker F₁.subtype) := by
    rw [Submodule.ker_subtype]; infer_instance
  haveI : FiniteDimensional 𝕜 (E ⧸ LinearMap.range E₁.subtype) := by
    rw [Submodule.range_subtype]; exact hE₁f
  haveI : FiniteDimensional 𝕜 (F ⧸ LinearMap.range F₁.subtype) := by
    rw [Submodule.range_subtype]; exact hF₁f
  have hiff : u.IsFredholm ↔ (u.restrict h).IsFredholm := by
    rw [FredholmBanach.isFredholm_iff_finiteDimensional,
      FredholmBanach.isFredholm_iff_finiteDimensional]
    constructor
    · rintro ⟨hk, hc⟩
      haveI := hk; haveI := hc
      -- `F₁.subtype ∘ L₁ = L ∘ E₁.subtype` has finite kernel and cokernel
      have hk' : FiniteDimensional 𝕜 (LinearMap.ker (F₁.subtype ∘ₗ L₁)) := by
        rw [hsq, LinearMap.ker_comp]; infer_instance
      have hc' : FiniteDimensional 𝕜 (F ⧸ LinearMap.range (F₁.subtype ∘ₗ L₁)) := by
        rw [hsq, LinearMap.range_comp]; infer_instance
      refine ⟨Submodule.finiteDimensional_of_le (LinearMap.ker_le_ker_comp L₁ F₁.subtype), ?_⟩
      have aux : LinearMap.range L₁ ≤ (LinearMap.range (F₁.subtype ∘ₗ L₁)).comap F₁.subtype := by
        rw [← Submodule.map_le_iff_le_comap, LinearMap.range_comp]
      refine Module.Finite.of_injective ((LinearMap.range L₁).mapQ _ F₁.subtype aux) ?_
      rw [← LinearMap.ker_eq_bot, Submodule.ker_mapQ, LinearMap.range_comp,
        Submodule.comap_map_eq_of_injective F₁.injective_subtype, Submodule.mkQ_map_self]
    · rintro ⟨hk, hc⟩
      haveI := hk; haveI := hc
      -- `L ∘ E₁.subtype = F₁.subtype ∘ L₁` has finite kernel and cokernel
      have hk' : FiniteDimensional 𝕜 (LinearMap.ker (L ∘ₗ E₁.subtype)) := by
        rw [← hsq, LinearMap.ker_comp]; infer_instance
      have hc' : FiniteDimensional 𝕜 (F ⧸ LinearMap.range (L ∘ₗ E₁.subtype)) := by
        rw [← hsq, LinearMap.range_comp]; infer_instance
      refine ⟨?_, Module.Finite.of_surjective
        (Submodule.factor (LinearMap.range_comp_le_range E₁.subtype L))
        (Submodule.factor_surjective _)⟩
      have hmap : ((LinearMap.ker L).map (LinearMap.range E₁.subtype).mkQ).FG :=
        Module.Finite.iff_fg.mp inferInstance
      have hinf : (LinearMap.ker L ⊓ LinearMap.ker (LinearMap.range E₁.subtype).mkQ).FG := by
        rw [Submodule.ker_mkQ]
        have hle : LinearMap.ker L ⊓ LinearMap.range E₁.subtype ≤
            (LinearMap.ker (L ∘ₗ E₁.subtype)).map E₁.subtype := by
          rintro _ ⟨hx, ⟨y, rfl⟩⟩
          exact ⟨y, by simpa using hx, rfl⟩
        haveI := Submodule.finiteDimensional_of_le hle
        exact Module.Finite.iff_fg.mp inferInstance
      exact Module.Finite.iff_fg.mpr (Submodule.fg_of_fg_map_of_fg_inf_ker _ hmap hinf)
  refine ⟨hiff, fun hu => ?_⟩
  have hu₁ := hiff.mp hu
  rw [FredholmBanach.isFredholm_iff_finiteDimensional] at hu hu₁
  haveI := hu.1; haveI := hu.2; haveI := hu₁.1; haveI := hu₁.2
  have e1 := LinearMap.index_comp (f := L₁) F₁.subtype
  have e2 := LinearMap.index_comp (f := E₁.subtype) L
  rw [hsq, e2] at e1
  have iE := LinearMap.index_of_injective (R := 𝕜) E₁.injective_subtype
  have iF := LinearMap.index_of_injective (R := 𝕜) F₁.injective_subtype
  rw [Submodule.range_subtype] at iE iF
  change L.index - L₁.index = _
  lia
