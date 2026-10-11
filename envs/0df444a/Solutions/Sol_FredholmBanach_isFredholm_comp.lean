-- Prove2me | solution 1 for FredholmBanach.isFredholm_comp
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T18:37:01.538501+00:00
-- url     : https://prove2.me/submissions/52644d50-1e3b-4c03-a575-fef5ff154986

import Definitions.Def_FredholmBanach_Setting
import Theorems.Thm_FredholmBanach_isFredholm_iff_finiteDimensional

open Topology

theorem solution {𝕜 E F G : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]
    {u : E →L[𝕜] F} {v : F →L[𝕜] G} (hu : u.IsFredholm) (hv : v.IsFredholm) :
    (v.comp u).IsFredholm := by
  rw [FredholmBanach.isFredholm_iff_finiteDimensional] at hu hv ⊢
  obtain ⟨hku, hcu⟩ := hu
  obtain ⟨hkv, hcv⟩ := hv
  refine ⟨?_, ?_⟩
  · -- kernel: `u` maps `ker (v ∘ u)` into `ker v`, with kernel inside `ker u`
    have hmap : ((v.comp u).ker.map (u : E →ₗ[𝕜] F)).FG := by
      have hle : (v.comp u).ker.map (u : E →ₗ[𝕜] F) ≤ v.ker := by
        rintro _ ⟨x, hx, rfl⟩
        simpa using hx
      haveI := Submodule.finiteDimensional_of_le hle
      exact Module.Finite.iff_fg.mp inferInstance
    have hinf : ((v.comp u).ker ⊓ LinearMap.ker (u : E →ₗ[𝕜] F)).FG := by
      haveI := Submodule.finiteDimensional_of_le
        (inf_le_right : (v.comp u).ker ⊓ LinearMap.ker (u : E →ₗ[𝕜] F) ≤ u.ker)
      exact Module.Finite.iff_fg.mp inferInstance
    exact Module.Finite.iff_fg.mpr (Submodule.fg_of_fg_map_of_fg_inf_ker _ hmap hinf)
  · -- cokernel: complements of `range u` and `range v`
    obtain ⟨D, hD⟩ := Submodule.exists_isCompl u.range
    obtain ⟨C, hC⟩ := Submodule.exists_isCompl v.range
    haveI : FiniteDimensional 𝕜 D := (Submodule.quotientEquivOfIsCompl _ _ hD).finiteDimensional
    haveI : FiniteDimensional 𝕜 C := (Submodule.quotientEquivOfIsCompl _ _ hC).finiteDimensional
    have hq : (D.map (v : F →ₗ[𝕜] G) ⊔ C).FG :=
      (Submodule.FG.map _ (Module.Finite.iff_fg.mp inferInstance)).sup
        (Module.Finite.iff_fg.mp inferInstance)
    have htop : (v.comp u).range ⊔ (D.map (v : F →ₗ[𝕜] G) ⊔ C) = ⊤ := by
      have hrv : LinearMap.range (v : F →ₗ[𝕜] G) =
          LinearMap.range ((v.comp u : E →L[𝕜] G) : E →ₗ[𝕜] G) ⊔ D.map (v : F →ₗ[𝕜] G) := by
        have hc : ((v.comp u : E →L[𝕜] G) : E →ₗ[𝕜] G) =
            (v : F →ₗ[𝕜] G).comp (u : E →ₗ[𝕜] F) := rfl
        rw [hc, LinearMap.range_comp, ← Submodule.map_sup,
          hD.sup_eq_top, Submodule.map_top]
      rw [← sup_assoc, ← hrv]
      exact hC.sup_eq_top
    haveI : Module.Finite 𝕜 (G ⧸ (v.comp u).range) := by
      rw [Module.finite_def, ← (Submodule.map_mkQ_eq_top _ _).mpr htop]
      exact hq.map _
    infer_instance
