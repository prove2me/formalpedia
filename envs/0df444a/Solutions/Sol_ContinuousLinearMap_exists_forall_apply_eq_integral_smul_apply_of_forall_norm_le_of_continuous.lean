-- Prove2me | solution 1 for ContinuousLinearMap.exists_forall_apply_eq_integral_smul_apply_of_forall_norm_le_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/60e1bf25-1b4b-5e79-9038-bd68840b498e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ContinuousLinearMap_exists_forall_apply_eq_integral_smul_apply_of_forall_norm_le_of_continuous

set_option autoImplicit false

open MeasureTheory
open scoped ComplexConjugate InnerProductSpace

namespace AvgOp

theorem hasCompactSupport_of_compactSpace' {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [Zero Y] [TopologicalSpace Y]
    (f : X → Y) : HasCompactSupport f :=
  IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport f) (Set.subset_univ _)

variable {C : Type*} [Group C] [TopologicalSpace C] [IsTopologicalGroup C] [CompactSpace C] [T2Space C]
  [MeasurableSpace C] [BorelSpace C] (μ : Measure C) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (S : C →* (H →L[ℂ] H)) (B : ℝ) (hSb : ∀ c : C, ‖S c‖ ≤ B) (hSc : ∀ v : H, Continuous fun c : C => S c v)
  (w : C → ℂ) (hw : Continuous w)

include hSb hSc hw

theorem continuous_integrand (v : H) : Continuous fun c : C => w c • S c v :=
  hw.smul (hSc v)

theorem integrable_integrand (v : H) : Integrable (fun c : C => w c • S c v) μ :=
  (continuous_integrand S B hSb hSc w hw v).integrable_of_hasCompactSupport (hasCompactSupport_of_compactSpace' _)

theorem norm_integrand_le (v : H) (c : C) : ‖w c • S c v‖ ≤ ‖w c‖ * (B * ‖v‖) := by
  rw [norm_smul]
  gcongr
  exact (S c).le_of_opNorm_le (hSb c) v

theorem exists_bound_w : ∃ M : ℝ, ∀ c : C, ‖w c‖ ≤ M := by
  obtain ⟨c₀, -, hc₀⟩ := isCompact_univ.exists_isMaxOn (Set.univ_nonempty) hw.norm.continuousOn
  exact ⟨‖w c₀‖, fun c => hc₀ (Set.mem_univ c)⟩

theorem norm_integral_le (M : ℝ) (hM : ∀ c : C, ‖w c‖ ≤ M) (v : H) :
    ‖∫ c, w c • S c v ∂μ‖ ≤ M * B * ‖v‖ := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hSb 1)
  calc ‖∫ c, w c • S c v ∂μ‖ ≤ ∫ c, ‖w c • S c v‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ c, M * B * ‖v‖ ∂μ := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) (integrable_const _) ?_
        refine Filter.Eventually.of_forall fun c => ?_
        calc ‖w c • S c v‖ ≤ ‖w c‖ * (B * ‖v‖) := norm_integrand_le S B hSb hSc w hw v c
          _ ≤ M * (B * ‖v‖) := by gcongr; exact hM c
          _ = M * B * ‖v‖ := by ring
    _ = M * B * ‖v‖ := by simp

noncomputable def avgLin : H →ₗ[ℂ] H where
  toFun v := ∫ c, w c • S c v ∂μ
  map_add' v v' := by
    simp only [map_add, smul_add]
    exact integral_add (integrable_integrand μ S B hSb hSc w hw v) (integrable_integrand μ S B hSb hSc w hw v')
  map_smul' a v := by
    simp only [map_smul, RingHom.id_apply]
    rw [← integral_smul]
    congr 1; funext c; rw [smul_comm]

noncomputable def avg : H →L[ℂ] H :=
  (avgLin μ S B hSb hSc w hw).mkContinuousOfExistsBound (by
    obtain ⟨M, hM⟩ := exists_bound_w S B hSb hSc w hw
    exact ⟨M * B, fun v => norm_integral_le μ S B hSb hSc w hw M hM v⟩)

theorem avg_apply (v : H) : avg μ S B hSb hSc w hw v = ∫ c, w c • S c v ∂μ := rfl

theorem comm (T : H →L[ℂ] H) (hT : ∀ c : C, T.comp (S c) = (S c).comp T) :
    T.comp (avg μ S B hSb hSc w hw) = (avg μ S B hSb hSc w hw).comp T := by
  ext v
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, avg_apply]
  rw [← ContinuousLinearMap.integral_comp_comm T (integrable_integrand μ S B hSb hSc w hw v)]
  congr 1; funext c
  rw [ContinuousLinearMap.map_smul]
  congr 1
  exact congrArg (fun R : H →L[ℂ] H => R v) (hT c)

theorem map_le (L : Submodule ℂ H) (hL : IsClosed (L : Set H)) (hLs : ∀ c : C, L.map (S c : H →ₗ[ℂ] H) ≤ L) :
    L.map (avg μ S B hSb hSc w hw : H →ₗ[ℂ] H) ≤ L := by
  rintro _ ⟨m, hm, rfl⟩
  have hLcl : Lᗮᗮ = L := by
    rw [Submodule.orthogonal_orthogonal_eq_closure]; exact hL.submodule_topologicalClosure_eq
  rw [← hLcl, Submodule.mem_orthogonal]
  intro u hu
  show ⟪u, avg μ S B hSb hSc w hw m⟫_ℂ = 0
  rw [avg_apply, ← integral_inner (integrable_integrand μ S B hSb hSc w hw m)]
  have : ∀ c, ⟪u, w c • S c m⟫_ℂ = 0 := fun c => by
    rw [inner_smul_right]
    have hcm : S c m ∈ L := hLs c ⟨m, hm, rfl⟩
    rw [Submodule.inner_left_of_mem_orthogonal hcm hu, mul_zero]
  simp [this]

end AvgOp

theorem solution
    {C : Type*} [Group C] [TopologicalSpace C] [IsTopologicalGroup C] [CompactSpace C] [T2Space C]
    [MeasurableSpace C] [BorelSpace C] (μ : Measure C) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : C →* (H →L[ℂ] H)) (B : ℝ) (hSb : ∀ c : C, ‖S c‖ ≤ B) (hSc : ∀ v : H, Continuous fun c : C => S c v)
    (w : C → ℂ) (hw : Continuous w) :
    ∃ A : H →L[ℂ] H,
      (∀ v : H, A v = ∫ c, (w c) • (S c v) ∂μ) ∧
      (∀ M : ℝ, (∀ c : C, ‖w c‖ ≤ M) → ∀ v : H, ‖A v‖ ≤ M * B * ‖v‖) ∧
      (∀ L : Submodule ℂ H, IsClosed (L : Set H) →
        (∀ c : C, L.map (S c : H →ₗ[ℂ] H) ≤ L) → L.map (A : H →ₗ[ℂ] H) ≤ L) ∧
      (∀ T : H →L[ℂ] H, (∀ c : C, T.comp (S c) = (S c).comp T) → T.comp A = A.comp T)  := by
  refine ⟨AvgOp.avg μ S B hSb hSc w hw, fun v => rfl, fun M hM v => AvgOp.norm_integral_le μ S B hSb hSc w hw M hM v,
    fun L hL hLs => AvgOp.map_le μ S B hSb hSc w hw L hL hLs, fun T hT => AvgOp.comm μ S B hSb hSc w hw T hT⟩

end S_ContinuousLinearMap_exists_forall_apply_eq_integral_smul_apply_of_forall_norm_le_of_continuous
end P2MW
export P2MW.S_ContinuousLinearMap_exists_forall_apply_eq_integral_smul_apply_of_forall_norm_le_of_continuous (solution)
