-- Prove2me | solution 1 for Formalism.L2.SG.Pf.NcS.LT.GLP.surj_equiv
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T02:50:00.330605+00:00
-- url     : https://prove2.me/submissions/c577e71f-25a9-46ca-81c6-c5dde919c9c5

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_NcSGLP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.NcS Formalism.L2.SG.Pf.NcS.LT Formalism.L2.SG.Pf.NcS.LT.GLP
variable {K : Type*} [Field K]
theorem _root_.solution {C W : Type*} [AddCommGroup C] [Module K C] [FiniteDimensional K C]
    [AddCommGroup W] [Module K W] (L1 L2 : C →ₗ[K] W) (h1 : Function.Surjective L1)
    (h2 : Function.Surjective L2) : ∃ δ : C ≃ₗ[K] C, ∀ c, L1 (δ c) = L2 c := by
  obtain ⟨s1, hs1⟩ := L1.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 h1)
  obtain ⟨s2, hs2⟩ := L2.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 h2)
  have e1 : ∀ w, L1 (s1 w) = w := fun w => LinearMap.congr_fun hs1 w
  have e2 : ∀ w, L2 (s2 w) = w := fun w => LinearMap.congr_fun hs2 w
  have hdim : Module.finrank K (LinearMap.ker L2) = Module.finrank K (LinearMap.ker L1) := by
    have a := LinearMap.finrank_range_add_finrank_ker L1
    have b := LinearMap.finrank_range_add_finrank_ker L2
    rw [LinearMap.range_eq_top.2 h1] at a
    rw [LinearMap.range_eq_top.2 h2] at b
    omega
  let e : LinearMap.ker L2 ≃ₗ[K] LinearMap.ker L1 := LinearEquiv.ofFinrankEq _ _ hdim
  let π : C →ₗ[K] LinearMap.ker L2 := LinearMap.codRestrict (LinearMap.ker L2) (LinearMap.id - s2 ∘ₗ L2) (by
    intro c; simp [LinearMap.mem_ker, e2])
  let d : C →ₗ[K] C := s1 ∘ₗ L2 + (LinearMap.ker L1).subtype ∘ₗ e.toLinearMap ∘ₗ π
  have hd : ∀ c, L1 (d c) = L2 c := by
    intro c
    show L1 (s1 (L2 c) + (e (π c) : C)) = L2 c
    rw [map_add, e1, LinearMap.mem_ker.1 (e (π c)).2, add_zero]
  have hinj : Function.Injective d := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    have h0 : L2 c = 0 := by rw [← hd c, hc, map_zero]
    have h3 : (e (π c) : C) = 0 := by
      have : s1 (L2 c) + (e (π c) : C) = 0 := hc
      rwa [h0, map_zero, zero_add] at this
    have h4 : π c = 0 := by
      have : e (π c) = 0 := Subtype.ext h3
      exact e.injective (by rw [this, map_zero])
    have h5 : c - s2 (L2 c) = 0 := congrArg Subtype.val h4
    rwa [h0, map_zero, sub_zero] at h5
  exact ⟨LinearEquiv.ofInjectiveEndo d hinj, fun c => hd c⟩

