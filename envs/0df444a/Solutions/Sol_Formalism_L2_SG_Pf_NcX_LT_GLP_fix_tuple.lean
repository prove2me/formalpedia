-- Prove2me | solution 1 for Formalism.L2.SG.Pf.NcX.LT.GLP.fix_tuple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:17:42.963717+00:00
-- url     : https://prove2.me/submissions/f8a77600-e4e0-46fc-8315-fdecbb1fa2de

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_NcXGLP
import Theorems.Thm_Formalism_L2_SG_Pf_NcX_LT_GLP_surj_equiv
import Theorems.Thm_Formalism_L2_SG_Pf_NcX_LT_GLP_pi_surj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.NcX Formalism.L2.SG.Pf.NcX.LT Formalism.L2.SG.Pf.NcX.LT.GLP
variable {K : Type*} [Field K]
namespace Formalism.L2.SG.Pf.NcX.LT.GLP
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {a : ℕ}
    (x : Fin a → V) (hx : LinearIndependent K x) (φ ψ : Fin a → Module.Dual K V)
    (hφ : LinearIndependent K φ) (hψ : LinearIndependent K ψ) (h : ∀ i j, φ i (x j) = ψ i (x j)) :
    ∃ B : V ≃ₗ[K] V, (∀ j, B (x j) = x j) ∧ ∀ i v, ψ i (B v) = φ i v := by
  set U := Submodule.span K (Set.range x)
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl U
  set Φ := LinearMap.pi φ
  set Ψ := LinearMap.pi ψ
  have hUeq : Φ ∘ₗ U.subtype = Ψ ∘ₗ U.subtype := by
    apply (Module.Basis.span hx).ext
    intro j
    ext i
    simp [Φ, Ψ, Module.Basis.span_apply, h i j]
  have hUv : ∀ u : U, Φ u = Ψ u := fun u => LinearMap.congr_fun hUeq u
  have hsplit : ∀ v : V, ∃ u ∈ U, ∃ c ∈ C, u + c = v := fun v =>
    Submodule.mem_sup.1 (by rw [hC.sup_eq_top]; exact Submodule.mem_top)
  set R := LinearMap.range (Ψ ∘ₗ U.subtype)
  have hsurj : ∀ Θ : V →ₗ[K] (Fin a → K), Function.Surjective Θ → (∀ u : U, Θ u = Ψ u) →
      Function.Surjective (R.mkQ ∘ₗ Θ ∘ₗ C.subtype) := by
    intro Θ hΘ hΘU w
    obtain ⟨w', rfl⟩ := R.mkQ_surjective w
    obtain ⟨v, rfl⟩ := hΘ w'
    obtain ⟨u, hu, c, hc, rfl⟩ := hsplit v
    refine ⟨⟨c, hc⟩, ?_⟩
    have h0 : R.mkQ (Θ u) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨⟨u, hu⟩, (hΘU ⟨u, hu⟩).symm⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, map_add, h0, zero_add]
  obtain ⟨δ, hδ⟩ := surj_equiv (R.mkQ ∘ₗ Ψ ∘ₗ C.subtype) (R.mkQ ∘ₗ Φ ∘ₗ C.subtype)
    (hsurj Ψ (pi_surj ψ hψ) fun _ => rfl) (hsurj Φ (pi_surj φ hφ) hUv)
  set D : C →ₗ[K] (Fin a → K) := Φ ∘ₗ C.subtype - Ψ ∘ₗ C.subtype ∘ₗ δ.toLinearMap
  have hD : ∀ c, D c ∈ R := by
    intro c
    have e := hδ c
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply] at e
    exact (Submodule.Quotient.eq R).1 e.symm
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective (Ψ ∘ₗ U.subtype).rangeRestrict
    (LinearMap.range_rangeRestrict _)
  set β : C →ₗ[K] U := s ∘ₗ D.codRestrict R hD
  have hβ : ∀ c, Ψ (β c : V) = D c := by
    intro c
    have e := congrArg Subtype.val (LinearMap.congr_fun hs (D.codRestrict R hD c))
    simpa [β] using e
  set P := (Submodule.prodEquivOfIsCompl _ _ hC).symm
  have hP : ∀ (u : U) (c : C), P ((u : V) + c) = (u, c) := by
    intro u c
    have e : (u : V) + c = Submodule.prodEquivOfIsCompl _ _ hC (u, c) :=
      (Submodule.coe_prodEquivOfIsCompl' _ _ hC (u, c)).symm
    rw [e]
    exact LinearEquiv.symm_apply_apply _ _
  set B0 : V →ₗ[K] V := (U.subtype ∘ₗ LinearMap.fst K U C + U.subtype ∘ₗ β ∘ₗ LinearMap.snd K U C +
    C.subtype ∘ₗ δ.toLinearMap ∘ₗ LinearMap.snd K U C) ∘ₗ P.toLinearMap
  have hB0 : ∀ (u : U) (c : C), B0 ((u : V) + c) = (u : V) + (β c : V) + (δ c : V) := by
    intro u c
    simp [B0, hP u c]
  have hinj : Function.Injective B0 := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    obtain ⟨u, hu, c, hc, rfl⟩ := hsplit v
    have e := hB0 ⟨u, hu⟩ ⟨c, hc⟩
    rw [hv] at e
    have hδU : (δ ⟨c, hc⟩ : V) ∈ U := by
      have : (δ ⟨c, hc⟩ : V) = -(u + (β ⟨c, hc⟩ : V)) := eq_neg_of_add_eq_zero_right e.symm
      rw [this]
      exact U.neg_mem (U.add_mem hu (β _).2)
    have h1 : (δ ⟨c, hc⟩ : V) = 0 := Submodule.disjoint_def.1 hC.disjoint _ hδU (δ _).2
    have h2 : (⟨c, hc⟩ : C) = 0 := δ.injective (by rw [map_zero]; exact Subtype.ext h1)
    have hc0 : c = 0 := congrArg Subtype.val h2
    subst hc0
    have hβ0 : (β ⟨0, hc⟩ : V) = 0 := by
      rw [show (⟨0, hc⟩ : C) = 0 from rfl, map_zero]; rfl
    rw [h1, hβ0, add_zero, add_zero] at e
    rw [add_zero]
    exact e.symm
  refine ⟨LinearEquiv.ofInjectiveEndo B0 hinj, fun j => ?_, fun i v => ?_⟩
  · have hxj : x j ∈ U := Submodule.subset_span ⟨j, rfl⟩
    have e := hB0 ⟨x j, hxj⟩ 0
    simp only [map_zero, Submodule.coe_zero, add_zero] at e
    exact e
  · obtain ⟨u, hu, c, hc, rfl⟩ := hsplit v
    have hv : Ψ (B0 (u + c)) = Φ (u + c) := by
      rw [show u + c = ((⟨u, hu⟩ : U) : V) + ((⟨c, hc⟩ : C) : V) from rfl, hB0]
      simp only [map_add, hβ, hUv ⟨u, hu⟩, D, LinearMap.sub_apply, LinearMap.comp_apply,
        Submodule.subtype_apply, LinearEquiv.coe_coe]
      abel
    exact congrFun hv i
end Formalism.L2.SG.Pf.NcX.LT.GLP
