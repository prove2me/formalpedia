-- Prove2me | solution 1 for Formalism.L2.SG.Pf.NcS.LT.GLP.fix_tuple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:32:36.27199+00:00
-- url     : https://prove2.me/submissions/725f42c3-3cb4-4ebe-b85c-a86170279505

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_NcSGLP
import Theorems.Thm_Formalism_L2_SG_Pf_NcS_LT_GLP_pi_surj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.L2.SG.Pf.NcS.LT.GLP
variable {K : Type*} [Field K]
private theorem eq_zero_of_mem_of_disjoint {V : Type*} [AddCommGroup V] [Module K V] {S T : Submodule K V}
    (h : Disjoint S T) {v : V} (hS : v ∈ S) (hT : v ∈ T) : v = 0 :=
  (Submodule.mem_bot K).mp (h.le_bot (Submodule.mem_inf.mpr ⟨hS, hT⟩))
private theorem exists_not_mem_of_ne_top_of_ne_top {V : Type*} [AddCommGroup V] [Module K V]
    (U W : Submodule K V) (hU : U ≠ ⊤) (hW : W ≠ ⊤) : ∃ v, v ∉ U ∧ v ∉ W := by
  obtain ⟨u, hu⟩ : ∃ u, u ∉ U := by
    by_contra hcon
    push_neg at hcon
    exact hU (Submodule.eq_top_iff'.mpr hcon)
  obtain ⟨w, hw⟩ : ∃ w, w ∉ W := by
    by_contra hcon
    push_neg at hcon
    exact hW (Submodule.eq_top_iff'.mpr hcon)
  by_cases huW : u ∈ W
  · by_cases hwU : w ∈ U
    · refine ⟨u + w, fun h => hu ?_, fun h => hw ?_⟩
      · simpa using U.sub_mem h hwU
      · simpa using W.sub_mem h huW
    · exact ⟨w, hwU, hw⟩
  · exact ⟨u, hu, huW⟩
private theorem exists_common_complement_of_finrank_eq {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (n : ℕ) : ∀ U W : Submodule K V, Module.finrank K U = Module.finrank K W →
      Module.finrank K V = Module.finrank K U + n →
      ∃ T : Submodule K V, Disjoint T U ∧ Disjoint T W ∧
        Module.finrank K V = Module.finrank K U + Module.finrank K T := by
  induction n with
  | zero =>
    intro U W _ hn
    refine ⟨⊥, disjoint_bot_left, disjoint_bot_left, ?_⟩
    rw [finrank_bot]
    omega
  | succ n ih =>
    intro U W hUW hn
    have hU : U ≠ ⊤ := by
      rintro rfl
      rw [finrank_top] at hn
      omega
    have hW : W ≠ ⊤ := by
      rintro rfl
      rw [finrank_top] at hUW
      omega
    obtain ⟨v, hvU, hvW⟩ := exists_not_mem_of_ne_top_of_ne_top U W hU hW
    have hv0 : v ≠ 0 := fun h => hvU (by rw [h]; exact U.zero_mem)
    have hback : ∀ S : Submodule K V, ∀ c : K, c ≠ 0 → c • v ∈ S → v ∈ S := by
      intro S c hc hcv
      have hm := S.smul_mem c⁻¹ hcv
      first
      | (rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at hm)
      | simpa [hc] using hm
    have hinf : ∀ S : Submodule K V, v ∉ S → S ⊓ Submodule.span K {v} = ⊥ := by
      intro S hvS
      rw [eq_bot_iff]
      intro z hz
      rw [Submodule.mem_bot]
      obtain ⟨hzS, hzv⟩ := Submodule.mem_inf.mp hz
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hzv
      by_cases hc : c = 0
      · simp [hc]
      · exact (hvS (hback S c hc hzS)).elim
    have key : ∀ S : Submodule K V, v ∉ S →
        Module.finrank K ↥(S ⊔ Submodule.span K {v}) = Module.finrank K S + 1 := by
      intro S hvS
      have h := Submodule.finrank_sup_add_finrank_inf_eq S (Submodule.span K {v})
      rw [hinf S hvS, finrank_bot, finrank_span_singleton hv0] at h
      omega
    obtain ⟨T, hTU, hTW, hT⟩ := ih (U ⊔ Submodule.span K {v}) (W ⊔ Submodule.span K {v})
      (by rw [key U hvU, key W hvW, hUW]) (by rw [key U hvU]; omega)
    have hvT : v ∉ T := fun h => hv0 (eq_zero_of_mem_of_disjoint hTU h
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self v)))
    have disj : ∀ S : Submodule K V, v ∉ S → Disjoint T (S ⊔ Submodule.span K {v}) →
        Disjoint (T ⊔ Submodule.span K {v}) S := by
      intro S hvS hTS
      rw [disjoint_iff, eq_bot_iff]
      intro z hz
      rw [Submodule.mem_bot]
      obtain ⟨hz1, hzS⟩ := Submodule.mem_inf.mp hz
      obtain ⟨t, ht, w', hw', rfl⟩ := Submodule.mem_sup.mp hz1
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw'
      have ht0 : t = 0 := by
        refine eq_zero_of_mem_of_disjoint hTS ht ?_
        have htt : t = (t + c • v) - c • v := by abel
        rw [htt]
        exact Submodule.sub_mem _ (Submodule.mem_sup_left hzS)
          (Submodule.mem_sup_right (Submodule.smul_mem _ c (Submodule.mem_span_singleton_self v)))
      subst ht0
      by_cases hc : c = 0
      · simp [hc]
      · exact (hvS (hback S c hc (by simpa using hzS))).elim
    refine ⟨T ⊔ Submodule.span K {v}, disj U hvU hTU, disj W hvW hTW, ?_⟩
    rw [key T hvT]
    rw [key U hvU] at hT
    omega
end Formalism.L2.SG.Pf.NcS.LT.GLP
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.NcS Formalism.L2.SG.Pf.NcS.LT Formalism.L2.SG.Pf.NcS.LT.GLP
variable {K : Type*} [Field K]
namespace Formalism.L2.SG.Pf.NcS.LT.GLP
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {a : ℕ}
    (x : Fin a → V) (hx : LinearIndependent K x) (φ ψ : Fin a → Module.Dual K V)
    (hφ : LinearIndependent K φ) (hψ : LinearIndependent K ψ) (h : ∀ i j, φ i (x j) = ψ i (x j)) :
    ∃ B : V ≃ₗ[K] V, (∀ j, B (x j) = x j) ∧ ∀ i v, ψ i (B v) = φ i v := by
  let Φ : V →ₗ[K] (Fin a → K) := LinearMap.pi φ
  let Ψ : V →ₗ[K] (Fin a → K) := LinearMap.pi ψ
  have hΦ : Function.Surjective Φ := pi_surj φ hφ
  have hΨ : Function.Surjective Ψ := pi_surj ψ hψ
  have eΦ := LinearMap.finrank_range_add_finrank_ker Φ
  have eΨ := LinearMap.finrank_range_add_finrank_ker Ψ
  rw [LinearMap.range_eq_top.mpr hΦ, finrank_top] at eΦ
  rw [LinearMap.range_eq_top.mpr hΨ, finrank_top] at eΨ
  obtain ⟨T, hTΦ, hTΨ, hT⟩ := exists_common_complement_of_finrank_eq
    (Module.finrank K V - Module.finrank K (LinearMap.ker Φ)) (LinearMap.ker Φ) (LinearMap.ker Ψ)
    (by omega) (by omega)
  have hTdim : Module.finrank K T = Module.finrank K (Fin a → K) := by omega
  let f : T →ₗ[K] (Fin a → K) := Ψ.domRestrict T
  have hfinj : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).mpr fun t ht => ?_
    have h0 : (t : V) = 0 := eq_zero_of_mem_of_disjoint hTΨ t.2 (LinearMap.mem_ker.mpr ht)
    first
    | exact Subtype.ext h0
    | simpa using h0
  have hfsurj : Function.Surjective f := by
    first
    | exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hTdim).mp hfinj
    | exact LinearMap.range_eq_top.mp
        ((LinearMap.ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank hTdim).mp
          (LinearMap.ker_eq_bot.mpr hfinj))
  let eT : T ≃ₗ[K] (Fin a → K) := LinearEquiv.ofBijective f ⟨hfinj, hfsurj⟩
  let s : (Fin a → K) →ₗ[K] V := T.subtype ∘ₗ eT.symm.toLinearMap
  have hs : ∀ t, Ψ (s t) = t := by
    intro t
    have h1 : Ψ (s t) = eT (eT.symm t) := by
      first
      | rfl
      | exact (LinearEquiv.ofBijective_apply f _ (eT.symm t)).symm
    rw [h1, LinearEquiv.apply_symm_apply]
  have hsT : ∀ t, s t ∈ T := fun t => (eT.symm t).2
  let B : V →ₗ[K] V := LinearMap.id + s ∘ₗ (Φ - Ψ)
  have hBv : ∀ v, B v = v + s (Φ v - Ψ v) := by
    intro v
    first
    | rfl
    | simp [B]
  have hΨB : ∀ v, Ψ (B v) = Φ v := by
    intro v
    rw [hBv, map_add, hs]
    abel
  have hBx : ∀ j, B (x j) = x j := by
    intro j
    have hM : Φ (x j) = Ψ (x j) := funext fun i => h i j
    rw [hBv, hM, sub_self, map_zero, add_zero]
  have hinj : Function.Injective B := by
    refine (injective_iff_map_eq_zero B).mpr fun v hv => ?_
    have hΦv : Φ v = 0 := by rw [← hΨB v, hv, map_zero]
    have hvT : v ∈ T := by
      rw [hBv] at hv
      rw [eq_neg_of_add_eq_zero_left hv]
      exact T.neg_mem (hsT _)
    exact eq_zero_of_mem_of_disjoint hTΦ hvT (LinearMap.mem_ker.mpr hΦv)
  refine ⟨LinearEquiv.ofInjectiveEndo B hinj, fun j => ?_, fun i v => ?_⟩
  · first
    | exact hBx j
    | simpa using hBx j
  · first
    | exact congrFun (hΨB v) i
    | simpa using congrFun (hΨB v) i
end Formalism.L2.SG.Pf.NcS.LT.GLP
