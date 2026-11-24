-- Prove2me | solution 1 for Formalism.MainNotions.FormalGroupSystem.Pf.descent_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:06:18.087233+00:00
-- url     : https://prove2.me/submissions/afe70d7f-f730-4eba-8f4f-b59337a7fccf

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MultisetValuation_DescentCore
import Theorems.Thm_Formalism_MainNotions_FormalGroupSystem_Pf_pivot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.MainNotions.FormalGroupSystem.Pf
open Finset
private theorem coeff_mem_range_algebraMap_of_linearIndependent {K Kc V Vc M : Type*} [Field K] [Field Kc] [Algebra K Kc]
    [AddCommGroup V] [Module K V] [AddCommGroup Vc] [Module Kc Vc]
    (ι : V →+ Vc) (hιs : ∀ (c : K) (v : V), ι (c • v) = algebraMap K Kc c • ι v)
    (π : M → V →ₗ[K] K) (πc : M → Vc →ₗ[Kc] Kc) (hπ : ∀ m v, πc m (ι v) = algebraMap K Kc (π m v))
    (hsep : ∀ v : V, (∀ m, π m v = 0) → v = 0) {κ : Type*} (s : Finset κ) (z : κ → V)
    (hind : ∀ w : s → K, ∑ k : s, w k • z k = 0 → w = 0)
    (a : κ → Kc) (y : V) (hy : ι y = ∑ k ∈ s, a k • ι (z k)) (k0 : s) :
    a k0 ∈ Set.range (algebraMap K Kc) := by
  classical
  let T : (s → K) →ₗ[K] V :=
    { toFun := fun w => ∑ k : s, w k • z k
      map_add' := fun w w' => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c w => by simp [Finset.smul_sum, smul_smul] }
  let φ : M → Module.Dual K (s → K) := fun m => (π m).comp T
  have hspan : Submodule.span K (Set.range φ) = ⊤ := by
    have h1 : (Submodule.span K (Set.range φ)).dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro w hw
      rw [Submodule.mem_dualCoannihilator] at hw
      have hT : T w = 0 := hsep _ (fun m => hw (φ m) (Submodule.subset_span ⟨m, rfl⟩))
      simpa using hind w hT
    have h2 := Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span K (Set.range φ))
    rw [h1, Submodule.dualAnnihilator_bot] at h2
    exact h2.symm
  have hmem : (LinearMap.proj k0 : (s → K) →ₗ[K] K) ∈ Submodule.span K (Set.range φ) := by
    rw [hspan]; exact Submodule.mem_top
  obtain ⟨l, hl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hmem
  have hz : ∀ k : s, (∑ m ∈ l.support, l m * π m (z k)) = if k = k0 then 1 else 0 := by
    intro k
    have h3 := congrArg (fun f : Module.Dual K (s → K) => f (Pi.single k 1)) hl
    have hT : ∀ m, φ m (Pi.single k 1) = π m (z k) := by
      intro m; simp [φ, T, Pi.single_apply, ite_smul]
    simp only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.proj_apply, hT, smul_eq_mul] at h3
    rw [h3, Pi.single_apply]
    simp [eq_comm]
  have hy' : ι y = ∑ k : s, a k • ι (z k) := by
    rw [hy]; exact (Finset.sum_coe_sort s (fun k => a k • ι (z k))).symm
  have e1 : ∀ m, algebraMap K Kc (π m y) = ∑ k : s, a k * algebraMap K Kc (π m (z k)) := by
    intro m; rw [← hπ, hy', map_sum]; simp [hπ]
  refine ⟨∑ m ∈ l.support, l m * π m y, ?_⟩
  rw [map_sum]
  simp only [map_mul, e1, Finset.mul_sum]
  rw [Finset.sum_comm]
  have h4 : ∀ k : s, ∑ m ∈ l.support, algebraMap K Kc (l m) * (a k * algebraMap K Kc (π m (z k))) =
      a k * algebraMap K Kc (if k = k0 then 1 else 0) := by
    intro k
    rw [← hz k, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_mul]; ring
  rw [Finset.sum_congr rfl (fun k _ => h4 k)]
  simp
end Formalism.MainNotions.FormalGroupSystem.Pf
end

set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.FormalGroupSystem.Pf
open Finset
namespace Formalism.MainNotions.FormalGroupSystem.Pf
theorem _root_.solution {K Kc V Vc M : Type*} [Field K] [Field Kc] [Algebra K Kc]
    [AddCommGroup V] [Module K V] [AddCommGroup Vc] [Module Kc Vc]
    (ι : V →+ Vc) (hιs : ∀ (c : K) (v : V), ι (c • v) = algebraMap K Kc c • ι v)
    (π : M → V →ₗ[K] K) (πc : M → Vc →ₗ[Kc] Kc) (hπ : ∀ m v, πc m (ι v) = algebraMap K Kc (π m v))
    (hsep : ∀ v : V, (∀ m, π m v = 0) → v = 0)
    (R : Subring K) (hR : ∀ x : K, x ∈ R ∨ x⁻¹ ∈ R)
    (A : AddSubgroup Kc) (hA : ∀ r ∈ R, ∀ a ∈ A, algebraMap K Kc r * a ∈ A) {κ : Type*} [DecidableEq κ] :
    ∀ (n : ℕ) (s : Finset κ), s.card = n → ∀ (z : κ → V) (a : κ → Kc), (∀ k ∈ s, a k ∈ A) → ∀ y : V,
      ι y = ∑ k ∈ s, a k • ι (z k) →
      ∃ c : κ → K, (∀ k ∈ s, algebraMap K Kc (c k) ∈ A) ∧ y = ∑ k ∈ s, c k • z k := by
  classical
  have hιinj : ∀ v : V, ι v = 0 → v = 0 := fun v hv => hsep v (fun m => by
    have h0 := hπ m v
    rw [hv, map_zero] at h0
    exact (algebraMap K Kc).injective (h0.symm.trans (map_zero _).symm))
  intro n
  induction n with
  | zero =>
    intro s hs z a _ y hy
    rw [Finset.card_eq_zero] at hs
    subst hs
    refine ⟨0, by simp, ?_⟩
    simp only [Finset.sum_empty] at hy ⊢
    exact hιinj y hy
  | succ n ih =>
    intro s hs z a ha y hy
    by_cases hdep : ∃ b : κ → K, ∑ k ∈ s, b k • z k = 0 ∧ ∃ k ∈ s, b k ≠ 0
    · obtain ⟨b, hb0, hbne⟩ := hdep
      obtain ⟨k0, hk0, hbk0, hbR⟩ := pivot R hR b s hbne
      have hzk0 : ι (z k0) = - ∑ k ∈ s.erase k0, algebraMap K Kc (b k / b k0) • ι (z k) := by
        have h1 : ∑ k ∈ s, (b k / b k0) • z k = 0 := by
          simp_rw [div_eq_mul_inv, mul_comm _ (b k0)⁻¹, mul_smul, ← Finset.smul_sum, hb0, smul_zero]
        rw [← Finset.add_sum_erase s _ hk0, div_self hbk0, one_smul] at h1
        rw [eq_neg_of_add_eq_zero_left h1, map_neg, map_sum]
        simp only [hιs]
      have hy' : ι y = ∑ k ∈ s.erase k0,
          (a k - algebraMap K Kc (b k / b k0) * a k0) • ι (z k) := by
        rw [hy, ← Finset.add_sum_erase s _ hk0, hzk0, smul_neg, Finset.smul_sum,
          ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [smul_smul, sub_smul, mul_comm (a k0)]
        abel
      have hcard : (s.erase k0).card = n := by
        rw [Finset.card_erase_of_mem hk0, hs]; rfl
      obtain ⟨c, hcA, hyc⟩ := ih (s.erase k0) hcard z
        (fun k => a k - algebraMap K Kc (b k / b k0) * a k0)
        (fun k hk => A.sub_mem (ha k (Finset.mem_of_mem_erase hk))
          (hA _ (hbR k (Finset.mem_of_mem_erase hk)) _ (ha k0 hk0))) y hy'
      refine ⟨fun k => if k = k0 then 0 else c k, fun k hk => ?_, ?_⟩
      · by_cases hkk : k = k0
        · simp only [hkk, if_true, map_zero]; exact A.zero_mem
        · simp only [hkk, if_false]; exact hcA k (Finset.mem_erase.2 ⟨hkk, hk⟩)
      · rw [← Finset.add_sum_erase s _ hk0, hyc]
        simp only [if_true, zero_smul, zero_add]
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [if_neg (Finset.ne_of_mem_erase hk)]
    · push_neg at hdep
      have hind : ∀ w : s → K, ∑ k : s, w k • z k = 0 → w = 0 := by
        intro w hw
        have h5 := hdep (fun k => if h : k ∈ s then w ⟨k, h⟩ else 0) (by
          rw [← Finset.sum_coe_sort]; simpa using hw)
        funext k
        simpa using h5 k k.2
      have hr : ∀ k (hk : k ∈ s), a k ∈ Set.range (algebraMap K Kc) := fun k hk =>
        coeff_mem_range_algebraMap_of_linearIndependent ι hιs π πc hπ hsep s z hind a y hy ⟨k, hk⟩
      let c : κ → K := fun k => if hk : k ∈ s then (hr k hk).choose else 0
      have hc : ∀ k ∈ s, algebraMap K Kc (c k) = a k := fun k hk => by
        simp only [c, dif_pos hk]; exact (hr k hk).choose_spec
      refine ⟨c, fun k hk => ?_, ?_⟩
      · rw [hc k hk]; exact ha k hk
      · have h6 : ι (y - ∑ k ∈ s, c k • z k) = 0 := by
          rw [map_sub, map_sum, hy, sub_eq_zero]
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [hιs, hc k hk]
        exact sub_eq_zero.1 (hιinj _ h6)
end Formalism.MainNotions.FormalGroupSystem.Pf
