-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.scale_sandwich_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:12:45.163143+00:00
-- url     : https://prove2.me/submissions/dd570887-e5b9-4ba7-bbfa-b0b4b2ce913e

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementL
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MapScale
import Theorems.Thm_Formalism_BranchingDeterminantCap_ms_htMap_nat
import Theorems.Thm_Formalism_BranchingDeterminantCap_map_slope_mu
import Theorems.Thm_Formalism_HN_slope_inequality_mean


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
open Formalism.HN
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution : ScaleSandwich := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X hX A B n hA hA0 hn hBA hnA
  have hne : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    apply hA0
    rw [eq_bot_iff]
    intro x _
    have : x = 0 := b.repr.injective (by ext i; exact (h.false i).elim)
    exact (Submodule.mem_bot _).2 this
  have hBfg : B.FG := by
    have : IsNoetherian (𝓞 K) A := isNoetherian_of_fg_of_noetherian A hA
    exact (isNoetherian_submodule.1 this) B hBA
  set φ : V →ₗ[K] V := (n : K) • (LinearMap.id : V →ₗ[K] V) with hφ
  have hφx : ∀ x, φ x = (n : 𝓞 K) • x := by
    intro x
    simp [hφ, Nat.cast_smul_eq_nsmul]
  have hnK : (n : K) ≠ 0 := by exact_mod_cast hn.ne'
  have hinj : Function.Injective φ := by
    intro x y hxy
    simp only [hφ, LinearMap.smul_apply, LinearMap.id_apply] at hxy
    exact smul_right_injective V hnK hxy
  have hmap : A.map (φ.restrictScalars (𝓞 K)) ≤ B := by
    rintro _ ⟨x, hx, rfl⟩
    show φ x ∈ B
    rw [hφx]
    exact hnA x hx
  have hmap0 : A.map (φ.restrictScalars (𝓞 K)) ≠ ⊥ := by
    intro h
    apply hA0
    rw [eq_bot_iff]
    intro x hx
    have h1 : φ x ∈ A.map (φ.restrictScalars (𝓞 K)) := ⟨x, hx, rfl⟩
    rw [h, Submodule.mem_bot] at h1
    exact (Submodule.mem_bot _).2 (hinj (by rw [h1, map_zero]))
  have hB0 : B ≠ ⊥ := fun h => hmap0 (le_bot_iff.mp (h ▸ hmap))
  have hrk : rkK B = rkK A := by
    have hspan : Submodule.span K (B : Set V) = Submodule.span K (A : Set V) := by
      apply le_antisymm (Submodule.span_mono hBA)
      rw [Submodule.span_le]
      intro x hx
      have h1 : (n : K) • x ∈ Submodule.span K (B : Set V) := by
        apply Submodule.subset_span
        have := hnA x hx
        rwa [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul K] at this
      have h2 := Submodule.smul_mem _ ((n : K)⁻¹) h1
      rwa [smul_smul, inv_mul_cancel₀ hnK, one_smul] at h2
    unfold rkK
    rw [hspan]
  have hht := ms_htMap_nat b X hX n
  have hht1 : htMap b X b X (LinearMap.id : V →ₗ[K] V) = 0 := by
    have := ms_htMap_nat b X hX 1
    simpa using this
  have hmapid : B.map ((LinearMap.id : V →ₗ[K] V).restrictScalars (𝓞 K)) = B := by
    ext x
    simp
  refine ⟨hrk, ?_, ?_, ?_, ?_⟩
  · have := map_slope_mu K V ι V ι b X b X hX hX LinearMap.id B A hBfg hA hB0
      (Function.injective_id.injOn) (by rw [hmapid]; exact hBA) hrk.symm
    rw [hht1] at this
    linarith
  · have := map_slope_mu K V ι V ι b X b X hX hX φ A B hA hBfg hA0 hinj.injOn hmap hrk
    rw [hht] at this
    exact this
  · have := ((slope_inequality_mean K V ι V ι b X b X hX hX LinearMap.id B hBfg
      (by rw [hmapid]; exact hB0)).2 A hA (by rw [hmapid]; exact hBA)).2 Function.injective_id.injOn
    rw [hht1] at this
    linarith
  · have := ((slope_inequality_mean K V ι V ι b X b X hX hX φ A hA hmap0).2 B hBfg hmap).2 hinj.injOn
    rw [hht] at this
    exact this
end Formalism.BranchingDeterminantCap
