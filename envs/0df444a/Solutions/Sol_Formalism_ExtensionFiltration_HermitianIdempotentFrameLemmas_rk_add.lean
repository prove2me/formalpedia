-- Prove2me | solution 1 for Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.rk_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:51:39.264925+00:00
-- url     : https://prove2.me/submissions/6182dec3-69f8-4540-98bf-038ccad117a1

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_MuMaxMinkowski
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_GoodBadCut
import Theorems.Thm_Formalism_ExtensionFiltration_HermitianIdempotentFrameLemmas_idem_apply
import Theorems.Thm_Formalism_ExtensionFiltration_HermitianIdempotentFrameLemmas_cut_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.ExtensionFiltration
open Formalism.HN
open Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas
theorem _root_.solution (b : Basis ι K V) (e : V →ₗ[K] V) (g : ℕ) (N : Submodule (𝓞 K) V) (hg : 1 ≤ g)
    (hee : e ∘ₗ e = e) (hint : ∀ x ∈ N, (g : K) • e x ∈ N) :
    rkK (N ⊓ (LinearMap.range e).restrictScalars (𝓞 K)) +
      rkK (N ⊓ (LinearMap.ker e).restrictScalars (𝓞 K)) = rkK N := by
  haveI : FiniteDimensional K V := Module.Finite.of_basis b
  have hg0 : (g : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hinv : ∀ y : V, (g : K)⁻¹ • ((g : K) • y) = y := fun y => by
    rw [smul_smul, inv_mul_cancel₀ hg0, one_smul]
  set S : Submodule K V := Submodule.span K (N : Set V) with hS
  have hNS : ∀ x ∈ N, x ∈ S := fun x hx => Submodule.subset_span hx
  have heS : ∀ x ∈ S, e x ∈ S := by
    have hle : S.map e ≤ S := by
      rw [hS, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      have h1 : (g : K) • e x ∈ S := hNS _ (hint x hx)
      have h2 := S.smul_mem ((g : K)⁻¹) h1
      rw [hinv] at h2
      exact h2
    intro x hx
    exact hle ⟨x, hx, rfl⟩
  have hA : Submodule.span K ((N ⊓ (LinearMap.range e).restrictScalars (𝓞 K) : Submodule (𝓞 K) V) : Set V) =
      S.map e := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro y hy
      obtain ⟨hyN, hyr⟩ := hy
      obtain ⟨z, hz⟩ := LinearMap.mem_range.mp hyr
      refine ⟨y, hNS y hyN, ?_⟩
      rw [← hz, idem_apply e hee z]
    · rw [hS, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      have h1 : (g : K) • e x ∈ (N ⊓ (LinearMap.range e).restrictScalars (𝓞 K) : Submodule (𝓞 K) V) :=
        Submodule.mem_inf.mpr ⟨hint x hx, LinearMap.mem_range.mpr ⟨(g : K) • x, map_smul e _ x⟩⟩
      have h3 : (g : K) • e x ∈ Submodule.span K ((N ⊓ (LinearMap.range e).restrictScalars (𝓞 K) :
          Submodule (𝓞 K) V) : Set V) := Submodule.subset_span h1
      have h2 := Submodule.smul_mem _ ((g : K)⁻¹) h3
      rw [hinv] at h2
      exact h2
  have hB : Submodule.span K ((N ⊓ (LinearMap.ker e).restrictScalars (𝓞 K) : Submodule (𝓞 K) V) : Set V) =
      S.map (LinearMap.id - e : V →ₗ[K] V) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro y hy
      obtain ⟨hyN, hyk⟩ := hy
      have hy0 : e y = 0 := hyk
      refine ⟨y, hNS y hyN, ?_⟩
      show y - e y = y
      rw [hy0, sub_zero]
    · rw [hS, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      have h1 := cut_mem e g N hee hint hx
      have h3 : (g : K) • (x - e x) ∈ Submodule.span K ((N ⊓ (LinearMap.ker e).restrictScalars (𝓞 K) :
          Submodule (𝓞 K) V) : Set V) := Submodule.subset_span h1
      have h2 := Submodule.smul_mem _ ((g : K)⁻¹) h3
      rw [hinv] at h2
      exact h2
  have hsup : S.map e ⊔ S.map (LinearMap.id - e : V →ₗ[K] V) = S := by
    apply le_antisymm
    · apply sup_le
      · rintro _ ⟨x, hx, rfl⟩
        exact heS x hx
      · rintro _ ⟨x, hx, rfl⟩
        exact S.sub_mem hx (heS x hx)
    · intro x hx
      have h1 : e x + (LinearMap.id - e : V →ₗ[K] V) x ∈ S.map e ⊔ S.map (LinearMap.id - e : V →ₗ[K] V) :=
        Submodule.add_mem_sup ⟨x, hx, rfl⟩ ⟨x, hx, rfl⟩
      have h2 : e x + (LinearMap.id - e : V →ₗ[K] V) x = x := by
        simp
      rw [h2] at h1
      exact h1
  have hinf : S.map e ⊓ S.map (LinearMap.id - e : V →ₗ[K] V) = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨⟨a, ha, hay⟩, ⟨c, hc, hcy⟩⟩
    have h1 : e y = y := by rw [← hay, idem_apply e hee a]
    have h2 : e y = 0 := by
      rw [← hcy]
      show e (c - e c) = 0
      rw [map_sub, idem_apply e hee c, sub_self]
    exact (Submodule.mem_bot K).mpr (h1.symm.trans h2)
  have key := Submodule.finrank_sup_add_finrank_inf_eq (S.map e) (S.map (LinearMap.id - e : V →ₗ[K] V))
  rw [hsup, hinf, finrank_bot, add_zero] at key
  unfold rkK
  rw [hA, hB]
  exact key.symm
end Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas
