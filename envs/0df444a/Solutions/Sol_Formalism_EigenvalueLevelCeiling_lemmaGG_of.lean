-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.lemmaGG_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:53:28.674004+00:00
-- url     : https://prove2.me/submissions/cc9094d8-cd76-49a8-8829-e0c4bb4e4484

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_OrthogonalityOfMackey
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LemmaGG
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_gg_core
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ggE_apply
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ggE_mem_eig
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ggE_eig
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ggE_stable
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_mapsTo_locP
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_gg_lix_of_le
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_gg_isLatIn_cut
import Theorems.Thm_Formalism_DivisionValues_valuation_basic_properties
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_orthogonality_of_mackey
import Theorems.Thm_Formalism_HermitianLatticesTheory_indexBasic_denom
import Theorems.Thm_Formalism_HermitianLatticesTheory_indexBasic_finLen
import Theorems.Thm_Formalism_HermitianLatticesTheory_indexBasic_locLen_self
import Theorems.Thm_Formalism_HermitianLatticesTheory_indexBasic_locS_top


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution (hSc : IdxScaleIn) : LemmaGG := by
  intro K _ _ _ Z _ _ _ _ _ w P _ _ ρ U ψ hMk B B' hB hB' hle hst hst'
  classical
  have : Fintype P := Fintype.ofFinite P
  have : Fintype U := Fintype.ofFinite U
  have : Fintype (P ⧸ U) := Fintype.ofFinite _
  obtain ⟨W, hW⟩ : ∃ W, W = eig ρ U ψ := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N, N = Fintype.card U := ⟨_, rfl⟩
  have hN0 : N ≠ 0 := by rw [hN]; exact Fintype.card_ne_zero
  have hNK : (N : K) ≠ 0 := Nat.cast_ne_zero.mpr hN0
  rw [Nat.card_eq_fintype_card, ← hN, ← hW]
  have hidx : U.index = Fintype.card (P ⧸ U) := by
    unfold Subgroup.index
    rw [Nat.card_eq_fintype_card]
  rw [hidx]
  let rep : P ⧸ U → P := Quotient.out
  have hrep : ∀ i j, (rep i)⁻¹ * rep j ∈ U → i = j := by
    intro i j h
    have := QuotientGroup.eq.mpr h
    rwa [QuotientGroup.out_eq', QuotientGroup.out_eq'] at this
  have hkey : ∀ i j, ∀ a ∈ W, ggE ρ U ψ (ρ (rep i)⁻¹ (ρ (rep j) a)) =
      if i = j then (N : K) • a else 0 := by
    intro i j a ha
    have e0 : ρ (rep i)⁻¹ (ρ (rep j) a) = ρ ((rep i)⁻¹ * rep j) a := by
      rw [map_mul, Module.End.mul_apply]
    rw [e0]
    split_ifs with hij
    · rw [hij, inv_mul_cancel, map_one, Module.End.one_apply, hN]
      exact ggE_eig ρ U ψ hMk a (hW ▸ ha)
    · rw [ggE_apply]
      exact orthogonality_of_mackey K Z P ρ U ψ hMk _ (fun h => hij (hrep i j h)) a (hW ▸ ha)

  have hdim : Fintype.card (P ⧸ U) * finrank K W ≤ finrank K Z := by
    let S : ((P ⧸ U) → W) →ₗ[K] Z := ∑ i, (ρ (rep i)) ∘ₗ W.subtype ∘ₗ LinearMap.proj i
    have hS : Function.Injective S := by
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro f hf
      rw [LinearMap.mem_ker] at hf
      rw [Submodule.mem_bot]
      ext i
      have h1 : ggE ρ U ψ (ρ (rep i)⁻¹ (S f)) = (N : K) • (f i : Z) := by
        simp only [S, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
          Submodule.subtype_apply, map_sum]
        rw [Finset.sum_congr rfl (fun j _ => hkey i j _ (f j).2)]
        simp
      rw [hf, map_zero, map_zero] at h1
      have := (smul_eq_zero.mp h1.symm).resolve_left hNK
      simpa using this
    have := LinearMap.finrank_le_finrank_of_injective hS
    rw [Module.finrank_pi_fintype] at this
    simpa using this

  have hp : w.asIdeal.IsPrime := w.isPrime
  let s : P ⧸ U → Z →ₗ[𝓞 K] Z := fun i => (ρ (rep i)).restrictScalars (𝓞 K)
  let t : P ⧸ U → Z →ₗ[𝓞 K] Z := fun i => (ggE ρ U ψ ∘ₗ ρ (rep i)⁻¹).restrictScalars (𝓞 K)
  have hlocW : ∀ L : Submodule (𝓞 K) Z, ∀ a ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (cut W L), a ∈ W := by
    rintro L a ⟨σ, hσ, ha⟩
    have hσ0 : (σ : K) ≠ 0 := by
      have : σ ≠ 0 := fun h => hσ (by rw [h]; exact w.asIdeal.zero_mem)
      exact_mod_cast this
    have e : a = (σ : K)⁻¹ • (σ • a) := by
      rw [← algebraMap_smul K σ a, smul_smul, inv_mul_cancel₀ hσ0, one_smul]
    rw [e]
    exact W.smul_mem _ ha.2
  have hcore := gg_core (N : 𝓞 K) (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (cut W B))
    (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (cut W B')) (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (sc (N : K) (cut W B)))
    (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal B) (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal B') s t
    (fun i => mapsTo_locP _ _ _ _ (fun x hx => hst _ ⟨x, hx.1, rfl⟩))
    (fun i => mapsTo_locP _ _ _ _ (fun x hx => hst' _ ⟨x, hx.1, rfl⟩))
    (fun i => mapsTo_locP _ _ _ _ (fun x hx =>
      ⟨ggE_stable ρ U ψ B hst _ (hst _ ⟨x, hx, rfl⟩), hW ▸ ggE_mem_eig ρ U ψ hMk _⟩))
    (fun i => mapsTo_locP _ _ _ _ (fun x hx =>
      ⟨ggE_stable ρ U ψ B' hst' _ (hst' _ ⟨x, hx, rfl⟩), hW ▸ ggE_mem_eig ρ U ψ hMk _⟩))
    (by
      intro i j a ha
      have := hkey i j a (hlocW B a ha)
      have e : ((N : 𝓞 K)) • a = (N : K) • a := by
        rw [← algebraMap_smul K (N : 𝓞 K) a, map_natCast]
      rw [e]
      exact this)
    (by
      rintro c ⟨σ, hσ, hc⟩ -
      obtain ⟨y, hy, hyc⟩ := hc
      have hσ0 : (σ : K) ≠ 0 := by
        have : σ ≠ 0 := fun h => hσ (by rw [h]; exact w.asIdeal.zero_mem)
        exact_mod_cast this
      refine ⟨(σ : K)⁻¹ • y, ⟨σ, hσ, ?_⟩, ?_⟩
      · rw [← algebraMap_smul K σ, smul_smul, mul_inv_cancel₀ hσ0, one_smul]
        exact hy
      · have hyc' : (N : K) • y = (σ : K) • c := by
          rw [algebraMap_smul]
          simpa using hyc
        rw [← algebraMap_smul K (N : 𝓞 K), map_natCast, smul_comm, hyc', smul_smul,
          inv_mul_cancel₀ hσ0, one_smul])

  have hA := gg_isLatIn_cut W B hB
  obtain ⟨d, hd, hdB⟩ : ∃ d ∈ nonZeroDivisors (𝓞 K), ∀ x ∈ B, d • x ∈ B' := by
    apply Formalism.HermitianLatticesTheory.indexBasic_denom _ B B' hB.1
    rw [Formalism.HermitianLatticesTheory.indexBasic_locS_top (K := K) B' hB'.2]
    exact le_top
  have f1 := Module.length_ne_top_iff.mpr
    (Formalism.HermitianLatticesTheory.indexBasic_finLen w.asIdeal B B' hB.1 hd hdB)
  have f2 := Module.length_ne_top_iff.mpr
    (Formalism.HermitianLatticesTheory.indexBasic_finLen w.asIdeal (cut W B) (cut W B') hA.1 hd (fun x hx =>
      ⟨hdB x hx.1, (W.restrictScalars (𝓞 K)).smul_mem d hx.2⟩))
  have hNnz : (N : 𝓞 K) ∈ nonZeroDivisors (𝓞 K) :=
    mem_nonZeroDivisors_of_ne_zero (Nat.cast_ne_zero.mpr hN0)
  have eN : ∀ x : Z, (N : 𝓞 K) • x = (N : K) • x := by
    intro x
    rw [← algebraMap_smul K (N : 𝓞 K) x, map_natCast]
  have f3 := Module.length_ne_top_iff.mpr
    (Formalism.HermitianLatticesTheory.indexBasic_finLen w.asIdeal (cut W B) (sc (N : K) (cut W B)) hA.1 hNnz
      (fun x hx => ⟨x, hx, by rw [eN]; rfl⟩))
  have hscle : sc (N : K) (cut W B) ≤ cut W B := by
    rintro x ⟨y, hy, rfl⟩
    have : ((N : K) • (LinearMap.id : Z →ₗ[K] Z)).restrictScalars (𝓞 K) y = (N : 𝓞 K) • y := by
      rw [eN]; rfl
    rw [this]
    exact (cut W B).smul_mem _ hy
  obtain ⟨-, hsc⟩ := hSc K Z w W (cut W B) (cut W B) hA hA (N : K) hNK
  rw [gg_lix_of_le w _ _ hscle, gg_lix_of_le w _ _ le_rfl, Formalism.HermitianLatticesTheory.indexBasic_locLen_self] at hsc
  have hcutle : cut W B' ≤ cut W B := inf_le_inf_right _ hle
  rw [gg_lix_of_le w (cut W B) (cut W B') hcutle, gg_lix_of_le w _ _ hle]
  unfold Formalism.HermitianLatticesTheory.locLen at hsc ⊢
  revert hcore hsc
  generalize Module.length (𝓞 K) (↥(Formalism.HermitianLatticesTheory.localization₂ w.asIdeal B) ⧸
    (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal B').comap (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal B).subtype) = l1 at f1 ⊢
  generalize Module.length (𝓞 K) (↥(Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (cut W B)) ⧸
    (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (cut W B')).comap (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (cut W B)).subtype) = l2 at f2 ⊢
  generalize Module.length (𝓞 K) (↥(Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (cut W B)) ⧸
    (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (sc (N : K) (cut W B))).comap
      (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (cut W B)).subtype) = l3 at f3 ⊢
  intro hcore hsc
  lift l1 to ℕ using f1
  lift l2 to ℕ using f2
  lift l3 to ℕ using f3
  simp only [ENat.toNat_natCast] at hsc ⊢
  have hc' : Fintype.card (P ⧸ U) * l2 ≤ l1 + Fintype.card (P ⧸ U) * l3 := by exact_mod_cast hcore
  have hv : 0 ≤ vw w (N : K) := by
    have := (valuation_basic_properties K w).2.2.2.2.2.2 (N : 𝓞 K)
    simpa using this
  have hc'' : (Fintype.card (P ⧸ U) : ℤ) * l2 ≤ l1 + (Fintype.card (P ⧸ U) : ℤ) * l3 := by
    exact_mod_cast hc'
  have hdim' : (Fintype.card (P ⧸ U) : ℤ) * (finrank K W : ℤ) ≤ (finrank K Z : ℤ) := by
    exact_mod_cast hdim
  rw [hsc, Nat.cast_zero, zero_add, ← mul_assoc] at hc''
  have := mul_le_mul_of_nonneg_right hdim' hv
  linarith
end Formalism.EigenvalueLevelCeiling
