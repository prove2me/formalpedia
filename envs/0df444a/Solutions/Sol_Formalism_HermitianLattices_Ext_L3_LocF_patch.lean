-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LocF.patch
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:21.896855+00:00
-- url     : https://prove2.me/submissions/0abcec72-50b0-4eb4-b240-dfbb6d2df6c2

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_TraceReal
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapIntCastSmul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_mem_locF_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_le_locF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_locF_mono
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_locF_idem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_iInf_locF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_exists_prime_to_part
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_exists_zsmul_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_algebraMap_intCast_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LocF
variable {K F : Type} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K]
variable [StarRing K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.LocF
theorem _root_.solution {L₀ : Submodule (𝓞 K) V} (hL₀ : Submodule.IsLattice K L₀)
    (s : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal})
    (B : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → Submodule (𝓞 K) V)
    (hB : ∀ 𝔭, Submodule.IsLattice K (B 𝔭)) (hBs : ∀ 𝔭 ∉ s, B 𝔭 = L₀) :
    Submodule.IsLattice K (⨅ 𝔭, locF 𝔭.1 (B 𝔭)) ∧
      ∀ 𝔭, locF 𝔭.1 (⨅ 𝔮, locF 𝔮.1 (B 𝔮)) = locF 𝔭.1 (B 𝔭) := by
  classical
  choose n₁ hn₁ hn₁x using fun 𝔭 => exists_zsmul_le (hB 𝔭) hL₀
  choose n₂ hn₂ hn₂x using fun 𝔭 => exists_zsmul_le hL₀ (hB 𝔭)
  obtain ⟨N, hN, hN1, hN2⟩ : ∃ N : ℤ, N ≠ 0 ∧ (∀ 𝔭, ∀ x ∈ B 𝔭, N • x ∈ L₀) ∧
      ∀ 𝔭, ∀ x ∈ L₀, N • x ∈ B 𝔭 := by
    refine ⟨∏ 𝔭 ∈ s, (n₁ 𝔭 * n₂ 𝔭),
      Finset.prod_ne_zero_iff.mpr fun 𝔭 _ => mul_ne_zero (hn₁ 𝔭) (hn₂ 𝔭), ?_, ?_⟩
    · intro 𝔭 x hx
      by_cases h𝔭 : 𝔭 ∈ s
      · obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun 𝔭 => n₁ 𝔭 * n₂ 𝔭) h𝔭
        rw [hm, show n₁ 𝔭 * n₂ 𝔭 * m = (n₂ 𝔭 * m) * n₁ 𝔭 by ring, mul_smul]
        exact zsmul_mem (hn₁x 𝔭 x hx) _
      · rw [hBs 𝔭 h𝔭] at hx
        exact zsmul_mem hx _
    · intro 𝔭 x hx
      by_cases h𝔭 : 𝔭 ∈ s
      · obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun 𝔭 => n₁ 𝔭 * n₂ 𝔭) h𝔭
        rw [hm, show n₁ 𝔭 * n₂ 𝔭 * m = (n₁ 𝔭 * m) * n₂ 𝔭 by ring, mul_smul]
        exact zsmul_mem (hn₂x 𝔭 x hx) _
      · rw [hBs 𝔭 h𝔭]
        exact zsmul_mem hx _
  set Λ : Submodule (𝓞 K) V := ⨅ 𝔭, locF 𝔭.1 (B 𝔭) with hΛ
  have hΛle : ∀ 𝔭, Λ ≤ locF 𝔭.1 (B 𝔭) := fun 𝔭 => iInf_le _ 𝔭
  have h2 : ∀ x ∈ L₀, N • x ∈ Λ := by
    intro x hx
    rw [hΛ, Submodule.mem_iInf]
    exact fun 𝔭 => le_locF 𝔭.1 _ (hN2 𝔭 x hx)
  have h3 : ∀ x ∈ Λ, N • x ∈ L₀ := by
    intro x hx
    rw [← iInf_locF (F := F) L₀, Submodule.mem_iInf]
    intro 𝔭
    obtain ⟨t, ht, htx⟩ := (mem_locF_iff 𝔭.2.isPrime _ x).mp (hΛle 𝔭 hx)
    refine (mem_locF_iff 𝔭.2.isPrime _ _).mpr ⟨t, ht, ?_⟩
    rw [smul_comm]
    exact hN1 𝔭 _ htx
  have hNK : (N : K) ≠ 0 := by exact_mod_cast hN
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · let φ : V →ₗ[𝓞 K] V := N • LinearMap.id
    have hφ : Function.Injective φ := by
      intro x y hxy
      have : N • x = N • y := hxy
      rw [← Int.cast_smul_eq_zsmul K, ← Int.cast_smul_eq_zsmul K] at this
      exact smul_right_injective V hNK this
    apply Submodule.fg_of_fg_map_injective φ hφ
    have hle : Λ.map φ ≤ L₀ := by
      rintro _ ⟨x, hx, rfl⟩
      exact h3 x hx
    exact hL₀.fg.of_le hle
  · rw [eq_top_iff, ← hL₀.span_eq_top, Submodule.span_le]
    intro x hx
    have h4 : (N : K)⁻¹ • (N • x) ∈ Submodule.span K (Λ : Set V) :=
      Submodule.smul_mem _ _ (Submodule.subset_span (h2 x hx))
    rwa [← Int.cast_smul_eq_zsmul K, smul_smul, inv_mul_cancel₀ hNK, one_smul] at h4
  · intro 𝔭
    apply le_antisymm
    · calc locF 𝔭.1 Λ ≤ locF 𝔭.1 (locF 𝔭.1 (B 𝔭)) := locF_mono _ (hΛle 𝔭)
        _ = _ := locF_idem _ _
    · intro x hx
      obtain ⟨t₀, ht₀, hy⟩ := (mem_locF_iff 𝔭.2.isPrime _ x).mp hx
      have hc : ((N * N : ℤ) : 𝓞 F) ≠ 0 := by
        exact_mod_cast mul_ne_zero hN hN
      obtain ⟨t, ht, hq⟩ := exists_prime_to_part hc 𝔭.2
      refine (mem_locF_iff 𝔭.2.isPrime _ x).mpr
        ⟨t * t₀, fun h => (𝔭.2.isPrime.mem_or_mem h).elim ht ht₀, ?_⟩
      rw [map_mul, mul_smul]
      generalize algebraMap (𝓞 F) (𝓞 K) t₀ • x = y at hy
      have hcy : (N * N) • y ∈ Λ := by
        rw [mul_smul]
        exact h2 _ (hN1 𝔭 y hy)
      rw [hΛ, Submodule.mem_iInf]
      intro 𝔮
      by_cases hqp : 𝔮 = 𝔭
      · rw [hqp]
        exact Submodule.smul_mem _ _ (le_locF _ _ hy)
      · obtain ⟨u, hu, d, hd⟩ := hq 𝔮.1 𝔮.2 (fun h => hqp (Subtype.ext h))
        rw [← locF_idem]
        refine (mem_locF_iff 𝔮.2.isPrime _ _).mpr ⟨u, hu, ?_⟩
        rw [← mul_smul, ← map_mul, hd, mul_comm, map_mul, mul_smul, algebraMap_intCast_smul]
        exact Submodule.smul_mem _ _ (hΛle 𝔮 hcy)
end Formalism.HermitianLattices.Ext.L3.LocF
