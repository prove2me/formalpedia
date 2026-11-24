-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.ib_exists_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:53:28.432875+00:00
-- url     : https://prove2.me/submissions/257a83ee-2fea-46d2-8679-df5a92096061

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_DedekindFactorK
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_IdealBasis
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_ib_im_conj_mul
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_ib_mem_range

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
open NumberField Classical
open scoped Pointwise
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
theorem _root_.solution {K : Type} [Field K] [NumberField K] (φ : K →+* ℂ) (a₀ b₀ : ℂ)
    (hab₀ : 0 < ((starRingEnd ℂ) a₀ * b₀).im)
    (h₀ : latI φ ⊤ 1 = AddSubgroup.closure {a₀, b₀}) :
    ∃ B : Module.Basis (Fin 2) ℤ (𝓞 K), (φ.comp (algebraMap (𝓞 K) K)) (B 0) = a₀ ∧
      (φ.comp (algebraMap (𝓞 K) K)) (B 1) = b₀ := by
  obtain ⟨e, he⟩ := ib_mem_range φ a₀ b₀ h₀ a₀ (AddSubgroup.subset_closure (by simp))
  obtain ⟨f, hf⟩ := ib_mem_range φ a₀ b₀ h₀ b₀ (AddSubgroup.subset_closure (by simp))
  set ψ : 𝓞 K →+* ℂ := φ.comp (algebraMap (𝓞 K) K) with hψ
  have hinj : Function.Injective ψ :=
    φ.injective.comp (FaithfulSMul.algebraMap_injective (𝓞 K) K)
  have hli : LinearIndependent ℤ ![e, f] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 : (s : ℂ) * a₀ + (t : ℂ) * b₀ = 0 := by
      have := congrArg ψ hst
      simpa [map_add, map_zsmul, he, hf, zsmul_eq_mul] using this
    rw [ib_im_conj_mul] at hab₀
    have hre := congrArg Complex.re h1
    have him := congrArg Complex.im h1
    simp at hre him
    constructor
    · have : (s : ℝ) * (a₀.re * b₀.im - a₀.im * b₀.re) = 0 := by
        linear_combination b₀.im * hre - b₀.re * him
      exact_mod_cast (mul_eq_zero.mp this).resolve_right hab₀.ne'
    · have : (t : ℝ) * (a₀.re * b₀.im - a₀.im * b₀.re) = 0 := by
        linear_combination a₀.re * him - a₀.im * hre
      exact_mod_cast (mul_eq_zero.mp this).resolve_right hab₀.ne'
  have hsp : ⊤ ≤ Submodule.span ℤ (Set.range ![e, f]) := by
    intro c _
    have hc : ψ c ∈ AddSubgroup.closure ({a₀, b₀} : Set ℂ) := by
      rw [← h₀]
      exact AddSubgroup.subset_closure ⟨c, Submodule.mem_top, by simp [hψ]⟩
    obtain ⟨m, n, hmn⟩ := AddSubgroup.mem_closure_pair.mp hc
    have : c = m • e + n • f := hinj (by rw [← hmn]; simp [map_add, he, hf, zsmul_eq_mul])
    rw [this]
    exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  refine ⟨Module.Basis.mk hli hsp, ?_, ?_⟩ <;> simp [he, hf]
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
