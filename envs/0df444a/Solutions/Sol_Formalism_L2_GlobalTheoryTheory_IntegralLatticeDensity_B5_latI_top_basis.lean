-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.latI_top_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:53:12.694526+00:00
-- url     : https://prove2.me/submissions/5e884df2-1d11-4a55-86c9-538107d502db

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_DedekindFactorK
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_QuadDiscr
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_LatITopBasis
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_covA_sq_im
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_covA_span

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
open NumberField Polynomial Matrix Classical
open scoped Pointwise
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
theorem _root_.solution (K : Type) [Field K] [NumberField K] (d : ℕ) [Fact d.Prime] (hd4 : d % 4 = 3)
    (x : K) (hx : x ^ 2 = -(d : K)) (hK : Module.finrank ℚ K = 2)
    (φ : K →+* ℂ) :
    ∃ a b : ℂ, 0 < ((starRingEnd ℂ) a * b).im ∧ latI φ ⊤ 1 = AddSubgroup.closure {a, b} ∧
      ((starRingEnd ℂ) a * b).im = Real.sqrt d / 2 := by
  obtain ⟨ω, hω, hspan⟩ := covA_span K d hd4 x hx hK
  have hd0 : 0 < d := (Fact.out : d.Prime).pos
  have hφx : (φ x) ^ 2 = -(d : ℂ) := by rw [← map_pow, hx]; simp
  have ht := covA_sq_im (φ x) d hd0 hφx
  have key : ∀ ω' : 𝓞 K, (∀ y : 𝓞 K, ∃ m n : ℤ, y = (m : 𝓞 K) + (n : 𝓞 K) * ω') →
      latI φ ⊤ 1 = AddSubgroup.closure {1, φ (ω' : K)} := by
    intro ω' hsp
    apply le_antisymm
    · rw [latI, AddSubgroup.closure_le]
      rintro w ⟨c, -, rfl⟩
      obtain ⟨m, n, rfl⟩ := hsp c
      have e : (1 : ℂ) * φ (((m : 𝓞 K) + (n : 𝓞 K) * ω' : 𝓞 K) : K) =
          m • (1 : ℂ) + n • φ (ω' : K) := by
        push_cast
        simp [zsmul_eq_mul]
      rw [e]
      exact add_mem (zsmul_mem (AddSubgroup.subset_closure (Set.mem_insert _ _)) m)
        (zsmul_mem (AddSubgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))) n)
    · rw [AddSubgroup.closure_le]
      rintro w (rfl | rfl)
      · exact AddSubgroup.subset_closure ⟨1, Submodule.mem_top, by simp⟩
      · exact AddSubgroup.subset_closure ⟨ω', Submodule.mem_top, by simp⟩
  have hωc : φ (ω : K) = (1 + φ x) / 2 := by rw [hω, map_div₀, map_add, map_one, map_ofNat]
  rcases lt_or_ge 0 (φ x).im with hpos | hneg
  · refine ⟨1, φ (ω : K), ?_, key ω hspan, ?_⟩
    · simp [hωc]
      linarith
    · have hs : Real.sqrt d = (φ x).im := by
        rw [← ht, Real.sqrt_sq hpos.le]
      simp [hωc, hs]
  · have hneg' : (φ x).im < 0 := by
      rcases hneg.lt_or_eq with h | h
      · exact h
      · rw [h] at ht
        have : (0 : ℝ) < d := by exact_mod_cast hd0
        nlinarith
    refine ⟨1, φ ((1 - ω : 𝓞 K) : K), ?_, key (1 - ω) ?_, ?_⟩
    · simp [hωc]
      linarith
    · intro y
      obtain ⟨m, n, rfl⟩ := hspan y
      exact ⟨m + n, -n, by push_cast; ring⟩
    · have hs : Real.sqrt d = -(φ x).im := by
        rw [← ht, ← neg_sq, Real.sqrt_sq (by linarith)]
      have h1ω : φ ((1 - ω : 𝓞 K) : K) = (1 - φ x) / 2 := by
        push_cast
        rw [map_sub, map_one, hωc]
        ring
      rw [h1ω, hs]
      simp
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
