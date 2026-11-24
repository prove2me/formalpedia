-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.latI_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:04:20.875311+00:00
-- url     : https://prove2.me/submissions/2a043ea5-bd96-4a8e-bbca-2af15d8ccee8

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_DedekindFactorK
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_IdealBasis
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_ib_im_conj_mul
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_ib_exists_basis
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_ib_im_det

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
theorem _root_.solution (K : Type) [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2)
    (φ : K →+* ℂ) (a₀ b₀ : ℂ) (hab₀ : 0 < ((starRingEnd ℂ) a₀ * b₀).im)
    (h₀ : latI φ ⊤ 1 = AddSubgroup.closure {a₀, b₀}) (𝔞 : Ideal (𝓞 K)) (h𝔞 : 𝔞 ≠ ⊥) :
    ∃ a b : ℂ, 0 < ((starRingEnd ℂ) a * b).im ∧ latI φ 𝔞 1 = AddSubgroup.closure {a, b} ∧
      ((starRingEnd ℂ) a * b).im = (Ideal.absNorm 𝔞 : ℝ) * ((starRingEnd ℂ) a₀ * b₀).im := by
  set ψ : 𝓞 K →+* ℂ := φ.comp (algebraMap (𝓞 K) K) with hψ
  obtain ⟨B, hB0, hB1⟩ := ib_exists_basis φ a₀ b₀ hab₀ h₀
  set bI := Ideal.selfBasis B 𝔞 h𝔞
  have hdet := Ideal.natAbs_det_basis_change B 𝔞 bI
  set D := B.det ((↑) ∘ bI) with hD
  have hD0 : D ≠ 0 := by
    intro h
    rw [h, Int.natAbs_zero] at hdet
    exact h𝔞 (Ideal.absNorm_eq_zero_iff.mp hdet.symm)
  have hcross := ib_im_det ψ a₀ b₀ B hB0 hB1 ((↑) ∘ bI)
  rw [← hD] at hcross
  simp only [Function.comp_apply] at hcross
  have hN : (Ideal.absNorm 𝔞 : ℝ) = |(D : ℝ)| := by
    rw [← hdet, Nat.cast_natAbs, Int.cast_abs]
  have hlat : latI φ 𝔞 1 = AddSubgroup.closure {ψ (bI 0 : 𝓞 K), ψ (bI 1 : 𝓞 K)} := by
    apply le_antisymm
    · unfold latI
      rw [AddSubgroup.closure_le]
      rintro _ ⟨c, hc, rfl⟩
      rw [one_mul, SetLike.mem_coe, AddSubgroup.mem_closure_pair]
      have hs := bI.sum_repr ⟨c, hc⟩
      have hc' : c = (bI.repr ⟨c, hc⟩ 0) • (bI 0 : 𝓞 K) + (bI.repr ⟨c, hc⟩ 1) • (bI 1 : 𝓞 K) := by
        have h2 : ((∑ i, bI.repr ⟨c, hc⟩ i • bI i : 𝔞) : 𝓞 K) = c := by rw [hs]
        rw [Fin.sum_univ_two] at h2
        exact h2.symm
      refine ⟨bI.repr ⟨c, hc⟩ 0, bI.repr ⟨c, hc⟩ 1, ?_⟩
      show _ = ψ c
      conv_rhs => rw [hc']
      simp [map_add]
    · rw [AddSubgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨AddSubgroup.subset_closure ⟨_, (bI 0).2, by simp [hψ]⟩,
        AddSubgroup.subset_closure ⟨_, (bI 1).2, by simp [hψ]⟩⟩
  rcases lt_or_gt_of_ne hD0 with hneg | hpos
  · have hneg' : (D : ℝ) < 0 := by exact_mod_cast hneg
    have hsw : ((starRingEnd ℂ) (ψ (bI 1 : 𝓞 K)) * ψ (bI 0 : 𝓞 K)).im =
        -((starRingEnd ℂ) (ψ (bI 0 : 𝓞 K)) * ψ (bI 1 : 𝓞 K)).im := by
      rw [ib_im_conj_mul, ib_im_conj_mul]; ring
    refine ⟨ψ (bI 1 : 𝓞 K), ψ (bI 0 : 𝓞 K), ?_, by rw [hlat, Set.pair_comm], ?_⟩
    · rw [hsw, hcross]; nlinarith
    · rw [hsw, hcross, hN, abs_of_neg hneg']; ring
  · have hpos' : (0 : ℝ) < D := by exact_mod_cast hpos
    refine ⟨ψ (bI 0 : 𝓞 K), ψ (bI 1 : 𝓞 K), ?_, hlat, ?_⟩
    · rw [hcross]; positivity
    · rw [hcross, hN, abs_of_pos hpos']
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
