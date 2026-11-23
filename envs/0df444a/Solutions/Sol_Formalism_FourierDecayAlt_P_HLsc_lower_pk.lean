-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HLsc.lower_pk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:40.056109+00:00
-- url     : https://prove2.me/submissions/61990895-b89b-4a18-bbd4-90c9842ce58a

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Herglotz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HerglotzLowerSemicontinuous
import Theorems.Thm_Formalism_FourierDecayAlt_P_HLsc_isCompact_cube
import Theorems.Thm_Formalism_FourierDecayAlt_P_HLsc_continuous_pk
import Theorems.Thm_Formalism_FourierDecayAlt_P_HLsc_pk_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_HLsc_pk_periodic
import Theorems.Thm_Formalism_FourierDecayAlt_P_HLsc_integrable_mul_pk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HLsc
open Real Filter Topology Finset MeasureTheory Formalism.FourierDecayAlt.P.Herglotz
variable {d : ℕ}
namespace Formalism.FourierDecayAlt.P.HLsc
theorem _root_.solution {N : (Fin d → ℝ) → ℝ} (hN0 : ∀ z, 0 ≤ N z) (hint : Integrable N)
    (z₀ : Fin d → ℝ) (S : Finset (Fin d → ℤ)) (η : ℝ) (U : Set (Fin d → ℝ)) (hUo : IsOpen U)
    (hU1 : ∀ y ∈ U, ∀ m ∈ S, N (fun j => z₀ j + (m j : ℝ)) - η < N (fun j => z₀ j + (m j : ℝ) + y j))
    (hU2 : ∀ y ∈ U, ∀ j, |y j| < 1 / 2) (n : ℕ) :
    (∑ m ∈ S, (N (fun j => z₀ j + (m j : ℝ)) - η)) *
      (∫ y in cube d, pk y ^ n • U.indicator (fun _ => (1 : ℝ)) y) ≤ ∫ z, N z * pk (z - z₀) ^ n := by
  set G : (Fin d → ℝ) → ℝ := fun y => pk y ^ n • U.indicator (fun _ => (1 : ℝ)) y with hG
  have hUc : U ⊆ cube d := fun y hy =>
    ⟨fun j => (abs_lt.1 (hU2 y hy j)).1.le, fun j => (abs_lt.1 (hU2 y hy j)).2.le⟩
  have hGint0 : IntegrableOn G (cube d) := by
    have h1 : IntegrableOn (fun y : Fin d → ℝ => pk y ^ n) (cube d) :=
      (continuous_pk.pow n).continuousOn.integrableOn_compact isCompact_cube
    have h2 := h1.indicator hUo.measurableSet
    refine h2.congr (Eventually.of_forall (fun y => ?_))
    by_cases hy : y ∈ U
    · simp [hG, hy]
    · simp [hG, hy]
  have hGz : ∀ y, y ∉ cube d → G y = 0 := by
    intro y hy
    have : y ∉ U := fun h => hy (hUc h)
    simp [hG, this]
  have hGint : Integrable G := by
    rw [← integrableOn_univ]
    refine (integrableOn_iff_integrable_of_support_subset ?_).1 hGint0 |>.integrableOn
    intro y hy
    by_contra hc
    exact hy (hGz y hc)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hGz]
  have hpt : ∀ z, ∑ m ∈ S, (N (fun j => z₀ j + (m j : ℝ)) - η) * G (z - fun j => z₀ j + (m j : ℝ)) ≤
      N z * pk (z - z₀) ^ n := by
    intro z
    have hR : 0 ≤ N z * pk (z - z₀) ^ n := mul_nonneg (hN0 z) (pow_nonneg (pk_nonneg _) n)
    by_cases h : ∃ m ∈ S, (z - fun j => z₀ j + (m j : ℝ)) ∈ U
    · obtain ⟨m, hm, hmU⟩ := h
      rw [Finset.sum_eq_single_of_mem m hm]
      · have hper : pk (z - fun j => z₀ j + (m j : ℝ)) = pk (z - z₀) := by
          rw [← pk_periodic (z - fun j => z₀ j + (m j : ℝ)) m]
          congr 1
          funext j
          simp only [Pi.sub_apply]
          ring
        have hz : (fun j => z₀ j + (m j : ℝ) + (z - fun j => z₀ j + (m j : ℝ)) j) = z := by
          funext j
          simp only [Pi.sub_apply]
          ring
        have h1 := hU1 _ hmU m hm
        rw [hz] at h1
        simp only [hG, Set.indicator_of_mem hmU, smul_eq_mul, mul_one, hper]
        exact mul_le_mul_of_nonneg_right h1.le (pow_nonneg (pk_nonneg _) n)
      · intro m' hm' hne
        have : (z - fun j => z₀ j + (m' j : ℝ)) ∉ U := by
          intro hm'U
          apply hne
          funext j
          have a1 := abs_lt.1 (hU2 _ hmU j)
          have a2 := abs_lt.1 (hU2 _ hm'U j)
          simp only [Pi.sub_apply] at a1 a2
          have b1 : ((m' j - m j : ℤ) : ℝ) < 1 := by push_cast; linarith [a1.1, a1.2, a2.1, a2.2]
          have b2 : (-1 : ℝ) < ((m' j - m j : ℤ) : ℝ) := by push_cast; linarith [a1.1, a1.2, a2.1, a2.2]
          have c1 : m' j - m j < 1 := by exact_mod_cast b1
          have c2 : -1 < m' j - m j := by exact_mod_cast b2
          omega
        simp [hG, this]
    · push Not at h
      rw [Finset.sum_eq_zero]
      · exact hR
      · intro m hm
        simp [hG, h m hm]
  have hmono := integral_mono
    (integrable_finsetSum S (fun m _ =>
      (hGint.comp_sub_right (fun j => z₀ j + (m j : ℝ))).const_mul
        (N (fun j => z₀ j + (m j : ℝ)) - η)))
    (integrable_mul_pk hint z₀ n) hpt
  rw [integral_finsetSum] at hmono
  · simp_rw [integral_const_mul, integral_sub_right_eq_self G] at hmono
    rw [← Finset.sum_mul] at hmono
    exact hmono
  · intro m _
    exact (hGint.comp_sub_right (fun j => z₀ j + (m j : ℝ))).const_mul _
end Formalism.FourierDecayAlt.P.HLsc
