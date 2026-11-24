-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SettingConstruction.transitive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:54:08.344371+00:00
-- url     : https://prove2.me/submissions/08d1b13e-1501-4d36-beb9-ceced5e0799a

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SettingConstruction
import Theorems.Thm_Formalism_FourierDecayAlt_P_SettingConstruction_herm_add_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_SettingConstruction_herm_sub_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_SettingConstruction_herm_smul_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_SettingConstruction_herm_add_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_SettingConstruction_herm_sub_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_SettingConstruction_herm_smul_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_SettingConstruction_herm_symm
import Theorems.Thm_Formalism_FourierDecayAlt_P_SettingConstruction_unitary_of_form
import Theorems.Thm_Formalism_FourierDecayAlt_P_SettingConstruction_rk_mulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SettingConstruction
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ)
variable [DecidableEq ι]
namespace Formalism.FourierDecayAlt.P.SettingConstruction
theorem _root_.solution (hH : Hᴴ = H) (u v : ι → ℂ) (t : ℝ) (ht : 0 < t) (hu : herm H u u = -(t : ℂ)) (hv : herm H v v = -(t : ℂ)) :
    ∃ g : Matrix ι ι ℂ, gᴴ * H * g = H ∧ g *ᵥ u = v := by
  set p := herm H u v with hp_def
  obtain ⟨c, hcc, s, hs0, hsp⟩ : ∃ c : ℂ, c * star c = 1 ∧ ∃ s : ℝ, 0 ≤ s ∧ star c * p = s := by
    by_cases hp : p = 0
    · exact ⟨1, by simp, 0, le_rfl, by simp [hp]⟩
    · have hn : (‖p‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hp
      have hpp : p * star p = (‖p‖ : ℂ) ^ 2 := by
        rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
      have hsn : star (‖p‖ : ℂ) = (‖p‖ : ℂ) := Complex.conj_ofReal _
      refine ⟨p / ‖p‖, ?_, ‖p‖, norm_nonneg _, ?_⟩
      · rw [star_div₀, hsn, div_mul_div_comm, hpp, ← sq, div_self (pow_ne_zero 2 hn)]
      · rw [star_div₀, hsn, div_mul_eq_mul_div, mul_comm, hpp, sq, mul_div_assoc, div_self hn, mul_one]
  have hs_star : star (s : ℂ) = s := Complex.conj_ofReal s
  have hsp' : c * star p = s := by
    have := congrArg star hsp
    rw [star_mul', star_star, hs_star] at this
    linear_combination this
  have hvu : herm H v u = star p := (herm_symm H hH u v).symm
  set d := u - c • v with hd
  have hσ : (0 : ℝ) < t + s := by linarith
  set σ : ℂ := ((t + s : ℝ) : ℂ) with hσ_def
  have hσ0 : σ ≠ 0 := by rw [hσ_def]; exact_mod_cast hσ.ne'
  have hud : herm H u d = -σ := by
    rw [hd, herm_sub_right, herm_smul_right, hu, hsp, hσ_def]; push_cast; ring
  have hdd : herm H d d = -2 * σ := by
    simp only [hd, herm_sub_left, herm_sub_right, herm_smul_left, herm_smul_right, hu, hv, hvu, hσ_def]
    push_cast
    linear_combination (-1 : ℂ) * hsp - hsp' - (t : ℂ) * hcc
  have hdy : ∀ y, herm H d y = star (herm H y d) := fun y => (herm_symm H hH y d).symm
  refine ⟨rk H d (star c) (star c * σ⁻¹), ?_, ?_⟩
  · apply unitary_of_form
    intro x y
    rw [rk_mulVec, rk_mulVec]
    simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, hdy x, hdy y, hdd]
    have hsσ : star σ⁻¹ = σ⁻¹ := by rw [star_inv₀, hσ_def, Complex.star_def, Complex.conj_ofReal]
    have hβ : σ⁻¹ * σ = 1 := inv_mul_cancel₀ hσ0
    simp only [star_mul', star_star, hsσ, hdy d]
    linear_combination (herm H x y) * hcc - 2 * herm H x d * star (herm H y d) * c * star c * σ⁻¹ * hβ
  · rw [rk_mulVec, hud]
    have hβ : σ⁻¹ * σ = 1 := inv_mul_cancel₀ hσ0
    funext i
    simp only [hd, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    linear_combination v i * hcc - star c * (u i - c * v i) * hβ
end Formalism.FourierDecayAlt.P.SettingConstruction
