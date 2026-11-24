-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.plane_gram_theorem_of_combined_lemmas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:38:28.915843+00:00
-- url     : https://prove2.me/submissions/2e9194b7-39ed-4e5c-b9b4-d6ba713dfc63

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ProjKeepsLetter
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_TestBoundOfRhoAndNormSets
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Lam_smul
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_ph_mem_PolK
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_cge_ph
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Dm_nonneg
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Dl_nonneg
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_kapD_ge_one
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_smul
import Theorems.Thm_Formalism_MainNotions_PlaneGram_bge_iff
import Theorems.Thm_Formalism_MainNotions_PlaneGram_bge_mono
import Theorems.Thm_Formalism_MainNotions_PlaneGram_bge_of_cge
import Theorems.Thm_Formalism_MainNotions_PlaneGram_cge_zero_iff_Integral
import Theorems.Thm_Formalism_MainNotions_PlaneGram_two_le_p
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_mono
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_smul
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vle_add_of_lt
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vle_pow_p
import Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_kapL_le_kap__2a6ba908208b


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ} {C0 : ℝ}
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (h1 : 1 ≤ C0) (hBC : StepBC K v p C0) (hDEF : StepDEF K v p C0) :
    LiftBoundUniform K v p C0 := by
  intro hD D hV hH hc F hF hF0
  obtain ⟨Z, hZi, hZg, hZy, hZl⟩ := hBC hD D hV hc F hF hF0
  obtain ⟨Om, N2, hN2, hOi, hOg, hOc, hOy, hOl⟩ := hDEF hD D hV hH hc F hF hF0
  have hp : 2 ≤ p := two_le_p hD
  have hr : 1 ≤ D.r := hV.1
  have hJ : 1 ≤ D.J := hV.2.1
  have hkap := D.kapD_ge_one hp hr hJ
  have hDm := D.Dm_nonneg hp hr h1
  have hDl := D.Dl_nonneg hp hr h1
  have hcc : 4 * (D.Dm p C0 + D.Dl p C0 + 3 * D.kapD p) < D.c := hc
  have hG : D.Good p (((p : K) ^ N2) • Om Z) := TwistData.Good.smul D (hOg Z hZg) _
  have hGi : Integral v (((p : K) ^ N2) • Om Z) := hOi Z hZi hZg
  refine ⟨((p : K) ^ N2) • Om Z, 0, ⟨⟨hGi, ?_⟩, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro α hα j m hm a
    exact (hG α hα).2.1 j m hm a
  · intro j i
    exact vala_smul _ (hOc Z hZg j i)
  · intro j m hm
    have := vala_smul ((p : K) ^ N2) (hOy Z hZg j m _ hm (hZy j m hm))
    exact vala_mono (by linarith) this
  · intro α hα t a
    exact (hG α hα).1 t a
  · intro α hα; simp at hα
  · intro α hα; simp at hα
  · intro α; simp [vR]
  · intro α hα
    exact ⟨(hG α hα).2.2.1, fun t => by
      have := (hG α hα).2.2.2.1 t
      simp only [ldeg] at this
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
      exact this⟩
  · intro α hα; simp at hα
  · rw [add_zero, ← bge_iff]
    have h2 := bge_of_cge hD (D.ph_mem_PolK p hG) (D.cge_ph v p ((cge_zero_iff_Integral v _).mpr hGi))
    refine bge_mono v ?_ h2
    have h3 := kapL_le_kap' hp hr D.dO
    have h4 : D.n0 v = vN v (∏ i : D.OL, (D.dO i).factorial) / 2 := rfl
    have h5 : D.kapD p = kap p D.r D.dO := rfl
    rw [h4, h5]; linarith
  · rw [add_zero]
    have e1 : fock F (D.gaAct (D.ph p (((p : K) ^ N2) • Om Z))) = (p : K) ^ N2 * D.abelian₂ p F (Om Z) :=
      D.Lam_smul p F _ _
    have e2 : D.abelian₂ p F (Om Z) = D.abelian₂ p F Z + (D.abelian₂ p F (Om Z) - D.abelian₂ p F Z) := by ring
    have h6 : vle v (D.n0 v + D.Dl p C0 + 1) (D.abelian₂ p F (Om Z)) := by
      rw [e2]
      exact vle_add_of_lt v hZl (hOl Z hZi hZg) (by linarith)
    have h7 := vle_pow_p hD N2 h6
    rw [e1]
    have h8 : vR v ((p : K) ^ N2 * D.abelian₂ p F (Om Z)) ≤ ((D.n0 v + D.Dl p C0 + 1 + N2 : ℝ) : WithTop ℝ) := h7
    calc vR v ((p : K) ^ N2 * D.abelian₂ p F (Om Z)) + ((-D.n0 v + D.kapD p : ℝ) : WithTop ℝ)
        ≤ ((D.n0 v + D.Dl p C0 + 1 + N2 : ℝ) : WithTop ℝ) + ((-D.n0 v + D.kapD p : ℝ) : WithTop ℝ) := by
          gcongr
      _ = ((D.n0 v + D.Dl p C0 + 1 + N2 + (-D.n0 v + D.kapD p) : ℝ) : WithTop ℝ) := by
          rw [← WithTop.coe_add]
      _ ≤ ((D.E p C0 2 + 2 * D.kapD p : ℝ) : WithTop ℝ) := by
          rw [WithTop.coe_le_coe]
          unfold TwistData.E
          linarith
end Formalism.MainNotions.PlaneGram
