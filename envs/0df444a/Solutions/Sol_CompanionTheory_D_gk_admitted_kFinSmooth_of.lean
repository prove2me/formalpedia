-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.kFinSmooth_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:56:56.641029+00:00
-- url     : https://prove2.me/submissions/c17d6723-4fbe-4f0d-905b-eb46acec659a

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_InPCommutatorOfInK
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_AdmissibleOfFiniteRank
import Theorems.Thm_CompanionTheory_D_gk_admitted_Kset_sub
import Theorems.Thm_CompanionTheory_D_gk_admitted_admissible_of_finite_rank
import Theorems.Thm_CompanionTheory_D_gk_admitted_smooth_of_adm
import Theorems.Thm_CompanionTheory_D_gk_admitted_smoothOnH_conj
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil



set_option autoImplicit false
open MeasureTheory Matrix
open scoped ContDiff
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted
open PI.UpqRep
variable {n : ℕ} {ε : Fin n → Bool}
namespace CompanionTheory.D.gk.admitted
theorem _root_.solution (h1 : FinOfPI) (h2 : GoodPI) (h3 : Transfer) (h4 : ExistsAvg) (h5 : IwaHpk) (h6 : GardingFin) :
    PI.KFinSmooth := by
  intro k r ε lam H _ _ _ σ _ hσ v hv
  obtain ⟨P, hP, hDS⟩ := hσ
  obtain ⟨S, hSf, hvS, hS⟩ := hv
  have hPP : Pᴴ * P = 1 := Matrix.mem_unitaryGroup_iff'.1 hP.2
  have hPP' : P * Pᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hP.2
  have hinv : P⁻¹ = Pᴴ := Matrix.inv_eq_left_inv hPP
  refine smoothOnH_conj hP.1.1 hP.1.2 (smooth_of_adm (admissible_of_finite_rank h1 h2 h3 h4 (h5 k r ε P hP)) h6
    (σ := fun g => σ (P⁻¹ * g * P)) hDS.2.2.1 hDS.2.2.2.1 ⟨S, hSf, hvS, fun g hg x hx => hS _ ⟨?_, ?_⟩ x hx⟩)
  · have hg' : gᴴ * Jm ε * g = Jm ε := Kset_sub hg
    show (P⁻¹ * g * P)ᴴ * Hpk k r * (P⁻¹ * g * P) = Hpk k r
    rw [hinv, ← hP.1.2]
    calc (Pᴴ * g * P)ᴴ * (Pᴴ * Jm ε * P) * (Pᴴ * g * P) = Pᴴ * (gᴴ * (P * Pᴴ) * Jm ε * (P * Pᴴ) * g) * P := by
          simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = _ := by rw [hPP', Matrix.mul_one, Matrix.mul_one, hg']
  · rw [hinv]
    exact Submonoid.mul_mem _ (Submonoid.mul_mem _ (Unitary.star_mem hP.2) hg.1) hP.2
end CompanionTheory.D.gk.admitted
