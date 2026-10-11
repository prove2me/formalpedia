-- Prove2me | solution 1 for BookProof.ReducedEsa.deficiencyTrivialAt_red
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:51:55.505833+00:00
-- url     : https://prove2.me/submissions/40bf82df-8d04-44d2-af7a-dbd8b3db53a9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterReducingSubspaceEsa.lean — solution of BookProof.ReducedEsa.deficiencyTrivialAt_red
import Mathlib
import Definitions.Def_ChapterReducingSubspaceEsa
import Theorems.Thm_BookProof_ChapterWignerOrbitClassification_SameOrbit_symm
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterA
import Definitions.Def_ChapterFarisLavineCore
open BookProof.ReducedEsa




open BookProof.FarisLavine BookProof.GraphCore

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {P : F →ₗ[ℂ] F}
variable {D : Submodule ℂ F}
variable (T : D →ₗ[ℂ] F)
variable {T}
variable (T) in

set_option maxHeartbeats 1000000 in
theorem solution (hP : IsReducingProjection P) {hPD : ∀ x ∈ D, P x ∈ D}
    (hC : Commutes T hPD) {z : ℂ} (hz : DeficiencyTrivialAt D T z) :
    DeficiencyTrivialAt (redDom P D) (redOp T hP hC) z := by

  intro w hw
  set W : F := (w : F) with hW
  have hPW : P W = W := hP.apply_of_mem_range (w : sector P).2
  have key : ∀ v : D, (inner ℂ (T v) W : ℂ) = z * inner ℂ (v : F) W := by
    intro v
    -- the projected vector, as an element of the reduced domain
    have hPv : P (v : F) ∈ D := hPD _ v.2
    set v' : redDom P D := ⟨⟨P (v : F), ⟨(v : F), rfl⟩⟩, hPv⟩ with hv'
    have h1 : (inner ℂ (T ⟨P (v : F), hPv⟩) W : ℂ) = z * inner ℂ (P (v : F)) W := by
      have h2 := hw v'
      simp only [hv', redOp_coe, Submodule.coe_inner] at h2
      have hinc : (redIncl P D) ⟨⟨P (v : F), ⟨(v : F), rfl⟩⟩, hPv⟩ = ⟨P (v : F), hPv⟩ := rfl
      rw [hinc] at h2
      rw [hW]
      exact h2
    have h2 : (inner ℂ (T v) W : ℂ) = inner ℂ (P (T v)) W := by
      rw [hP.symm (T v) W, hPW]
    have h3 : (inner ℂ (P (T v)) W : ℂ) = inner ℂ (T ⟨P (v : F), hPv⟩) W := by
      rw [hC.comm v]
    have h4 : (inner ℂ (P (v : F)) W : ℂ) = inner ℂ (v : F) W := by
      rw [hP.symm (v : F) W, hPW]
    rw [h2, h3, h1, h4]
  have hW0 : W = 0 := hz W key
  exact Subtype.ext (by simpa [hW] using hW0)
