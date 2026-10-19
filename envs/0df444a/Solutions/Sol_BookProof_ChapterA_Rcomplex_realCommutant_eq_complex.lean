-- Prove2me | solution 1 for BookProof.ChapterA.Rcomplex_realCommutant_eq_complex
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:47:37.209591+00:00
-- url     : https://prove2.me/submissions/0d2f50c6-1f09-4371-986c-47abac1d7c36

-- Generated from ChapterA2c.lean — solution of BookProof.ChapterA.Rcomplex_realCommutant_eq_complex
import Mathlib
import Definitions.Def_ChapterA2c
import Theorems.Thm_BookProof_ChapterA_cembed_apply
import Theorems.Thm_BookProof_ChapterA_cembed_realCommutes
import Theorems.Thm_BookProof_ChapterA_cplxify_commutes
import Theorems.Thm_BookProof_ChapterA_Plin_add_Qanti
import Theorems.Thm_BookProof_ChapterA_Plin_commutes_mulI
import Theorems.Thm_BookProof_ChapterA_Qanti_anticommutes_mulI
import Theorems.Thm_BookProof_ChapterA_Plin_realCommutes
import Theorems.Thm_BookProof_ChapterA_Qanti_realCommutes
import Definitions.Def_ChapterA
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace Quaternion


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution (M : System ℂ V) (hSchur : IsSchurFull M)
    (hNo : NoAntilinearCommutant M) (S : V →L[ℝ] V) :
    RealCommutes M S ↔ ∃ c : ℂ, S = cembed c := by

  constructor
  · intro hS
    have hP := Plin_commutes_mulI S
    obtain ⟨c, hc⟩ := hSchur _ (cplxify_commutes hP (Plin_realCommutes hS))
    have hQ0 : Qanti S = 0 :=
      hNo (Qanti S) (Qanti_anticommutes_mulI S) (Qanti_realCommutes hS)
    have hSP : S = Plin S := by
      conv_lhs => rw [← Plin_add_Qanti S]
      rw [hQ0, add_zero]
    refine ⟨c, ?_⟩
    ext x
    rw [hSP, cembed_apply]
    have hcx : cplxify (Plin S) hP x = (c • (1 : V →L[ℂ] V)) x := by rw [hc]
    simpa using hcx
  · rintro ⟨c, rfl⟩
    exact cembed_realCommutes M c
