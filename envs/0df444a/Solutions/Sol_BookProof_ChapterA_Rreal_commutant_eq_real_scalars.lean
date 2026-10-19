-- Prove2me | solution 1 for BookProof.ChapterA.Rreal_commutant_eq_real_scalars
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:43:51.998124+00:00
-- url     : https://prove2.me/submissions/011c16f4-d180-42c8-bcc5-4782ea0c0d89

-- Generated from ChapterA2b.lean — solution of BookProof.ChapterA.Rreal_commutant_eq_real_scalars
import Mathlib
import Definitions.Def_ChapterA2b
import Theorems.Thm_BookProof_ChapterA_real_scalar_commutesConj
import Definitions.Def_ChapterA
import Definitions.Def_ChapterA1
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution (M : System ℂ V) (hSchur : IsSchurFull M)
    {θ : AntiUnitary V} (_hθ : IsConjugation M θ) (S : V →L[ℂ] V) :
    (M.Commutes S ∧ CommutesConj θ S) ↔ ∃ r : ℝ, S = ((r : ℂ)) • (1 : V →L[ℂ] V) := by

  constructor <;> intro h;
  · obtain ⟨c, hc⟩ := hSchur S h.1;
    by_cases hc : c = starRingEnd ℂ c;
    · rw [ eq_comm ] at hc;
      simp_all only [Complex.ext_iff, Complex.conj_re, Complex.conj_im, true_and, Complex.coe_smul];
      exact ⟨ c.re, by congr; simp [ Complex.ext_iff, show c.im = 0 by linarith ] ⟩;
    · have h_subsingleton : ∀ x : V, x = 0 := by
        intro x
        have h_eq : (c - starRingEnd ℂ c) • θ x = 0 := by
          have := h.2 x; simp_all [ sub_smul, θ.map_smulₛₗ ] ;
        simp_all [ sub_eq_iff_eq_add ];
      exact ⟨ 0, by ext; simp [ h_subsingleton ] ⟩;
  · rcases h with ⟨ r, rfl ⟩; exact ⟨ fun m hm => by simp, real_scalar_commutesConj θ r ⟩
