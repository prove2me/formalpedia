-- Prove2me | solution 1 for BookProof.ChapterA.Rreal_isometric_iff_complexification_isometric
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:48:09.159268+00:00
-- url     : https://prove2.me/submissions/fcff77ab-6c9c-49e6-8ac1-ad3423c623d9

-- Generated from ChapterA2d.lean — solution of BookProof.ChapterA.Rreal_isometric_iff_complexification_isometric
import Mathlib
import Definitions.Def_ChapterA2d
import Theorems.Thm_BookProof_ChapterA_exists_unit_sqrt
import Theorems.Thm_BookProof_ChapterA_conjCLM_unitScale
import Theorems.Thm_BookProof_ChapterA_conjAU_commutesAntiUnitary
import Theorems.Thm_BookProof_ChapterA_IsConjugation_commutesAntiUnitary
import Theorems.Thm_BookProof_ChapterA_antiisometry_unique_up_to_phase
import Definitions.Def_ChapterA
import Definitions.Def_ChapterA1
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

set_option maxHeartbeats 1000000 in
theorem solution
    (M : System ℂ V) (N : System ℂ W) (hN : IsSchurUnitary N)
    {θM : AntiUnitary V} {θN : AntiUnitary W}
    (hθM : IsConjugation M θM) (hθN : IsConjugation N θN) :
    (∃ α : V ≃ₗᵢ[ℂ] W, IsSystemIso M N α ∧ ∀ x, α (θM x) = θN (α x)) ↔
    (∃ α : V ≃ₗᵢ[ℂ] W, IsSystemIso M N α) := by

  refine ⟨ fun ⟨ α, hα, h_intertwine ⟩ => ⟨ α, hα ⟩, ?_ ⟩;
  intro h;
  obtain ⟨α, hα⟩ := h
  obtain ⟨c, hc⟩ : ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ x, θN x = c • (conjAU α θM) x := by
    exact BookProof.ChapterA.antiisometry_unique_up_to_phase N hN
      (conjAU_commutesAntiUnitary hα hθM.commutesAntiUnitary) hθN.commutesAntiUnitary
  obtain ⟨l, hl⟩ : ∃ l : ℂ, l^2 = c ∧ ‖l‖ = 1 := exists_unit_sqrt c hc.left;
  refine ⟨ α.trans ( unitScaleEquiv l hl.2 ), ?_, ?_ ⟩ <;> simp_all only [IsSystemIso, conjAU_apply,
      LinearIsometryEquiv.trans_apply, unitScaleEquiv_apply, map_smul,
          LinearIsometryEquiv.symm_apply_apply];
  · ext; simp [conjCLM_unitScale];
  · intro x; simp [ ← hl.1 ] ;
    have h_unitScaleEquiv : α (θM (l • x)) = (starRingEnd ℂ) l • α (θM x) := by
      convert α.map_smul ( starRingEnd ℂ l ) ( θM x ) using 1;
      exact congr_arg _ ( θM.map_smulₛₗ _ _ );
    simp [ h_unitScaleEquiv, sq ];
    simp [ ← smul_assoc, mul_assoc, hl.2, Complex.mul_conj, Complex.normSq_eq_norm_sq ]
