-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBL.gN_setC_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:47:44.109561+00:00
-- url     : https://prove2.me/submissions/655004d6-e16c-45dc-be94-8ec7e5b0ec17

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FormPos
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AeNeZeroComplex
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBL_rr_eq_form
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBL_g_pos_of_built
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBL_gN_setC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.FourierDecayAlt.P.PBL
open Formalism.FourierDecayAlt NumberField MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.PBD
open scoped ComplexConjugate
noncomputable section
section rr
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}
end rr
section frame
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
end frame
section main
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
end main
section main2
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
end main2
section main3
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
end main3
section main4
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
private theorem tent_lemma (r : ℕ) (g : ℝ) (hg : g ≠ 0) (P : C.LPt) :
    ∀ x : ℕ, (∀ b ∈ D.toStd r g x P, 1 ≤ b.1 ∧ b.2 ≠ 0) ↔ (∀ b ∈ P, 1 ≤ b.1 ∧ b.2 ≠ 0) := by
  have hX : ∀ (n : ℤ) (m : ℕ), (((g / (2 * Real.pi)) ^ n : ℝ) : ℂ) * Complex.I ^ m ≠ 0 := by
    intro n m
    apply mul_ne_zero
    · exact_mod_cast zpow_ne_zero n (div_ne_zero hg (by positivity))
    · exact pow_ne_zero _ Complex.I_ne_zero
  induction P with
  | nil => intro x; simp only [D.toStd]
  | cons a l ih =>
    intro x
    simp only [D.toStd, List.forall_mem_cons]
    rw [ih (x + a.1)]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, right_ne_zero_of_mul h2⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, mul_ne_zero (hX _ _) h2⟩, h3⟩
end main4
end
end Formalism.FourierDecayAlt.P.PBL
end

set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBL
open Formalism.FourierDecayAlt NumberField MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.PBD
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
namespace Formalism.FourierDecayAlt.P.PBL
theorem _root_.solution {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}
    (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (v : Fin S.f) (ε : ℝ) (i : ℕ) (hi : i ≤ S.G.r) (w : List C.Letter) (P Q : C.LPt) (hP : D.IsLocPt P i)
    (hQ : D.IsLocPt Q i) :
    KB.gN (setC S p F) v ε i w P Q =
      ((dW S v i w P Q : ℝ) : ℂ) * (p v).form i hi w
        (KB.slv (p v).T (F v ε) i hi w (stdS S P) ((stdS_size S P).trans hP.2))
        (KB.slv (p v).T (F v ε) i hi w (stdS S Q) ((stdS_size S Q).trans hQ.2)) := by
  have hg := g_pos_of_built hB
  have key : ∀ R : C.LPt, D.IsLocPt R i → D.IsLocPt (stdS S R) i := by
    intro R hR
    exact And.intro ((tent_lemma _ _ hg.ne' R 1).mpr hR.1) ((stdS_size S R).trans hR.2)
  rw [gN_setC hB F v ε i w P Q, rr_eq_form (p v) (F v ε) i hi w (stdS S P) (stdS S Q) (key P hP) (key Q hQ)]
  unfold dW
  rfl
end Formalism.FourierDecayAlt.P.PBL
