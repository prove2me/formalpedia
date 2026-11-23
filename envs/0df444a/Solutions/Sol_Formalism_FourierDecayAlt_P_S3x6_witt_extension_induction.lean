-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x6.witt_extension_induction
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:29:19.900893+00:00
-- url     : https://prove2.me/submissions/f3caccb2-a683-493a-8ad7-5e0947701989

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictOrthogonalComplementNondeg
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_form_sum_right_alt
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_gram_mulVec_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_witt_extension_of_nondeg_gram
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_exists_isotropic_completion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x6
open Module
variable {K : Type} [Field K] {σ : K →+* K}
variable {V : Type} [AddCommGroup V] [Module K V]
namespace Formalism.FourierDecayAlt.P.S3x6
theorem _root_.solution (hσ : Inv σ) [FiniteDimensional K V] (h : V →ₛₗ[σ] V →ₗ[K] K) (hh : Herm h)
    (hn : Nondeg h) : ∀ (d a : ℕ) (x y : Fin a → V), a + d = finrank K V →
    LinearIndependent K x → LinearIndependent K y →
    (∀ i j, h (x i) (x j) = h (y i) (y j)) →
    ∃ g : V ≃ₗ[K] V, (∀ u v, h (g u) (g v) = h u v) ∧ ∀ i, g (x i) = y i := by
  intro d
  induction d with
  | zero =>
    intro a x y had hx hy hxy
    by_cases hG : IsUnit (gramMatrix h x).det
    · exact witt_extension_of_nondeg_gram hσ h hh hn x y hG hxy
    · exfalso
      rw [isUnit_iff_ne_zero, not_not] at hG
      obtain ⟨N, hN0, hN⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hG
      obtain ⟨i0, hi0⟩ := Function.ne_iff.1 hN0
      have hGN : ∀ i, h (x i) (∑ j, N j • x j) = 0 := by
        intro i
        rw [← gram_mulVec_eq, hN]; rfl
      obtain ⟨m, -, -, hm⟩ := exists_isotropic_completion hσ h hh hn x hx N i0 hi0 hGN
      have hli : LinearIndependent K (Fin.snoc x m : Fin (a + 1) → V) :=
        linearIndependent_finSnoc.2 ⟨hx, hm⟩
      have := hli.fintype_card_le_finrank
      simp only [Fintype.card_fin] at this
      omega
  | succ d ih =>
    intro a x y had hx hy hxy
    by_cases hG : IsUnit (gramMatrix h x).det
    · exact witt_extension_of_nondeg_gram hσ h hh hn x y hG hxy
    · rw [isUnit_iff_ne_zero, not_not] at hG
      obtain ⟨N, hN0, hN⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hG
      obtain ⟨i0, hi0⟩ := Function.ne_iff.1 hN0
      have hGN : ∀ i, h (x i) (∑ j, N j • x j) = 0 := by
        intro i
        rw [← gram_mulVec_eq, hN]; rfl
      have hGN' : ∀ i, h (y i) (∑ j, N j • y j) = 0 := by
        intro i
        rw [form_sum_right_alt]
        have h1 := hGN i
        rw [form_sum_right_alt] at h1
        simpa only [hxy] using h1
      obtain ⟨m, hm1, hm2, hm3⟩ := exists_isotropic_completion hσ h hh hn x hx N i0 hi0 hGN
      obtain ⟨m', hm1', hm2', hm3'⟩ := exists_isotropic_completion hσ h hh hn y hy N i0 hi0 hGN'
      obtain ⟨g, hg1, hg2⟩ := ih (a + 1) (Fin.snoc x m : Fin (a + 1) → V)
        (Fin.snoc y m' : Fin (a + 1) → V) (by omega)
        (linearIndependent_finSnoc.2 ⟨hx, hm3⟩) (linearIndependent_finSnoc.2 ⟨hy, hm3'⟩) (by
          intro i j
          refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
          · simp only [Fin.snoc_last, hm2, hm2']
          · simp only [Fin.snoc_last, Fin.snoc_castSucc]
            rw [← hh, hm1, ← hh (y j), hm1']
          · simp only [Fin.snoc_last, Fin.snoc_castSucc, hm1, hm1']
          · simp only [Fin.snoc_castSucc, hxy])
      refine ⟨g, hg1, fun i => ?_⟩
      have := hg2 i.castSucc
      simpa only [Fin.snoc_castSucc] using this
end Formalism.FourierDecayAlt.P.S3x6
