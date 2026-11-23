-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x6.witt_extension_of_nondeg_gram
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:20:33.045819+00:00
-- url     : https://prove2.me/submissions/c4a7aeb8-6eaf-46f5-87d4-b8b519e1c9c5

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictOrthogonalComplementNondeg
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_form_sum_expand
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_extend_to_orthogonal_basis

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
    (hn : Nondeg h) {a : ℕ} (x y : Fin a → V) (hG : IsUnit (gramMatrix h x).det)
    (hxy : ∀ i j, h (x i) (x j) = h (y i) (y j)) :
    ∃ g : V ≃ₗ[K] V, (∀ u v, h (g u) (g v) = h u v) ∧ ∀ i, g (x i) = y i := by
  have hGy : IsUnit (gramMatrix h y).det := by
    have : gramMatrix h y = gramMatrix h x := by
      ext i j
      exact (hxy i j).symm
    rw [this]; exact hG
  obtain ⟨bx, hx1, hx2, hx3, hx4⟩ := extend_to_orthogonal_basis hσ h hh hn x hG
  obtain ⟨bY, hy1, hy2, hy3, hy4⟩ := extend_to_orthogonal_basis hσ h hh hn y hGy
  have hb : ∀ i j, h (bx i) (bx j) = h (bY i) (bY j) := by
    intro i j
    rcases i with i | i <;> rcases j with j | j
    · rw [hx1, hx1, hy1, hy1, hxy]
    · rw [hx2, hy2]
    · rw [hx3, hy3]
    · rw [hx4, hy4]
  refine ⟨bx.equiv bY (Equiv.refl _), ?_, ?_⟩
  · intro u v
    have hg : ∀ w, bx.equiv bY (Equiv.refl _) w = ∑ i, bx.repr w i • bY i := by
      intro w
      calc bx.equiv bY (Equiv.refl _) w
          = bx.equiv bY (Equiv.refl _) (∑ i, bx.repr w i • bx i) := by rw [bx.sum_repr]
        _ = ∑ i, bx.repr w i • bY i := by
            rw [map_sum]
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [map_smul, Basis.equiv_apply]
            rfl
    rw [hg, hg, form_sum_expand]
    conv_rhs => rw [← bx.sum_repr u, ← bx.sum_repr v, form_sum_expand]
    simp only [hb]
  · intro i
    rw [← hx1, Basis.equiv_apply, ← hy1]
    rfl
end Formalism.FourierDecayAlt.P.S3x6
