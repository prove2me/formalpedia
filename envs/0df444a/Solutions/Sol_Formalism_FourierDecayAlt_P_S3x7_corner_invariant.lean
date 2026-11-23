-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x7.corner_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:24:05.145482+00:00
-- url     : https://prove2.me/submissions/d5881807-4bf4-43bc-a8ef-e8184abb4ffa

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LduDecompositionExists
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_submatrix_mul_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_submatrix_mul_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_up_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_mk_low
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_mk_up
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_not_range_castLE
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_not_range_rev
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_rev_inj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x7
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni IsLowUni isUpUni_mul isLowUni_mul isUpUni_inv isLowUni_inv isUpUni_one isLowUni_one
  isUpUni_det isLowUni_det)
open Formalism.FourierDecayAlt.S3
variable {A : Type} [CommRing A]
namespace Formalism.FourierDecayAlt.P.S3x7
theorem _root_.solution {r : ℕ} {v₂ X v₁ : Matrix (Fin r) (Fin r) A} (h₂ : IsUpUni v₂) (h₁ : IsUpUni v₁)
    (l : ℕ) (hl : l ≤ r) : cm (v₂ * X * v₁) l hl = cm X l hl := by
  unfold cm
  rw [submatrix_mul_right _ (Fin.castLE_injective hl), submatrix_mul_left _ (rev_inj hl),
    Matrix.det_mul, Matrix.det_mul]
  · have h1 : IsLowUni (v₂.submatrix (fun i : Fin l => (Fin.castLE hl i).rev)
        (fun i : Fin l => (Fin.castLE hl i).rev)) :=
      mk_low (fun i j hij => up_apply h₂ (by
        rw [Fin.lt_def] at hij ⊢
        have := j.isLt
        simp only [Fin.val_rev, Fin.val_castLE]; omega)) (fun i => h₂.2 _)
    have h2 : IsUpUni (v₁.submatrix (Fin.castLE hl) (Fin.castLE hl)) :=
      mk_up (fun i j hij => up_apply h₁ (by rw [Fin.lt_def] at hij ⊢; exact hij)) (fun i => h₁.2 _)
    rw [isLowUni_det A h1, isUpUni_det A h2, one_mul, mul_one]
  · intro a k hk
    have := not_range_rev hl hk
    exact up_apply h₂ (by
      rw [Fin.lt_def]; have := a.isLt; simp only [Fin.val_rev, Fin.val_castLE]; omega)
  · intro k b hk
    have := not_range_castLE hl hk
    exact up_apply h₁ (by rw [Fin.lt_def]; have := b.isLt; simp only [Fin.val_castLE]; omega)
end Formalism.FourierDecayAlt.P.S3x7
