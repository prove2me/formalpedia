-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x8.keyCm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:30:24.212798+00:00
-- url     : https://prove2.me/submissions/3296c4e4-487b-4598-8e80-3fec9e527d40

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CentreBlockStructure
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_key

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x8
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni IsLowUni isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det isLowUni_det)
open Formalism.FourierDecayAlt.S3
variable {A F : Type} [CommRing A] [CommRing F]
namespace Formalism.FourierDecayAlt.P.S3x8
theorem _root_.solution (φ : A →+* F) (hφ : Function.Injective φ) (I : AddSubgroup F)
    (hI : ∀ a x, x ∈ I → φ a * x ∈ I) {r : ℕ} (X X' : Matrix (Fin r) (Fin r) A)
    (v₂ v₁ : Matrix (Fin r) (Fin r) F) (h₂ : IsUpUni v₂) (h₁ : IsUpUni v₁)
    (hE : v₂ * X'.map φ = X.map φ * v₁) (hd : ∀ a b, φ (X' a b - X a b) ∈ I)
    (hu : ∀ (l : ℕ) (hl : l ≤ r), IsUnit (cm X l hl)) :
    (∀ a b, (v₂ - 1) a b ∈ I) ∧ (∀ a b, (v₁ - 1) a b ∈ I) ∧
      ∀ (l : ℕ) (hl : l ≤ r), cm X' l hl = cm X l hl := by
  have hL : IsLowUni (v₂.submatrix Fin.rev Fin.rev) :=
    ⟨fun i j h => h₂.1 (by simpa using h), fun a => h₂.2 _⟩
  have hE' : v₂.submatrix Fin.rev Fin.rev * (X'.submatrix Fin.rev id).map φ =
      (X.submatrix Fin.rev id).map φ * v₁ := by
    calc v₂.submatrix Fin.rev Fin.rev * (X'.submatrix Fin.rev id).map φ
        = (v₂ * X'.map φ).submatrix Fin.rev id :=
          Matrix.submatrix_mul_equiv v₂ (X'.map φ) Fin.rev Fin.revPerm id
      _ = (X.map φ * v₁).submatrix Fin.rev id := by rw [hE]
      _ = (X.submatrix Fin.rev id).map φ * v₁ :=
          (Matrix.submatrix_mul_equiv (X.map φ) v₁ Fin.rev (Equiv.refl _) id).symm
  obtain ⟨a1, a2, a3⟩ := key φ hφ I hI r (X.submatrix Fin.rev id) (X'.submatrix Fin.rev id) _ _ hL h₁ hE'
    (fun a b => hd _ _) (fun l hl => hu l hl)
  refine ⟨fun a b => ?_, a2, fun l hl => a3 l hl⟩
  have := a1 a.rev b.rev
  simpa [Matrix.one_apply] using this
end Formalism.FourierDecayAlt.P.S3x8
