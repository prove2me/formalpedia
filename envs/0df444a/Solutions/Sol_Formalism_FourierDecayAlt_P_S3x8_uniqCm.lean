-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x8.uniqCm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:33:12.110127+00:00
-- url     : https://prove2.me/submissions/8cd768aa-a50d-497e-97e8-11895e3347b9

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CentreBlockStructure
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_keyCm

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
theorem _root_.solution {r : ℕ} (X v₂ v₁ : Matrix (Fin r) (Fin r) F) (h₂ : IsUpUni v₂) (h₁ : IsUpUni v₁)
    (hE : v₂ * X = X * v₁) (hu : ∀ (l : ℕ) (hl : l ≤ r), IsUnit (cm X l hl)) : v₂ = 1 ∧ v₁ = 1 := by
  obtain ⟨a1, a2, -⟩ := keyCm (RingHom.id F) Function.injective_id ⊥ (by simp) X X v₂ v₁ h₂ h₁
    (by simpa using hE) (by simp) hu
  constructor
  · ext a b
    have := a1 a b
    simpa [sub_eq_zero] using this
  · ext a b
    have := a2 a b
    simpa [sub_eq_zero] using this
end Formalism.FourierDecayAlt.P.S3x8
