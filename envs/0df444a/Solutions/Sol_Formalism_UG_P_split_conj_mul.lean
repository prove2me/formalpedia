-- Prove2me | solution 1 for Formalism.UG.P.split_conj_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:36:59.179783+00:00
-- url     : https://prove2.me/submissions/83bee7f7-396b-4dfb-ad1c-92e54e948676

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SplitUnitaryGroupIso

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution (J₁ : Matrix n n R) (hJ : IsUnit J₁.det) {P Q : Matrix n n R}
    (hPQ : P * Q = 1) : (J₁ * P * J₁⁻¹) * (J₁ * Q * J₁⁻¹) = 1 := by
  have h1 : J₁⁻¹ * J₁ = 1 := Matrix.nonsing_inv_mul _ hJ
  have h2 : J₁ * J₁⁻¹ = 1 := Matrix.mul_nonsing_inv _ hJ
  calc (J₁ * P * J₁⁻¹) * (J₁ * Q * J₁⁻¹) = J₁ * (P * (J₁⁻¹ * J₁) * Q) * J₁⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h1, Matrix.mul_one, hPQ, Matrix.mul_one, h2]
end Formalism.UG.P
