-- Prove2me | solution 1 for Formalism.L2.DIV.unitary_det_norm_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:26:41.612522+00:00
-- url     : https://prove2.me/submissions/35824132-1ed4-4327-b9f5-39a0707f4fc8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain TensorProduct Formalism.UG Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.UG.P
open scoped nonZeroDivisors
open Formalism Formalism.L2 Formalism.L2.DIV
namespace Formalism.L2.DIV
theorem _root_.solution {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A) (hJ : IsUnit J.det)
    (g : GL (Fin n) A) (hg : g ∈ UJ σ J) : σ (g : Matrix (Fin n) (Fin n) A).det * (g : Matrix (Fin n) (Fin n) A).det = 1 := by
  have h : cT σ (g : Matrix (Fin n) (Fin n) A) * J * (g : Matrix (Fin n) (Fin n) A) = J := hg
  have h2 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, cT, Matrix.det_transpose] at h2
  have h3 : ((g : Matrix (Fin n) (Fin n) A).map σ).det = σ (g : Matrix (Fin n) (Fin n) A).det := by
    rw [RingHom.map_det]; rfl
  rw [h3] at h2
  apply hJ.mul_left_cancel
  linear_combination h2
end Formalism.L2.DIV
