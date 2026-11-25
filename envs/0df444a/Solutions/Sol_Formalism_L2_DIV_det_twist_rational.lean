-- Prove2me | solution 1 for Formalism.L2.DIV.det_twist_rational
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:11:17.742802+00:00
-- url     : https://prove2.me/submissions/bef59ac6-0b6d-44a0-91f8-b2843ffec196

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP
import Theorems.Thm_Formalism_L2_DIV_tensor_conjugation_tmul
import Theorems.Thm_Formalism_L2_DIV_hilbert90_quadratic_field
import Theorems.Thm_Formalism_L2_DIV_unitary_det_norm_one
import Theorems.Thm_Formalism_L2_DIV_conjugation_units_val
import Theorems.Thm_Formalism_L2_DIV_norm_quotient_eq_iff
import Theorems.Thm_Formalism_L2_DIV_norm_quotient_ker_le
import Theorems.Thm_Formalism_L2_DIV_detTw_of_det


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
theorem _root_.solution : DetTwRat := by
  intro F E _ _ _ _ _ L _ σ n J ξ hσ hJ hξ hrat g hg
  have hk := norm_quotient_ker_le σ ξ hσ hξ
  obtain ⟨g0, hg0, rfl⟩ := hg
  have hd := unitary_det_norm_one (σ : E →+* E) J hJ g0 hg0
  obtain ⟨x, hx0, hx⟩ := hilbert90_quadratic_field σ hσ _ hd
  have key : h90 σ (ratId F E (Units.mk0 x hx0)) =
      Matrix.GeneralLinearGroup.det (bc (inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)) g0) := by
    rw [norm_quotient_eq_iff]
    apply Units.ext
    rw [Units.val_mul, conjugation_units_val, Matrix.GeneralLinearGroup.val_det_apply]
    have e1 : ((ratId F E (Units.mk0 x hx0) : (AfE F E)ˣ) : AfE F E) =
        inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F) x := rfl
    have e2 : ((bc (inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)) g0 : GL (Fin n) (AfE F E)) :
        Matrix (Fin n) (Fin n) (AfE F E)).det =
        inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F) (g0 : Matrix (Fin n) (Fin n) E).det := by
      rw [RingHom.map_det]; rfl
    have e3 : sigR σ (FiniteAdeleRing (𝓞 F) F) (inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F) x) =
        inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F) (σ x) := tensor_conjugation_tmul σ _ x 1
    rw [e1, e2, e3, ← map_mul]
    exact congrArg _ hx
  rw [detTw_of_det σ ξ hk _ _ key]
  exact hrat ⟨_, rfl⟩
end Formalism.L2.DIV
