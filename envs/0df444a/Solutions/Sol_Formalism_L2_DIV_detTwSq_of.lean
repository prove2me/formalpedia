-- Prove2me | solution 1 for Formalism.L2.DIV.detTwSq_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:11:17.737468+00:00
-- url     : https://prove2.me/submissions/b60c1675-61ac-49b1-aadd-800d792bd425

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP
import Theorems.Thm_Formalism_L2_DIV_conjugation_invariant_measure
import Theorems.Thm_Formalism_L2_DIV_det_in_unitary_one
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
theorem _root_.solution (H : Hilbert90FiniteIdeles) : DetTwSq := by
  intro F E _ _ _ _ _ L _ σ n J ξ hσ hJ hξ g hg
  have hk := norm_quotient_ker_le σ ξ hσ hξ
  have h1 := det_in_unitary_one F E σ n J hJ g hg
  rw [H F E σ hσ] at h1
  obtain ⟨x, hx⟩ := h1
  rw [detTw_of_det σ ξ hk g x hx, ← hx, h90, MonoidHom.div_apply, MonoidHom.id_apply, map_div]
  have := congrArg (fun η : Chr F E L => η x) (conjugation_invariant_measure F E L σ ξ hσ hξ)
  simp only [MonoidHom.comp_apply, MonoidHom.inv_apply] at this
  rw [this, div_inv_eq_mul, sq]
end Formalism.L2.DIV
