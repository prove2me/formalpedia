-- Prove2me | solution 1 for Formalism.L2.DIV.detTwMul_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:11:57.38707+00:00
-- url     : https://prove2.me/submissions/a6308ddc-d240-445b-831d-6fcc697d912f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP
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
theorem _root_.solution (H : Hilbert90FiniteIdeles) : DetTwMul := by
  intro F E _ _ _ _ _ L _ σ n J ξ hσ hJ hξ g hg g' hg'
  have hk := norm_quotient_ker_le σ ξ hσ hξ
  have h1 := det_in_unitary_one F E σ n J hJ g hg
  have h2 := det_in_unitary_one F E σ n J hJ g' hg'
  rw [H F E σ hσ] at h1 h2
  obtain ⟨x, hx⟩ := h1
  obtain ⟨x', hx'⟩ := h2
  rw [detTw_of_det σ ξ hk g x hx, detTw_of_det σ ξ hk g' x' hx',
    detTw_of_det σ ξ hk (g * g') (x * x') (by rw [map_mul, map_mul, hx, hx']), map_mul]
end Formalism.L2.DIV
