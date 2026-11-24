-- Prove2me | solution 1 for Formalism.UG.P.GL_integral_hecke_commute
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:08:24.574927+00:00
-- url     : https://prove2.me/submissions/d69e273c-c34f-44bf-8248-651d03a1b65b

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Lemmata_NearbyExistence_ExistsNear
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Theorems.Thm_Formalism_UG_P_glint_princ_le_map_conj
import Theorems.Thm_Formalism_UG_P_glint_princ_relIndex_ne_zero
import Theorems.Thm_Formalism_UG_P_glint_exists_denom
import Theorems.Thm_Formalism_UG_P_glint_finite_residueField
import Theorems.Thm_Formalism_UG_P_glint_finite_quotient_of_dvr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
namespace Formalism.UG.P
theorem _root_.solution : Formalism.UG.GLintComm := by
  intro F _ _ v n g
  obtain ⟨c, hc0, hg, hg'⟩ := glint_exists_denom (v.adicCompletionIntegers F) g
  have hP := glint_princ_le_map_conj (v.adicCompletionIntegers F).toSubring g c hg hg'
  have hres : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) := glint_finite_residueField v
  have hI : Ideal.span {c * c} ≠ (⊥ : Ideal (v.adicCompletionIntegers F).toSubring) := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact mul_ne_zero hc0 hc0
  have hfin : Finite ((v.adicCompletionIntegers F).toSubring ⧸ Ideal.span {c * c}) :=
    glint_finite_quotient_of_dvr hres _ hI
  have hne := glint_princ_relIndex_ne_zero (n := Fin n) (v.adicCompletionIntegers F).toSubring
    (Ideal.span {c * c})
  have hd := Subgroup.relIndex_dvd_of_le_left (bc (n := Fin n) (v.adicCompletionIntegers F).toSubring.subtype).range hP
  intro h0
  apply hne
  unfold GLint at h0 hd
  rw [h0] at hd
  exact Nat.eq_zero_of_zero_dvd hd
end Formalism.UG.P
