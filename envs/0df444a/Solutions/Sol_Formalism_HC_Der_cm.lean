-- Prove2me | solution 1 for Formalism.HC.Der.cm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:08:01.002687+00:00
-- url     : https://prove2.me/submissions/5c9a57ec-fc2a-461f-ad0a-b2c690d3d764

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DecompTypeI
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSymOfModEq
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycBasic
import Theorems.Thm_Formalism_HC_Der_conj_apply
import Theorems.Thm_Formalism_HC_Der_sqd_ne_zero
import Theorems.Thm_Formalism_HC_Der_conj_sqd
import Theorems.Thm_Formalism_FrobeniusOrbits_Final_conj
import Theorems.Thm_Formalism_HC_HostAx_sqd_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits
variable {φ : Frame} (H : HostRaw φ)
namespace Formalism.HC.Der
theorem _root_.solution : IsCMField H.E := by
  have := H.galois
  have hTC : IsTotallyComplex H.E := by
    refine ⟨fun w => ?_⟩
    rw [InfinitePlace.isComplex_iff, ComplexEmbedding.isReal_iff]
    intro hw
    have h2 := RingHom.congr_fun hw H.sqd
    rw [ComplexEmbedding.conjugate_coe_eq, ← conj_apply, conj_sqd, map_neg] at h2
    have h3 : (2 : ℂ) * w.embedding H.sqd = 0 := by linear_combination -h2
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact two_ne_zero h4
    · exact (map_ne_zero _).2 (sqd_ne_zero H) h4
  refine IsCMField.of_forall_isConj H.E (σ := H.conj) (fun ψ => ?_)
  ext x
  rw [ComplexEmbedding.conjugate_coe_eq]
  exact (conj_apply H ψ x).symm
end Formalism.HC.Der
