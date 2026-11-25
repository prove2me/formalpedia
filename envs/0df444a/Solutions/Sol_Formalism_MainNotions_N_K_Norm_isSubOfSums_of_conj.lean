-- Prove2me | solution 1 for Formalism.MainNotions.N.K.Norm.isSubOfSums_of_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:22:32.779888+00:00
-- url     : https://prove2.me/submissions/8f0c580a-6550-4c18-827a-cd8489ea8f97

import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_QuotientHomNonvanishingBound
import Definitions.Def_Formalism_AdmissibleDesigns_InvariantsEqBotIff
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Module Formalism.WeaklyAdmissibleFiltrations TensorProduct
open Formalism Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K Formalism.MainNotions.N.K.Norm
variable {G : Type} [Group G] {LL : Type} [Field LL] {V : Type} [AddCommGroup V] [Module LL V]
  (ρ : Representation LL G V) {ι : Type} {k : ℕ}
namespace Formalism.MainNotions.N.K.Norm
theorem _root_.solution (Ms Ms' : ι → G → Matrix (Fin k) (Fin k) LL) (hc : ∀ x, IsConjM (Ms x) (Ms' x))
    (h : IsSubOfSums ρ Ms') : IsSubOfSums ρ Ms := by
  choose P Q h1 h2 h3 using fun x => (hc x).symm
  obtain ⟨m, xs, j, hj, hjg⟩ := h
  refine ⟨m, xs, LinearMap.pi (fun a => (Matrix.toLin' (P (xs a))) ∘ₗ (LinearMap.proj a ∘ₗ j)), ?_, fun g v => ?_⟩
  · intro v w hvw
    apply hj
    funext a
    have h0 := congrArg (Matrix.mulVec (Q (xs a))) (congrFun hvw a)
    simp only [LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply, Matrix.toLin'_apply,
      Matrix.mulVec_mulVec, h2, Matrix.one_mulVec] at h0
    exact h0
  · funext a
    simp only [LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply, Matrix.toLin'_apply]
    rw [hjg, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h3]
end Formalism.MainNotions.N.K.Norm
