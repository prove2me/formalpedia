-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.substS_rename
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:33:25.292487+00:00
-- url     : https://prove2.me/submissions/82b6afc5-b133-4c9b-8d07-c0565468a865

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_substS_X
import Theorems.Thm_Formalism_MainNotions_PlaneGram_substS_C

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] {L : Type} [DecidableEq L] {L' : Type} [DecidableEq L'] {r : ℕ}
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {R : Type} [CommRing R] (ι : K →+* R) (A B : Matrix (Fin r) (Fin r) R)
    (f : L → L') (hf : Function.Injective f) (sg' : L' → Bool) (S' : Finset L')
    (F : MvPolynomial (L × Fin r) K) :
    substS ι sg' S' A B (rename (Prod.map f id) F) =
      rename (Prod.map f id) (substS ι (sg' ∘ f) (S'.preimage f hf.injOn) A B F) := by
  have : (substS ι sg' S' A B).comp (rename (Prod.map f (id : Fin r → Fin r))).toRingHom =
      ((rename (Prod.map f (id : Fin r → Fin r)) :
        MvPolynomial (L × Fin r) R →ₐ[R] MvPolynomial (L' × Fin r) R).toRingHom).comp
        (substS ι (sg' ∘ f) (S'.preimage f hf.injOn) A B) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [substS_C]
    · intro x
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X, substS_X]
      unfold subX
      simp only [Prod.map_fst, Prod.map_snd, id_eq, Finset.mem_preimage, Function.comp_apply]
      split_ifs <;> simp [map_sum, rename_X]
  exact RingHom.congr_fun this F
end Formalism.MainNotions.PlaneGram
