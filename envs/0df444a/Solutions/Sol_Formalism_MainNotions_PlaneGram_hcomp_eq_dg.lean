-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.hcomp_eq_dg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:06:21.615008+00:00
-- url     : https://prove2.me/submissions/b4740642-b1a7-4819-aa5e-1729dd5cded1

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_coeff_hcomp
import Theorems.Thm_Formalism_MainNotions_PlaneGram_coeff_dg


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
variable {L : Type} {r : ℕ}
variable {K : Type} [Field K] [DecidableEq L] {R : Type} [CommRing R]
  (ι : K →+* R) (sg : L → Bool) (S : Finset L) (A B : Matrix (Fin r) (Fin r) R)
variable [Fintype L]
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (d : L → ℕ) (F : MvPolynomial (L × Fin r) K) :
    hcomp d F = dg (fun α => if (∀ i, ldeg α i = d i) then (1 : K) else 0) F := by
  ext β
  rw [coeff_hcomp, coeff_dg]
  split_ifs <;> simp
end Formalism.MainNotions.PlaneGram
