-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.le_lord_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:07:44.493002+00:00
-- url     : https://prove2.me/submissions/e84e146f-791b-4aa3-99db-64b950c122f3

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_le_lord_iff

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
variable {R : Type} [Semiring R]
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {m n : WithTop ℤ} {f g : LaurentPolynomial R} (hf : m ≤ lord f) (hg : n ≤ lord g) :
    m + n ≤ lord (f * g) := by
  classical
  rw [le_lord_iff] at *
  intro k hk
  have hk' : k ∈ (f * g).coeff.support := Finsupp.mem_support_iff.mpr hk
  have := AddMonoidAlgebra.support_coeff_mul_subset f g hk'
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp this
  have h1 := hf a (Finsupp.mem_support_iff.mp ha)
  have h2 := hg b (Finsupp.mem_support_iff.mp hb)
  rw [WithTop.coe_add]
  exact add_le_add h1 h2
end Formalism.MainNotions.PlaneGram
