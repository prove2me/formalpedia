-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.locBasic_conj_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:35:56.85209+00:00
-- url     : https://prove2.me/submissions/38bf8c6f-9e43-475c-87a5-4256e42bc431

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_sigma_spec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {R K : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (hinj : Function.Injective (algebraMap R K))
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K)) (p : Ideal R) :
    conjIdeal (K := K) p = p.comap (locBasic_sigma hinj hstar) := by
  have hσ := locBasic_sigma_spec hinj hstar
  have hσσ : ∀ r, locBasic_sigma hinj hstar (locBasic_sigma hinj hstar r) = r := fun r =>
    hinj (by rw [hσ, hσ, star_star])
  apply le_antisymm
  · unfold conjIdeal
    rw [Ideal.span_le]
    rintro r ⟨s, hs, hrs⟩
    have e : r = locBasic_sigma hinj hstar s := hinj (by rw [hrs, hσ])
    rw [SetLike.mem_coe, Ideal.mem_comap, e, hσσ]
    exact hs
  · intro r hr
    unfold conjIdeal
    apply Ideal.subset_span
    exact ⟨locBasic_sigma hinj hstar r, Ideal.mem_comap.mp hr, by rw [hσ, star_star]⟩
end Formalism.HermitianLatticesTheory
