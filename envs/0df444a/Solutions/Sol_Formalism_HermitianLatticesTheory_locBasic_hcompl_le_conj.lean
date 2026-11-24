-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.locBasic_hcompl_le_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:52.198951+00:00
-- url     : https://prove2.me/submissions/842253e4-78af-484f-891a-324c3ba0b40c

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_sigma_spec
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_conj_eq

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
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K)) (p : Ideal R)
    [(conjIdeal (K := K) p).IsPrime] :
    hcompl (K := K) p ≤ (conjIdeal (K := K) p).primeCompl := by
  unfold hcompl
  rw [Submonoid.closure_le]
  rintro s ⟨_, hs2⟩
  rw [SetLike.mem_coe, Ideal.mem_primeCompl_iff, locBasic_conj_eq hinj hstar p, Ideal.mem_comap]
  exact hs2 _ (locBasic_sigma_spec hinj hstar s)
end Formalism.HermitianLatticesTheory
