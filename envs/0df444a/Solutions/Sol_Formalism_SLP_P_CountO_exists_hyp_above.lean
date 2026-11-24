-- Prove2me | solution 1 for Formalism.SLP.P.CountO.exists_hyp_above
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:37:27.005845+00:00
-- url     : https://prove2.me/submissions/1a8faddb-db8d-4844-8251-8b75b2de0e27

import Definitions.Def_Formalism_HyperbolicPlaceProducts_Statement
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_CountO

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.SLP Formalism.SLP.P
open Formalism.SLP.P.CountO
variable {R : Type} [CommRing R] [IsDedekindDomain R]
namespace Formalism.SLP.P.CountO
theorem _root_.solution {X : Type} [AddCommGroup X] [Module R X] [Module.Finite R X]
    (N : Submodule R X) (hN : N ≠ ⊤) :
    ∃ P : Ideal R, P.IsMaximal ∧ ∃ L ∈ hyp P X, N ≤ L := by
  obtain ⟨L, hL, hNL⟩ := (eq_top_or_exists_le_coatom N).resolve_left hN
  have hs : IsSimpleModule R (X ⧸ L) := isSimpleModule_iff_isCoatom.mpr hL
  obtain ⟨P, hPm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hs
  refine ⟨P, hPm, L, ⟨?_, ?_⟩, hNL⟩
  · refine Submodule.smul_le.mpr fun r hr n _ => ?_
    rw [← Submodule.Quotient.mk_eq_zero, ← e.map_eq_zero_iff, Submodule.Quotient.mk_smul,
      map_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.mpr hr, zero_mul]
  · exact Nat.card_congr e.toEquiv
end Formalism.SLP.P.CountO
