-- Prove2me | solution 1 for Formalism.L2.NCov.intAway_coeff_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:11:45.850285+00:00
-- url     : https://prove2.me/submissions/84b2586d-6330-4e7a-a22c-d3694978a99d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoverVal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.NCov
open Polynomial
variable {R : Type*} [CommRing R]
variable {q : R}
namespace Formalism.L2.NCov
theorem _root_.solution (hq : IsIntegral ℤ q) (s : Multiset R) (hs : ∀ μ ∈ s, IntAway q μ) (n : ℕ) :
    IntAway q ((s.map fun μ => X - C μ).prod.coeff n) := by
  let S := intAwaySubring hq
  have hmem : (s.map fun μ => X - C μ).prod ∈ Polynomial.liftsRing S.subtype := by
    refine Subring.multiset_prod_mem _ _ (fun P hP => ?_)
    obtain ⟨μ, hμ, rfl⟩ := Multiset.mem_map.mp hP
    refine Subring.sub_mem _ ?_ ?_
    · rw [← Polynomial.lifts_iff_liftsRing]; exact Polynomial.X_mem_lifts _
    · rw [← Polynomial.lifts_iff_liftsRing]; exact Polynomial.C_mem_lifts S.subtype ⟨μ, hs μ hμ⟩
  rw [← Polynomial.lifts_iff_liftsRing, Polynomial.lifts_iff_coeff_lifts] at hmem
  obtain ⟨c, hc⟩ := hmem n
  rw [← hc]
  exact c.2
end Formalism.L2.NCov
