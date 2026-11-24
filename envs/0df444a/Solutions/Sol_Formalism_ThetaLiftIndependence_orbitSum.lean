-- Prove2me | solution 1 for Formalism.ThetaLiftIndependence.orbitSum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:32:46.25463+00:00
-- url     : https://prove2.me/submissions/fa75ab15-01b5-457c-8bfc-31990b02fafe

import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_OrbitSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.ThetaLiftIndependence
open MulAction
namespace Formalism.ThetaLiftIndependence
theorem _root_.solution : OrbitSum := by
  classical
  intro H X _ _ _ _ k _ _ F hF
  rw [finsum_eq_sum_of_fintype]
  rw [← Fintype.sum_equiv (selfEquivSigmaOrbits H X).symm (fun p => F p.2) F (fun p => rfl),
    Fintype.sum_sigma, Finset.mul_sum]
  refine Finset.sum_congr rfl fun o _ => ?_
  have hconst : ∀ y : orbit H (Quotient.out o), F y = F (Quotient.out o) := by
    rintro ⟨y, a, rfl⟩
    exact hF a _
  rw [Finset.sum_congr rfl (fun y _ => hconst y), Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  have hcard := card_orbit_mul_card_stabilizer_eq_card_group H (Quotient.out o)
  rw [Nat.card_eq_fintype_card, ← hcard]
  have h1 : (Fintype.card (orbit H (Quotient.out o)) : k) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨⟨_, mem_orbit_self (Quotient.out o)⟩⟩ :
      0 < Fintype.card (orbit H (Quotient.out o))).ne'
  have h2 : (Fintype.card (stabilizer H (Quotient.out o)) : k) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := stabilizer H (Quotient.out o))).ne'
  push_cast
  field_simp
end Formalism.ThetaLiftIndependence
