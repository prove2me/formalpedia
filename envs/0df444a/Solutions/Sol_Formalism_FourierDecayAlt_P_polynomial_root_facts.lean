-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.polynomial_root_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:48:34.762864+00:00
-- url     : https://prove2.me/submissions/246d6293-0265-4fc1-ad8d-a7a485b1593a

import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HomogeneityNaturalDegree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants MvPolynomial
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open PartialDerivativeAlgebra
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C6.RootFacts := by
  intro s D' hs hD
  have hs0 : s ≠ 0 := by omega
  have hprim := Complex.isPrimitiveRoot_exp s hs0
  have hnd : (Polynomial.nthRoots s D').Nodup := hprim.nthRoots_nodup hD
  refine ⟨?_, ?_⟩
  · unfold G.rootSet
    rw [Multiset.toFinset_card_of_nodup hnd, hprim.card_nthRoots D']
    rw [if_pos (IsAlgClosed.exists_pow_nat_eq D' (by omega))]
  · intro z hz
    unfold G.rootSet at hz
    rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots (by omega)] at hz
    rw [← hz, norm_pow, one_div, Real.pow_rpow_inv_natCast (norm_nonneg z) hs0]
end Formalism.FourierDecayAlt.P
