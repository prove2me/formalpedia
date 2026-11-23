-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.bddAbove_norm_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:28:58.111799+00:00
-- url     : https://prove2.me/submissions/f164c9c4-a5ce-4fb4-9f62-2355fb8e0637

import Definitions.Def_Formalism_GaussJetBounds_FrameJetEval
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormDetLeOneOfEntries
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Labels

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {R : Type} [NormedField R] {σ : Type} (Q : MvPolynomial σ R) :
    BddAbove (Set.range fun n : σ →₀ ℕ => ‖MvPolynomial.coeff n Q‖) := by
  classical
  have hfin : (Set.range fun n : σ →₀ ℕ => ‖MvPolynomial.coeff n Q‖).Finite := by
    refine Set.Finite.subset
      ((Q.support.image fun n => ‖MvPolynomial.coeff n Q‖).finite_toSet.insert 0) ?_
    rintro _ ⟨n, rfl⟩
    by_cases hn : n ∈ Q.support
    · right
      exact Finset.mem_coe.2 (Finset.mem_image_of_mem _ hn)
    · left
      simp only [MvPolynomial.notMem_support_iff.1 hn, norm_zero]
  exact hfin.bddAbove
end Formalism.DworkPowerSeriesWeights
