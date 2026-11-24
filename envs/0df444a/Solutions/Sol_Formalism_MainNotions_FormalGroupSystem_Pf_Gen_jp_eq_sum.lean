-- Prove2me | solution 1 for Formalism.MainNotions.FormalGroupSystem.Pf.Gen.jp_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:39:08.010554+00:00
-- url     : https://prove2.me/submissions/f85cc0f2-a8fb-491f-a26c-477081c1ca9d

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MultisetValuation_CoeffProdRename

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.FormalGroupSystem.Pf Formalism.MainNotions.FormalGroupSystem.Pf.Gen
open Finset
namespace Formalism.MainNotions.FormalGroupSystem.Pf.Gen
theorem _root_.solution {K A σ : Type} [CommRing K] [CommRing A] [Algebra K A] (P : MvPolynomial σ A)
    (f : MvPowerSeries σ K) (S : Finset (σ →₀ ℕ)) (hS : P.support ⊆ S) :
    jp P f = ∑ κ ∈ S, (((fac κ : ℕ) : K) * MvPowerSeries.coeff κ f) • MvPolynomial.coeff κ P := by
  unfold jp
  refine Finset.sum_subset hS ?_
  intro κ _ hκ
  have h0 : MvPolynomial.coeff κ P = 0 := by simpa [MvPolynomial.mem_support_iff] using hκ
  rw [h0, smul_zero]
end Formalism.MainNotions.FormalGroupSystem.Pf.Gen
