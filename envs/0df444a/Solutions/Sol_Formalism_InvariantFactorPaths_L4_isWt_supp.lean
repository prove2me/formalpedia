-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.isWt_supp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:59:50.758679+00:00
-- url     : https://prove2.me/submissions/100709e5-477b-4713-8555-c31d9c67b8cc

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_LatDefs
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_MulEarlyModP
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_Vanish
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_DischargeHeightBound
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_DerivativeKillsDegreeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.GM.DimensionMonotonicity Formalism.CountingSumsFrames Formalism.InvariantFactorPaths.PW MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {K s : ℕ}
variable (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (c : ℤ)
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (G : GlW ℚ_[p] (MvPolynomial (Fin (K + 1) × Fin (s + 1)) ℚ_[p]) (s + 1))
    (hcomp : ∀ μ x m, coeff m (G.comp μ x) = if wtX LL c m = μ then coeff m x else 0)
    (μ : Fin (s + 1) → ℤ) (x : MvPolynomial (Fin (K + 1) × Fin (s + 1)) ℚ_[p]) (hx : G.IsWt μ x) :
    ∀ m ∈ x.support, wtX LL c m = μ := by
  intro m hm
  by_contra hne
  have hx' : G.comp μ x = x := hx
  have h1 := hcomp μ x m
  rw [hx', if_neg hne] at h1
  exact (MvPolynomial.mem_support_iff.1 hm) h1
end Formalism.InvariantFactorPaths.L4
