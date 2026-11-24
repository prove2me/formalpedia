-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.sum_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:49:50.447157+00:00
-- url     : https://prove2.me/submissions/8ed5db79-373a-468e-9b6b-a9b52427ae9d

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementB
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.InvariantFactorPaths.L4
open Formalism.GM.M MvPolynomial Finset Formalism.CountingSumsFrames
section Gen
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}
private theorem single_add_sub_single_eq_of_one_le {σ : Type} (m : σ →₀ ℕ) (v : σ) (hv : 1 ≤ m v) :
    Finsupp.single v 1 + (m - Finsupp.single v 1) = m :=
  add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr hv)
end Gen
section Tools
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}
end Tools
section Last
variable (p : ℕ) [Fact p.Prime] {K r : ℕ} [NeZero r] (LL : Letters (K + 1)) (j : ℕ) (M : WithTop ℤ)
end Last
end Formalism.InvariantFactorPaths.L4
end

set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM.M MvPolynomial Finset Formalism.CountingSumsFrames
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution {σ : Type} [Fintype σ] [DecidableEq σ] (m : σ →₀ ℕ) (u v : σ) (hv : 1 ≤ m v) :
    ∑ w, (Finsupp.single u 1 + (m - Finsupp.single v 1) : σ →₀ ℕ) w = ∑ w, m w := by
  have h := single_add_sub_single_eq_of_one_le m v hv
  have e1 : ∀ x : σ, ∑ w, (Finsupp.single x 1 : σ →₀ ℕ) w = 1 := by
    intro x; simp [Finsupp.single_apply]
  calc ∑ w, (Finsupp.single u 1 + (m - Finsupp.single v 1) : σ →₀ ℕ) w
      = ∑ w, (Finsupp.single u 1 : σ →₀ ℕ) w + ∑ w, (m - Finsupp.single v 1 : σ →₀ ℕ) w := by
        simp only [Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib]
    _ = ∑ w, (Finsupp.single v 1 : σ →₀ ℕ) w + ∑ w, (m - Finsupp.single v 1 : σ →₀ ℕ) w := by rw [e1, e1]
    _ = ∑ w, m w := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun w _ => by rw [← Finsupp.add_apply, h]
end Formalism.InvariantFactorPaths.L4
