-- Prove2me | solution 1 for Formalism.L2.DIV.fk_map_bidet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:23:46.589119+00:00
-- url     : https://prove2.me/submissions/3031bbf2-8c0e-4669-ae2e-292c2af2e787

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefModLemmas
import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_FkMapInitMinor
import Theorems.Thm_Formalism_L2_DIV_fk_map_initMinor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open scoped Matrix
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.BasicNotions
namespace Formalism.L2.DIV
theorem _root_.solution {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {r n k : ℕ} (sz : Fin k → ℕ)
    (hsz : ∀ i, sz i ≤ n) (I : ∀ i, Fin (sz i) → Fin r) :
    map φ (Formalism.GradedWeylDivisibility.bideterminant R sz hsz I) = Formalism.GradedWeylDivisibility.bideterminant S sz hsz I := by
  unfold Formalism.GradedWeylDivisibility.bideterminant
  rw [map_prod]
  exact Finset.prod_congr rfl fun i _ => fk_map_initMinor φ _ _
end Formalism.L2.DIV
