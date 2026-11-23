-- Prove2me | solution 1 for Formalism.FT.SymmetricSeries.prod_X_perm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:43:29.814218+00:00
-- url     : https://prove2.me/submissions/3d3276c9-114c-4cd4-942b-5335f2050cea

import Definitions.Def_Formalism_ArtinHasse_Statement
import Definitions.Def_Formalism_ArtinHasse_ArtinHasseProofs_SymmSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.FT Formalism.FT.SymmetricSeries
variable {R : Type*} [CommRing R] {n : ℕ}
namespace Formalism.FT.SymmetricSeries
theorem _root_.solution (π : Equiv.Perm (Fin n)) (e : Fin n →₀ ℕ) :
    e.prod (fun s k => (MvPowerSeries.X (π s) : MvPowerSeries (Fin n) R) ^ k) =
      MvPowerSeries.monomial (e.mapDomain π) 1 := by
  induction e using Finsupp.induction with
  | zero => simp
  | single_add a b f ha hb ih =>
    rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _), ih,
      Finsupp.prod_single_index (h := fun s k => (MvPowerSeries.X (π s) : MvPowerSeries (Fin n) R) ^ k)
        (pow_zero _), MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial,
      mul_one, Finsupp.mapDomain_add, Finsupp.mapDomain_single]
end Formalism.FT.SymmetricSeries
