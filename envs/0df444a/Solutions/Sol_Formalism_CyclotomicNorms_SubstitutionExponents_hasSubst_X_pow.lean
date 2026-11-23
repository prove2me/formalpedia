-- Prove2me | solution 1 for Formalism.CyclotomicNorms.SubstitutionExponents.hasSubst_X_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:50.744897+00:00
-- url     : https://prove2.me/submissions/70719abf-ec3d-40ec-8d5a-6170b583533c

import Definitions.Def_Formalism_CyclotomicNorms_StatementA
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_SubstitutionBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.CyclotomicNorms
open Formalism.CyclotomicNorms.SubstitutionExponents
variable {r : ℕ}
namespace Formalism.CyclotomicNorms.SubstitutionExponents
theorem _root_.solution {k : Type*} [CommRing k] (n : Fin r → ℕ) (hn : ∀ j, n j ≠ 0) :
    MvPowerSeries.HasSubst (fun j => (PowerSeries.X : PowerSeries k) ^ n j) := by
  refine MvPowerSeries.hasSubst_of_constantCoeff_zero (fun j => ?_)
  rw [map_pow]
  have : MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries k) = 0 :=
    MvPowerSeries.constantCoeff_X _
  rw [this, zero_pow (hn j)]
end Formalism.CyclotomicNorms.SubstitutionExponents
