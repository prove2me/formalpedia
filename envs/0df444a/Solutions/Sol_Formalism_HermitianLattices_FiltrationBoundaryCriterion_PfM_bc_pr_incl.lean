-- Prove2me | solution 1 for Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfM.bc_pr_incl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:12:07.561798+00:00
-- url     : https://prove2.me/submissions/24ffeb9d-1415-4380-b3de-b63de6497816

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_OrbitPointsDistinct
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_BehrendSets_TranslateMean
import Definitions.Def_Formalism_BehrendSets_FinalE
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferenceStableUnderAction
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.FiltrationBoundaryCriterion
open Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfM
open Formalism.HermitianLattices.FiltrationBoundaryCriterion Formalism.FrobeniusOrbits NumberField IsDedekindDomain
open scoped TensorProduct
namespace Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfM
theorem _root_.solution {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (k : ℕ)
    (w : HeightOneSpectrum (𝓞 F)) (γ₀ : Matrix.GeneralLinearGroup (Fin k) E) :
    Formalism.UG.bc (Formalism.UG.prV (E := E) w) (Formalism.UG.bc (Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ₀) =
      Formalism.UG.bc (Formalism.UG.inclE (F := F) (w.adicCompletion F)) γ₀ := by
  ext i l
  simp [Formalism.UG.bc, Formalism.UG.prV, Formalism.UG.inclE]
end Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfM
