-- Prove2me | solution 1 for Formalism.IndefR.Eqv.G5.adl_isOpen_nbhd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:04:59.114261+00:00
-- url     : https://prove2.me/submissions/fe450893-1e95-47c7-963c-7592713c0758

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_ExistsDenOfIsCompactAdele
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_IntAdCpctOpen
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_AdlEqZeroOfMemNbhd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism Formalism.IndefR Formalism.IndefR.Eqv Formalism.IndefR.Eqv.G5
variable {F : Type} [Field F] [NumberField F]
open scoped AdeleRing
namespace Formalism.IndefR.Eqv.G5
theorem _root_.solution : IsOpen (adlNbhd F) := by
  have h1 : IsOpen {y : InfiniteAdeleRing F | ∀ w, ‖y w‖ < 1} := by
    have e : {y : InfiniteAdeleRing F | ∀ w, ‖y w‖ < 1} = Set.pi Set.univ (fun _ => Metric.ball 0 1) := by
      ext y
      constructor
      · intro h w _
        simpa [mem_ball_zero_iff] using h w
      · intro h w
        simpa [mem_ball_zero_iff] using h w (Set.mem_univ w)
    rw [e]
    exact isOpen_set_pi Set.finite_univ (fun w _ => Metric.isOpen_ball)
  have h2 : IsOpen {y : FiniteAdeleRing (𝓞 F) F | ∀ v, y v ∈ v.adicCompletionIntegers F} := by
    apply RestrictedProduct.isOpen_forall_mem
    intro v
    first
      | exact IsDedekindDomain.HeightOneSpectrum.isOpen_adicCompletionIntegers F v
      | exact v.isOpen_adicCompletionIntegers F
      | exact Valued.isOpen_integer _
      | exact Valued.integer_isOpen _
  exact h1.prod h2
end Formalism.IndefR.Eqv.G5
