-- Prove2me | solution 1 for Formalism.MainNotions.BridgeLemVR.conjO_mem_hcompl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:39:07.028804+00:00
-- url     : https://prove2.me/submissions/1af9ba57-04ea-461d-b576-e186ff55f0bb

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMassConstOne
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandA
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLemVR

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemVR
open NumberField Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.RankOne nonZeroDivisors
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.MainNotions.BridgeLemVR
theorem _root_.solution {p : Ideal (𝓞 K)} {s : 𝓞 K} (hs : s ∈ hcompl (K := K) p) :
    conjO K s ∈ hcompl (K := K) p := by
  have key : hcompl (K := K) p ≤ (hcompl (K := K) p).comap (conjO K : 𝓞 K →* 𝓞 K) := by
    conv_lhs => unfold hcompl
    rw [Submonoid.closure_le]
    intro s hs
    show conjO K s ∈ hcompl (K := K) p
    apply Submonoid.subset_closure
    refine ⟨hs.2 (conjO K s) rfl, fun t ht => ?_⟩
    have e : t = s := by
      apply RingOfIntegers.ext
      have : (t : K) = star (star (s : K)) := ht
      rw [star_star] at this
      exact this
    rw [e]
    exact hs.1
  exact key hs
end Formalism.MainNotions.BridgeLemVR
