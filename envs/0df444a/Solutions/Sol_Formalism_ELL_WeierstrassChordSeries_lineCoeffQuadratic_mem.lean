-- Prove2me | solution 1 for Formalism.ELL.WeierstrassChordSeries.lineCoeffQuadratic_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:26:30.888572+00:00
-- url     : https://prove2.me/submissions/5f9e91c6-1afb-4ab4-bfbb-aaba73e69971

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_two_mem
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_three_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL
open Formalism.ELL.WeierstrassChordSeries
variable {R : Type*} [CommRing R]
variable (T : Subring R)
namespace Formalism.ELL.WeierstrassChordSeries
theorem _root_.solution {a1 a2 a3 a4 a6 l n : R} (h1 : a1 ∈ T) (h2 : a2 ∈ T) (h3 : a3 ∈ T) (h4 : a4 ∈ T)
    (h6 : a6 ∈ T) (hl : l ∈ T) (hn : n ∈ T) : c2 a1 a2 a3 a4 a6 l n ∈ T := by
  unfold c2
  exact T.add_mem (T.add_mem (T.add_mem (T.add_mem (T.mul_mem h1 hl) (T.mul_mem h2 hn))
    (T.mul_mem h3 (T.pow_mem hl 2))) (T.mul_mem (T.mul_mem (T.mul_mem (two_mem T) h4) hl) hn))
    (T.mul_mem (T.mul_mem (T.mul_mem (three_mem T) h6) (T.pow_mem hl 2)) hn)
end Formalism.ELL.WeierstrassChordSeries
