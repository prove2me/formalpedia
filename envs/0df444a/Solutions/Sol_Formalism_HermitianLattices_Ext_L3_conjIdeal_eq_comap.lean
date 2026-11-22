-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.conjIdeal_eq_comap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:43:28.108797+00:00
-- url     : https://prove2.me/submissions/0bd7c5a2-db3e-4027-81ad-03aec56f1ab0

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSubMemOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjO_coe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.HermitianLattices.Ext.L3
theorem _root_.solution (P : Ideal (𝓞 K)) :
    Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P.comap (conjO K) := by
  unfold Formalism.HermitianLatticesTheory.conjIdeal
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro r ⟨s, hs, hrs⟩
    have hr : conjO K r = s := by
      apply RingOfIntegers.ext
      rw [conjO_coe]
      have h2 : (r : K) = star (s : K) := hrs
      rw [h2, star_star]
    show conjO K r ∈ P
    rw [hr]
    exact hs
  · intro x hx
    apply Ideal.subset_span
    refine ⟨conjO K x, hx, ?_⟩
    show (x : K) = star ((conjO K x : 𝓞 K) : K)
    rw [conjO_coe, star_star]
end Formalism.HermitianLattices.Ext.L3
