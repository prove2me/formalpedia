-- Prove2me | solution 1 for Formalism.L2.PjFree.mem_range_of_vV_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:39:35.979951+00:00
-- url     : https://prove2.me/submissions/db50beb9-a5ce-4c3e-adf9-c1b50fde7c80

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CoreProofs
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ExistsOfValILeOne
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllProofFree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.PjFree
open Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open scoped WithZero
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K'] [Algebra V K']
  [IsFractionRing V K']
namespace Formalism.L2.PjFree
theorem _root_.solution {x : K'} (h : 0 ≤ vV V x) : x ∈ Set.range (algebraMap V K') := by
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  have hv0 : HeightOneSpectrum.valuation K' (IsDiscreteValuationRing.maximalIdeal V) x ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr hx
  have hle : HeightOneSpectrum.valuation K' (IsDiscreteValuationRing.maximalIdeal V) x ≤ 1 := by
    rw [← WithZero.exp_log hv0, ← WithZero.exp_zero, WithZero.exp_le_exp]
    unfold vV valV at h
    linarith
  have key : ∀ w : HeightOneSpectrum V, w.valuation K' x ≤ 1 := by
    intro w
    have hw : w = IsDiscreteValuationRing.maximalIdeal V :=
      HeightOneSpectrum.ext (IsLocalRing.eq_maximalIdeal w.isMaximal)
    rw [hw]
    exact hle
  obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := V) (K := K') x key
  exact ⟨y, hy⟩
end Formalism.L2.PjFree
