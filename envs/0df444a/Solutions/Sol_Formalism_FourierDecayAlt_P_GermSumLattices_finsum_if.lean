-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GermSumLattices.finsum_if
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:56:34.507771+00:00
-- url     : https://prove2.me/submissions/3d8c3415-4cca-4245-81dd-1f396fc9356f

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermSumLattices

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GermSumLattices
namespace Formalism.FourierDecayAlt.P.GermSumLattices
theorem _root_.solution {α : Type} {P : α → Prop} {inst : DecidablePred P} (hfin : {x | P x}.Finite)
    (G : α → ℂ) : ∑ᶠ x, (if P x then G x else 0) = ∑ x ∈ hfin.toFinset, G x := by
  rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset)]
  · apply Finset.sum_congr rfl
    intro x hx
    rw [if_pos (by simpa using hx)]
  · intro x hx
    simp only [Function.mem_support] at hx
    by_contra h
    apply hx
    rw [if_neg]
    simpa using h
end Formalism.FourierDecayAlt.P.GermSumLattices
