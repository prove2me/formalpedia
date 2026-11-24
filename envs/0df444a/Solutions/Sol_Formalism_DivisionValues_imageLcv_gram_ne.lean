-- Prove2me | solution 1 for Formalism.DivisionValues.imageLcv_gram_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:16:39.481552+00:00
-- url     : https://prove2.me/submissions/083392e3-cfc0-4d89-ae2e-5ed3b467dd5c

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Theorems.Thm_Formalism_HN_height_gram_determinant
import Theorems.Thm_Formalism_HN_place_lattice_structure


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.DivisionValues
theorem _root_.solution [IsTotallyComplex K] {d : ℕ}
    (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (hX : ∀ v, IsUnit (X v).det)
    (e : Fin d → Fin d → K) (he : LinearIndependent K e) (v : InfinitePlace K) :
    (gram X v e).det.re ≠ 0 := by
  obtain ⟨h1, -⟩ := Formalism.HN.height_gram_determinant K (Fin d → K) (Fin d) (Pi.basisFun K (Fin d)) X hX d e he
  obtain ⟨-, -, hpos⟩ := Formalism.HN.place_lattice_structure K (Fin d → K) (Fin d) (Pi.basisFun K (Fin d)) X hX
    (Submodule.span (𝓞 K) (Set.range e)) (Submodule.fg_span (Set.finite_range e))
  rw [h1] at hpos
  exact (Finset.prod_ne_zero_iff.mp hpos.ne') v (Finset.mem_univ v)
end Formalism.DivisionValues
