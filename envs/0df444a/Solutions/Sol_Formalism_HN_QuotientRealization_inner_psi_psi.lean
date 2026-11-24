-- Prove2me | solution 1 for Formalism.HN.QuotientRealization.inner_psi_psi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:42:20.98723+00:00
-- url     : https://prove2.me/submissions/dedfe2be-3167-44ef-82fb-fb144b3f6410

import Definitions.Def_Formalism_HarderNarasimhan_QuotRealize
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_QuotRealize

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
noncomputable section
open Formalism Formalism.HN
open Formalism.HN.QuotientRealization
variable {P ι : Type*} [Fintype P] [DecidableEq P] [Fintype ι]
namespace Formalism.HN.QuotientRealization
theorem _root_.solution (u v : P) (y z : ι → ℂ) :
    inner ℝ (PlaceDecomposition.psi u y) (PlaceDecomposition.psi (ι := ι) v z) =
      if u = v then (inner ℂ (WithLp.toLp 2 y : EuclideanSpace ℂ ι) (WithLp.toLp 2 z)).re
      else 0 := by
  rw [PiLp.inner_apply]
  by_cases h : u = v
  · subst h
    rw [if_pos rfl, PiLp.inner_apply, Complex.re_sum, Fintype.sum_prod_type, Finset.sum_eq_single u]
    · rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp [PlaceDecomposition.psi, Fin.sum_univ_two, Complex.mul_re]
    · intro w _ hw
      apply Finset.sum_eq_zero
      rintro ⟨i, k⟩ -
      simp [PlaceDecomposition.psi, hw]
    · intro hu
      exact absurd (Finset.mem_univ u) hu
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    rintro ⟨w, i, k⟩ -
    by_cases hw : w = u
    · subst hw
      simp [PlaceDecomposition.psi, h]
    · simp [PlaceDecomposition.psi, hw]
end Formalism.HN.QuotientRealization
