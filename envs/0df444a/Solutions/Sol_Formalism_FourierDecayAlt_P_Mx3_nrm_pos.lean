-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx3.nrm_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:55:26.251338+00:00
-- url     : https://prove2.me/submissions/b7d0ae46-faa5-4b07-b3fe-e75c4dbbd240

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_tyInterlaces
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_rhoUp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_ord

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx3
namespace Formalism.FourierDecayAlt.P.Mx3
theorem _root_.solution (P : Par) (hP : P.OK) (l : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) (π π' : Ty P) (hU : Up P l π π') :
    0 < Nrm P l π := by
  have hI := tyInterlaces P hP π
  have hI' := tyInterlaces P hP π'
  have hr := rhoUp P l π π' hU l hl
  rw [if_pos rfl] at hr
  have b' := hI' l hl
  rw [hr] at b'
  have b := hI l hl
  obtain ⟨o1, o2, o3, o4⟩ := ord P.k P.u P.u' (rho P π) hI l hl
  unfold Nrm I.qpoly
  apply div_pos
  · rw [neg_mul, neg_neg]
    apply mul_pos (mul_pos hP.T_pos hP.T'_pos)
    apply Finset.prod_pos
    intro i hi
    by_cases h : i ≤ l
    · have := o1 i hi h
      apply mul_pos <;> linarith [b'.1, b'.2.1, this.1, this.2]
    · have := o2 i hi (by omega)
      apply mul_pos_of_neg_of_neg <;> linarith [b.2.2.1, b.2.2.2, this.1, this.2]
  · rw [← Finset.prod_mul_distrib]
    apply Finset.prod_pos
    intro j hj
    have hj1 := Finset.mem_of_mem_erase hj
    have hj2 := Finset.ne_of_mem_erase hj
    by_cases h : j < l
    · have := o3 j hj1 h
      apply mul_pos <;> linarith [b'.1, b'.2.1, this.1, this.2]
    · have := o4 j hj1 (by omega)
      apply mul_pos_of_neg_of_neg <;> linarith [b.2.2.1, b.2.2.2, this.1, this.2]
end Formalism.FourierDecayAlt.P.Mx3
