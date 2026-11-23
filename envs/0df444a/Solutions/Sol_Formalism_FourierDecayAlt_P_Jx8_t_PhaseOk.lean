-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx8.t_PhaseOk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:22.966325+00:00
-- url     : https://prove2.me/submissions/baf03815-f885-4aa7-a6b6-8369e62de7b6

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OutsideSystemsBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx8_psd_congr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexOrder ComplexConjugate Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx8
namespace Formalism.FourierDecayAlt.P.Jx8
theorem _root_.solution : PhaseOk := by
  intro E α _ d S F hd hS
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hS
  have hdd : ∀ t, d t * conj (d t) = 1 := by
    intro t
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hd]; simp
  refine ⟨?_, ?_, h3, h4, ?_, h6⟩
  · intro t t' ht ht' h hh h' hh' hne
    refine h1 t t' ht ht' h hh h' hh' (fun h0 => hne ?_)
    show d t * conj (d t') * S.N t t' h h' = 0
    rw [h0, mul_zero]
  · intro t ht
    refine psd_congr (fun x _ y _ => ?_) (h2 t ht)
    show S.N t t x y = d t * conj (d t) * S.N t t x y
    rw [hdd, one_mul]
  · intro t ht
    refine psd_congr (fun x _ y _ => ?_) (h5 t ht)
    show S.Th t x y - S.N t t x y = S.Th t x y - d t * conj (d t) * S.N t t x y
    rw [hdd, one_mul]
end Formalism.FourierDecayAlt.P.Jx8
