-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.poisson_forms_agree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:47:46.437566+00:00
-- url     : https://prove2.me/submissions/38202036-72c4-4ad1-845a-887570c3e744

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PoissonJointFirstReduction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open MeasureTheory Formalism.H
open scoped FourierTransform ComplexConjugate nonZeroDivisors
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.J.PoissonAgree := by
  intro hA hT E W _ _ _ D H _ _ Φ ε i hε hi1 hi2 hwt hgram hPS
  intro w Hd kap hHd hk t0 T hTT B hB
  have hw : ((D.wt w : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hwt w)
  have e : i - 1 + 1 = i := Nat.sub_add_cancel hi1
  have hlev : ∀ h ∈ Hd, TB.level h = i - 1 := fun h hh => (hHd h hh).1
  have hpsd : TB.PSDOn Hd (fun h h' => kap h' h) := hT _ Hd kap ((hA _ Hd kap).1.mpr hk)
  have hT' : ∀ t ∈ T, t ≠ 0 ∧ t - t0 ∈ D.La i 1 := by
    intro t ht
    refine ⟨(hTT t ht).1, ?_⟩
    have h2 := (hTT t ht).2
    change t - t0 ∈ D.La (i - 1 + 1) 1 at h2
    rwa [e] at h2
  have hN : ∀ t, TA.Nst (Φ w) Hd kap 1 t t = D.Nst ε i 1 w Hd (fun h h' => kap h' h) t t := by
    intro t
    unfold TA.Nst TB.Data.Nst
    simp only [hgram]
    rw [Finset.sum_comm, eq_div_iff hw, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [TA.ext, TB.join]
    ring
  refine Eq.trans_le ?_ (hPS ε hε i hi1 hi2 w Hd hlev _ hpsd t0 B hB T hT')
  exact Finset.sum_congr rfl fun t _ => congrArg Complex.re (hN t)
end Formalism.FourierDecayAlt.P
