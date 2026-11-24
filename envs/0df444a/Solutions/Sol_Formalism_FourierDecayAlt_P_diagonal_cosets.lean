-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.diagonal_cosets
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:59:29.936828+00:00
-- url     : https://prove2.me/submissions/88d21ce4-b770-4779-ab7e-ba83547b411f

import Definitions.Def_Formalism_HermitianCurvature_StatementTA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagonalTopBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_TA1_isPt_PT

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.TA Finset Filter Topology TA1
open scoped InnerProductSpace ComplexConjugate
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.TA.DiagCosets := by
  classical
  intro E _ _ H _ _ W D Sg Φ w i s R hNZ hs hsi hi hA hcov huniq
  obtain ⟨_, hper, hdom, _⟩ := hA i s hs hsi hi
  have hHd : ∀ h ∈ PT Sg (i - s), IsPt (i - s) h := isPt_PT Sg hNZ (i - s)
  have key : ∀ t ∈ Sg i s, ∀ t0, t - t0 ∈ D.La i s →
      (Nst (Φ w) (PT Sg (i - s)) (offK (D.K i) s t t) s t t).re ≤
        (Nst (Φ w) (PT Sg (i - s)) (D.Th i s t0) s t t).re := by
    intro t ht t0 h0
    have e : D.Th i s t = D.Th i s t0 := by
      have := hper t0 (t - t0) h0
      rwa [add_sub_cancel] at this
    have h := form_self_nonneg (PT Sg (i - s)) _ (hdom t (PT Sg (i - s)) (hNZ _ _ t ht) hHd)
      (fun h => Φ w (Formalism.FourierDecayAlt.TA.ext h s t))
    have e2 : form (PT Sg (i - s))
        (fun h h' => D.Th i s t h h' - D.K i (Formalism.FourierDecayAlt.TA.ext h s t) (Formalism.FourierDecayAlt.TA.ext h' s t))
        (fun h => Φ w (Formalism.FourierDecayAlt.TA.ext h s t)) (fun h => Φ w (Formalism.FourierDecayAlt.TA.ext h s t)) =
        Nst (Φ w) (PT Sg (i - s)) (D.Th i s t) s t t -
          Nst (Φ w) (PT Sg (i - s)) (offK (D.K i) s t t) s t t := by
      simp only [form, Nst, offK, sub_mul, sum_sub_distrib]
    rw [e2, e, Complex.sub_re] at h
    linarith
  unfold Diag Cosets
  refine le_trans ?_ (le_of_eq (sum_comm' (s := Sg i s)
    (t := fun t => R.filter (fun t0 => t - t0 ∈ D.La i s)) ?_))
  · refine sum_le_sum fun t ht => ?_
    obtain ⟨t0, ht0, h0⟩ := hcov t ht
    have hf : R.filter (fun x => t - x ∈ D.La i s) = {t0} := by
      ext x
      simp only [mem_filter, mem_singleton]
      constructor
      · rintro ⟨hx, hxl⟩
        refine huniq x hx t0 ht0 ?_
        have := (D.La i s).sub_mem h0 hxl
        simpa using this
      · rintro rfl; exact ⟨ht0, h0⟩
    rw [hf, sum_singleton]
    exact key t ht t0 h0
  · intro t t0
    simp only [mem_filter]
    tauto
end Formalism.FourierDecayAlt.P
