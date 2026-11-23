-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.D1.t_FirstBracket
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:15.222804+00:00
-- url     : https://prove2.me/submissions/9c69caae-7f6c-464a-ab5e-f6f6a4b5c6a0

import Definitions.Def_Formalism_HermitianCurvature_StatementPN
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalVolumePositivity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentBlockMeasure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormNormLemmas Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.D1
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
open Finset
open Classical
namespace Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.D1
theorem _root_.solution : FirstBracket := by
  intro Γ Nu w Pn occ S1 hw hP hcard hsum T hT
  have hmaps : ∀ x ∈ T, x.1 ∈ T.image Prod.fst := fun x hx => mem_image_of_mem _ hx
  rw [← sum_fiberwise_of_maps_to hmaps]
  refine le_trans (sum_le_sum (g := fun γ => (w γ)⁻¹) ?_) (hsum _ ?_)
  · intro γ hγ
    obtain ⟨x0, hx0, rfl⟩ := mem_image.mp hγ
    have hPpos : 0 < Pn x0.1 := hP _ _ (hT x0 hx0)
    have hc : ∑ x ∈ T with x.1 = x0.1, (w x.1 * Pn x.1)⁻¹ =
        ((T.filter (fun x => x.1 = x0.1)).card : ℝ) * (w x0.1 * Pn x0.1)⁻¹ := by
      rw [sum_congr rfl (g := fun _ => (w x0.1 * Pn x0.1)⁻¹)]
      · rw [sum_const, nsmul_eq_mul]
      · intro x hx
        rw [(mem_filter.mp hx).2]
    rw [hc]
    have hinj : Set.InjOn Prod.snd ((T.filter (fun x => x.1 = x0.1) : Finset (Γ × Nu)) : Set (Γ × Nu)) := by
      intro a ha b hb hab
      have ha' := (mem_filter.mp (mem_coe.mp ha)).2
      have hb' := (mem_filter.mp (mem_coe.mp hb)).2
      exact Prod.ext (ha'.trans hb'.symm) hab
    have hcd : ((T.filter (fun x => x.1 = x0.1)).card : ℝ) ≤ Pn x0.1 := by
      rw [← card_image_of_injOn hinj]
      apply hcard
      intro ν hν
      obtain ⟨y, hy, rfl⟩ := mem_image.mp hν
      have hy' := mem_filter.mp hy
      rw [← hy'.2]
      exact hT y hy'.1
    have hwpos := hw x0.1
    calc ((T.filter (fun x => x.1 = x0.1)).card : ℝ) * (w x0.1 * Pn x0.1)⁻¹
        ≤ Pn x0.1 * (w x0.1 * Pn x0.1)⁻¹ := by
          apply mul_le_mul_of_nonneg_right hcd; positivity
      _ = (w x0.1)⁻¹ := by field_simp
  · intro γ hγ
    obtain ⟨x0, hx0, rfl⟩ := mem_image.mp hγ
    exact ⟨x0.2, hT x0 hx0⟩
end Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.D1
