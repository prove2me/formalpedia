-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.longBlockStep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:01:54.417829+00:00
-- url     : https://prove2.me/submissions/ae45da96-efb0-4496-861e-d54e15877e45

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FormDomination
import Theorems.Thm_Formalism_FourierDecayAlt_P_FormDomination_mean_dom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data Formalism.FourierDecayAlt.P.FormDomination
open Classical
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.TB.MultiStep := by
  intro E W _ D C₄ hG hK hW hA hB hC hv T ε hε i s hs hsi hi w hw hcnt hvol R hR M hM
  obtain ⟨θ, hθ, hest⟩ := hB ε hε i s hs hsi hi w hw hcnt hvol
  obtain ⟨⟨he0, he1⟩, -, -, hdom⟩ := hA i s (by omega) hsi hi
  have hY : ∀ h ∈ T.X (i - s), level h = i - s := fun h hh => ((T.isTower _ _).1 hh).1
  have hc : 0 ≤ C₄ ^ (D.f * s) * (∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s') :=
    mul_nonneg (pow_nonneg (by linarith) _) (Finset.prod_nonneg fun s' _ => hv _ _)
  have hd := hdom R hR (T.X (i - s)) hY
  have hd' : PSDOn (T.X (i - s)) (fun a b => (((1 + D.e i : ℝ)) : ℂ) * D.Kr (i - s) a b -
      ∑ t ∈ R, D.Th i s t a b) := by
    push_cast; exact hd
  calc ∑ t₀ ∈ R, ∑ t ∈ (T.Sg (i - s + 1) s).filter (fun t => t - t₀ ∈ D.La (i - s + 1) s),
            (D.Nst ε i s w (T.X (i - s)) (D.Th i s t₀) t t).re
      ≤ ∑ t₀ ∈ R, C₄ ^ (D.f * s) * (∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s') *
          ∑ w' ∈ D.Wb (D.cnt w + (s + 1) * D.K),
            θ w' * D.N0 ε (i - s) w' (T.X (i - s)) (D.Th i s t₀) := by
        refine Finset.sum_le_sum fun t₀ _ => ?_
        refine hest (T.X (i - s)) hY _ (hK.2 i s t₀ _) t₀ _ fun t ht => ?_
        rw [Finset.mem_filter] at ht
        exact ⟨fun h0 => T.zero_not_mem _ _ (h0 ▸ ht.1), ht.2⟩
    _ = C₄ ^ (D.f * s) * (∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s') *
          ∑ t₀ ∈ R, ∑ w' ∈ D.Wb (D.cnt w + (s + 1) * D.K),
            θ w' * D.N0 ε (i - s) w' (T.X (i - s)) (D.Th i s t₀) := by
        rw [Finset.mul_sum]
    _ ≤ C₄ ^ (D.f * s) * (∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s') * ((1 + D.e i) * M) :=
        mul_le_mul_of_nonneg_left
          (mean_dom D hG hW hε (i - s) _ θ hθ _ R (1 + D.e i) (by linarith) _ _ hd' M hM) hc
end Formalism.FourierDecayAlt.P
