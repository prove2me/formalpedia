-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RecursionWithDensities.A1.thetaDomination_d_of_axK_of_domMinA
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:00:53.645134+00:00
-- url     : https://prove2.me/submissions/bfc433cc-0769-42fe-9fde-400b9b125ae2

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequalitySplitBySize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionWithDensities
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_A1_psd_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_A1_psd_restr
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_A1_mk_eq_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_A1_G_cases
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_A1_G_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_A1_mem_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_A1_G_psd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RecursionWithDensities Formalism.FourierDecayAlt.P.RecursionWithDensities.A1
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TA Finset
open scoped ComplexConjugate InnerProductSpace
open Classical
variable {E : Type} [Field E] [DecidableEq E]
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.A1
theorem _root_.solution (D : TA.Data E) (Sg : ℕ → ℕ → Finset E) (Th) (hNZ : NZSg Sg) (hK : AxK D)
    (hD : TC.DomMinA D Sg Th) : ThetaDomination (D' D Sg Th) := by
  intro i s hs hsi hi
  have hG := G_psd D Sg Th hNZ hK hD i s hs hsi hi
  obtain ⟨h1, h2, h3⟩ := hD i s hs hsi hi
  refine ⟨fun t Hd _ => psd_restr (PT Sg (i - s)) Hd (hG (t : E ⧸ D.La i s)),
    fun t l hl => ?_, fun t Hd ht _ => ?_, fun R Hd hR _ => ?_⟩
  · show restr (PT Sg (i - s)) (G (D.La i s) (Sg i s) (Th i s) ((t + l : E) : E ⧸ D.La i s)) =
      restr (PT Sg (i - s)) (G (D.La i s) (Sg i s) (Th i s) (t : E ⧸ D.La i s))
    rw [(mk_eq_iff (D.La i s) (t + l) t).mpr (by have hl' : l ∈ D.La i s := hl; simpa using hl')]
  · by_cases htS : t ∈ Sg i s
    · obtain ⟨t₁, ht₁, hc₁, hG₁⟩ : ∃ t₁ ∈ Sg i s, ((t₁ : E ⧸ D.La i s) = (t : E ⧸ D.La i s)) ∧
          G (D.La i s) (Sg i s) (Th i s) (t : E ⧸ D.La i s) = Th i s t₁ := by
        rcases G_cases (D.La i s) (Sg i s) (Th i s) (t : E ⧸ D.La i s) with ⟨hn, _⟩ | h
        · exact absurd ⟨t, htS, rfl⟩ hn
        · exact h
      have hl : t₁ - t ∈ D.La i s := (mk_eq_iff _ _ _).mp hc₁
      refine psd_congr (fun h _ h' _ => ?_) (psd_restr (PT Sg (i - s)) Hd (h1 t htS))
      show restr _ _ h h' =
        restr (PT Sg (i - s)) (G (D.La i s) (Sg i s) (Th i s) (t : E ⧸ D.La i s)) h h' -
          restr (PT Sg i) (D.K i) (TA.ext h s t) (TA.ext h' s t)
      unfold restr
      by_cases hm : h ∈ PT Sg (i - s) ∧ h' ∈ PT Sg (i - s)
      · have he : TA.ext h s t ∈ PT Sg i ∧ TA.ext h' s t ∈ PT Sg i :=
          ⟨(mem_ext Sg i s hs hsi h t).mpr ⟨hm.1, htS⟩, (mem_ext Sg i s hs hsi h' t).mpr ⟨hm.2, htS⟩⟩
        rw [if_pos hm, if_pos hm, if_pos he, hG₁, h2 t₁ ht₁ t htS hl h hm.1 h' hm.2]
      · have he : ¬ (TA.ext h s t ∈ PT Sg i ∧ TA.ext h' s t ∈ PT Sg i) := fun he =>
          hm ⟨((mem_ext Sg i s hs hsi h t).mp he.1).1, ((mem_ext Sg i s hs hsi h' t).mp he.2).1⟩
        rw [if_neg hm, if_neg hm, if_neg he, sub_zero]
    · refine psd_congr (fun h _ h' _ => ?_)
        (psd_restr (PT Sg (i - s)) Hd (hG (t : E ⧸ D.La i s)))
      have he : ¬ (TA.ext h s t ∈ PT Sg i ∧ TA.ext h' s t ∈ PT Sg i) := fun he =>
        htS ((mem_ext Sg i s hs hsi h t).mp he.1).2
      show _ = restr (PT Sg (i - s)) (G (D.La i s) (Sg i s) (Th i s) (t : E ⧸ D.La i s)) h h' -
        restr (PT Sg i) (D.K i) (TA.ext h s t) (TA.ext h' s t)
      unfold restr
      rw [if_neg he, sub_zero]
  · obtain ⟨S', hS', -, hSd, hsum⟩ := G_sum (D.La i s) (Sg i s) (Th i s) R hR
    refine psd_congr (fun h _ h' _ => ?_) (psd_restr (PT Sg (i - s)) Hd (h3 S' hS' hSd))
    show _ = ((1 + (D' D Sg Th).e i : ℝ) : ℂ) * restr (PT Sg (i - s)) (D.K (i - s)) h h' -
      ∑ t ∈ R, restr (PT Sg (i - s)) (G (D.La i s) (Sg i s) (Th i s) (t : E ⧸ D.La i s)) h h'
    unfold restr
    by_cases hm : h ∈ PT Sg (i - s) ∧ h' ∈ PT Sg (i - s)
    · simp only [if_pos hm]
      rw [hsum h h']
      try rfl
    · simp only [if_neg hm, mul_zero, Finset.sum_const_zero, sub_zero]
end Formalism.FourierDecayAlt.P.RecursionWithDensities.A1
