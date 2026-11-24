-- Prove2me | solution 1 for Formalism.REAL.nPos_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:45:09.02562+00:00
-- url     : https://prove2.me/submissions/28cacec1-74ca-4e82-8abc-1b788b2dd9a9

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FirstSlotSliceSlotMixedCasimirZero
import Theorems.Thm_Formalism_REAL_re_inner_self_indexArray
import Theorems.Thm_Formalism_REAL_norm_sq_eq_sum_firstPositionSlice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution (hca : CasArr) (hs : OmSymSlice) (hp : OmPlus) : NPos := by
  intro V _ _ n ε E lam g u j hgl hu hk hfd hg F hF
  have hF' := hF
  simp only [Nset, Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap] at hF'
  obtain ⟨⟨h0, hsym⟩, hv⟩ := hF'
  obtain ⟨h1, h2⟩ := hca V n ε E (LamOf ε lam) u (j+1)
  rw [h1 hgl hk F h0]
  have hsum : ∑ i : Fin (j+1), ⟪F, OmS ε E i F⟫_ℂ = ((j:ℂ) + 1) * ⟪F, OmS ε E 0 F⟫_ℂ := by
    calc ∑ i : Fin (j+1), ⟪F, OmS ε E i F⟫_ℂ = ∑ _i : Fin (j+1), ⟪F, OmS ε E 0 F⟫_ℂ :=
          Finset.sum_congr rfl fun i _ => (hs V n ε E j F).1 hsym i
      _ = _ := by
          first
            | simp
            | (rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring)
  have hom : (g - 2 * (n:ℝ)) * ‖F‖ ^ 2 ≤ (⟪F, OmS ε E 0 F⟫_ℂ).re := by
    rw [(hs V n ε E j F).2, Complex.re_sum, norm_sq_eq_sum_firstPositionSlice, Finset.mul_sum]
    exact Finset.sum_le_sum fun α' _ => hp V n ε E lam g u hgl hu hk hfd hg _ (hv α')
  have hpos := h2 F
  rw [inner_add_right, inner_add_right, inner_smul_right, inner_smul_right, inner_sum, hsum]
  have e1 : (((ckv ε (LamOf ε lam) : ℝ) : ℂ) * ⟪F, F⟫_ℂ).re = ckv ε (LamOf ε lam) * ‖F‖ ^ 2 := by
    rw [Complex.re_ofReal_mul, re_inner_self_indexArray]
  have e2 : ((2:ℂ) * (((j:ℂ) + 1) * ⟪F, OmS ε E 0 F⟫_ℂ)).re =
      (2 * ((j:ℝ) + 1)) * (⟪F, OmS ε E 0 F⟫_ℂ).re := by
    rw [← Complex.re_ofReal_mul]
    congr 1
    push_cast
    ring
  rw [Complex.add_re, Complex.add_re, e1, e2]
  have h3 := mul_le_mul_of_nonneg_left hom (by positivity : (0:ℝ) ≤ 2 * ((j:ℝ) + 1))
  nlinarith [h3, hpos]
end Formalism.REAL
