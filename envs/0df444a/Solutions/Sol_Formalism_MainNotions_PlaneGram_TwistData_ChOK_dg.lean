-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.ChOK.dg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:59:24.756891+00:00
-- url     : https://prove2.me/submissions/72b2ad7b-c629-430c-bcfd-9e25b688e021

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SumOnLetterApplyInl
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_costA_ok
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_costA_choose
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_digitPart_dg
import Theorems.Thm_Formalism_MainNotions_PlaneGram_approx_of_trunc
import Theorems.Thm_Formalism_MainNotions_PlaneGram_cge_add
import Theorems.Thm_Formalism_MainNotions_PlaneGram_cge_dg
import Theorems.Thm_Formalism_MainNotions_PlaneGram_dg_sub_fun
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_natCast_bound
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_zero_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K]
open Formalism.MainNotions.PlaneGram.TwistData
variable [CharZero K] (D : TwistData K) (v : AddValuation K (WithTop ℚ)) (p : ℕ)
variable {D v p}
variable (D p)
variable {D p}
namespace Formalism.MainNotions.PlaneGram.TwistData
namespace ChOK
theorem _root_.solution [NeZero D.r] (hV2 : V2 K) {θ : (j : Fin D.J) → Fin (D.nch j) → ℝ} {a : ℝ}
    {G : MvPolynomial (D.OL × Fin D.r) K} (h : D.ChOK v p θ a G) (f : D.EA → K)
    (hf0 : ∀ α, 0 ≤ v (f α)) (T : Finset (D.OL × Fin D.r → ℕ)) (lam : (D.OL × Fin D.r → ℕ) → K)
    (hlam : ∀ m ∈ T, 0 ≤ v (lam m) ∧ ∑ x, m x ≤ 6 * D.c)
    (hf : ∀ α : D.EA, ((D.c : ℕ) : WithTop ℚ) ≤ v (f α - binomComb T lam (fun x => α x))) :
    D.ChOK v p (fun j i => θ j i - 6 * D.c) a (Formalism.MainNotions.PlaneGram.dg f G) := by
  obtain ⟨G0, E, h1, h2, h3, h4⟩ := h
  have hC := D.costA_ok (K := K) p
  obtain ⟨g, hg0, hg1, hg2⟩ :=
    approx_of_trunc (v := v) hC (D.costA_choose p hV2) T lam hlam f hf
  refine ⟨Formalism.MainNotions.PlaneGram.dg g G0, Formalism.MainNotions.PlaneGram.dg (fun α => f α - g α) G0 + Formalism.MainNotions.PlaneGram.dg f E,
    ?_, ?_, ?_, ?_⟩
  · rw [h1, map_add, dg_sub_fun]; abel
  · have := cge_dg v (fun α => (vge_zero_iff v _).mpr (hg0 α)) h2
    rwa [zero_add] at this
  · refine cge_add v ?_ ?_
    · have := cge_dg v (fun α => (vge_natCast_bound v D.c _).mpr (hg1 α)) h2
      rwa [add_comm] at this
    · have := cge_dg v (fun α => (vge_zero_iff v _).mpr (hf0 α)) h3
      rwa [zero_add] at this
  · intro ρ j i
    rw [digitPart_dg]
    have := hg2 ρ (D.chainSet j i) (Set.mem_univ _) (θ j i) _ (h4 ρ j i)
    have e : θ j i - ((6 * D.c : ℕ) : ℝ) = θ j i - 6 * D.c := by push_cast; ring
    rwa [e] at this
end ChOK
end Formalism.MainNotions.PlaneGram.TwistData
