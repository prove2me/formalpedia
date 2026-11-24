-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.cut_admissible_base
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:59:29.771729+00:00
-- url     : https://prove2.me/submissions/19e7d17b-6118-4ebd-bbc6-be513eb9795a

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModelWordsAssemble
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx9_eq_ofReal
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx9_star_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx9_far
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx9_xC_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx9_qC_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx9_ypt_im

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Matrix Finset Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.M
open Mx9
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.M.CutAdmBase := by
  intro hIS hIS2 hQP hQS hTy hR P hP l hl1 hlk S _ _ w hw
  obtain ⟨hnd, hpt, hpw⟩ := hw
  have key : ∀ (Y : ℝ), I.OnCut P.u P.u' l Y → ∀ e ∈ ({-1, 0, 1} : Finset ℝ),
      ((Y + e : ℝ) : ℂ) ∈ (startM P l).inv := by
    intro Y hY e he
    show ∀ π, xC P π _ ≠ 0
    intro π
    exact xC_ne hR P π (P.k - l) (Y + e) (hIS P.k P.u P.u' (rho P π) l Y hl1 hlk (hTy P hP π) hY e he)
  have qpos : ∀ (Y : ℝ), I.OnCut P.u P.u' l Y → (startM P l).q (Y : ℂ) ≠ 0 := by
    intro Y hY
    exact qC_ne hR P Y (hQP P.k P.u P.u' (rho P (ty0 P)) l Y P.T P.T' hl1 hlk (hTy P hP (ty0 P)) hY
      hP.T_pos hP.T'_pos)
  have qsh : ∀ (Y : ℝ), I.OnCut P.u P.u' l Y → (startM P l).q ((Y : ℂ) - 1) ≠ 0 := by
    intro Y hY
    have h := qC_ne hR P (Y - 1) (hQS P.k P.u P.u' (rho P (ty0 P)) l Y P.T P.T' hl1 hlk (hTy P hP (ty0 P)) hY
      hP.T_pos hP.T'_pos)
    push_cast at h
    exact h
  have key2 : ∀ (Y : ℝ), I.OnCut P.u P.u' l Y → ((Y + 2 : ℝ) : ℂ) ∈ (startM P l).inv := by
    intro Y hY
    show ∀ π, xC P π _ ≠ 0
    intro π
    exact xC_ne hR P π (P.k - l) (Y + 2) (hIS2 P.k P.u P.u' (rho P π) l Y hl1 hlk (hTy P hP π) hY 2 (by norm_num))
  refine ⟨hnd, fun a ha => star_eq (hpt a ha).1, fun a ha => ?_, hpw.imp fun h n hn => far h n hn⟩
  obtain ⟨him, hcut⟩ := hpt a ha
  have hz : ypt a = (((ypt a).re : ℝ) : ℂ) := eq_ofReal (ypt_im a him)
  rw [hz]
  rcases hcut with hc | hc
  · refine ⟨?_, ?_, fun _ => ?_, qpos _ hc⟩
    · convert key _ hc 0 (by norm_num) using 1 <;> push_cast <;> ring
    · convert key _ hc 1 (by norm_num) using 1 <;> push_cast <;> ring
    · convert key2 _ hc using 1 <;> push_cast <;> ring
  · refine ⟨?_, ?_, fun _ => ?_, ?_⟩
    · convert key _ hc (-1) (by norm_num) using 1 <;> push_cast <;> ring
    · convert key _ hc 0 (by norm_num) using 1 <;> push_cast <;> ring
    · convert key _ hc 1 (by norm_num) using 1 <;> push_cast <;> ring
    · convert qsh _ hc using 2 <;> push_cast <;> ring
end Formalism.FourierDecayAlt.P
