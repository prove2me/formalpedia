-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.cut_admissible
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:37:39.991802+00:00
-- url     : https://prove2.me/submissions/c8f1a915-f99e-41de-9e8d-73af0938ff87

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModelWordsAssemble
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx9_eq_ofReal
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx9_star_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx9_far
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx9_xC_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx9_qC_ne

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
theorem _root_.solution : Formalism.FourierDecayAlt.M.CutAdm := by
  intro hIS hQP hQS hTy hR P hP l hl1 hlk S _ _ w hw
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
  refine ⟨hnd, fun a ha => star_eq (hpt a ha).1, fun a ha => ?_, hpw.imp fun h n hn => far h n hn⟩
  obtain ⟨him, hcut⟩ := hpt a ha
  have hz : a.pt = ((a.pt.re : ℝ) : ℂ) := eq_ofReal him
  rw [hz]
  refine ⟨?_, ?_, ?_, qpos _ hcut, qsh _ hcut⟩
  · convert key _ hcut 0 (by norm_num) using 1 <;> push_cast <;> ring
  · convert key _ hcut 1 (by norm_num) using 1 <;> push_cast <;> ring
  · convert key _ hcut (-1) (by norm_num) using 1 <;> push_cast <;> ring
end Formalism.FourierDecayAlt.P
