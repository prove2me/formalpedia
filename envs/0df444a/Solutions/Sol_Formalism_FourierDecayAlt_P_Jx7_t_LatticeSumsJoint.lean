-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx7.t_LatticeSumsJoint
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:24:15.422425+00:00
-- url     : https://prove2.me/submissions/1a047628-9f9c-4581-b5d4-14ba62f0aed6

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_t_MajIsProf
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_t_BoxSumLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx7
open scoped nonZeroDivisors
namespace Formalism.FourierDecayAlt.P.Jx7
theorem _root_.solution : LatticeSumsJoint := by
  intro hB
  obtain ⟨C, hC1, hC⟩ := t_BoxSumLattice hB
  refine ⟨C, hC1, ?_⟩
  intro E W _ _ _ D e aaD aaL Θ a hP hK ha hΘ hI
  have hcard : Fintype.card (InfinitePlace E) = D.f := by
    rw [← Fintype.card_congr e, Fintype.card_fin]
  have hpc : ∀ ρ : Fin D.f → ℝ, ∏ w, ρ (e.symm w) = ∏ v, ρ v := fun ρ => Equiv.prod_comp e.symm ρ
  have hΘ0 : 0 < Θ := by linarith
  have ha0 : 0 < a := by linarith
  have hK3 : (3 : ℝ) ≤ (D.K : ℝ) := by exact_mod_cast hK
  constructor
  · intro i hi1 hi2 L hL
    obtain ⟨h0, hsub, hnn, hsz⟩ := hI.1 i hi1 hi2
    have h1 := hC E (aaD i) (D.Lad i) (fun w => D.szD i (e.symm w)) D.K Θ 1 h0 hsub
      (fun w => hnn _) hK le_rfl (by linarith) (by rw [hpc, hcard]; exact hsz)
    have h2 := h1.2 L hL
    rw [hcard] at h2
    simp_rw [t_MajIsProf E W D e hP]
    refine h2.trans ?_
    apply pow_le_pow_left₀ (by positivity)
    rw [Real.one_rpow, mul_one]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have : 1 ≤ a ^ ((D.K : ℝ) - 5 / 2) := Real.one_le_rpow ha (by linarith)
    nlinarith
  · intro i s hs1 hsi hi hnot L hL
    obtain ⟨h0, hsub, hnn, hsz⟩ := hI.2 (i - s + 1) s (by omega) hs1 (by omega)
      (by rintro ⟨hb, hs⟩; exact hnot ⟨by omega, hs⟩)
    have h1 := hC E (aaL (i - s + 1) s) (D.Lap (i - s + 1) s)
      (fun w => D.szL (i - s + 1) s (e.symm w)) D.K Θ a h0 hsub
      (fun w => hnn _) hK ha hΘ (by rw [hpc, hcard]; exact hsz)
    have h2 := h1.2 L hL
    rw [hcard] at h2
    simp_rw [t_MajIsProf E W D e hP]
    exact h2
end Formalism.FourierDecayAlt.P.Jx7
