-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz5.tcritLower_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:55:25.962489+00:00
-- url     : https://prove2.me/submissions/25c54f21-a535-43f4-bd8c-406411e2eb36

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CriticalThresholdLowerBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_vand_v_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_prodb_ge_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_vandLamLower
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_key_nontop
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_key_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz5
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz5
theorem _root_.solution (hBr : BracketBound) (hNT : VandNonTop) (hTp : VandTop) (hEF : EdgeFactors)
    (hVW : VandWords) : TcritLower := by
  intro c r bb de ka rd g VV h hm hs hw hrd hka hg hFD
  have hk1 : 1 ≤ c.k := by have := h.hk; omega
  obtain ⟨hVu0, -, -⟩ := hVW c de de h hs.hvth hw hw
  have hkey : 0 ≤ cOne c bb * c.prodb / c.aeff ∧
      (cOne c bb * c.prodb / c.aeff) ^ c.k * Vand c.k (c.u de) ≤
        Vand (c.k - 1) c.v * c.prodb ^ (c.k - 1) / 2 := by
    cases htop : c.top
    · exact key_nontop hNT hEF c bb de h hs hw htop
    · exact key_top hTp c bb de h hs hw htop
  obtain ⟨hcP0, hcPk⟩ := hkey
  have hLam := (vandLamLower c h).2
  unfold FormalDegreeLower at hFD
  have hvp := vand_v_pos c h (c.k - 1)
  have hpb := prodb_ge_one c h
  have hpos : 0 < Vand (c.k - 1) c.v * c.prodb ^ (c.k - 1) := mul_pos hvp (pow_pos (by linarith) _)
  have hVV0 : 0 < VV := by linarith
  have hkV : (cOne c bb * c.prodb / c.aeff) ^ c.k ≤ VV / Vand c.k (c.u de) := by
    first
    | (rw [le_div_iff₀ hVu0]; linarith)
    | (rw [le_div_iff hVu0]; linarith)
  have hcPY : cOne c bb * c.prodb / c.aeff ≤ (VV / Vand c.k (c.u de)) ^ ((1:ℝ) / (c.k:ℝ)) := by
    have hk0 : c.k ≠ 0 := by omega
    calc cOne c bb * c.prodb / c.aeff
        = ((cOne c bb * c.prodb / c.aeff) ^ c.k) ^ ((1:ℝ) / (c.k:ℝ)) := by
          rw [one_div]
          first
          | exact (Real.pow_rpow_inv_natCast hcP0 hk0).symm
          | exact (Real.pow_nat_rpow_nat_inv hcP0 hk0).symm
      _ ≤ (VV / Vand c.k (c.u de)) ^ ((1:ℝ) / (c.k:ℝ)) :=
          Real.rpow_le_rpow (pow_nonneg hcP0 _) hkV (by positivity)
  have hrd0 : 0 < rd := by linarith
  have hka0 : 0 < ka := by rw [hka]; positivity
  have hg0 : 0 < g := by linarith [Real.pi_pos]
  have hA : 0 < (ka ^ (c.m - 1))⁻¹ * g ^ c.m := by positivity
  have hb := hBr c.k r c.m ka rd g VV (Vand c.k (c.u de)) hm hk1 hrd hka hg hVV0 hVu0
  obtain ⟨hom1, -, hT⟩ := hb
  rw [hT]
  have fin : ∀ A om Y cP : ℝ, 0 < A → 1 ≤ om → 0 ≤ cP → cP ≤ Y → A * cP ≤ A * om * Y := by
    intro A om Y cP hA' hom hc hY
    have hY0 : 0 ≤ Y := le_trans hc hY
    have h1 : cP ≤ om * Y := by nlinarith
    calc A * cP ≤ A * (om * Y) := mul_le_mul_of_nonneg_left h1 hA'.le
      _ = A * om * Y := by ring
  rw [show cOne c bb * g ^ c.m * (ka ^ (c.m - 1))⁻¹ * c.prodb / c.aeff =
      ((ka ^ (c.m - 1))⁻¹ * g ^ c.m) * (cOne c bb * c.prodb / c.aeff) by ring]
  exact fin _ _ _ _ hA hom1 hcP0 hcPY
end Formalism.FourierDecayAlt.P.Sz5
