-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx2.t_LatticeSumsJoint
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:24:15.168331+00:00
-- url     : https://prove2.me/submissions/1f36e9d2-1b33-4b9f-b8db-aaa9775b0712

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx2_t_MajIsProf
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx2_t_BoxSumLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx2
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped nonZeroDivisors ComplexConjugate
namespace Formalism.FourierDecayAlt.P.Jx2
theorem _root_.solution : LatticeSumsJoint := by
  intro hBS
  obtain ⟨C, hC1, hC⟩ := t_BoxSumLattice hBS
  refine ⟨C, hC1, ?_⟩
  intro E W _ _ _ D e aaD aaL Θ a hP hK ha hΘ hI
  have hcard : Fintype.card (InfinitePlace E) = D.f := by
    rw [← Fintype.card_congr e, Fintype.card_fin]
  have hΘ0 : 0 < Θ := by linarith
  have key : ∀ (aa : FractionalIdeal (𝓞 E)⁰ E) (large₂ : AddSubgroup E) (z : Fin D.f → ℝ) (c : ℝ),
      aa ≠ 0 → (∀ l ∈ large₂, l ∈ aa) → (∀ v, 0 ≤ z v) → 0 ≤ c → c ≤ a →
      ∏ v, z v ≤ (c / Θ) ^ D.f * √(FractionalIdeal.absNorm aa : ℝ) →
      ∀ L : Finset E, (∀ l ∈ L, l ∈ large₂ ∧ l ≠ 0) →
        ∑ l ∈ L, D.maj z l ≤ (C * a ^ ((D.K : ℝ) - 5 / 2) * Θ ^ (-((D.K : ℝ) - 5 / 2))) ^ D.f := by
    intro aa large₂ z c haa hLg hz hc hca hprod L hL
    have hre : ∏ w, z (e.symm w) = ∏ v, z v := Fintype.prod_equiv e.symm _ _ (fun w => rfl)
    have hcd : c / Θ ≤ a / Θ := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hca (inv_nonneg.mpr hΘ0.le)
    have hle : (c / Θ) ^ D.f ≤ (a / Θ) ^ D.f := by
      first
      | exact pow_le_pow_left (div_nonneg hc hΘ0.le) hcd _
      | exact pow_le_pow_left₀ (div_nonneg hc hΘ0.le) hcd _
    have hprod' : ∏ w, z (e.symm w) ≤
        (a / Θ) ^ Fintype.card (InfinitePlace E) * √(FractionalIdeal.absNorm aa : ℝ) := by
      rw [hre, hcard]
      exact hprod.trans (mul_le_mul_of_nonneg_right hle (Real.sqrt_nonneg _))
    have hLS0 := hC E aa large₂ (fun w => z (e.symm w)) D.K Θ a haa hLg (fun w => hz _) hK ha hΘ hprod'
    unfold TA.LatSum at hLS0
    have hLS := hLS0.2 L hL
    rw [hcard] at hLS
    calc ∑ l ∈ L, D.maj z l = ∑ l ∈ L, prof (fun w => z (e.symm w)) D.K l :=
          Finset.sum_congr rfl (fun l _ => t_MajIsProf E W D e hP z l)
      _ ≤ _ := hLS
  unfold IdealSizes at hI
  unfold TB.Data.LatticeSums
  constructor
  · intro i hi1 hi2 L hL
    obtain ⟨h1, h2, h3, h4⟩ := hI.1 i hi1 hi2
    exact key (aaD i) (D.Lad i) (D.szD i) 1 h1 h2 h3 zero_le_one ha h4 L hL
  · intro i s hs1 hs2 hi hne L hL
    obtain ⟨h1, h2, h3, h4⟩ := hI.2 (i - s + 1) s (by omega) hs1 (by omega) (by omega)
    exact key (aaL (i - s + 1) s) (D.Lap (i - s + 1) s) (D.szL (i - s + 1) s) a h1 h2 h3
      (by linarith) le_rfl h4 L hL
end Formalism.FourierDecayAlt.P.Jx2
