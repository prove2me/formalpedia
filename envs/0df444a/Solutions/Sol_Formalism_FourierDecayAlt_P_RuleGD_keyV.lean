-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RuleGD.keyV
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:47:52.657796+00:00
-- url     : https://prove2.me/submissions/88494c11-2005-4384-b174-4de795f4ca89

import Definitions.Def_Formalism_HermitianCurvature_StatementR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleGD
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_map_ofFn_prod
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_tvprod_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RuleGD
open Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Matrix
variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ}
namespace Formalism.FourierDecayAlt.P.RuleGD
theorem _root_.solution (L : LevelData A r) (φ : A →+* A) (t : ℂ) (e : A)
    (hal : ∀ z, φ (algebraMap ℂ A z) = algebraMap ℂ A z)
    (hpb : ∀ l, φ (L.pb l) = L.pb l + algebraMap ℂ A t)
    (hcb : ∀ l, φ (L.cb l) = L.cb l) (hcbi : ∀ l, φ (L.cbi l) = L.cbi l)
    (hc : ∀ l, φ (L.c l) = L.c l) (hGG : φ L.GG = L.GG) (hz : φ L.ζ = L.ζ)
    (hGGi : φ L.GGi = L.GGi)
    (hnabs : φ L.nabs = L.nabs - algebraMap ℂ A t * (L.ζ * L.GGi) - e) (Y : ℂ) :
    φ (L.Ahatv Y) = L.Ahatv (Y - t) ∧
      φ (L.R0v Y) = L.R0v (Y - t) + L.Dr * L.GG * e * L.Avr (Y - t) := by
  have hT : (L.Tvprod Y).map φ = L.Tvprod (Y - t) := by
    apply tvprod_map
    intro l
    ext i j
    fin_cases i <;> fin_cases j <;> simp [LevelData.Tvl, hpb, hcb, hcbi, hal, map_sub]
    abel
  have hAr : φ (L.Avr Y) = L.Avr (Y - t) := by
    unfold LevelData.Avr; rw [← hT]; rfl
  have hBr : φ (L.Bvr Y) = L.Bvr (Y - t) := by
    unfold LevelData.Bvr; rw [← hT]; rfl
  have hDr : φ L.Dr = L.Dr := map_ofFn_prod φ L.c hc
  have hDrb : φ L.Drb = L.Drb := map_ofFn_prod φ L.cb hcb
  have hm0 : φ (L.m0 Y) = L.m0 (Y - t) + e := by
    have h2 : algebraMap ℂ A (Y - t - 1 / 2) = algebraMap ℂ A (Y - 1 / 2) - algebraMap ℂ A t := by
      rw [← map_sub]; congr 1; ring
    simp only [LevelData.m0, map_sub, map_neg, map_mul, hal, hnabs, hz, hGGi, h2, sub_mul]
    abel
  constructor
  · unfold LevelData.Ahatv; rw [map_mul, hDrb, hAr]
  · unfold LevelData.R0v
    rw [map_mul, map_mul, map_add, map_mul, hDr, hGG, hm0, hAr, hBr]
    simp only [add_mul, mul_add, mul_assoc]
    abel
end Formalism.FourierDecayAlt.P.RuleGD
