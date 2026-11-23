-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RuleGD.keyA
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:47:52.389096+00:00
-- url     : https://prove2.me/submissions/9346d8dc-a074-44ab-89d6-6368c9f617e2

import Definitions.Def_Formalism_HermitianCurvature_StatementR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleGD
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_map_ofFn_prod
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_tprod_map

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
    (hp : ∀ l, φ (L.p l) = L.p l + algebraMap ℂ A t)
    (hc : ∀ l, φ (L.c l) = L.c l) (hci : ∀ l, φ (L.ci l) = L.ci l)
    (hcb : ∀ l, φ (L.cb l) = L.cb l) (hGG : φ L.GG = L.GG) (hzb : φ L.ζb = L.ζb)
    (hGGi : φ L.GGi = L.GGi)
    (hnab : φ L.nab = L.nab + algebraMap ℂ A t * (L.ζb * L.GGi) - e) (Y : ℂ) :
    φ (L.Ahat Y) = L.Ahat (Y + t) ∧
      φ (L.R0 Y) = L.R0 (Y + t) + L.Drb * L.GG * e * L.Ar (Y + t) := by
  have hT : (L.Tprod Y).map φ = L.Tprod (Y + t) := by
    apply tprod_map
    intro l
    ext i j
    fin_cases i <;> fin_cases j <;> simp [LevelData.Tl, hp, hc, hci, hal, map_add]
    abel
  have hAr : φ (L.Ar Y) = L.Ar (Y + t) := by
    unfold LevelData.Ar; rw [← hT]; rfl
  have hBr : φ (L.Br Y) = L.Br (Y + t) := by
    unfold LevelData.Br; rw [← hT]; rfl
  have hDr : φ L.Dr = L.Dr := map_ofFn_prod φ L.c hc
  have hDrb : φ L.Drb = L.Drb := map_ofFn_prod φ L.cb hcb
  have hl0 : φ (L.l0 Y) = L.l0 (Y + t) + e := by
    have h2 : algebraMap ℂ A (Y + t + 1 / 2) = algebraMap ℂ A (Y + 1 / 2) + algebraMap ℂ A t := by
      rw [← map_add]; congr 1; ring
    simp only [LevelData.l0, map_sub, map_neg, map_mul, hal, hnab, hzb, hGGi, h2, add_mul]
    abel
  constructor
  · unfold LevelData.Ahat; rw [map_mul, hDr, hAr]
  · unfold LevelData.R0
    rw [map_mul, map_mul, map_add, map_mul, hDrb, hGG, hl0, hAr, hBr]
    simp only [add_mul, mul_add, mul_assoc]
    abel
end Formalism.FourierDecayAlt.P.RuleGD
