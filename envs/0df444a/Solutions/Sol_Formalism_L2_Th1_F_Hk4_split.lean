-- Prove2me | solution 1 for Formalism.L2.Th1.F.Hk4.split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:46:07.101186+00:00
-- url     : https://prove2.me/submissions/e99e7969-40f9-4388-83a4-65f94deb3b87

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_HkRowIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_EisensteinS2LimitFormulaOfHkLimit
import Theorems.Thm_Formalism_L2_Th1_F_Hk4_cellOff_norm_le
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_Ev_add
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hb
import Theorems.Thm_Formalism_G_LogP_hs2


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.Hk4
namespace Formalism.L2.Th1.F.Hk4
theorem _root_.solution (h2 : HkRowIntegral) {τ : ℂ} (hτ : τ.im ≠ 0) {b : ℤ × ℤ → ℝ} (hb : Summable b)
    (hbd : ∀ (s : ℝ) (p : ℤ × ℤ), 0 ≤ s → s ≤ 1 → p.2 ≠ 0 → ‖hkCell τ s p‖ ≤ b p)
    {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1)
    (hI : Summable (fun n : ℤ => if n = 0 then 0 else hkInt τ s n)) :
    ∑' n : ℤ, ∑' m : ℤ, hk s ((m : ℂ) + (n : ℂ) * τ)
      = ∑' m : ℤ, hk s (m : ℂ) + ∑' p : ℤ × ℤ, cellOff τ s p
        + ∑' n : ℤ, (if n = 0 then 0 else hkInt τ s n) := by
  have hC : Summable (cellOff τ s) :=
    Summable.of_norm_bounded hb.abs (cellOff_norm_le hbd h0 h1)
  have hC' : Summable (fun q : ℤ × ℤ => cellOff τ s (q.2, q.1)) :=
    (Equiv.prodComm ℤ ℤ).summable_iff.mpr hC
  have hCsum : ∑' p : ℤ × ℤ, cellOff τ s p = ∑' n : ℤ, ∑' m : ℤ, cellOff τ s (m, n) := by
    rw [← (Equiv.prodComm ℤ ℤ).tsum_eq (cellOff τ s)]
    exact hC'.tsum_prod
  have hG : Summable (fun n : ℤ => ∑' m : ℤ, cellOff τ s (m, n)) := hC'.prod
  have hrow : ∀ n : ℤ, ∑' m : ℤ, hk s ((m : ℂ) + (n : ℂ) * τ)
      = (if n = 0 then ∑' m : ℤ, hk s (m : ℂ) else 0) + ∑' m : ℤ, cellOff τ s (m, n)
        + (if n = 0 then 0 else hkInt τ s n) := by
    intro n
    by_cases hn : n = 0
    · subst hn
      simp [cellOff]
    · have hs1 : Summable (fun m : ℤ => cellOff τ s (m, n)) := hC'.prod_factor n
      have hs2 := (h2 τ s n hτ h0 hn).2
      have := hs1.hasSum.add hs2
      have he : (fun m : ℤ => cellOff τ s (m, n)
          + ∫ x in (0 : ℝ)..1, hk s ((m : ℂ) + (x : ℂ) + (n : ℂ) * τ))
          = fun m : ℤ => hk s ((m : ℂ) + (n : ℂ) * τ) := by
        funext m
        simp [cellOff, hkCell, hn]
      rw [he] at this
      rw [this.tsum_eq]
      simp [hn]
  have hR : Summable (fun n : ℤ => if n = 0 then ∑' m : ℤ, hk s (m : ℂ) else 0) :=
    (hasSum_ite_eq (0 : ℤ) _).summable
  rw [tsum_congr hrow, (hR.add hG).tsum_add hI, hR.tsum_add hG, tsum_ite_eq, hCsum]
end Formalism.L2.Th1.F.Hk4
