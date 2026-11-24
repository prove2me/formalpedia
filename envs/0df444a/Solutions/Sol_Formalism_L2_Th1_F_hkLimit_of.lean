-- Prove2me | solution 1 for Formalism.L2.Th1.F.hkLimit_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:00:10.5736+00:00
-- url     : https://prove2.me/submissions/c15e9ff4-9cda-4633-aab3-ff3316578cf9

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_HkRowIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_EisensteinS2LimitFormulaOfHkLimit
import Theorems.Thm_Formalism_L2_Th1_F_Hk4_hk_zero
import Theorems.Thm_Formalism_L2_Th1_F_Hk4_cellOff_norm_le
import Theorems.Thm_Formalism_L2_Th1_F_Hk4_split
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_Ev_add
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hb


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
open Hk4
namespace Formalism.L2.Th1.F
theorem _root_.solution (h1 : HkSummable) (h2 : HkRowIntegral) (h3 : HkCellBound) (h4 : HkCellCont)
    (h5 : HkIntZero) (h6 : HkRowZero) (h7 : HkIntLimit) : HkLimit := by
  intro τ hτ
  obtain ⟨b, hb, hbd⟩ := h3 τ hτ
  have hmem : Set.Ioc (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioc_mem_nhdsGT one_pos

  have hcell : Tendsto (fun s : ℝ => ∑' p : ℤ × ℤ, cellOff τ s p) (𝓝[>] 0)
      (𝓝 (∑' p : ℤ × ℤ, cellOff τ 0 p)) := by
    refine tendsto_tsum_of_dominated_convergence hb.abs ?_ ?_
    · intro p
      by_cases hp : p.2 = 0
      · simp [cellOff, hp]
      · simpa [cellOff, hp] using h4 τ p hτ hp
    · filter_upwards [hmem] with s hs p
      exact cellOff_norm_le hbd hs.1.le hs.2 p

  have hI0 : (fun n : ℤ => if n = 0 then (0 : ℂ) else hkInt τ 0 n) = fun _ => 0 := by
    funext n
    by_cases hn : n = 0
    · simp [hn]
    · simp [hn, h5 τ n hτ hn]
  have hzero := split h2 hτ hb hbd le_rfl zero_le_one (by rw [hI0]; exact summable_zero)
  rw [hI0, tsum_zero, add_zero] at hzero
  simp only [hk_zero] at hzero
  rw [hzero]
  have hlim := (h6.add hcell).add (h7 τ hτ).2
  rw [← sub_eq_add_neg] at hlim
  refine hlim.congr' ?_
  filter_upwards [hmem] with s hs
  rw [← split h2 hτ hb hbd hs.1.le hs.2 ((h7 τ hτ).1 s hs.1)]
  have hS := h1 τ s hτ hs.1
  have hS' : Summable (fun q : ℤ × ℤ => hk s ((q.2 : ℂ) + (q.1 : ℂ) * τ)) :=
    (Equiv.prodComm ℤ ℤ).summable_iff.mpr hS
  rw [← (Equiv.prodComm ℤ ℤ).tsum_eq (fun p : ℤ × ℤ => hk s ((p.1 : ℂ) + (p.2 : ℂ) * τ))]
  exact hS'.tsum_prod.symm
end Formalism.L2.Th1.F
