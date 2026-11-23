-- Prove2me | solution 1 for Formalism.SL.P.SphereChartDerivatives.sum_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:49:18.517832+00:00
-- url     : https://prove2.me/submissions/fe6431f6-5b9b-4cd4-8c4e-6ea09e28f8c9

import Mathlib
import Definitions.Def_Formalism_SobolevGaussianKernels_StatementSB
import Definitions.Def_Formalism_SobolevGaussianKernels_StatementLF
import Definitions.Def_Formalism_SobolevGaussianKernels_GaussianKernelBounds_HasDerivAtSphereChartLast
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_last
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_cast
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_last
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_cast

set_option autoImplicit false
open Formalism Formalism.SL Formalism.SL.P
open MeasureTheory Formalism.SL.SB
open scoped ContDiff
open Formalism.SL.P.SphereChartDerivatives
variable {n : ℕ}
namespace Formalism.SL.P.SphereChartDerivatives
theorem _root_.solution (f : Finset (Fin (n + 1)) → ℝ) :
    ∑ α : Finset (Fin (n + 1)), f α =
      ∑ β : Finset (Fin n), f (β.map Fin.castSuccEmb) +
        ∑ β : Finset (Fin n), f (insert (Fin.last n) (β.map Fin.castSuccEmb)) := by
  have hnot : Fin.last n ∉ (Finset.univ : Finset (Fin n)).map Fin.castSuccEmb := by
    simp [Fin.castSucc_ne_last]
  have hu : (Finset.univ : Finset (Finset (Fin (n + 1)))) =
      (insert (Fin.last n) ((Finset.univ : Finset (Fin n)).map Fin.castSuccEmb)).powerset := by
    rw [← Finset.cons_eq_insert _ _ hnot, ← Fin.univ_castSuccEmb, Finset.powerset_univ]
  rw [hu, Finset.sum_powerset_insert hnot]
  have key : ∀ h : Finset (Fin (n + 1)) → ℝ,
      ∑ t ∈ ((Finset.univ : Finset (Fin n)).map Fin.castSuccEmb).powerset, h t =
        ∑ β : Finset (Fin n), h (β.map Fin.castSuccEmb) := by
    intro h
    symm
    apply Finset.sum_nbij' (fun β => β.map Fin.castSuccEmb)
      (fun α => Finset.univ.filter (fun k => Fin.castSucc k ∈ α))
    · intro β _
      simp [Finset.map_subset_map]
    · intro α _
      simp
    · intro β _
      ext k
      simp
    · intro α hα
      rw [Finset.mem_powerset] at hα
      ext x
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Fin.coe_castSuccEmb]
      constructor
      · rintro ⟨k, hk, rfl⟩
        exact hk
      · intro hx
        obtain ⟨k, -, rfl⟩ := Finset.mem_map.1 (hα hx)
        exact ⟨k, hx, rfl⟩
    · intro β _
      rfl
  rw [key, key (fun t => f (insert (Fin.last n) t))]
end Formalism.SL.P.SphereChartDerivatives
