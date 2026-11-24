-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.A5.summable_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:39:37.030809+00:00
-- url     : https://prove2.me/submissions/b860edde-b14d-4283-aefe-8f58f90f30d6

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SummableSqGeom
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_mem_ebox
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_sum_ebox

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Finset
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.A5
variable {ι : Type*}
namespace Formalism.HermitianLattices.Ext.L3.A5
theorem _root_.solution {u : ι → ℕ → ℝ} (hu0 : ∀ i, u i 0 = 1) (hu : ∀ i j, 0 ≤ u i j) {t : ι → ℝ}
    (ht : Summable t) (hut : ∀ i J, ∑ j ∈ range (J + 1), u i j ≤ 1 + t i) :
    Summable fun v : ι →₀ ℕ => v.prod u := by
  classical
  have ht0 : ∀ i, 0 ≤ t i := by
    intro i
    have h := hut i 0
    simp [hu0] at h
    linarith
  apply summable_of_sum_le (c := Real.exp (∑' i, t i)) (fun v => by unfold Finsupp.prod; exact Finset.prod_nonneg fun i _ => hu i _)
  intro F
  have hsub : F ⊆ ebox (F.biUnion fun v => v.support) (fun i => F.sup fun v => v i) := by
    intro v hv
    rw [mem_ebox]
    exact ⟨fun i hi => Finset.mem_biUnion.mpr ⟨v, hv, hi⟩,
      fun i _ => Finset.le_sup (f := fun v : ι →₀ ℕ => v i) hv⟩
  calc ∑ v ∈ F, v.prod u
      ≤ ∑ v ∈ ebox (F.biUnion fun v => v.support) (fun i => F.sup fun v => v i), v.prod u :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun v _ _ => by unfold Finsupp.prod; exact Finset.prod_nonneg fun i _ => hu i _)
    _ = ∏ i ∈ F.biUnion (fun v => v.support), ∑ j ∈ range ((F.sup fun v => v i) + 1), u i j :=
        sum_ebox u hu0 _ _
    _ ≤ ∏ i ∈ F.biUnion (fun v => v.support), Real.exp (t i) := by
        apply Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun j _ => hu i j)
        intro i _
        calc _ ≤ 1 + t i := hut i _
          _ ≤ Real.exp (t i) := by linarith [Real.add_one_le_exp (t i)]
    _ = Real.exp (∑ i ∈ F.biUnion (fun v => v.support), t i) := (Real.exp_sum _ t).symm
    _ ≤ Real.exp (∑' i, t i) := Real.exp_le_exp.mpr (ht.sum_le_tsum _ (fun i _ => ht0 i))
end Formalism.HermitianLattices.Ext.L3.A5
