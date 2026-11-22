-- Prove2me | solution 1 for DualVC.dual_vcdim_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:45:47.229804+00:00
-- url     : https://prove2.me/submissions/ce4d6cfb-df7f-49a3-88f8-1bd51a0b7a02

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_VCDimension
public import Mathlib.Algebra.Order.Module.Field
public import Mathlib.Data.EReal.Inv
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.MetricSpace.Bounded
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_DualVC
public import Theorems.Thm_DualVC_dual_shatters_imp_original_shatters

set_option autoImplicit true
@[expose] public section
public section
open Finset
universe u
open DualVC
variable {X : Type u} {C : ConceptClass X Bool}
namespace DualVC
theorem _root_.solution {d : ℕ} (hd : VCDim X C ≤ ↑d) :
    VCDim ↥C (DualClass X C) ≤ ↑(2 ^ (d + 1) - 1) := by
  apply iSup₂_le
  intro S hS
  by_contra hlt
  push Not at hlt
  have hge : 2 ^ (d + 1) ≤ S.card := by
    by_contra hlt'
    push Not at hlt'
    have hle : S.card ≤ 2 ^ (d + 1) - 1 := by omega
    apply absurd _ (not_le.mpr hlt)
    change (↑S.card : WithTop ℕ) ≤ ↑(2 ^ (d + 1) - 1)
    exact WithTop.coe_le_coe.mpr hle
  obtain ⟨T, hTcard, hTshat⟩ := dual_shatters_imp_original_shatters S hS hge
  have hvc : (↑(d + 1) : WithTop ℕ) ≤ VCDim X C :=
    le_iSup₂_of_le T hTshat (by exact_mod_cast hTcard.ge)
  have : d + 1 ≤ d := by exact_mod_cast le_trans hvc hd
  omega
end DualVC
