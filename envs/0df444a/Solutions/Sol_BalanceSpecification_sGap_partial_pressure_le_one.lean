-- Prove2me | solution 1 for BalanceSpecification.sGap_partial_pressure_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:06:11.346543+00:00
-- url     : https://prove2.me/submissions/7082bc39-f6be-4751-b2a7-b0da4909ef35

module
public import Definitions.Def_BalanceSpecificaton_SGapRenewal
public import Definitions.Def_BalanceSpecificaton_GrowthUpperBounds
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SGapEntropy

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open Filter Set
open scoped Topology
namespace BalanceSpecification
theorem _root_.solution {S : Set ℕ} {β : ℝ} (hβ : 0 < β)
    (hroot : HasSum (fun s : S => (β⁻¹)^(s.val + 1)) 1)
    (F : Finset ℕ) (hF : ∀ s ∈ F, s ∈ S) :
    ∑ s ∈ F, (β⁻¹)^(s + 1) ≤ 1 := by
  classical
  let e : ↥F ↪ S := ⟨fun s => ⟨s.val, hF s.val s.property⟩,
    fun a b h => Subtype.ext (congrArg (fun z : S => z.val) h)⟩
  calc
    _ = ∑ s ∈ Finset.univ.map e, (β⁻¹)^(s.val + 1) := by
      rw [Finset.sum_map]
      exact (Finset.sum_coe_sort F (fun s => (β⁻¹)^(s + 1))).symm
    _ ≤ ∑' s : S, (β⁻¹)^(s.val + 1) :=
      hroot.summable.sum_le_tsum _ (fun _ _ => pow_nonneg (inv_nonneg.mpr hβ.le) _)
    _ = 1 := hroot.tsum_eq
end BalanceSpecification
