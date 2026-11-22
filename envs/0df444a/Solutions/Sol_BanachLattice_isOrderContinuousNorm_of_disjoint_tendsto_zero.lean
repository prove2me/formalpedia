-- Prove2me | solution 1 for BanachLattice.isOrderContinuousNorm_of_disjoint_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:20:12.987727+00:00
-- url     : https://prove2.me/submissions/0b7067d3-60a4-4997-9d7d-cd6785ccd7a0

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderContinuous_Nakano
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderContinuous_MeyerNieberg
public import Theorems.Thm_monotone_le_cauchySeq_iff_disjoint_tendsto_zero
public import Theorems.Thm_BanachLattice_isOrderContinuousNorm_of_isSigmaConditionallyCompleteLattice
public import Theorems.Thm_BanachLattice_isSigmaOrderContinuousNorm_of_mono_bddAbove_tendsto
public import Theorems.Thm_OrderConvergesTo_add


set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
open BanachLattice
variable [BanachLattice X]
namespace BanachLattice
theorem _root_.solution
    (h : ∀ {u : ℕ → X},
      Pairwise (fun i j => IsVLDisjoint (u i) (u j)) →
      BddAbove (Set.range fun n => |u n|) →
      Filter.Tendsto u Filter.atTop (nhds 0)) :
    IsOrderContinuousNorm X := by
  classical
  have hmono_tend :
      ∀ {u : ℕ → X}, Monotone u → BddAbove (Set.range u) →
        ∃ x, IsLUB (Set.range u) x ∧ Filter.Tendsto u Filter.atTop (nhds x) := by
    intro u hu_mono hu_bdd
    obtain ⟨b, hb⟩ := hu_bdd
    let v : ℕ → X := fun n => u n - u 0
    have hv0 : ∀ n, 0 ≤ v n := fun n => sub_nonneg.mpr (hu_mono (Nat.zero_le n))
    have hv_mono : Monotone v := fun m n hmn => sub_le_sub_right (hu_mono hmn) (u 0)
    have hv_le : ∀ n, v n ≤ b - u 0 := fun n => sub_le_sub_right (hb ⟨n, rfl⟩) (u 0)
    have hb0 : 0 ≤ b - u 0 := by simpa [v] using hv_le 0
    have hv_cauchy : CauchySeq v := by
      refine (monotone_le_cauchySeq_iff_disjoint_tendsto_zero hb0).2 ?_ hv0 hv_mono hv_le
      intro y hy_interval hy_disj
      refine h hy_disj ?_
      exact ⟨b - u 0, by
        rintro _ ⟨n, rfl⟩
        simpa [abs_of_nonneg (hy_interval n).1] using (hy_interval n).2⟩
    obtain ⟨a, hv_tend⟩ := cauchySeq_tendsto_of_complete hv_cauchy
    have hu_tend : Filter.Tendsto u Filter.atTop (nhds (u 0 + a)) := by
      have htend : Filter.Tendsto (fun n => u 0 + v n) Filter.atTop (nhds (u 0 + a)) :=
        tendsto_const_nhds.add hv_tend
      convert htend using 1
      · ext n
        simp [v, sub_eq_add_neg]
    exact ⟨u 0 + a, isLUB_of_tendsto_atTop hu_mono hu_tend, hu_tend⟩
  let banach : BanachLattice X := inferInstance
  let : SigmaConditionallyCompleteLattice X :=
    sigmaConditionallyCompleteLatticeOfMonoBddAboveTendsto hmono_tend
  let orderedAdd : IsOrderedAddMonoid X := {
    add_le_add_left := fun _ _ h _ => add_le_add_left h _
  }
  let : IsOrderedAddMonoid X := orderedAdd
  let sigmaOrderContinuous : IsSigmaOrderContinuousNorm X :=
    isSigmaOrderContinuousNorm_of_mono_bddAbove_tendsto hmono_tend
  have : IsSigmaOrderContinuousNorm X := sigmaOrderContinuous
  exact @isOrderContinuousNorm_of_isSigmaConditionallyCompleteLattice X
    inferInstance inferInstance orderedAdd banach sigmaOrderContinuous
end BanachLattice
