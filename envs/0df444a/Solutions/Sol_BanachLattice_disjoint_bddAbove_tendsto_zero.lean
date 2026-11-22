-- Prove2me | solution 1 for BanachLattice.disjoint_bddAbove_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:17:26.851545+00:00
-- url     : https://prove2.me/submissions/70624054-29e3-4e11-9be3-269757a47895

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderContinuous_Nakano
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderContinuous_MeyerNieberg
public import Theorems.Thm_BanachLattice_tendsto_of_monotone_bddAbove
public import Theorems.Thm_inf_le_inf_add_inf_of_nonneg


set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
open BanachLattice
variable [BanachLattice X]
namespace BanachLattice
theorem _root_.solution [IsOrderContinuousNorm X]
    {u : ℕ → X} (hd : Pairwise fun i j => IsVLDisjoint (u i) (u j))
    (hbd : BddAbove (Set.range fun n => |u n|)) :
    Filter.Tendsto u Filter.atTop (nhds 0) := by
  classical
  obtain ⟨w, hw⟩ := hbd
  -- Partial sums of `|u_k|`.
  let v : ℕ → X := fun m => ∑ k ∈ Finset.range m, |u k|
  have hv_nn : ∀ m, 0 ≤ v m := fun m =>
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hv_mono : Monotone v := by
    refine monotone_nat_of_le_succ (fun n => ?_)
    simp only [v, Finset.sum_range_succ]
    exact le_add_of_nonneg_right (abs_nonneg _)
  -- Partial sums are disjoint from later terms (by induction).
  have key : ∀ m k, m ≤ k → v m ⊓ |u k| = 0 := by
    intro m
    induction m with
    | zero =>
        intro k _
        simp [v]
    | succ n ih =>
        intro k hk
        have h1 : v n ⊓ |u k| = 0 := ih k (by omega)
        have h2 : |u n| ⊓ |u k| = 0 := hd (by omega)
        have heq : v (n + 1) = v n + |u n| := by
          simp [v, Finset.sum_range_succ]
        refine le_antisymm ?_
          (le_inf (by rw [heq]; exact add_nonneg (hv_nn n) (abs_nonneg _))
            (abs_nonneg _))
        rw [heq, inf_comm]
        calc |u k| ⊓ (v n + |u n|)
            ≤ |u k| ⊓ v n + |u k| ⊓ |u n| :=
              inf_le_inf_add_inf_of_nonneg (x := |u k|) (v n) (|u n|)
                (abs_nonneg _) (hv_nn n) (abs_nonneg _)
          _ = 0 := by rw [inf_comm, h1, inf_comm, h2, add_zero]
  -- Partial sums are bounded by `w`.
  have hv_le : ∀ m, v m ≤ w := by
    intro m
    induction m with
    | zero => simpa [v] using (abs_nonneg (u 0)).trans (hw ⟨0, rfl⟩)
    | succ n ih =>
        have hdisj : v n ⊓ |u n| = 0 := key n n (le_refl n)
        have heq : v (n + 1) = v n + |u n| := by
          simp [v, Finset.sum_range_succ]
        have hsup : v n + |u n| = v n ⊔ |u n| := by
          have := inf_add_sup (v n) (|u n|)
          rw [hdisj, zero_add] at this
          exact this.symm
        rw [heq, hsup]
        exact sup_le ih (hw ⟨n, rfl⟩)
  -- Use Nakano to get `v` converges in norm.
  obtain ⟨_, _, hv_tend⟩ :=
    tendsto_of_monotone_bddAbove hv_mono ⟨w, by rintro _ ⟨m, rfl⟩; exact hv_le m⟩
  have hv_cauchy : CauchySeq v := hv_tend.cauchySeq
  rw [Metric.cauchySeq_iff] at hv_cauchy
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N, hN⟩ := hv_cauchy ε hε
  refine Filter.eventually_atTop.mpr ⟨N, fun m hm => ?_⟩
  have hdist : dist (v (m + 1)) (v m) < ε := hN (m + 1) (by omega) m hm
  have heq : v (m + 1) - v m = |u m| := by
    simp [v, Finset.sum_range_succ]
  rw [dist_zero_right, ← norm_abs_eq_norm]
  rw [dist_eq_norm, heq] at hdist
  exact hdist
end BanachLattice
