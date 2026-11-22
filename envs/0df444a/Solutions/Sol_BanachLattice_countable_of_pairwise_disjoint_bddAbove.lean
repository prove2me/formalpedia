-- Prove2me | solution 1 for BanachLattice.countable_of_pairwise_disjoint_bddAbove
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:18:57.45562+00:00
-- url     : https://prove2.me/submissions/a83c6776-137a-430a-a26f-b053f3ea9489

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderContinuous_Nakano
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderContinuous_MeyerNieberg
public import Theorems.Thm_BanachLattice_disjoint_bddAbove_tendsto_zero

set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
open BanachLattice
variable [BanachLattice X]
namespace BanachLattice
theorem _root_.solution [IsOrderContinuousNorm X]
    {S : Set X} (h0 : ∀ x ∈ S, x ≠ 0)
    (hd : S.Pairwise (fun x y => IsVLDisjoint x y))
    (hbd : BddAbove ((fun x => |x|) '' S)) :
    S.Countable := by
  -- Stratify by norm: `S_n = {x ∈ S | ‖x‖ ≥ 1/(n+1)}`.
  classical
  set T : ℕ → Set X := fun n => {x ∈ S | 1 / (n + 1 : ℝ) ≤ ‖x‖} with hT
  -- Each stratum is finite.
  have hTfin : ∀ n, (T n).Finite := by
    intro n
    by_contra hinf
    rw [Set.not_finite] at hinf
    let φ : ℕ ↪ ↥(T n) := hinf.natEmbedding
    let y : ℕ → X := fun k => ((φ k : ↥(T n)) : X)
    have hy_mem : ∀ k, y k ∈ S := fun k => (φ k).prop.1
    have hy_norm : ∀ k, 1 / (n + 1 : ℝ) ≤ ‖y k‖ := fun k => (φ k).prop.2
    have hy_inj : Function.Injective y := by
      intro a b hab
      have : φ a = φ b := Subtype.ext hab
      exact φ.injective this
    have hy_disj : Pairwise fun i j => IsVLDisjoint (y i) (y j) := by
      intro i j hij
      exact hd (hy_mem i) (hy_mem j) (fun h => hij (hy_inj h))
    have hy_bd : BddAbove (Set.range fun k => |y k|) := by
      obtain ⟨u, hu⟩ := hbd
      exact ⟨u, by rintro _ ⟨k, rfl⟩; exact hu ⟨y k, hy_mem k, rfl⟩⟩
    have htend : Filter.Tendsto y Filter.atTop (nhds 0) :=
      disjoint_bddAbove_tendsto_zero hy_disj hy_bd
    rw [Metric.tendsto_nhds] at htend
    have hpos : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
    have hev := htend (1 / (n + 1 : ℝ)) hpos
    rw [Filter.eventually_atTop] at hev
    obtain ⟨K, hK⟩ := hev
    have := hK K (le_refl K)
    rw [dist_zero_right] at this
    exact absurd (hy_norm K) (not_le.mpr this)
  -- `S = ⋃ n, T n` because every nonzero element has positive norm.
  have hcover : S ⊆ ⋃ n, T n := by
    intro x hx
    have hne : x ≠ 0 := h0 x hx
    have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hne
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hnorm
    exact Set.mem_iUnion.mpr ⟨n, hx, le_of_lt hn⟩
  refine (Set.Countable.mono hcover ?_)
  exact Set.countable_iUnion (fun n => (hTfin n).countable)
end BanachLattice
