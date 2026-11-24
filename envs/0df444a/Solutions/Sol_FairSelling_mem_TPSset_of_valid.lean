-- Prove2me | solution 1 for FairSelling.mem_TPSset_of_valid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:28:52.362951+00:00
-- url     : https://prove2.me/submissions/19dd4968-a4f3-46ca-91fd-61893d0fb21a

import Mathlib
import Definitions.Def_RequestProject_Selling
import Theorems.Thm_FairSelling_bundle_trunc_ge

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
namespace FairSelling
theorem _root_.solution (v p : G → ℝ) (hn : 0 < n)
    (hv : ∀ g, 0 ≤ v g) (hp : ∀ g, 0 ≤ p g)
    (o : Outcome G n) (hvalid : o.Valid p) (r : ℝ) (hr : 0 ≤ r)
    (hguar : ∀ j, r ≤ util v o j) :
    r ∈ TPSset n v p := by
  -- By `bundle_trunc_ge`, for each agent `j`, `r ≤ (∑ g ∈ o.kept j, min (v g) r) + o.money j`.
  have hbundle_trunc_ge : ∀ j, r ≤ (∑ g ∈ o.kept j, min (v g) r) + o.money j := by
    exact fun j => bundle_trunc_ge v hv o j r hr ( hvalid.2.2.1 j ) ( hguar j );
  -- Summing over the `n` agents (`Finset.univ : Finset (Fin n)`), and using `∑ j : Fin n, r = n * r` (`Finset.sum_const`, `Finset.card_univ`, `Fintype.card_fin`):
  have hsum_trunc_ge : (n : ℝ) * r ≤ ∑ g ∈ Finset.biUnion Finset.univ o.kept, min (v g) r + ∑ j, o.money j := by
    rw [ Finset.sum_biUnion ];
    · simpa [ Finset.sum_add_distrib ] using Finset.sum_le_sum fun i ( hi : i ∈ Finset.univ ) => hbundle_trunc_ge i;
    · exact fun i _ j _ hij => hvalid.2.1 i j hij;
  -- Now `min (v g) r ≤ max (p g) (min (v g) r)` and `p g ≤ max (p g) (min (v g) r)`, so
  have hsum_max_ge : ∑ g ∈ Finset.biUnion Finset.univ o.kept, min (v g) r + ∑ j, o.money j ≤ ∑ g ∈ Finset.biUnion Finset.univ o.kept, max (p g) (min (v g) r) + ∑ g ∈ o.sold, max (p g) (min (v g) r) := by
    refine' add_le_add ( Finset.sum_le_sum fun g hg => _ ) _;
    · exact le_max_right _ _;
    · exact le_trans hvalid.2.2.2 ( Finset.sum_le_sum fun _ _ => le_max_left _ _ );
  -- Also `U` and `o.sold` are disjoint (each `o.kept j` is disjoint from `o.sold` by `hks`, so their biUnion is; use `Finset.disjoint_biUnion_left` and `Disjoint.symm`).
  have hdisjoint : Disjoint (Finset.biUnion Finset.univ o.kept) o.sold := by
    exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by obtain ⟨ j, _, hj ⟩ := Finset.mem_biUnion.mp hx₁; exact Finset.disjoint_left.mp ( hvalid.1 j ) hx₂ hj;
  -- Hence `∑ g ∈ U, f g + ∑ g ∈ o.sold, f g = ∑ g ∈ U ∪ o.sold, f g` where `f g = max (p g) (min (v g) r)` (`Finset.sum_union` on disjoint sets).
  have hsum_union : ∑ g ∈ Finset.biUnion Finset.univ o.kept, max (p g) (min (v g) r) + ∑ g ∈ o.sold, max (p g) (min (v g) r) = ∑ g ∈ Finset.biUnion Finset.univ o.kept ∪ o.sold, max (p g) (min (v g) r) := by
    rw [ Finset.sum_union hdisjoint ];
  exact le_div_iff₀' ( by positivity ) |>.2 ( hsum_trunc_ge.trans <| hsum_max_ge.trans <| hsum_union.le.trans <| Finset.sum_le_sum_of_subset_of_nonneg ( Finset.subset_univ _ ) fun _ _ _ => le_max_of_le_left <| hp _ )
end FairSelling
