-- Prove2me | solution 1 for FairSelling.exists_reducedN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:32:25.085052+00:00
-- url     : https://prove2.me/submissions/9de2c9be-3d5a-4bf4-b89b-2ea064db67ce

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
import Definitions.Def_RequestProject_MMSPartition
import Theorems.Thm_FairSelling_reduce_to_nsub1
import Theorems.Thm_FairSelling_exists_MMS_partition
import Theorems.Thm_FairSelling_sum_le_vbarSum


set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (n : ℕ) (hn : 0 < n) (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g) :
    ∃ (A : Fin n → Finset G) (s : Finset G) (q : Fin n → ℝ),
      ConfigN n w p (MMS n w p) A s q ∧ s.card ≤ n - 1 := by
  obtain ⟨ o, ho₁, ho₂, ho₃ ⟩ := exists_MMS_partition hn w p hw hp;
  obtain ⟨q, hq⟩ : ∃ q : Fin n → ℝ, (∀ i, 0 ≤ q i) ∧ (∑ i, q i = ∑ g ∈ o.sold, p g) ∧ (∀ i, MMS n w p ≤ vbarSum w p (o.kept i) + q i) := by
    refine' ⟨ fun i => o.money i + ( ∑ g ∈ o.sold, p g - ∑ j, o.money j ) / n, _, _, _ ⟩ <;> simp_all +decide [ Finset.sum_add_distrib, mul_div_cancel₀ _ ( by positivity : ( n : ℝ ) ≠ 0 ) ];
    · exact fun i => add_nonneg ( ho₁.2.2.1 i ) ( div_nonneg ( sub_nonneg.2 ( ho₁.2.2.2 ) ) ( Nat.cast_nonneg _ ) );
    · intro j; specialize ho₃ j; simp_all +decide [ util ] ;
      refine' le_trans ho₃ _;
      exact add_le_add ( sum_le_vbarSum _ _ _ ) ( le_add_of_nonneg_right <| div_nonneg ( sub_nonneg.2 <| ho₁.2.2.2 ) <| Nat.cast_nonneg _ );
  convert reduce_to_nsub1 n hn w p hp ( MMS n w p ) ( Finset.card o.sold ) ( fun i => o.kept i ) o.sold q _ _;
  · exact ⟨ ho₁.2.1, fun i => ho₁.1 i, ho₂, hq.1, hq.2.1, hq.2.2 ⟩;
  · rfl
end FairSelling
