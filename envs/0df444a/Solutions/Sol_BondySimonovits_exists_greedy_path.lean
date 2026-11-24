-- Prove2me | solution 1 for BondySimonovits.exists_greedy_path
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:04:12.747716+00:00
-- url     : https://prove2.me/submissions/7c1c567d-d677-4afd-b9fb-9eaa180ee787

module
public import Mathlib
public import Definitions.Def_BondySimonovitsLib_BSBasic

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BondySimonovits
variable {V : Type*}
namespace BondySimonovits
theorem _root_.solution (K : SimpleGraph V) [DecidableRel K.Adj] (Y Z : Finset V) (D : ℕ)
    (hY : ∀ v ∈ Y, D ≤ (Y.filter (K.Adj v)).card) (w : V) (hw : w ∈ Y) (hwZ : w ∉ Z) :
    ∀ m, m + Z.card < D → ∃ q : ℕ → V, q 0 = w ∧ (∀ t < m, K.Adj (q t) (q (t + 1))) ∧
      (∀ t ≤ m, q t ∈ Y ∧ q t ∉ Z) ∧ (∀ s ≤ m, ∀ t ≤ m, q s = q t → s = t) := by
  classical
  intro m
  induction m with
  | zero =>
    intro _
    exact ⟨fun _ => w, rfl, fun t ht => absurd ht (Nat.not_lt_zero _),
      fun t _ => ⟨hw, hwZ⟩, fun s hs t ht _ => by omega⟩
  | succ m ih =>
    intro hm
    obtain ⟨q, hq0, hqa, hqY, hqi⟩ := ih (by omega)
    set T := Z ∪ (Finset.range (m + 1)).image q
    have hT : T.card < (Y.filter (K.Adj (q m))).card := by
      calc T.card ≤ Z.card + ((Finset.range (m + 1)).image q).card := Finset.card_union_le _ _
        _ ≤ Z.card + (m + 1) := by
          have := Finset.card_image_le (s := Finset.range (m + 1)) (f := q)
          simp only [Finset.card_range] at this
          omega
        _ < D := by omega
        _ ≤ _ := hY _ (hqY m le_rfl).1
    obtain ⟨u, hu, huT⟩ := Finset.exists_mem_notMem_of_card_lt_card hT
    simp only [Finset.mem_filter] at hu
    simp only [T, Finset.mem_union, Finset.mem_image, Finset.mem_range, not_or,
      not_exists, not_and] at huT
    refine ⟨fun t => if t ≤ m then q t else u, by simp [hq0], ?_, ?_, ?_⟩
    · intro t ht
      by_cases htm : t + 1 ≤ m
      · simp only [show t ≤ m by omega, htm, ite_true]
        exact hqa t (by omega)
      · have : t = m := by omega
        subst this
        simp only [le_refl, ite_true, show ¬ t + 1 ≤ t by omega, ite_false]
        exact hu.2
    · intro t ht
      by_cases htm : t ≤ m
      · simp only [htm, ite_true]; exact hqY t htm
      · simp only [htm, ite_false]; exact ⟨hu.1, huT.1⟩
    · intro s hs t ht hst
      by_cases hsm : s ≤ m <;> by_cases htm : t ≤ m <;>
        simp only [hsm, htm, ite_true, ite_false] at hst
      · exact hqi s hsm t htm hst
      · exact absurd hst (huT.2 s (by omega))
      · exact absurd hst.symm (huT.2 t (by omega))
      · omega
end BondySimonovits
