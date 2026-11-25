-- Prove2me | solution 1 for CliqueMinors.color_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:41:06.491556+00:00
-- url     : https://prove2.me/submissions/8347d4ad-9429-4cd2-9edc-dd1d5fe870a8

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_GraphOps
public import Definitions.Def_CliqueMinorsLib_Minors
public import Theorems.Thm_CliqueMinors_deleteIncidenceSet_supp
public import Theorems.Thm_P2M_CliqueMinors_deleteIncidenceSet_le__01daa08c1827


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CliqueMinors
variable {V W : Type*}
open scoped Classical
variable [Fintype V]
namespace CliqueMinors
theorem _root_.solution (k : ℕ) (hk : 1 ≤ k) (P : SimpleGraph V → Prop)
    (hP : ∀ G G' : SimpleGraph V, G' ≤ G → P G → P G')
    (hlow : ∀ (G : SimpleGraph V) (S : Finset V), S.Nonempty → (∀ a b, G.Adj a b → a ∈ S) →
      P G → ∃ v ∈ S, G.degree v < k) :
    ∀ (n : ℕ) (G : SimpleGraph V) (S : Finset V), S.card = n →
      (∀ a b, G.Adj a b → a ∈ S) → P G → G.Colorable k := by
  intro n
  induction n with
  | zero =>
    intro G S hn hsupp _
    rw [Finset.card_eq_zero] at hn
    subst hn
    exact ⟨Coloring.mk (fun _ => ⟨0, hk⟩) fun h => absurd (hsupp _ _ h) (Finset.notMem_empty _)⟩
  | succ n ih =>
    intro G S hn hsupp hPG
    obtain ⟨v, hv, hdv⟩ := hlow G S (Finset.card_pos.1 (by omega)) hsupp hPG
    obtain ⟨C'⟩ := ih (G.deleteIncidenceSet v) (S.erase v)
      (by rw [Finset.card_erase_of_mem hv, hn]; rfl) (deleteIncidenceSet_supp hsupp)
      (hP _ _ (deleteIncidenceSet_le' G v) hPG)
    obtain ⟨col, -, hcol⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := (G.neighborFinset v).image C') (t := Finset.univ) (by
        rw [Finset.card_univ, Fintype.card_fin]
        exact Finset.card_image_le.trans_lt ((card_neighborFinset_eq_degree G v).trans_lt hdv))
    refine ⟨Coloring.mk (fun u => if u = v then col else C' u) fun {a b} hab => ?_⟩
    by_cases ha : a = v
    · subst ha
      have hb : b ≠ a := hab.ne.symm
      simp only [hb, ite_true, ite_false]
      exact fun h => hcol (Finset.mem_image.2 ⟨b, by simpa using hab, h.symm⟩)
    by_cases hb : b = v
    · subst hb
      simp only [ha, ite_true, ite_false]
      exact fun h => hcol (Finset.mem_image.2 ⟨a, by simpa using hab.symm, h⟩)
    simp only [ha, hb, ite_false]
    exact C'.valid (deleteIncidenceSet_adj.2 ⟨hab, ha, hb⟩)
end CliqueMinors
