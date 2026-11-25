-- Prove2me | solution 1 for ChvatalPosa.exists_nonadj_degree_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:20:40.143967+00:00
-- url     : https://prove2.me/submissions/1b87714c-dc14-445b-878b-d43cc982a4c8

module
public import Mathlib
public import Definitions.Def_MengerHamilton_Hamiltonian
public import Definitions.Def_ChvatalPosaLib_ChvatalPosa
public import Theorems.Thm_ChvatalPosa_card_le_degree_add_card
public import Theorems.Thm_Menger_Aux_Sep_symm


set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ChvatalPosa
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
omit [DecidableEq V]
namespace ChvatalPosa
theorem _root_.solution (H : SimpleGraph V) [DecidableRel H.Adj]
    (hn : 3 ≤ Fintype.card V) (h : ChvatalCond H) (hnc : ∃ u v, u ≠ v ∧ ¬ H.Adj u v) :
    ∃ u v, u ≠ v ∧ ¬ H.Adj u v ∧ Fintype.card V ≤ H.degree u + H.degree v := by
  classical
  by_contra hcon
  push Not at hcon
  set n := Fintype.card V with hn_def
  obtain ⟨a, b, hab, hnab⟩ := hnc
  set P := (univ : Finset (V × V)).filter (fun p => p.1 ≠ p.2 ∧ ¬ H.Adj p.1 p.2) with hP
  have hPne : P.Nonempty := ⟨(a, b), by simp [hP, hab, hnab]⟩
  obtain ⟨p, hp, hmax⟩ := exists_max_image P (fun p => H.degree p.1 + H.degree p.2) hPne
  simp only [hP, mem_filter, mem_univ, true_and] at hp hmax
  have hmax' : ∀ x y, x ≠ y → ¬ H.Adj x y →
      H.degree x + H.degree y ≤ H.degree p.1 + H.degree p.2 :=
    fun x y hxy hn => hmax (x, y) ⟨hxy, hn⟩
  obtain ⟨u, v, huv, hnuv, hle, hmx⟩ : ∃ u v, u ≠ v ∧ ¬ H.Adj u v ∧ H.degree u ≤ H.degree v ∧
      ∀ x y, x ≠ y → ¬ H.Adj x y → H.degree x + H.degree y ≤ H.degree u + H.degree v := by
    rcases le_total (H.degree p.1) (H.degree p.2) with h12 | h21
    · exact ⟨p.1, p.2, hp.1, hp.2, h12, hmax'⟩
    · refine ⟨p.2, p.1, Ne.symm hp.1, fun h' => hp.2 (h'.symm), h21, ?_⟩
      intro x y hxy hn'; have := hmax' x y hxy hn'; omega
  have hsum := hcon u v huv hnuv
  set i := H.degree u with hi_def
  rcases Nat.eq_zero_or_pos i with hi0 | hipos
  · -- `u` is isolated: use the condition with `i = 1`.
    have hu1 : 1 ≤ #{w | H.degree w ≤ 1} :=
      card_pos.2 ⟨u, by simp only [mem_filter, mem_univ, true_and]; omega⟩
    have h2 : 1 + 1 ≤ #{w | n - 1 ≤ H.degree w} := h 1 le_rfl (by omega) hu1
    obtain ⟨w, hw, hwu⟩ := exists_mem_ne (by omega : 1 < #{w | n - 1 ≤ H.degree w}) u
    simp only [mem_filter, mem_univ, true_and] at hw
    by_cases hadj : H.Adj w u
    · have : 0 < H.degree u := by
        rw [← card_neighborFinset_eq_degree]
        exact card_pos.2 ⟨w, (mem_neighborFinset _ _ _).2 (hadj.symm)⟩
      omega
    · have hsub : H.neighborFinset w ⊆ (univ.erase w).erase u := by
        intro x hx
        rw [mem_neighborFinset] at hx
        refine mem_erase.2 ⟨?_, mem_erase.2 ⟨?_, mem_univ _⟩⟩
        · rintro rfl; exact hadj hx
        · rintro rfl; exact hx.ne rfl
      have hc := card_le_card hsub
      rw [card_neighborFinset_eq_degree, card_erase_of_mem (mem_erase.2 ⟨hwu.symm, mem_univ _⟩),
        card_erase_of_mem (mem_univ _), card_univ] at hc
      omega
  · have h2i : 2 * i < n := by omega
    -- at least `i` vertices of degree `≤ i`
    have hA : i ≤ #{w | H.degree w ≤ i} := by
      have hS := card_le_degree_add_card H v (insert v ({w | H.degree w ≤ i} : Finset V)) (by
        intro w hw
        by_cases hwv : w = v
        · exact hwv ▸ mem_insert_self _ _
        · refine mem_insert_of_mem ?_
          simp only [mem_filter, mem_univ, true_and]
          have := hmx w v hwv (fun h' => hw (h'.symm))
          omega)
      have := card_insert_le v ({w | H.degree w ≤ i} : Finset V)
      omega
    have hB : i + 1 ≤ #{w | n - i ≤ H.degree w} := h i hipos h2i hA
    -- at least `n - i` vertices of degree `< n - i`
    have hT := card_le_degree_add_card H u {w | ¬ (n - i ≤ H.degree w)} (by
      intro w hw
      simp only [mem_filter, mem_univ, true_and]
      by_cases hwu : w = u
      · subst hwu; omega
      · have := hmx w u hwu (fun h' => hw (h'.symm))
        omega)
    have hsplit := card_filter_add_card_filter_not (s := (univ : Finset V))
      (fun w => n - i ≤ H.degree w)
    rw [card_univ] at hsplit
    omega
end ChvatalPosa
