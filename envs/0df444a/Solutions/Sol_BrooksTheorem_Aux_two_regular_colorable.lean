-- Prove2me | solution 1 for BrooksTheorem.Aux.two_regular_colorable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:37:48.58625+00:00
-- url     : https://prove2.me/submissions/52239001-bd95-4624-b019-cc4de769aa75

module
public import Definitions.Def_BrooksLib_BrooksCore
public import Definitions.Def_BrooksLib_Cycle
public import Definitions.Def_BrooksLib_BrooksLow
public import Theorems.Thm_BrooksTheorem_Aux_cycle_iso
public import Theorems.Thm_BrooksTheorem_Aux_exists_cycle_equiv


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BrooksTheorem
open BrooksTheorem.Aux
variable {V : Type*} [Fintype V]
namespace BrooksTheorem.Aux
theorem _root_.solution (G : SimpleGraph V) (hconn : G.Connected)
    (h2 : ∀ v, (nb G v).card = 2) (hC : ∀ n, Odd n → IsEmpty (G ≃g cycleGraph n)) :
    G.Colorable 2 := by
  obtain ⟨n, e, he⟩ := exists_cycle_equiv G hconn h2
  obtain ⟨φ⟩ := cycle_iso G h2 n e he
  rcases Nat.even_or_odd (n + 3) with hev | hodd
  · refine ⟨Coloring.mk (fun v => (⟨(φ v).val % 2, Nat.mod_lt _ (by omega)⟩ : Fin 2)) ?_⟩
    intro u v huv hcol
    have hij : (cycleGraph (n + 3)).Adj (φ u) (φ v) := φ.map_adj_iff.2 huv
    rw [cycleGraph_adj] at hij
    have hmod : (φ u).val % 2 = (φ v).val % 2 := congrArg Fin.val hcol
    obtain ⟨k, hk⟩ := hev
    have hstep : ∀ a b : Fin (n + 3), a - b = 1 → a.val % 2 ≠ b.val % 2 := by
      intro a b hab
      have h1 : a = 1 + b := by rw [← hab]; exact (sub_add_cancel a b).symm
      have hv : a.val = (1 + b.val) % (n + 3) := by
        rw [h1, Fin.val_add, Fin.val_one]
      by_cases hb : 1 + b.val < n + 3
      · rw [Nat.mod_eq_of_lt hb] at hv; omega
      · have hbe : 1 + b.val = n + 3 := by have := b.isLt; omega
        rw [hbe, Nat.mod_self] at hv; omega
    rcases hij with h | h
    · exact hstep _ _ h hmod
    · exact hstep _ _ h hmod.symm
  · exact ((hC _ hodd).false φ).elim
end BrooksTheorem.Aux
