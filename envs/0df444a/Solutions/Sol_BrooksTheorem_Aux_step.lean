-- Prove2me | solution 1 for BrooksTheorem.Aux.step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:42:47.972626+00:00
-- url     : https://prove2.me/submissions/aeb1676d-9121-4cc4-8591-dfdf6c707cdb

module
public import Definitions.Def_BrooksLib_Greedy
public import Definitions.Def_BrooksLib_BrooksCore
public import Theorems.Thm_BrooksTheorem_Aux_restr_adj
public import Theorems.Thm_BrooksTheorem_Aux_addE_adj
public import Theorems.Thm_BrooksTheorem_Aux_Proper_comp
public import Theorems.Thm_BrooksTheorem_Aux_Proper_mono
public import Theorems.Thm_BrooksTheorem_Aux_exists_perm2
public import Theorems.Thm_BrooksTheorem_Aux_glue
public import Theorems.Thm_BrooksTheorem_Aux_mu_addE_lt
public import Theorems.Thm_BrooksTheorem_Aux_deg_addE
public import Theorems.Thm_BrooksTheorem_Aux_clique_side
public import Theorems.Thm_BrooksTheorem_Aux_few_side
public import Theorems.Thm_BrooksTheorem_Aux_cut_case
public import Theorems.Thm_BrooksTheorem_Aux_greedy_reach
public import Theorems.Thm_BrooksTheorem_Aux_mem_nb
attribute [local simp] BrooksTheorem.Aux.mem_nb


attribute [local simp] BrooksTheorem.Aux.restr_adj

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BrooksTheorem
open BrooksTheorem.Aux
variable {V : Type*}
variable [Fintype V]
namespace BrooksTheorem.Aux
theorem _root_.solution {k : ℕ} (hk : 3 ≤ k) {H : SimpleGraph V} (ih : IHyp k H)
    (hdeg : ∀ v, (nb H v).card ≤ k) (hcf : H.CliqueFree (k + 1)) :
    ∃ f : V → Fin k, Proper H f := by
  classical
  by_cases hreg : ∃ y0, k ≤ (nb H y0).card
  swap
  · push Not at hreg
    obtain ⟨g, -, hg⟩ := greedy_reach H k hdeg ∅ (fun _ => ⟨0, by omega⟩) (by simp)
      (fun _ => True) (fun w _ _ => by simpa using hreg w) (fun w _ => ⟨0, trivial⟩)
    exact ⟨g, hg⟩
  obtain ⟨y0, hy0⟩ := hreg
  have hy0k : (nb H y0).card = k := le_antisymm (hdeg y0) hy0
  obtain ⟨x, hx, z, hz, hxz, hn⟩ : ∃ x ∈ nb H y0, ∃ z ∈ nb H y0, x ≠ z ∧ ¬ H.Adj x z := by
    by_contra hcon
    push Not at hcon
    apply hcf (insert y0 (nb H y0))
    rw [isNClique_iff]
    refine ⟨?_, ?_⟩
    · rw [coe_insert, isClique_insert]
      exact ⟨fun u hu v hv huv => hcon u hu v hv huv, fun u hu _ => mem_nb.1 hu⟩
    · rw [card_insert_of_notMem (by simp), hy0k]
  rw [mem_nb] at hx hz
  set P : Finset V := {x, z} with hPdef
  let f : V → Fin k := fun _ => ⟨0, by omega⟩
  let T : V → Prop := fun w => w = y0 ∨ (nb H w).card < k
  have hy0x : y0 ≠ x := H.ne_of_adj hx
  have hy0z : y0 ≠ z := H.ne_of_adj hz
  have hf : ∀ u ∈ P, ∀ v ∈ P, H.Adj u v → f u ≠ f v := by
    intro u hu v hv huv
    exfalso
    have hne := H.ne_of_adj huv
    simp only [hPdef, mem_insert, mem_singleton] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact hne rfl
    · exact hn huv
    · exact hn huv.symm
    · exact hne rfl
  have hT : ∀ w ∉ P, T w → (((nb H w).filter (· ∈ P)).image f).card +
       ((nb H w).filter (· ∉ P)).card < k := by
    intro w _ hw
    have himg := card_image_le (s := (nb H w).filter (· ∈ P)) (f := f)
    have himg1 : (((nb H w).filter (· ∈ P)).image f).card ≤ 1 := by
      apply card_le_one.2
      intro a ha b hb
      simp only [mem_image] at ha hb
      obtain ⟨_, _, rfl⟩ := ha
      obtain ⟨_, _, rfl⟩ := hb
      rfl
    have hsplit := card_filter_add_card_filter_not (s := nb H w) (fun u => u ∈ P)
    rcases hw with rfl | hw
    · have h2 : ({x, z} : Finset V) ⊆ (nb H w).filter (· ∈ P) := by
        intro u hu
        simp only [mem_insert, mem_singleton] at hu
        rcases hu with rfl | rfl
        · simp [hPdef, hx]
        · simp [hPdef, hz]
      have := card_le_card h2
      rw [card_pair hxz] at this
      omega
    · omega
  by_cases hall : ∀ w ∉ P, ∃ n, near H P T n w
  · obtain ⟨g, -, hg⟩ := greedy_reach H k hdeg P f hf T hT hall
    exact ⟨g, hg⟩
  push Not at hall
  obtain ⟨b, hbP, hbn⟩ := hall
  set B : Set V := {v | v ∉ P ∧ ∀ n, ¬ near H P T n v} with hBdef
  have hBcl : ∀ u ∈ B, ∀ v, H.Adj u v → v ∈ B ∨ v = x ∨ v = z := by
    intro u hu v huv
    by_cases hvP : v ∈ P
    · right; simpa [hPdef] using hvP
    · left
      exact ⟨hvP, fun n hn => hu.2 (n + 1) ⟨v, huv, hvP, hn⟩⟩
  have hy0B : y0 ∉ B := fun h => h.2 0 (Or.inl rfl)
  have hxB : x ∉ B := fun h => h.1 (by simp [hPdef])
  have hzB : z ∉ B := fun h => h.1 (by simp [hPdef])
  have hbB : b ∈ B := ⟨hbP, hbn⟩
  have hbdeg : k ≤ (nb H b).card := by
    by_contra hcon
    exact hbn 0 (Or.inr (by omega))
  obtain ⟨bn, hbn'⟩ : (nb H b).Nonempty := card_pos.1 (by omega)
  rw [mem_nb] at hbn'
  by_cases hxB' : ∃ bx ∈ B, H.Adj x bx
  swap
  · push Not at hxB'
    refine cut_case ih hdeg hcf B hxz hxB hx.symm ?_ hbB hbn'
    intro u hu v huv
    rcases hBcl u hu v huv with h | rfl | h
    · exact Or.inl h
    · exact absurd huv.symm (hxB' u hu)
    · exact Or.inr h
  by_cases hzB' : ∃ bz ∈ B, H.Adj z bz
  swap
  · push Not at hzB'
    refine cut_case ih hdeg hcf B hxz.symm hzB hz.symm ?_ hbB hbn'
    intro u hu v huv
    rcases hBcl u hu v huv with h | h | rfl
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd huv.symm (hzB' u hu)
  obtain ⟨bx, hbxB, hbx⟩ := hxB'
  obtain ⟨bz, hbzB, hbz⟩ := hzB'
  set S1 : Set V := Bᶜ with hS1
  set S2 : Set V := {v | v ∈ B ∨ v = x ∨ v = z} with hS2
  have hedge : ∀ u v, H.Adj u v → (u ∈ S1 ∧ v ∈ S1) ∨ (u ∈ S2 ∧ v ∈ S2) := by
    intro u v h
    by_cases hu : u ∈ B
    · exact Or.inr ⟨Or.inl hu, hBcl u hu v h⟩
    · by_cases hv : v ∈ B
      · exact Or.inr ⟨hBcl v hv u h.symm, Or.inl hv⟩
      · exact Or.inl ⟨hu, hv⟩
  have hinter : ∀ v ∈ S1, v ∈ S2 → v = x ∨ v = z := by
    intro v hv1 hv2
    rcases hv2 with hv2 | hv2
    · exact absurd hv2 hv1
    · exact hv2
  have hzS1 : z ∈ S1 := hzB
  have hzS2 : z ∈ S2 := Or.inr (Or.inr rfl)
  have hbxS1 : bx ∉ S1 := fun h => h hbxB
  have hbzS1 : bz ∉ S1 := fun h => h hbzB
  have hy0S2 : y0 ∉ S2 := by
    rintro (h | h | h)
    · exact hy0B h
    · exact hy0x h
    · exact hy0z h
  -- gluing two colourings in which `x` and `z` share a colour
  have same_glue : ∀ c1 c2 : V → Fin k, Proper (restr H S1) c1 → c1 x = c1 z →
      Proper (restr H S2) c2 → c2 x = c2 z → ∃ g : V → Fin k, Proper H g := by
    intro c1 c2 h1 e1 h2 e2
    refine glue H S1 S2 hedge c1 (Equiv.swap (c2 x) (c1 x) ∘ c2) h1 (h2.comp _) ?_
    intro v hv1 hv2
    rcases hinter v hv1 hv2 with rfl | rfl
    · simp
    · simp [← e1, ← e2]
  by_cases hc1 : (restr H S1 ⊔ edge x z).CliqueFree (k + 1)
  · by_cases hc2 : (restr H S2 ⊔ edge x z).CliqueFree (k + 1)
    · obtain ⟨c1, h1⟩ := ih _ (mu_addE_lt H S1 hxz hzS1 hbx hbxS1 hbz hbzS1)
        (deg_addE hdeg S1 hbx hbxS1 hbz hbzS1) hc1
      obtain ⟨c2, h2⟩ := ih _ (mu_addE_lt H S2 hxz hzS2 hx.symm hy0S2 hz.symm hy0S2)
        (deg_addE hdeg S2 hx.symm hy0S2 hz.symm hy0S2) hc2
      have hexz : (restr H S1 ⊔ edge x z).Adj x z := addE_adj.2 (Or.inr ⟨Or.inl ⟨rfl, rfl⟩, hxz⟩)
      have hexz2 : (restr H S2 ⊔ edge x z).Adj x z :=
        addE_adj.2 (Or.inr ⟨Or.inl ⟨rfl, rfl⟩, hxz⟩)
      obtain ⟨σ, hσ1, hσ2⟩ := exists_perm2 (h2 x z hexz2) (h1 x z hexz)
      refine glue H S1 S2 hedge c1 (σ ∘ c2) (h1.mono le_sup_left)
        ((h2.mono le_sup_left).comp σ) ?_
      intro v hv1 hv2
      rcases hinter v hv1 hv2 with rfl | rfl
      · simp [hσ1]
      · simp [hσ2]
    · obtain ⟨⟨c2, h2, e2⟩, ux, uz⟩ := clique_side hk ih hdeg hcf S2 hxz hn hx.symm hy0S2
        hz.symm hy0S2 hc2
      obtain ⟨c1, h1, e1⟩ := few_side hk ih hdeg hcf S1 (qx := y0) (qz := y0) hn hbx
        (fun v hv1 hvz hxv => ux v (fun hv2 => by
          rcases hinter v hv1 hv2 with rfl | rfl
          · exact H.loopless.irrefl _ hxv
          · exact hvz rfl) hxv)
        (fun v hv1 hvx hzv => uz v (fun hv2 => by
          rcases hinter v hv1 hv2 with rfl | rfl
          · exact hvx rfl
          · exact H.loopless.irrefl _ hzv) hzv)
      exact same_glue c1 c2 h1 e1 h2 e2
  · obtain ⟨⟨c1, h1, e1⟩, ux, uz⟩ := clique_side hk ih hdeg hcf S1 hxz hn hbx hbxS1
      hbz hbzS1 hc1
    obtain ⟨c2, h2, e2⟩ := few_side hk ih hdeg hcf S2 (qx := bx) (qz := bz) hn hx.symm
      (fun v hv2 hvz hxv => ux v (fun hv1 => by
        rcases hinter v hv1 hv2 with rfl | rfl
        · exact H.loopless.irrefl _ hxv
        · exact hvz rfl) hxv)
      (fun v hv2 hvx hzv => uz v (fun hv1 => by
        rcases hinter v hv1 hv2 with rfl | rfl
        · exact hvx rfl
        · exact H.loopless.irrefl _ hzv) hzv)
    exact same_glue c1 c2 h1 e1 h2 e2
end BrooksTheorem.Aux
