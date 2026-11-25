-- Prove2me | solution 1 for DiracCycle.extend_through
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:57:34.908845+00:00
-- url     : https://prove2.me/submissions/73ec15a0-f52f-4f77-85db-3052e53c332a

module
public import Mathlib
public import Definitions.Def_MengerHamilton_ChvatalErdosAux
public import Definitions.Def_DiracCycleLib_DiracCycle
public import Theorems.Thm_DiracCycle_splice_two
public import Theorems.Thm_DiracCycle_exists_gap
public import Theorems.Thm_Hamiltonicity_CycArr_eq_iff
public import Theorems.Thm_Hamiltonicity_CycArr_eq_mod
public import Theorems.Thm_Hamiltonicity_CycArr_pos
public import Theorems.Thm_Hamiltonicity_exists_fan


set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open DiracCycle
open Hamiltonicity
variable {V : Type*} {G : SimpleGraph V}
namespace DiracCycle
theorem _root_.solution [Finite V] {k : ℕ} (hk : 2 ≤ k)
    (hconn : ∀ S : Set V, S.ncard < k → (G.induce Sᶜ).Connected)
    {m : ℕ} {f : ℕ → V} (hC : CycArr G m f) (T : Finset V) (hTk : #T < k)
    (hT0 : T.Nonempty → f 0 ∈ T) {x : V} (hx : ∀ i, f i ≠ x) :
    ∃ m' g, CycArr G m' g ∧ (∃ i, g i = x) ∧ ∀ p < m, f p ∈ T → ∃ i, g i = f p := by
  classical
  obtain ⟨r, hr, t, P, hP, hPC, hPd⟩ := exists_fan hconn hC hx
  have hm := hC.three_le
  have hm0 := hC.pos
  set s : Fin r → ℕ := fun j => t j % m with hs
  have hsinj : ∀ j j', s j = s j' → j = j' := by
    intro j j' hjj'
    by_contra hne
    have heq : f (t j) = f (t j') := hC.eq_iff.2 hjj'
    have h2 : f (t j) ∈ (P j').support := by rw [heq]; exact (P j').end_mem_support
    exact hx _ (hPd j j' hne (f (t j)) (P j).end_mem_support h2)
  have hsm : ∀ j, s j < m := fun j => Nat.mod_lt _ hm0
  obtain ⟨j₁, j₂, h12, hgood⟩ : ∃ j₁ j₂, s j₁ < s j₂ ∧
      ∀ p < m, f p ∈ T → p = 0 ∨ p ≤ s j₁ ∨ s j₂ ≤ p := by
    set R := Finset.univ.image s with hR
    have hRcard : #R = r := by
      rw [hR, Finset.card_image_of_injective _ (fun j j' h => hsinj j j' h), Finset.card_univ,
        Fintype.card_fin]
    by_cases hmk : m ≤ k
    · have hrm : m ≤ r := by rw [min_eq_right hmk] at hr; exact hr
      have hsub : R ⊆ Finset.range m := by
        intro y hy
        obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hy
        exact Finset.mem_range.2 (hsm j)
      have hReq : R = Finset.range m :=
        Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_range]; omega)
      obtain ⟨j₁, -, hj₁⟩ := Finset.mem_image.1 (hReq ▸ Finset.mem_range.2 (by omega) :
        (0 : ℕ) ∈ R)
      obtain ⟨j₂, -, hj₂⟩ := Finset.mem_image.1 (hReq ▸ Finset.mem_range.2 (by omega) :
        (1 : ℕ) ∈ R)
      refine ⟨j₁, j₂, by omega, fun p _ _ => by omega⟩
    · have hrk : k ≤ r := by rw [min_eq_left (by omega)] at hr; exact hr
      set U := (Finset.range m).filter (fun p => f p ∈ T ∧ p ≠ 0) with hU
      have hUcard : #U + 2 ≤ #R := by
        rw [hRcard]
        by_cases hTne : T.Nonempty
        · have h0 := hT0 hTne
          have hle : #U ≤ #(T.erase (f 0)) := by
            refine Finset.card_le_card_of_injOn f ?_ ?_
            · intro p hp
              rw [hU, Finset.coe_filter] at hp
              obtain ⟨hpm, hpT, hp0⟩ := hp
              refine Finset.mem_erase.2 ⟨fun h => hp0 ?_, hpT⟩
              exact hC.inj _ _ (Finset.mem_range.1 hpm) (by omega) h
            · intro p hp q hq hpq
              rw [hU, Finset.coe_filter] at hp hq
              exact hC.inj _ _ (Finset.mem_range.1 hp.1) (Finset.mem_range.1 hq.1) hpq
          rw [Finset.card_erase_of_mem h0] at hle
          have := Finset.card_pos.2 hTne
          omega
        · rw [Finset.not_nonempty_iff_eq_empty] at hTne
          subst hTne
          have : U = ∅ := by
            rw [hU]
            simp
          rw [this, Finset.card_empty]
          omega
      obtain ⟨a, ha, b, hb, hab, hgap⟩ := exists_gap _ R U rfl hUcard
      obtain ⟨j₁, -, rfl⟩ := Finset.mem_image.1 ha
      obtain ⟨j₂, -, rfl⟩ := Finset.mem_image.1 hb
      refine ⟨j₁, j₂, hab, fun p hp hpT => ?_⟩
      by_cases hp0 : p = 0
      · exact Or.inl hp0
      · have := hgap p (by rw [hU, Finset.mem_filter]; exact ⟨Finset.mem_range.2 hp, hpT, hp0⟩)
        omega
  have e : ∀ j, f (t j) = f (s j) := fun j => hC.eq_mod _
  obtain ⟨m', g, hg, hgx, hgarc⟩ := splice_two hC hx h12 (hsm j₂)
    ((P j₁).copy rfl (e j₁)) ((P j₂).copy rfl (e j₂))
    (by rw [Walk.isPath_copy]; exact hP j₁) (by rw [Walk.isPath_copy]; exact hP j₂)
    (by
      intro y hy i hi
      rw [Walk.support_copy] at hy
      exact (hPC j₁ y hy i hi).trans (e j₁))
    (by
      intro y hy i hi
      rw [Walk.support_copy] at hy
      exact (hPC j₂ y hy i hi).trans (e j₂))
    (by
      intro y hy₁ hy₂
      rw [Walk.support_copy] at hy₁ hy₂
      exact hPd j₁ j₂ (fun h => by rw [h] at h12; omega) y hy₁ hy₂)
  exact ⟨m', g, hg, hgx, fun p hp hpT => hgarc p hp (hgood p hp hpT)⟩
end DiracCycle
