-- Prove2me | solution 1 for BrooksTheorem.Aux.clique_side
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:41:11.08885+00:00
-- url     : https://prove2.me/submissions/917977d4-de48-4877-84be-eb4d5a11674d

module
public import Definitions.Def_BrooksLib_Greedy
public import Definitions.Def_BrooksLib_BrooksCore
public import Theorems.Thm_BrooksTheorem_Aux_restr_adj
public import Theorems.Thm_BrooksTheorem_Aux_addE_adj
public import Theorems.Thm_BrooksTheorem_Aux_colour_restr
public import Theorems.Thm_BrooksTheorem_Aux_nb_eq_insert
public import Theorems.Thm_BrooksTheorem_Aux_proper_update2
public import Theorems.Thm_BrooksTheorem_Aux_exists_not_mem_of_card_lt
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
    (hdeg : ∀ v, (nb H v).card ≤ k) (hcf : H.CliqueFree (k + 1)) (S : Set V) {x z px pz : V}
    (hxz : x ≠ z) (hn : ¬ H.Adj x z) (hpx : H.Adj x px) (hpxS : px ∉ S)
    (hpz : H.Adj z pz) (hpzS : pz ∉ S)
    (hK : ¬ (restr H S ⊔ edge x z).CliqueFree (k + 1)) :
    (∃ c : V → Fin k, Proper (restr H S) c ∧ c x = c z) ∧
    (∀ v ∉ S, H.Adj x v → v = px) ∧ (∀ v ∉ S, H.Adj z v → v = pz) := by
  classical
  simp only [CliqueFree, not_forall, not_not] at hK
  obtain ⟨K, hK⟩ := hK
  rw [isNClique_iff] at hK
  obtain ⟨hKc, hKcard⟩ := hK
  have hadjK : ∀ u ∈ K, ∀ v ∈ K, u ≠ v → (restr H S ⊔ edge x z).Adj u v :=
    fun u hu v hv huv => hKc hu hv huv
  have hxK : x ∈ K ∧ z ∈ K := by
    by_contra hcon
    apply hcf K
    rw [isNClique_iff]
    refine ⟨fun u hu v hv huv => ?_, hKcard⟩
    have := hadjK u hu v hv huv
    rw [addE_adj] at this
    rcases this with h | ⟨h, _⟩
    · exact h.1
    · exfalso; apply hcon
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hu, hv⟩
      · exact ⟨hv, hu⟩
  set Q := (K.erase x).erase z with hQdef
  have hzKx : z ∈ K.erase x := mem_erase.2 ⟨hxz.symm, hxK.2⟩
  have hQcard : Q.card = k - 1 := by
    rw [hQdef, card_erase_of_mem hzKx, card_erase_of_mem hxK.1, hKcard]; omega
  have hQmem : ∀ q ∈ Q, q ≠ z ∧ q ≠ x ∧ q ∈ K := by
    intro q hq
    simp only [hQdef, mem_erase] at hq
    exact ⟨hq.1, hq.2.1, hq.2.2⟩
  have hQadj : ∀ w ∈ ({x, z} : Finset V), ∀ q ∈ Q, H.Adj w q ∧ q ∈ S := by
    intro w hw q hq
    obtain ⟨hqz, hqx, hqK⟩ := hQmem q hq
    have hwK : w ∈ K := by
      simp only [mem_insert, mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact hxK.1
      · exact hxK.2
    have hwq : w ≠ q := by
      simp only [mem_insert, mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact hqx.symm
      · exact hqz.symm
    have := hadjK w hwK q hqK hwq
    rw [addE_adj] at this
    rcases this with h | ⟨h, _⟩
    · exact ⟨h.1, h.2.2⟩
    · exfalso
      rcases h with ⟨_, h⟩ | ⟨_, h⟩
      · exact hqz h
      · exact hqx h
  have hQS : ∀ q ∈ Q, q ∈ S := fun q hq => (hQadj x (by simp) q hq).2
  have hnbx : nb H x = insert px Q :=
    nb_eq_insert hdeg (fun q hq => mem_nb.2 (hQadj x (by simp) q hq).1) hpx
      (fun h => hpxS (hQS px h)) (by omega)
  have hnbz : nb H z = insert pz Q :=
    nb_eq_insert hdeg (fun q hq => mem_nb.2 (hQadj z (by simp) q hq).1) hpz
      (fun h => hpzS (hQS pz h)) (by omega)
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨c0, hc0⟩ := colour_restr ih hdeg hcf {v | v ∈ S ∧ v ≠ x ∧ v ≠ z} hpx
      (fun h => h.2.1 rfl)
    have hinj : Set.InjOn c0 (Q : Set V) := by
      intro q1 hq1 q2 hq2 he
      by_contra hne
      obtain ⟨h1z, h1x, h1K⟩ := hQmem q1 hq1
      obtain ⟨h2z, h2x, h2K⟩ := hQmem q2 hq2
      have := hadjK q1 h1K q2 h2K hne
      rw [addE_adj] at this
      rcases this with h | ⟨h, _⟩
      · exact hc0 q1 q2 ⟨h.1, ⟨h.2.1, h1x, h1z⟩, ⟨h.2.2, h2x, h2z⟩⟩ he
      · rcases h with ⟨h, _⟩ | ⟨h, _⟩
        · exact h1x h
        · exact h1z h
    have himg : (Q.image c0).card < k := by
      rw [card_image_of_injOn hinj, hQcard]; omega
    obtain ⟨col, hcol⟩ := exists_not_mem_of_card_lt _ himg
    refine ⟨_, proper_update2 S hn c0 hc0 col ?_, by simp⟩
    intro w v hw hvS hvx hvz hwv he
    apply hcol
    rw [← he]
    apply mem_image_of_mem
    have hv : v ∈ nb H w := mem_nb.2 hwv
    rcases hw with rfl | rfl
    · rw [hnbx, mem_insert] at hv
      rcases hv with rfl | hv
      · exact absurd hvS hpxS
      · exact hv
    · rw [hnbz, mem_insert] at hv
      rcases hv with rfl | hv
      · exact absurd hvS hpzS
      · exact hv
  · intro v hvS hxv
    have hv : v ∈ nb H x := mem_nb.2 hxv
    rw [hnbx, mem_insert] at hv
    rcases hv with rfl | hv
    · rfl
    · exact absurd (hQS v hv) hvS
  · intro v hvS hzv
    have hv : v ∈ nb H z := mem_nb.2 hzv
    rw [hnbz, mem_insert] at hv
    rcases hv with rfl | hv
    · rfl
    · exact absurd (hQS v hv) hvS
end BrooksTheorem.Aux
