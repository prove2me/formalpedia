-- Prove2me | solution 1 for Erdos81.chordal_clique_suffix_peo
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T23:13:36.331946+00:00
-- url     : https://prove2.me/submissions/93e1d5b9-1849-4e0a-ac55-679316206b76

import Definitions.Def_erdos81_clique_partitions
import Mathlib.Data.Finset.Max

namespace ChordalSuffix

variable {n : ℕ} (G : SimpleGraph (Fin n))

def SimplicialOn (U : Finset (Fin n)) (v : Fin n) : Prop :=
  ∀ ⦃a b⦄, a ∈ U → b ∈ U → G.Adj v a → G.Adj v b → a ≠ b → G.Adj a b

theorem simplicial_outside
    (ρ : Fin n → ℕ) (hi : Function.Injective ρ)
    (hp : ∀ ⦃v a b⦄, G.Adj v a → G.Adj v b →
      ρ v < ρ a → ρ v < ρ b → a ≠ b → G.Adj a b)
    (U : Finset (Fin n)) :
    ∀ (S : Finset (Fin n)), S ⊆ U → Erdos81.IsClique G S →
      (∃ w ∈ U, w ∉ S) → ∃ v ∈ U, v ∉ S ∧ SimplicialOn G U v := by
  classical
  induction U using Finset.strongInductionOn with
  | _ U ih =>
    intro S hSU hS hout
    obtain ⟨w, hw, hwS⟩ := hout
    obtain ⟨v, hv, hmin⟩ := U.exists_min_image ρ ⟨w, hw⟩
    have hsimp : SimplicialOn G U v := by
      intro a b ha hb hva hvb hab
      apply hp hva hvb
      · exact lt_of_le_of_ne (hmin a ha) (fun he => G.ne_of_adj hva (hi he))
      · exact lt_of_le_of_ne (hmin b hb) (fun he => G.ne_of_adj hvb (hi he))
      · exact hab
    by_cases hvS : v ∈ S
    · let N := U.filter (G.Adj v)
      have hNU : N ⊆ U.erase v := by
        intro a ha
        obtain ⟨haU, hva⟩ := Finset.mem_filter.mp ha
        exact Finset.mem_erase.mpr ⟨(G.ne_of_adj hva).symm, haU⟩
      have hNC : Erdos81.IsClique G N := by
        intro a b ha hb hab
        obtain ⟨haU, hva⟩ := Finset.mem_filter.mp ha
        obtain ⟨hbU, hvb⟩ := Finset.mem_filter.mp hb
        exact hsimp haU hbU hva hvb hab
      by_cases hOutside : ∃ a ∈ U.erase v, a ∉ N
      · obtain ⟨a, ha, haN, haSimp⟩ :=
          ih (U.erase v) (Finset.erase_ssubset hv) N hNU hNC hOutside
        have haU := Finset.mem_of_mem_erase ha
        have hav : ¬ G.Adj v a := by
          intro hva
          exact haN (Finset.mem_filter.mpr ⟨haU, hva⟩)
        have haS : a ∉ S := by
          intro haS
          exact hav (hS hvS haS (Finset.ne_of_mem_erase ha).symm)
        refine ⟨a, haU, haS, ?_⟩
        intro b c hb hc hab hac hbc
        have hbv : b ≠ v := by
          intro he; subst b; exact hav hab.symm
        have hcv : c ≠ v := by
          intro he; subst c; exact hav hac.symm
        exact haSimp (Finset.mem_erase.mpr ⟨hbv, hb⟩)
          (Finset.mem_erase.mpr ⟨hcv, hc⟩) hab hac hbc
      · have hcover : ∀ a ∈ U, a ≠ v → G.Adj v a := by
          intro a ha hav
          have haN : a ∈ N := by
            by_contra hh
            exact hOutside ⟨a, Finset.mem_erase.mpr ⟨hav, ha⟩, hh⟩
          exact (Finset.mem_filter.mp haN).2
        have hcomplete : Erdos81.IsClique G U := by
          intro a b ha hb hab
          by_cases hav : a = v
          · subst a; exact hcover b hb hab.symm
          by_cases hbv : b = v
          · subst b; exact (hcover a ha hab).symm
          exact hsimp ha hb (hcover a ha hav) (hcover b hb hbv) hab
        exact ⟨w, hw, hwS, fun {_ _} hb hc _ _ hbc => hcomplete hb hc hbc⟩
    · exact ⟨v, hv, hvS, hsimp⟩

theorem order_subset
    (ρ : Fin n → ℕ) (hi : Function.Injective ρ)
    (hp : ∀ ⦃v a b⦄, G.Adj v a → G.Adj v b →
      ρ v < ρ a → ρ v < ρ b → a ≠ b → G.Adj a b)
    (U : Finset (Fin n)) :
    ∀ (S : Finset (Fin n)), S ⊆ U → Erdos81.IsClique G S →
      ∃ r : Fin n → ℕ,
        (∀ a ∈ U, ∀ b ∈ U, r a = r b → a = b) ∧
        (∀ ⦃v a b⦄, v ∈ U → a ∈ U → b ∈ U → G.Adj v a → G.Adj v b →
          r v < r a → r v < r b → a ≠ b → G.Adj a b) ∧
        (∀ v ∈ U, v ∉ S → ∀ s ∈ S, r v < r s) := by
  classical
  induction U using Finset.strongInductionOn with
  | _ U ih =>
    intro S hSU hS
    by_cases hout : ∃ w ∈ U, w ∉ S
    · obtain ⟨v, hv, hvS, hsimp⟩ := simplicial_outside G ρ hi hp U S hSU hS hout
      have hSerase : S ⊆ U.erase v := by
        intro s hs
        exact Finset.mem_erase.mpr ⟨fun he => hvS (he ▸ hs), hSU hs⟩
      obtain ⟨r, hri, hrp, hrs⟩ :=
        ih (U.erase v) (Finset.erase_ssubset hv) S hSerase hS
      let R : Fin n → ℕ := fun a => if a = v then 0 else r a + 1
      refine ⟨R, ?_, ?_, ?_⟩
      · intro a ha b hb he
        by_cases hav : a = v <;> by_cases hbv : b = v
        · exact hav.trans hbv.symm
        · simp [R, hav, hbv] at he
        · simp [R, hav, hbv] at he
        · apply hri a (Finset.mem_erase.mpr ⟨hav, ha⟩) b
            (Finset.mem_erase.mpr ⟨hbv, hb⟩)
          simpa [R, hav, hbv] using he
      · intro a b c ha hb hc hab hac hrab hrac hbc
        by_cases hav : a = v
        · subst a; exact hsimp hb hc hab hac hbc
        have hbv : b ≠ v := by
          intro he; simp [R, hav, he] at hrab
        have hcv : c ≠ v := by
          intro he; simp [R, hav, he] at hrac
        apply hrp (Finset.mem_erase.mpr ⟨hav, ha⟩)
          (Finset.mem_erase.mpr ⟨hbv, hb⟩) (Finset.mem_erase.mpr ⟨hcv, hc⟩) hab hac
        · simpa [R, hav, hbv] using hrab
        · simpa [R, hav, hcv] using hrac
        · exact hbc
      · intro a ha haS s hs
        have hsv : s ≠ v := fun he => hvS (he ▸ hs)
        by_cases hav : a = v
        · simp [R, hav, hsv]
        · have hh := hrs a (Finset.mem_erase.mpr ⟨hav, ha⟩) haS s hs
          simpa [R, hav, hsv] using hh
    · refine ⟨ρ, fun a _ b _ he => hi he, fun {_ _ _} _ _ _ hab hac h1 h2 h3 => hp hab hac h1 h2 h3, ?_⟩
      intro v hv hvS
      exact False.elim (hout ⟨v, hv, hvS⟩)

end ChordalSuffix

theorem solution {n : ℕ}
    (G : SimpleGraph (Fin n)) (hG : Erdos81.IsChordal G)
    (S : Finset (Fin n)) (hS : Erdos81.IsClique G S) :
    ∃ rank : Fin n → ℕ, Function.Injective rank ∧
      (∀ ⦃v a b : Fin n⦄, G.Adj v a → G.Adj v b →
        rank v < rank a → rank v < rank b → a ≠ b → G.Adj a b) ∧
      (∀ v : Fin n, v ∉ S → ∀ s ∈ S, rank v < rank s) := by
  classical
  obtain ⟨ρ, hi, hp⟩ := hG
  obtain ⟨r, hri, hrp, hrs⟩ := ChordalSuffix.order_subset G ρ hi hp
    Finset.univ S (Finset.subset_univ S) hS
  exact ⟨r, fun _ _ he => hri _ (Finset.mem_univ _) _ (Finset.mem_univ _) he,
    fun {_ _ _} h1 h2 h3 h4 h5 => hrp (Finset.mem_univ _) (Finset.mem_univ _) (Finset.mem_univ _)
      h1 h2 h3 h4 h5,
    fun v hvS s hs => hrs v (Finset.mem_univ _) hvS s hs⟩
