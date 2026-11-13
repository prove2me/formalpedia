-- Prove2me | solution 1 for FatFlat.Hereditary.lemma_5_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:59:05.786131+00:00
-- url     : https://prove2.me/submissions/521d089c-3e07-40bb-b32b-65527349d676

import Mathlib
import Definitions.Def_FatFlat_Hereditary_Basic
import Definitions.Def_FatFlat_Hereditary_Minors
import Definitions.Def_FatFlat_Hereditary_Patterns
import Definitions.Def_FatFlat_Hereditary_Classes

section
set_option autoImplicit false

namespace FatFlat.Dev.L51
open FatFlat.Hereditary

lemma edist_map_le {V W : Type} {G : SimpleGraph V} {G' : SimpleGraph W} (f : G →g G') (u v : V) :
    G'.edist (f u) (f v) ≤ G.edist u v := by
  by_cases h : G.edist u v = ⊤
  · rw [h]; exact le_top
  · obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top h
    rw [← hp]
    have := SimpleGraph.edist_le (p.map f)
    simpa [SimpleGraph.Walk.length_map] using this

/-- centre to point inside a superset -/
lemma edist_centre_super {V : Type} (G : SimpleGraph V) {S T : Set V} (hST : S ⊆ T) (r : ℕ)
    (c : V) (hc : c ∈ S) (hcc : ∀ v : ↥S, (G.induce S).edist ⟨c, hc⟩ v ≤ r)
    (u : V) (hu : u ∈ S) :
    (G.induce T).edist ⟨c, hST hc⟩ ⟨u, hST hu⟩ ≤ r := by
  have h1 := edist_map_le (G.induceHomOfLE hST).toHom ⟨c, hc⟩ ⟨u, hu⟩
  simp only [RelEmbedding.coe_toRelHom, SimpleGraph.induceHomOfLE_apply] at h1
  exact h1.trans (hcc ⟨u, hu⟩)

/-- two points of a radius-`r` set are close inside any superset -/
lemma edist_in_super {V : Type} (G : SimpleGraph V) {S T : Set V} (hST : S ⊆ T) (r : ℕ)
    (c : V) (hc : c ∈ S) (hcc : ∀ v : ↥S, (G.induce S).edist ⟨c, hc⟩ v ≤ r)
    (u v : V) (hu : u ∈ S) (hv : v ∈ S) :
    (G.induce T).edist ⟨u, hST hu⟩ ⟨v, hST hv⟩ ≤ 2 * (r : ℕ∞) := by
  have h1' := edist_centre_super G hST r c hc hcc u hu
  have h2' := edist_centre_super G hST r c hc hcc v hv
  calc (G.induce T).edist ⟨u, hST hu⟩ ⟨v, hST hv⟩
      ≤ (G.induce T).edist ⟨u, hST hu⟩ ⟨c, hST hc⟩ + (G.induce T).edist ⟨c, hST hc⟩ ⟨v, hST hv⟩ :=
        SimpleGraph.edist_triangle
    _ ≤ r + r := by
        rw [SimpleGraph.edist_comm (G := G.induce T) (u := ⟨u, hST hu⟩) (v := ⟨c, hST hc⟩)]; exact add_le_add h1' h2'
    _ = 2 * (r : ℕ∞) := by ring

abbrev KE (n : ℕ) := (⊤ : SimpleGraph (Fin n)).edgeSet

lemma block_card (n : ℕ) (T : Fin n ⊕ KE n → Prop)
    (hT : ∀ o1 o2, T o1 → T o2 → o1 = o2 ∨ Incident (⊤ : SimpleGraph (Fin n)) o1 o2) :
    ∃ S : Finset (Fin n), S.card ≤ 2 ∧ ∀ p : Fin n,
      (T (Sum.inl p) ∨ ∃ e : KE n, p ∈ (e : Sym2 (Fin n)) ∧ T (Sum.inr e)) → p ∈ S := by
  classical
  by_cases h : ∃ e, T (Sum.inr e)
  · obtain ⟨e0, he0⟩ := h
    have hs : ∀ z : Sym2 (Fin n), ∃ a b, z = s(a, b) := fun z => Sym2.ind (fun a b => ⟨a, b, rfl⟩) z
    obtain ⟨a, b, hab⟩ := hs (e0 : Sym2 (Fin n))
    refine ⟨{a, b}, Finset.card_le_two, ?_⟩
    have key : ∀ p : Fin n, p ∈ (e0 : Sym2 (Fin n)) → p ∈ ({a, b} : Finset (Fin n)) := by
      intro p hp
      rw [hab, Sym2.mem_iff] at hp
      simpa using hp
    rintro p (hp | ⟨e, hpe, he⟩)
    · rcases hT _ _ hp he0 with h1 | h1
      · exact absurd h1 Sum.inl_ne_inr
      · exact key p (by simpa [Incident] using h1)
    · rcases hT _ _ he he0 with h1 | h1
      · have : e = e0 := Sum.inr_injective h1
        subst this; exact key p hpe
      · simp [Incident] at h1
  · by_cases h2 : ∃ u, T (Sum.inl u)
    · obtain ⟨u, hu⟩ := h2
      refine ⟨{u}, by simp, ?_⟩
      rintro p (hp | ⟨e, _, he⟩)
      · rcases hT _ _ hp hu with h1 | h1
        · simp [Sum.inl_injective.eq_iff.mp h1]
        · simp [Incident] at h1
      · exact absurd ⟨e, he⟩ h
    · refine ⟨∅, by simp, ?_⟩
      rintro p (hp | ⟨e, _, he⟩)
      · exact absurd ⟨p, hp⟩ h2
      · exact absurd ⟨e, he⟩ h

end FatFlat.Dev.L51

namespace FatFlat.Hereditary
open FatFlat.Dev.L51 in
theorem chk_lemma_5_1 (C : GraphClass) (hC : DrillFlat C) : FSMF C := by
  classical
  obtain ⟨β, hβ, h⟩ := hC
  refine ⟨2 * β + 1, by omega, fun α => ?_⟩
  obtain ⟨N, s, hNs⟩ := h (4 * max α 1) (by omega)
  refine ⟨N (2 * s + 2), ⊤, ?_⟩
  intro V inst G hG hmin
  obtain ⟨M, hM⟩ := hmin
  let n := N (2 * s + 2)
  have hcen' : ∀ o, ∃ c : V, ∃ hc : c ∈ M.φ o,
      ∀ v : ↥(M.φ o), (G.induce (M.φ o)).edist ⟨c, hc⟩ v ≤ α := by
    intro o
    obtain ⟨c, hc⟩ := hM o
    exact ⟨c.1, c.2, hc⟩
  choose cen hcen hrad using hcen'
  let cp : Fin n → V := fun p => cen (Sum.inl p)
  have hcp_inj : Function.Injective cp := by
    intro p q hpq
    by_contra hne
    have hfar := M.far (Sum.inl p) (Sum.inl q) (by simpa using hne) (by simp [Incident])
      (cen (Sum.inl p)) (hcen _) (cen (Sum.inl q)) (hcen _)
    have : cen (Sum.inl p) = cen (Sum.inl q) := hpq
    rw [this, SimpleGraph.edist_self] at hfar
    have := Nat.cast_le.mp (hfar.trans (le_refl _) : ((2 * β + 1 : ℕ) : ℕ∞) ≤ ((0 : ℕ) : ℕ∞))
    omega
  let A : Finset V := Finset.univ.image cp
  have hA : A.card = n := by
    rw [Finset.card_image_of_injective _ hcp_inj]; simp
  obtain ⟨B, hBA, hBcard, X, hXcard, hscat⟩ := hNs V G hG (2 * s + 2) A (by rw [hA])
  -- the objects close to `x`
  let T : V → (Fin n ⊕ KE n) → Prop := fun x o => ∃ y ∈ M.φ o, G.edist x y ≤ β
  have hT : ∀ x o1 o2, T x o1 → T x o2 → o1 = o2 ∨ Incident (⊤ : SimpleGraph (Fin n)) o1 o2 := by
    intro x o1 o2 ⟨y1, hy1, d1⟩ ⟨y2, hy2, d2⟩
    by_contra hcon
    push Not at hcon
    have hfar := M.far o1 o2 hcon.1 hcon.2 y1 hy1 y2 hy2
    have h3 : G.edist y1 y2 ≤ (β : ℕ∞) + β := by
      calc G.edist y1 y2 ≤ G.edist y1 x + G.edist x y2 := SimpleGraph.edist_triangle
        _ ≤ β + β := by rw [SimpleGraph.edist_comm (G := G) (u := y1) (v := x)]; exact add_le_add d1 d2
    have h4 : ((2 * β + 1 : ℕ) : ℕ∞) ≤ ((β + β : ℕ) : ℕ∞) := by
      push_cast; exact hfar.trans h3
    have := Nat.cast_le.mp h4
    omega
  choose S hScard hSblock using fun x => block_card n (T x) (hT x)
  let Bl : Finset (Fin n) := X.biUnion S
  have hBl : Bl.card ≤ 2 * s := by
    have := Finset.card_biUnion_le_card_mul X S 2 (fun x _ => hScard x)
    nlinarith
  let P : Finset (Fin n) := Finset.univ.filter (fun p => cp p ∈ B)
  have hP : B.card ≤ P.card := by
    have hsub : B ⊆ P.image cp := by
      intro b hb
      obtain ⟨p, _, hp⟩ := Finset.mem_image.mp (hBA hb)
      exact Finset.mem_image.mpr ⟨p, by simp [P, hp, hb], hp⟩
    exact (Finset.card_le_card hsub).trans Finset.card_image_le
  have hPBl : 2 ≤ (P \ Bl).card := by
    have := Finset.le_card_sdiff Bl P
    omega
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (by omega : 1 < (P \ Bl).card)
  rw [Finset.mem_sdiff] at hp hq
  have hpB : cp p ∈ B := by simpa [P] using hp.1
  have hqB : cp q ∈ B := by simpa [P] using hq.1
  have hemem : s(p, q) ∈ (⊤ : SimpleGraph (Fin n)).edgeSet := by simpa using hpq
  let e : KE n := ⟨s(p, q), hemem⟩
  let Sset : Set V := M.φ (Sum.inl p) ∪ M.φ (Sum.inr e) ∪ M.φ (Sum.inl q)
  let Z : Set V := ball G (X : Set V) β
  have hSZ : Sset ⊆ Zᶜ := by
    intro z hz hzZ
    obtain ⟨x, hxX, hzx⟩ := hzZ
    have hzx' : G.edist x z ≤ β := by rw [SimpleGraph.edist_comm]; exact hzx
    rcases hz with (hz | hz) | hz
    · exact hp.2 (Finset.mem_biUnion.mpr ⟨x, hxX, hSblock x p (Or.inl ⟨z, hz, hzx'⟩)⟩)
    · exact hp.2 (Finset.mem_biUnion.mpr ⟨x, hxX, hSblock x p
        (Or.inr ⟨e, by simp [e], ⟨z, hz, hzx'⟩⟩)⟩)
    · exact hq.2 (Finset.mem_biUnion.mpr ⟨x, hxX, hSblock x q (Or.inl ⟨z, hz, hzx'⟩)⟩)
  have h1 : M.φ (Sum.inl p) ⊆ Sset := fun z hz => Or.inl (Or.inl hz)
  have h2 : M.φ (Sum.inr e) ⊆ Sset := fun z hz => Or.inl (Or.inr hz)
  have h3 : M.φ (Sum.inl q) ⊆ Sset := fun z hz => Or.inr hz
  obtain ⟨u, hue, hup⟩ := M.meet e p (by simp [e])
  obtain ⟨v, hve, hvq⟩ := M.meet e q (by simp [e])
  have d1 := edist_centre_super G h1 α _ (hcen (Sum.inl p)) (hrad (Sum.inl p)) u hup
  have d2 := edist_in_super G h2 α _ (hcen (Sum.inr e)) (hrad (Sum.inr e)) u v hue hve
  have d3 := edist_centre_super G h3 α _ (hcen (Sum.inl q)) (hrad (Sum.inl q)) v hvq
  rw [SimpleGraph.edist_comm] at d3
  have d1' : (G.induce Sset).edist ⟨cp p, h1 (hcen (Sum.inl p))⟩ ⟨u, h1 hup⟩ ≤ α := d1
  have d2' : (G.induce Sset).edist ⟨u, h2 hue⟩ ⟨v, h2 hve⟩ ≤ 2 * (α : ℕ∞) := d2
  have d3' : (G.induce Sset).edist ⟨v, h3 hvq⟩ ⟨cp q, h3 (hcen (Sum.inl q))⟩ ≤ α := d3
  have dS : (G.induce Sset).edist ⟨cp p, h1 (hcen (Sum.inl p))⟩ ⟨cp q, h3 (hcen (Sum.inl q))⟩
      ≤ (α : ℕ∞) + 2 * α + α := by
    calc _ ≤ (G.induce Sset).edist ⟨cp p, h1 (hcen (Sum.inl p))⟩ ⟨v, h3 hvq⟩
          + (G.induce Sset).edist ⟨v, h3 hvq⟩ ⟨cp q, h3 (hcen (Sum.inl q))⟩ :=
          SimpleGraph.edist_triangle
      _ ≤ ((G.induce Sset).edist ⟨cp p, h1 (hcen (Sum.inl p))⟩ ⟨u, h2 hue⟩
          + (G.induce Sset).edist ⟨u, h2 hue⟩ ⟨v, h2 hve⟩)
          + (G.induce Sset).edist ⟨v, h3 hvq⟩ ⟨cp q, h3 (hcen (Sum.inl q))⟩ :=
          add_le_add_left SimpleGraph.edist_triangle _
      _ ≤ (α + 2 * α) + α := add_le_add (add_le_add d1' d2') d3'
  have hmono := edist_map_le (G.induceHomOfLE hSZ).toHom
    ⟨cp p, h1 (hcen (Sum.inl p))⟩ ⟨cp q, h3 (hcen (Sum.inl q))⟩
  simp only [RelEmbedding.coe_toRelHom, SimpleGraph.induceHomOfLE_apply] at hmono
  have hne : (⟨cp p, hSZ (h1 (hcen (Sum.inl p)))⟩ : ↥Zᶜ) ≠ ⟨cp q, hSZ (h3 (hcen (Sum.inl q)))⟩ := by
    intro hh
    exact hpq (hcp_inj (congrArg Subtype.val hh))
  have hlt := hscat _ _ hpB hqB hne
  have hle : (α : ℕ∞) + 2 * α + α ≤ ((4 * max α 1 : ℕ) : ℕ∞) := by
    have : α + 2 * α + α ≤ 4 * max α 1 := by omega
    exact_mod_cast this
  exact absurd (hlt.trans_le (hmono.trans (dS.trans hle))) (lt_irrefl _)

end FatFlat.Hereditary
end

theorem solution : type_of% @FatFlat.Hereditary.chk_lemma_5_1 := @FatFlat.Hereditary.chk_lemma_5_1
