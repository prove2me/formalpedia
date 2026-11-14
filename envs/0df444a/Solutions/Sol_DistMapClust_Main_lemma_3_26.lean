-- Prove2me | solution 1 for DistMapClust.Main.lemma_3_26
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-14T03:51:21.373698+00:00
-- url     : https://prove2.me/submissions/b7d74988-39fc-47e1-b89b-8eaf4671b599

import Mathlib

theorem solution {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (E : Finset (A × B)) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hB : ∀ v : B, a * b ≤ (E.filter (fun e => e.2 = v)).card)
    (hA : ∀ u : A, (E.filter (fun e => e.1 = u)).card ≤ b) :
    ∃ E' ⊆ E, (∀ v : B, a ≤ (E'.filter (fun e => e.2 = v)).card) ∧
      ∀ u : A, (E'.filter (fun e => e.1 = u)).card ≤ 1 := by
  classical
  -- The relation "copy (v,i) of v is adjacent to u"
  set r : B × Fin a → A → Prop := fun x u => (u, x.1) ∈ E with hr
  -- Hall's condition by double counting
  have hHall : ∀ X : Finset (B × Fin a), X.card ≤ ({u : A | ∃ x ∈ X, r x u} : Finset A).card := by
    intro X
    set S : Finset B := X.image Prod.fst with hS
    set F : Finset (A × B) := S.biUnion (fun v => E.filter (fun e => e.2 = v)) with hF
    set N : Finset A := F.image Prod.fst with hN
    have hNdef : N = ({u : A | ∃ x ∈ X, r x u} : Finset A) := by
      ext u
      simp only [hN, hF, hS, Finset.mem_image, Finset.mem_biUnion, Finset.mem_filter, hr,
        Finset.mem_univ, true_and]
      constructor
      · rintro ⟨e, ⟨v, hvS, heE, hev⟩, rfl⟩
        obtain ⟨x, hxX, hxv⟩ := hvS
        refine ⟨x, hxX, ?_⟩
        have hee : e = (e.1, x.1) := Prod.ext rfl (by rw [hev, ← hxv])
        rwa [hee] at heE
      · rintro ⟨x, hxX, hxu⟩
        exact ⟨(u, x.1), ⟨x.1, ⟨x, hxX, rfl⟩, hxu, rfl⟩, rfl⟩
    -- lower bound on F: each vertex of S contributes at least a*b edges
    have hlow : S.card * (a * b) ≤ F.card := by
      rw [hF, Finset.card_biUnion]
      · calc S.card * (a * b) = ∑ v ∈ S, a * b := by
              simp [Finset.sum_const]
          _ ≤ ∑ v ∈ S, (E.filter (fun e => e.2 = v)).card :=
              Finset.sum_le_sum (fun v _ => hB v)
      · intro v hv w hw hvw
        show Disjoint _ _
        rw [Finset.disjoint_left]
        intro e hev hew
        simp only [Finset.mem_filter] at hev hew
        exact hvw (hev.2.symm.trans hew.2)
    -- upper bound on the neighbourhood: each vertex of N is incident to at most b edges
    set G : Finset (A × B) := N.biUnion (fun u => E.filter (fun e => e.1 = u)) with hG
    have hFG : F ⊆ G := by
      intro e he
      rw [hF, Finset.mem_biUnion] at he
      obtain ⟨v, hvS, hev⟩ := he
      rw [Finset.mem_filter] at hev
      obtain ⟨heE, he2⟩ := hev
      rw [hG, Finset.mem_biUnion]
      refine ⟨e.1, ?_, ?_⟩
      · rw [hN, Finset.mem_image]
        refine ⟨e, ?_, rfl⟩
        rw [hF, Finset.mem_biUnion]
        exact ⟨v, hvS, by rw [Finset.mem_filter]; exact ⟨heE, he2⟩⟩
      · rw [Finset.mem_filter]
        exact ⟨heE, rfl⟩
    have hupp : G.card ≤ N.card * b := by
      rw [hG, Finset.card_biUnion]
      · calc ∑ u ∈ N, (E.filter (fun e => e.1 = u)).card ≤ ∑ u ∈ N, b :=
              Finset.sum_le_sum (fun u _ => hA u)
          _ = N.card * b := by simp [Finset.sum_const]
      · intro u hu w hw huw
        show Disjoint _ _
        rw [Finset.disjoint_left]
        intro e heu hew
        simp only [Finset.mem_filter] at heu hew
        exact huw (heu.2.symm.trans hew.2)
    have hmul : a * S.card * b ≤ N.card * b := by
      calc a * S.card * b = S.card * (a * b) := by ring
        _ ≤ F.card := hlow
        _ ≤ G.card := Finset.card_le_card hFG
        _ ≤ N.card * b := hupp
    have h1 : a * S.card ≤ N.card := Nat.le_of_mul_le_mul_right hmul hb
    -- upper bound on X: each vertex of B has at most a copies
    have h2 : X.card ≤ a * S.card := by
      have hfib : ∀ v ∈ Finset.image Prod.fst X, {x ∈ X | x.1 = v}.card ≤ a := by
        intro v _
        have hinj : Set.InjOn (fun x : B × Fin a => x.2) ↑{x ∈ X | x.1 = v} := by
          intro x hx y hy hxy
          simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hx hy
          exact Prod.ext (by rw [hx.2, hy.2]) hxy
        calc {x ∈ X | x.1 = v}.card = ({x ∈ X | x.1 = v}.image (fun x => x.2)).card :=
              (Finset.card_image_of_injOn hinj).symm
          _ ≤ Fintype.card (Fin a) := Finset.card_le_univ _
          _ = a := by simp
      have h := Finset.card_le_mul_card_image X a hfib
      rwa [← hS] at h
    have h3 : X.card ≤ N.card := le_trans h2 h1
    simpa only [hNdef] using h3
  obtain ⟨g, hg, hgr⟩ := (Fintype.all_card_le_filter_rel_iff_exists_injective r).mp hHall
  -- build the matching from the distinct representatives
  set φ : B × Fin a → A × B := fun x => (g x, x.1) with hφ
  have hφinj : Function.Injective φ := by
    intro x y hxy
    exact hg (congrArg Prod.fst hxy)
  refine ⟨Finset.univ.image φ, ?_, ?_, ?_⟩
  · intro e he
    rw [Finset.mem_image] at he
    obtain ⟨x, -, rfl⟩ := he
    exact hgr x
  · intro v
    have heq : (Finset.univ.image φ).filter (fun e => e.2 = v) =
        (Finset.univ.filter (fun x : B × Fin a => x.1 = v)).image φ := by
      ext e
      constructor
      · intro he
        rw [Finset.mem_filter] at he
        obtain ⟨heE', hev⟩ := he
        rw [Finset.mem_image] at heE'
        obtain ⟨x, -, rfl⟩ := heE'
        rw [Finset.mem_image]
        exact ⟨x, by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hev⟩, rfl⟩
      · intro he
        rw [Finset.mem_image] at he
        obtain ⟨x, hx, rfl⟩ := he
        rw [Finset.mem_filter]
        refine ⟨?_, ?_⟩
        · rw [Finset.mem_image]
          exact ⟨x, Finset.mem_univ _, rfl⟩
        · rw [Finset.mem_filter] at hx
          exact hx.2
    rw [heq, Finset.card_image_of_injective _ hφinj]
    have hcard : (Finset.univ.filter (fun x : B × Fin a => x.1 = v)).card = a := by
      have h := Finset.card_bij (fun x (_ : x ∈ Finset.univ.filter (fun x : B × Fin a => x.1 = v)) => x.2)
          (fun x _ => Finset.mem_univ x.2)
          (fun x hx y hy hxy => by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
            exact Prod.ext (hx.trans hy.symm) hxy)
          (fun i _ => ⟨(v, i), by simp, rfl⟩)
        (t := Finset.univ)
      simpa using h
    exact le_of_eq hcard.symm
  · intro u
    have heq : (Finset.univ.image φ).filter (fun e => e.1 = u) =
        (Finset.univ.filter (fun x : B × Fin a => g x = u)).image φ := by
      ext e
      constructor
      · intro he
        rw [Finset.mem_filter] at he
        obtain ⟨heE', hev⟩ := he
        rw [Finset.mem_image] at heE'
        obtain ⟨x, -, rfl⟩ := heE'
        rw [Finset.mem_image]
        exact ⟨x, by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hev⟩, rfl⟩
      · intro he
        rw [Finset.mem_image] at he
        obtain ⟨x, hx, rfl⟩ := he
        rw [Finset.mem_filter]
        refine ⟨?_, ?_⟩
        · rw [Finset.mem_image]
          exact ⟨x, Finset.mem_univ _, rfl⟩
        · rw [Finset.mem_filter] at hx
          exact hx.2
    rw [heq, Finset.card_image_of_injective _ hφinj]
    rw [Finset.card_le_one]
    intro x hx y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    exact hg (hx.trans hy.symm)

