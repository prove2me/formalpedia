-- Prove2me | solution 1 for Erdos77.finite_asymmetric_ramsey_step
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T12:21:50.756991+00:00
-- url     : https://prove2.me/submissions/00a0c348-6dab-4418-8a35-5cdfcbb0abfb

import Mathlib

theorem solution (r s : Nat) (hr : 1 < r) (hs : 1 < s)
    (h₁ : Exists fun n : Nat => forall G : SimpleGraph (Fin n),
      Or
        (Exists fun t : Finset (Fin n) => And (t.card = r - 1) (G.IsClique t))
        (Exists fun t : Finset (Fin n) => And (t.card = s) ((Compl.compl G).IsClique t)))
    (h₂ : Exists fun n : Nat => forall G : SimpleGraph (Fin n),
      Or
        (Exists fun t : Finset (Fin n) => And (t.card = r) (G.IsClique t))
        (Exists fun t : Finset (Fin n) => And (t.card = s - 1) ((Compl.compl G).IsClique t))) :
    Exists fun n : Nat => forall G : SimpleGraph (Fin n),
      Or
        (Exists fun t : Finset (Fin n) => And (t.card = r) (G.IsClique t))
        (Exists fun t : Finset (Fin n) => And (t.card = s) ((Compl.compl G).IsClique t)) := by
  classical
  rcases h₁ with ⟨n₁, hn₁⟩
  rcases h₂ with ⟨n₂, hn₂⟩
  have hnpos : 0 < n₁ + n₂ := by
    by_contra h
    have hn₁zero : n₁ = 0 := by omega
    have hn₂zero : n₂ = 0 := by omega
    subst n₁
    subst n₂
    have hbad := hn₁ (⊥ : SimpleGraph (Fin 0))
    rcases hbad with ⟨t, ht, _⟩ | ⟨t, ht, _⟩
    · have hcard : t.card ≤ 0 := by simpa using (Finset.card_le_univ t)
      omega
    · have hcard : t.card ≤ 0 := by simpa using (Finset.card_le_univ t)
      omega
  refine ⟨n₁ + n₂, ?_⟩
  intro G
  let v : Fin (n₁ + n₂) := ⟨0, by omega⟩
  let V : Finset (Fin (n₁ + n₂)) := Finset.univ.erase v
  let A := V.filter fun x => G.Adj v x
  let B := V.filter fun x => ¬ G.Adj v x
  have hV : V.card = n₁ + n₂ - 1 := by simp [V, v]
  have hAB : A.card + B.card = V.card := by
    rw [← Finset.card_filter_add_card_filter_not (s := V) (p := fun x => G.Adj v x)]
  by_cases hA : n₁ ≤ A.card
  · obtain ⟨T, hTA, hTcard⟩ := Finset.exists_subset_card_eq hA
    let e : Fin n₁ ↪ Fin (n₁ + n₂) := (T.orderEmbOfFin hTcard).toEmbedding
    let H : SimpleGraph (Fin n₁) := G.comap e
    rcases hn₁ H with ⟨t, htcard, htcl⟩ | ⟨t, htcard, htcl⟩
    · let u := t.map e
      have hucl : G.IsClique u := by
        have hm := htcl.finsetMap (f := e)
        exact hm.mono (SimpleGraph.map_comap_le e G)
      have hucard : u.card = r - 1 := by simp [u, htcard]
      have huT : ∀ x ∈ u, x ∈ T := by
        intro x hx
        rcases Finset.mem_map.mp hx with ⟨i, hi, rfl⟩
        simpa [e] using Finset.orderEmbOfFin_mem T hTcard i
      have huV : ∀ x ∈ u, x ∈ V := fun x hx => Finset.filter_subset _ _ (hTA (huT x hx))
      have huv : v ∉ u := by
        intro hvu
        have : v ∈ V := huV v hvu
        simp [V] at this
      refine Or.inl ⟨insert v u, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem huv, hucard]
        omega
      · intro x hx y hy hxy
        rcases Finset.mem_insert.mp hx with rfl | hx
        · rcases Finset.mem_insert.mp hy with rfl | hy
          · exact (hxy rfl).elim
          · have : y ∈ A := hTA (huT y hy)
            exact (Finset.mem_filter.mp this).2
        · rcases Finset.mem_insert.mp hy with rfl | hy
          · have : x ∈ A := hTA (huT x hx)
            exact ((Finset.mem_filter.mp this).2).symm
          · exact hucl hx hy hxy
    · let u := t.map e
      have hucl : (Compl.compl G).IsClique u := by
        have hm := htcl.finsetMap (f := e)
        have hEq : Compl.compl (G.comap e) = (Compl.compl G).comap e := by
          ext x y
          simp [SimpleGraph.compl_adj]
        have hle : ((Compl.compl (G.comap e)).map e) ≤ Compl.compl G := by
          rw [hEq]
          exact SimpleGraph.map_comap_le e (Compl.compl G)
        exact hm.mono hle
      refine Or.inr ⟨u, ?_, hucl⟩
      simpa [u] using htcard
  · have hB : n₂ ≤ B.card := by
      have : A.card < n₁ := Nat.lt_of_not_ge hA
      omega
    obtain ⟨T, hTB, hTcard⟩ := Finset.exists_subset_card_eq hB
    let e : Fin n₂ ↪ Fin (n₁ + n₂) := (T.orderEmbOfFin hTcard).toEmbedding
    let H : SimpleGraph (Fin n₂) := G.comap e
    rcases hn₂ H with ⟨t, htcard, htcl⟩ | ⟨t, htcard, htcl⟩
    · let u := t.map e
      have hucl : G.IsClique u := by
        have hm := htcl.finsetMap (f := e)
        exact hm.mono (SimpleGraph.map_comap_le e G)
      refine Or.inl ⟨u, ?_, hucl⟩
      simpa [u] using htcard
    · let u := t.map e
      have hucl : (Compl.compl G).IsClique u := by
        have hm := htcl.finsetMap (f := e)
        have hEq : Compl.compl (G.comap e) = (Compl.compl G).comap e := by
          ext x y
          simp [SimpleGraph.compl_adj]
        have hle : ((Compl.compl (G.comap e)).map e) ≤ Compl.compl G := by
          rw [hEq]
          exact SimpleGraph.map_comap_le e (Compl.compl G)
        exact hm.mono hle
      have hucard : u.card = s - 1 := by simp [u, htcard]
      have huT : ∀ x ∈ u, x ∈ T := by
        intro x hx
        rcases Finset.mem_map.mp hx with ⟨i, hi, rfl⟩
        simpa [e] using Finset.orderEmbOfFin_mem T hTcard i
      have huV : ∀ x ∈ u, x ∈ V := fun x hx => Finset.filter_subset _ _ (hTB (huT x hx))
      have huv : v ∉ u := by
        intro hvu
        have : v ∈ V := huV v hvu
        simp [V] at this
      refine Or.inr ⟨insert v u, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem huv, hucard]
        omega
      · intro x hx y hy hxy
        rcases Finset.mem_insert.mp hx with rfl | hx
        · rcases Finset.mem_insert.mp hy with rfl | hy
          · exact (hxy rfl).elim
          · have : y ∈ B := hTB (huT y hy)
            have hnot : ¬ G.Adj v y := (Finset.mem_filter.mp this).2
            exact (G.compl_adj v y).mpr ⟨hxy, hnot⟩
        · rcases Finset.mem_insert.mp hy with rfl | hy
          · have : x ∈ B := hTB (huT x hx)
            have hnot : ¬ G.Adj v x := (Finset.mem_filter.mp this).2
            exact (G.compl_adj x v).mpr ⟨hxy, fun h => hnot h.symm⟩
          · exact hucl hx hy hxy
