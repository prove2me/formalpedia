-- Prove2me | solution 1 for ConeLifts.StableSet.stab_facets
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T17:30:22.241417+00:00
-- url     : https://prove2.me/submissions/d13ad5d4-7416-49c4-b513-e23186069407

import Mathlib
import Definitions.Def_ConeLifts_StableSet_stab
import Definitions.Def_ConeLifts_StableSet_IsFacet



namespace ConeLifts.StableSet

lemma fc_incidenceVector_apply {n : ℕ} (S : Finset (Fin n)) (i : Fin n) :
    incidenceVector S i = if i ∈ S then 1 else 0 := by
  simp [incidenceVector]

lemma fc_mem_stab {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (hS : G.IsIndepSet (S : Set (Fin n))) : incidenceVector S ∈ stab G :=
  subset_convexHull ℝ _ ⟨S, hS, rfl⟩

lemma fc_single_mem {n : ℕ} (G : SimpleGraph (Fin n)) (i : Fin n) :
    incidenceVector {i} ∈ stab G := by
  apply fc_mem_stab
  intro a ha b hb hab
  simp at ha hb
  exact absurd (ha.trans hb.symm) hab

lemma fc_zero_eq {n : ℕ} : incidenceVector (∅ : Finset (Fin n)) = 0 := by
  ext i; simp [fc_incidenceVector_apply]

lemma fc_zero_mem {n : ℕ} (G : SimpleGraph (Fin n)) : (0 : EuclideanSpace ℝ (Fin n)) ∈ stab G := by
  rw [← fc_zero_eq]; exact fc_mem_stab G ∅ (by simp)

lemma fc_stab_nonneg {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∀ x ∈ stab G, ∀ i, 0 ≤ x i := by
  intro x hx
  have hc : Convex ℝ {x : EuclideanSpace ℝ (Fin n) | ∀ i, 0 ≤ x i} := by
    intro a ha b hb s t hs ht hst
    simp only [Set.mem_ofPred_eq] at *
    intro i
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    have := ha i; have := hb i
    positivity
  have hsub : {x | ∃ S : Finset (Fin n), G.IsIndepSet (S : Set (Fin n)) ∧
      x = incidenceVector S} ⊆ {x : EuclideanSpace ℝ (Fin n) | ∀ i, 0 ≤ x i} := by
    rintro _ ⟨S, -, rfl⟩ i
    rw [fc_incidenceVector_apply]
    split_ifs <;> norm_num
  exact convexHull_min hsub hc hx

lemma fc_span_top {n : ℕ} (S : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (h : ∀ j, incidenceVector {j} ∈ S) : S = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : x = ∑ j, x j • incidenceVector {j} := by
    ext i
    simp [fc_incidenceVector_apply]
  rw [hx]
  exact Submodule.sum_mem _ fun j _ => S.smul_mem _ (h j)

lemma fc_dim {n : ℕ} (S : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (v : EuclideanSpace ℝ (Fin n))
    (hv : v ∉ S) (hsup : S ⊔ (ℝ ∙ v) = ⊤) : Module.finrank ℝ S + 1 = n := by
  have hne : S ≠ ⊤ := by intro h; rw [h] at hv; exact hv trivial
  have h1 := Submodule.finrank_lt hne
  rw [finrank_euclideanSpace_fin] at h1
  have hv0 : v ≠ 0 := by rintro rfl; exact hv S.zero_mem
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq S (ℝ ∙ v)
  rw [hsup, finrank_span_singleton hv0, finrank_top, finrank_euclideanSpace_fin] at h2
  omega

lemma fc_vectorSpan_stab {n : ℕ} (G : SimpleGraph (Fin n)) :
    Module.finrank ℝ (vectorSpan ℝ (stab G)) = n := by
  have : vectorSpan ℝ (stab G) = ⊤ := by
    apply fc_span_top
    intro j
    have := vsub_mem_vectorSpan ℝ (fc_single_mem G j) (fc_zero_mem G)
    simpa using this
  rw [this, finrank_top, finrank_euclideanSpace_fin]

lemma fc_vectorSpan_le {n : ℕ} (F : Set (EuclideanSpace ℝ (Fin n)))
    (l : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (c : ℝ) (hF : ∀ x ∈ F, l x = c) :
    vectorSpan ℝ F ≤ LinearMap.ker (l : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ) := by
  rw [vectorSpan_def, Submodule.span_le]
  rintro _ ⟨a, ha, b, hb, rfl⟩
  simp [hF a ha, hF b hb]

theorem stab_facets_core {n : ℕ} (hn : 1 ≤ n) (G : SimpleGraph (Fin n)) :
    (∀ i : Fin n, IsFacet (stab G) {x | x ∈ stab G ∧ x i = 0}) ∧
      ∃ F : Set (EuclideanSpace ℝ (Fin n)), IsFacet (stab G) F ∧
        (0 : EuclideanSpace ℝ (Fin n)) ∉ F := by
  classical
  constructor
  · intro i
    refine ⟨fun _ => ⟨-(EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ), ?_⟩,
      ⟨0, fc_zero_mem G, by simp⟩, ?_, ?_⟩
    · have hp : ∀ x : EuclideanSpace ℝ (Fin n), EuclideanSpace.proj i x = x i := fun x => rfl
      ext x
      simp only [Set.mem_ofPred_eq, ContinuousLinearMap.neg_apply, hp, neg_le_neg_iff]
      constructor
      · rintro ⟨hx, hxi⟩
        exact ⟨hx, fun y hy => hxi ▸ fc_stab_nonneg G y hy i⟩
      · rintro ⟨hx, h⟩
        exact ⟨hx, le_antisymm (by simpa using h 0 (fc_zero_mem G)) (fc_stab_nonneg G x hx i)⟩
    · intro h
      have : incidenceVector {i} ∈ {x | x ∈ stab G ∧ x i = 0} := by
        rw [h]; exact fc_single_mem G i
      simp [fc_incidenceVector_apply] at this
    · rw [fc_vectorSpan_stab]
      apply fc_dim _ (incidenceVector {i})
      · intro hmem
        have := fc_vectorSpan_le _ (EuclideanSpace.proj i) 0 (fun x hx => hx.2) hmem
        simp [fc_incidenceVector_apply] at this
      · apply fc_span_top
        intro j
        by_cases hji : j = i
        · subst hji; exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
        · apply Submodule.mem_sup_left
          have h1 : incidenceVector {j} ∈ {x | x ∈ stab G ∧ x i = 0} :=
            ⟨fc_single_mem G j, by simp [fc_incidenceVector_apply, Ne.symm hji]⟩
          have h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ {x | x ∈ stab G ∧ x i = 0} :=
            ⟨fc_zero_mem G, by simp⟩
          simpa using vsub_mem_vectorSpan ℝ h1 h0
  · -- a maximum clique
    let cliques : Finset (Finset (Fin n)) := Finset.univ.filter
      (fun s : Finset (Fin n) => G.IsClique (s : Set (Fin n)))
    have hne : cliques.Nonempty := ⟨∅, by simp [cliques]⟩
    obtain ⟨C, hCmem, hCmax⟩ := Finset.exists_max_image cliques Finset.card hne
    have hC : G.IsClique (C : Set (Fin n)) := by simpa [cliques] using hCmem
    let i0 : Fin n := ⟨0, hn⟩
    have hCne : C.Nonempty := by
      have : ({i0} : Finset (Fin n)) ∈ cliques := by simp [cliques]
      have := hCmax _ this
      rw [Finset.card_singleton] at this
      exact Finset.card_pos.mp this
    obtain ⟨c0, hc0⟩ := hCne
    have hext : ∀ j ∉ C, ∃ c ∈ C, c ≠ j ∧ ¬ G.Adj c j := by
      intro j hj
      by_contra hcon
      push_neg at hcon
      have : insert j C ∈ cliques := by
        simp only [cliques, Finset.mem_filter, Finset.mem_univ, true_and, Finset.coe_insert]
        refine hC.insert ?_
        intro c hc hcj
        exact (hcon c hc (Ne.symm hcj)).symm
      have := hCmax _ this
      rw [Finset.card_insert_of_notMem hj] at this
      omega
    let l : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := ∑ c ∈ C, EuclideanSpace.proj c
    have hl : ∀ x, l x = ∑ c ∈ C, x c := by
      intro x
      show (∑ c ∈ C, (EuclideanSpace.proj c : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) x = _
      rw [ContinuousLinearMap.sum_apply]
      rfl
    have hlS : ∀ S : Finset (Fin n), l (incidenceVector S) = (C ∩ S).card := by
      intro S
      rw [hl]
      simp only [fc_incidenceVector_apply]
      rw [Finset.sum_boole, Finset.filter_mem_eq_inter]
    have hle : ∀ x ∈ stab G, l x ≤ 1 := by
      intro x hx
      have hc : Convex ℝ {x : EuclideanSpace ℝ (Fin n) | l x ≤ 1} := by
        intro a ha b hb s t hs ht hst
        simp only [Set.mem_ofPred_eq, map_add, map_smul, smul_eq_mul] at *
        nlinarith
      have hsub : {x | ∃ S : Finset (Fin n), G.IsIndepSet (S : Set (Fin n)) ∧
          x = incidenceVector S} ⊆ {x : EuclideanSpace ℝ (Fin n) | l x ≤ 1} := by
        rintro _ ⟨S, hS, rfl⟩
        simp only [Set.mem_ofPred_eq, hlS]
        have : (C ∩ S).card ≤ 1 := by
          rw [Finset.card_le_one]
          intro a ha b hb
          by_contra hab
          simp only [Finset.mem_inter] at ha hb
          exact hS ha.2 hb.2 hab (hC ha.1 hb.1 hab)
        exact_mod_cast this
      exact convexHull_min hsub hc hx
    have hlc0 : l (incidenceVector {c0}) = 1 := by
      rw [hlS]; simp [hc0]
    set F : Set (EuclideanSpace ℝ (Fin n)) := {x | x ∈ stab G ∧ l x = 1} with hFdef
    have hc0F : incidenceVector {c0} ∈ F := ⟨fc_single_mem G c0, hlc0⟩
    have hpairF : ∀ j ∉ C, ∃ c ∈ C, incidenceVector {c, j} ∈ F := by
      intro j hj
      obtain ⟨c, hc, hcj, hadj⟩ := hext j hj
      refine ⟨c, hc, fc_mem_stab G _ ?_, ?_⟩
      · intro a ha b hb hab
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact absurd rfl hab
        · exact hadj
        · exact fun h => hadj h.symm
        · exact absurd rfl hab
      · rw [hlS]
        have : C ∩ {c, j} = {c} := by
          ext a
          simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨ha, rfl | rfl⟩
            · rfl
            · exact absurd ha hj
          · rintro rfl; exact ⟨hc, Or.inl rfl⟩
        rw [this]; simp
    refine ⟨F, ⟨fun _ => ⟨l, ?_⟩, ⟨_, hc0F⟩, ?_, ?_⟩, ?_⟩
    · ext x
      simp only [hFdef, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨hx, hx1⟩
        exact ⟨hx, fun y hy => hx1 ▸ hle y hy⟩
      · rintro ⟨hx, h⟩
        exact ⟨hx, le_antisymm (hle x hx) (hlc0 ▸ h _ (fc_single_mem G c0))⟩
    · intro h
      have : (0 : EuclideanSpace ℝ (Fin n)) ∈ F := h ▸ fc_zero_mem G
      have := this.2
      simp at this
    · rw [fc_vectorSpan_stab]
      apply fc_dim _ (incidenceVector {c0})
      · intro hmem
        have := fc_vectorSpan_le F l 1 (fun x hx => hx.2) hmem
        simp [hlc0] at this
      · apply fc_span_top
        set T := vectorSpan ℝ F ⊔ (ℝ ∙ incidenceVector {c0}) with hT
        have hc0T : incidenceVector {c0} ∈ T :=
          Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
        have hFT : ∀ x ∈ F, x ∈ T := by
          intro x hx
          have h1 : x - incidenceVector {c0} ∈ T :=
            Submodule.mem_sup_left (by simpa using vsub_mem_vectorSpan ℝ hx hc0F)
          simpa using T.add_mem h1 hc0T
        have hCT : ∀ c ∈ C, incidenceVector {c} ∈ T := by
          intro c hc
          apply hFT
          refine ⟨fc_single_mem G c, ?_⟩
          rw [hlS]; simp [hc]
        intro j
        by_cases hj : j ∈ C
        · exact hCT j hj
        · obtain ⟨c, hc, hcF⟩ := hpairF j hj
          have hcj : c ≠ j := fun h => hj (h ▸ hc)
          have heq : incidenceVector {j} = incidenceVector {c, j} - incidenceVector {c} := by
            ext a
            simp only [fc_incidenceVector_apply, PiLp.sub_apply, Finset.mem_insert,
              Finset.mem_singleton]
            by_cases h1 : a = c <;> by_cases h2 : a = j <;> simp_all
          rw [heq]
          exact T.sub_mem (hFT _ hcF) (hCT c hc)
    · intro h0
      have := h0.2
      simp at this

end ConeLifts.StableSet

open ConeLifts.StableSet


theorem solution {n : ℕ} (hn : 1 ≤ n) (G : SimpleGraph (Fin n)) :
    (∀ i : Fin n, IsFacet (stab G) {x | x ∈ stab G ∧ x i = 0}) ∧
      ∃ F : Set (EuclideanSpace ℝ (Fin n)), IsFacet (stab G) F ∧
        (0 : EuclideanSpace ℝ (Fin n)) ∉ F := by
  exact stab_facets_core hn G
