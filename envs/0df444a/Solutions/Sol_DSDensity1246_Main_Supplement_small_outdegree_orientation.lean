-- Prove2me | solution 1 for DSDensity1246.Main.Supplement.small_outdegree_orientation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T16:38:14.060328+00:00
-- url     : https://prove2.me/submissions/78b81f74-7cbf-453f-a8b5-2c9f12583a9a

import Mathlib
import Definitions.Def_DSDensity1246_Main_Supplement_orientation
import Definitions.Def_DSDensity1246_Main_maximumDensity

section
set_option autoImplicit false

namespace DSDensity1246.Dev.Orient

open DSDensity1246.Main DSDensity1246.Main.Supplement
open scoped Classical
open scoped NNReal

noncomputable def num {Y : Type*} {n : ℕ} (ℓ : ℕ) (V : Finset (Fin n → Y)) : ℕ :=
  ∑ i : Fin n, ∑ a ∈ finiteBehaviors V i, ((finiteFiber V i a).card - ℓ)

lemma num_le {Y : Type*} {n : ℕ} (ℓ : ℕ) (V : Finset (Fin n → Y)) :
    num ℓ V ≤ n * V.card := by
  unfold num
  calc _ ≤ ∑ i : Fin n, ∑ a ∈ finiteBehaviors V i, (finiteFiber V i a).card :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun a _ => Nat.sub_le _ _
    _ = ∑ _i : Fin n, V.card := Finset.sum_congr rfl fun i _ => by
        unfold finiteBehaviors finiteFiber
        convert (Finset.card_eq_sum_card_image (away i) V).symm
    _ = n * V.card := by simp

lemma listDensity_le_n {Y : Type*} {n : ℕ} (ℓ : ℕ) (V : Finset (Fin n → Y)) :
    listDensity ℓ V ≤ n := by
  unfold listDensity
  rcases V.eq_empty_or_nonempty with rfl | hV
  · simp
  · rw [div_le_iff₀ (by exact_mod_cast hV.card_pos)]
    have := num_le ℓ V
    unfold num at this
    exact_mod_cast this

lemma density_le_max {Y : Type*} {n : ℕ} (ℓ : ℕ) (W : Set (Fin n → Y))
    (V : Finset (Fin n → Y)) (hV : V.Nonempty) (hsub : (↑V : Set (Fin n → Y)) ⊆ W) :
    listDensity ℓ V ≤ maximumDensity ℓ W n := by
  unfold maximumDensity
  apply le_csSup
  · refine ⟨n, ?_⟩
    rintro r ⟨S, V', _, _, rfl⟩
    exact listDensity_le_n _ _
  · refine ⟨id, V, hV, ?_, rfl⟩
    simpa [MulticlassDS.Compress.proj] using hsub

lemma num_le_D {Y : Type*} {n : ℕ} (ℓ : ℕ) (W : Set (Fin n → Y))
    (V : Finset (Fin n → Y)) (hsub : (↑V : Set (Fin n → Y)) ⊆ W) :
    num ℓ V ≤ ⌈maximumDensity ℓ W n⌉₊ * V.card := by
  rcases V.eq_empty_or_nonempty with rfl | hV
  · simp [num, finiteBehaviors]
  · have h1 := density_le_max ℓ W V hV hsub
    have h2 : maximumDensity ℓ W n ≤ (⌈maximumDensity ℓ W n⌉₊ : ℝ≥0) := Nat.le_ceil _
    have h3 := h1.trans h2
    unfold listDensity at h3
    rw [div_le_iff₀ (by exact_mod_cast hV.card_pos)] at h3
    unfold num
    exact_mod_cast h3

abbrev K (Y : Type*) (n : ℕ) := Σ i : Fin n, ({j : Fin n // j ≠ i} → Y)

noncomputable def tset {Y : Type*} {n : ℕ} (ℓ D : ℕ) (W : Set (Fin n → Y)) (p : W × Fin n) :
    Finset (K Y n × Fin ℓ ⊕ W × Fin D) :=
  (Finset.univ : Finset (Fin ℓ)).image (fun j => Sum.inl (⟨p.2, away p.2 p.1.1⟩, j)) ∪
  (Finset.univ : Finset (Fin D)).image (fun d => Sum.inr (p.1, d))

lemma hall_cond {Y : Type*} {n : ℕ} (ℓ : ℕ) (W : Set (Fin n → Y)) (s : Finset (W × Fin n)) :
    s.card ≤ (s.biUnion (tset ℓ ⌈maximumDensity ℓ W n⌉₊ W)).card := by
  set D := ⌈maximumDensity ℓ W n⌉₊ with hD
  let V' : Finset W := s.image Prod.fst
  let Vf : Finset (Fin n → Y) := V'.image Subtype.val
  let key : W × Fin n → K Y n := fun p => ⟨p.2, away p.2 p.1.1⟩
  let Kset : Finset (K Y n) := s.image key
  have hVf : (↑Vf : Set (Fin n → Y)) ⊆ W := by
    intro x hx
    simp only [Vf, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx
    obtain ⟨v, _, rfl⟩ := hx
    exact v.2
  have hVfc : Vf.card = V'.card := Finset.card_image_of_injective _ Subtype.val_injective
  -- Step A
  have hA : s.card ≤ ∑ k ∈ Kset, (finiteFiber Vf k.1 k.2).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := key) (t := Kset) (fun p hp => Finset.mem_image_of_mem _ hp)]
    refine Finset.sum_le_sum fun k hk => ?_
    refine Finset.card_le_card_of_injOn (fun p => p.1.1) ?_ ?_
    · intro p hp
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hp
      obtain ⟨hps, rfl⟩ := hp
      simp only [finiteFiber, Finset.coe_filter, Set.mem_ofPred_eq]
      exact ⟨Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hps), rfl⟩
    · intro p hp q hq hpq
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hp hq
      have h1 : p.2 = q.2 := by
        have := hp.2.trans hq.2.symm
        exact congrArg Sigma.fst this
      exact Prod.ext (Subtype.ext hpq) h1
  -- Step B
  have hB : ∑ k ∈ Kset, ((finiteFiber Vf k.1 k.2).card - ℓ) ≤ num ℓ Vf := by
    unfold num
    rw [Finset.sum_sigma' (s := (Finset.univ : Finset (Fin n))) (t := fun i => finiteBehaviors Vf i)
      (f := fun i a => (finiteFiber Vf i a).card - ℓ)]
    refine Finset.sum_le_sum_of_subset ?_
    intro k hk
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
    simp only [Finset.mem_sigma, Finset.mem_univ, true_and, key]
    exact Finset.mem_image.mpr ⟨p.1.1, Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hp), rfl⟩
  have hB' : ∑ k ∈ Kset, (finiteFiber Vf k.1 k.2).card ≤
      num ℓ Vf + ℓ * Kset.card := by
    calc _ ≤ ∑ k ∈ Kset, (((finiteFiber Vf k.1 k.2).card - ℓ) + ℓ) :=
          Finset.sum_le_sum fun k _ => by omega
      _ = ∑ k ∈ Kset, ((finiteFiber Vf k.1 k.2).card - ℓ) + Kset.card * ℓ := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]
      _ ≤ _ := by
        have := hB
        nlinarith
  -- Step C
  have hC : ℓ * Kset.card + D * V'.card ≤ (s.biUnion (tset ℓ D W)).card := by
    let T1 : Finset (K Y n × Fin ℓ ⊕ W × Fin D) :=
      (Kset ×ˢ (Finset.univ : Finset (Fin ℓ))).map ⟨Sum.inl, Sum.inl_injective⟩
    let T2 : Finset (K Y n × Fin ℓ ⊕ W × Fin D) :=
      (V' ×ˢ (Finset.univ : Finset (Fin D))).map ⟨Sum.inr, Sum.inr_injective⟩
    have hdisj : Disjoint T1 T2 := by
      rw [Finset.disjoint_left]
      intro x hx hx2
      simp only [T1, T2, Finset.mem_map, Function.Embedding.coeFn_mk] at hx hx2
      obtain ⟨a, _, rfl⟩ := hx
      obtain ⟨b, _, hb⟩ := hx2
      exact Sum.inr_ne_inl hb
    have hsub : T1 ∪ T2 ⊆ s.biUnion (tset ℓ D W) := by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · simp only [T1, Finset.mem_map, Function.Embedding.coeFn_mk, Finset.mem_product,
          Finset.mem_univ, and_true] at hx
        obtain ⟨⟨k, j⟩, hk, rfl⟩ := hx
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
        exact Finset.mem_biUnion.mpr ⟨p, hp, by
          simp only [tset, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
          exact Or.inl ⟨j, rfl⟩⟩
      · simp only [T2, Finset.mem_map, Function.Embedding.coeFn_mk, Finset.mem_product,
          Finset.mem_univ, and_true] at hx
        obtain ⟨⟨v, d⟩, hv, rfl⟩ := hx
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
        exact Finset.mem_biUnion.mpr ⟨p, hp, by
          simp only [tset, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
          exact Or.inr ⟨d, rfl⟩⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj] at this
    simp only [T1, T2, Finset.card_map, Finset.card_product, Finset.card_univ,
      Fintype.card_fin] at this
    nlinarith
  have hD' := num_le_D ℓ W Vf hVf
  rw [hVfc] at hD'
  nlinarith


noncomputable def sel {Y : Type*} {n : ℕ} (ℓ D : ℕ) (W : Set (Fin n → Y))
    (f : W × Fin n → K Y n × Fin ℓ ⊕ W × Fin D) (e : OneInclusionEdge W) :
    Finset (Fin n → Y) :=
  (Finset.univ : Finset (Fin ℓ)).biUnion (fun j =>
    if h : ∃ p : W × Fin n, f p = Sum.inl (⟨e.1, e.2.1⟩, j) then {(h.choose.1 : Fin n → Y)}
    else ∅)

lemma key_eq {Y : Type*} {n : ℕ} (ℓ D : ℕ) (W : Set (Fin n → Y))
    (f : W × Fin n → K Y n × Fin ℓ ⊕ W × Fin D) (hf : ∀ x, f x ∈ tset ℓ D W x)
    (e : OneInclusionEdge W) (j : Fin ℓ) (p : W × Fin n)
    (hp : f p = Sum.inl (⟨e.1, e.2.1⟩, j)) : p.1.1 ∈ edge W e.1 e.2.1 := by
  have h := hf p
  rw [hp] at h
  simp only [tset, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at h
  rcases h with ⟨j', hj'⟩ | ⟨d, hd⟩
  · obtain ⟨hk, -⟩ := Prod.mk.inj (Sum.inl.inj hj').symm
    obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp hk
    obtain ⟨i, a, ha⟩ := e
    obtain ⟨v, q⟩ := p
    dsimp only at h1 h2 ⊢
    subst h1
    exact ⟨v.2, (eq_of_heq h2).symm⟩
  · exact absurd hd (by simp)

lemma sel_incident {Y : Type*} {n : ℕ} (ℓ D : ℕ) (W : Set (Fin n → Y))
    (f : W × Fin n → K Y n × Fin ℓ ⊕ W × Fin D) (hf : ∀ x, f x ∈ tset ℓ D W x)
    (e : OneInclusionEdge W) : (↑(sel ℓ D W f e) : Set (Fin n → Y)) ⊆ edge W e.1 e.2.1 := by
  intro v hv
  simp only [sel, Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true,
    Set.mem_iUnion] at hv
  obtain ⟨j, hj⟩ := hv
  by_cases h : ∃ p : W × Fin n, f p = Sum.inl (⟨e.1, e.2.1⟩, j)
  · rw [dif_pos h] at hj
    simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hj
    rw [hj]
    exact key_eq ℓ D W f hf e j _ h.choose_spec
  · rw [dif_neg h] at hj
    simp at hj

lemma sel_card {Y : Type*} {n : ℕ} (ℓ D : ℕ) (W : Set (Fin n → Y))
    (f : W × Fin n → K Y n × Fin ℓ ⊕ W × Fin D) (e : OneInclusionEdge W) :
    (sel ℓ D W f e).card ≤ ℓ := by
  unfold sel
  refine (Finset.card_biUnion_le).trans ?_
  calc _ ≤ ∑ _j : Fin ℓ, 1 := Finset.sum_le_sum fun j _ => by
        split_ifs <;> simp
    _ = ℓ := by simp

lemma outdeg_le {Y : Type*} {n : ℕ} (ℓ D : ℕ) (W : Set (Fin n → Y))
    (f : W × Fin n → K Y n × Fin ℓ ⊕ W × Fin D) (hf : ∀ x, f x ∈ tset ℓ D W x)
    (hinj : Function.Injective f) (w : W) :
    (Finset.univ.filter (fun i : Fin n => w.1 ∉ sel ℓ D W f (incidentEdge w i))).card ≤ D := by
  let T : Finset (K Y n × Fin ℓ ⊕ W × Fin D) :=
    (Finset.univ : Finset (Fin D)).image (fun d => Sum.inr (w, d))
  have hT : T.card ≤ D := by
    refine Finset.card_image_le.trans ?_
    simp
  refine le_trans (Finset.card_le_card_of_injOn (fun i => f (w, i)) ?_ ?_) hT
  · intro i hi
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hi
    have h := hf (w, i)
    simp only [tset, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at h
    rcases h with ⟨j, hj⟩ | ⟨d, hd⟩
    · exfalso
      apply hi
      have h : ∃ p : W × Fin n, f p = Sum.inl (⟨(incidentEdge w i).1, (incidentEdge w i).2.1⟩, j) :=
        ⟨(w, i), hj.symm⟩
      simp only [sel, Finset.mem_biUnion, Finset.mem_univ, true_and]
      refine ⟨j, ?_⟩
      rw [dif_pos h]
      have := hinj (h.choose_spec.trans hj)
      rw [this]
      simp
    · simp only [T, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
      exact ⟨d, hd⟩
  · intro i _ i' _ h
    exact (Prod.mk.inj (hinj h)).2

theorem exists_orientation {Y : Type*} {n : ℕ} (ℓ : ℕ) (W : Set (Fin n → Y)) :
    ∃ σ : ListOrientation ℓ W, ∀ w : W, listOutdegree σ w ≤ ⌈maximumDensity ℓ W n⌉₊ := by
  obtain ⟨f, hinj, hf⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective
    (tset ℓ ⌈maximumDensity ℓ W n⌉₊ W)).mp (hall_cond ℓ W)
  refine ⟨⟨sel ℓ _ W f, sel_incident ℓ _ W f hf, sel_card ℓ _ W f⟩, fun w => ?_⟩
  unfold listOutdegree
  exact outdeg_le ℓ _ W f hf hinj w

end DSDensity1246.Dev.Orient

set_option autoImplicit false

namespace DSDensity1246.Main.Supplement

/-- Lemma A.1, p.45. No finiteness restriction, including n=0. -/
theorem chk_small_outdegree_orientation {Y : Type*} (n ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (W : Set (Fin n → Y)) :
    ∃ σ : ListOrientation ℓ W, ∀ w : W,
      listOutdegree σ w ≤ ⌈maximumDensity ℓ W n⌉₊ :=
  DSDensity1246.Dev.Orient.exists_orientation ℓ W


end DSDensity1246.Main.Supplement
end

theorem solution : type_of% @DSDensity1246.Main.Supplement.chk_small_outdegree_orientation := @DSDensity1246.Main.Supplement.chk_small_outdegree_orientation
