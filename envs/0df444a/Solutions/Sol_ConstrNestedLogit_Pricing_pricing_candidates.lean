-- Prove2me | solution 1 for ConstrNestedLogit.Pricing.pricing_candidates
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T13:34:28.490273+00:00
-- url     : https://prove2.me/submissions/9035536a-c496-4606-b349-86bf1eefd17c

import Mathlib
import Definitions.Def_NestedLogitVariants_LP_Model
import Definitions.Def_ConstrNestedLogit_Pricing_Model

set_option autoImplicit false

namespace PCand98

open NestedLogitVariants.LP ConstrNestedLogit.Pricing

lemma line_nonneg {a c t δ u : ℝ} {T : Finset ℝ} (htu : t ≤ u)
    (hgap : ∀ z ∈ T, t < z → u < z ∧ t + δ < z) (hδ : 0 < δ)
    (hroot : c ≠ 0 → a / c ∈ T) (hm : 0 ≤ a - c * (t + δ)) : 0 ≤ a - c * u := by
  by_contra h
  push Not at h
  by_cases hc : c = 0
  · subst hc; simp at h hm; linarith
  have hz := hroot hc
  have ha : a = c * (a / c) := by field_simp
  rcases lt_or_gt_of_ne hc with hc' | hc'
  · -- c < 0
    have h1 : u < a / c := by
      by_contra h2; push Not at h2
      have : c * (a / c) ≥ c * u := by nlinarith
      linarith
    have h2 := (hgap _ hz (lt_of_le_of_lt htu h1)).2
    have : c * (a / c) < c * (t + δ) := by nlinarith
    linarith
  · -- c > 0
    have h1 : t + δ ≤ a / c := by
      by_contra h2; push Not at h2
      have : c * (a / c) < c * (t + δ) := by nlinarith
      linarith
    have h2 := (hgap _ hz (by linarith)).1
    have : c * u < c * (a / c) := by nlinarith
    linarith

variable {ι : Type*} {n p : ℕ}

lemma obj7_eq (I : Instance ι n) (i : ι) (hvnp : I.vnp i = 0) (hv : ∀ j, 0 < I.v i j)
    (u : ℝ) (X : Finset (Fin n)) :
    obj7 I i u X = ∑ j ∈ X, I.v i j * (I.r i j - u) := by
  simp only [obj7, R, V, hvnp, zero_add]
  by_cases hX : X = ∅
  · subst hX; simp
  have hpos : 0 < ∑ j ∈ X, I.v i j :=
    Finset.sum_pos (fun j _ => hv j) (Finset.nonempty_iff_ne_empty.mpr hX)
  have h1 : (∑ j ∈ X, I.v i j) * ((∑ j ∈ X, I.r i j * I.v i j) / ∑ j ∈ X, I.v i j)
      = ∑ j ∈ X, I.r i j * I.v i j := by field_simp
  rw [mul_sub, h1, Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _; ring

lemma sum_line (I : Instance ι n) (i : ι) (u : ℝ) (Y : Finset (Fin n)) :
    ∑ j ∈ Y, I.v i j * (I.r i j - u)
      = (∑ j ∈ Y, I.v i j * I.r i j) - (∑ j ∈ Y, I.v i j) * u := by
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _; ring

lemma exists_opt (I : Instance ι n) (prod : Fin n → Fin p) (i : ι) (w : ℝ) :
    ∃ S, IsOptimal7 I prod i w S := by
  classical
  obtain ⟨S, hS, hmax⟩ := (Finset.univ.filter (fun S : Finset (Fin n) => PricingFeasible prod S)).exists_max_image
    (obj7 I i w) ⟨∅, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; intro k; simp⟩
  exact ⟨S, (Finset.mem_filter.1 hS).2, fun S' h => hmax S' (by simp [h])⟩

lemma card_le_one_cases {Y : Finset (Fin n)} (h : Y.card ≤ 1) : Y = ∅ ∨ ∃ j, Y = {j} := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h with h0 | h1
  · exact Or.inl (Finset.card_eq_zero.1 h0)
  · exact Or.inr (Finset.card_eq_one.1 h1)

noncomputable def cross (I : Instance ι n) (i : ι) (q : Fin n × Fin n) : ℝ :=
  (I.v i q.1 * I.r i q.1 - I.v i q.2 * I.r i q.2) / (I.v i q.1 - I.v i q.2)

noncomputable def Tset (I : Instance ι n) (i : ι) (prod : Fin n → Fin p) : Finset ℝ :=
  insert 0 (Finset.univ.image (I.r i) ∪
    (Finset.univ.filter (fun q : Fin n × Fin n => prod q.1 = prod q.2)).image (cross I i))

lemma Tset_card (I : Instance ι n) (i : ι) (prod : Fin n → Fin p) (b : ℕ)
    (hb : IsVirtualProductMap prod b) : (Tset I i prod).card ≤ p * (b + 1) ^ 2 + 1 := by
  classical
  have hn : n = p * b := by
    have := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin n)))
      (t := (Finset.univ : Finset (Fin p))) (f := prod) (fun _ _ => Finset.mem_univ _)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    rw [this]
    have hb' : ∀ k : Fin p, (Finset.univ.filter (fun j => prod j = k)).card = b := hb
    simp [hb']
  have hpairs : (Finset.univ.filter (fun q : Fin n × Fin n => prod q.1 = prod q.2)).card ≤ p * b ^ 2 := by
    have hsub : Finset.univ.filter (fun q : Fin n × Fin n => prod q.1 = prod q.2) ⊆
        (Finset.univ : Finset (Fin p)).biUnion (fun k =>
          (Finset.univ.filter (fun j => prod j = k)) ×ˢ (Finset.univ.filter (fun j => prod j = k))) := by
      intro q hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
      simp [hq]
    refine (Finset.card_le_card hsub).trans ((Finset.card_biUnion_le).trans ?_)
    have hb' : ∀ k : Fin p, (Finset.univ.filter (fun j => prod j = k)).card = b := hb
    simp [Finset.card_product, hb', sq]
  have h1 : (Finset.univ.image (I.r i)).card ≤ n :=
    (Finset.card_image_le).trans (by simp)
  have h2 := (Finset.card_image_le (s := Finset.univ.filter (fun q : Fin n × Fin n => prod q.1 = prod q.2))
    (f := cross I i)).trans hpairs
  unfold Tset
  refine (Finset.card_insert_le _ _).trans ?_
  have h3 := Finset.card_union_le (Finset.univ.image (I.r i))
    ((Finset.univ.filter (fun q : Fin n × Fin n => prod q.1 = prod q.2)).image (cross I i))
  have : n + p * b ^ 2 ≤ p * (b + 1) ^ 2 := by
    subst hn; nlinarith [Nat.zero_le (p * b), Nat.zero_le p]
  omega

lemma exists_gap (T : Finset ℝ) : ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ T, ∀ z ∈ T, t < z → t + δ < z := by
  classical
  let D := ((T ×ˢ T).filter (fun q : ℝ × ℝ => q.1 < q.2)).image (fun q => q.2 - q.1)
  by_cases hD : D.Nonempty
  · refine ⟨D.min' hD / 2, ?_, ?_⟩
    · have hmem := D.min'_mem hD
      simp only [D, Finset.mem_image, Finset.mem_filter, Finset.mem_product] at hmem
      obtain ⟨q, ⟨_, hq⟩, he⟩ := hmem
      rw [← he]; linarith
    · intro t ht z hz htz
      have hle : D.min' hD ≤ z - t := D.min'_le _ (by
        simp only [D, Finset.mem_image, Finset.mem_filter, Finset.mem_product]
        exact ⟨(t, z), ⟨⟨ht, hz⟩, htz⟩, rfl⟩)
      have hmem := D.min'_mem hD
      simp only [D, Finset.mem_image, Finset.mem_filter, Finset.mem_product] at hmem
      obtain ⟨q, ⟨_, hq⟩, he⟩ := hmem
      have : 0 < D.min' hD := by rw [← he]; linarith
      linarith
  · refine ⟨1, one_pos, ?_⟩
    intro t ht z hz htz
    exact absurd ⟨z - t, by
      simp only [D, Finset.mem_image, Finset.mem_filter, Finset.mem_product]
      exact ⟨(t, z), ⟨⟨ht, hz⟩, htz⟩, rfl⟩⟩ hD

/-- the per-product swap inequality at the representative point -/
lemma swap_le (I : Instance ι n) (prod : Fin n → Fin p) (i : ι)
    (hvnp : I.vnp i = 0) (hv : ∀ j, 0 < I.v i j) (w : ℝ) (S S' : Finset (Fin n))
    (hS : IsOptimal7 I prod i w S) (hS' : PricingFeasible prod S') (k : Fin p) :
    ∑ j ∈ S'.filter (fun j => prod j = k), I.v i j * (I.r i j - w)
      ≤ ∑ j ∈ S.filter (fun j => prod j = k), I.v i j * (I.r i j - w) := by
  classical
  set S'' := S.filter (fun j => ¬ prod j = k) ∪ S'.filter (fun j => prod j = k) with hS''
  have hfeas : PricingFeasible prod S'' := by
    intro k'
    by_cases hk : k' = k
    · subst hk
      refine le_trans (Finset.card_le_card ?_) (hS' k')
      intro j hj
      simp only [hS'', Finset.mem_filter, Finset.mem_union] at hj ⊢
      tauto
    · refine le_trans (Finset.card_le_card ?_) (hS.1 k')
      intro j hj
      simp only [hS'', Finset.mem_filter, Finset.mem_union] at hj ⊢
      rcases hj with ⟨h1 | h1, h2⟩
      · exact ⟨h1.1, h2⟩
      · exact absurd (h2.symm.trans h1.2) hk
  have hopt := hS.2 S'' hfeas
  rw [obj7_eq I i hvnp hv, obj7_eq I i hvnp hv] at hopt
  have hdisj : Disjoint (S.filter (fun j => ¬ prod j = k)) (S'.filter (fun j => prod j = k)) := by
    rw [Finset.disjoint_left]
    intro j h1 h2
    exact (Finset.mem_filter.1 h1).2 (Finset.mem_filter.1 h2).2
  rw [hS'', Finset.sum_union hdisj] at hopt
  have hsplit := Finset.sum_filter_add_sum_filter_not S (fun j => prod j = k)
    (fun j => I.v i j * (I.r i j - w))
  linarith

lemma root_mem (I : Instance ι n) (prod : Fin n → Fin p) (i : ι) (hv : ∀ j, 0 < I.v i j)
    (S S' : Finset (Fin n)) (hS : PricingFeasible prod S) (hS' : PricingFeasible prod S') (k : Fin p) :
    ((∑ j ∈ S.filter (fun j => prod j = k), I.v i j) - ∑ j ∈ S'.filter (fun j => prod j = k), I.v i j) ≠ 0 →
    ((∑ j ∈ S.filter (fun j => prod j = k), I.v i j * I.r i j)
        - ∑ j ∈ S'.filter (fun j => prod j = k), I.v i j * I.r i j) /
      ((∑ j ∈ S.filter (fun j => prod j = k), I.v i j) - ∑ j ∈ S'.filter (fun j => prod j = k), I.v i j)
      ∈ Tset I i prod := by
  classical
  intro hc
  have mk : ∀ j, j ∈ S.filter (fun j => prod j = k) → prod j = k := fun j h => (Finset.mem_filter.1 h).2
  have mk' : ∀ j, j ∈ S'.filter (fun j => prod j = k) → prod j = k := fun j h => (Finset.mem_filter.1 h).2
  unfold Tset
  rcases card_le_one_cases (hS k) with h1 | ⟨j, h1⟩ <;>
    rcases card_le_one_cases (hS' k) with h2 | ⟨j', h2⟩
  · rw [h1, h2] at hc; simp at hc
  · rw [h1, h2]
    have hj := hv j'
    have : ((∑ x ∈ (∅ : Finset (Fin n)), I.v i x * I.r i x) - ∑ x ∈ ({j'} : Finset (Fin n)), I.v i x * I.r i x) /
        ((∑ x ∈ (∅ : Finset (Fin n)), I.v i x) - ∑ x ∈ ({j'} : Finset (Fin n)), I.v i x) = I.r i j' := by
      simp only [Finset.sum_empty, Finset.sum_singleton, zero_sub, neg_div_neg_eq]
      field_simp
    rw [this]
    simp
  · rw [h1, h2]
    have hj := hv j
    have : ((∑ x ∈ ({j} : Finset (Fin n)), I.v i x * I.r i x) - ∑ x ∈ (∅ : Finset (Fin n)), I.v i x * I.r i x) /
        ((∑ x ∈ ({j} : Finset (Fin n)), I.v i x) - ∑ x ∈ (∅ : Finset (Fin n)), I.v i x) = I.r i j := by
      simp only [Finset.sum_empty, Finset.sum_singleton, sub_zero]
      field_simp
    rw [this]
    simp
  · have hpj : prod j = k := mk j (by rw [h1]; simp)
    have hpj' : prod j' = k := mk' j' (by rw [h2]; simp)
    rw [h1, h2]
    simp only [Finset.sum_singleton]
    apply Finset.mem_insert_of_mem
    apply Finset.mem_union_right
    rw [Finset.mem_image]
    exact ⟨(j, j'), by simp [hpj, hpj'], rfl⟩

end PCand98

open NestedLogitVariants.LP ConstrNestedLogit.Pricing in
theorem solution {ι : Type*} {n p b : ℕ} (I : Instance ι n) (i : ι)
    (hvnp : I.vnp i = 0) (hv : ∀ j, 0 < I.v i j)
    (prod : Fin n → Fin p) (hb : IsVirtualProductMap prod b) :
    ∃ A : Finset (Finset (Fin n)),
      (∀ S ∈ A, PricingFeasible prod S) ∧
      A.card ≤ p * (b + 1) ^ 2 + 1 ∧
      ∀ u : ℝ, 0 ≤ u → ∃ S ∈ A, IsOptimal7 I prod i u S := by
  classical
  obtain ⟨δ, hδ, hgapδ⟩ := PCand98.exists_gap (PCand98.Tset I i prod)
  let ψ : ℝ → Finset (Fin n) := fun t => (PCand98.exists_opt I prod i (t + δ)).choose
  have hψ : ∀ t, IsOptimal7 I prod i (t + δ) (ψ t) := fun t => (PCand98.exists_opt I prod i (t + δ)).choose_spec
  refine ⟨(PCand98.Tset I i prod).image ψ, ?_, ?_, ?_⟩
  · intro S hS
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.1 hS
    exact (hψ t).1
  · exact (Finset.card_image_le).trans (PCand98.Tset_card I i prod b hb)
  · intro u hu
    have hne : ((PCand98.Tset I i prod).filter (fun x => x ≤ u)).Nonempty :=
      ⟨0, by simp [PCand98.Tset, hu]⟩
    set t := ((PCand98.Tset I i prod).filter (fun x => x ≤ u)).max' hne with ht
    have htmem := Finset.max'_mem _ hne
    rw [← ht, Finset.mem_filter] at htmem
    have hgap : ∀ z ∈ PCand98.Tset I i prod, t < z → u < z ∧ t + δ < z := by
      intro z hz htz
      refine ⟨?_, hgapδ t htmem.1 z hz htz⟩
      by_contra hzu; push Not at hzu
      have : z ≤ t := Finset.le_max' _ z (Finset.mem_filter.2 ⟨hz, hzu⟩)
      linarith
    refine ⟨ψ t, Finset.mem_image_of_mem _ htmem.1, (hψ t).1, ?_⟩
    intro S' hS'
    rw [PCand98.obj7_eq I i hvnp hv, PCand98.obj7_eq I i hvnp hv,
      ← Finset.sum_fiberwise S' prod, ← Finset.sum_fiberwise (ψ t) prod]
    apply Finset.sum_le_sum
    intro k _
    have hsw := PCand98.swap_le I prod i hvnp hv (t + δ) (ψ t) S' (hψ t) hS' k
    rw [PCand98.sum_line, PCand98.sum_line] at hsw
    rw [PCand98.sum_line, PCand98.sum_line]
    have hroot := PCand98.root_mem I prod i hv (ψ t) S' (hψ t).1 hS' k
    have := PCand98.line_nonneg (T := PCand98.Tset I i prod) htmem.2 hgap hδ hroot (by linarith)
    linarith
