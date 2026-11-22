-- Prove2me | solution 1 for GelfandVNA.Duality.lemma_5_11
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-21T22:09:45.707234+00:00
-- url     : https://prove2.me/submissions/0b2730e3-31c4-486f-a9e9-c11deb575ad7

import Mathlib
import Definitions.Def_GelfandVNA_Duality_EMS
import Theorems.Thm_GelfandVNA_Duality_proposition_4_65

/-!
Lemma 5.11 of Pavlov, *Gelfand-type duality for commutative von Neumann algebras*
(arXiv:2005.05284v3, p. 42): for a morphism `f` of compact strictly localizable enhanced measurable
spaces the induced map `f* : M'/N' → M/N` is a map of frames.
-/

namespace GelfandVNA.Duality.L511

open CategoryTheory QAlgorithms.Papers.Independent.Support21.P20 GelfandVNA.Duality

universe u

/-! ### Partial preimages -/

section PartialPreimage

variable {X Y : Type u} (f : X → Option Y)

lemma pp_mono {s t : Set Y} (h : s ⊆ t) : partialPreimage f s ⊆ partialPreimage f t := by
  rintro x ⟨y, hy, hxy⟩
  exact ⟨y, h hy, hxy⟩

lemma pp_diff (s t : Set Y) :
    partialPreimage f (s \ t) = partialPreimage f s \ partialPreimage f t := by
  ext x
  constructor
  · rintro ⟨y, ⟨hys, hyt⟩, hxy⟩
    refine ⟨⟨y, hys, hxy⟩, ?_⟩
    rintro ⟨y', hy', hxy'⟩
    rw [hxy] at hxy'
    cases hxy'
    exact hyt hy'
  · rintro ⟨⟨y, hys, hxy⟩, hn⟩
    exact ⟨y, ⟨hys, fun hyt => hn ⟨y, hyt, hxy⟩⟩, hxy⟩

lemma pp_disjoint {s t : Set Y} (h : Disjoint s t) :
    Disjoint (partialPreimage f s) (partialPreimage f t) := by
  rw [Set.disjoint_left] at h ⊢
  rintro x ⟨y, hys, hxy⟩ ⟨y', hyt, hxy'⟩
  rw [hxy] at hxy'
  cases hxy'
  exact h hys hyt

lemma pp_sUnion (D : Set (Set Y)) :
    partialPreimage f (⋃₀ D) = ⋃₀ ((fun d => partialPreimage f d) '' D) := by
  ext x
  constructor
  · rintro ⟨y, ⟨d, hd, hyd⟩, hxy⟩
    exact ⟨partialPreimage f d, ⟨d, hd, rfl⟩, ⟨y, hyd, hxy⟩⟩
  · rintro ⟨_, ⟨d, hd, rfl⟩, ⟨y, hyd, hxy⟩⟩
    exact ⟨y, ⟨d, hd, hyd⟩, hxy⟩

end PartialPreimage

/-! ### σ-algebra and σ-ideal bookkeeping -/

section Enhanced

variable {X : Type u} (E : Enhanced X)

lemma meas_compl {a : Set X} (ha : a ∈ E.measurable) : aᶜ ∈ E.measurable :=
  E.sigmaAlgebra.2.1 a ha

lemma meas_iUnion {a : ℕ → Set X} (ha : ∀ i, a i ∈ E.measurable) :
    (⋃ i, a i) ∈ E.measurable :=
  E.sigmaAlgebra.2.2 a ha

lemma meas_union {a b : Set X} (ha : a ∈ E.measurable) (hb : b ∈ E.measurable) :
    a ∪ b ∈ E.measurable := by
  have h := meas_iUnion E (a := fun i : ℕ => if i = 0 then a else b)
    (fun i => by
      show (if i = 0 then a else b) ∈ _
      split_ifs <;> assumption)
  rwa [iUnion_two] at h

lemma meas_inter {a b : Set X} (ha : a ∈ E.measurable) (hb : b ∈ E.measurable) :
    a ∩ b ∈ E.measurable := by
  have h := meas_compl E (meas_union E (meas_compl E ha) (meas_compl E hb))
  rwa [Set.compl_union, compl_compl, compl_compl] at h

lemma meas_diff {a b : Set X} (ha : a ∈ E.measurable) (hb : b ∈ E.measurable) :
    a \ b ∈ E.measurable := by
  rw [Set.sdiff_eq]
  exact meas_inter E ha (meas_compl E hb)

lemma meas_sUnion {D : Set (Set X)} (hD : D.Countable) (h : ∀ d ∈ D, d ∈ E.measurable) :
    ⋃₀ D ∈ E.measurable := by
  rcases D.eq_empty_or_nonempty with rfl | hne
  · rw [Set.sUnion_empty]
    exact E.sigmaAlgebra.1
  · obtain ⟨e, rfl⟩ := hD.exists_eq_range hne
    rw [Set.sUnion_range]
    exact meas_iUnion E (fun i => h _ ⟨i, rfl⟩)

lemma negl_empty : (∅ : Set X) ∈ E.negligible := E.sigmaIdeal.1

lemma negl_sUnion {D : Set (Set X)} (hD : D.Countable) (h : ∀ d ∈ D, d ∈ E.negligible) :
    ⋃₀ D ∈ E.negligible := by
  rcases D.eq_empty_or_nonempty with rfl | hne
  · rw [Set.sUnion_empty]
    exact E.sigmaIdeal.1
  · obtain ⟨e, rfl⟩ := hD.exists_eq_range hne
    rw [Set.sUnion_range]
    exact E.sigmaIdeal.2.2 e (fun i => h _ ⟨i, rfl⟩)

end Enhanced

/-! ### The quotient `M/N` -/

lemma MmodN.exists_rep {X : Type u} {E : Enhanced X} (q : MmodN E) :
    ∃ (m : Set X) (hm : m ∈ E.measurable), MmodN.mk m hm = q :=
  Quotient.inductionOn (motive := fun q : Quotient (nullSetoid E) =>
    ∃ (m : Set X) (hm : m ∈ E.measurable), MmodN.mk m hm = q) q (fun a => ⟨a.1, a.2, rfl⟩)

lemma mk_le_mk {X : Type u} {E : Enhanced X} {a b : Set X} (ha : a ∈ E.measurable)
    (hb : b ∈ E.measurable) : MmodN.mk a ha ≤ MmodN.mk b hb ↔ a \ b ∈ E.negligible :=
  Iff.rfl

lemma pullPremap_mk {X Y : Type u} {E : Enhanced X} {F : Enhanced Y} (f : Premap E F)
    (m : Set Y) (hm : m ∈ F.measurable) :
    pullPremap f (MmodN.mk m hm) = MmodN.mk (partialPreimage f.1 m) (f.2.2.1 _ hm) :=
  rfl

lemma pullHom_exists_rep {A B : EMS.{u}} (F : A ⟶ B) :
    ∃ g : Premap A.E B.E, pullHom F = pullPremap g :=
  Quot.inductionOn (motive := fun F : Quot (weakHomRelation A.E B.E) =>
    ∃ g : Premap A.E B.E, pullHom F = pullPremap g) F (fun g => ⟨g, rfl⟩)

/-! ### The countable chain condition for σ-finite spaces -/

/-- A pairwise disjoint family of non-negligible measurable sets of a σ-finite enhanced measurable
space is countable. -/
lemma countable_of_disjoint {Y : Type u} (F : Enhanced Y) (μ : Set Y → ℂ)
    (hμ : IsEMeasure F F.measurable μ) (hf : IsFaithfulEMeasure F F.measurable μ)
    (D : Set (Set Y)) (hD : ∀ d ∈ D, d ∈ F.measurable ∧ d ∉ F.negligible)
    (hdisj : ∀ d ∈ D, ∀ d' ∈ D, d ≠ d' → Disjoint d d') : D.Countable := by
  have hβ : ∀ d ∈ D, ∃ b, b ∈ F.measurable ∧ b ⊆ d ∧ μ b ≠ 0 := by
    intro d hd
    by_contra hcon
    push Not at hcon
    exact (hD d hd).2 (hf d (hD d hd).1 (fun m' hm' hsub => hcon m' hm' hsub))
  choose! β hβm hβs hβμ using hβ
  have hfin : ∀ n : ℕ, {d | d ∈ D ∧ 1 / ((n : ℝ) + 1) < ‖μ (β d)‖}.Finite := by
    intro n
    by_contra hinf
    have hinf' : {d | d ∈ D ∧ 1 / ((n : ℝ) + 1) < ‖μ (β d)‖}.Infinite := hinf
    let e := Set.Infinite.natEmbedding _ hinf'
    have hmem : ∀ k, (e k).1 ∈ D := fun k => (e k).2.1
    have hbig : ∀ k, 1 / ((n : ℝ) + 1) < ‖μ (β (e k).1)‖ := fun k => (e k).2.2
    have hpw : Pairwise (Function.onFun Disjoint (fun k => β (e k).1)) := by
      intro k l hkl
      have hne : (e k).1 ≠ (e l).1 := fun h => hkl (e.injective (Subtype.ext h))
      exact (hdisj _ (hmem k) _ (hmem l) hne).mono (hβs _ (hmem k)) (hβs _ (hmem l))
    have hsum := (hμ.2.2.2.2.2.1 (fun k => β (e k).1) (fun k => hβm _ (hmem k)) hpw
      (meas_iUnion F (fun k => hβm _ (hmem k)))).1
    have ht := hsum.tendsto_atTop_zero
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨k, hk⟩ := (ht.eventually (gt_mem_nhds hpos)).exists
    exact absurd hk (not_lt.2 (le_of_lt (hbig k)))
  refine Set.Countable.mono ?_ (Set.countable_iUnion (fun n => (hfin n).countable))
  intro d hd
  have hpos : 0 < ‖μ (β d)‖ := norm_pos_iff.2 (hβμ d hd)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
  exact Set.mem_iUnion.2 ⟨n, hd, hn⟩

/-! ### The key step on a compact σ-finite source -/

/-- Let `h : (Y, F) → (Z, G)` be a premap from a compact σ-finite space to a strictly localizable
one, and let `[a₀]` be the supremum of `s ⊆ M'/N'`. If `C` bounds every `h* s₀`, `[s₀] ∈ s`, modulo
negligible sets, then it bounds `h* a₀`. -/
lemma component_key {Y Z : Type u} (F : Enhanced Y) (G : Enhanced Z)
    (hc : IsCompactEnhancedOn F Set.univ) (μ : Set Y → ℂ)
    (hμ : IsEMeasure F F.measurable μ) (hf : IsFaithfulEMeasure F F.measurable μ)
    (hsl : IsStrictlyLocalizable G) (h : Premap F G)
    (s : Set (MmodN G)) (a0 : Set Z) (ha0 : a0 ∈ G.measurable)
    (hlub : IsLUB s (MmodN.mk a0 ha0)) (C : Set Y)
    (hub : ∀ (s0 : Set Z) (hs0 : s0 ∈ G.measurable), MmodN.mk s0 hs0 ∈ s →
      partialPreimage h.1 s0 \ C ∈ F.negligible) :
    partialPreimage h.1 a0 \ C ∈ F.negligible := by
  -- the measurable image of `h`
  obtain ⟨⟨m, hm, hmc, hmin⟩, -⟩ := proposition_4_65 F G hc
    ⟨F.measurable, μ, hμ, hf, fun m hm hn => ⟨m, hm, hn, subset_rfl⟩⟩ hsl h
  -- a maximal disjoint family of non-negligible pieces of the image lying under members of `s`
  let 𝔉 : Set (Set (Set Z)) := {D | (∀ d ∈ D, d ∈ G.measurable ∧ d ⊆ m ∧ d ∉ G.negligible ∧
    ∃ (s0 : Set Z) (hs0 : s0 ∈ G.measurable), MmodN.mk s0 hs0 ∈ s ∧ d ⊆ s0) ∧
    ∀ d ∈ D, ∀ d' ∈ D, d ≠ d' → Disjoint d d'}
  obtain ⟨Dm, hDm⟩ : ∃ Dm, Maximal (· ∈ 𝔉) Dm := by
    apply zorn_subset
    intro c hc𝔉 hchain
    refine ⟨⋃₀ c, ⟨?_, ?_⟩, fun D hD => Set.subset_sUnion_of_mem hD⟩
    · rintro d ⟨D, hD, hd⟩
      exact (hc𝔉 hD).1 d hd
    · rintro d ⟨D, hD, hd⟩ d' ⟨D', hD', hd'⟩ hne
      rcases hchain.total hD hD' with hsub | hsub
      · exact (hc𝔉 hD').2 d (hsub hd) d' hd' hne
      · exact (hc𝔉 hD).2 d hd d' (hsub hd') hne
  have hD1 := hDm.1.1
  have hD2 := hDm.1.2
  -- the family is countable, by the countable chain condition on the source
  have hnn : ∀ d ∈ Dm, partialPreimage h.1 d ∉ F.negligible := fun d hd hneg =>
    (hD1 d hd).2.2.1 (hmin d (hD1 d hd).1 (hD1 d hd).2.1 hneg)
  have hinj : Set.InjOn (fun d => partialPreimage h.1 d) Dm := by
    intro d hd d' hd' heq
    by_contra hne
    have hdis := pp_disjoint h.1 (hD2 d hd d' hd' hne)
    have heq' : partialPreimage h.1 d = partialPreimage h.1 d' := heq
    rw [← heq', disjoint_self, Set.bot_eq_empty] at hdis
    exact hnn d hd (hdis ▸ negl_empty F)
  have hcount : Dm.Countable := by
    apply Set.countable_of_injective_of_countable_image hinj
    apply countable_of_disjoint F μ hμ hf
    · rintro _ ⟨d, hd, rfl⟩
      exact ⟨h.2.2.1 _ (hD1 d hd).1, hnn d hd⟩
    · rintro _ ⟨d, hd, rfl⟩ _ ⟨d', hd', rfl⟩ hne
      exact pp_disjoint h.1 (hD2 d hd d' hd' (fun heq => hne (by rw [heq])))
  have hUm : ⋃₀ Dm ∈ G.measurable := meas_sUnion G hcount (fun d hd => (hD1 d hd).1)
  -- the preimage of the union is bounded by `C`
  have hU : partialPreimage h.1 (⋃₀ Dm) \ C ∈ F.negligible := by
    have hneg : ⋃₀ ((fun d => partialPreimage h.1 d \ C) '' Dm) ∈ F.negligible := by
      apply negl_sUnion F (hcount.image _)
      rintro _ ⟨d, hd, rfl⟩
      obtain ⟨s0, hs0, hs0s, hds0⟩ := (hD1 d hd).2.2.2
      exact negligible_mono F (Set.sdiff_subset_sdiff_left (pp_mono h.1 hds0)) (hub s0 hs0 hs0s)
    refine negligible_mono F ?_ hneg
    rintro x ⟨⟨y, ⟨d, hd, hyd⟩, hxy⟩, hxC⟩
    exact ⟨partialPreimage h.1 d \ C, ⟨d, hd, rfl⟩, ⟨y, hyd, hxy⟩, hxC⟩
  -- the rest of `a₀` inside the image is negligible
  have hrm : (a0 ∩ m) \ ⋃₀ Dm ∈ G.measurable := meas_diff G (meas_inter G ha0 hm) hUm
  have hr : (a0 ∩ m) \ ⋃₀ Dm ∈ G.negligible := by
    by_contra hrn
    have hpiece : ∀ (s0 : Set Z) (hs0 : s0 ∈ G.measurable), MmodN.mk s0 hs0 ∈ s →
        s0 ∩ ((a0 ∩ m) \ ⋃₀ Dm) ∈ G.negligible := by
      intro s0 hs0 hs0s
      by_contra hdn
      have hdU : ∀ d' ∈ Dm, Disjoint (s0 ∩ ((a0 ∩ m) \ ⋃₀ Dm)) d' := by
        intro d' hd'
        rw [Set.disjoint_left]
        rintro z ⟨-, -, hzU⟩ hzd'
        exact hzU ⟨d', hd', hzd'⟩
      have hins : insert (s0 ∩ ((a0 ∩ m) \ ⋃₀ Dm)) Dm ∈ 𝔉 := by
        refine ⟨?_, ?_⟩
        · rintro d (rfl | hd)
          · exact ⟨meas_inter G hs0 hrm, fun z hz => hz.2.1.2, hdn, s0, hs0, hs0s,
              Set.inter_subset_left⟩
          · exact hD1 d hd
        · rintro d (rfl | hd) d' (rfl | hd') hne
          · exact absurd rfl hne
          · exact hdU d' hd'
          · exact (hdU d hd).symm
          · exact hD2 d hd d' hd' hne
      have hmem : s0 ∩ ((a0 ∩ m) \ ⋃₀ Dm) ∈ Dm :=
        hDm.2 hins (Set.subset_insert _ _) (Set.mem_insert _ _)
      have hself := hdU _ hmem
      rw [disjoint_self, Set.bot_eq_empty] at hself
      exact hdn (hself ▸ negl_empty G)
    have hbound : MmodN.mk (a0 \ ((a0 ∩ m) \ ⋃₀ Dm)) (meas_diff G ha0 hrm) ∈ upperBounds s := by
      intro q hq
      obtain ⟨s0, hs0, rfl⟩ := MmodN.exists_rep q
      rw [mk_le_mk]
      have h1 : s0 \ a0 ∈ G.negligible := (mk_le_mk hs0 ha0).1 (hlub.1 hq)
      refine negligible_mono G ?_ (negligible_union G h1 (hpiece s0 hs0 hq))
      intro z hz
      by_cases hza : z ∈ a0
      · refine Or.inr ⟨hz.1, ?_⟩
        by_contra hzr
        exact hz.2 ⟨hza, hzr⟩
      · exact Or.inl ⟨hz.1, hza⟩
    have hle := (mk_le_mk ha0 (meas_diff G ha0 hrm)).1 (hlub.2 hbound)
    refine hrn (negligible_mono G ?_ hle)
    intro z hz
    exact ⟨hz.1.1, fun hz' => hz'.2 hz⟩
  -- assemble
  refine negligible_mono F ?_ (negligible_union F (negligible_union F hmc (h.2.2.2 _ hr)) hU)
  rintro x ⟨⟨y, hya, hxy⟩, hxC⟩
  by_cases hym : y ∈ m
  · by_cases hyU : y ∈ ⋃₀ Dm
    · exact Or.inr ⟨⟨y, hyU, hxy⟩, hxC⟩
    · exact Or.inl (Or.inr ⟨y, ⟨⟨hya, hym⟩, hyU⟩, hxy⟩)
  · exact Or.inl (Or.inl ⟨y, hym, hxy⟩)

/-! ### Strictly localizable spaces: the components -/

section Components

variable {X : Type u} {E : Enhanced X} {I : Type u} {Y : I → Type u} {F : ∀ i, Enhanced (Y i)}

/-- The inclusion of a component into the coproduct, as a premap. -/
def incl (F : ∀ i, Enhanced (Y i)) (i : I) : Premap (F i) (coprodEnhanced F) :=
  ⟨fun y => some ⟨i, y⟩, by
    have hpp : ∀ s : Set (Σ i, Y i),
        partialPreimage (fun y : Y i => some (⟨i, y⟩ : Σ i, Y i)) s = Sigma.mk i ⁻¹' s := by
      intro s
      ext y
      simp [partialPreimage]
    refine ⟨?_, fun s hs => ?_, fun s hs => ?_⟩
    · have : (partialDomain (fun y : Y i => some (⟨i, y⟩ : Σ i, Y i)))ᶜ = ∅ := by
        ext y
        simp [partialDomain]
      rw [this]
      exact (F i).sigmaIdeal.1
    · rw [hpp]
      exact hs i
    · rw [hpp]
      exact hs i⟩

lemma sigma_preimage_image (i i' : I) (t : Set (Y i)) :
    (i' = i → ∃ t' : Set (Y i'), HEq t' t ∧
      Sigma.mk i' ⁻¹' ((Sigma.mk i '' t : Set (Σ i, Y i))) = t') ∧
    (i' ≠ i → Sigma.mk i' ⁻¹' ((Sigma.mk i '' t : Set (Σ i, Y i))) = ∅) := by
  constructor
  · rintro rfl
    exact ⟨t, HEq.rfl, Set.preimage_image_eq _ sigma_mk_injective⟩
  · intro hne
    ext y
    simp only [Set.mem_preimage, Set.mem_image, Set.mem_empty_iff_false, iff_false, not_exists,
      not_and]
    intro z _ heq
    exact hne (congrArg Sigma.fst heq).symm

lemma coprod_meas_image (i : I) {t : Set (Y i)} (ht : t ∈ (F i).measurable) :
    (Sigma.mk i '' t : Set (Σ i, Y i)) ∈ (coprodEnhanced F).measurable := by
  intro i'
  by_cases hi : i' = i
  · subst hi
    rw [Set.preimage_image_eq _ sigma_mk_injective]
    exact ht
  · rw [(sigma_preimage_image i i' t).2 hi]
    exact (F i').sigmaAlgebra.1

lemma coprod_negl_image (i : I) {t : Set (Y i)} (ht : t ∈ (F i).negligible) :
    (Sigma.mk i '' t : Set (Σ i, Y i)) ∈ (coprodEnhanced F).negligible := by
  intro i'
  by_cases hi : i' = i
  · subst hi
    rw [Set.preimage_image_eq _ sigma_mk_injective]
    exact ht
  · rw [(sigma_preimage_image i i' t).2 hi]
    exact (F i').sigmaIdeal.1

/-- Each component of a compact strictly localizable space is compact. -/
lemma component_compact (hc : IsCompactEnhancedOn E Set.univ)
    (φ : Premap E (coprodEnhanced F)) (ψ : Premap (coprodEnhanced F) E)
    (h1 : partialCompose ψ.1 φ.1 = (fun x => some x))
    (h2 : partialCompose φ.1 ψ.1 = (fun y => some y)) (i : I) :
    IsCompactEnhancedOn (F i) Set.univ := by
  -- the point bijection
  have hex : ∀ p : Σ i, Y i, ∃ x, ψ.1 p = some x ∧ φ.1 x = some p := by
    intro p
    have h := congrFun h2 p
    simp only [partialCompose] at h
    rcases hψ : ψ.1 p with _ | x
    · rw [hψ] at h
      cases h
    · rw [hψ] at h
      exact ⟨x, rfl, h⟩
  choose jj hj1 hj2 using hex
  have hjinj : Function.Injective jj := by
    intro p q hpq
    have := hj2 p
    rw [hpq, hj2 q] at this
    exact (Option.some.inj this).symm
  have hφ : ∀ x p, φ.1 x = some p → x = jj p := by
    intro x p hxp
    have h := congrFun h1 x
    simp only [partialCompose] at h
    rw [hxp] at h
    have h' : ψ.1 p = some x := h
    rw [hj1 p] at h'
    exact (Option.some.inj h').symm
  -- preimages along the component inclusion
  have hppψ : ∀ s : Set X, Sigma.mk i ⁻¹' (partialPreimage ψ.1 s) = (fun y => jj ⟨i, y⟩) ⁻¹' s := by
    intro s
    ext y
    constructor
    · rintro ⟨x, hx, hψx⟩
      rw [hj1] at hψx
      cases hψx
      exact hx
    · intro hy
      exact ⟨jj ⟨i, y⟩, hy, hj1 _⟩
  have hppφ : ∀ t : Set (Y i),
      partialPreimage φ.1 (Sigma.mk i '' t) = (fun y => jj ⟨i, y⟩) '' t := by
    intro t
    ext x
    constructor
    · rintro ⟨p, ⟨y, hy, rfl⟩, hxp⟩
      exact ⟨y, hy, (hφ x _ hxp).symm⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨i, y⟩, ⟨y, hy, rfl⟩, hj2 _⟩
  have hji : Function.Injective (fun y : Y i => jj ⟨i, y⟩) := by
    intro y y' hyy'
    have := hjinj hyy'
    cases this
    rfl
  obtain ⟨K, hK, hKc, hKi⟩ := hc
  refine ⟨{t | ∃ k ∈ K, k ⊆ Set.range (fun y : Y i => jj ⟨i, y⟩) ∧
    t = (fun y : Y i => jj ⟨i, y⟩) ⁻¹' k}, ?_, ?_, ?_⟩
  · rintro t ⟨k, hk, -, rfl⟩
    refine ⟨Set.subset_univ _, ?_⟩
    rw [← hppψ]
    exact ψ.2.2.1 k (hK k hk).2 i
  · intro T hT hfip
    rcases T.eq_empty_or_nonempty with rfl | ⟨t0, ht0⟩
    · exact hfip ∅ Set.finite_empty (Set.empty_subset _)
    · have hx : (Set.univ ∩ ⋂₀ {k | k ∈ K ∧ k ⊆ Set.range (fun y : Y i => jj ⟨i, y⟩) ∧
          (fun y : Y i => jj ⟨i, y⟩) ⁻¹' k ∈ T}).Nonempty := by
        apply hKc _ (fun k hk => hk.1)
        intro U' hU'fin hU'
        obtain ⟨y, -, hy⟩ := hfip ((fun k => (fun y : Y i => jj ⟨i, y⟩) ⁻¹' k) '' U')
          (hU'fin.image _) (by
            rintro _ ⟨k, hk, rfl⟩
            exact (hU' hk).2.2)
        refine ⟨jj ⟨i, y⟩, Set.mem_univ _, ?_⟩
        intro k hk
        exact hy _ ⟨k, hk, rfl⟩
      obtain ⟨x, -, hx⟩ := hx
      obtain ⟨k0, hk0, hk0r, rfl⟩ := hT ht0
      obtain ⟨y, rfl⟩ := hk0r (hx k0 ⟨hk0, hk0r, ht0⟩)
      refine ⟨y, Set.mem_univ _, ?_⟩
      intro t ht
      obtain ⟨k, hk, hkr, rfl⟩ := hT ht
      exact hx k ⟨hk, hkr, ht⟩
  · intro s _ hsm hsn
    have hSm : (fun y : Y i => jj ⟨i, y⟩) '' s ∈ E.measurable := by
      rw [← hppφ]
      exact φ.2.2.1 _ (coprod_meas_image i hsm)
    have hSn : (fun y : Y i => jj ⟨i, y⟩) '' s ∉ E.negligible := by
      intro hneg
      have := ψ.2.2.2 _ hneg i
      rw [hppψ, Set.preimage_image_eq _ hji] at this
      exact hsn this
    obtain ⟨k, hk, hks, hkn⟩ := hKi _ (Set.subset_univ _) hSm hSn
    have hkr : k ⊆ Set.range (fun y : Y i => jj ⟨i, y⟩) := fun x hx => by
      obtain ⟨y, -, rfl⟩ := hks hx
      exact ⟨y, rfl⟩
    refine ⟨_, ⟨k, hk, hkr, rfl⟩, ?_, ?_⟩
    · intro y hy
      obtain ⟨y', hy', hyy'⟩ := hks hy
      rw [← hji hyy']
      exact hy'
    · intro hneg
      have := φ.2.2.2 _ (coprod_negl_image i hneg)
      rw [hppφ, Set.image_preimage_eq_of_subset hkr] at this
      exact hkn this

end Components

/-! ### Suprema -/

/-- The essential step of Lemma 5.11: `f*` sends a supremum to a least upper bound. -/
lemma sup_key {X Z : Type u} (E : Enhanced X) (G : Enhanced Z)
    (hc : IsCompactEnhancedOn E Set.univ) (hslE : IsStrictlyLocalizable E)
    (hslG : IsStrictlyLocalizable G) (g : Premap E G)
    (s : Set (MmodN G)) (a0 : Set Z) (ha0 : a0 ∈ G.measurable)
    (hlub : IsLUB s (MmodN.mk a0 ha0)) (C : Set X)
    (hub : ∀ (s0 : Set Z) (hs0 : s0 ∈ G.measurable), MmodN.mk s0 hs0 ∈ s →
      partialPreimage g.1 s0 \ C ∈ E.negligible) :
    partialPreimage g.1 a0 \ C ∈ E.negligible := by
  obtain ⟨I, Y, F, hσ, φ, ψ, h1, h2⟩ := hslE
  -- it suffices to check negligibility on every component
  have hback : partialPreimage φ.1 (partialPreimage ψ.1 (partialPreimage g.1 a0 \ C)) =
      partialPreimage g.1 a0 \ C := by
    rw [← partialPreimage_comp, h1, partialPreimage_id]
  rw [← hback]
  apply φ.2.2.2
  intro i
  obtain ⟨μ, hμ, hf⟩ := hσ i
  have hci := component_compact hc φ ψ h1 h2 i
  -- the premap from the component
  have hpp : ∀ t : Set Z, partialPreimage (compPremap (compPremap (incl F i) ψ) g).1 t =
      Sigma.mk i ⁻¹' (partialPreimage ψ.1 (partialPreimage g.1 t)) := by
    intro t
    show partialPreimage (partialCompose g.1 (partialCompose ψ.1 (incl F i).1)) t = _
    rw [partialPreimage_comp, partialPreimage_comp]
    ext y
    simp [partialPreimage, incl]
  have hkey := component_key (F i) G hci μ hμ hf hslG (compPremap (compPremap (incl F i) ψ) g)
    s a0 ha0 hlub (Sigma.mk i ⁻¹' (partialPreimage ψ.1 C)) (by
      intro s0 hs0 hs0s
      rw [hpp]
      have := ψ.2.2.2 _ (hub s0 hs0 hs0s) i
      rwa [pp_diff, Set.preimage_sdiff] at this)
  rw [hpp] at hkey
  rwa [pp_diff, Set.preimage_sdiff]

end GelfandVNA.Duality.L511

open CategoryTheory QAlgorithms.Papers.Independent.Support21.P20 GelfandVNA.Duality
  GelfandVNA.Duality.L511 in
/-- Lemma 5.11 with Definition 5.10, p. 42. -/
theorem solution.{u} {A B : CSLEMS.{u}} (f : A ⟶ B) :
    (∀ a b c : MmodN B.obj.E, IsGLB {a, b} c →
      IsGLB {pullHom f.hom a, pullHom f.hom b} (pullHom f.hom c)) ∧
    (∀ a : MmodN B.obj.E, IsGreatest Set.univ a → IsGreatest Set.univ (pullHom f.hom a)) ∧
    ∀ (s : Set (MmodN B.obj.E)) (a : MmodN B.obj.E), IsLUB s a →
      IsLUB (pullHom f.hom '' s) (pullHom f.hom a) := by
  obtain ⟨g, hg⟩ := pullHom_exists_rep f.hom
  rw [hg]
  have hmono : ∀ a b : MmodN B.obj.E, a ≤ b → pullPremap g a ≤ pullPremap g b := by
    intro a b hab
    obtain ⟨a0, ha0, rfl⟩ := MmodN.exists_rep a
    obtain ⟨b0, hb0, rfl⟩ := MmodN.exists_rep b
    rw [pullPremap_mk, pullPremap_mk, mk_le_mk, ← pp_diff]
    exact g.2.2.2 _ ((mk_le_mk ha0 hb0).1 hab)
  refine ⟨?_, ?_, ?_⟩
  · -- binary meets
    intro a b c hglb
    obtain ⟨a0, ha0, rfl⟩ := MmodN.exists_rep a
    obtain ⟨b0, hb0, rfl⟩ := MmodN.exists_rep b
    obtain ⟨c0, hc0, rfl⟩ := MmodN.exists_rep c
    have hca : MmodN.mk c0 hc0 ≤ MmodN.mk a0 ha0 := hglb.1 (by simp)
    have hcb : MmodN.mk c0 hc0 ≤ MmodN.mk b0 hb0 := hglb.1 (by simp)
    have hab : MmodN.mk (a0 ∩ b0) (meas_inter _ ha0 hb0) ≤ MmodN.mk c0 hc0 := by
      apply hglb.2
      rintro x (rfl | rfl)
      · rw [mk_le_mk]
        have : (a0 ∩ b0) \ a0 = ∅ := by
          ext z
          simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
          tauto
        rw [this]
        exact negl_empty _
      · rw [mk_le_mk]
        have : (a0 ∩ b0) \ b0 = ∅ := by
          ext z
          simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
          tauto
        rw [this]
        exact negl_empty _
    refine ⟨?_, ?_⟩
    · rintro x (rfl | rfl)
      · exact hmono _ _ hca
      · exact hmono _ _ hcb
    · intro d hd
      obtain ⟨d0, hd0, rfl⟩ := MmodN.exists_rep d
      have hda : MmodN.mk d0 hd0 ≤ pullPremap g (MmodN.mk a0 ha0) := hd (by simp)
      have hdb : MmodN.mk d0 hd0 ≤ pullPremap g (MmodN.mk b0 hb0) := hd (by simp)
      rw [pullPremap_mk, mk_le_mk] at hda hdb ⊢
      have hab' := g.2.2.2 _ ((mk_le_mk _ hc0).1 hab)
      refine negligible_mono _ ?_ (negligible_union _ (negligible_union _ hda hdb) hab')
      intro x hx
      by_cases hxa : x ∈ partialPreimage g.1 a0
      · by_cases hxb : x ∈ partialPreimage g.1 b0
        · obtain ⟨y, hya, hxy⟩ := hxa
          obtain ⟨y', hyb, hxy'⟩ := hxb
          rw [hxy] at hxy'
          cases hxy'
          exact Or.inr ⟨y, ⟨⟨hya, hyb⟩, fun hyc => hx.2 ⟨y, hyc, hxy⟩⟩, hxy⟩
        · exact Or.inl (Or.inr ⟨hx.1, hxb⟩)
      · exact Or.inl (Or.inl ⟨hx.1, hxa⟩)
  · -- the top element
    intro a ha
    obtain ⟨a0, ha0, rfl⟩ := MmodN.exists_rep a
    refine ⟨Set.mem_univ _, ?_⟩
    intro d _
    obtain ⟨d0, hd0, rfl⟩ := MmodN.exists_rep d
    have htop : MmodN.mk Set.univ (by
        have := meas_compl B.obj.E B.obj.E.sigmaAlgebra.1
        rwa [Set.compl_empty] at this) ≤ MmodN.mk a0 ha0 := ha.2 (Set.mem_univ _)
    rw [mk_le_mk] at htop
    rw [pullPremap_mk, mk_le_mk]
    refine negligible_mono _ ?_ (negligible_union _ g.2.1 (g.2.2.2 _ htop))
    intro x hx
    by_cases hdom : x ∈ partialDomain g.1
    · obtain ⟨y, hxy⟩ := hdom
      exact Or.inr ⟨y, ⟨Set.mem_univ _, fun hya => hx.2 ⟨y, hya, hxy⟩⟩, hxy⟩
    · exact Or.inl hdom
  · -- arbitrary suprema
    intro s a hlub
    obtain ⟨a0, ha0, rfl⟩ := MmodN.exists_rep a
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact hmono _ _ (hlub.1 hx)
    · intro c hc
      obtain ⟨C, hC, rfl⟩ := MmodN.exists_rep c
      rw [pullPremap_mk, mk_le_mk]
      apply sup_key A.obj.E B.obj.E A.property.1 A.property.2 B.property.2 g s a0 ha0 hlub C
      intro s0 hs0 hs0s
      have := hc ⟨_, hs0s, rfl⟩
      rwa [pullPremap_mk, mk_le_mk] at this
