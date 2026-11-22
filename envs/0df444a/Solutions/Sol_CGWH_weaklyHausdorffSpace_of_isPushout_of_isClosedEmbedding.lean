-- Prove2me | solution 1 for CGWH.weaklyHausdorffSpace_of_isPushout_of_isClosedEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:21:09.462959+00:00
-- url     : https://prove2.me/submissions/c7ac75cd-248f-48d7-abd9-900c135fa1f2

import Definitions.Def_CGWH_WeakHausdorff
import Theorems.Thm_CGWH_weaklyHausdorffSpace_quotient_iff
import Theorems.Thm_CGWH_weaklyHausdorffSpace_iff_isClosed_diagonal

open CategoryTheory Topology TopologicalSpace

set_option autoImplicit false

universe u

namespace Sol_CGWH_weaklyHausdorffSpace_of_isPushout_of_isClosedEmbedding

section General

/-- A continuous map with values in the range of an embedding lifts continuously. -/
theorem exists_lift {A B C : Type*} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    {e : A → B} (he : IsEmbedding e) {t : C → B} (ht : Continuous t)
    (h : ∀ c, t c ∈ Set.range e) : ∃ a : C → A, Continuous a ∧ ∀ c, e (a c) = t c := by
  choose a ha using h
  refine ⟨a, ?_, ha⟩
  rw [he.continuous_iff]
  have hc : e ∘ a = t := funext ha
  rw [hc]
  exact ht

/-- A subset of a closed set `C` is closed as soon as its trace on the subspace `C` is closed. -/
theorem isClosed_inter_of_subtype {K : Type*} [TopologicalSpace K] {C s : Set K} (hC : IsClosed C)
    (h : IsClosed ((Subtype.val : C → K) ⁻¹' s)) : IsClosed (C ∩ s) := by
  rw [← Subtype.image_preimage_coe]
  exact hC.isClosedEmbedding_subtypeVal.isClosedMap _ h

/-- Closed sets of the `k`-ification: a set is `k`-closed iff its preimage under every test map
is closed. -/
theorem isClosed_compactlyGenerated_iff {Y : Type u} [TopologicalSpace Y] (s : Set Y) :
    IsClosed[TopologicalSpace.compactlyGenerated.{u} Y] s ↔
      ∀ (K : CompHaus.{u}) (f : C(K, Y)), IsClosed (f ⁻¹' s) := by
  rw [TopologicalSpace.compactlyGenerated, isClosed_coinduced, isClosed_sigma_iff]
  exact ⟨fun h K f => h ⟨K, f⟩, fun h ⟨K, f⟩ => h K f⟩

/-- The coincidence set of two continuous maps from a compact Hausdorff space to a compactly
generated weakly Hausdorff space is closed. -/
theorem isClosed_setOf_eq {Q : Type u} [TopologicalSpace Q] [CompactlyGeneratedSpace Q]
    [CGWH.WeaklyHausdorffSpace Q] {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    {a b : K → Q} (ha : Continuous a) (hb : Continuous b) : IsClosed {k | a k = b k} := by
  have h := (CGWH.weaklyHausdorffSpace_iff_isClosed_diagonal Q).1 inferInstance
  rw [isClosed_compactlyGenerated_iff] at h
  exact h (CompHaus.of K) ⟨fun k => (a k, b k), ha.prodMk hb⟩

end General

section Pushout

variable {P X Z Y : TopCat.{u}} {q : P ⟶ X} {p : P ⟶ Z} {f : X ⟶ Y} {g : Z ⟶ Y}

/-- The underlying function of a morphism of `TopCat` is continuous. -/
theorem continuous_hom {A B : TopCat.{u}} (h : A ⟶ B) : Continuous (h : A → B) :=
  h.hom.continuous

/-- The square commutes pointwise. -/
theorem comm (sq : IsPushout q p f g) (a : P) : f (q a) = g (p a) :=
  ConcreteCategory.congr_hom sq.w a

/-- Every point of the pushout comes from `X` or from `Z`. -/
theorem jointly_surjective (sq : IsPushout q p f g) (y : Y) :
    (∃ x, f x = y) ∨ ∃ z, g z = y :=
  Limits.Types.eq_or_eq_of_isPushout (sq.map (forget TopCat)) y

/-- If `p` is injective, so is the map `f : X → Y` into the pushout. -/
theorem inl_injective (sq : IsPushout q p f g) (hp : Function.Injective p) :
    Function.Injective f :=
  Limits.Types.pushoutCocone_inr_injective_of_isColimit
    (sq.flip.map (forget TopCat)).isColimit hp

/-- If `p` is injective, a point of `Z` identified in the pushout with a point of `X` lies in the
range of `p`. -/
theorem mem_range_of_eq (sq : IsPushout q p f g) (hp : Function.Injective p) {x : X} {z : Z}
    (h : f x = g z) : z ∈ Set.range p := by
  obtain ⟨a, ha, -⟩ := (Limits.Types.pushoutCocone_inl_eq_inr_iff_of_isColimit
    (sq.flip.map (forget TopCat)).isColimit hp z x).1 h.symm
  exact ⟨a, ha⟩

/-- A point of `Z` outside the range of `p` is identified in the pushout with no other point of
`Z`: the function "equal to `z`" on `Z` and the constant function "false" on `X` glue to a function
on the pushout. -/
theorem eq_of_notMem_range (sq : IsPushout q p f g) {z z' : Z} (hz : z ∉ Set.range p)
    (h : g z = g z') : z' = z := by
  have sq' := sq.map (forget TopCat)
  let hX : (forget TopCat).obj X ⟶ ULift.{u} Prop := ↾(fun _ => ⟨False⟩)
  let hZ : (forget TopCat).obj Z ⟶ ULift.{u} Prop := ↾(fun z'' => ⟨z'' = z⟩)
  have w : (forget TopCat).map q ≫ hX = (forget TopCat).map p ≫ hZ := by
    ext a
    have : ¬ (p a = z) := fun h => hz ⟨a, h⟩
    simp [hX, hZ, this]
  have hd := ConcreteCategory.congr_hom (sq'.inr_desc hX hZ w)
  have key : ∀ x : Z, (sq'.desc hX hZ w : _ → ULift.{u} Prop) (g x) = ⟨x = z⟩ := fun x => hd x
  have e : (⟨z = z⟩ : ULift.{u} Prop) = ⟨z' = z⟩ :=
    (key z).symm.trans ((congrArg _ h).trans (key z'))
  have e' : (z = z) = (z' = z) := congrArg ULift.down e
  exact e'.mp rfl

/-- Two points of `Z` with the same image in the pushout are equal or both lie in the range of
`p`. -/
theorem eq_or_mem_range (sq : IsPushout q p f g) {z z' : Z} (h : g z = g z') :
    z = z' ∨ (z ∈ Set.range p ∧ z' ∈ Set.range p) := by
  by_cases hz : z ∈ Set.range p
  · by_cases hz' : z' ∈ Set.range p
    · exact Or.inr ⟨hz, hz'⟩
    · exact Or.inl (eq_of_notMem_range sq hz' h.symm)
  · exact Or.inl (eq_of_notMem_range sq hz h).symm

/-- A subset of the pushout is closed iff its preimages in `X` and in `Z` are closed. -/
theorem isClosed_iff (sq : IsPushout q p f g) (s : Set Y) :
    IsClosed s ↔ IsClosed (f ⁻¹' s) ∧ IsClosed (g ⁻¹' s) := by
  refine ⟨fun h => ⟨h.preimage (continuous_hom f), h.preimage (continuous_hom g)⟩, ?_⟩
  rintro ⟨h1, h2⟩
  refine (TopCat.isClosed_iff_of_isColimit sq.cocone sq.isColimit s).2 ?_
  rintro (_ | _ | _)
  · have h3 : IsClosed (q ⁻¹' (f ⁻¹' s)) := h1.preimage (continuous_hom q)
    exact h3
  · exact h1
  · exact h2

/-- The canonical map `X ⊕ Z → Y` onto the pushout is a quotient map. -/
theorem isQuotientMap_sumElim (sq : IsPushout q p f g) :
    IsQuotientMap (Sum.elim f g : X ⊕ Z → Y) := by
  rw [isQuotientMap_iff_isClosed]
  refine ⟨?_, fun s => ?_⟩
  · intro y
    rcases jointly_surjective sq y with ⟨x, rfl⟩ | ⟨z, rfl⟩
    · exact ⟨Sum.inl x, rfl⟩
    · exact ⟨Sum.inr z, rfl⟩
  · rw [isClosed_iff sq, isClosed_sum_iff]
    rfl

/-- The pushout of compactly generated spaces is compactly generated. -/
theorem compactlyGeneratedSpace_pushout [CompactlyGeneratedSpace X] [CompactlyGeneratedSpace Z]
    (sq : IsPushout q p f g) : CompactlyGeneratedSpace Y := by
  refine compactlyGeneratedSpace_of_isClosed fun s hs => ?_
  rw [isClosed_iff sq]
  constructor
  · exact CompactlyGeneratedSpace.isClosed' fun K _ _ _ k hk =>
      hs K (f ∘ k) ((continuous_hom f).comp hk)
  · exact CompactlyGeneratedSpace.isClosed' fun K _ _ _ k hk =>
      hs K (g ∘ k) ((continuous_hom g).comp hk)

/-- The map `X → Y` into the pushout along a closed embedding is a closed embedding. -/
theorem isClosedEmbedding_inl (sq : IsPushout q p f g) (hp : IsClosedEmbedding p) :
    IsClosedEmbedding f := by
  have hf := inl_injective sq hp.injective
  refine .of_continuous_injective_isClosedMap (continuous_hom f) hf fun C hC => ?_
  rw [isClosed_iff sq]
  constructor
  · rw [Set.preimage_image_eq _ hf]
    exact hC
  · have e : g ⁻¹' (f '' C) = p '' (q ⁻¹' C) := by
      ext z
      constructor
      · rintro ⟨x, hx, hxz⟩
        obtain ⟨a, rfl⟩ := mem_range_of_eq sq hp.injective hxz
        have hxa : x = q a := hf (hxz.trans (comm sq a).symm)
        refine ⟨a, ?_, rfl⟩
        rw [Set.mem_preimage, ← hxa]
        exact hx
      · rintro ⟨a, ha, rfl⟩
        exact ⟨q a, ha, comm sq a⟩
    rw [e]
    exact hp.isClosedMap _ (hC.preimage (continuous_hom q))

/-- The pushout square along a closed embedding is cartesian. -/
theorem isPullback_pushout (sq : IsPushout q p f g) (hp : IsClosedEmbedding p) : IsPullback q p f g := by
  have hf := inl_injective sq hp.injective
  have ex : ∀ s : Limits.PullbackCone f g,
      ∃ l : s.pt → P, Continuous l ∧ ∀ w, p (l w) = s.snd w := fun s =>
    exists_lift hp.isEmbedding (continuous_hom s.snd)
      (fun w => mem_range_of_eq sq hp.injective (ConcreteCategory.congr_hom s.condition w))
  choose l hl hle using ex
  refine IsPullback.of_isLimit' ⟨sq.w⟩ (Limits.PullbackCone.IsLimit.mk _
    (fun s => TopCat.ofHom ⟨l s, hl s⟩) ?_ ?_ ?_)
  · intro s
    ext w
    apply hf
    have h1 : f (q (l s w)) = g (s.snd w) := by rw [comm sq, hle s w]
    exact h1.trans (ConcreteCategory.congr_hom s.condition w).symm
  · intro s
    ext w
    exact hle s w
  · intro s m _ h2
    ext w
    apply hp.injective
    exact (ConcreteCategory.congr_hom h2 w).trans (hle s w).symm

section WeaklyHausdorff

/-- Coincidence set in the pushout of two test maps into `X`. -/
theorem coinc_ff [CompactlyGeneratedSpace X] [CGWH.WeaklyHausdorffSpace X]
    (sq : IsPushout q p f g) (hp : IsClosedEmbedding p)
    {L : Type u} [TopologicalSpace L] [CompactSpace L] [T2Space L] {a b : L → X}
    (ha : Continuous a) (hb : Continuous b) : IsClosed {l | f (a l) = f (b l)} := by
  have e : {l | f (a l) = f (b l)} = {l | a l = b l} := by
    ext l
    exact (inl_injective sq hp.injective).eq_iff
  rw [e]
  exact isClosed_setOf_eq ha hb

/-- Coincidence set in the pushout of a test map into `X` and a test map into `Z`. -/
theorem coinc_fg [CompactlyGeneratedSpace X] [CGWH.WeaklyHausdorffSpace X]
    (sq : IsPushout q p f g) (hp : IsClosedEmbedding p)
    {L : Type u} [TopologicalSpace L] [CompactSpace L] [T2Space L] {a : L → X} {b : L → Z}
    (ha : Continuous a) (hb : Continuous b) : IsClosed {l | f (a l) = g (b l)} := by
  have hf := inl_injective sq hp.injective
  have hC : IsClosed (b ⁻¹' Set.range p) := hp.isClosed_range.preimage hb
  have hsub : {l | f (a l) = g (b l)} = (b ⁻¹' Set.range p) ∩ {l | f (a l) = g (b l)} := by
    ext l
    constructor
    · intro h
      exact ⟨mem_range_of_eq sq hp.injective h, h⟩
    · exact fun h => h.2
  rw [hsub]
  refine isClosed_inter_of_subtype hC ?_
  have : CompactSpace ↥(b ⁻¹' Set.range p) := isCompact_iff_compactSpace.mp hC.isCompact
  obtain ⟨b', hb', hb'e⟩ := exists_lift hp.isEmbedding
    (t := fun c : ↥(b ⁻¹' Set.range p) => b c) (hb.comp continuous_subtype_val) (fun c => c.2)
  have e : (Subtype.val : ↥(b ⁻¹' Set.range p) → L) ⁻¹' {l | f (a l) = g (b l)} =
      {c : ↥(b ⁻¹' Set.range p) | a c = q (b' c)} := by
    ext c
    change f (a c) = g (b c) ↔ a c = q (b' c)
    rw [← hb'e c, ← comm sq, hf.eq_iff]
  rw [e]
  exact isClosed_setOf_eq (ha.comp continuous_subtype_val) ((continuous_hom q).comp hb')

/-- Coincidence set in the pushout of two test maps into `Z`. -/
theorem coinc_gg [CompactlyGeneratedSpace X] [CGWH.WeaklyHausdorffSpace X]
    [CompactlyGeneratedSpace Z] [CGWH.WeaklyHausdorffSpace Z]
    (sq : IsPushout q p f g) (hp : IsClosedEmbedding p)
    {L : Type u} [TopologicalSpace L] [CompactSpace L] [T2Space L] {a b : L → Z}
    (ha : Continuous a) (hb : Continuous b) : IsClosed {l | g (a l) = g (b l)} := by
  have hf := inl_injective sq hp.injective
  have hC : IsClosed (a ⁻¹' Set.range p ∩ b ⁻¹' Set.range p) :=
    (hp.isClosed_range.preimage ha).inter (hp.isClosed_range.preimage hb)
  have hsub : {l | g (a l) = g (b l)} =
      {l | a l = b l} ∪ ((a ⁻¹' Set.range p ∩ b ⁻¹' Set.range p) ∩ {l | g (a l) = g (b l)}) := by
    ext l
    constructor
    · intro h
      rcases eq_or_mem_range sq h with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨h', h⟩
    · rintro (h | h)
      · exact congrArg g h
      · exact h.2
  rw [hsub]
  refine (isClosed_setOf_eq ha hb).union (isClosed_inter_of_subtype hC ?_)
  have : CompactSpace ↥(a ⁻¹' Set.range p ∩ b ⁻¹' Set.range p) :=
    isCompact_iff_compactSpace.mp hC.isCompact
  obtain ⟨a', ha', ha'e⟩ := exists_lift hp.isEmbedding
    (t := fun c : ↥(a ⁻¹' Set.range p ∩ b ⁻¹' Set.range p) => a c)
    (ha.comp continuous_subtype_val) (fun c => c.2.1)
  obtain ⟨b', hb', hb'e⟩ := exists_lift hp.isEmbedding
    (t := fun c : ↥(a ⁻¹' Set.range p ∩ b ⁻¹' Set.range p) => b c)
    (hb.comp continuous_subtype_val) (fun c => c.2.2)
  have e : (Subtype.val : ↥(a ⁻¹' Set.range p ∩ b ⁻¹' Set.range p) → L) ⁻¹'
      {l | g (a l) = g (b l)} =
      {c : ↥(a ⁻¹' Set.range p ∩ b ⁻¹' Set.range p) | q (a' c) = q (b' c)} := by
    ext c
    change g (a c) = g (b c) ↔ q (a' c) = q (b' c)
    rw [← ha'e c, ← hb'e c, ← comm sq, ← comm sq, hf.eq_iff]
  rw [e]
  exact isClosed_setOf_eq ((continuous_hom q).comp ha') ((continuous_hom q).comp hb')

/-- The equivalence relation of the quotient map `X ⊕ Z → Y` is `k`-closed: the coincidence set
of two test maps into `X ⊕ Z` composed with the quotient map is closed. -/
theorem coinc_sum [CompactlyGeneratedSpace X] [CGWH.WeaklyHausdorffSpace X]
    [CompactlyGeneratedSpace Z] [CGWH.WeaklyHausdorffSpace Z]
    (sq : IsPushout q p f g) (hp : IsClosedEmbedding p)
    {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K] {t₁ t₂ : K → X ⊕ Z}
    (h₁ : Continuous t₁) (h₂ : Continuous t₂) :
    IsClosed {k | Sum.elim f g (t₁ k) = Sum.elim f g (t₂ k)} := by
  -- the part of the coincidence set where `t₁`, `t₂` take values in given closed summands
  have key : ∀ {A B : Type u} [TopologicalSpace A] [TopologicalSpace B]
      (eA : A → X ⊕ Z) (eB : B → X ⊕ Z), IsClosedEmbedding eA → IsClosedEmbedding eB →
      (∀ (L : Type u) [TopologicalSpace L] [CompactSpace L] [T2Space L] (a : L → A) (b : L → B),
        Continuous a → Continuous b →
          IsClosed {l | Sum.elim f g (eA (a l)) = Sum.elim f g (eB (b l))}) →
      IsClosed ((t₁ ⁻¹' Set.range eA ∩ t₂ ⁻¹' Set.range eB) ∩
        {k | Sum.elim f g (t₁ k) = Sum.elim f g (t₂ k)}) := by
    intro A B _ _ eA eB hA hB H
    have hC : IsClosed (t₁ ⁻¹' Set.range eA ∩ t₂ ⁻¹' Set.range eB) :=
      (hA.isClosed_range.preimage h₁).inter (hB.isClosed_range.preimage h₂)
    refine isClosed_inter_of_subtype hC ?_
    have : CompactSpace ↥(t₁ ⁻¹' Set.range eA ∩ t₂ ⁻¹' Set.range eB) :=
      isCompact_iff_compactSpace.mp hC.isCompact
    obtain ⟨a, ha, hae⟩ := exists_lift hA.isEmbedding
      (t := fun c : ↥(t₁ ⁻¹' Set.range eA ∩ t₂ ⁻¹' Set.range eB) => t₁ c)
      (h₁.comp continuous_subtype_val) (fun c => c.2.1)
    obtain ⟨b, hb, hbe⟩ := exists_lift hB.isEmbedding
      (t := fun c : ↥(t₁ ⁻¹' Set.range eA ∩ t₂ ⁻¹' Set.range eB) => t₂ c)
      (h₂.comp continuous_subtype_val) (fun c => c.2.2)
    have e : (Subtype.val : ↥(t₁ ⁻¹' Set.range eA ∩ t₂ ⁻¹' Set.range eB) → K) ⁻¹'
        {k | Sum.elim f g (t₁ k) = Sum.elim f g (t₂ k)} =
        {c : ↥(t₁ ⁻¹' Set.range eA ∩ t₂ ⁻¹' Set.range eB) |
          Sum.elim f g (eA (a c)) = Sum.elim f g (eB (b c))} := by
      ext c
      change Sum.elim f g (t₁ c) = Sum.elim f g (t₂ c) ↔ _
      rw [← hae c, ← hbe c]
      rfl
    rw [e]
    exact H _ a b ha hb
  have hll := key (Sum.inl : X → X ⊕ Z) (Sum.inl : X → X ⊕ Z) .inl .inl
    (fun L _ _ _ a b ha hb => coinc_ff sq hp ha hb)
  have hlr := key (Sum.inl : X → X ⊕ Z) (Sum.inr : Z → X ⊕ Z) .inl .inr
    (fun L _ _ _ a b ha hb => coinc_fg sq hp ha hb)
  have hrl := key (Sum.inr : Z → X ⊕ Z) (Sum.inl : X → X ⊕ Z) .inr .inl
    (fun L _ _ _ a b ha hb => by
      have e : {l | Sum.elim f g (Sum.inr (a l)) = Sum.elim f g (Sum.inl (b l))} =
          {l | f (b l) = g (a l)} := by
        ext l
        exact eq_comm
      rw [e]
      exact coinc_fg sq hp hb ha)
  have hrr := key (Sum.inr : Z → X ⊕ Z) (Sum.inr : Z → X ⊕ Z) .inr .inr
    (fun L _ _ _ a b ha hb => coinc_gg sq hp ha hb)
  have cover : {k | Sum.elim f g (t₁ k) = Sum.elim f g (t₂ k)} =
      ((t₁ ⁻¹' Set.range (Sum.inl : X → X ⊕ Z) ∩ t₂ ⁻¹' Set.range (Sum.inl : X → X ⊕ Z)) ∩
        {k | Sum.elim f g (t₁ k) = Sum.elim f g (t₂ k)}) ∪
      ((t₁ ⁻¹' Set.range (Sum.inl : X → X ⊕ Z) ∩ t₂ ⁻¹' Set.range (Sum.inr : Z → X ⊕ Z)) ∩
        {k | Sum.elim f g (t₁ k) = Sum.elim f g (t₂ k)}) ∪
      ((t₁ ⁻¹' Set.range (Sum.inr : Z → X ⊕ Z) ∩ t₂ ⁻¹' Set.range (Sum.inl : X → X ⊕ Z)) ∩
        {k | Sum.elim f g (t₁ k) = Sum.elim f g (t₂ k)}) ∪
      ((t₁ ⁻¹' Set.range (Sum.inr : Z → X ⊕ Z) ∩ t₂ ⁻¹' Set.range (Sum.inr : Z → X ⊕ Z)) ∩
        {k | Sum.elim f g (t₁ k) = Sum.elim f g (t₂ k)}) := by
    ext k
    have c₁ : t₁ k ∈ Set.range (Sum.inl : X → X ⊕ Z) ∨ t₁ k ∈ Set.range (Sum.inr : Z → X ⊕ Z) := by
      rcases t₁ k with x | z
      · exact Or.inl ⟨x, rfl⟩
      · exact Or.inr ⟨z, rfl⟩
    have c₂ : t₂ k ∈ Set.range (Sum.inl : X → X ⊕ Z) ∨ t₂ k ∈ Set.range (Sum.inr : Z → X ⊕ Z) := by
      rcases t₂ k with x | z
      · exact Or.inl ⟨x, rfl⟩
      · exact Or.inr ⟨z, rfl⟩
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_preimage]
    tauto
  rw [cover]
  exact ((hll.union hlr).union hrl).union hrr

/-- The pushout of compactly generated weakly Hausdorff spaces along a closed embedding is weakly
Hausdorff. -/
theorem weaklyHausdorffSpace_pushout [CompactlyGeneratedSpace X] [CGWH.WeaklyHausdorffSpace X]
    [CompactlyGeneratedSpace Z] [CGWH.WeaklyHausdorffSpace Z]
    (sq : IsPushout q p f g) (hp : IsClosedEmbedding p) :
    CGWH.WeaklyHausdorffSpace Y := by
  have hF₀ := isQuotientMap_sumElim sq
  let F : C(X ⊕ Z, Y) := ⟨Sum.elim f g, hF₀.continuous⟩
  have hF : IsQuotientMap F := hF₀
  have hQ : CGWH.WeaklyHausdorffSpace (Quotient (Setoid.ker F)) := by
    rw [CGWH.weaklyHausdorffSpace_quotient_iff, isClosed_compactlyGenerated_iff]
    intro K t
    exact coinc_sum sq hp (continuous_fst.comp t.continuous) (continuous_snd.comp t.continuous)
  let e : Y ≃ₜ Quotient (Setoid.ker F) := hF.homeomorph.symm
  refine ⟨fun K _ _ _ h hh => ?_⟩
  have hcl : IsClosed (Set.range (e ∘ h)) :=
    hQ.isClosed_range K (e ∘ h) (e.continuous.comp hh)
  have he : Set.range h = e ⁻¹' Set.range (e ∘ h) := by
    rw [Set.range_comp, Set.preimage_image_eq _ e.injective]
  rw [he]
  exact hcl.preimage e.continuous

end WeaklyHausdorff

end Pushout

end Sol_CGWH_weaklyHausdorffSpace_of_isPushout_of_isClosedEmbedding

open CGWH Sol_CGWH_weaklyHausdorffSpace_of_isPushout_of_isClosedEmbedding

theorem solution
    {P X Z Y : TopCat.{u}} {q : P ⟶ X} {p : P ⟶ Z} {f : X ⟶ Y} {g : Z ⟶ Y}
    [CompactlyGeneratedSpace X] [WeaklyHausdorffSpace X]
    [CompactlyGeneratedSpace Z] [WeaklyHausdorffSpace Z]
    (sq : IsPushout q p f g) (hp : IsClosedEmbedding p) :
    CompactlyGeneratedSpace Y ∧ WeaklyHausdorffSpace Y ∧ IsClosedEmbedding f ∧
      IsPullback q p f g :=
  ⟨compactlyGeneratedSpace_pushout sq, weaklyHausdorffSpace_pushout sq hp,
    isClosedEmbedding_inl sq hp, isPullback_pushout sq hp⟩
