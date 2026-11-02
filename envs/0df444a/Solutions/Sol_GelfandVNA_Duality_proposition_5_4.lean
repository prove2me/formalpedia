-- Prove2me | solution 1 for GelfandVNA.Duality.proposition_5_4
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T02:50:59.991085+00:00
-- url     : https://prove2.me/submissions/7a053876-43ba-4dc4-9840-601cdce3d83b

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P20
import Definitions.Def_GelfandVNA_Duality_Locales
import Definitions.Def_GelfandVNA_Duality_Spaces
import Definitions.Def_GelfandVNA_Duality_EMS

/-! Direct proof of Pavlov Proposition 5.4. The accepted localizability
criterion by fizzyinc3 (e4ac8c1d-3289-4144-baeb-8ddb71a3176f) is
inlined with attribution; all remaining proof modules are included below. -/
noncomputable section

section Gelfand54_part_0
/- Source module: Work.Gelfand273.LocalizableCriterion -/
/- Reused accepted proof by fizzyinc3, submission e4ac8c1d-3289-4144-baeb-8ddb71a3176f. Only a wrapper namespace and theorem name change. -/

namespace Gelfand273Criterion

open QAlgorithms.Papers.Independent.Support21.P20

open Set Filter

open scoped NNReal

universe u v

theorem g67c_restrict {A : Type u} [CompleteBooleanAlgebra A] (nu : A → ℝ≥0)
    (hnu : IsPositiveContinuousValuation nu) (a : A) :
    IsPositiveContinuousValuation (fun x : Set.Iic a => nu x.val) := by
  obtain ⟨⟨hbot, hmod⟩, hmono, hcont⟩ := hnu
  refine ⟨⟨hbot, fun x y => hmod x.val y.val⟩, fun x y hxy => hmono hxy, ?_⟩
  intro s b hsne hdir hlub
  have hl : IsLUB (Subtype.val '' s) b.val := by
    constructor
    · rintro _ ⟨x, hx, rfl⟩; exact hlub.1 hx
    · intro u hu
      have : b ≤ ⟨u ⊓ a, inf_le_right⟩ := hlub.2 (fun x hx =>
        show x.val ≤ u ⊓ a from le_inf (hu ⟨x, hx, rfl⟩) x.2)
      exact (show b.val ≤ u ⊓ a from this).trans inf_le_left
  have hd : DirectedOn (· ≤ ·) (Subtype.val '' s) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hxz, hyz⟩ := hdir x hx y hy
    exact ⟨z.val, ⟨z, hz, rfl⟩, hxz, hyz⟩
  have h := hcont _ _ (hsne.image _) hd hl
  rw [Set.image_image] at h
  exact h

theorem g67c_extend {A : Type u} [CompleteBooleanAlgebra A] (a : A) (mu : Set.Iic a → ℝ≥0)
    (hmu : IsPositiveContinuousValuation mu) :
    IsPositiveContinuousValuation (fun x : A => mu ⟨x ⊓ a, inf_le_right⟩) := by
  obtain ⟨⟨hbot, hmod⟩, hmono, hcont⟩ := hmu
  refine ⟨⟨?_, fun x y => ?_⟩, fun x y hxy => hmono (show x ⊓ a ≤ y ⊓ a from inf_le_inf_right a hxy), ?_⟩
  · have : (⟨(⊥ : A) ⊓ a, inf_le_right⟩ : Set.Iic a) = ⊥ := Subtype.ext (by simp)
    simp only; rw [this, hbot]
  · have h1 : (⟨(x ⊔ y) ⊓ a, inf_le_right⟩ : Set.Iic a) =
        (⟨x ⊓ a, inf_le_right⟩ : Set.Iic a) ⊔ ⟨y ⊓ a, inf_le_right⟩ :=
      Subtype.ext (by
        show (x ⊔ y) ⊓ a = (x ⊓ a) ⊔ (y ⊓ a)
        rw [inf_sup_right])
    have h2 : (⟨(x ⊓ y) ⊓ a, inf_le_right⟩ : Set.Iic a) =
        (⟨x ⊓ a, inf_le_right⟩ : Set.Iic a) ⊓ ⟨y ⊓ a, inf_le_right⟩ :=
      Subtype.ext (by
        show (x ⊓ y) ⊓ a = (x ⊓ a) ⊓ (y ⊓ a)
        rw [inf_inf_distrib_right])
    simp only; rw [h1, h2]; exact hmod _ _
  · intro s b hsne hdir hlub
    let g : A → Set.Iic a := fun x => ⟨x ⊓ a, inf_le_right⟩
    have hb : b = sSup s := hlub.unique (isLUB_sSup s)
    have hl : IsLUB (g '' s) (g b) := by
      constructor
      · rintro _ ⟨x, hx, rfl⟩
        exact show x ⊓ a ≤ b ⊓ a from inf_le_inf_right a (hlub.1 hx)
      · intro u hu
        show b ⊓ a ≤ u.val
        rw [hb, sSup_inf_eq]
        exact iSup₂_le fun x hx => (show g x ≤ u from hu ⟨x, hx, rfl⟩)
    have hd : DirectedOn (· ≤ ·) (g '' s) := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      obtain ⟨z, hz, hxz, hyz⟩ := hdir x hx y hy
      exact ⟨g z, ⟨z, hz, rfl⟩, show x ⊓ a ≤ z ⊓ a from inf_le_inf_right a hxz,
        show y ⊓ a ≤ z ⊓ a from inf_le_inf_right a hyz⟩
    have h := hcont _ _ (hsne.image _) hd hl
    rw [Set.image_image] at h
    exact h

theorem localizableCriterion (A : Type u) [CompleteBooleanAlgebra A] :
    HasFiniteValuationCover A ↔ ∀ b : A, b ≠ ⊥ →
      ∃ nu : A → ℝ≥0, IsPositiveContinuousValuation nu ∧ nu b ≠ 0 := by
  constructor
  · intro hcov b hb
    have : ∃ g ∈ {a : A | ∃ nu : Set.Iic a → ℝ≥0,
        IsPositiveContinuousValuation nu ∧ ∀ b, nu b = 0 → b = ⊥}, b ⊓ g ≠ ⊥ := by
      by_contra hall
      push Not at hall
      apply hb
      have : b = b ⊓ ⊤ := (inf_top_eq b).symm
      rw [this, ← hcov, inf_sSup_eq]
      exact le_antisymm (iSup₂_le fun d hd => (hall d hd).le) bot_le
    obtain ⟨g, ⟨mu, hmu, hfaith⟩, hbg⟩ := this
    refine ⟨_, g67c_extend g mu hmu, fun h0 => hbg ?_⟩
    have := hfaith _ h0
    exact congrArg Subtype.val this
  · intro h
    unfold HasFiniteValuationCover
    set G := {a : A | ∃ nu : Set.Iic a → ℝ≥0,
        IsPositiveContinuousValuation nu ∧ ∀ b, nu b = 0 → b = ⊥}
    set g := sSup G
    by_contra hne
    have hgc : gᶜ ≠ ⊥ := fun h' => hne (compl_eq_bot.1 h')
    obtain ⟨nu, hnu, hnz⟩ := h gᶜ hgc
    have hnu' := hnu
    obtain ⟨⟨hbot, hmod⟩, hmono, hcont⟩ := hnu'
    let Z : Set A := {x | nu x = 0}
    set n := sSup Z
    have hsupz : ∀ x y, x ∈ Z → y ∈ Z → x ⊔ y ∈ Z := by
      intro x y hx hy
      have := hmod x y
      simp only [Z, Set.mem_setOf_eq] at hx hy ⊢
      rw [hx, hy, zero_add] at this
      exact (add_eq_zero.1 this.symm).1
    have hn : nu n = 0 := by
      have hc := hcont Z n ⟨⊥, hbot⟩
        (fun x hx y hy => ⟨x ⊔ y, hsupz x y hx hy, le_sup_left, le_sup_right⟩) (isLUB_sSup Z)
      exact le_antisymm (hc.2 (by rintro _ ⟨x, hx, rfl⟩; exact le_of_eq hx)) bot_le
    set c := gᶜ ⊓ nᶜ
    have hcG : c ∈ G := by
      refine ⟨fun x => nu x.val, g67c_restrict nu hnu c, fun x hx => ?_⟩
      apply Subtype.ext
      have hxn : x.val ≤ n := le_sSup hx
      have hxc : x.val ≤ nᶜ := x.2.trans inf_le_right
      show x.val = ⊥
      exact le_antisymm (le_inf hxn hxc |>.trans (inf_compl_self n).le) bot_le
    have hcle : c ≤ g := le_sSup hcG
    have hc0 : c = ⊥ := le_antisymm ((le_inf hcle inf_le_left).trans (inf_compl_self g).le) bot_le
    apply hnz
    have h1 : gᶜ ≤ c ⊔ n := by
      rw [sup_comm, sup_inf_left, sup_compl_eq_top, inf_top_eq]; exact le_sup_right
    have h2 := hmono h1
    rw [hc0, bot_sup_eq, hn] at h2
    exact le_antisymm h2 bot_le

end Gelfand273Criterion
end Gelfand54_part_0

section Gelfand54_part_1
/- Source module: Work.Gelfand54.CarrierPartition -/
set_option autoImplicit false
open Set QAlgorithms.Papers.Independent.Support21.P20
open scoped NNReal

namespace Gelfand54Partition
universe u
variable {B : Type u} [CompleteBooleanAlgebra B]

/-- Faithfulness survives restriction to a smaller principal algebra. -/
theorem faithful_below {a b : B} (hab : a ≤ b) (ν : Iic b → ℝ≥0)
    (hν : IsPositiveContinuousValuation ν) (hf : ∀ x, ν x = 0 → x = ⊥) :
    ∃ μ : Iic a → ℝ≥0, IsPositiveContinuousValuation μ ∧
      ∀ x, μ x = 0 → x = ⊥ := by
  let η : B → ℝ≥0 := fun x => ν ⟨x ⊓ b, inf_le_right⟩
  have hη : IsPositiveContinuousValuation η := Gelfand273Criterion.g67c_extend b ν hν
  refine ⟨fun x => η x.val, Gelfand273Criterion.g67c_restrict η hη a, ?_⟩
  intro x hx
  have hxb : x.val ≤ b := x.property.trans hab
  have heq : (⟨x.val ⊓ b, inf_le_right⟩ : Iic b) = ⟨x.val, hxb⟩ :=
    Subtype.ext (inf_eq_left.mpr hxb)
  have hz : ν ⟨x.val, hxb⟩ = 0 := by
    change ν ⟨x.val ⊓ b, inf_le_right⟩ = 0 at hx
    rwa [heq] at hx
  apply Subtype.ext
  change x.val = (⊥ : B)
  exact congrArg (fun y : Iic b => y.val) (hf _ hz)

/-- Every nonzero part of a localizable algebra contains a nonzero faithful
finite principal part. -/
theorem exists_faithful_below (hB : HasFiniteValuationCover B) {b : B} (hb : b ≠ ⊥) :
    ∃ a : B, a ≤ b ∧ a ≠ ⊥ ∧ ∃ ν : Iic a → ℝ≥0,
      IsPositiveContinuousValuation ν ∧ ∀ x, ν x = 0 → x = ⊥ := by
  have hex : ∃ g ∈ {a : B | ∃ ν : Iic a → ℝ≥0,
      IsPositiveContinuousValuation ν ∧ ∀ x, ν x = 0 → x = ⊥}, b ⊓ g ≠ ⊥ := by
    by_contra hall
    push_neg at hall
    apply hb
    have heq : b = b ⊓ ⊤ := (inf_top_eq b).symm
    rw [heq, ← hB, inf_sSup_eq]
    exact le_antisymm (iSup₂_le fun g hg => (hall g hg).le) bot_le
  obtain ⟨g, ⟨ν, hν, hf⟩, hbg⟩ := hex
  exact ⟨b ⊓ g, inf_le_left, hbg, faithful_below inf_le_right ν hν hf⟩

/-- Zorn's lemma produces the disjoint faithful principal pieces used in
Pavlov's Proposition 5.4. The supremum is taken in the original algebra. -/
theorem exists_disjoint_faithful_cover (hB : HasFiniteValuationCover B) :
    ∃ S : Set B, S.PairwiseDisjoint id ∧
      (∀ a ∈ S, a ≠ ⊥ ∧ ∃ ν : Iic a → ℝ≥0,
        IsPositiveContinuousValuation ν ∧ ∀ x, ν x = 0 → x = ⊥) ∧
      sSup S = ⊤ := by
  classical
  let P : Set (Set B) := {S | S.PairwiseDisjoint id ∧
    ∀ a ∈ S, a ≠ ⊥ ∧ ∃ ν : Iic a → ℝ≥0,
      IsPositiveContinuousValuation ν ∧ ∀ x, ν x = 0 → x = ⊥}
  obtain ⟨S, hS⟩ := zorn_subset P (by
    intro C hCP hchain
    refine ⟨⋃₀ C, ?_, fun s hs => subset_sUnion_of_mem hs⟩
    constructor
    · rintro a ⟨s, hs, ha⟩ b ⟨t, ht, hb⟩ hab
      rcases hchain.total hs ht with hst | hts
      · exact (hCP ht).1 (hst ha) hb hab
      · exact (hCP hs).1 ha (hts hb) hab
    · rintro a ⟨s, hs, ha⟩
      exact (hCP hs).2 a ha)
  refine ⟨S, hS.1.1, hS.1.2, ?_⟩
  by_contra hne
  have hc : (sSup S)ᶜ ≠ (⊥ : B) := fun h => hne (compl_eq_bot.mp h)
  obtain ⟨a, ha, hna, hν⟩ := exists_faithful_below hB hc
  have hdisj (b : B) (hb : b ∈ S) : Disjoint a b :=
    (disjoint_compl_left : Disjoint (sSup S)ᶜ (sSup S)).mono ha (le_sSup hb)
  have hins : insert a S ∈ P := by
    constructor
    · exact hS.1.1.insert (fun b hb _ => hdisj b hb)
    · intro b hb
      rcases hb with rfl | hb
      · exact ⟨hna, hν⟩
      · exact hS.1.2 b hb
  have haS : a ∈ S := hS.2 hins (subset_insert a S) (mem_insert a S)
  exact hna (by simpa only [inf_idem] using (hdisj a haS).eq_bot)

end Gelfand54Partition
end Gelfand54_part_1

section Gelfand54_part_2
/- Source module: Work.Gelfand54.ClopenAlgebra -/
set_option autoImplicit false
open Set TopologicalSpace

namespace Gelfand54Clopens
universe u
variable {X : Type u} [TopologicalSpace X]

theorem coe_doublecompl (a : Opens X) :
    ((aᶜᶜ : Opens X) : Set X) = interior (closure (a : Set X)) := by
  have hc : ((aᶜ : Opens X) : Set X) = (closure (a : Set X))ᶜ := by
    rw [Opens.coe_compl_eq_interior_compl, interior_compl]
  rw [Opens.coe_compl_eq_interior_compl, hc, compl_compl]

theorem clopen_regular (C : Clopens X) : Heyting.IsRegular C.toOpens := by
  change C.toOpensᶜᶜ = C.toOpens
  apply Opens.ext
  rw [coe_doublecompl]
  change interior (closure (C : Set X)) = (C : Set X)
  rw [C.isClosed.closure_eq, C.isOpen.interior_eq]

theorem regular_closed [ExtremallyDisconnected X] (a : Heyting.Regular (Opens X)) :
    IsClosed ((a : Opens X) : Set X) := by
  have h : interior (closure ((a : Opens X) : Set X)) = ((a : Opens X) : Set X) :=
    (coe_doublecompl (a : Opens X)).symm.trans
      (congrArg (fun U : Opens X => (U : Set X)) a.property)
  have ho : IsOpen (closure ((a : Opens X) : Set X)) :=
    ExtremallyDisconnected.open_closure _ (a : Opens X).isOpen
  have hc : closure ((a : Opens X) : Set X) = ((a : Opens X) : Set X) :=
    ho.interior_eq.symm.trans h
  rw [← hc]
  exact isClosed_closure

/-- The original clopen Boolean order is the regular-open Boolean order. -/
def clopenRegularIso [ExtremallyDisconnected X] :
    Clopens X ≃o Heyting.Regular (Opens X) where
  toFun C := ⟨C.toOpens, clopen_regular C⟩
  invFun a := ⟨((a : Opens X) : Set X), ⟨regular_closed a, (a : Opens X).isOpen⟩⟩
  left_inv C := Clopens.ext rfl
  right_inv a := Subtype.ext (Opens.ext rfl)
  map_rel_iff' := fun {a b} => Iff.rfl

/-- A clopen subset of a clopen subspace is exactly a clopen of the ambient
space below that subspace, with its original inclusion order. -/
def subtypeClopenIso (C : Clopens X) : Clopens C ≃o Iic C where
  toFun D := ⟨⟨Subtype.val '' (D : Set C),
    ⟨C.isClosed.isClosedMap_subtype_val _ D.isClosed,
      C.isOpen.isOpenMap_subtype_val _ D.isOpen⟩⟩, by
        rintro x ⟨y, _, rfl⟩
        exact y.property⟩
  invFun D := ⟨Subtype.val ⁻¹' (D.val : Set X), D.val.isClopen.preimage continuous_subtype_val⟩
  left_inv D := by
    apply Clopens.ext
    ext x
    change (∃ y : C, y ∈ D ∧ y.val = x.val) ↔ x ∈ D
    constructor
    · rintro ⟨y, hy, hxy⟩
      have heq : y = x := Subtype.ext hxy
      simpa only [heq] using hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  right_inv D := by
    apply Subtype.ext
    apply Clopens.ext
    ext x
    change (∃ y : C, y.val ∈ D.val ∧ y.val = x) ↔ x ∈ D.val
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, D.property hx⟩, hx, rfl⟩
  map_rel_iff' := by
    intro A B
    change (Subtype.val '' (A : Set C) ⊆ Subtype.val '' (B : Set C)) ↔
      ((A : Set C) ⊆ (B : Set C))
    constructor
    · intro h x hx
      obtain ⟨y, hy, hyx⟩ := h ⟨x, hx, rfl⟩
      have heq : y = x := Subtype.ext hyx
      simpa only [heq] using hy
    · rintro h _ ⟨x, hx, rfl⟩
      exact ⟨x, h hx, rfl⟩


theorem subtype_extremallyDisconnected [ExtremallyDisconnected X] (C : Clopens X) :
    ExtremallyDisconnected C := by
  constructor
  intro U hU
  rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image]
  exact (ExtremallyDisconnected.open_closure _
    (C.isOpen.isOpenMap_subtype_val _ hU)).preimage continuous_subtype_val

def subtypeRegularIso [ExtremallyDisconnected X] (C : Clopens X) :
    Clopens C ≃o Iic (clopenRegularIso C) :=
  (subtypeClopenIso C).trans (clopenRegularIso.Iic C)

def regularCarrierIso [ExtremallyDisconnected X] (a : Heyting.Regular (Opens X)) :
    Clopens ((clopenRegularIso (X := X)).symm a) ≃o Iic a := by
  let e := clopenRegularIso (X := X)
  exact (subtypeRegularIso (e.symm a)).trans
    (OrderIso.setCongr _ _ (congrArg Iic (e.apply_symm_apply a)))

end Gelfand54Clopens
end Gelfand54_part_2

section Gelfand54_part_3
/- Source module: Work.Gelfand273.ValuationBridge -/
/- Helpers reproduced from our accepted lemma2.58 solution, unchanged. -/

set_option autoImplicit false

open Set Filter QAlgorithms.Papers.Independent.Support21.P20

namespace Gelfand258Work

variable {L : Type*} [Order.Frame L]

theorem compact_regular (hL : IsStoneanLocale L) {a : L} (ha : IsCompactElement a) :
    Heyting.IsRegular a := by
  let s : Set L := {b | bᶜ ⊔ a = ⊤}
  have hs : s.Nonempty := ⟨⊥, by simp [s]⟩
  have hd : DirectedOn (· ≤ ·) s := by
    intro b hb c hc
    refine ⟨b ⊔ c, ?_, le_sup_left, le_sup_right⟩
    change (b ⊔ c)ᶜ ⊔ a = ⊤
    change bᶜ ⊔ a = ⊤ at hb
    change cᶜ ⊔ a = ⊤ at hc
    simp only [compl_sup, sup_inf_right, hb, hc, inf_top_eq]
  have heq : a = sSup s := hL.1.2 a
  have hlub : IsLUB s a := heq.symm ▸ isLUB_sSup s
  obtain ⟨b, hb, hab⟩ := ha s a hs hd hlub le_rfl
  have hcomp : aᶜ ⊔ a = ⊤ := by
    apply top_le_iff.mp
    change bᶜ ⊔ a = ⊤ at hb
    rw [← hb]
    exact sup_le_sup_right (compl_anti hab) a
  exact (IsCompl.of_eq compl_inf_eq_bot hcomp).compl_eq

theorem regular_compact (hL : IsStoneanLocale L) {a : L} (ha : Heyting.IsRegular a) :
    IsCompactElement a := by
  have hac : a ⊔ aᶜ = ⊤ := by
    simpa only [ha.eq, sup_comm] using hL.2 a
  intro s u hs hd hlu hau
  let f : L → L := fun x => x ⊔ aᶜ
  have hf : Monotone f := fun _ _ h => sup_le_sup_right h _
  have hdi : DirectedOn (· ≤ ·) (f '' s) := by
    rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩
    obtain ⟨d, hd, hbd, hcd⟩ := hd b hb c hc
    exact ⟨f d, ⟨d, hd, rfl⟩, hf hbd, hf hcd⟩
  have hli : IsLUB (f '' s) (u ⊔ aᶜ) := by
    constructor
    · rintro _ ⟨x, hx, rfl⟩
      exact sup_le_sup_right (hlu.1 hx) _
    · intro b hb
      apply sup_le
      · apply hlu.2
        intro x hx
        exact le_sup_left.trans (hb ⟨x, hx, rfl⟩)
      · obtain ⟨x, hx⟩ := hs
        exact le_sup_right.trans (hb ⟨x, hx, rfl⟩)
  have htop : (⊤ : L) ≤ u ⊔ aᶜ := by
    rw [← hac]
    exact sup_le_sup_right hau _
  obtain ⟨_, ⟨x, hx, rfl⟩, hlarge⟩ := hL.1.1.1 (f '' s) (u ⊔ aᶜ)
    (hs.image f) hdi hli htop
  refine ⟨x, hx, ?_⟩
  calc
    a = a ⊓ ⊤ := by simp
    _ ≤ a ⊓ (x ⊔ aᶜ) := inf_le_inf_left a hlarge
    _ = a ⊓ x := by rw [inf_sup_left, inf_compl_eq_bot, sup_bot_eq]
    _ ≤ x := inf_le_right

def compactRegularIso (hL : IsStoneanLocale L) :
    {a : L // IsCompactElement a} ≃o Heyting.Regular L where
  toFun a := ⟨a.1, compact_regular hL a.2⟩
  invFun a := ⟨a.1, regular_compact hL a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

theorem continuous_comp {A B R : Type*}
    [Lattice A] [OrderBot A] [Lattice B] [OrderBot B]
    [Zero R] [Add R] [TopologicalSpace R]
    (f : A → B) (hm : Monotone f) (hbot : f ⊥ = ⊥)
    (hsup : ∀ a b, f (a ⊔ b) = f a ⊔ f b)
    (hinf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (hlub : ∀ (s : Set A) (a : A), IsLUB s a → IsLUB (f '' s) (f a))
    (ν : B → R) (hν : IsContinuousValuation ν) :
    IsContinuousValuation (ν ∘ f) := by
  constructor
  · constructor
    · simpa only [Function.comp_apply, hbot] using hν.1.1
    · intro a b
      simpa only [Function.comp_apply, hsup, hinf] using hν.1.2 (f a) (f b)
  · intro s a hs hd hsa
    have hdi : DirectedOn (· ≤ ·) (f '' s) := by
      rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩
      obtain ⟨d, hd, hbd, hcd⟩ := hd b hb c hc
      exact ⟨f d, ⟨d, hd, rfl⟩, hm hbd, hm hcd⟩
    let g : s → f '' s := fun b => ⟨f b.1, ⟨b.1, b.2, rfl⟩⟩
    have hgm : Monotone g := fun _ _ h => hm h
    have hgt : Tendsto g atTop atTop := hgm.tendsto_atTop_atTop (by
      rintro ⟨b, x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, le_rfl⟩)
    exact (hν.2 (f '' s) (f a) (hs.image f) hdi (hlub s a hsa)).comp hgt

open Heyting.Regular

theorem regularize_inf (a b : L) : toRegular (a ⊓ b) = toRegular a ⊓ toRegular b := by
  apply coe_injective
  exact compl_compl_inf_distrib a b

theorem regularize_normal {R : Type*} [Zero R] [Add R] [TopologicalSpace R]
    (μ : Heyting.Regular L → R) (hμ : IsContinuousValuation μ) :
    IsNormalValuation (fun a => μ (toRegular a)) := by
  constructor
  · exact continuous_comp toRegular toRegular.monotone (by
      apply coe_injective
      simp) (fun _ _ => gi.gc.l_sup) regularize_inf
      (fun _ _ h => gi.gc.isLUB_l_image h) μ hμ
  · intro a
    apply congrArg μ
    apply coe_injective
    exact compl_compl_compl aᶜ

theorem restriction_continuous {R : Type*} [Zero R] [Add R] [TopologicalSpace R]
    (ν : L → R) (hν : IsNormalValuation ν) :
    IsContinuousValuation (fun a : Heyting.Regular L => ν a) := by
  constructor
  · constructor
    · exact hν.1.1.1
    · intro a b
      change ν (a : L) + ν (b : L) = ν ((a : L) ⊔ b)ᶜᶜ + ν ((a : L) ⊓ b)
      rw [hν.2]
      exact hν.1.1.2 (a : L) (b : L)
  · intro s a hs hd hsa
    let t : Set L := ((↑) : Heyting.Regular L → L) '' s
    have ht : t.Nonempty := hs.image _
    have hdt : DirectedOn (· ≤ ·) t := by
      rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩
      obtain ⟨d, hd, hbd, hcd⟩ := hd b hb c hc
      exact ⟨d, ⟨d, hd, rfl⟩, hbd, hcd⟩
    have himage : toRegular '' t = s := by
      simp [t, Set.image_image, Function.comp_def]
    have hlu := gi.gc.isLUB_l_image (isLUB_sSup t)
    rw [himage] at hlu
    have hqa : toRegular (sSup t) = a := hlu.unique hsa
    have hv : ν (sSup t) = ν (a : L) := by
      calc
        ν (sSup t) = ν (sSup t)ᶜᶜ := (hν.2 _).symm
        _ = ν (a : L) := congrArg ν (congrArg ((↑) : Heyting.Regular L → L) hqa)
    let g : s → t := fun b => ⟨b.1, ⟨b.1, b.2, rfl⟩⟩
    have hgm : Monotone g := fun _ _ h => h
    have hgt : Tendsto g atTop atTop := hgm.tendsto_atTop_atTop (by
      rintro ⟨_, b, hb, rfl⟩
      exact ⟨⟨b, hb⟩, le_rfl⟩)
    have hc := (hν.1.2 t (sSup t) ht hdt (isLUB_sSup t)).comp hgt
    rw [hv] at hc
    exact hc

theorem iso_continuous {A B R : Type*}
    [Lattice A] [OrderBot A] [Lattice B] [OrderBot B]
    [Zero R] [Add R] [TopologicalSpace R]
    (e : A ≃o B) (ν : B → R) (hν : IsContinuousValuation ν) :
    IsContinuousValuation (ν ∘ e) :=
  continuous_comp e e.monotone e.map_bot e.map_sup e.map_inf
    (fun _ _ h => e.isLUB_image'.2 h) ν hν

theorem continuous_extension {R B : Type*} [Zero R] [Add R] [TopologicalSpace R]
    [Lattice B] [OrderBot B] (hL : IsStoneanLocale L)
    (e : B ≃o {a : L // IsCompactElement a}) :
    (∀ ν : L → R, IsNormalValuation ν → IsContinuousValuation (fun b => ν (e b))) ∧
    (∀ μ : B → R, IsContinuousValuation μ →
      ∃! ν : L → R, IsNormalValuation ν ∧ ∀ b, ν (e b) = μ b) := by
  let er : B ≃o Heyting.Regular L := e.trans (compactRegularIso hL)
  have hcoe (b : B) : (er b : L) = e b := rfl
  have hback (a : Heyting.Regular L) : (e (er.symm a) : L) = a := by
    rw [← hcoe, er.apply_symm_apply]
  constructor
  · intro ν hν
    exact iso_continuous er _ (restriction_continuous ν hν)
  · intro μ hμ
    let ν : L → R := fun a => μ (er.symm (toRegular a))
    refine ⟨ν, ⟨regularize_normal _ (iso_continuous er.symm μ hμ), ?_⟩, ?_⟩
    · intro b
      change μ (er.symm (toRegular (e b : L))) = μ b
      rw [← hcoe, toRegular_coe, er.symm_apply_apply]
    · intro ξ hξ
      funext a
      calc
        ξ a = ξ aᶜᶜ := (hξ.1.2 a).symm
        _ = ξ (e (er.symm (toRegular a))) := congrArg ξ (hback (toRegular a)).symm
        _ = μ (er.symm (toRegular a)) := hξ.2 _
        _ = ν a := rfl

theorem positive_comp {A B : Type*}
    [Lattice A] [OrderBot A] [Lattice B] [OrderBot B]
    (f : A → B) (hm : Monotone f) (hbot : f ⊥ = ⊥)
    (hsup : ∀ a b, f (a ⊔ b) = f a ⊔ f b)
    (hinf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (hlub : ∀ (s : Set A) (a : A), IsLUB s a → IsLUB (f '' s) (f a))
    (ν : B → NNReal) (hν : IsPositiveContinuousValuation ν) :
    IsPositiveContinuousValuation (ν ∘ f) := by
  refine ⟨⟨?_, ?_⟩, hν.2.1.comp hm, ?_⟩
  · simpa only [Function.comp_apply, hbot] using hν.1.1
  · intro a b
    simpa only [Function.comp_apply, hsup, hinf] using hν.1.2 (f a) (f b)
  · intro s a hs hd hsa
    have hdi : DirectedOn (· ≤ ·) (f '' s) := by
      rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩
      obtain ⟨d, hd, hbd, hcd⟩ := hd b hb c hc
      exact ⟨f d, ⟨d, hd, rfl⟩, hm hbd, hm hcd⟩
    simpa only [Set.image_image, Function.comp_def] using
      hν.2.2 (f '' s) (f a) (hs.image f) hdi (hlub s a hsa)

theorem regularize_positive_normal (μ : Heyting.Regular L → NNReal)
    (hμ : IsPositiveContinuousValuation μ) :
    IsPositiveNormalValuation (fun a => μ (toRegular a)) := by
  constructor
  · exact positive_comp toRegular toRegular.monotone (by
      apply coe_injective
      simp) (fun _ _ => gi.gc.l_sup) regularize_inf
      (fun _ _ h => gi.gc.isLUB_l_image h) μ hμ
  · intro a
    apply congrArg μ
    apply coe_injective
    exact compl_compl_compl aᶜ

theorem restriction_positive_continuous (ν : L → NNReal)
    (hν : IsPositiveNormalValuation ν) :
    IsPositiveContinuousValuation (fun a : Heyting.Regular L => ν a) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · exact hν.1.1.1
  · intro a b
    change ν (a : L) + ν (b : L) = ν ((a : L) ⊔ b)ᶜᶜ + ν ((a : L) ⊓ b)
    rw [hν.2]
    exact hν.1.1.2 (a : L) (b : L)
  · intro a b h
    exact hν.1.2.1 h
  · intro s a hs hd hsa
    let t : Set L := ((↑) : Heyting.Regular L → L) '' s
    have ht : t.Nonempty := hs.image _
    have hdt : DirectedOn (· ≤ ·) t := by
      rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩
      obtain ⟨d, hd, hbd, hcd⟩ := hd b hb c hc
      exact ⟨d, ⟨d, hd, rfl⟩, hbd, hcd⟩
    have himage : toRegular '' t = s := by
      simp [t, Set.image_image, Function.comp_def]
    have hlu := gi.gc.isLUB_l_image (isLUB_sSup t)
    rw [himage] at hlu
    have hqa : toRegular (sSup t) = a := hlu.unique hsa
    have hv : ν (sSup t) = ν (a : L) := by
      calc
        ν (sSup t) = ν (sSup t)ᶜᶜ := (hν.2 _).symm
        _ = ν (a : L) := congrArg ν (congrArg ((↑) : Heyting.Regular L → L) hqa)
    simpa only [t, Set.image_image, Function.comp_def, hv] using
      hν.1.2.2 t (sSup t) ht hdt (isLUB_sSup t)

theorem iso_positive_continuous {A B : Type*}
    [Lattice A] [OrderBot A] [Lattice B] [OrderBot B]
    (e : A ≃o B) (ν : B → NNReal) (hν : IsPositiveContinuousValuation ν) :
    IsPositiveContinuousValuation (ν ∘ e) :=
  positive_comp e e.monotone e.map_bot e.map_sup e.map_inf
    (fun _ _ h => e.isLUB_image'.2 h) ν hν

theorem positive_extension {B : Type*} [Lattice B] [OrderBot B]
    (hL : IsStoneanLocale L) (e : B ≃o {a : L // IsCompactElement a}) :
    (∀ ν : L → NNReal, IsPositiveNormalValuation ν →
      IsPositiveContinuousValuation (fun b => ν (e b))) ∧
    (∀ μ : B → NNReal, IsPositiveContinuousValuation μ →
      ∃! ν : L → NNReal, IsPositiveNormalValuation ν ∧ ∀ b, ν (e b) = μ b) := by
  let er : B ≃o Heyting.Regular L := e.trans (compactRegularIso hL)
  have hcoe (b : B) : (er b : L) = e b := rfl
  have hback (a : Heyting.Regular L) : (e (er.symm a) : L) = a := by
    rw [← hcoe, er.apply_symm_apply]
  constructor
  · intro ν hν
    exact iso_positive_continuous er _ (restriction_positive_continuous ν hν)
  · intro μ hμ
    let ν : L → NNReal := fun a => μ (er.symm (toRegular a))
    refine ⟨ν, ⟨regularize_positive_normal _ (iso_positive_continuous er.symm μ hμ), ?_⟩, ?_⟩
    · intro b
      change μ (er.symm (toRegular (e b : L))) = μ b
      rw [← hcoe, toRegular_coe, er.symm_apply_apply]
    · intro ξ hξ
      funext a
      calc
        ξ a = ξ aᶜᶜ := (hξ.1.2 a).symm
        _ = ξ (e (er.symm (toRegular a))) := congrArg ξ (hback (toRegular a)).symm
        _ = μ (er.symm (toRegular a)) := hξ.2 _
        _ = ν a := rfl

end Gelfand258Work
end Gelfand54_part_3

section Gelfand54_part_4
/- Source module: Work.Gelfand273.Forward -/
set_option autoImplicit false

open Set CategoryTheory QAlgorithms.Papers.Independent.Support21.P20
open GelfandVNA.Duality Heyting Gelfand258Work
open scoped NNReal

namespace Gelfand273Work

universe u

/-- The regular elements of a frame form a complete Boolean algebra; joins are
the double negation of the ambient joins (Pavlov, Proposition 2.48). -/
noncomputable instance regularCompleteBooleanAlgebra (L : Type u) [Order.Frame L] :
    CompleteBooleanAlgebra (Heyting.Regular L) where
  __ := (inferInstance : BooleanAlgebra (Heyting.Regular L))
  sSup := (Heyting.Regular.gi (α := L)).liftCompleteLattice.sSup
  sInf := (Heyting.Regular.gi (α := L)).liftCompleteLattice.sInf
  isLUB_sSup := (Heyting.Regular.gi (α := L)).liftCompleteLattice.isLUB_sSup
  isGLB_sInf := (Heyting.Regular.gi (α := L)).liftCompleteLattice.isGLB_sInf

theorem regular_coe_sSup {L : Type u} [Order.Frame L] (s : Set (Heyting.Regular L)) :
    ((sSup s : Heyting.Regular L) : L) = (sSup (((↑) : Heyting.Regular L → L) '' s))ᶜᶜ := rfl

/-- This is the object restriction needed for hyperstonean duality. The two
valuation transports are the already proved positive case of Lemma 2.58. -/
theorem hyperstonean_iff_regular_localizable {L : Type u} [Order.Frame L]
    (hL : IsStoneanLocale L) :
    IsHyperstoneanLocale L ↔ HasFiniteValuationCover (Heyting.Regular L) := by
  rw [Gelfand273Criterion.localizableCriterion]
  constructor
  · intro h b hb
    have hb' : (b : L) ≠ ⊥ := fun e => hb (Heyting.Regular.coe_injective e)
    obtain ⟨ν, hν, hn⟩ := h.2 (b : L) hb'
    exact ⟨fun a : Heyting.Regular L => ν a, restriction_positive_continuous ν hν, hn⟩
  · intro h
    refine ⟨hL, ?_⟩
    intro a ha
    have hqa : Heyting.Regular.toRegular a ≠ (⊥ : Heyting.Regular L) := by
      intro e
      have he : aᶜᶜ = ⊥ := congrArg ((↑) : Heyting.Regular L → L) e
      exact ha (le_antisymm (le_compl_compl.trans he.le) bot_le)
    obtain ⟨μ, hμ, hn⟩ := h (Heyting.Regular.toRegular a) hqa
    exact ⟨fun b => μ (Heyting.Regular.toRegular b), regularize_positive_normal μ hμ, hn⟩

theorem open_map_compl {L L' : Type u} [Order.Frame L] [Order.Frame L']
    (f : FrameHom L' L) (hf : IsOpenFrameHom f) (a : L') :
    f aᶜ = (f a)ᶜ := by
  simpa only [himp_bot, map_bot] using hf.2 a ⊥

theorem open_map_regular {L L' : Type u} [Order.Frame L] [Order.Frame L']
    (f : FrameHom L' L) (hf : IsOpenFrameHom f) {a : L'} (ha : Heyting.IsRegular a) :
    Heyting.IsRegular (f a) := by
  change (f a)ᶜᶜ = f a
  rw [← open_map_compl f hf, ← open_map_compl f hf, ha.eq]

/-- Restriction to regular elements preserves all joins, using preservation of
double negation by an open frame map. -/
noncomputable def regularMap {L L' : Type u} [Order.Frame L] [Order.Frame L']
    (f : FrameHom L' L) (hf : IsOpenFrameHom f) :
    FrameHom (Heyting.Regular L') (Heyting.Regular L) where
  toFun a := ⟨f a, open_map_regular f hf a.prop⟩
  map_top' := Heyting.Regular.coe_injective (map_top f)
  map_inf' a b := Heyting.Regular.coe_injective (map_inf f (a : L') (b : L'))
  map_sSup' s := by
    apply Heyting.Regular.coe_injective
    change f (sSup (((↑) : Heyting.Regular L' → L') '' s))ᶜᶜ =
      (sSup (((↑) : Heyting.Regular L → L) ''
        ((fun a : Heyting.Regular L' => (⟨f a, open_map_regular f hf a.prop⟩ : Heyting.Regular L)) '' s)))ᶜᶜ
    rw [open_map_compl f hf, open_map_compl f hf, map_sSup]
    simp only [Set.image_image, Function.comp_def]
    apply congrArg (fun t : Set L => (sSup t)ᶜᶜ)
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨f a, open_map_regular f hf a.prop⟩, ⟨a, ha, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨a, ha, rfl⟩

theorem open_map_compact {L L' : Type u} [Order.Frame L] [Order.Frame L']
    (hL : IsStoneanLocale L) (hL' : IsStoneanLocale L')
    (f : FrameHom L' L) (hf : IsOpenFrameHom f) {a : L'} (ha : IsCompactElement a) :
    IsCompactElement (f a) :=
  regular_compact hL (open_map_regular f hf (compact_regular hL' ha))

/-- The measurable locale assigned by the compact-opens construction. -/
noncomputable def cOpenObj (L : HStoneanLoc.{u}) : MLoc.{u} :=
  show MLocObj from
    { carrier := Heyting.Regular L.carrier
      localizable := (hyperstonean_iff_regular_localizable L.hyperstonean.1).mp L.hyperstonean }

/-- The forward functor in Proposition 2.73. -/
noncomputable def cOpenFunctor : HStoneanLoc.{u} ⥤ MLoc.{u} where
  obj := cOpenObj
  map f := InducedCategory.homMk (Frm.ofHom (regularMap f.1 f.2)).op
  map_id _ := rfl
  map_comp _ _ := rfl

noncomputable def compactOpenIso (L : HStoneanLoc.{u}) :
    (cOpenFunctor.obj L).carrier ≃o {a : L.carrier // IsCompactElement a} :=
  (compactRegularIso L.hyperstonean.1).symm

/-- The compatibility clause of the canonical target holds definitionally for
this forward functor. The equivalence itself is still a separate obligation. -/
theorem compactOpenIso_natural {L L' : HStoneanLoc.{u}} (f : L ⟶ L')
    (b : (cOpenFunctor.obj L').carrier) :
    ((compactOpenIso L (MLoc.frameHom (cOpenFunctor.map f) b) : L.carrier)) =
      f.1 ((compactOpenIso L' b : L'.carrier)) := rfl

end Gelfand273Work
end Gelfand54_part_4

section Gelfand54_part_5
/- Source module: Work.Gelfand54.PartitionTopology -/
set_option autoImplicit false
open Set TopologicalSpace

namespace Gelfand54Clopens
universe u
variable {X : Type u} [TopologicalSpace X] [ExtremallyDisconnected X]

theorem regular_carriers_disjoint
    (R : Set (Heyting.Regular (Opens X))) (hR : R.PairwiseDisjoint id) :
    Pairwise (fun a b : R => Disjoint
      (((clopenRegularIso (X := X)).symm a.val : Clopens X) : Set X)
      (((clopenRegularIso (X := X)).symm b.val : Clopens X) : Set X)) := by
  intro a b hab
  apply Clopens.coe_disjoint.mpr
  exact (hR a.property b.property (fun h => hab (Subtype.ext h))).map_orderIso
    (clopenRegularIso (X := X)).symm

/-- A family whose supremum is top in the regular-open algebra has dense
union of its corresponding actual clopen carriers. -/
theorem regular_carriers_dense
    (R : Set (Heyting.Regular (Opens X))) (hR : sSup R = ⊤) :
    Dense (⋃ a : R, (((clopenRegularIso (X := X)).symm a.val : Clopens X) : Set X)) := by
  let e := clopenRegularIso (X := X)
  let W : Opens X := ⟨⋃ a : R, ((e.symm a.val : Clopens X) : Set X),
    isOpen_iUnion (fun a => (e.symm a.val).isOpen)⟩
  let U : Clopens X := ⟨(closure (W : Set X))ᶜ,
    ⟨(ExtremallyDisconnected.open_closure _ W.isOpen).isClosed_compl,
      isClosed_closure.isOpen_compl⟩⟩
  have hd (a : Heyting.Regular (Opens X)) (ha : a ∈ R) : Disjoint (e U) a := by
    have h : Disjoint U (e.symm a) := by
      apply Clopens.coe_disjoint.mp
      apply Set.disjoint_left.mpr
      intro x hxU hxa
      exact hxU (subset_closure (Set.mem_iUnion.mpr ⟨⟨a, ha⟩, hxa⟩))
    simpa only [OrderIso.apply_symm_apply] using h.map_orderIso e
  have hdisj : Disjoint (e U) (sSup R) := disjoint_sSup_iff.mpr hd
  rw [hR] at hdisj
  have he0 : e U = ⊥ := by simpa only [inf_top_eq] using hdisj.eq_bot
  have hU0 : U = ⊥ := e.injective (he0.trans e.map_bot.symm)
  apply dense_iff_closure_eq.mpr
  apply Set.eq_univ_of_forall
  intro x
  by_contra hx
  have hxU : x ∈ U := hx
  rw [hU0] at hxU
  change False at hxU
  exact hxU

end Gelfand54Clopens
end Gelfand54_part_5

section Gelfand54_part_6
/- Source module: Work.Gelfand454.CountableSup -/
open Set QAlgorithms.Papers.Independent.Support21.P20 GelfandVNA.Duality

namespace Gelfand454
universe u
variable {X : Type u} (E : Enhanced X)

theorem mk_le_mk {a b : Set X} (ha : a ∈ E.measurable) (hb : b ∈ E.measurable) :
    MmodN.mk a ha ≤ MmodN.mk b hb ↔ a \ b ∈ E.negligible := Iff.rfl

theorem mk_mono {a b : Set X} (ha : a ∈ E.measurable) (hb : b ∈ E.measurable)
    (hab : a ⊆ b) : MmodN.mk a ha ≤ MmodN.mk b hb := by
  change a \ b ∈ E.negligible
  simpa only [Set.diff_eq_empty.mpr hab] using E.sigmaIdeal.1

/-- Countable unions are actual least upper bounds in the exact canonical quotient. -/
theorem mk_iUnion_isLUB (a : ℕ → Set X) (ha : ∀ n, a n ∈ E.measurable) :
    IsLUB (Set.range fun n => MmodN.mk (a n) (ha n))
      (MmodN.mk (⋃ n, a n) (E.sigmaAlgebra.2.2 a ha)) := by
  constructor
  · rintro q ⟨n, rfl⟩
    exact mk_mono E (ha n) _ (Set.subset_iUnion a n)
  · intro q hq
    induction q using Quotient.ind with
    | _ b =>
      change (⋃ n, a n) \ b.1 ∈ E.negligible
      rw [Set.iUnion_diff]
      apply E.sigmaIdeal.2.2
      intro n
      exact hq (Set.mem_range_self n)

theorem exists_lub_sequence (a : ℕ → MmodN E) :
    ∃ q, IsLUB (Set.range a) q := by
  classical
  let r (n : ℕ) := (a n).out
  have heq (n : ℕ) : MmodN.mk (r n).1 (r n).2 = a n := Quotient.out_eq _
  refine ⟨MmodN.mk (⋃ n, (r n).1) (E.sigmaAlgebra.2.2 _ fun n => (r n).2), ?_⟩
  have h := mk_iUnion_isLUB E (fun n => (r n).1) (fun n => (r n).2)
  simpa only [heq] using h

/-- No measure hypothesis is needed for sigma-completeness of M/N. -/
theorem exists_lub_countable (s : Set (MmodN E)) (hs : s.Countable) :
    ∃ q, IsLUB s q := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · refine ⟨MmodN.mk ∅ E.sigmaAlgebra.1, ?_, ?_⟩
    · simp
    · intro q _
      induction q using Quotient.ind with
      | _ b => exact mk_mono E _ b.2 (Set.empty_subset _)
  · obtain ⟨a, rfl⟩ := hs.exists_eq_range hne
    exact exists_lub_sequence E a

end Gelfand454
end Gelfand54_part_6

section Gelfand54_part_7
/- Source module: Work.Gelfand54.BaireIso -/
open Set TopologicalSpace GelfandVNA.Duality
open scoped Topology

namespace Gelfand54Baire
universe u
variable {X : Type u} [TopologicalSpace X]

/-- A clopen is Baire measurable for the exact canonical enhanced space. -/
theorem clopen_measurable (C : Clopens X) : (C : Set X) ∈ (TM X).measurable :=
  (baire_iff _).2 C.isOpen.baireMeasurableSet

/-- The canonical quotient class of a clopen set. -/
def clopenClass (C : Clopens X) : MmodN (TM X) :=
  MmodN.mk (C : Set X) (clopen_measurable C)

/-- In a Baire space a clopen difference is meagre exactly when it is empty. -/
theorem clopenClass_le_iff [BaireSpace X] (C D : Clopens X) :
    clopenClass C ≤ clopenClass D ↔ C ≤ D := by
  change IsMeagre ((C : Set X) \ D) ↔ (C : Set X) ⊆ D
  constructor
  · intro hn x hx
    by_contra hD
    exact not_isMeagre_of_isOpen (IsOpen.sdiff C.isOpen D.isClosed) ⟨x, hx, hD⟩ hn
  · intro h
    rw [Set.sdiff_eq_empty.mpr h]
    exact IsMeagre.empty

/-- Every Baire measurable set in an extremally disconnected space agrees
modulo the canonical meagre ideal with a clopen set. -/
theorem exists_clopen_representative [ExtremallyDisconnected X]
    (s : Set X) (hs : s ∈ (TM X).measurable) :
    ∃ C : Clopens X, IsMeagre (symmDiff s (C : Set X)) := by
  obtain ⟨U, hU, h⟩ := hs
  refine ⟨⟨closure U, isClosed_closure, ExtremallyDisconnected.open_closure U hU⟩, ?_⟩
  apply (isMeagre_symmDiff_iff _ _).2
  exact ((isMeagre_symmDiff_iff _ _).1 h).trans
    (closure_residualEq hU.isLocallyClosed).symm

/-- The actual clopen classes embed in the canonical quotient order. -/
def clopenOrderEmbedding [BaireSpace X] : Clopens X ↪o MmodN (TM X) :=
  OrderEmbedding.ofMapLEIff clopenClass clopenClass_le_iff

theorem clopenClass_surjective [ExtremallyDisconnected X] :
    Function.Surjective (clopenClass (X := X)) := by
  intro q
  induction q using Quotient.ind with
  | _ s =>
    obtain ⟨C, hC⟩ := exists_clopen_representative s.1 s.2
    refine ⟨C, ?_⟩
    apply Quotient.sound
    change IsMeagre (symmDiff (C : Set X) s.1)
    rw [symmDiff_comm]
    exact hC

/-- The Baire quotient is the Boolean algebra of clopens, with its original
quotient order and no replacement of the canonical null ideal. -/
noncomputable def baireClopenIso (X : Type u) [TopologicalSpace X]
    [BaireSpace X] [ExtremallyDisconnected X] : MmodN (TM X) ≃o Clopens X :=
  (OrderIso.ofSurjective clopenOrderEmbedding clopenClass_surjective).symm

@[simp] theorem baireClopenIso_symm_apply [BaireSpace X] [ExtremallyDisconnected X]
    (C : Clopens X) : (baireClopenIso X).symm C = clopenClass C := rfl

/-- A specified clopen representative determines the image of a measurable set. -/
theorem baireClopenIso_mk_eq [BaireSpace X] [ExtremallyDisconnected X]
    (s : Set X) (hs : s ∈ (TM X).measurable) (C : Clopens X)
    (hC : IsMeagre (symmDiff s (C : Set X))) :
    baireClopenIso X (MmodN.mk s hs) = C := by
  apply (baireClopenIso X).symm.injective
  rw [OrderIso.symm_apply_apply, baireClopenIso_symm_apply]
  exact Quotient.sound hC

/-- The selected clopen represents precisely the given Baire set modulo meagre sets. -/
theorem baireClopenIso_mk_spec [BaireSpace X] [ExtremallyDisconnected X]
    (s : Set X) (hs : s ∈ (TM X).measurable) :
    IsMeagre (symmDiff s (baireClopenIso X (MmodN.mk s hs) : Set X)) := by
  have h := (baireClopenIso X).symm_apply_apply (MmodN.mk s hs)
  rw [baireClopenIso_symm_apply] at h
  exact Quotient.exact h.symm

/-- Countable measurable unions become countable least upper bounds of the
corresponding clopen representatives. No preservation assumption is added. -/
theorem baireClopenIso_iUnion_isLUB [BaireSpace X] [ExtremallyDisconnected X]
    (s : ℕ → Set X) (hs : ∀ n, s n ∈ (TM X).measurable) :
    IsLUB (Set.range fun n => baireClopenIso X (MmodN.mk (s n) (hs n)))
      (baireClopenIso X (MmodN.mk (⋃ n, s n) ((TM X).sigmaAlgebra.2.2 s hs))) := by
  have h := (baireClopenIso X).isLUB_image'.2 (Gelfand454.mk_iUnion_isLUB (TM X) s hs)
  simpa only [← Set.range_comp, Function.comp_def] using h

end Gelfand54Baire
end Gelfand54_part_7

section Gelfand54_part_8
/- Source module: Work.Gelfand454.FiniteMeasure -/
open MeasureTheory QAlgorithms.Papers.Independent.Support21.P20 GelfandVNA.Duality

namespace Gelfand454
universe u

/-- The measurable-space structure already specified by an enhanced space. -/
@[instance_reducible] def measurableSpace {X : Type u} (E : Enhanced X) : MeasurableSpace X where
  MeasurableSet' s := s ∈ E.measurable
  measurableSet_empty := E.sigmaAlgebra.1
  measurableSet_compl := E.sigmaAlgebra.2.1
  measurableSet_iUnion := E.sigmaAlgebra.2.2

section
variable {X : Type u} (E : Enhanced X)

/-- A finite enhanced complex measure is an ordinary complex vector measure.
Its unconstrained values on nonmeasurable sets are replaced by zero. -/
noncomputable def complexMeasureOf (μ : Set X → ℂ)
    (hμ : IsEMeasure E E.measurable μ) : @ComplexMeasure X (measurableSpace E) := by
  classical
  letI : MeasurableSpace X := measurableSpace E
  exact {
    measureOf' s := if s ∈ E.measurable then μ s else 0
    empty' := by
      simp only [E.sigmaAlgebra.1, if_pos]
      exact hμ.2.2.2.2.1 _ E.sigmaIdeal.1
    not_measurable' s hs := if_neg hs
    m_iUnion' f hs hd := by
      have hs' : ∀ i, f i ∈ E.measurable := hs
      have hu := E.sigmaAlgebra.2.2 _ hs'
      simpa only [hs', hu, if_pos] using (hμ.2.2.2.2.2.1 _ hs hd hu).2
  }
theorem complexMeasureOf_apply (μ : Set X → ℂ) (hμ : IsEMeasure E E.measurable μ)
    {s : Set X} (hs : s ∈ E.measurable) : complexMeasureOf E μ hμ s = μ s := by
  exact if_pos hs

/-- A positive finite measure with the same null ideal as a faithful finite
enhanced complex measure. Taking both real variations avoids cancellation. -/
noncomputable def finiteMeasure (μ : Set X → ℂ) (hμ : IsEMeasure E E.measurable μ) :
    @Measure X (measurableSpace E) := by
  letI : MeasurableSpace X := measurableSpace E
  exact
    (ComplexMeasure.re (complexMeasureOf E μ hμ)).totalVariation +
    (ComplexMeasure.im (complexMeasureOf E μ hμ)).totalVariation

instance finiteMeasure_isFinite (μ : Set X → ℂ) (hμ : IsEMeasure E E.measurable μ) :
    IsFiniteMeasure (finiteMeasure E μ hμ) := by
  letI : MeasurableSpace X := measurableSpace E
  unfold finiteMeasure
  infer_instance

theorem finiteMeasure_null_iff_measurable (μ : Set X → ℂ)
    (hμ : IsEMeasure E E.measurable μ) (hf : IsFaithfulEMeasure E E.measurable μ)
    {s : Set X} (hs : s ∈ E.measurable) :
    finiteMeasure E μ hμ s = 0 ↔ s ∈ E.negligible := by
  letI : MeasurableSpace X := measurableSpace E
  have hsm : MeasurableSet s := hs
  rw [finiteMeasure, Measure.add_apply, add_eq_zero,
    SignedMeasure.totalVariation_eq_variation,
    SignedMeasure.totalVariation_eq_variation,
    VectorMeasure.variation_apply_eq_zero hsm,
    VectorMeasure.variation_apply_eq_zero hsm]
  constructor
  · rintro ⟨hr, hi⟩
    apply hf s hs
    intro t ht hts
    apply Complex.ext
    · have h := hr t hts ht
      change (complexMeasureOf E μ hμ t).re = 0 at h
      simpa only [complexMeasureOf_apply E μ hμ ht, Complex.zero_re] using h
    · have h := hi t hts ht
      change (complexMeasureOf E μ hμ t).im = 0 at h
      simpa only [complexMeasureOf_apply E μ hμ ht, Complex.zero_im] using h
  · intro hn
    have hzero : ∀ t, t ⊆ s → t ∈ E.measurable → complexMeasureOf E μ hμ t = 0 := by
      intro t hts ht
      rw [complexMeasureOf_apply E μ hμ ht]
      exact hμ.2.2.2.2.1 _ (negligible_mono E hts hn)
    constructor
    · intro t hts ht
      change (complexMeasureOf E μ hμ t).re = 0
      rw [hzero t hts ht, Complex.zero_re]
    · intro t hts ht
      change (complexMeasureOf E μ hμ t).im = 0
      rw [hzero t hts ht, Complex.zero_im]

theorem finiteMeasure_null_iff (μ : Set X → ℂ)
    (hμ : IsEMeasure E E.measurable μ) (hf : IsFaithfulEMeasure E E.measurable μ)
    (s : Set X) : finiteMeasure E μ hμ s = 0 ↔ s ∈ E.negligible := by
  letI : MeasurableSpace X := measurableSpace E
  constructor
  · intro h
    apply negligible_mono E (subset_toMeasurable (finiteMeasure E μ hμ) s)
    apply (finiteMeasure_null_iff_measurable E μ hμ hf
      (measurableSet_toMeasurable (finiteMeasure E μ hμ) s)).1
    rwa [measure_toMeasurable]
  · intro h
    exact (finiteMeasure_null_iff_measurable E μ hμ hf (E.negligibleMeasurable h)).2 h

/-- The exact canonical sigma-finiteness predicate supplies a finite positive
measure, without adding positivity to its complex-measure hypothesis. -/
theorem exists_finiteMeasure (hE : IsSigmaFiniteE E) :
    ∃ ν : @Measure X (measurableSpace E), IsFiniteMeasure ν ∧ ∀ s : Set X, ν s = 0 ↔ s ∈ E.negligible := by
  letI : MeasurableSpace X := measurableSpace E
  obtain ⟨μ, hμ, hf⟩ := hE
  exact ⟨finiteMeasure E μ hμ, inferInstance, finiteMeasure_null_iff E μ hμ hf⟩

end
end Gelfand454
end Gelfand54_part_8

section Gelfand54_part_9
/- Source module: Work.Gelfand54.ValuationSums -/
set_option autoImplicit false
open Set Filter QAlgorithms.Papers.Independent.Support21.P20
open scoped NNReal

namespace Gelfand54
variable {B : Type*} [CompleteBooleanAlgebra B]
variable (ν : B → ℝ≥0) (hν : IsPositiveContinuousValuation ν)
include hν

theorem valuation_finset_sup_eq_sum {ι : Type*} (s : Finset ι) (f : ι → B)
    (hd : ∀ i j, i ≠ j → Disjoint (f i) (f j)) :
    ν (s.sup f) = ∑ i ∈ s, ν (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [hν.1.1]
  | @insert i s hi ih =>
    have hdisj : Disjoint (f i) (s.sup f) := by
      apply Finset.disjoint_sup_right.mpr
      intro j hj
      exact hd i j (fun h => hi (h.symm ▸ hj))
    have hadd : ν (f i ⊔ s.sup f) = ν (f i) + ν (s.sup f) := by
      simpa only [hdisj.eq_bot, hν.1.1, add_zero] using (hν.1.2 (f i) (s.sup f)).symm
    rw [Finset.sup_insert, hadd, Finset.sum_insert hi, ih]

/-- A finite positive continuous valuation is completely additive. -/
theorem valuation_hasSum_disjoint {ι : Type*} (f : ι → B)
    (hd : ∀ i j, i ≠ j → Disjoint (f i) (f j)) :
    HasSum (fun i => ν (f i)) (ν (iSup f)) := by
  classical
  let g : Finset ι → B := fun s => s.sup f
  have hne : (Set.range g).Nonempty := ⟨g ∅, ⟨∅, rfl⟩⟩
  have hdir : DirectedOn (· ≤ ·) (Set.range g) := by
    rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
    exact ⟨g (s ∪ t), ⟨s ∪ t, rfl⟩,
      Finset.sup_mono Finset.subset_union_left,
      Finset.sup_mono Finset.subset_union_right⟩
  have hlub : IsLUB (Set.range g) (iSup f) := by
    constructor
    · rintro _ ⟨s, rfl⟩
      exact Finset.sup_le (fun i _ => le_iSup f i)
    · intro b hb
      apply iSup_le
      intro i
      have h := hb (Set.mem_range_self ({i} : Finset ι))
      simpa only [g, Finset.sup_singleton] using h
  have hνlub : IsLUB (Set.range (fun s => ν (g s))) (ν (iSup f)) := by
    simpa only [← Set.range_comp, Function.comp_def] using
      hν.2.2 (Set.range g) (iSup f) hne hdir hlub
  have hm : Monotone (fun s => ν (g s)) := by
    intro s t hst
    exact hν.2.1 (Finset.sup_mono hst)
  have ht := tendsto_atTop_isLUB hm hνlub
  change Tendsto (fun s : Finset ι => ∑ i ∈ s, ν (f i)) atTop (nhds (ν (iSup f)))
  simpa only [g, valuation_finset_sup_eq_sum ν hν _ _ hd] using ht

end Gelfand54
end Gelfand54_part_9

section Gelfand54_part_10
/- Source module: Work.Gelfand54.QuotientValuation -/
open Set MeasureTheory QAlgorithms.Papers.Independent.Support21.P20 GelfandVNA.Duality
open scoped NNReal

namespace Gelfand54Quotient
universe u v
variable {X : Type u} (E : Enhanced X)
variable {B : Type v} [CompleteBooleanAlgebra B] (e : MmodN E ≃o B)

/-- The empty measurable set maps to the actual bottom of the target algebra. -/
theorem map_mk_empty : e (MmodN.mk ∅ E.sigmaAlgebra.1) = ⊥ := by
  apply le_antisymm _ bot_le
  have h (q : MmodN E) : MmodN.mk ∅ E.sigmaAlgebra.1 ≤ q := by
    induction q using Quotient.ind with
    | _ q => exact Gelfand454.mk_mono E _ q.2 (Set.empty_subset _)
  exact (e.monotone (h (e.symm ⊥))).trans_eq (e.apply_symm_apply _)

theorem map_mk_eq_bot_iff (s : Set X) (hs : s ∈ E.measurable) :
    e (MmodN.mk s hs) = ⊥ ↔ s ∈ E.negligible := by
  rw [← map_mk_empty E e, e.injective.eq_iff]
  constructor
  · intro h
    have h' := Quotient.exact h
    change (s \ ∅) ∪ (∅ \ s) ∈ E.negligible at h'
    simpa only [sdiff_empty, empty_sdiff, union_empty] using h'
  · intro h
    apply Quotient.sound
    change (s \ ∅) ∪ (∅ \ s) ∈ E.negligible
    simpa only [sdiff_empty, empty_sdiff, union_empty] using h

/-- The quotient order alone identifies intersections with infima. -/
theorem map_mk_inter (a b : Set X) (ha : a ∈ E.measurable) (hb : b ∈ E.measurable)
    (hi : a ∩ b ∈ E.measurable) :
    e (MmodN.mk (a ∩ b) hi) = e (MmodN.mk a ha) ⊓ e (MmodN.mk b hb) := by
  have hglb : IsGLB {MmodN.mk a ha, MmodN.mk b hb} (MmodN.mk (a ∩ b) hi) := by
    constructor
    · intro q hq
      rcases hq with rfl | hq
      · exact Gelfand454.mk_mono E hi ha inter_subset_left
      · rcases hq with rfl
        exact Gelfand454.mk_mono E hi hb inter_subset_right
    · intro q hq
      have hqa := hq (Set.mem_insert _ _)
      have hqb := hq (Set.mem_insert_of_mem _ (Set.mem_singleton _))
      induction q using Quotient.ind with
      | _ q =>
        change q.1 \ (a ∩ b) ∈ E.negligible
        rw [Set.sdiff_inter]
        exact negligible_union E hqa hqb
  have h := e.isGLB_image'.2 hglb
  have h' : IsGLB {e (MmodN.mk a ha), e (MmodN.mk b hb)}
      (e (MmodN.mk (a ∩ b) hi)) := by simpa only [Set.image_pair] using h
  exact h'.unique isGLB_pair

theorem map_mk_disjoint (a b : Set X) (ha : a ∈ E.measurable) (hb : b ∈ E.measurable)
    (hd : Disjoint a b) : Disjoint (e (MmodN.mk a ha)) (e (MmodN.mk b hb)) := by
  letI := Gelfand454.measurableSpace E
  have hi : a ∩ b ∈ E.measurable :=
    (show MeasurableSet a from ha).inter (show MeasurableSet b from hb)
  apply disjoint_iff.mpr
  rw [← map_mk_inter E e a b ha hb hi]
  apply (map_mk_eq_bot_iff E e _ hi).2
  rw [Set.disjoint_iff_inter_eq_empty.mp hd]
  exact E.sigmaIdeal.1

theorem map_mk_iUnion (s : ℕ → Set X) (hs : ∀ n, s n ∈ E.measurable) :
    e (MmodN.mk (⋃ n, s n) (E.sigmaAlgebra.2.2 s hs)) =
      ⨆ n, e (MmodN.mk (s n) (hs n)) := by
  have h := e.isLUB_image'.2 (Gelfand454.mk_iUnion_isLUB E s hs)
  have h' : IsLUB (Set.range fun n => e (MmodN.mk (s n) (hs n)))
      (e (MmodN.mk (⋃ n, s n) (E.sigmaAlgebra.2.2 s hs))) := by
    simpa only [← Set.range_comp, Function.comp_def] using h
  exact h'.unique isLUB_iSup

/-- Pull a finite nonnegative valuation back to the canonical measurable sets. -/
noncomputable def valuationEMeasure (ν : B → ℝ≥0) (s : Set X) : ℂ := by
  classical
  exact if hs : s ∈ E.measurable then ((ν (e (MmodN.mk s hs)) : ℝ) : ℂ) else 0

theorem valuationEMeasure_apply (ν : B → ℝ≥0) (s : Set X) (hs : s ∈ E.measurable) :
    valuationEMeasure E e ν s = ((ν (e (MmodN.mk s hs)) : ℝ) : ℂ) := by
  simp only [valuationEMeasure, dif_pos hs]

/-- Continuity supplies both countable additivity and absolute summability. -/
theorem valuationEMeasure_additive (ν : B → ℝ≥0) (hν : IsPositiveContinuousValuation ν)
    (s : ℕ → Set X) (hs : ∀ n, s n ∈ E.measurable)
    (hd : Pairwise (Function.onFun Disjoint s)) :
    Summable (fun n => ‖valuationEMeasure E e ν (s n)‖) ∧
      HasSum (fun n => valuationEMeasure E e ν (s n)) (valuationEMeasure E e ν (⋃ n, s n)) := by
  have h := Gelfand54.valuation_hasSum_disjoint ν hν
    (fun n => e (MmodN.mk (s n) (hs n)))
    (fun i j hij => map_mk_disjoint E e _ _ (hs i) (hs j) (hd hij))
  rw [← map_mk_iUnion E e s hs] at h
  have hR := NNReal.hasSum_coe.mpr h
  constructor
  · simpa only [valuationEMeasure_apply E e ν _ (hs _), Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)] using hR.summable
  · simpa only [valuationEMeasure_apply E e ν _ (hs _),
      valuationEMeasure_apply E e ν _ (E.sigmaAlgebra.2.2 s hs)] using
      Complex.hasSum_ofReal.mpr hR

include e

/-- A faithful finite continuous valuation on the exact quotient yields the
canonical sigma-finiteness predicate, including its absolute-summability clause. -/
theorem sigmaFinite_of_quotient_valuation (ν : B → ℝ≥0)
    (hν : IsPositiveContinuousValuation ν) (hf : ∀ b, ν b = 0 → b = ⊥) :
    IsSigmaFiniteE E := by
  letI := Gelfand454.measurableSpace E
  refine ⟨valuationEMeasure E e ν, ?_, ?_⟩
  · refine ⟨Subset.rfl, E.negligibleMeasurable, ?_, ?_, ?_, ?_, ?_⟩
    · intro a ha b hb
      exact (show MeasurableSet a from ha).union (show MeasurableSet b from hb)
    · intro a ha b hb _
      exact hb
    · intro n hn
      rw [valuationEMeasure_apply E e ν n (E.negligibleMeasurable hn),
        (map_mk_eq_bot_iff E e n (E.negligibleMeasurable hn)).2 hn, hν.1.1]
      simp
    · intro s hs hd _
      exact valuationEMeasure_additive E e ν hν s hs hd
    · intro s hs hd _
      exact ⟨E.sigmaAlgebra.2.2 s hs, (valuationEMeasure_additive E e ν hν s hs hd).2⟩
  · intro s hs hz
    apply (map_mk_eq_bot_iff E e s hs).1
    apply hf
    have h := hz s hs Subset.rfl
    rw [valuationEMeasure_apply E e ν s hs] at h
    exact_mod_cast h

end Gelfand54Quotient
end Gelfand54_part_10

section Gelfand54_part_11
/- Source module: Work.Gelfand54.CarrierSigmaFinite -/
open Set TopologicalSpace GelfandVNA.Duality
open QAlgorithms.Papers.Independent.Support21.P20
open scoped NNReal

namespace Gelfand54Quotient
universe u

/-- The standard principal-interval lattice of a complete Boolean algebra
is again a complete Boolean algebra; its existing order and bounds are retained. -/
@[instance_reducible] noncomputable def intervalCompleteBooleanAlgebra
    {B : Type*} [CompleteBooleanAlgebra B] (a : B) : CompleteBooleanAlgebra (Set.Iic a) := by
  letI : DistribLattice (Set.Iic a) :=
    { (inferInstance : Lattice (Set.Iic a)) with le_sup_inf := fun _ _ _ => le_sup_inf }
  letI : BooleanAlgebra (Set.Iic a) := DistribLattice.booleanAlgebraOfComplemented (Set.Iic a)
  exact { (inferInstance : CompleteLattice (Set.Iic a)),
    (inferInstance : BooleanAlgebra (Set.Iic a)) with }

/-- A faithful finite continuous valuation on a principal regular-open interval
makes its actual clopen carrier sigma-finite in the canonical enhanced sense. -/
theorem regularCarrier_sigmaFinite {X : Type u} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] [ExtremallyDisconnected X]
    (a : Heyting.Regular (Opens X)) (ν : Set.Iic a → ℝ≥0)
    (hν : IsPositiveContinuousValuation ν) (hf : ∀ b, ν b = 0 → b = ⊥) :
    IsSigmaFiniteE (TM ((Gelfand54Clopens.clopenRegularIso (X := X)).symm a)) := by
  letI : CompleteBooleanAlgebra (Set.Iic a) := intervalCompleteBooleanAlgebra a
  let C : Clopens X := (Gelfand54Clopens.clopenRegularIso (X := X)).symm a
  letI : CompactSpace C := isCompact_iff_compactSpace.mp C.isClosed.isCompact
  letI : ExtremallyDisconnected C := Gelfand54Clopens.subtype_extremallyDisconnected C
  let e : MmodN (TM C) ≃o Set.Iic a :=
    (Gelfand54Baire.baireClopenIso C).trans (Gelfand54Clopens.regularCarrierIso a)
  exact sigmaFinite_of_quotient_valuation (TM C) e ν hν hf

end Gelfand54Quotient
end Gelfand54_part_11

section Gelfand54_part_12
/- Source module: Work.Gelfand54.Morphisms -/
set_option autoImplicit false
open Set CategoryTheory GelfandVNA.Duality
open QAlgorithms.Papers.Independent.Support21.P20

namespace Gelfand54
universe u

theorem partialPreimage_some {X Y : Type u} (f : X → Y) (s : Set Y) :
    partialPreimage (fun x => some (f x)) s = f ⁻¹' s := by
  ext x
  simp [partialPreimage]

/-- Lemma 5.3: every continuous open map gives a total premap for the exact TM objects. -/
theorem isPremap_TM {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hc : Continuous f) (ho : IsOpenMap f) :
    IsPremap (TM X) (TM Y) (fun x => some (f x)) := by
  refine ⟨?_, ?_, ?_⟩
  · have he : (partialDomain (fun x => some (f x)))ᶜ = ∅ := by
      ext x
      simp [partialDomain]
    rw [he]
    exact IsMeagre.empty
  · intro s hs
    rw [partialPreimage_some]
    exact (baire_iff _).2 (BaireMeasurableSet.preimage hc ho ((baire_iff _).1 hs))
  · intro s hs
    rw [partialPreimage_some]
    exact IsMeagre.preimage_of_isOpenMap hc ho hs

/-- The entire morphism clause of the frozen Proposition 5.4. -/
theorem hstonean_morphism {S T : HStonean.{u}} (f : S ⟶ T) :
    IsPremap (TM S.toTop) (TM T.toTop) (fun x => some (f.1 x)) :=
  isPremap_TM f.1.continuous f.2

end Gelfand54
end Gelfand54_part_12

section Gelfand54_part_13
/- Source module: Work.Gelfand54.Gluing -/
set_option autoImplicit false
open Set TopologicalSpace GelfandVNA.Duality
open QAlgorithms.Papers.Independent.Support21.P20

namespace Gelfand54Gluing
universe u
variable {X I : Type u} [TopologicalSpace X]

/-- Nowhere-dense pieces inside disjoint open carriers have nowhere-dense union. -/
theorem nowhereDense_iUnion (A : I → Set X) (ho : ∀ i, IsOpen (A i))
    (hd : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hcover : Dense (⋃ i, A i)) (n : I → Set X)
    (hnA : ∀ i, n i ⊆ A i) (hn : ∀ i, IsNowhereDense (n i)) :
    IsNowhereDense (⋃ i, n i) := by
  change interior (closure (⋃ i, n i)) = ∅
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨y, hyV, hyA⟩ := hcover.inter_open_nonempty
    (interior (closure (⋃ i, n i))) isOpen_interior ⟨x, hx⟩
  obtain ⟨i, hyi⟩ := mem_iUnion.mp hyA
  have hinter : A i ∩ (⋃ j, n j) = n i := by
    ext z
    constructor
    · rintro ⟨hzA, hzN⟩
      obtain ⟨j, hzj⟩ := mem_iUnion.mp hzN
      by_cases hij : i = j
      · simpa only [hij] using hzj
      · exact False.elim ((Set.disjoint_left.mp (hd hij)) hzA (hnA j hzj))
    · intro hz
      exact ⟨hnA i hz, mem_iUnion.mpr ⟨i, hz⟩⟩
  have hsub : A i ∩ interior (closure (⋃ j, n j)) ⊆ closure (n i) := by
    intro z hz
    have h := (ho i).inter_closure ⟨hz.1, interior_subset hz.2⟩
    rwa [hinter] at h
  have hsubi : A i ∩ interior (closure (⋃ j, n j)) ⊆ interior (closure (n i)) :=
    interior_maximal hsub ((ho i).inter isOpen_interior)
  have hbad := hsubi ⟨hyi, hyV⟩
  have he : interior (closure (n i)) = ∅ := hn i
  rwa [he] at hbad

variable (A : I → Clopens X)

def residual : Set X := (⋃ i, (A i : Set X))ᶜ

theorem residual_meagre (hcover : Dense (⋃ i, (A i : Set X))) :
    IsMeagre (residual A) := by
  have hc : IsClosed (residual A) := (isOpen_iUnion fun i => (A i).isOpen).isClosed_compl
  apply IsNowhereDense.isMeagre
  apply hc.isNowhereDense_iff.mpr
  apply interior_eq_empty_iff_dense_compl.mpr
  simpa only [residual, compl_compl] using hcover

theorem meagre_iUnion_images
    (hd : Pairwise (fun i j => Disjoint (A i : Set X) (A j : Set X)))
    (hcover : Dense (⋃ i, (A i : Set X)))
    (hrare : ∀ n : Set X, IsMeagre n → IsNowhereDense n)
    (n : ∀ i, Set (A i)) (hn : ∀ i, IsMeagre (n i)) :
    IsMeagre (⋃ i, Subtype.val '' n i) := by
  apply IsNowhereDense.isMeagre
  apply nowhereDense_iUnion (fun i => (A i : Set X)) (fun i => (A i).isOpen)
    hd hcover (fun i => Subtype.val '' n i)
  · intro i x hx
    obtain ⟨y, _, rfl⟩ := hx
    exact y.property
  · intro i
    exact hrare _ (IsMeagre.image_val (hn i))

theorem measurable_iUnion_images
    (hd : Pairwise (fun i j => Disjoint (A i : Set X) (A j : Set X)))
    (hcover : Dense (⋃ i, (A i : Set X)))
    (hrare : ∀ n : Set X, IsMeagre n → IsNowhereDense n)
    (m : ∀ i, Set (A i)) (hm : ∀ i, m i ∈ (TM (A i)).measurable) :
    (⋃ i, Subtype.val '' m i) ∈ (TM X).measurable := by
  have hm' : ∀ i, ∃ U : Set (A i), IsOpen U ∧ IsMeagre (symmDiff (m i) U) := hm
  choose U hU hdiff using hm'
  refine ⟨⋃ i, Subtype.val '' U i, isOpen_iUnion (fun i =>
    (A i).isOpen.isOpenEmbedding_subtypeVal.isOpenMap _ (hU i)), ?_⟩
  have hn := meagre_iUnion_images A hd hcover hrare
    (fun i => symmDiff (m i) (U i)) hdiff
  apply hn.mono
  simpa only [Set.image_symmDiff Subtype.val_injective] using
    (Set.iUnion_symmDiff_iUnion_subset (f := fun i => Subtype.val '' m i)
      (g := fun i => Subtype.val '' U i))

/-- The negligible residual uses the complete all-null enhanced structure. -/
def nullEnhanced (Y : Type u) : Enhanced Y where
  measurable := univ
  negligible := univ
  sigmaAlgebra := ⟨mem_univ _, fun _ _ => mem_univ _, fun _ _ => mem_univ _⟩
  sigmaIdeal := ⟨mem_univ _, fun _ _ _ _ => mem_univ _, fun _ _ => mem_univ _⟩
  negligibleMeasurable := fun _ _ => mem_univ _

theorem nullEnhanced_sigmaFinite (Y : Type u) : IsSigmaFiniteE (nullEnhanced Y) := by
  refine ⟨fun _ => 0, ?_, ?_⟩
  · refine ⟨subset_rfl, subset_rfl, ?_, ?_, ?_, ?_, ?_⟩
    · intro a ha b hb
      exact mem_univ _
    · intro a ha b hb hba
      exact mem_univ _
    · intro n hn
      rfl
    · intro m hm hdisj hunion
      exact ⟨by simpa only [norm_zero] using (summable_zero : Summable (fun _ : ℕ => (0 : ℝ))),
        hasSum_zero⟩
    · intro m hm hdisj habs
      exact ⟨mem_univ _, hasSum_zero⟩
  · intro m hm hzero
    exact mem_univ _

def Fiber : Option I → Type u
  | none => residual A
  | some i => A i

def fiberEnhanced : (j : Option I) → Enhanced (Fiber A j)
  | none => nullEnhanced (residual A)
  | some i => TM (A i)

def evaluate : (Σ j, Fiber A j) → X
  | ⟨none, x⟩ => x.val
  | ⟨some _, x⟩ => x.val

theorem evaluate_bijective
    (hd : Pairwise (fun i j => Disjoint (A i : Set X) (A j : Set X))) :
    Function.Bijective (evaluate A) := by
  constructor
  · rintro ⟨i, x⟩ ⟨j, y⟩ h
    cases i with
    | none =>
      cases j with
      | none =>
        change x.val = y.val at h
        exact congrArg (Sigma.mk none) (Subtype.ext h)
      | some j =>
        change x.val = y.val at h
        exact False.elim (x.property (mem_iUnion.mpr ⟨j, h.symm ▸ y.property⟩))
    | some i =>
      cases j with
      | none =>
        change x.val = y.val at h
        exact False.elim (y.property (mem_iUnion.mpr ⟨i, h ▸ x.property⟩))
      | some j =>
        change x.val = y.val at h
        have hij : i = j := by
          by_contra hne
          exact (Set.disjoint_left.mp (hd hne)) x.property (h.symm ▸ y.property)
        subst j
        exact congrArg (Sigma.mk (some i)) (Subtype.ext h)
  · intro x
    by_cases hx : ∃ i, x ∈ (A i : Set X)
    · obtain ⟨i, hi⟩ := hx
      exact ⟨⟨some i, ⟨x, hi⟩⟩, rfl⟩
    · refine ⟨⟨none, ⟨x, ?_⟩⟩, rfl⟩
      exact fun h => hx (mem_iUnion.mp h)

def partitionEquiv
    (hd : Pairwise (fun i j => Disjoint (A i : Set X) (A j : Set X))) :
    (Σ j, Fiber A j) ≃ X := Equiv.ofBijective (evaluate A) (evaluate_bijective A hd)

theorem evaluate_image (m : Set (Σ j, Fiber A j)) :
    evaluate A '' m =
      (Subtype.val : residual A → X) ''
        ((@Sigma.mk (Option I) (Fiber A) none) ⁻¹' m) ∪
        ⋃ i, (Subtype.val : A i → X) ''
          ((@Sigma.mk (Option I) (Fiber A) (some i)) ⁻¹' m) := by
  ext x
  constructor
  · rintro ⟨⟨j, y⟩, hy, rfl⟩
    cases j with
    | none => exact Or.inl ⟨y, hy, rfl⟩
    | some i => exact Or.inr (mem_iUnion.mpr ⟨i, y, hy, rfl⟩)
  · rintro (⟨y, hy, rfl⟩ | h)
    · exact ⟨⟨none, y⟩, hy, rfl⟩
    · obtain ⟨i, y, hy, rfl⟩ := mem_iUnion.mp h
      exact ⟨⟨some i, y⟩, hy, rfl⟩

theorem evaluate_image_null
    (hd : Pairwise (fun i j => Disjoint (A i : Set X) (A j : Set X)))
    (hcover : Dense (⋃ i, (A i : Set X)))
    (hrare : ∀ n : Set X, IsMeagre n → IsNowhereDense n)
    (m : Set (Σ j, Fiber A j)) (hm : m ∈ (coprodEnhanced (fiberEnhanced A)).negligible) :
    evaluate A '' m ∈ (TM X).negligible := by
  change IsMeagre (evaluate A '' m)
  rw [evaluate_image]
  apply IsMeagre.union
  · exact (residual_meagre A hcover).mono (by
      rintro x ⟨y, hy, rfl⟩
      exact y.property)
  · exact meagre_iUnion_images A hd hcover hrare _ (fun i => hm (some i))

theorem evaluate_image_measurable
    (hd : Pairwise (fun i j => Disjoint (A i : Set X) (A j : Set X)))
    (hcover : Dense (⋃ i, (A i : Set X)))
    (hrare : ∀ n : Set X, IsMeagre n → IsNowhereDense n)
    (m : Set (Σ j, Fiber A j)) (hm : m ∈ (coprodEnhanced (fiberEnhanced A)).measurable) :
    evaluate A '' m ∈ (TM X).measurable := by
  rw [evaluate_image]
  apply (baire_iff _).2
  apply BaireMeasurableSet.union
  · apply (baire_iff _).1
    apply (TM X).negligibleMeasurable
    exact (residual_meagre A hcover).mono (by
      rintro x ⟨y, hy, rfl⟩
      exact y.property)
  · exact (baire_iff _).1 (measurable_iUnion_images A hd hcover hrare _
      (fun i => hm (some i)))

def totalPremap {Y Z : Type u} (E : Enhanced Y) (F : Enhanced Z) (f : Y → Z)
    (hm : ∀ s ∈ F.measurable, f ⁻¹' s ∈ E.measurable)
    (hn : ∀ s ∈ F.negligible, f ⁻¹' s ∈ E.negligible) : Premap E F := by
  refine ⟨fun x => some (f x), ?_, ?_, ?_⟩
  · have he : (partialDomain (fun x => some (f x)))ᶜ = ∅ := by
      ext x
      simp [partialDomain]
    rw [he]
    exact E.sigmaIdeal.1
  · intro s hs
    rw [Gelfand54.partialPreimage_some]
    exact hm s hs
  · intro s hs
    rw [Gelfand54.partialPreimage_some]
    exact hn s hs

/-- Topological gluing along a dense disjoint clopen family supplies the
literal coproduct isomorphism required by canonical strict localizability. -/
theorem strictlyLocalizable_TM_of_clopen_partition
    (hd : Pairwise (fun i j => Disjoint (A i : Set X) (A j : Set X)))
    (hcover : Dense (⋃ i, (A i : Set X)))
    (hrare : ∀ n : Set X, IsMeagre n → IsNowhereDense n)
    (hsigma : ∀ i, IsSigmaFiniteE (TM (A i))) : IsStrictlyLocalizable (TM X) := by
  let e := partitionEquiv A hd
  have heval : (e : (Σ j, Fiber A j) → X) = evaluate A := rfl
  let f : Premap (TM X) (coprodEnhanced (fiberEnhanced A)) :=
    totalPremap _ _ e.symm
      (by
        intro s hs
        rw [← e.image_eq_preimage_symm, heval]
        exact evaluate_image_measurable A hd hcover hrare s hs)
      (by
        intro s hs
        rw [← e.image_eq_preimage_symm, heval]
        exact evaluate_image_null A hd hcover hrare s hs)
  let g : Premap (coprodEnhanced (fiberEnhanced A)) (TM X) :=
    totalPremap _ _ e
      (by
        intro s hs j
        cases j with
        | none => exact mem_univ _
        | some i =>
          change (Subtype.val ⁻¹' s : Set (A i)) ∈ (TM (A i)).measurable
          exact (baire_iff _).2 (BaireMeasurableSet.preimage continuous_subtype_val
            (A i).isOpen.isOpenEmbedding_subtypeVal.isOpenMap ((baire_iff _).1 hs)))
      (by
        intro s hs j
        cases j with
        | none => exact mem_univ _
        | some i =>
          change IsMeagre (Subtype.val ⁻¹' s : Set (A i))
          exact IsMeagre.preimage_of_isOpenMap continuous_subtype_val
            (A i).isOpen.isOpenEmbedding_subtypeVal.isOpenMap hs)
  refine ⟨Option I, Fiber A, fiberEnhanced A, ?_, f, g, ?_, ?_⟩
  · intro j
    cases j with
    | none => exact nullEnhanced_sigmaFinite _
    | some i => exact hsigma i
  · funext x
    change some (e (e.symm x)) = some x
    rw [e.apply_symm_apply]
  · funext y
    change some (e.symm (e y)) = some y
    rw [e.symm_apply_apply]

end Gelfand54Gluing
end Gelfand54_part_13

section Gelfand54_part_14
/- Source module: Work.Gelfand272.SpaceProperties -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open GelfandVNA.Duality QAlgorithms.Papers.Independent.Support21.P20

universe u

namespace Gelfand272Space

variable {X : Type*} [TopologicalSpace X]

lemma coe_pseudocompl (a : Opens X) :
    ((aᶜ : Opens X) : Set X) = (closure (a : Set X))ᶜ := by
  rw [Opens.coe_compl_eq_interior_compl, _root_.interior_compl]

lemma closure_subset_of_compl_sup (a b : Opens X) (h : bᶜ ⊔ a = ⊤) :
    closure (b : Set X) ⊆ (a : Set X) := by
  intro x hx
  have hm : x ∈ (bᶜ ⊔ a : Opens X) := by rw [h]; trivial
  rcases Opens.mem_sup.mp hm with hb | ha
  · have hn : x ∈ (closure (b : Set X))ᶜ := by
      rw [← coe_pseudocompl b]
      exact hb
    exact False.elim (hn hx)
  · exact ha

theorem regularSpace_of_regularLocale (h : IsRegularLocale (Opens X)) : RegularSpace X := by
  apply RegularSpace.of_exists_mem_nhds_isClosed_subset
  intro x s hs
  obtain ⟨U, hUs, hU, hxU⟩ := mem_nhds_iff.mp hs
  let a : Opens X := ⟨U, hU⟩
  have hx : x ∈ a := hxU
  rw [h a] at hx
  obtain ⟨b, hb, hxb⟩ := Opens.mem_sSup.mp hx
  refine ⟨closure (b : Set X), ?_, isClosed_closure, ?_⟩
  · exact mem_of_superset (b.isOpen.mem_nhds hxb) subset_closure
  · exact (closure_subset_of_compl_sup a b hb).trans hUs

theorem extremallyDisconnected_of_opens (h : ∀ a : Opens X, aᶜ ⊔ aᶜᶜ = ⊤) :
    ExtremallyDisconnected X := by
  constructor
  intro U hU
  let a : Opens X := ⟨U, hU⟩
  have hle : ((aᶜᶜ : Opens X) : Set X) ⊆ closure (a : Set X) := by
    rw [Opens.coe_compl_eq_interior_compl, coe_pseudocompl a, compl_compl]
    exact interior_subset
  have heq : closure (a : Set X) = ((aᶜᶜ : Opens X) : Set X) :=
    subset_antisymm (closure_subset_of_compl_sup (aᶜᶜ) a (h a)) hle
  change IsOpen (closure (a : Set X))
  rw [heq]
  exact (aᶜᶜ).isOpen

theorem hstonean_compact (S : HStonean.{u}) : CompactSpace S.toTop := by
  apply isCompact_univ_iff.mp
  exact (Opens.isCompactElement_iff (⊤ : Opens S.toTop)).mp S.hyperstonean.1.1.1.1

theorem hstonean_regular (S : HStonean.{u}) : RegularSpace S.toTop :=
  regularSpace_of_regularLocale S.hyperstonean.1.1.2

theorem hstonean_t2 (S : HStonean.{u}) : T2Space S.toTop := by
  letI : RegularSpace S.toTop := hstonean_regular S
  infer_instance

theorem hstonean_extremallyDisconnected (S : HStonean.{u}) :
    ExtremallyDisconnected S.toTop :=
  extremallyDisconnected_of_opens S.hyperstonean.1.2

end Gelfand272Space
end Gelfand54_part_14

section Gelfand54_part_15
/- Source module: Work.Gelfand54.Compactness -/
set_option autoImplicit false
open Set Filter GelfandVNA.Duality
open QAlgorithms.Papers.Independent.Support21.P20
open scoped Topology

namespace Gelfand54
universe u

/-- The family of all closed subsets of a compact space is a compact class. -/
theorem isCompactClassOn_closed {X : Type u} [TopologicalSpace X] [CompactSpace X] :
    IsCompactClassOn (univ : Set X) {k | IsClosed k} := by
  intro T hT hfin
  exact isCompact_univ.nonempty_inter_sInter
    (fun a ha => hT ha) (fun a ha haf => hfin a haf ha)

/-- The compact-class part of Proposition 5.4, isolated from its substantive
hyperstonean meagre/nowhere-dense lemma. No conclusion about that lemma is assumed
for a hyperstonean object elsewhere in this file. -/
theorem compactEnhanced_TM_of_meagre_nowhereDense {X : Type u} [TopologicalSpace X]
    [CompactSpace X] [RegularSpace X]
    (hrare : ∀ n : Set X, IsMeagre n → IsNowhereDense n) :
    IsCompactEnhancedOn (TM X) univ := by
  refine ⟨{k | IsClosed k}, ?_, isCompactClassOn_closed, ?_⟩
  · intro k hk
    refine ⟨subset_univ k, (baire_iff k).2 ?_⟩
    simpa only [compl_compl] using hk.isOpen_compl.baireMeasurableSet.compl
  · intro s _ hs hsn
    change ∃ U : Set X, IsOpen U ∧ IsMeagre (symmDiff s U) at hs
    obtain ⟨U, hU, hn⟩ := hs
    have hUn : U.Nonempty := by
      by_contra h
      have he : U = ∅ := not_nonempty_iff_eq_empty.mp h
      apply hsn
      change IsMeagre s
      have he' : symmDiff s U = s := by
        rw [he]
        exact symmDiff_bot s
      rwa [he'] at hn
    let n := symmDiff s U
    have hnd : IsNowhereDense n := hrare n hn
    have hd : Dense (closure n)ᶜ :=
      (isClosed_isNowhereDense_iff_compl.mp ⟨isClosed_closure, hnd.closure⟩).2
    obtain ⟨x, hxU, hxn⟩ := hd.inter_open_nonempty U hU hUn
    have hxV : U \ closure n ∈ 𝓝 x :=
      (IsOpen.sdiff (show IsOpen U from hU) isClosed_closure).mem_nhds ⟨hxU, hxn⟩
    obtain ⟨k, hkx, hkc, hkV⟩ := exists_mem_nhds_isClosed_subset hxV
    refine ⟨k, hkc, ?_, ?_⟩
    · intro y hy
      obtain ⟨hyU, hyn⟩ := hkV hy
      by_contra hys
      apply hyn
      exact subset_closure (Or.inr ⟨hyU, hys⟩)
    · intro hkm
      have hki : interior k = ∅ := hkc.isNowhereDense_iff.mp (hrare k hkm)
      have hxki : x ∈ interior k := mem_interior_iff_mem_nhds.mpr hkx
      rw [hki] at hxki
      exact hxki

/-- Exact compactness conclusion for a canonical HStonean object, conditional
only on the as-yet separate meagre/nowhere-dense lemma from the source proof. -/
theorem hstonean_compactEnhanced_of_meagre_nowhereDense (S : HStonean.{u})
    (hrare : ∀ n : Set S.toTop, IsMeagre n → IsNowhereDense n) :
    IsCompactEnhancedOn (TM S.toTop) univ := by
  letI := Gelfand272Space.hstonean_compact S
  letI := Gelfand272Space.hstonean_regular S
  exact compactEnhanced_TM_of_meagre_nowhereDense hrare

end Gelfand54
end Gelfand54_part_15

section Gelfand54_part_16
/- Source module: Work.Gelfand54.NormalApproximation -/
set_option autoImplicit false
open Set TopologicalSpace GelfandVNA.Duality
open QAlgorithms.Papers.Independent.Support21.P20
open scoped NNReal

namespace Gelfand54
universe u

/-- Directed continuity approximates an open set by compact open subsets. -/
theorem exists_compact_open_valuation_approx (S : HStonean.{u})
    (ν : Opens S.toTop → ℝ≥0) (hν : IsPositiveContinuousValuation ν)
    (V : Opens S.toTop) (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ C : Opens S.toTop, IsCompactElement C ∧ C ≤ V ∧ ν V < ν C + ε := by
  let K : Set (Opens S.toTop) := {C | IsCompactElement C ∧ C ≤ V}
  have hbot : IsCompactElement (⊥ : Opens S.toTop) :=
    (Opens.isCompactElement_iff _).2 isCompact_empty
  have hKn : K.Nonempty := ⟨⊥, hbot, bot_le⟩
  have hKd : DirectedOn (· ≤ ·) K := by
    intro a ha b hb
    have hab : IsCompactElement (a ⊔ b) :=
      (Opens.isCompactElement_iff _).2
        (((Opens.isCompactElement_iff a).1 ha.1).union
          ((Opens.isCompactElement_iff b).1 hb.1))
    exact ⟨a ⊔ b, ⟨hab, sup_le ha.2 hb.2⟩, le_sup_left, le_sup_right⟩
  have hKsup : sSup K = V := (S.hyperstonean.1.1.1.2.2 V).symm
  have hKlub : IsLUB K V := hKsup ▸ isLUB_sSup K
  have hνlub : IsLUB (ν '' K) (ν V) := hν.2.2 K V hKn hKd hKlub
  by_cases hsmall : ν V < ε
  · refine ⟨⊥, hbot, bot_le, ?_⟩
    simpa only [hν.1.1, zero_add] using hsmall
  · have hle : ε ≤ ν V := le_of_not_gt hsmall
    have hlt : ν V - ε < ν V := tsub_lt_self (lt_of_lt_of_le hε hle) hε
    obtain ⟨z, ⟨C, hC, rfl⟩, hz, _⟩ := hνlub.exists_between hlt
    exact ⟨C, hC.1, hC.2, lt_add_of_tsub_lt_right hz⟩

/-- A finite positive normal valuation makes closed nowhere-dense sets
arbitrarily small inside clopen neighborhoods. This uses only the canonical
frame valuation and topology, without assuming a measure extension. -/
theorem exists_clopen_superset_valuation_lt (S : HStonean.{u})
    (ν : Opens S.toTop → ℝ≥0) (hν : IsPositiveNormalValuation ν)
    (F : Set S.toTop) (hF : IsClosed F) (hFn : IsNowhereDense F)
    (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ U : Opens S.toTop, IsClosed (U : Set S.toTop) ∧ F ⊆ U ∧ ν U < ε := by
  letI : T2Space S.toTop := Gelfand272Space.hstonean_t2 S
  let V : Opens S.toTop := ⟨Fᶜ, hF.isOpen_compl⟩
  have hVc : Vᶜ = ⊥ := by
    apply Opens.ext
    rw [Opens.coe_compl_eq_interior_compl]
    change interior (Fᶜ)ᶜ = ∅
    rw [compl_compl]
    exact hF.isNowhereDense_iff.mp hFn
  have hνV : ν V = ν ⊤ := by
    have h := hν.2 V
    rw [hVc, compl_bot] at h
    exact h.symm
  obtain ⟨C, hC, hCV, happrox⟩ :=
    exists_compact_open_valuation_approx S ν hν.1 V ε hε
  have hCc : IsClosed (C : Set S.toTop) :=
    ((Opens.isCompactElement_iff C).1 hC).isClosed
  let U : Opens S.toTop := Cᶜ
  have hUcoe : (U : Set S.toTop) = (C : Set S.toTop)ᶜ := by
    exact Opens.coe_compl_eq_interior_compl.trans hCc.isOpen_compl.interior_eq
  have hsup : C ⊔ U = ⊤ := by
    apply Opens.ext
    rw [Opens.coe_sup, hUcoe, Opens.coe_top, union_compl_self]
  have hinf : C ⊓ U = ⊥ := by
    apply Opens.ext
    rw [Opens.coe_inf, hUcoe, Opens.coe_bot, inter_compl_self]
  have hsum : ν C + ν U = ν ⊤ := by
    simpa only [hsup, hinf, hν.1.1.1, add_zero] using hν.1.1.2 C U
  refine ⟨U, ?_, ?_, ?_⟩
  · rw [hUcoe]
    exact C.isOpen.isClosed_compl
  · intro x hx
    rw [hUcoe]
    intro hxC
    exact hCV hxC hx
  · apply (add_lt_add_iff_left (ν C)).mp
    calc
      ν C + ν U = ν ⊤ := hsum
      _ = ν V := hνV.symm
      _ < ν C + ε := happrox

end Gelfand54
end Gelfand54_part_16

section Gelfand54_part_17
/- Source module: Work.Gelfand54.ValuationBounds -/
set_option autoImplicit false
open Set QAlgorithms.Papers.Independent.Support21.P20
open scoped NNReal

namespace Gelfand54
variable {L : Type*} [CompleteLattice L]
variable (ν : L → ℝ≥0) (hν : IsPositiveContinuousValuation ν)
include hν

theorem valuation_sup_le (a b : L) : ν (a ⊔ b) ≤ ν a + ν b := by
  calc
    ν (a ⊔ b) ≤ ν (a ⊔ b) + ν (a ⊓ b) := le_add_of_nonneg_right bot_le
    _ = ν a + ν b := (hν.1.2 a b).symm

theorem valuation_finset_sup_le {ι : Type*} (s : Finset ι) (f : ι → L) :
    ν (s.sup f) ≤ ∑ i ∈ s, ν (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [hν.1.1]
  | @insert i s hi ih =>
    rw [Finset.sup_insert, Finset.sum_insert hi]
    exact (valuation_sup_le ν hν _ _).trans (add_le_add le_rfl ih)

/-- Finite subadditivity and continuity at directed suprema control an
arbitrary union whenever all its finite sums have the same finite bound. -/
theorem valuation_iSup_le_of_finite_sums {ι : Type*} (f : ι → L) (c : ℝ≥0)
    (hc : ∀ s : Finset ι, ∑ i ∈ s, ν (f i) ≤ c) : ν (iSup f) ≤ c := by
  classical
  let D : Set L := Set.range (fun s : Finset ι => s.sup f)
  have hne : D.Nonempty := ⟨(∅ : Finset ι).sup f, ⟨∅, rfl⟩⟩
  have hdir : DirectedOn (· ≤ ·) D := by
    rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
    exact ⟨(s ∪ t).sup f, ⟨s ∪ t, rfl⟩,
      Finset.sup_mono Finset.subset_union_left,
      Finset.sup_mono Finset.subset_union_right⟩
  have hlub : IsLUB D (iSup f) := by
    constructor
    · rintro _ ⟨s, rfl⟩
      exact Finset.sup_le (fun i _ => le_iSup f i)
    · intro b hb
      apply iSup_le
      intro i
      have h := hb (Set.mem_range_self ({i} : Finset ι))
      simpa only [Finset.sup_singleton] using h
  apply (hν.2.2 D (iSup f) hne hdir hlub).2
  rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
  exact (valuation_finset_sup_le ν hν s f).trans (hc s)

end Gelfand54
end Gelfand54_part_17

section Gelfand54_part_18
/- Source module: Work.Gelfand54.MeagreRare -/
set_option autoImplicit false
open Set TopologicalSpace GelfandVNA.Duality
open QAlgorithms.Papers.Independent.Support21.P20
open scoped NNReal

namespace Gelfand54
universe u

/-- A normal valuation sees no open part in the closure of a meagre set.
Small clopen neighborhoods of the individual nowhere-dense pieces suffice;
no extension of the valuation to a measure is required. -/
theorem normal_zero_on_meagre_closure (S : HStonean.{u})
    (ν : Opens S.toTop → ℝ≥0) (hν : IsPositiveNormalValuation ν)
    (N : Set S.toTop) (hN : IsMeagre N) :
    ν ⟨interior (closure N), isOpen_interior⟩ = 0 := by
  classical
  let a : Opens S.toTop := ⟨interior (closure N), isOpen_interior⟩
  have heps (ε : ℝ≥0) (hε : 0 < ε) : ν a ≤ ε := by
    obtain ⟨T, hT, hTc, hsub⟩ := isMeagre_iff_countable_union_isNowhereDense.mp hN
    letI : Countable T := hTc
    obtain ⟨δ, hδpos, hδsum⟩ :=
      (Set.countable_univ : (Set.univ : Set T).Countable).exists_pos_forall_sum_le
        (show (0 : ℝ) < ε from hε)
    let d : T → ℝ≥0 := fun t => ⟨δ t, (hδpos t).le⟩
    have hd (t : T) : 0 < d t := hδpos t
    choose U hUclosed hUcover hUν using fun t : T =>
      exists_clopen_superset_valuation_lt S ν hν (closure t.val)
        isClosed_closure (hT t.val t.property).closure (d t) (hd t)
    let W : Opens S.toTop := iSup U
    have hNsub : N ⊆ (W : Set S.toTop) := by
      intro x hx
      obtain ⟨F, hFT, hxF⟩ := hsub hx
      exact Opens.mem_iSup.mpr ⟨⟨F, hFT⟩, hUcover ⟨F, hFT⟩ (subset_closure hxF)⟩
    have hfinite (s : Finset T) : ∑ i ∈ s, ν (U i) ≤ ε := by
      have h1 : ∑ i ∈ s, ν (U i) ≤ ∑ i ∈ s, d i :=
        Finset.sum_le_sum (fun i _ => (hUν i).le)
      have h2 : ∑ i ∈ s, d i ≤ ε := by
        change ((∑ i ∈ s, d i : ℝ≥0) : ℝ) ≤ (ε : ℝ)
        push_cast
        exact hδsum s (Set.subset_univ _)
      exact h1.trans h2
    have hle : a ≤ Wᶜᶜ := by
      change interior (closure N) ⊆ ((Wᶜᶜ : Opens S.toTop) : Set S.toTop)
      rw [Opens.coe_compl_eq_interior_compl, Gelfand272Space.coe_pseudocompl,
        compl_compl]
      exact interior_mono (closure_mono hNsub)
    calc
      ν a ≤ ν Wᶜᶜ := hν.1.2.1 hle
      _ = ν W := hν.2 W
      _ ≤ ε := valuation_iSup_le_of_finite_sums ν hν.1 U ε hfinite
  by_contra hnz
  have hpos : 0 < ν a := pos_iff_ne_zero.mpr hnz
  exact (not_le_of_gt (half_lt_self hpos)) (heps (ν a / 2) (half_pos hpos))

/-- In a hyperstonean space every meagre set is nowhere dense. -/
theorem meagre_isNowhereDense (S : HStonean.{u}) (N : Set S.toTop) (hN : IsMeagre N) :
    IsNowhereDense N := by
  change interior (closure N) = ∅
  by_contra hne
  let a : Opens S.toTop := ⟨interior (closure N), isOpen_interior⟩
  have ha : a ≠ ⊥ := by
    intro h
    exact hne (congrArg (fun U : Opens S.toTop => (U : Set S.toTop)) h)
  obtain ⟨ν, hν, hnz⟩ := S.hyperstonean.2 a ha
  exact hnz (normal_zero_on_meagre_closure S ν hν N hN)

end Gelfand54
end Gelfand54_part_18

section Gelfand54_part_19
/- Source module: Work.Gelfand54.CompactnessComplete -/
set_option autoImplicit false
open GelfandVNA.Duality QAlgorithms.Papers.Independent.Support21.P20

namespace Gelfand54
universe u

/-- The full compactness clause of the frozen Proposition 5.4. -/
theorem hstonean_compactEnhanced (S : HStonean.{u}) :
    IsCompactEnhancedOn (TM S.toTop) Set.univ :=
  hstonean_compactEnhanced_of_meagre_nowhereDense S (meagre_isNowhereDense S)

end Gelfand54
end Gelfand54_part_19

section Gelfand54_part_20
/- Source module: Work.Gelfand54.Final -/
set_option autoImplicit false
open Set TopologicalSpace GelfandVNA.Duality
open QAlgorithms.Papers.Independent.Support21.P20

namespace Gelfand54
universe u

theorem hstonean_strictlyLocalizable (S : HStonean.{u}) :
    IsStrictlyLocalizable (TM S.toTop) := by
  classical
  letI : CompactSpace S.toTop := Gelfand272Space.hstonean_compact S
  letI : T2Space S.toTop := Gelfand272Space.hstonean_t2 S
  letI : ExtremallyDisconnected S.toTop := Gelfand272Space.hstonean_extremallyDisconnected S
  have hB : HasFiniteValuationCover (Heyting.Regular (Opens S.toTop)) :=
    (Gelfand273Work.hyperstonean_iff_regular_localizable S.hyperstonean.1).mp S.hyperstonean
  obtain ⟨R, hdisj, hfaith, hsup⟩ := Gelfand54Partition.exists_disjoint_faithful_cover hB
  let A : R → Clopens S.toTop := fun a => Gelfand54Clopens.clopenRegularIso.symm a.val
  apply Gelfand54Gluing.strictlyLocalizable_TM_of_clopen_partition A
    (Gelfand54Clopens.regular_carriers_disjoint R hdisj)
    (Gelfand54Clopens.regular_carriers_dense R hsup)
    (meagre_isNowhereDense S)
  intro a
  obtain ⟨ν, hν, hf⟩ := (hfaith a.val a.property).2
  exact Gelfand54Quotient.regularCarrier_sigmaFinite a.val ν hν hf

end Gelfand54

open CategoryTheory
universe u

theorem solution :
    (∀ S : HStonean.{u}, IsCompactEnhancedOn (TM S.toTop) Set.univ ∧
      IsStrictlyLocalizable (TM S.toTop)) ∧
    ∀ {S T : HStonean.{u}} (f : S ⟶ T),
      IsPremap (TM S.toTop) (TM T.toTop) (fun x => some (f.1 x)) := by
  refine ⟨fun S => ⟨Gelfand54.hstonean_compactEnhanced S,
    Gelfand54.hstonean_strictlyLocalizable S⟩, ?_⟩
  intro S T f
  exact Gelfand54.hstonean_morphism f
end Gelfand54_part_20

#print axioms solution
