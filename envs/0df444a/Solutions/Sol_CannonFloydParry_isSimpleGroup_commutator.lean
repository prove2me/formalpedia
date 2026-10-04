-- Prove2me | solution 1 for CannonFloydParry.isSimpleGroup_commutator
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-16T12:16:02.622618+00:00
-- url     : https://prove2.me/submissions/31a51774-6d0e-48e9-9a43-e4a34d392b7c

import Theorems.Thm_CannonFloydParry_mem_commutator_iff
import Theorems.Thm_CannonFloydParry_center_eq_bot
import Theorems.Thm_CannonFloydParry_F_ne_bot
import Theorems.Thm_CannonFloydParry_exists_dyadic_interval_image_disjoint
import Theorems.Thm_CannonFloydParry_exists_conj_supp_subset_Icc
import Theorems.Thm_CannonFloydParry_mem_closure_commutator_supp_Icc
import Definitions.Def_CannonFloydParry
import Mathlib

open CannonFloydParry
open scoped commutatorElement

namespace CFPSimpleAux

/-! ### A commutator identity

If `u` commutes with `w` and with `⁅w, v⁻¹⁆`, then conjugating `u * v⁻¹` by `w` sees only the
`v⁻¹` factor.  This is the algebraic core of the simplicity argument: `u` will be a map whose
support is disjoint from the interval carrying `v` and `w`. -/

lemma comm_trick {G : Type*} [Group G] {u v w : G}
    (h1 : Commute u w) (h2 : Commute u (w * v⁻¹ * w⁻¹ * v)) :
    w * (u * v⁻¹) * w⁻¹ * (u * v⁻¹)⁻¹ = w * v⁻¹ * w⁻¹ * v := by
  have e1 : w * (u * v⁻¹) * w⁻¹ * (u * v⁻¹)⁻¹ = (w * u) * (v⁻¹ * w⁻¹ * v * u⁻¹) := by group
  rw [e1, ← h1.eq]
  have e2 : u * w * (v⁻¹ * w⁻¹ * v * u⁻¹) = u * (w * v⁻¹ * w⁻¹ * v) * u⁻¹ := by group
  rw [e2, h2.eq]
  group

/-! ### Moved-point sets

`supp f` is the set of points of `[0,1]` moved by `f`.  The lemmas below are the standard
bookkeeping: a map fixes everything outside its support, supports are inversion invariant,
supports of products and conjugates behave as expected, and maps with disjoint supports
commute. -/

lemma supp_subset_iff {f : UI ≃o UI} {s : Set ℝ} :
    supp f ⊆ s ↔ ∀ z : UI, (f z : ℝ) ≠ (z : ℝ) → (z : ℝ) ∈ s := by
  constructor
  · intro h z hz
    exact h ⟨z, rfl, hz⟩
  · rintro h t ⟨z, rfl, hz⟩
    exact h z hz

lemma fixed_of_supp_subset {f : UI ≃o UI} {s : Set ℝ} (h : supp f ⊆ s) {z : UI}
    (hz : (z : ℝ) ∉ s) : f z = z := by
  by_contra hne
  exact hz (supp_subset_iff.mp h z fun hc => hne (Subtype.ext hc))

lemma mem_supp_of_ne {f : UI ≃o UI} {s : Set ℝ} (h : supp f ⊆ s) {z : UI} (hz : f z ≠ z) :
    (z : ℝ) ∈ s :=
  supp_subset_iff.mp h z fun hc => hz (Subtype.ext hc)

lemma apply_mem_of_ne {f : UI ≃o UI} {s : Set ℝ} (h : supp f ⊆ s) {z : UI} (hz : f z ≠ z) :
    ((f z : UI) : ℝ) ∈ s := by
  refine h ⟨f z, rfl, ?_⟩
  intro hc
  exact hz (f.injective (Subtype.ext hc))

lemma inv_apply_eq_iff (f : UI ≃o UI) (z : UI) : f⁻¹ z = z ↔ f z = z := by
  constructor
  · intro h
    have := congrArg (fun y => f y) h
    simpa using this.symm
  · intro h
    have := congrArg (fun y => f⁻¹ y) h
    simpa using this.symm

lemma supp_inv (f : UI ≃o UI) : supp f⁻¹ = supp f := by
  ext t
  constructor
  · rintro ⟨z, rfl, hz⟩
    exact ⟨z, rfl, fun hc => hz (congrArg (fun y : UI => (y : ℝ))
      ((inv_apply_eq_iff f z).mpr (Subtype.ext hc)))⟩
  · rintro ⟨z, rfl, hz⟩
    exact ⟨z, rfl, fun hc => hz (congrArg (fun y : UI => (y : ℝ))
      ((inv_apply_eq_iff f z).mp (Subtype.ext hc)))⟩

lemma supp_mul_subset {f g : UI ≃o UI} {s : Set ℝ} (hf : supp f ⊆ s) (hg : supp g ⊆ s) :
    supp (f * g) ⊆ s := by
  rw [supp_subset_iff]
  intro z hz
  by_cases hgz : g z = z
  · refine mem_supp_of_ne hf (z := z) ?_
    intro hc
    apply hz
    show ((f (g z) : UI) : ℝ) = (z : ℝ)
    rw [hgz, hc]
  · exact mem_supp_of_ne hg hgz

lemma commute_of_supp_disjoint {f g : UI ≃o UI} {s t : Set ℝ}
    (hf : supp f ⊆ s) (hg : supp g ⊆ t) (hst : Disjoint s t) : Commute f g := by
  refine RelIso.ext fun z => ?_
  show f (g z) = g (f z)
  by_cases hgz : g z = z
  · rw [hgz]
    by_cases hfz : f z = z
    · rw [hfz, hgz]
    · have hfzs : ((f z : UI) : ℝ) ∈ s := apply_mem_of_ne hf hfz
      exact (fixed_of_supp_subset hg (Set.disjoint_left.mp hst hfzs)).symm
  · have hzt : (z : ℝ) ∈ t := mem_supp_of_ne hg hgz
    have hgzt : ((g z : UI) : ℝ) ∈ t := apply_mem_of_ne hg hgz
    have h1 : f (g z) = g z :=
      fixed_of_supp_subset hf (Set.disjoint_right.mp hst hgzt)
    have h2 : f z = z := fixed_of_supp_subset hf (Set.disjoint_right.mp hst hzt)
    rw [h1, h2]

lemma supp_conj_subset {f g : UI ≃o UI} {s t : Set ℝ} (hg : supp g ⊆ s)
    (hmap : ∀ z : UI, (z : ℝ) ∈ s → ((f z : UI) : ℝ) ∈ t) :
    supp (f * g * f⁻¹) ⊆ t := by
  rw [supp_subset_iff]
  intro z hz
  have hzy : f (f⁻¹ z) = z := by simp
  have hgy : g (f⁻¹ z) ≠ f⁻¹ z := by
    intro hc
    apply hz
    show ((f (g (f⁻¹ z)) : UI) : ℝ) = (z : ℝ)
    rw [hc, hzy]
  have hys : ((f⁻¹ z : UI) : ℝ) ∈ s := mem_supp_of_ne hg hgy
  have hfin := hmap _ hys
  rwa [hzy] at hfin

/-- The ambient group of order isomorphisms, reached from `[F,F]`. -/
def iota : (commutator CannonFloydParry.F) →* (UI ≃o UI) :=
  (CannonFloydParry.F.subtype).comp (commutator CannonFloydParry.F).subtype

lemma iota_injective : Function.Injective iota := by
  intro x y h
  exact Subtype.ext (Subtype.ext h)

end CFPSimpleAux

open CFPSimpleAux

theorem solution : IsSimpleGroup (commutator CannonFloydParry.F) := by
  -- `F` is nontrivial, so `[F,F]` is nontrivial: were it trivial, `F` would be abelian and its
  -- centre would be all of `F`, contradicting `center_eq_bot`.
  haveI hFnt : Nontrivial (CannonFloydParry.F) :=
    (Subgroup.nontrivial_iff_ne_bot CannonFloydParry.F).mpr CannonFloydParry.F_ne_bot
  have hcne : commutator (CannonFloydParry.F) ≠ ⊥ := by
    intro hc
    have habel : ∀ x y : (CannonFloydParry.F), x * y = y * x := by
      intro x y
      have h1 : ⁅x, y⁆ ∈ commutator (CannonFloydParry.F) :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
      rw [hc, Subgroup.mem_bot] at h1
      exact commutatorElement_eq_one_iff_mul_comm.mp h1
    have htop : Subgroup.center (CannonFloydParry.F) = ⊤ := by
      rw [Subgroup.eq_top_iff']
      intro x
      rw [Subgroup.mem_center_iff]
      intro y
      exact habel y x
    rw [CannonFloydParry.center_eq_bot] at htop
    have hall : ∀ z : (CannonFloydParry.F), z = 1 := by
      intro z
      have hz : z ∈ (⊥ : Subgroup (CannonFloydParry.F)) := by
        rw [htop]; trivial
      simpa [Subgroup.mem_bot] using hz
    obtain ⟨p, q, hpq⟩ := exists_pair_ne (CannonFloydParry.F)
    exact hpq ((hall p).trans (hall q).symm)
  haveI hntc : Nontrivial (commutator (CannonFloydParry.F)) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hcne
  refine ⟨fun N hN => ?_⟩
  by_cases hNbot : N = ⊥
  · exact Or.inl hNbot
  refine Or.inr ?_
  haveI hNnt : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hNbot
  obtain ⟨⟨f, hfN⟩, hfne⟩ := exists_ne (1 : N)
  have hf1 : f ≠ 1 := fun h => hfne (Subtype.ext h)
  have hf₀F : iota f ∈ CannonFloydParry.F := (f : CannonFloydParry.F).2
  have hf₀1 : iota f ≠ 1 := fun h => hf1 (Subtype.ext (Subtype.ext h))
  obtain ⟨a, b, ha0, hab, hb1, hdya, hdyb, hdisj⟩ :=
    CannonFloydParry.exists_dyadic_interval_image_disjoint hf₀F hf₀1
  -- the image of `N` in the ambient group of order isomorphisms of `[0,1]`
  have hmemK : ∀ x : (commutator (CannonFloydParry.F)), iota x ∈ N.map iota ↔ x ∈ N :=
    fun x => Subgroup.mem_map_iff_mem iota_injective
  -- an element of `F` supported in `[a,b] ⊆ (0,1)` is trivial near `0` and near `1`,
  -- hence lies in `[F,F]` by Theorem 4.1
  have hpromote : ∀ (x : UI ≃o UI), x ∈ CannonFloydParry.F → supp x ⊆ Set.Icc a b →
      ∃ y : (commutator (CannonFloydParry.F)), iota y = x := by
    intro x hx hs
    have h0 : TrivialNearZero x := by
      refine ⟨a, ha0, fun z hz => ?_⟩
      have hnot : (z : ℝ) ∉ Set.Icc a b := fun hcc => absurd hcc.1 (not_le.mpr hz)
      exact congrArg (fun y : UI => (y : ℝ)) (fixed_of_supp_subset hs hnot)
    have h1 : TrivialNearOne x := by
      refine ⟨1 - b, by linarith, fun z hz => ?_⟩
      have hnot : (z : ℝ) ∉ Set.Icc a b := by
        intro hcc
        have hzb : (z : ℝ) ≤ b := hcc.2
        linarith
      exact congrArg (fun y : UI => (y : ℝ)) (fixed_of_supp_subset hs hnot)
    exact ⟨⟨⟨x, hx⟩, (CannonFloydParry.mem_commutator_iff ⟨x, hx⟩).mpr ⟨h0, h1⟩⟩, rfl⟩
  -- Step 1: commutators of elements supported in `[a,b]` land in `N`
  have hkey : ∀ g h : UI ≃o UI, g ∈ CannonFloydParry.F → h ∈ CannonFloydParry.F →
      supp g ⊆ Set.Icc a b → supp h ⊆ Set.Icc a b → h * g⁻¹ * h⁻¹ * g ∈ N.map iota := by
    intro g h hgF hhF hgs hhs
    obtain ⟨ĝ, hĝ⟩ := hpromote g hgF hgs
    obtain ⟨ĥ, hĥ⟩ := hpromote h hhF hhs
    have hu : ⁅f, ĝ⁆ ∈ N := by
      have h1 : ĝ * f⁻¹ * ĝ⁻¹ ∈ N := hN.conj_mem _ (N.inv_mem hfN) ĝ
      have h2 : f * (ĝ * f⁻¹ * ĝ⁻¹) ∈ N := N.mul_mem hfN h1
      have h3 : f * (ĝ * f⁻¹ * ĝ⁻¹) = ⁅f, ĝ⁆ := by
        rw [commutatorElement_def]; group
      rwa [h3] at h2
    have hv : ⁅ĥ, ⁅f, ĝ⁆⁆ ∈ N := by
      have h1 : ĥ * ⁅f, ĝ⁆ * ĥ⁻¹ ∈ N := hN.conj_mem _ hu ĥ
      have h2 : (ĥ * ⁅f, ĝ⁆ * ĥ⁻¹) * (⁅f, ĝ⁆)⁻¹ ∈ N := N.mul_mem h1 (N.inv_mem hu)
      have h3 : (ĥ * ⁅f, ĝ⁆ * ĥ⁻¹) * (⁅f, ĝ⁆)⁻¹ = ⁅ĥ, ⁅f, ĝ⁆⁆ :=
        (commutatorElement_def ĥ ⁅f, ĝ⁆).symm
      rwa [h3] at h2
    have himg : iota ⁅ĥ, ⁅f, ĝ⁆⁆ = ⁅h, ⁅iota f, g⁆⁆ := by
      rw [map_commutatorElement, map_commutatorElement, hĝ, hĥ]
    -- supports: the conjugate of `g` by `f` lives off `[a,b]`
    have hbar : supp (iota f * g * (iota f)⁻¹) ⊆ (Set.Icc a b)ᶜ :=
      supp_conj_subset hgs fun z hz => hdisj z hz
    have hc1 : Commute (iota f * g * (iota f)⁻¹) h :=
      commute_of_supp_disjoint hbar hhs disjoint_compl_left
    have hXs : supp (h * g⁻¹ * h⁻¹ * g) ⊆ Set.Icc a b := by
      refine supp_mul_subset (supp_mul_subset (supp_mul_subset hhs ?_) ?_) hgs
      · rw [supp_inv]; exact hgs
      · rw [supp_inv]; exact hhs
    have hc2 : Commute (iota f * g * (iota f)⁻¹) (h * g⁻¹ * h⁻¹ * g) :=
      commute_of_supp_disjoint hbar hXs disjoint_compl_left
    have he1 : ⁅iota f, g⁆ = (iota f * g * (iota f)⁻¹) * g⁻¹ :=
      commutatorElement_def _ _
    have hident : ⁅h, ⁅iota f, g⁆⁆ = h * g⁻¹ * h⁻¹ * g := by
      rw [he1, commutatorElement_def]
      exact comm_trick hc1 hc2
    rw [hident] at himg
    rw [← himg]
    exact (hmemK _).mpr hv
  have hkey' : ∀ g h : UI ≃o UI, g ∈ CannonFloydParry.F → h ∈ CannonFloydParry.F →
      supp g ⊆ Set.Icc a b → supp h ⊆ Set.Icc a b → g * h * g⁻¹ * h⁻¹ ∈ N.map iota := by
    intro g h hgF hhF hgs hhs
    have hh : supp h⁻¹ ⊆ Set.Icc a b := by rw [supp_inv]; exact hhs
    have hres := hkey h⁻¹ g (CannonFloydParry.F.inv_mem hhF) hgF hh hgs
    rwa [inv_inv] at hres
  -- Step 2: every element of `[F,F]` lies in `N`
  rw [Subgroup.eq_top_iff']
  intro w
  have hwF : iota w ∈ CannonFloydParry.F := (w : CannonFloydParry.F).2
  have hw01 : TrivialNearZero (iota w) ∧ TrivialNearOne (iota w) :=
    (CannonFloydParry.mem_commutator_iff (w : CannonFloydParry.F)).mp w.2
  obtain ⟨φ, hφF, hφ0, hφ1, c, d, hac, hcd, hdb, hsupp⟩ :=
    CannonFloydParry.exists_conj_supp_subset_Icc ha0 hab hb1 hdya hdyb hwF hw01.1 hw01.2
  have hsupp' : supp (φ * iota w * φ⁻¹) ⊆ Set.Icc c d := by
    rw [supp_subset_iff]
    intro z hz
    exact hsupp z hz
  have huF : φ * iota w * φ⁻¹ ∈ CannonFloydParry.F :=
    CannonFloydParry.F.mul_mem (CannonFloydParry.F.mul_mem hφF hwF)
      (CannonFloydParry.F.inv_mem hφF)
  have hu := CannonFloydParry.mem_closure_commutator_supp_Icc ha0 hac hcd hdb hb1 hdya hdyb
    huF hsupp'
  have hsub : Subgroup.closure {x : UI ≃o UI | ∃ g h : UI ≃o UI,
      g ∈ CannonFloydParry.F ∧ h ∈ CannonFloydParry.F ∧ supp g ⊆ Set.Icc a b ∧
        supp h ⊆ Set.Icc a b ∧ x = g * h * g⁻¹ * h⁻¹} ≤ N.map iota := by
    rw [Subgroup.closure_le]
    rintro x ⟨g, h, hgF, hhF, hgs, hhs, rfl⟩
    exact hkey' g h hgF hhF hgs hhs
  have huK : φ * iota w * φ⁻¹ ∈ N.map iota := hsub hu
  have hφc : (⟨φ, hφF⟩ : CannonFloydParry.F) ∈ commutator (CannonFloydParry.F) :=
    (CannonFloydParry.mem_commutator_iff ⟨φ, hφF⟩).mpr ⟨hφ0, hφ1⟩
  have himg2 : iota ((⟨⟨φ, hφF⟩, hφc⟩ : (commutator (CannonFloydParry.F))) * w *
      (⟨⟨φ, hφF⟩, hφc⟩ : (commutator (CannonFloydParry.F)))⁻¹) = φ * iota w * φ⁻¹ := by
    rw [map_mul, map_mul, map_inv]
    rfl
  rw [← himg2] at huK
  have hmem := (hmemK _).mp huK
  have h2 := hN.conj_mem _ hmem (⟨⟨φ, hφF⟩, hφc⟩ : (commutator (CannonFloydParry.F)))⁻¹
  have h3 : (⟨⟨φ, hφF⟩, hφc⟩ : (commutator (CannonFloydParry.F)))⁻¹ *
      ((⟨⟨φ, hφF⟩, hφc⟩ : (commutator (CannonFloydParry.F))) * w *
        (⟨⟨φ, hφF⟩, hφc⟩ : (commutator (CannonFloydParry.F)))⁻¹) *
      ((⟨⟨φ, hφF⟩, hφc⟩ : (commutator (CannonFloydParry.F)))⁻¹)⁻¹ = w := by group
  rwa [h3] at h2
