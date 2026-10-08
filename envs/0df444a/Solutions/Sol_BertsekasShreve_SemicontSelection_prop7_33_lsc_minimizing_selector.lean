-- Prove2me | solution 1 for BertsekasShreve.SemicontSelection.prop7_33_lsc_minimizing_selector
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T04:13:52.117642+00:00
-- url     : https://prove2.me/submissions/49ba5354-8029-4dd1-99b8-691d37130a5e

import Mathlib

set_option autoImplicit false

namespace Caa51840

open Classical in
/-- Prefixes of the lexicographically least branch of `G ⊆ ℕ → Bool`. -/
noncomputable def pfx (G : Set (ℕ → Bool)) : ℕ → (ℕ → Bool)
  | 0 => fun _ => false
  | n + 1 => Function.update (pfx G n) n
      (if ∃ z ∈ G, (∀ i < n, z i = pfx G n i) ∧ z n = false then false else true)

noncomputable def lexb (G : Set (ℕ → Bool)) (n : ℕ) : Bool := pfx G (n + 1) n

theorem pfx_eq (G : Set (ℕ → Bool)) : ∀ n, ∀ i < n, pfx G n i = lexb G i := by
  intro n
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
    · have hne : i ≠ n := by omega
      simp only [pfx, Function.update_of_ne hne]
      exact ih i h
    · subst h; rfl

theorem lexb_false_iff (G : Set (ℕ → Bool)) (n : ℕ) :
    lexb G n = false ↔ ∃ z ∈ G, (∀ i < n, z i = lexb G i) ∧ z n = false := by
  have key : ∀ z : ℕ → Bool, (∀ i < n, z i = pfx G n i) ↔ (∀ i < n, z i = lexb G i) := by
    intro z
    constructor
    · intro h i hi; rw [h i hi, pfx_eq G n i hi]
    · intro h i hi; rw [h i hi, pfx_eq G n i hi]
  rw [show lexb G n = pfx G (n + 1) n from rfl]
  simp only [pfx, Function.update_self]
  classical
  by_cases h : ∃ z ∈ G, (∀ i < n, z i = pfx G n i) ∧ z n = false
  · rw [if_pos h]
    simp only [true_iff]
    obtain ⟨z, hz, h1, h2⟩ := h
    exact ⟨z, hz, (key z).mp h1, h2⟩
  · rw [if_neg h]
    simp only [Bool.true_eq_false, false_iff]
    rintro ⟨z, hz, h1, h2⟩
    exact h ⟨z, hz, (key z).mpr h1, h2⟩

theorem lexb_prefix (G : Set (ℕ → Bool)) (hG : G.Nonempty) :
    ∀ n, ∃ z ∈ G, ∀ i < n, z i = lexb G i := by
  intro n
  induction n with
  | zero => obtain ⟨z, hz⟩ := hG; exact ⟨z, hz, fun i hi => by omega⟩
  | succ n ih =>
    obtain ⟨z, hz, hzn⟩ := ih
    cases hb : lexb G n with
    | false =>
      obtain ⟨z', hz', h1, h2⟩ := (lexb_false_iff G n).mp hb
      refine ⟨z', hz', fun i hi => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
      · exact h1 i h
      · subst h; rw [h2, hb]
    | true =>
      refine ⟨z, hz, fun i hi => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
      · exact hzn i h
      · subst h
        cases hzi : z i with
        | true => exact hb.symm
        | false =>
          have : lexb G i = false := (lexb_false_iff G i).mpr ⟨z, hz, hzn, hzi⟩
          rw [hb] at this; exact absurd this (by decide)

theorem lexb_mem (G : Set (ℕ → Bool)) (hG : G.Nonempty) (hc : IsClosed G) :
    lexb G ∈ G := by
  choose z hz hzp using lexb_prefix G hG
  apply hc.mem_of_tendsto (f := z) (b := Filter.atTop)
  · rw [tendsto_pi_nhds]
    intro i
    apply tendsto_const_nhds.congr'
    filter_upwards [Filter.eventually_gt_atTop i] with n hn
    exact (hzp n i hn).symm
  · exact Filter.Eventually.of_forall hz

/-- Measurable selection from closed-valued maps into a continuous image of Cantor space. -/
theorem cantor_select {S Y : Type*} [MeasurableSpace S] [TopologicalSpace Y] [T2Space Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (c : (ℕ → Bool) → Y) (hc : Continuous c)
    (A : S → Set Y) (hA : ∀ x, IsClosed (A x)) (hne : ∀ x, ∃ z, c z ∈ A x)
    (hH : ∀ K : Set Y, IsClosed K → MeasurableSet {x | (A x ∩ K).Nonempty}) :
    ∃ φ : S → Y, Measurable φ ∧ ∀ x, φ x ∈ A x := by
  let G : S → Set (ℕ → Bool) := fun x => c ⁻¹' A x
  let b : S → ℕ → Bool := fun x => lexb (G x)
  have hGne : ∀ x, (G x).Nonempty := fun x => hne x
  have hGc : ∀ x, IsClosed (G x) := fun x => (hA x).preimage hc
  -- hit sets for closed subsets of Cantor space
  have hH' : ∀ C : Set (ℕ → Bool), IsClosed C →
      MeasurableSet {x | ∃ z ∈ G x, z ∈ C} := by
    intro C hC
    have hK : IsClosed (c '' C) := (hC.isCompact.image hc).isClosed
    convert hH _ hK using 1
    ext x
    simp only [Set.mem_setOf_eq, G, Set.mem_preimage]
    constructor
    · rintro ⟨z, hz, hzC⟩; exact ⟨c z, hz, z, hzC, rfl⟩
    · rintro ⟨y, hy, z, hzC, rfl⟩; exact ⟨z, hy, hzC⟩
  have hcoord : ∀ n, Measurable (fun x => b x n) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      let π : S → (Fin n → Bool) := fun x i => b x i
      have hπ : Measurable π := measurable_pi_lambda _ (fun i => ih i i.2)
      have hset : {x | b x n = false} =
          ⋃ t : Fin n → Bool, (π ⁻¹' {t} ∩
            {x | ∃ z ∈ G x, z ∈ {z : ℕ → Bool | (∀ i : Fin n, z i = t i) ∧ z n = false}}) := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage,
          Set.mem_singleton_iff, b]
        rw [lexb_false_iff]
        constructor
        · rintro ⟨z, hz, h1, h2⟩
          refine ⟨π x, rfl, z, hz, fun i => h1 i i.2, h2⟩
        · rintro ⟨t, ht, z, hz, h1, h2⟩
          refine ⟨z, hz, fun i hi => ?_, h2⟩
          have := h1 ⟨i, hi⟩
          rw [this, ← ht]
      have hmeas : MeasurableSet {x | b x n = false} := by
        rw [hset]
        refine MeasurableSet.iUnion fun t => (hπ (measurableSet_singleton t)).inter (hH' _ ?_)
        have hs : {z : ℕ → Bool | (∀ i : Fin n, z i = t i) ∧ z n = false} =
            (⋂ i : Fin n, {z : ℕ → Bool | z i = t i}) ∩ {z | z n = false} := by
          ext z; simp
        rw [hs]
        exact (isClosed_iInter fun i => isClosed_eq (continuous_apply _) continuous_const).inter
          (isClosed_eq (continuous_apply n) continuous_const)
      apply measurable_to_countable'
      intro v
      cases v with
      | false => exact hmeas
      | true =>
        have : (fun x => b x n) ⁻¹' {true} = {x | b x n = false}ᶜ := by
          ext x; simp
        rw [this]; exact hmeas.compl
  have hb : Measurable b := measurable_pi_lambda _ hcoord
  refine ⟨fun x => c (b x), hc.measurable.comp hb, fun x => ?_⟩
  exact lexb_mem (G x) (hGne x) (hGc x)

section
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem section_lsc (E : Set (X × Y)) (f : X × Y → EReal) (hf : LowerSemicontinuousOn f E)
    (x : X) : LowerSemicontinuousOn (fun y => f (x, y)) {y | (x, y) ∈ E} := by
  intro y hy c hc
  have h1 := hf (x, y) hy c hc
  have ht : Filter.Tendsto (fun y' : Y => (x, y')) (nhdsWithin y {y | (x, y) ∈ E})
      (nhdsWithin (x, y) E) :=
    (Continuous.prodMk_right x).continuousWithinAt.tendsto_nhdsWithin (fun y' hy' => hy')
  exact ht.eventually h1

theorem section_closed (E : Set (X × Y)) (hE : IsClosed E) (x : X) :
    IsClosed {y | (x, y) ∈ E} := hE.preimage (Continuous.prodMk_right x)

theorem attain [CompactSpace Y] (E : Set (X × Y)) (hE : IsClosed E) (f : X × Y → EReal)
    (hf : LowerSemicontinuousOn f E) (x : X) (y₀ : Y) (h₀ : (x, y₀) ∈ E) :
    ∃ y, (x, y) ∈ E ∧ f (x, y) = ⨅ (y : Y) (_ : (x, y) ∈ E), f (x, y) := by
  obtain ⟨a, ha, hmin⟩ := (section_lsc E f hf x).exists_isMinOn ⟨y₀, h₀⟩
    (section_closed E hE x).isCompact
  refine ⟨a, ha, le_antisymm (le_iInf₂ fun y hy => hmin hy) (iInf₂_le a ha)⟩

theorem inf_lsc [CompactSpace Y] (E : Set (X × Y)) (hE : IsClosed E) (f : X × Y → EReal)
    (hf : LowerSemicontinuousOn f E) :
    LowerSemicontinuous (fun x => ⨅ (y : Y) (_ : (x, y) ∈ E), f (x, y)) := by
  intro x₀ c hc
  obtain ⟨c', hcc', hc'⟩ := exists_between hc
  have hP : ∀ y ∈ (Set.univ : Set Y),
      ∀ᶠ z : X × Y in nhds (x₀, y), (z.1, z.2) ∈ E → c' < f (z.1, z.2) := by
    intro y _
    by_cases hy : (x₀, y) ∈ E
    · have h1 : c' < f (x₀, y) := lt_of_lt_of_le hc' (iInf₂_le y hy)
      have h2 := hf (x₀, y) hy c' h1
      rw [eventually_nhdsWithin_iff] at h2
      simpa using h2
    · filter_upwards [hE.isOpen_compl.mem_nhds hy] with z hz hzE
      exact absurd hzE hz
  have := IsCompact.eventually_forall_of_forall_eventually (x₀ := x₀)
    (P := fun x y => (x, y) ∈ E → c' < f (x, y)) isCompact_univ hP
  filter_upwards [this] with x hx
  exact lt_of_lt_of_le hcc' (le_iInf₂ fun y hy => (hx y (Set.mem_univ y) hy).le)

end

end Caa51840

open TopologicalSpace in
theorem solution {X Y : Type*}
    [TopologicalSpace X] [MetrizableSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MetrizableSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (D : Set (X × Y)) (hD : IsClosed D) (f : X × Y → EReal) (hf : LowerSemicontinuousOn f D) :
    IsClosed (Prod.fst '' D) ∧
    LowerSemicontinuousOn (fun x => ⨅ (y : Y) (_ : (x, y) ∈ D), f (x, y)) (Prod.fst '' D) ∧
    ∃ φ : (Prod.fst '' D) → Y, Measurable φ ∧
      ∀ x : (Prod.fst '' D), ((x : X), φ x) ∈ D ∧
        f ((x : X), φ x) = ⨅ (y : Y) (_ : ((x : X), y) ∈ D), f ((x : X), y) := by
  set g : X → EReal := fun x => ⨅ (y : Y) (_ : (x, y) ∈ D), f (x, y) with hg_def
  have hg : LowerSemicontinuous g := Caa51840.inf_lsc D hD f hf
  refine ⟨isClosedMap_fst_of_compactSpace D hD, hg.lowerSemicontinuousOn _, ?_⟩
  rcases isEmpty_or_nonempty Y with hY | hY
  · haveI : IsEmpty (Prod.fst '' D) := ⟨fun x => isEmptyElim x.2.choose.2⟩
    exact ⟨fun x => isEmptyElim x, Subsingleton.measurable, fun x => isEmptyElim x⟩
  letI : MetricSpace Y := metrizableSpaceMetric Y
  obtain ⟨c, hc, hcs⟩ := exists_nat_bool_continuous_surjective_of_compact Y
  let A : (Prod.fst '' D) → Set Y := fun x => {y | ((x : X), y) ∈ D ∧ f ((x : X), y) ≤ g x}
  have hA : ∀ x, IsClosed (A x) := by
    intro x
    obtain ⟨v, hv, hveq⟩ := (lowerSemicontinuousOn_iff_preimage_Iic.mp
      (Caa51840.section_lsc D f hf (x : X))) (g x)
    have : A x = {y | ((x : X), y) ∈ D} ∩ v := by
      rw [← hveq]; rfl
    rw [this]; exact (Caa51840.section_closed D hD _).inter hv
  have hAne : ∀ x, (A x).Nonempty := by
    intro x
    obtain ⟨⟨x', y₀⟩, h₀, hx'⟩ := x.2
    simp only at hx'
    obtain ⟨y, hy, hyeq⟩ := Caa51840.attain D hD f hf (x : X) y₀ (hx' ▸ h₀)
    exact ⟨y, hy, hyeq.le⟩
  have hH : ∀ K : Set Y, IsClosed K → MeasurableSet {x | (A x ∩ K).Nonempty} := by
    intro K hK
    let E : Set (X × Y) := D ∩ {p | p.2 ∈ K}
    have hE : IsClosed E := hD.inter (hK.preimage continuous_snd)
    have hfE : LowerSemicontinuousOn f E := hf.mono Set.inter_subset_left
    let gE : X → EReal := fun x => ⨅ (y : Y) (_ : (x, y) ∈ E), f (x, y)
    have hgE : LowerSemicontinuous gE := Caa51840.inf_lsc E hE f hfE
    have hM : MeasurableSet (Prod.fst '' E ∩ {x | gE x ≤ g x}) :=
      (isClosedMap_fst_of_compactSpace E hE).measurableSet.inter
        (measurableSet_le hgE.measurable hg.measurable)
    convert measurable_subtype_coe hM using 1
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_inter_iff, Set.mem_image]
    constructor
    · rintro ⟨y, ⟨hyD, hyle⟩, hyK⟩
      refine ⟨⟨((x : X), y), ⟨hyD, hyK⟩, rfl⟩, le_trans (iInf₂_le y ⟨hyD, hyK⟩) hyle⟩
    · rintro ⟨⟨⟨x', y₀⟩, h₀, hx'⟩, hle⟩
      simp only at hx'
      obtain ⟨y, hy, hyeq⟩ := Caa51840.attain E hE f hfE (x : X) y₀ (hx' ▸ h₀)
      exact ⟨y, ⟨hy.1, hyeq.trans_le hle⟩, hy.2⟩
  obtain ⟨φ, hφ, hφA⟩ := Caa51840.cantor_select c hc A hA
    (fun x => by obtain ⟨y, hy⟩ := hAne x; obtain ⟨z, rfl⟩ := hcs y; exact ⟨z, hy⟩) hH
  refine ⟨φ, hφ, fun x => ⟨(hφA x).1, le_antisymm (hφA x).2 (iInf₂_le (φ x) (hφA x).1)⟩⟩
