-- Prove2me | solution 1 for BertsekasShreve.SemicontSelection.prop7_34_usc_epsilon_selector
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T01:03:29.510161+00:00
-- url     : https://prove2.me/submissions/a4815d23-7fd9-4882-b734-1a752afd2344

import Mathlib



namespace BertsekasShreve.SemicontSelection

open TopologicalSpace Filter Topology

theorem p734_core {X Y : Type*}
    [TopologicalSpace X] [MetrizableSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MetrizableSpace Y] [SeparableSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (D : Set (X × Y)) (hD : IsOpen D) (f : X × Y → EReal) (hf : UpperSemicontinuousOn f D) :
    IsOpen (Prod.fst '' D) ∧
    UpperSemicontinuousOn (fun x => ⨅ (y : Y) (_ : (x, y) ∈ D), f (x, y)) (Prod.fst '' D) ∧
    ∀ ε : ℝ, 0 < ε → ∃ φ : (Prod.fst '' D) → Y, Measurable φ ∧
      ∀ x : (Prod.fst '' D), ((x : X), φ x) ∈ D ∧
        ((⨅ (y : Y) (_ : ((x : X), y) ∈ D), f ((x : X), y)) ≠ ⊥ →
          f ((x : X), φ x) ≤ (⨅ (y : Y) (_ : ((x : X), y) ∈ D), f ((x : X), y)) + (ε : EReal)) ∧
        ((⨅ (y : Y) (_ : ((x : X), y) ∈ D), f ((x : X), y)) = ⊥ →
          f ((x : X), φ x) ≤ ((-1 / ε : ℝ) : EReal)) := by
  classical
  have husc : ∀ z ∈ D, ∀ c, f z < c → ∀ᶠ z' in 𝓝 z, z' ∈ D ∧ f z' < c := by
    intro z hz c hc
    have := hf z hz c hc
    rw [hD.nhdsWithin_eq hz] at this
    exact Filter.Eventually.and (hD.mem_nhds hz) this
  set F : X → EReal := fun x => ⨅ (y : Y) (_ : (x, y) ∈ D), f (x, y) with hFdef
  have hFlt : ∀ x c, F x < c → ∃ y, (x, y) ∈ D ∧ f (x, y) < c := by
    intro x c hc
    simp only [hFdef, iInf_lt_iff] at hc
    obtain ⟨y, hyD, hy⟩ := hc
    exact ⟨y, hyD, hy⟩
  have hFusc : UpperSemicontinuousOn F (Prod.fst '' D) := by
    intro x _ c hc
    obtain ⟨y, hyD, hy⟩ := hFlt x c hc
    have hev := husc _ hyD c hy
    have hev2 : ∀ᶠ x' in 𝓝 x, (x', y) ∈ D ∧ f (x', y) < c :=
      ((by fun_prop : Continuous fun x' : X => (x', y)).tendsto x).eventually hev
    apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
    filter_upwards [hev2] with x' hx'
    exact lt_of_le_of_lt (iInf₂_le y hx'.1) hx'.2
  refine ⟨isOpenMap_fst D hD, hFusc, ?_⟩
  intro ε hε
  rcases isEmpty_or_nonempty Y with hY | hY
  · have hS : IsEmpty (Prod.fst '' D) := ⟨fun ⟨x, ⟨⟨_, y⟩, _, _⟩⟩ => hY.false y⟩
    refine ⟨fun x => isEmptyElim x, fun s _ => ?_, fun x => isEmptyElim x⟩
    have : (fun x : (Prod.fst '' D) => (isEmptyElim x : Y)) ⁻¹' s = ∅ := Set.eq_empty_of_isEmpty _
    rw [this]; exact MeasurableSet.empty
  let yk := denseSeq Y
  have hyk : DenseRange yk := denseRange_denseSeq Y
  have hfind : ∀ x y c, (x, y) ∈ D → f (x, y) < c → ∃ k, (x, yk k) ∈ D ∧ f (x, yk k) < c := by
    intro x y c hD' hlt
    have hev := husc _ hD' c hlt
    have hev2 : ∀ᶠ y' in 𝓝 y, (x, y') ∈ D ∧ f (x, y') < c :=
      ((by fun_prop : Continuous fun y' : Y => (x, y')).tendsto y).eventually hev
    obtain ⟨U, hUsub, hUo, hyU⟩ := mem_nhds_iff.mp hev2
    obtain ⟨k, hk⟩ := hyk.exists_mem_open hUo ⟨y, hyU⟩
    exact ⟨k, hUsub hk⟩
  have hfind2 : ∀ x y, (x, y) ∈ D → ∃ k, (x, yk k) ∈ D := by
    intro x y hD'
    have hev2 : ∀ᶠ y' in 𝓝 y, (x, y') ∈ D :=
      ((by fun_prop : Continuous fun y' : Y => (x, y')).tendsto y).eventually (hD.mem_nhds hD')
    obtain ⟨U, hUsub, hUo, hyU⟩ := mem_nhds_iff.mp hev2
    obtain ⟨k, hk⟩ := hyk.exists_mem_open hUo ⟨y, hyU⟩
    exact ⟨k, hUsub hk⟩
  let S := Prod.fst '' D
  let T : S → EReal := fun x => if F x = ⊥ then ((-1 / ε : ℝ) : EReal) else F x + (ε : EReal)
  let g : ℕ → S → EReal := fun k x => if ((x : X), yk k) ∈ D then f ((x : X), yk k) else ⊤
  let p : S → ℕ → Prop := fun x k => ((x : X), yk k) ∈ D ∧ g k x ≤ T x
  have hex : ∀ x : S, ∃ k, p x k := by
    rintro ⟨x, hx⟩
    obtain ⟨⟨x0, y0⟩, h0D, rfl⟩ := hx
    by_cases hb : F x0 = ⊥
    · have hlt : F x0 < ((-1 / ε : ℝ) : EReal) := hb ▸ EReal.bot_lt_coe _
      obtain ⟨y, hyD, hy⟩ := hFlt _ _ hlt
      obtain ⟨k, hk1, hk2⟩ := hfind _ _ _ hyD hy
      refine ⟨k, hk1, ?_⟩
      simp only [g, T, if_pos hk1, if_pos hb]
      exact hk2.le
    · by_cases ht : F x0 = ⊤
      · obtain ⟨k, hk⟩ := hfind2 _ _ h0D
        refine ⟨k, hk, ?_⟩
        simp only [g, T, if_pos hk, if_neg hb, ht, EReal.top_add_coe]
        exact le_top
      · have hlt : F x0 < F x0 + (ε : EReal) := by
          have e := EReal.coe_toReal ht hb
          rw [← e, ← EReal.coe_add]
          exact EReal.coe_lt_coe_iff.mpr (by linarith)
        obtain ⟨y, hyD, hy⟩ := hFlt _ _ hlt
        obtain ⟨k, hk1, hk2⟩ := hfind _ _ _ hyD hy
        refine ⟨k, hk1, ?_⟩
        simp only [g, T, if_pos hk1, if_neg hb]
        exact hk2.le
  have hgusc : ∀ k, UpperSemicontinuous (g k) := by
    intro k x c hc
    by_cases hin : ((x : X), yk k) ∈ D
    · have hc' : f ((x : X), yk k) < c := by simpa [g, hin] using hc
      have hev := husc _ hin c hc'
      have hcont : Continuous (fun x' : S => ((x' : X), yk k)) := by fun_prop
      filter_upwards [(hcont.tendsto x).eventually hev] with x' hx'
      simp only [g, if_pos hx'.1]
      exact hx'.2
    · simp [g, hin] at hc
  have hFm : Measurable (fun x : S => F x) := by
    have := (upperSemicontinuousOn_iff_restrict.mpr hFusc).measurable
    exact this
  have hTm : Measurable T := by
    apply Measurable.ite (hFm (measurableSet_singleton ⊥)) measurable_const
    exact (Monotone.measurable (f := fun a : EReal => a + (ε : EReal))
      (fun a b h => add_le_add h le_rfl)).comp hFm
  classical
  refine ⟨fun x => yk (Nat.find (hex x)), ?_, fun x => ?_⟩
  · apply (measurable_from_nat (f := yk)).comp
    apply measurable_find hex
    intro k
    have h1 : MeasurableSet {x : S | ((x : X), yk k) ∈ D} :=
      (hD.preimage (by fun_prop : Continuous fun x' : S => ((x' : X), yk k))).measurableSet
    have h2 : MeasurableSet {x : S | g k x ≤ T x} := measurableSet_le (hgusc k).measurable hTm
    exact h1.inter h2
  · have hs := Nat.find_spec (hex x)
    obtain ⟨hs1, hs2⟩ := hs
    simp only [g, if_pos hs1] at hs2
    refine ⟨hs1, fun hb => ?_, fun hb => ?_⟩
    · have : T x = F x + (ε : EReal) := if_neg hb
      exact le_of_le_of_eq hs2 this
    · have : T x = ((-1 / ε : ℝ) : EReal) := if_pos hb
      exact le_of_le_of_eq hs2 this

end BertsekasShreve.SemicontSelection

open BertsekasShreve.SemicontSelection
open TopologicalSpace BertsekasShreve.SemicontSelection

theorem solution {X Y : Type*}
    [TopologicalSpace X] [MetrizableSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MetrizableSpace Y] [SeparableSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (D : Set (X × Y)) (hD : IsOpen D) (f : X × Y → EReal) (hf : UpperSemicontinuousOn f D) :
    IsOpen (Prod.fst '' D) ∧
    UpperSemicontinuousOn (fun x => ⨅ (y : Y) (_ : (x, y) ∈ D), f (x, y)) (Prod.fst '' D) ∧
    ∀ ε : ℝ, 0 < ε → ∃ φ : (Prod.fst '' D) → Y, Measurable φ ∧
      ∀ x : (Prod.fst '' D), ((x : X), φ x) ∈ D ∧
        ((⨅ (y : Y) (_ : ((x : X), y) ∈ D), f ((x : X), y)) ≠ ⊥ →
          f ((x : X), φ x) ≤ (⨅ (y : Y) (_ : ((x : X), y) ∈ D), f ((x : X), y)) + (ε : EReal)) ∧
        ((⨅ (y : Y) (_ : ((x : X), y) ∈ D), f ((x : X), y)) = ⊥ →
          f ((x : X), φ x) ≤ ((-1 / ε : ℝ) : EReal)) := by
  exact p734_core D hD f hf
