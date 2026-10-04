-- Prove2me | solution 1 for ConnesFeldmanWeiss.isHyperfinite_tailRel_of_isNonsingular
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-03T21:34:12.837997+00:00
-- url     : https://prove2.me/submissions/005e2d96-0e82-45b7-a20d-fc6f3c89242c

import Mathlib
import Definitions.Def_ConnesFeldmanWeiss
import Theorems.Thm_ConnesFeldmanWeiss_isHyperfinite_tailRel_of_isHyperfinite

section
/-! # Corollary 13 through Corollary 12

CFW p. 445: "Apply corollary 12 with R = {(x, x)}". Corollary 12 asks every fibre of `θ` to be
countable and Corollary 13 only almost every fibre, so `T` is first changed on a null set. Let `B`
be a measurable null hull of the points with an uncountable fibre and `X₀` the points whose forward
orbit avoids `B`: `X₀` is conull and forward invariant, and `θ = T` on `X₀`, `θ = id` off it, is
non-singular with every fibre countable. Corollary 12 for `θ` and the diagonal makes the tail
relation of `θ` hyperfinite, and it agrees with that of `T` on `X₀`. -/

namespace ConnesFeldmanWeiss.Cor13ViaCor12

open MeasureTheory Set Function

set_option linter.style.haveILetI false

variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

theorem diag_isDiscreteMeasured (μ : Measure X) :
    IsDiscreteMeasured μ {p : X × X | p.1 = p.2} := by
  refine ⟨measurableSet_diagonal, ⟨fun x => rfl, fun h => h.symm, fun h h' => h.trans h'⟩,
    fun x => ?_, ?_⟩
  · exact (countable_singleton x).mono fun y (hy : x = y) => hy.symm
  · intro A _ hA0
    refine measure_mono_null ?_ hA0
    rintro x ⟨y, hy, hxy⟩
    have h : x = y := hxy
    rw [h]
    exact hy

omit [StandardBorelSpace X] in
theorem standardBorelSpace_of_measurableEquiv' {α β : Type*} [MeasurableSpace α]
    [StandardBorelSpace α] [MeasurableSpace β] (e : α ≃ᵐ β) : StandardBorelSpace β := by
  letI := upgradeStandardBorel α
  letI τ : TopologicalSpace β := TopologicalSpace.induced e.symm inferInstance
  have hemb : Topology.IsClosedEmbedding (e.symm : β → α) := by
    refine ⟨⟨⟨rfl⟩, e.symm.injective⟩, ?_⟩
    rw [e.symm.surjective.range_eq]
    exact isClosed_univ
  haveI : PolishSpace β := hemb.polishSpace
  haveI : BorelSpace β := ⟨by
    rw [borel_comap, ← eq_borel_upgradeStandardBorel α]
    exact e.symm.measurableEmbedding.comap_eq.symm⟩
  exact ⟨⟨τ, inferInstance, inferInstance⟩⟩

/-- The diagonal is of type I: its quotient of `univ` is `univ` itself. -/
theorem diag_isTypeI (μ : Measure X) : IsTypeI μ {p : X × X | p.1 = p.2} := by
  have hcut : cutOff {p : X × X | p.1 = p.2} (univ : Set X)ᶜ = {p | p.1 = p.2} := by
    ext p
    simp [cutOff]
  refine ⟨univ, MeasurableSet.univ, by simp, fun _ _ _ => Iff.rfl,
    by rw [hcut]; exact diag_isDiscreteMeasured μ, ?_⟩
  haveI : StandardBorelSpace (univ : Set X) := MeasurableSet.univ.standardBorel
  let r : ↥(univ : Set X) → ↥(univ : Set X) → Prop := fun a b =>
    ((a : X), (b : X)) ∈ {p : X × X | p.1 = p.2}
  let e : ↥(univ : Set X) ≃ᵐ Quot r :=
    { toFun := Quot.mk r
      invFun := Quot.lift id fun a b (h : (a : X) = b) => Subtype.ext h
      left_inv := fun _ => rfl
      right_inv := fun q => Quot.inductionOn q fun _ => rfl
      measurable_toFun := measurable_quot_mk
      measurable_invFun := fun _ hs => hs }
  exact standardBorelSpace_of_measurableEquiv' e

theorem diag_isHyperfinite (μ : Measure X) : IsHyperfinite μ {p : X × X | p.1 = p.2} := by
  have hD := diag_isDiscreteMeasured μ
  have hcut : cutOff {p : X × X | p.1 = p.2} ∅ = {p | p.1 = p.2} := by
    ext p
    simp [cutOff]
  exact ⟨∅, MeasurableSet.empty, measure_empty, by rw [hcut]; exact hD, fun _ => {p | p.1 = p.2},
    monotone_const, fun _ => ⟨measurableSet_diagonal, hD.equivalence, diag_isTypeI μ⟩,
    fun x y _ _ => ⟨fun h => ⟨0, h⟩, fun ⟨_, h⟩ => h⟩⟩

theorem cutOff_isDiscreteMeasured {μ : Measure X} {E : Set (X × X)}
    (hE : IsDiscreteMeasured μ E) {M : Set X} (hM : MeasurableSet M) :
    IsDiscreteMeasured μ (cutOff E M) := by
  refine ⟨?_, ⟨fun x => Or.inr rfl, ?_, ?_⟩, fun x => ?_, fun A hA hA0 => ?_⟩
  · have h : cutOff E M = (E ∩ (Mᶜ ×ˢ Mᶜ)) ∪ {p | p.1 = p.2} := by
      ext p
      simp only [cutOff, mem_ofPred_eq, mem_union, mem_inter_iff, mem_prod, mem_compl_iff]
    rw [h]
    exact (hE.measurableSet.inter (hM.compl.prod hM.compl)).union measurableSet_diagonal
  · rintro x y (⟨h, hx, hy⟩ | h)
    · exact Or.inl ⟨hE.equivalence.symm h, hy, hx⟩
    · exact Or.inr (h : x = y).symm
  · rintro x y z (⟨h, hx, hy⟩ | h) (⟨h', hy', hz⟩ | h')
    · exact Or.inl ⟨hE.equivalence.trans h h', hx, hz⟩
    · have hyz : y = z := h'
      subst hyz
      exact Or.inl ⟨h, hx, hy⟩
    · have hxy : x = y := h
      subst hxy
      exact Or.inl ⟨h', hy', hz⟩
    · exact Or.inr ((h : x = y).trans h')
  · refine ((hE.countable_classes x).union (countable_singleton x)).mono ?_
    rintro y (⟨h, -, -⟩ | h)
    · exact Or.inl h
    · exact Or.inr (h : x = y).symm
  · refine measure_mono_null ?_ (measure_union_null hA0 (hE.quasiInvariant A hA hA0))
    rintro x ⟨y, hy, (⟨h, -, -⟩ | h)⟩
    · exact Or.inr ⟨y, hy, h⟩
    · have hxy : x = y := h
      rw [hxy]
      exact Or.inl hy

omit [MeasurableSpace X] [StandardBorelSpace X] in
theorem cutOff_cutOff' {R : Set (X × X)} {N N' : Set X} (h : N ⊆ N') :
    cutOff (cutOff R N) N' = cutOff R N' := by
  ext p
  simp only [cutOff, mem_ofPred_eq]
  constructor
  · rintro (⟨(⟨hR, -, -⟩ | hd), h1, h2⟩ | hd)
    · exact Or.inl ⟨hR, h1, h2⟩
    · exact Or.inr hd
    · exact Or.inr hd
  · rintro (⟨hR, h1, h2⟩ | hd)
    · exact Or.inl ⟨Or.inl ⟨hR, fun h' => h1 (h h'), fun h' => h2 (h h')⟩, h1, h2⟩
    · exact Or.inr hd

/-- Hyperfiniteness only sees a relation off a null set. -/
theorem isHyperfinite_of_agree_off_null {μ : Measure X} {R R' : Set (X × X)}
    (h : IsHyperfinite μ R) {N : Set X} (hN : MeasurableSet N) (hN0 : μ N = 0)
    (hRR' : ∀ x y, x ∉ N → y ∉ N → ((x, y) ∈ R ↔ (x, y) ∈ R')) : IsHyperfinite μ R' := by
  obtain ⟨N₁, hN₁, hN₁0, hdisc, S, hmono, hS, hN₁R⟩ := h
  have hagree : ∀ x y, x ∉ N₁ ∪ N → y ∉ N₁ ∪ N → ((x, y) ∈ R ↔ (x, y) ∈ R') :=
    fun x y hx hy => hRR' x y (fun h => hx (Or.inr h)) (fun h => hy (Or.inr h))
  have hcut : cutOff R' (N₁ ∪ N) = cutOff R (N₁ ∪ N) := by
    ext ⟨x, y⟩
    simp only [cutOff, mem_ofPred_eq]
    constructor
    · rintro (⟨h, hx, hy⟩ | h)
      · exact Or.inl ⟨(hagree x y hx hy).2 h, hx, hy⟩
      · exact Or.inr h
    · rintro (⟨h, hx, hy⟩ | h)
      · exact Or.inl ⟨(hagree x y hx hy).1 h, hx, hy⟩
      · exact Or.inr h
  refine ⟨N₁ ∪ N, hN₁.union hN, measure_union_null hN₁0 hN0, ?_, S, hmono, hS,
    fun x y hx hy => ?_⟩
  · rw [hcut, ← cutOff_cutOff' (subset_union_left : N₁ ⊆ N₁ ∪ N)]
    exact cutOff_isDiscreteMeasured hdisc (hN₁.union hN)
  · rw [← hagree x y hx hy]
    exact hN₁R x y (fun h => hx (Or.inl h)) (fun h => hy (Or.inl h))

omit [StandardBorelSpace X] in
theorem measure_preimage_iterate_eq_zero {μ : Measure X} {T : X → X} (hT : IsNonsingular μ T)
    {B : Set X} (hB : MeasurableSet B) (hB0 : μ B = 0) (n : ℕ) : μ (T^[n] ⁻¹' B) = 0 := by
  induction n with
  | zero => simpa using hB0
  | succ n ih =>
    rw [Function.iterate_succ, preimage_comp]
    exact (hT.2 _ ((hT.1.iterate n) hB)).2 ih

/-- **Corollary 13** (CFW p. 445), by Corollary 12 applied to the diagonal. -/
theorem isHyperfinite_tailRel_via_cor12 (μ : Measure X) [SigmaFinite μ]
    (T : X → X) (hT : IsNonsingular μ T) (hcount : ∀ᵐ x ∂μ, (T ⁻¹' {x}).Countable) :
    IsHyperfinite μ {p : X × X | ∃ n m : ℕ, T^[n] p.1 = T^[m] p.2} := by
  classical
  let B₀ : Set X := {x | ¬(T ⁻¹' {x}).Countable}
  have hB₀ : μ B₀ = 0 := ae_iff.1 hcount
  let B : Set X := toMeasurable μ B₀
  have hB : MeasurableSet B := measurableSet_toMeasurable μ B₀
  have hB0 : μ B = 0 := by rw [measure_toMeasurable]; exact hB₀
  -- `X₀`: the points whose forward orbit avoids `B`
  let X₀ : Set X := ⋂ n, T^[n] ⁻¹' Bᶜ
  have hX₀ : MeasurableSet X₀ := MeasurableSet.iInter fun n => (hT.1.iterate n) hB.compl
  have hX₀c : μ X₀ᶜ = 0 := by
    rw [compl_iInter]
    refine measure_iUnion_null fun n => ?_
    rw [preimage_compl, compl_compl]
    exact measure_preimage_iterate_eq_zero hT hB hB0 n
  have hfwd : ∀ x ∈ X₀, T x ∈ X₀ := by
    intro x hx
    refine mem_iInter.2 fun n => ?_
    have h := mem_iInter.1 hx (n + 1)
    rwa [mem_preimage, Function.iterate_succ_apply] at h
  have hnotB : ∀ x ∈ X₀, T x ∉ B := by
    intro x hx
    have h := mem_iInter.1 hx 1
    simpa using h
  let θ : X → X := X₀.piecewise T id
  have hθX : ∀ x ∈ X₀, θ x = T x := fun x hx => piecewise_eq_of_mem _ _ _ hx
  have hθn : ∀ x ∉ X₀, θ x = x := fun x hx => piecewise_eq_of_notMem _ _ _ hx
  have hiter : ∀ n, ∀ x ∈ X₀, θ^[n] x = T^[n] x ∧ T^[n] x ∈ X₀ := by
    intro n
    induction n with
    | zero => exact fun x hx => ⟨rfl, hx⟩
    | succ n ih =>
      intro x hx
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', (ih x hx).1,
        hθX _ (ih x hx).2]
      exact ⟨rfl, hfwd _ (ih x hx).2⟩
  have hpre : ∀ C, θ ⁻¹' C = (T ⁻¹' C ∩ X₀) ∪ (C \ X₀) := by
    intro C
    ext x
    by_cases hx : x ∈ X₀
    · simp only [mem_preimage, hθX x hx, mem_union, mem_inter_iff, hx, and_true, mem_sdiff,
        not_true_eq_false, and_false, or_false]
    · simp only [mem_preimage, hθn x hx, mem_union, mem_inter_iff, hx, and_false, mem_sdiff,
        not_false_eq_true, and_true, false_or]
  have hcompl : ∀ C : Set X, μ (C \ X₀) = 0 := fun C =>
    measure_mono_null (fun x hx => hx.2) hX₀c
  have hθ : IsNonsingular μ θ := by
    refine ⟨Measurable.piecewise hX₀ hT.1 measurable_id, fun C hC => ⟨fun h => ?_, fun h => ?_⟩⟩
    · rw [hpre] at h
      have h1 : μ (T ⁻¹' C ∩ X₀) = 0 := measure_mono_null subset_union_left h
      have h2 : μ (T ⁻¹' C) = 0 := by
        refine measure_mono_null (t := (T ⁻¹' C ∩ X₀) ∪ (T ⁻¹' C \ X₀)) ?_
          (measure_union_null h1 (hcompl _))
        intro x hx
        by_cases hxX : x ∈ X₀
        · exact Or.inl ⟨hx, hxX⟩
        · exact Or.inr ⟨hx, hxX⟩
      exact (hT.2 C hC).1 h2
    · rw [hpre]
      exact measure_union_null (measure_mono_null inter_subset_left ((hT.2 C hC).2 h))
        (hcompl _)
  have hcount' : ∀ y, (θ ⁻¹' {y}).Countable := by
    intro y
    by_cases hy : y ∈ B
    · refine (countable_singleton y).mono fun x hx => ?_
      have hx' : θ x = y := hx
      by_cases hxX : x ∈ X₀
      · rw [hθX x hxX] at hx'
        exact absurd (hx' ▸ hy) (hnotB x hxX)
      · rw [hθn x hxX] at hx'
        exact hx'
    · have hyc : (T ⁻¹' {y}).Countable := not_not.1 fun h => hy (subset_toMeasurable μ B₀ h)
      refine (hyc.union (countable_singleton y)).mono fun x hx => ?_
      have hx' : θ x = y := hx
      by_cases hxX : x ∈ X₀
      · rw [hθX x hxX] at hx'
        exact Or.inl hx'
      · rw [hθn x hxX] at hx'
        exact Or.inr hx'
  have h := ConnesFeldmanWeiss.isHyperfinite_tailRel_of_isHyperfinite μ {p : X × X | p.1 = p.2}
    (diag_isDiscreteMeasured μ) (diag_isHyperfinite μ) θ hθ hcount'
    (fun x y (h : x = y) => show θ x = θ y from congrArg θ h)
  refine isHyperfinite_of_agree_off_null h hX₀.compl hX₀c fun x y hx hy => ?_
  have hx' : x ∈ X₀ := not_not.1 hx
  have hy' : y ∈ X₀ := not_not.1 hy
  simp only [mem_ofPred_eq]
  constructor
  · rintro ⟨n, m, h⟩
    rw [(hiter n y hy').1, (hiter m x hx').1] at h
    exact ⟨m, n, h.symm⟩
  · rintro ⟨n, m, h⟩
    refine ⟨m, n, ?_⟩
    rw [(hiter m y hy').1, (hiter n x hx').1]
    exact h.symm

end ConnesFeldmanWeiss.Cor13ViaCor12
end

section
open ConnesFeldmanWeiss
open ConnesFeldmanWeiss.Cor13ViaCor12
open MeasureTheory Set Function
set_option linter.style.haveILetI false
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
theorem solution {X : Type*} [MeasurableSpace X]
    [StandardBorelSpace X] (μ : MeasureTheory.Measure X) [MeasureTheory.SigmaFinite μ]
    (T : X → X) (hT : IsNonsingular μ T) (hcount : ∀ᵐ x ∂μ, (T ⁻¹' {x}).Countable) :
    IsHyperfinite μ {p : X × X | ∃ n m : ℕ, T^[n] p.1 = T^[m] p.2} :=
  isHyperfinite_tailRel_via_cor12 μ T hT hcount
end
