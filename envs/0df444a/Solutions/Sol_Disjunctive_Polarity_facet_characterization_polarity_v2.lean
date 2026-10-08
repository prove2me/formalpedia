-- Prove2me | solution 1 for Disjunctive.Polarity.facet_characterization_polarity_v2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T08:03:17.301077+00:00
-- url     : https://prove2.me/submissions/d1ecf8a5-cf9d-4c12-8d6b-ec2589914d2a

import Mathlib
import Definitions.Def_Disjunctive_Polarity_Projection
import Definitions.Def_Disjunctive_Polarity_Polars
import Definitions.Def_Disjunctive_Polarity_FacetDefining

set_option autoImplicit false

namespace P2MFacetB34

open Finset

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Finitely generated cone. -/
def coneSet (v : ι → E) : Set E := {x | ∃ c : ι → ℝ, (∀ i, 0 ≤ c i) ∧ x = ∑ i, c i • v i}

lemma sum_ext (v : ι → E) (s : Finset ι) (d : s → ℝ) :
    ∑ i : s, d i • v i = ∑ i, (if h : i ∈ s then d ⟨i, h⟩ else 0) • v i := by
  have hz : ∀ i ∈ (univ : Finset ι), i ∉ s →
      (if h : i ∈ s then d ⟨i, h⟩ else 0) • v i = 0 := by
    intro i _ hi; simp [hi]
  rw [← Finset.sum_subset (Finset.subset_univ s) hz, ← Finset.sum_coe_sort s]
  refine Finset.sum_congr rfl ?_
  intro i _
  simp [i.2]

lemma sum_restrict (v : ι → E) (s : Finset ι) (c : ι → ℝ) (hc : ∀ i ∉ s, c i = 0) :
    ∑ i : s, c i • v i = ∑ i, c i • v i := by
  rw [Finset.sum_coe_sort s (fun i => c i • v i)]
  exact Finset.sum_subset (Finset.subset_univ s) (fun i _ hi => by simp [hc i hi])

lemma cara (v : ι → E) (x : E) : ∀ k : ℕ, ∀ c : ι → ℝ, (∀ i, 0 ≤ c i) → x = ∑ i, c i • v i →
    (univ.filter (fun i => c i ≠ 0)).card = k →
    ∃ s : Finset ι, LinearIndependent ℝ (fun i : s => v i) ∧
      ∃ c' : ι → ℝ, (∀ i, 0 ≤ c' i) ∧ (∀ i ∉ s, c' i = 0) ∧ x = ∑ i, c' i • v i := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro c hc hx hk
  set s := univ.filter (fun i => c i ≠ 0) with hs
  by_cases hli : LinearIndependent ℝ (fun i : s => v i)
  · exact ⟨s, hli, c, hc, fun i hi => by simpa [hs] using hi, hx⟩
  · obtain ⟨g, hg, i0, hi0⟩ := Fintype.not_linearIndependent_iff.mp hli
    let μ0 : ι → ℝ := fun i => if h : i ∈ s then g ⟨i, h⟩ else 0
    have hμ0 : ∑ i, μ0 i • v i = 0 := by rw [← sum_ext]; exact hg
    have hμ0s : ∀ i, c i = 0 → μ0 i = 0 := fun i hi => by simp [μ0, hs, hi]
    have hμ0i : μ0 i0 ≠ 0 := by
      have : μ0 i0 = g i0 := by simp [μ0, i0.2]
      rw [this]; exact hi0
    obtain ⟨μ, hμsum, hμs, j0, hj0⟩ : ∃ μ : ι → ℝ, ∑ i, μ i • v i = 0 ∧
        (∀ i, c i = 0 → μ i = 0) ∧ ∃ j, 0 < μ j := by
      rcases lt_or_gt_of_ne hμ0i with h | h
      · refine ⟨fun i => - μ0 i, ?_, ?_, i0, ?_⟩
        · simp [neg_smul, Finset.sum_neg_distrib, hμ0]
        · intro i hi; simp [hμ0s i hi]
        · simp only; linarith
      · exact ⟨μ0, hμ0, hμ0s, i0, h⟩
    set T := univ.filter (fun i => 0 < μ i) with hT
    have hTne : T.Nonempty := ⟨j0, by simp [T, hj0]⟩
    obtain ⟨j, hjT, hjmin⟩ := Finset.exists_min_image T (fun i => c i / μ i) hTne
    have hμj : 0 < μ j := by simpa [T] using hjT
    set t := c j / μ j with ht_def
    have ht : 0 ≤ t := div_nonneg (hc j) hμj.le
    let c' : ι → ℝ := fun i => c i - t * μ i
    have hc' : ∀ i, 0 ≤ c' i := by
      intro i
      by_cases hi : 0 < μ i
      · have h1 := hjmin i (by simp [T, hi])
        have h2 : t * μ i ≤ c i := by rwa [le_div_iff₀ hi] at h1
        simp only [c']; linarith
      · push Not at hi
        have : t * μ i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht hi
        simp only [c']; linarith [hc i]
    have hx' : x = ∑ i, c' i • v i := by
      simp only [c', sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, hμsum,
        smul_zero, sub_zero]
      exact hx
    have hcj : c j ≠ 0 := by
      intro h0; have := hμs j h0; linarith
    have hcard : (univ.filter (fun i => c' i ≠ 0)).card < k := by
      rw [← hk]
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨j, by simp [hs, hcj], ?_⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not, c', ht_def]
        field_simp
        ring
      · intro i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hs]
        intro h hci
        apply h
        simp [c', hci, hμs i hci]
    exact ih _ hcard c' hc' hx' rfl

lemma coneSet_closed (v : ι → E) : IsClosed (coneSet v) := by
  have key : coneSet v = ⋃ s ∈ {s : Finset ι | LinearIndependent ℝ (fun i : s => v i)},
      (Fintype.linearCombination ℝ (fun i : s => v i)) '' {d | ∀ i, 0 ≤ d i} := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_image, Set.mem_setOf_eq, coneSet, exists_prop]
    constructor
    · rintro ⟨c, hc, hx⟩
      obtain ⟨s, hli, c', hc', hs, hx'⟩ := cara v x _ c hc hx rfl
      refine ⟨s, hli, fun i => c' i, fun i => hc' i, ?_⟩
      rw [Fintype.linearCombination_apply, sum_restrict v s c' hs, hx']
    · rintro ⟨s, _, d, hd, rfl⟩
      refine ⟨fun i => if h : i ∈ s then d ⟨i, h⟩ else 0, ?_, ?_⟩
      · intro i
        by_cases h : i ∈ s
        · simp only [h, dite_true]; exact hd _
        · simp [h]
      · rw [Fintype.linearCombination_apply, sum_ext]
  rw [key]
  refine Set.Finite.isClosed_biUnion (Set.toFinite _) ?_
  intro s hs
  have hinj : Function.Injective (Fintype.linearCombination ℝ (fun i : s => v i)) :=
    linearIndependent_iff_injective_fintypeLinearCombination.mp hs
  have hcl : IsClosed {d : s → ℝ | ∀ i, 0 ≤ d i} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  exact (LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hinj)).isClosedMap _ hcl

lemma coneSet_convex (v : ι → E) : Convex ℝ (coneSet v) := by
  rintro x ⟨c, hc, rfl⟩ y ⟨d, hd, rfl⟩ a b ha hb _
  refine ⟨fun i => a * c i + b * d i, fun i => ?_, ?_⟩
  · have := hc i; have := hd i; positivity
  · simp only [add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]

lemma farkas_cone (v : ι → E) (p : E) (hp : p ∉ coneSet v) :
    ∃ f : StrongDual ℝ E, (∀ i, f (v i) ≤ 0) ∧ 0 < f p := by
  obtain ⟨f, u, hf, hu⟩ :=
    geometric_hahn_banach_closed_point (coneSet_convex v) (coneSet_closed v) hp
  have h0 : (0 : E) ∈ coneSet v := ⟨0, fun _ => le_rfl, by simp⟩
  have hu0 : 0 < u := by simpa using hf 0 h0
  refine ⟨f, fun i => ?_, by linarith⟩
  by_contra hcon
  push Not at hcon
  have hmem : (u / f (v i)) • v i ∈ coneSet v := by
    refine ⟨fun j => if j = i then u / f (v i) else 0, fun j => ?_, ?_⟩
    · dsimp only
      split_ifs
      · positivity
      · exact le_rfl
    · simp [ite_smul]
  have := hf _ hmem
  rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hcon.ne'] at this
  exact lt_irrefl _ this


omit [DecidableEq ι] in
lemma sum_smul_dot {n : ℕ} (u : ι → ℝ) (M : ι → Fin n → ℝ) (x : Fin n → ℝ) :
    (∑ i, u i • M i) ⬝ᵥ x = ∑ i, u i * (M i ⬝ᵥ x) := by
  rw [sum_dotProduct]
  simp [smul_dotProduct]

omit [DecidableEq ι] in
lemma cone_alt {n : ℕ} (M : ι → Fin n → ℝ) (c : ι → ℝ) (γ : Fin n → ℝ) (γ0 : ℝ) :
    (∃ u : ι → ℝ, 0 ≤ u ∧ ∑ i, u i • M i = γ ∧ γ0 ≤ ∑ i, u i * c i) ∨
    (∃ y : Fin n → ℝ, ∃ s : ℝ, 0 ≤ s ∧ (∀ i, M i ⬝ᵥ y + c i * s ≤ 0) ∧
      0 < γ ⬝ᵥ y + γ0 * s) := by
  classical
  let v : Option ι → (Fin n → ℝ) × ℝ := fun o =>
    match o with
    | none => (0, -1)
    | some i => (M i, c i)
  by_cases hp : ((γ, γ0) : (Fin n → ℝ) × ℝ) ∈ coneSet v
  · left
    obtain ⟨d, hd, hx⟩ := hp
    refine ⟨fun i => d (some i), fun i => hd _, ?_, ?_⟩
    · rw [Fintype.sum_option] at hx
      have h1 := congrArg Prod.fst hx
      simp only [Prod.fst_add, Prod.fst_sum, Prod.smul_fst, v, smul_zero, zero_add] at h1
      exact h1.symm
    · rw [Fintype.sum_option] at hx
      have h2 := congrArg Prod.snd hx
      simp only [Prod.snd_add, Prod.snd_sum, Prod.smul_snd, v, smul_eq_mul] at h2
      rw [h2]
      linarith [hd none]
  · right
    obtain ⟨f, hfv, hfp⟩ := farkas_cone v _ hp
    let y : Fin n → ℝ := fun j => f ((Pi.single j 1 : Fin n → ℝ), (0 : ℝ))
    let s : ℝ := f ((0 : Fin n → ℝ), (1 : ℝ))
    have hf : ∀ z r, f (z, r) = z ⬝ᵥ y + r * s := by
      intro z r
      have : ((z, r) : (Fin n → ℝ) × ℝ) =
          ∑ j, z j • ((Pi.single j 1 : Fin n → ℝ), (0 : ℝ)) + r • ((0 : Fin n → ℝ), (1 : ℝ)) := by
        ext k
        · simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
        · simp [Prod.snd_sum]
      rw [this]
      simp only [map_add, map_sum, map_smul, smul_eq_mul]
      rfl
    refine ⟨y, s, ?_, fun i => ?_, ?_⟩
    · have := hfv none
      simp only [v] at this
      rw [hf] at this
      simp at this
      linarith
    · rw [← hf]; exact hfv (some i)
    · rw [← hf]; exact hfp

omit [DecidableEq ι] in
lemma aff_farkas {n : ℕ} (M : ι → Fin n → ℝ) (c : ι → ℝ) (α : Fin n → ℝ) (α0 : ℝ)
    (hne : ∃ x, ∀ i, c i ≤ M i ⬝ᵥ x)
    (hval : ∀ x, (∀ i, c i ≤ M i ⬝ᵥ x) → α0 ≤ α ⬝ᵥ x) :
    ∃ u : ι → ℝ, 0 ≤ u ∧ ∑ i, u i • M i = α ∧ α0 ≤ ∑ i, u i * c i := by
  rcases cone_alt M c α α0 with h | ⟨y, s, hs, hM, hpos⟩
  · exact h
  exfalso
  obtain ⟨x0, hx0⟩ := hne
  rcases hs.lt_or_eq with hs | hs
  · let x : Fin n → ℝ := (-s⁻¹) • y
    have hx : ∀ i, c i ≤ M i ⬝ᵥ x := by
      intro i
      have := hM i
      simp only [x, dotProduct_smul, smul_eq_mul]
      rw [show -s⁻¹ * (M i ⬝ᵥ y) = (-(M i ⬝ᵥ y)) / s by ring, le_div_iff₀ hs]
      linarith
    have hv := hval x hx
    have e : α ⬝ᵥ x = (-(α ⬝ᵥ y)) / s := by
      simp only [x, dotProduct_smul, smul_eq_mul]
      ring
    have : (-(α ⬝ᵥ y)) / s < α0 := by
      rw [div_lt_iff₀ hs]; linarith
    linarith
  · rw [← hs] at hM hpos
    have hαy : 0 < α ⬝ᵥ y := by simpa using hpos
    set t := (|α ⬝ᵥ x0 - α0| + 1) / (α ⬝ᵥ y) with ht_def
    have ht : 0 ≤ t := by positivity
    let x : Fin n → ℝ := x0 - t • y
    have hx : ∀ i, c i ≤ M i ⬝ᵥ x := by
      intro i
      have h1 := hM i
      have h2 := hx0 i
      simp only [x, dotProduct_sub, dotProduct_smul, smul_eq_mul]
      simp only [mul_zero, add_zero] at h1
      nlinarith
    have hv := hval x hx
    have e : α ⬝ᵥ x = α ⬝ᵥ x0 - t * (α ⬝ᵥ y) := by
      simp only [x, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    have e2 : t * (α ⬝ᵥ y) = |α ⬝ᵥ x0 - α0| + 1 := by
      rw [ht_def, div_mul_cancel₀ _ hαy.ne']
    have := le_abs_self (α ⬝ᵥ x0 - α0)
    linarith

omit [DecidableEq ι] in
lemma infeas_farkas {n : ℕ} (M : ι → Fin n → ℝ) (c : ι → ℝ)
    (hemp : ¬ ∃ x, ∀ i, c i ≤ M i ⬝ᵥ x) :
    ∃ u : ι → ℝ, 0 ≤ u ∧ ∑ i, u i • M i = 0 ∧ 0 < ∑ i, u i * c i := by
  rcases cone_alt M c 0 1 with ⟨u, hu, h1, h2⟩ | ⟨y, s, hs, hM, hpos⟩
  · exact ⟨u, hu, h1, by linarith⟩
  · exfalso
    simp only [zero_dotProduct, zero_add, one_mul] at hpos
    apply hemp
    refine ⟨(-s⁻¹) • y, fun i => ?_⟩
    have := hM i
    simp only [dotProduct_smul, smul_eq_mul]
    rw [show -s⁻¹ * (M i ⬝ᵥ y) = (-(M i ⬝ᵥ y)) / s by ring, le_div_iff₀ hpos]
    linarith

open Filter Topology in
omit [DecidableEq ι] in
lemma finish {n : ℕ} (M : ι → Fin n → ℝ) (c : ι → ℝ) (α β : Fin n → ℝ) (α0 β0 : ℝ)
    (u z : ι → ℝ) (hu : 0 ≤ u) (huM : ∑ i, u i • M i = α) (hzM : ∑ i, z i • M i = β)
    (hz : ∀ i, ¬ 0 < u i → 0 ≤ z i)
    (hc : α0 < ∑ i, u i * c i ∨ (α0 ≤ ∑ i, u i * c i ∧ β0 ≤ ∑ i, z i * c i)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ x, (∀ i, c i ≤ M i ⬝ᵥ x) →
      α0 + ε * β0 ≤ (α + ε • β) ⬝ᵥ x := by
  have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have h1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i, 0 ≤ u i + ε * z i := by
    rw [Filter.eventually_all]
    intro i
    by_cases hui : 0 < u i
    · have ht : Tendsto (fun ε : ℝ => u i + ε * z i) (𝓝[>] (0 : ℝ)) (𝓝 (u i)) := by
        have : Tendsto (fun ε : ℝ => u i + ε * z i) (𝓝 (0 : ℝ)) (𝓝 (u i + 0 * z i)) :=
          (continuous_const.add (continuous_id.mul continuous_const)).tendsto 0
        simp only [zero_mul, add_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      filter_upwards [ht.eventually (lt_mem_nhds hui)] with ε hε
      exact hε.le
    · have hu0 : u i = 0 := le_antisymm (not_lt.1 hui) (hu i)
      filter_upwards [hpos] with ε hε
      rw [hu0, zero_add]
      exact mul_nonneg hε.le (hz i hui)
  have h2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      α0 + ε * β0 ≤ ∑ i, u i * c i + ε * ∑ i, z i * c i := by
    rcases hc with hc | ⟨hc1, hc2⟩
    · have ht : Tendsto (fun ε : ℝ => ∑ i, u i * c i + ε * ∑ i, z i * c i - ε * β0)
          (𝓝[>] (0 : ℝ)) (𝓝 (∑ i, u i * c i)) := by
        have : Tendsto (fun ε : ℝ => ∑ i, u i * c i + ε * ∑ i, z i * c i - ε * β0)
            (𝓝 (0 : ℝ)) (𝓝 (∑ i, u i * c i + 0 * ∑ i, z i * c i - 0 * β0)) :=
          ((continuous_const.add (continuous_id.mul continuous_const)).sub
            (continuous_id.mul continuous_const)).tendsto 0
        simp only [zero_mul, add_zero, sub_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      filter_upwards [ht.eventually (lt_mem_nhds hc)] with ε hε
      linarith
    · filter_upwards [hpos] with ε hε
      nlinarith
  filter_upwards [h1, h2] with ε hε1 hε2
  intro x hx
  have e : (α + ε • β) ⬝ᵥ x = ∑ i, (u i + ε * z i) * (M i ⬝ᵥ x) := by
    rw [← huM, ← hzM, add_dotProduct, smul_dotProduct, sum_smul_dot, sum_smul_dot,
      smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => by ring)
  have e2 : ∑ i, (u i + ε * z i) * c i = ∑ i, u i * c i + ε * ∑ i, z i * c i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => by ring)
  have hle : ∑ i, (u i + ε * z i) * c i ≤ ∑ i, (u i + ε * z i) * (M i ⬝ᵥ x) :=
    Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hx i) (hε1 i))
  linarith

omit [DecidableEq ι] in
/-- Multipliers for a perturbation direction, supported off the zero set of `u` up to sign. -/
lemma get_z {n : ℕ} (M : ι → Fin n → ℝ) (u c0 : ι → ℝ) (β : Fin n → ℝ) (β0 : ℝ)
    (hne : ∃ x, ∀ i, c0 i ≤ M i ⬝ᵥ x ∧ (0 < u i → M i ⬝ᵥ x ≤ c0 i))
    (hval : ∀ x, (∀ i, c0 i ≤ M i ⬝ᵥ x ∧ (0 < u i → M i ⬝ᵥ x ≤ c0 i)) → β0 ≤ β ⬝ᵥ x) :
    ∃ z : ι → ℝ, ∑ i, z i • M i = β ∧ β0 ≤ ∑ i, z i * c0 i ∧ ∀ i, ¬ 0 < u i → 0 ≤ z i := by
  classical
  let M' : ι ⊕ ι → Fin n → ℝ := Sum.elim M (fun i => if 0 < u i then -M i else 0)
  let c' : ι ⊕ ι → ℝ := Sum.elim c0 (fun i => if 0 < u i then -c0 i else 0)
  have hmem : ∀ x, (∀ j, c' j ≤ M' j ⬝ᵥ x) ↔
      (∀ i, c0 i ≤ M i ⬝ᵥ x ∧ (0 < u i → M i ⬝ᵥ x ≤ c0 i)) := by
    intro x
    constructor
    · intro h i
      refine ⟨h (Sum.inl i), fun hi => ?_⟩
      have := h (Sum.inr i)
      simp only [M', c', Sum.elim_inr, if_pos hi, neg_dotProduct] at this
      linarith
    · intro h j
      rcases j with i | i
      · exact (h i).1
      · simp only [M', c', Sum.elim_inr]
        split_ifs with hi
        · rw [neg_dotProduct]; linarith [(h i).2 hi]
        · simp
  obtain ⟨v, hv, hvM, hvc⟩ := aff_farkas M' c' β β0
    (by obtain ⟨x, hx⟩ := hne; exact ⟨x, (hmem x).2 hx⟩)
    (fun x hx => hval x ((hmem x).1 hx))
  refine ⟨fun i => v (Sum.inl i) - (if 0 < u i then v (Sum.inr i) else 0), ?_, ?_, ?_⟩
  · rw [← hvM, Fintype.sum_sum_type]
    simp only [M', Sum.elim_inl, Sum.elim_inr, sub_smul, Finset.sum_sub_distrib]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    split_ifs <;> simp
  · refine hvc.trans (le_of_eq ?_)
    rw [Fintype.sum_sum_type]
    simp only [c', Sum.elim_inl, Sum.elim_inr, sub_mul, Finset.sum_sub_distrib]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    split_ifs <;> simp
  · intro i hi
    simp only [if_neg hi, sub_zero]
    exact hv _

open Filter Topology in
omit [DecidableEq ι] in
/-- Per-polyhedron perturbation lemma. -/
lemma perturb {n : ℕ} (M : ι → Fin n → ℝ) (c : ι → ℝ) (α β : Fin n → ℝ) (α0 β0 : ℝ)
    (hne : ∃ x, ∀ i, c i ≤ M i ⬝ᵥ x)
    (hval : ∀ x, (∀ i, c i ≤ M i ⬝ᵥ x) → α0 ≤ α ⬝ᵥ x)
    (H1 : ∀ x, (∀ i, c i ≤ M i ⬝ᵥ x) → α ⬝ᵥ x = α0 → β ⬝ᵥ x = β0)
    (H2 : ∀ r, (∀ i, 0 ≤ M i ⬝ᵥ r) → α ⬝ᵥ r = 0 → β ⬝ᵥ r = 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ x, (∀ i, c i ≤ M i ⬝ᵥ x) →
      α0 + ε * β0 ≤ (α + ε • β) ⬝ᵥ x := by
  classical
  by_cases hface : ∃ x, (∀ i, c i ≤ M i ⬝ᵥ x) ∧ α ⬝ᵥ x = α0
  · obtain ⟨xb, hxb, hxbα⟩ := hface
    obtain ⟨u, hu, huM, huc⟩ := aff_farkas M c α α0 hne hval
    have e1 : ∑ i, u i * (M i ⬝ᵥ xb - c i) = α ⬝ᵥ xb - ∑ i, u i * c i := by
      rw [← huM, sum_smul_dot, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => by ring)
    have e2 : 0 ≤ ∑ i, u i * (M i ⬝ᵥ xb - c i) :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (hu i) (by linarith [hxb i]))
    have hsum : ∑ i, u i * (M i ⬝ᵥ xb - c i) = 0 := by linarith
    have hsumc : ∑ i, u i * c i = α0 := by linarith
    have hterm : ∀ i, u i * (M i ⬝ᵥ xb - c i) = 0 := by
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => mul_nonneg (hu i) (by linarith [hxb i]))).1 hsum i (Finset.mem_univ _)
    obtain ⟨z, hzM, hzc, hz⟩ := get_z M u c β β0
      ⟨xb, fun i => ⟨hxb i, fun hi => by
        have := hterm i
        rcases mul_eq_zero.1 this with h | h
        · exact absurd h hi.ne'
        · linarith⟩⟩
      (by
        intro x hx
        have hxP : ∀ i, c i ≤ M i ⬝ᵥ x := fun i => (hx i).1
        have hαx : α ⬝ᵥ x = α0 := by
          have e1 : α ⬝ᵥ x = ∑ i, u i * c i := by
            rw [← huM, sum_smul_dot]
            refine Finset.sum_congr rfl (fun i _ => ?_)
            by_cases hi : 0 < u i
            · rw [le_antisymm ((hx i).2 hi) ((hx i).1)]
            · rw [le_antisymm (not_lt.1 hi) (hu i)]; simp
          rw [e1, hsumc]
        rw [H1 x hxP hαx])
    exact finish M c α β α0 β0 u z hu huM hzM hz (Or.inr ⟨huc, hzc⟩)
  · -- no point of the face: a strict multiplier
    let M'' : ι ⊕ Unit → Fin n → ℝ := Sum.elim M (fun _ => -α)
    let c'' : ι ⊕ Unit → ℝ := Sum.elim c (fun _ => -α0)
    have hemp : ¬ ∃ x, ∀ j, c'' j ≤ M'' j ⬝ᵥ x := by
      rintro ⟨x, hx⟩
      apply hface
      have hxP : ∀ i, c i ≤ M i ⬝ᵥ x := fun i => hx (Sum.inl i)
      have h2 := hx (Sum.inr ())
      simp only [M'', c'', Sum.elim_inr, neg_dotProduct] at h2
      exact ⟨x, hxP, le_antisymm (by linarith) (hval x hxP)⟩
    obtain ⟨w, hw, hwM, hwc⟩ := infeas_farkas M'' c'' hemp
    rw [Fintype.sum_sum_type] at hwM hwc
    simp only [M'', c'', Sum.elim_inl, Sum.elim_inr, Finset.univ_unique,
      Finset.sum_singleton] at hwM hwc
    obtain ⟨x0, hx0⟩ := hne
    have htpos : 0 < w (Sum.inr ()) := by
      rcases (hw (Sum.inr ())).lt_or_eq with h | h
      · exact h
      · exfalso
        rw [← h, Pi.zero_apply, zero_smul, add_zero] at hwM
        rw [← h, Pi.zero_apply, zero_mul, add_zero] at hwc
        have e := congrArg (fun v => v ⬝ᵥ x0) hwM
        simp only [sum_smul_dot, zero_dotProduct] at e
        have : ∑ i, w (Sum.inl i) * c i ≤ ∑ i, w (Sum.inl i) * (M i ⬝ᵥ x0) :=
          Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hx0 i) (hw _))
        linarith
    set t := w (Sum.inr ()) with ht
    let u : ι → ℝ := fun i => w (Sum.inl i) / t
    have hu : 0 ≤ u := fun i => div_nonneg (hw _) htpos.le
    have huM : ∑ i, u i • M i = α := by
      have h1 : ∑ i, w (Sum.inl i) • M i = t • α := by
        rw [smul_neg] at hwM
        exact (add_neg_eq_zero.1 hwM)
      have h2 : ∑ i, u i • M i = t⁻¹ • ∑ i, w (Sum.inl i) • M i := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        simp only [u, smul_smul, div_eq_inv_mul]
      rw [h2, h1, smul_smul, inv_mul_cancel₀ htpos.ne', one_smul]
    have huc : α0 < ∑ i, u i * c i := by
      have : t * α0 < ∑ i, w (Sum.inl i) * c i := by linarith
      have e : ∑ i, u i * c i = (∑ i, w (Sum.inl i) * c i) / t := by
        simp only [u, Finset.sum_div]
        refine Finset.sum_congr rfl (fun i _ => by ring)
      rw [e, lt_div_iff₀ htpos]
      linarith
    obtain ⟨z, hzM, -, hz⟩ := get_z M u 0 β 0
      ⟨0, fun i => by simp⟩
      (by
        intro r hr
        have hrec : ∀ i, 0 ≤ M i ⬝ᵥ r := fun i => by simpa using (hr i).1
        have hαr : α ⬝ᵥ r = 0 := by
          rw [← huM, sum_smul_dot]
          refine Finset.sum_eq_zero (fun i _ => ?_)
          by_cases hi : 0 < u i
          · have h2 := (hr i).2 hi
            simp only [Pi.zero_apply] at h2
            rw [le_antisymm h2 (hrec i), mul_zero]
          · rw [le_antisymm (not_lt.1 hi) (hu i), zero_mul]
        rw [H2 r hrec hαr])
    exact finish M c α β α0 β0 u z hu huM hzM hz (Or.inl huc)

/-- `x ↦ α ⬝ᵥ x` as a linear functional. -/
def dotL {n : ℕ} (α : Fin n → ℝ) : (Fin n → ℝ) →ₗ[ℝ] ℝ where
  toFun x := α ⬝ᵥ x
  map_add' x y := dotProduct_add α x y
  map_smul' r x := by simp [dotProduct_smul]

lemma dotL_apply {n : ℕ} (α x : Fin n → ℝ) : dotL α x = α ⬝ᵥ x := rfl

lemma finrank_ker_dotL {n : ℕ} (α : Fin n → ℝ) (hα : α ≠ 0) :
    Module.finrank ℝ (LinearMap.ker (dotL α)) + 1 = n := by
  have h := LinearMap.finrank_range_add_finrank_ker (dotL α)
  rw [Module.finrank_fin_fun] at h
  have hle : Module.finrank ℝ (LinearMap.range (dotL α)) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range (dotL α))
    simpa using this
  have hne : Module.finrank ℝ (LinearMap.range (dotL α)) ≠ 0 := by
    intro h0
    rw [Submodule.finrank_eq_zero] at h0
    have : dotL α α ∈ LinearMap.range (dotL α) := LinearMap.mem_range_self _ _
    rw [h0, Submodule.mem_bot, dotL_apply] at this
    exact hα (dotProduct_self_eq_zero.1 this)
  omega

lemma prop_of_ker {n : ℕ} (α β : Fin n → ℝ) (hα : α ≠ 0)
    (h : ∀ v, α ⬝ᵥ v = 0 → β ⬝ᵥ v = 0) : ∃ s : ℝ, β = s • α := by
  have hαα : α ⬝ᵥ α ≠ 0 := fun h0 => hα (dotProduct_self_eq_zero.1 h0)
  refine ⟨(β ⬝ᵥ α) / (α ⬝ᵥ α), ?_⟩
  have key : ∀ v, β ⬝ᵥ v = (β ⬝ᵥ α) / (α ⬝ᵥ α) * (α ⬝ᵥ v) := by
    intro v
    have hw := h (v - ((α ⬝ᵥ v) / (α ⬝ᵥ α)) • α) (by
      rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, div_mul_cancel₀ _ hαα, sub_self])
    rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, sub_eq_zero] at hw
    rw [hw, dotProduct_comm β α]
    ring
  have hz : ∀ v, (β - ((β ⬝ᵥ α) / (α ⬝ᵥ α)) • α) ⬝ᵥ v = 0 := by
    intro v
    rw [sub_dotProduct, smul_dotProduct, smul_eq_mul, key v]
    ring
  have := hz (β - ((β ⬝ᵥ α) / (α ⬝ᵥ α)) • α)
  rw [dotProduct_self_eq_zero, sub_eq_zero] at this
  exact this

lemma dual_to_vec {n : ℕ} (f : Module.Dual ℝ (Fin n → ℝ)) :
    ∃ β : Fin n → ℝ, ∀ x, f x = β ⬝ᵥ x := by
  refine ⟨fun j => f (Pi.single j 1), fun x => ?_⟩
  have : x = ∑ j, x j • (Pi.single j 1 : Fin n → ℝ) := by
    ext k; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [this]
  simp only [map_sum, map_smul, smul_eq_mul, dotProduct]
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

lemma vectorSpan_le_ker {n : ℕ} (S : Set (Fin n → ℝ)) (β : Fin n → ℝ)
    (h : ∀ x ∈ S, ∀ y ∈ S, β ⬝ᵥ x = β ⬝ᵥ y) : vectorSpan ℝ S ≤ LinearMap.ker (dotL β) := by
  rw [vectorSpan_def, Submodule.span_le]
  rintro _ ⟨x, hx, y, hy, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, dotL_apply, vsub_eq_sub, dotProduct_sub]
  rw [h x hx y hy, sub_self]

open Disjunctive.Polarity

lemma W0_iff {n : ℕ} {Q : Type*} [Fintype Q] (m : Q → ℕ)
    (A : (h : Q) → Matrix (Fin (m h)) (Fin n) ℝ) (b : (h : Q) → Fin (m h) → ℝ)
    (p : (Fin n → ℝ) × ℝ) :
    p ∈ W0 m A b ↔ ∀ x ∈ DisjunctiveSet m A b, p.2 ≤ p.1 ⬝ᵥ x := by
  constructor
  · rintro ⟨u, hu⟩ x hx
    obtain ⟨h, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨h1, h2, h3⟩ := hu h ⟨x, hx⟩
    calc p.2 ≤ dotProduct (u h) (b h) := h2
      _ ≤ dotProduct (u h) ((A h).mulVec x) := dotProduct_le_dotProduct_of_nonneg_left hx h3
      _ = p.1 ⬝ᵥ x := by rw [Matrix.dotProduct_mulVec, h1]
  · intro hp
    have key : ∀ h : Q, ∃ uh : Fin (m h) → ℝ, (Poly (A h) (b h)).Nonempty →
        (Matrix.vecMul uh (A h) = p.1 ∧ p.2 ≤ dotProduct uh (b h) ∧ 0 ≤ uh) := by
      intro h
      by_cases hne : (Poly (A h) (b h)).Nonempty
      · obtain ⟨u, hu0, huM, huc⟩ := aff_farkas (fun i => A h i) (b h) p.1 p.2
          (by obtain ⟨x, hx⟩ := hne; exact ⟨x, fun i => hx i⟩)
          (fun x hx => hp x (Set.mem_iUnion.mpr ⟨h, fun i => hx i⟩))
        refine ⟨u, fun _ => ⟨?_, huc, hu0⟩⟩
        rw [Matrix.vecMul_eq_sum]
        exact huM
      · exact ⟨0, fun h' => absurd h' hne⟩
    choose u hu using key
    exact ⟨u, fun h hh => hu h hh⟩

end P2MFacetB34

open P2MFacetB34 Filter Topology

open Disjunctive.Polarity in
theorem solution {n : ℕ} {Q : Type*} [Fintype Q] (m : Q → ℕ)
    (A : (h : Q) → Matrix (Fin (m h)) (Fin n) ℝ) (b : (h : Q) → Fin (m h) → ℝ)
    (hdim : PolyDim (DisjunctiveSet m A b) = (n : ℤ)) (α : Fin n → ℝ) (α0 : ℝ)
    (hα : α ≠ 0) (hα0 : α0 ≠ 0) :
    DefinesFacetGE (closure (convexHull ℝ (DisjunctiveSet m A b))) α α0 ↔
      IsExtremeRay (W0 m A b) (α, α0) := by
  classical
  set F := DisjunctiveSet m A b with hF
  set C := closure (convexHull ℝ F) with hC
  have hFC : F ⊆ C := (subset_convexHull ℝ F).trans subset_closure
  have hCconv : Convex ℝ C := (convex_convexHull ℝ F).closure
  have hCcl : IsClosed C := isClosed_closure
  have hFne : F.Nonempty := by
    by_contra h
    unfold PolyDim at hdim
    rw [if_neg h] at hdim
    omega
  have hspanF : vectorSpan ℝ F = ⊤ := by
    unfold PolyDim at hdim
    rw [if_pos hFne] at hdim
    have : Module.finrank ℝ (vectorSpan ℝ F) = n := by exact_mod_cast hdim
    exact Submodule.eq_top_of_finrank_eq (by rw [this, Module.finrank_fin_fun])
  have hspanC : vectorSpan ℝ C = ⊤ := top_unique (hspanF ▸ vectorSpan_mono ℝ hFC)
  have hCne : C.Nonempty := hFne.mono hFC
  have hPDC : PolyDim C = n := by
    unfold PolyDim
    rw [if_pos hCne, hspanC, finrank_top, Module.finrank_fin_fun]
  have hn := finrank_ker_dotL α hα
  -- validity on `F` transfers to `C`
  have valid_C : ∀ (β : Fin n → ℝ) (β0 : ℝ), (∀ x ∈ F, β0 ≤ β ⬝ᵥ x) → ∀ x ∈ C, β0 ≤ β ⬝ᵥ x := by
    intro β β0 hv
    have hconv : Convex ℝ {x : Fin n → ℝ | β0 ≤ β ⬝ᵥ x} := by
      intro x hx y hy a c ha hc hac
      simp only [Set.mem_setOf_eq, dotProduct_add, dotProduct_smul, smul_eq_mul] at hx hy ⊢
      have k1 := mul_le_mul_of_nonneg_left hx ha
      have k2 := mul_le_mul_of_nonneg_left hy hc
      have k3 : a * β0 + c * β0 = β0 := by rw [← add_mul, hac, one_mul]
      linarith
    have hcl : IsClosed {x : Fin n → ℝ | β0 ≤ β ⬝ᵥ x} :=
      isClosed_le continuous_const (continuous_const.dotProduct continuous_id)
    exact closure_minimal (convexHull_min hv hconv) hcl
  have W0_valid : ∀ p ∈ W0 m A b, ∀ x ∈ C, p.2 ≤ p.1 ⬝ᵥ x := fun p hp =>
    valid_C p.1 p.2 ((W0_iff m A b p).1 hp)
  have valid_W0 : ∀ p : (Fin n → ℝ) × ℝ, (∀ x ∈ C, p.2 ≤ p.1 ⬝ᵥ x) → p ∈ W0 m A b :=
    fun p hp => (W0_iff m A b p).2 (fun x hx => hp x (hFC hx))
  have ray_sub : (α, α0) ∈ W0 m A b →
      {x | ∃ t : ℝ, 0 ≤ t ∧ x = t • ((α, α0) : (Fin n → ℝ) × ℝ)} ⊆ W0 m A b := by
    rintro hW _ ⟨t, ht, rfl⟩
    apply valid_W0
    intro x hx
    have := W0_valid _ hW x hx
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, smul_dotProduct]
    exact mul_le_mul_of_nonneg_left this ht
  have exists_above : (∀ x ∈ C, α0 ≤ α ⬝ᵥ x) → ∃ x ∈ C, α0 < α ⬝ᵥ x := by
    intro hv
    by_contra hcon
    push Not at hcon
    have hle : vectorSpan ℝ C ≤ LinearMap.ker (dotL α) :=
      vectorSpan_le_ker C α (fun x hx y hy => by
        rw [le_antisymm (hcon x hx) (hv x hx), le_antisymm (hcon y hy) (hv y hy)])
    rw [hspanC] at hle
    have : α ∈ LinearMap.ker (dotL α) := hle Submodule.mem_top
    rw [LinearMap.mem_ker, dotL_apply] at this
    exact hα (dotProduct_self_eq_zero.1 this)
  set G := C ∩ {x | α ⬝ᵥ x = α0} with hG
  have hGsub : vectorSpan ℝ G ≤ LinearMap.ker (dotL α) :=
    vectorSpan_le_ker G α (fun x hx y hy => by rw [hx.2, hy.2])
  have hextG : (∀ x ∈ C, α0 ≤ α ⬝ᵥ x) → IsExtreme ℝ C G := by
    intro hv
    refine ⟨Set.inter_subset_left, fun x1 hx1 x2 hx2 y hy hseg => ?_⟩
    obtain ⟨a, c, ha, hc, hac, rfl⟩ := hseg
    have h1 := hv x1 hx1
    have h2 := hv x2 hx2
    have hy2 := hy.2
    simp only [Set.mem_setOf_eq, dotProduct_add, dotProduct_smul, smul_eq_mul] at hy2
    have k : a * (α ⬝ᵥ x1 - α0) + c * (α ⬝ᵥ x2 - α0) = 0 := by
      have : a * α0 + c * α0 = α0 := by rw [← add_mul, hac, one_mul]
      rw [mul_sub, mul_sub]; linarith
    have p1 := mul_nonneg ha.le (sub_nonneg.2 h1)
    have p2 := mul_nonneg hc.le (sub_nonneg.2 h2)
    have z1 : a * (α ⬝ᵥ x1 - α0) = 0 := by linarith
    have e1 : α ⬝ᵥ x1 = α0 := sub_eq_zero.1 ((mul_eq_zero.1 z1).resolve_left ha.ne')
    exact Set.mem_inter hx1 e1
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; exact absurd (Subsingleton.elim α 0) hα
    · exact h0
  constructor
  · rintro ⟨hval, -, hGne, hdimG⟩
    have hVG : vectorSpan ℝ G = LinearMap.ker (dotL α) := by
      apply Submodule.eq_of_le_of_finrank_eq hGsub
      rw [hPDC] at hdimG
      unfold PolyDim at hdimG
      rw [if_pos hGne] at hdimG
      have h' : (Module.finrank ℝ (vectorSpan ℝ G) : ℤ) = n - 1 := hdimG
      omega
    obtain ⟨xb, hxbC, hxbα⟩ := hGne
    have tight_ray : ∀ p ∈ W0 m A b, (∀ x ∈ G, p.1 ⬝ᵥ x = p.2) →
        ∃ t : ℝ, 0 ≤ t ∧ p = t • ((α, α0) : (Fin n → ℝ) × ℝ) := by
      intro p hp htight
      have hker : LinearMap.ker (dotL α) ≤ LinearMap.ker (dotL p.1) := by
        rw [← hVG]
        exact vectorSpan_le_ker G p.1 (fun x hx y hy => by rw [htight x hx, htight y hy])
      obtain ⟨s, hs⟩ := prop_of_ker α p.1 hα (fun v hv => by
        have : v ∈ LinearMap.ker (dotL p.1) := hker (by rw [LinearMap.mem_ker, dotL_apply]; exact hv)
        rwa [LinearMap.mem_ker, dotL_apply] at this)
      have hp2 : p.2 = s * α0 := by
        rw [← htight xb ⟨hxbC, hxbα⟩, hs, smul_dotProduct, hxbα, smul_eq_mul]
      obtain ⟨xs, hxsC, hxs⟩ := exists_above hval
      have hvp := W0_valid p hp xs hxsC
      rw [hs, hp2, smul_dotProduct, smul_eq_mul] at hvp
      have hs0 : 0 ≤ s := by
        by_contra hneg
        push Not at hneg
        nlinarith
      refine ⟨s, hs0, Prod.ext ?_ ?_⟩
      · simp [hs]
      · simp [hp2]
    have hW : (α, α0) ∈ W0 m A b := valid_W0 _ hval
    refine ⟨fun h => hα (congrArg Prod.fst h), hW, ray_sub hW, ?_⟩
    intro p1 hp1 p2 hp2 z hz hseg
    obtain ⟨t, ht, rfl⟩ := hz
    obtain ⟨a, c, ha, hc, hac, hzab⟩ := hseg
    have hf := congrArg Prod.fst hzab
    have hs := congrArg Prod.snd hzab
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hf hs
    have tight : ∀ x ∈ G, p1.1 ⬝ᵥ x = p1.2 ∧ p2.1 ⬝ᵥ x = p2.2 := by
      intro x hx
      have e := congrArg (fun v => v ⬝ᵥ x) hf
      simp only [add_dotProduct, smul_dotProduct, smul_eq_mul] at e
      rw [hx.2] at e
      have v1 := W0_valid p1 hp1 x hx.1
      have v2 := W0_valid p2 hp2 x hx.1
      constructor <;> nlinarith
    exact tight_ray p1 hp1 (fun x hx => (tight x hx).1)
  · rintro ⟨-, hW, hext⟩
    have hvalF : ∀ x ∈ F, α0 ≤ α ⬝ᵥ x := (W0_iff m A b _).1 hW
    have hval : ∀ x ∈ C, α0 ≤ α ⬝ᵥ x := valid_C α α0 hvalF
    have memP : ∀ h x, x ∈ Poly (A h) (b h) ↔ ∀ i, b h i ≤ A h i ⬝ᵥ x := fun _ _ => Iff.rfl
    -- the key consequence of extremality
    have key : ∀ (β : Fin n → ℝ) (β0 : ℝ),
        (∀ h ∈ FeasibleIndices m A b, ∀ x ∈ Poly (A h) (b h), α ⬝ᵥ x = α0 → β ⬝ᵥ x = β0) →
        (∀ h ∈ FeasibleIndices m A b, ∀ r : Fin n → ℝ, (∀ i, 0 ≤ A h i ⬝ᵥ r) →
          α ⬝ᵥ r = 0 → β ⬝ᵥ r = 0) →
        ∃ s : ℝ, β = s • α ∧ β0 = s * α0 := by
      intro β β0 H1 H2
      have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ∀ h : Q, h ∈ FeasibleIndices m A b →
          (∀ x, (∀ i, b h i ≤ A h i ⬝ᵥ x) → α0 + ε * β0 ≤ (α + ε • β) ⬝ᵥ x) ∧
          (∀ x, (∀ i, b h i ≤ A h i ⬝ᵥ x) → α0 + ε * (-β0) ≤ (α + ε • (-β)) ⬝ᵥ x) := by
        have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := eventually_mem_nhdsWithin
        refine hpos.and ?_
        rw [Filter.eventually_all]
        intro h
        by_cases hh : h ∈ FeasibleIndices m A b
        · have hne : ∃ x, ∀ i, b h i ≤ A h i ⬝ᵥ x := by
            obtain ⟨x, hx⟩ := hh; exact ⟨x, fun i => hx i⟩
          have hv : ∀ x, (∀ i, b h i ≤ A h i ⬝ᵥ x) → α0 ≤ α ⬝ᵥ x :=
            fun x hx => hvalF x (Set.mem_iUnion.mpr ⟨h, fun i => hx i⟩)
          have P1 := perturb (fun i => A h i) (b h) α β α0 β0 hne hv
            (fun x hx hαx => H1 h hh x (fun i => hx i) hαx) (fun r hr hαr => H2 h hh r hr hαr)
          have P2 := perturb (fun i => A h i) (b h) α (-β) α0 (-β0) hne hv
            (fun x hx hαx => by rw [neg_dotProduct, H1 h hh x (fun i => hx i) hαx])
            (fun r hr hαr => by rw [neg_dotProduct, H2 h hh r hr hαr, neg_zero])
          filter_upwards [P1, P2] with ε e1 e2
          exact fun _ => ⟨e1, e2⟩
        · exact Filter.Eventually.of_forall (fun ε hh' => absurd hh' hh)
      obtain ⟨ε, hεpos, hε⟩ := hev.exists
      have memW : ∀ γ : Fin n → ℝ, ∀ γ0 : ℝ, (∀ h ∈ FeasibleIndices m A b,
          ∀ x, (∀ i, b h i ≤ A h i ⬝ᵥ x) → α0 + ε * γ0 ≤ (α + ε • γ) ⬝ᵥ x) →
          ((α + ε • γ, α0 + ε * γ0) : (Fin n → ℝ) × ℝ) ∈ W0 m A b := by
        intro γ γ0 hγ
        apply (W0_iff m A b _).2
        intro x hx
        obtain ⟨h, hx⟩ := Set.mem_iUnion.mp hx
        exact hγ h ⟨x, hx⟩ x (fun i => hx i)
      have hp1 := memW β β0 (fun h hh => (hε h hh).1)
      have hp2 := memW (-β) (-β0) (fun h hh => (hε h hh).2)
      have hray : ((α, α0) : (Fin n → ℝ) × ℝ) ∈
          {x | ∃ t : ℝ, 0 ≤ t ∧ x = t • ((α, α0) : (Fin n → ℝ) × ℝ)} :=
        ⟨1, zero_le_one, (one_smul _ _).symm⟩
      have hseg : ((α, α0) : (Fin n → ℝ) × ℝ) ∈ openSegment ℝ
          ((α + ε • β, α0 + ε * β0) : (Fin n → ℝ) × ℝ) (α + ε • (-β), α0 + ε * (-β0)) := by
        refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
        ext k
        · simp only [Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
            Pi.neg_apply]
          ring
        · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
          ring
      obtain ⟨t, -, ht⟩ := hext.2 hp1 hp2 hray hseg
      have hf := congrArg Prod.fst ht
      have hs := congrArg Prod.snd ht
      simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hf hs
      refine ⟨(t - 1) / ε, ?_, ?_⟩
      · ext k
        have := congrFun hf k
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
        field_simp
        linarith
      · field_simp
        linarith
    -- recession directions of the disjuncts are recession directions of `C`
    have hrec : ∀ h ∈ FeasibleIndices m A b, ∀ r : Fin n → ℝ, (∀ i, 0 ≤ A h i ⬝ᵥ r) →
        ∀ x ∈ C, x + r ∈ C := by
      intro h hh r hr x hx
      obtain ⟨p, hp⟩ := hh
      have ht : Tendsto (fun t : ℝ => (1 - t) • x + t • p + r) (𝓝[>] (0 : ℝ)) (𝓝 (x + r)) := by
        have hc : Continuous (fun t : ℝ => (1 - t) • x + t • p + r) := by fun_prop
        exact (hc.tendsto' 0 (x + r) (by simp)).mono_left nhdsWithin_le_nhds
      apply hCcl.mem_of_tendsto ht
      filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t htI
      have hq : p + t⁻¹ • r ∈ C := by
        apply hFC
        refine Set.mem_iUnion.mpr ⟨h, fun i => ?_⟩
        show b h i ≤ A h i ⬝ᵥ (p + t⁻¹ • r)
        rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
        have := hp i
        have := hr i
        have : 0 ≤ t⁻¹ := inv_nonneg.2 htI.1.le
        change b h i ≤ A h i ⬝ᵥ p at *
        nlinarith
      have hmem := hCconv hx hq (by linarith [htI.2] : (0 : ℝ) ≤ 1 - t) htI.1.le (by ring)
      have e : (1 - t) • x + t • (p + t⁻¹ • r) = (1 - t) • x + t • p + r := by
        rw [smul_add, smul_smul, mul_inv_cancel₀ htI.1.ne', one_smul, add_assoc]
      rwa [e] at hmem
    -- the face is nonempty
    have hGne : G.Nonempty := by
      by_contra hGe
      obtain ⟨s, hs1, hs2⟩ := key 0 1
        (fun h _ x hx hαx => absurd ⟨x, hFC (Set.mem_iUnion.mpr ⟨h, hx⟩), hαx⟩ hGe)
        (fun _ _ r _ _ => zero_dotProduct r)
      have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs2
      exact hα ((smul_eq_zero.1 hs1.symm).resolve_left hs0)
    obtain ⟨xb, hxbC, hxbα⟩ := hGne
    have hVG : vectorSpan ℝ G = LinearMap.ker (dotL α) := by
      refine le_antisymm hGsub ?_
      by_contra hnot
      obtain ⟨v, hvK, hvV⟩ := SetLike.not_le_iff_exists.1 hnot
      obtain ⟨f, hfv, hfmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hvV inferInstance
      obtain ⟨β, hβ⟩ := dual_to_vec f
      have hf0 : ∀ w ∈ vectorSpan ℝ G, f w = 0 := by
        intro w hw
        have : f w ∈ (vectorSpan ℝ G).map f := Submodule.mem_map_of_mem hw
        rw [hfmap, Submodule.mem_bot] at this
        exact this
      have hGc : ∀ x ∈ G, β ⬝ᵥ x = β ⬝ᵥ xb := by
        intro x hx
        have := hf0 _ (vsub_mem_vectorSpan ℝ hx ⟨hxbC, hxbα⟩)
        rw [hβ, vsub_eq_sub, dotProduct_sub, sub_eq_zero] at this
        exact this
      obtain ⟨s, hs1, -⟩ := key β (β ⬝ᵥ xb)
        (fun h _ x hx hαx => hGc x ⟨hFC (Set.mem_iUnion.mpr ⟨h, hx⟩), hαx⟩)
        (fun h hh r hr hαr => by
          have hxr : xb + r ∈ G := ⟨hrec h hh r hr xb hxbC, by
            show α ⬝ᵥ (xb + r) = α0
            rw [dotProduct_add, hxbα, hαr, add_zero]⟩
          have := hGc _ hxr
          rw [dotProduct_add] at this
          linarith)
      apply hfv
      rw [hβ, hs1, smul_dotProduct, smul_eq_mul]
      rw [LinearMap.mem_ker, dotL_apply] at hvK
      rw [hvK, mul_zero]
    refine ⟨hval, hextG hval, ⟨xb, hxbC, hxbα⟩, ?_⟩
    rw [hPDC]
    unfold PolyDim
    rw [if_pos ⟨xb, hxbC, hxbα⟩, hVG]
    omega
