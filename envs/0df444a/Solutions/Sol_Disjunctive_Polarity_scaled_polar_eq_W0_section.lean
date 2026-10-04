-- Prove2me | solution 1 for Disjunctive.Polarity.scaled_polar_eq_W0_section
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T04:23:46.993458+00:00
-- url     : https://prove2.me/submissions/8843f5f4-a82b-4fd2-8053-0dd5f4eb70a3

import Mathlib
import Definitions.Def_Disjunctive_Polarity_Polars

set_option autoImplicit false

namespace P2MFarkasEB

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

open Disjunctive.Polarity in
theorem affine_farkas {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (α : Fin n → ℝ) (α0 : ℝ) (hne : (Poly A b).Nonempty)
    (hval : ∀ x ∈ Poly A b, α0 ≤ dotProduct x α) :
    ∃ u : Fin m → ℝ, Matrix.vecMul u A = α ∧ α0 ≤ dotProduct u b ∧ 0 ≤ u := by
  classical
  let v : Option (Fin m) → (Fin n → ℝ) × ℝ := fun o =>
    match o with
    | none => (0, -1)
    | some i => (A i, b i)
  by_cases hp : ((α, α0) : (Fin n → ℝ) × ℝ) ∈ coneSet v
  · obtain ⟨c, hc, hx⟩ := hp
    refine ⟨fun i => c (some i), ?_, ?_, fun i => hc _⟩
    · rw [Fintype.sum_option] at hx
      have h1 := congrArg Prod.fst hx
      simp only [Prod.fst_add, Prod.fst_sum, Prod.smul_fst, v, smul_zero, zero_add] at h1
      ext j
      rw [h1]
      simp [Matrix.vecMul, dotProduct, Finset.sum_apply]
    · rw [Fintype.sum_option] at hx
      have h2 := congrArg Prod.snd hx
      simp only [Prod.snd_add, Prod.snd_sum, Prod.smul_snd, v, smul_eq_mul] at h2
      rw [h2]
      simp only [dotProduct]
      linarith [hc none]
  · obtain ⟨f, hfv, hfp⟩ := farkas_cone v _ hp
    let y : Fin n → ℝ := fun j => f ((Pi.single j 1 : Fin n → ℝ), (0 : ℝ))
    let s : ℝ := f ((0 : Fin n → ℝ), (1 : ℝ))
    have hf : ∀ z r, f (z, r) = dotProduct z y + r * s := by
      intro z r
      have : ((z, r) : (Fin n → ℝ) × ℝ) =
          ∑ j, z j • ((Pi.single j 1 : Fin n → ℝ), (0 : ℝ)) + r • ((0 : Fin n → ℝ), (1 : ℝ)) := by
        ext k
        · simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
        · simp [Prod.snd_sum]
      rw [this]
      simp only [map_add, map_sum, map_smul, smul_eq_mul]
      rfl
    have hgen : ∀ i, dotProduct (A i) y + b i * s ≤ 0 := fun i => by
      rw [← hf]; exact hfv (some i)
    have hs : 0 ≤ s := by
      have := hfv none
      simp only [v] at this
      rw [hf] at this
      simp at this
      linarith
    have hpos : 0 < dotProduct α y + α0 * s := by rw [← hf]; exact hfp
    have hmv : ∀ (z : Fin n → ℝ) (i : Fin m), (A.mulVec z) i = dotProduct (A i) z :=
      fun _ _ => rfl
    obtain ⟨x0, hx0⟩ := hne
    exfalso
    rcases hs.lt_or_eq with hs | hs
    · let x : Fin n → ℝ := (-s⁻¹) • y
      have hx : x ∈ Poly A b := by
        intro i
        rw [hmv]
        have := hgen i
        simp only [x, dotProduct_smul, smul_eq_mul]
        rw [show -s⁻¹ * dotProduct (A i) y = (-dotProduct (A i) y) / s by ring, le_div_iff₀ hs]
        linarith
      have hv := hval x hx
      have e : dotProduct x α = (-dotProduct α y) / s := by
        simp only [x, smul_dotProduct, smul_eq_mul, dotProduct_comm y α]
        ring
      have : (-dotProduct α y) / s < α0 := by
        rw [div_lt_iff₀ hs]; linarith
      linarith
    · rw [← hs] at hgen hpos
      have hαy : 0 < dotProduct α y := by simpa using hpos
      set t := (|dotProduct x0 α - α0| + 1) / dotProduct α y with ht_def
      have ht : 0 ≤ t := by positivity
      let x : Fin n → ℝ := x0 - t • y
      have hx : x ∈ Poly A b := by
        intro i
        rw [hmv]
        have h1 := hgen i
        have h2 := hx0 i
        rw [hmv] at h2
        simp only [x, dotProduct_sub, dotProduct_smul, smul_eq_mul]
        simp only [mul_zero, add_zero] at h1
        nlinarith
      have hv := hval x hx
      have e : dotProduct x α = dotProduct x0 α - t * dotProduct α y := by
        simp only [x, sub_dotProduct, smul_dotProduct, smul_eq_mul, dotProduct_comm y α]
      have e2 : t * dotProduct α y = |dotProduct x0 α - α0| + 1 := by
        rw [ht_def, div_mul_cancel₀ _ hαy.ne']
      have := le_abs_self (dotProduct x0 α - α0)
      linarith

end P2MFarkasEB

open Disjunctive.Polarity in
theorem solution {n : ℕ} {Q : Type*} [Fintype Q] (m : Q → ℕ)
    (A : (h : Q) → Matrix (Fin (m h)) (Fin n) ℝ) (b : (h : Q) → Fin (m h) → ℝ) (α0 : ℝ) :
    ScaledPolar (DisjunctiveSet m A b) α0 = {α : Fin n → ℝ | (α, α0) ∈ W0 m A b} := by
  ext α
  constructor
  · intro hα
    have key : ∀ h : Q, ∃ uh : Fin (m h) → ℝ, (Poly (A h) (b h)).Nonempty →
        (Matrix.vecMul uh (A h) = α ∧ α0 ≤ dotProduct uh (b h) ∧ 0 ≤ uh) := by
      intro h
      by_cases hne : (Poly (A h) (b h)).Nonempty
      · obtain ⟨u, hu⟩ := P2MFarkasEB.affine_farkas (A h) (b h) α α0 hne
          (fun x hx => hα x (Set.mem_iUnion.mpr ⟨h, hx⟩))
        exact ⟨u, fun _ => hu⟩
      · exact ⟨0, fun h' => absurd h' hne⟩
    choose u hu using key
    exact ⟨u, fun h hh => hu h hh⟩
  · rintro ⟨u, hu⟩ x hx
    obtain ⟨h, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨h1, h2, h3⟩ := hu h ⟨x, hx⟩
    calc α0 ≤ dotProduct (u h) (b h) := h2
      _ ≤ dotProduct (u h) ((A h).mulVec x) := dotProduct_le_dotProduct_of_nonneg_left hx h3
      _ = dotProduct x α := by rw [Matrix.dotProduct_mulVec, h1, dotProduct_comm]
