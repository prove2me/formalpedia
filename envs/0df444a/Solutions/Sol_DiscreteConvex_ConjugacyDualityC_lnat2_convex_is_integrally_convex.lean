-- Prove2me | solution 1 for DiscreteConvex.ConjugacyDualityC.lnat2_convex_is_integrally_convex
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T23:39:09.347077+00:00
-- url     : https://prove2.me/submissions/a2991073-c1aa-4e5d-a266-f2a432c173ee

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_LNat2Convex
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_LNat2ConvexSet
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_IsIntegrallyConvexFunction
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_IsIntegrallyConvex

set_option autoImplicit false

namespace P7d18

open Classical
open DiscreteConvex.ConjugacyDualityC
open scoped Pointwise


theorem ceil_int_add (n : ℤ) (y : ℝ) (h1 : -1 < y) (h2 : y ≤ 1) :
    ⌈(n : ℝ) + y⌉ = n + if 0 < y then 1 else 0 := by
  rw [Int.ceil_eq_iff]
  split_ifs with h
  · push_cast; constructor <;> linarith
  · push_cast; constructor <;> linarith [not_lt.mp h]

/-- Threshold-rounding hull lemma: `q` is a convex combination of its roundings `⌈q - θ⌉`. -/
theorem round_hull {ι : Type*} [Fintype ι] :
    ∀ (n : ℕ) (q : ι → ℝ), (Finset.univ.filter (fun i => Int.fract (q i) ≠ 0)).card ≤ n →
      q ∈ convexHull ℝ {x : ι → ℝ | ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧
        x = fun i => ((⌈q i - θ⌉ : ℤ) : ℝ)} := by
  intro n
  induction n with
  | zero =>
    intro q hq
    apply subset_convexHull
    refine ⟨0, le_refl _, one_pos, ?_⟩
    funext i
    have hf : Int.fract (q i) = 0 := by
      by_contra h
      have hmem : i ∈ Finset.univ.filter (fun i => Int.fract (q i) ≠ 0) := by simp [h]
      rw [Finset.card_eq_zero.mp (Nat.le_zero.mp hq)] at hmem
      simp at hmem
    have h2 : q i = (⌊q i⌋ : ℝ) := by have := Int.floor_add_fract (q i); linarith
    rw [sub_zero, h2, Int.ceil_intCast]
  | succ n ih =>
    intro q hq
    by_cases hle : (Finset.univ.filter (fun i => Int.fract (q i) ≠ 0)).card ≤ n
    · exact ih q hle
    have hpos : 0 < (Finset.univ.filter (fun i => Int.fract (q i) ≠ 0)).card := by omega
    obtain ⟨i1, hi1⟩ := Finset.card_pos.mp hpos
    have hne : (Finset.univ : Finset ι).Nonempty := ⟨i1, Finset.mem_univ _⟩
    set μ := Finset.univ.sup' hne (fun i => Int.fract (q i)) with hμdef
    have hle_mu : ∀ i, Int.fract (q i) ≤ μ := fun i => Finset.le_sup' (fun i => Int.fract (q i)) (Finset.mem_univ i)
    obtain ⟨i0, -, hi0⟩ := Finset.exists_mem_eq_sup' hne (fun i => Int.fract (q i))
    have hi0' : Int.fract (q i0) = μ := hi0.symm
    have hf1 : Int.fract (q i1) ≠ 0 := (Finset.mem_filter.mp hi1).2
    have hμpos : 0 < μ := lt_of_lt_of_le (lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm hf1)) (hle_mu i1)
    have hμlt : μ < 1 := hi0' ▸ Int.fract_lt_one _
    have hμne : μ ≠ 0 := ne_of_gt hμpos
    set A : ι → ℝ := fun i => (⌊q i⌋ : ℝ) + Int.fract (q i) / μ with hA
    -- claim 1: roundings of A are roundings of q
    have claim1 : ∀ θ : ℝ, 0 ≤ θ → θ < 1 → ∀ i, ⌈A i - θ⌉ = ⌈q i - μ * θ⌉ := by
      intro θ h0 h1 i
      have hf0 := Int.fract_nonneg (q i)
      have hfl := hle_mu i
      have hμθ : μ * θ < μ := by nlinarith
      have e1 : A i - θ = (⌊q i⌋ : ℝ) + (Int.fract (q i) - μ * θ) / μ := by
        simp only [hA]; field_simp; ring
      have e2 : q i - μ * θ = (⌊q i⌋ : ℝ) + (Int.fract (q i) - μ * θ) := by
        have := Int.floor_add_fract (q i); linarith
      rw [e1, e2]
      have hy1 : -1 < (Int.fract (q i) - μ * θ) / μ := by
        rw [lt_div_iff₀ hμpos]; linarith
      have hy2 : (Int.fract (q i) - μ * θ) / μ ≤ 1 := by
        rw [div_le_iff₀ hμpos]; nlinarith
      rw [ceil_int_add _ _ hy1 hy2, ceil_int_add _ _ (by nlinarith) (by nlinarith)]
      have : (0 < (Int.fract (q i) - μ * θ) / μ) ↔ (0 < Int.fract (q i) - μ * θ) :=
        div_pos_iff_of_pos_right hμpos
      simp only [this]
    -- claim 2: the floor vector is a rounding of q at θ = μ
    have claim2 : ∀ i, ⌈q i - μ⌉ = ⌊q i⌋ := by
      intro i
      have hf0 := Int.fract_nonneg (q i)
      have hfl := hle_mu i
      have e2 : q i - μ = (⌊q i⌋ : ℝ) + (Int.fract (q i) - μ) := by
        have := Int.floor_add_fract (q i); linarith
      rw [e2, ceil_int_add _ _ (by linarith) (by linarith)]
      simp [not_lt.mpr (sub_nonpos.mpr hfl)]
    -- claim 3: fewer fractional coordinates
    have claim3 : (Finset.univ.filter (fun i => Int.fract (A i) ≠ 0)).card ≤ n := by
      have hsub : Finset.univ.filter (fun i => Int.fract (A i) ≠ 0) ⊂
          Finset.univ.filter (fun i => Int.fract (q i) ≠ 0) := by
        rw [Finset.ssubset_iff_of_subset]
        · refine ⟨i0, ?_, ?_⟩
          · simp [hi0', hμne]
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not]
            have : A i0 = ((⌊q i0⌋ + 1 : ℤ) : ℝ) := by
              simp only [hA, hi0', div_self hμne]; push_cast; ring
            rw [this, Int.fract_intCast]
        · intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
          intro hq0
          apply hi
          have : A i = ((⌊q i⌋ : ℤ) : ℝ) := by simp [hA, hq0]
          rw [this, Int.fract_intCast]
      have := Finset.card_lt_card hsub
      omega
    have hAmem := ih A claim3
    have hsubset : {x : ι → ℝ | ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧ x = fun i => ((⌈A i - θ⌉ : ℤ) : ℝ)} ⊆
        {x : ι → ℝ | ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧ x = fun i => ((⌈q i - θ⌉ : ℤ) : ℝ)} := by
      rintro x ⟨θ, h0, h1, rfl⟩
      refine ⟨μ * θ, by positivity, by nlinarith, ?_⟩
      funext i
      rw [claim1 θ h0 h1 i]
    have hA' := convexHull_mono hsubset hAmem
    have hF : (fun i => ((⌊q i⌋ : ℤ) : ℝ)) ∈ convexHull ℝ
        {x : ι → ℝ | ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧ x = fun i => ((⌈q i - θ⌉ : ℤ) : ℝ)} := by
      apply subset_convexHull
      refine ⟨μ, hμpos.le, hμlt, ?_⟩
      funext i
      rw [claim2 i]
    have hcomb := convex_convexHull ℝ _ hA' hF hμpos.le (by linarith : (0:ℝ) ≤ 1 - μ)
      (by ring : μ + (1 - μ) = 1)
    convert hcomb using 1
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hA]
    have := Int.floor_add_fract (q i)
    field_simp
    linarith

/-- Membership criterion for L-convex sets. -/
theorem lconv_mem {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W] (E : Set (W → ℤ))
    (hE : LConvexSet E) (p : W → ℝ) (hp : p ∈ convexHull ℝ (IntEmbed E)) (y : W → ℤ)
    (hy : ∀ a b, ((y b : ℝ) - y a) < p b - p a + 1) : y ∈ E := by
  obtain ⟨hne, hmm, htr⟩ := hE
  -- step 1
  have step1 : ∀ a b, ∃ d ∈ E, y b - y a ≤ d b - d a := by
    intro a b
    by_contra hcon
    push_neg at hcon
    have hsub : IntEmbed E ⊆ {x : W → ℝ | x b - x a ≤ ((y b - y a - 1 : ℤ) : ℝ)} := by
      rintro x ⟨d, hd, rfl⟩
      have := hcon d hd
      simp only [Set.mem_setOf_eq]
      have h' : d b - d a ≤ y b - y a - 1 := by omega
      exact_mod_cast h'
    have hconv : Convex ℝ {x : W → ℝ | x b - x a ≤ ((y b - y a - 1 : ℤ) : ℝ)} := by
      intro x hx z hz α β hα hβ hαβ
      simp only [Set.mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx hz ⊢
      have : α * x b + β * z b - (α * x a + β * z a) = α * (x b - x a) + β * (z b - z a) := by ring
      rw [this]
      calc α * (x b - x a) + β * (z b - z a) ≤ α * ((y b - y a - 1 : ℤ) : ℝ) + β * ((y b - y a - 1 : ℤ) : ℝ) := by
            gcongr
        _ = _ := by rw [← add_mul, hαβ, one_mul]
    have := convexHull_min hsub hconv hp
    simp only [Set.mem_setOf_eq] at this
    have h2 := hy a b
    push_cast at this
    linarith
  -- step 2: integer translations
  have step2 : ∀ d ∈ E, ∀ k : ℤ, (fun v => d v + k) ∈ E := by
    intro d hd k
    induction k using Int.induction_on with
    | zero => simpa using hd
    | succ k ih =>
      have := (htr _ ih).1
      convert this using 2 with v
      push_cast; ring
    | pred k ih =>
      have := (htr _ ih).2
      convert this using 2 with v
      push_cast; ring
  -- step 3
  have step3 : ∀ a b, ∃ d ∈ E, d a = y a ∧ y b ≤ d b := by
    intro a b
    obtain ⟨d, hd, hdb⟩ := step1 a b
    refine ⟨fun v => d v + (y a - d a), step2 d hd _, by ring, by simp only; omega⟩
  -- step 4
  have step4 : ∀ a, ∀ s : Finset W, ∃ e ∈ E, e a = y a ∧ ∀ b ∈ s, y b ≤ e b := by
    intro a s
    induction s using Finset.induction_on with
    | empty =>
      obtain ⟨d, hd, hda, -⟩ := step3 a a
      exact ⟨d, hd, hda, by simp⟩
    | insert b s hb ih =>
      obtain ⟨e, he, hea, heb⟩ := ih
      obtain ⟨d, hd, hda, hdb⟩ := step3 a b
      refine ⟨fun v => max (e v) (d v), (hmm e he d hd).1, by simp [hea, hda], ?_⟩
      intro c hc
      rcases Finset.mem_insert.mp hc with rfl | hc
      · exact le_trans hdb (le_max_right _ _)
      · exact le_trans (heb c hc) (le_max_left _ _)
  -- step 5
  have step5 : ∀ s : Finset W, ∃ f ∈ E, (∀ v, y v ≤ f v) ∧ ∀ a ∈ s, f a = y a := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      obtain ⟨e, he, -, heb⟩ := step4 (Classical.arbitrary W) Finset.univ
      exact ⟨e, he, fun v => heb v (Finset.mem_univ v), by simp⟩
    | insert a s ha ih =>
      obtain ⟨f, hf, hfy, hfa⟩ := ih
      obtain ⟨e, he, hea, heb⟩ := step4 a Finset.univ
      refine ⟨fun v => min (f v) (e v), (hmm f hf e he).2, ?_, ?_⟩
      · intro v; exact le_min (hfy v) (heb v (Finset.mem_univ v))
      · intro c hc
        rcases Finset.mem_insert.mp hc with rfl | hc
        · simp only; rw [hea]; exact min_eq_right (hfy c)
        · simp only; rw [hfa c hc]; exact min_eq_left (heb c (Finset.mem_univ c))
  obtain ⟨f, hf, -, hfa⟩ := step5 Finset.univ
  have : f = y := funext fun v => hfa v (Finset.mem_univ v)
  rw [← this]; exact hf

/-- The lift linear map `x ↦ (0, x)`. -/
noncomputable def liftLin (V : Type*) : (V → ℝ) →ₗ[ℝ] (Option V → ℝ) where
  toFun x o := Option.elim o 0 x
  map_add' x y := by funext o; cases o <;> simp
  map_smul' c x := by funext o; cases o <;> simp

/-- Membership criterion for L♮-convex sets. -/
theorem lnat_mem {V : Type*} [Fintype V] [DecidableEq V] (D : Set (V → ℤ))
    (hD : LNatConvexSet D) (x : V → ℝ) (hx : x ∈ convexHull ℝ (IntEmbed D)) (y : V → ℤ)
    (hb1 : ∀ v, (y v : ℝ) < x v + 1) (hb2 : ∀ v, x v - 1 < (y v : ℝ))
    (hy : ∀ a b, ((y b : ℝ) - y a) < x b - x a + 1) : y ∈ D := by
  have hlift : liftLin V x ∈ convexHull ℝ (IntEmbed (LiftedSetL D)) := by
    have h1 : liftLin V x ∈ liftLin V '' convexHull ℝ (IntEmbed D) := ⟨x, hx, rfl⟩
    rw [LinearMap.image_convexHull] at h1
    refine convexHull_mono ?_ h1
    rintro z ⟨w, ⟨d, hd, rfl⟩, rfl⟩
    refine ⟨fun o => Option.elim o 0 d, ?_, ?_⟩
    · show (fun v => d v - 0) ∈ D
      simpa using hd
    · funext o; cases o <;> simp [liftLin]
  have hmem := lconv_mem (LiftedSetL D) hD (liftLin V x) hlift (fun o => Option.elim o 0 y) (by
    intro a b
    rcases a with _ | a <;> rcases b with _ | b <;> simp [liftLin]
    · linarith [hb1 b]
    · linarith [hb2 a]
    · linarith [hy a b])
  have : (fun v => (fun o => Option.elim o 0 y) (some v) - (fun o => Option.elim o 0 y) none) = y := by
    funext v; simp
  have h' : (fun v => (fun o => Option.elim o 0 y) (some v) - (fun o => Option.elim o 0 y) none) ∈ D :=
    hmem
  rwa [this] at h'


/-- LN-1: the Minkowski sum of two L♮-convex sets is integrally convex. -/
theorem set_part {V : Type*} [Fintype V] [DecidableEq V] (D1 D2 : Set (V → ℤ))
    (h1 : LNatConvexSet D1) (h2 : LNatConvexSet D2) : IsIntegrallyConvex (D1 + D2) := by
  intro p hp
  have hsub : IntEmbed (D1 + D2) ⊆ IntEmbed D1 + IntEmbed D2 := by
    rintro z ⟨d, ⟨d1, hd1, d2, hd2, rfl⟩, rfl⟩
    exact ⟨_, ⟨d1, hd1, rfl⟩, _, ⟨d2, hd2, rfl⟩, by funext v; simp⟩
  have hp' := convexHull_mono hsub hp
  rw [convexHull_add] at hp'
  obtain ⟨x1, hx1, x2, hx2, hsum⟩ := hp'
  let q : V ⊕ V → ℝ := Sum.elim x1 (fun v => -x2 v)
  have hq := round_hull _ q le_rfl
  let S : (V ⊕ V → ℝ) →ₗ[ℝ] (V → ℝ) :=
    { toFun := fun z v => z (Sum.inl v) - z (Sum.inr v),
      map_add' := by intro a b; funext v; simp; ring,
      map_smul' := by intro c a; funext v; simp; ring }
  have hSq : S q = p := by
    rw [← hsum]; funext v; simp [S, q]
  have h3 : p ∈ S '' convexHull ℝ {x : V ⊕ V → ℝ | ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧
        x = fun i => ((⌈q i - θ⌉ : ℤ) : ℝ)} := ⟨q, hq, hSq⟩
  rw [LinearMap.image_convexHull] at h3
  refine convexHull_mono ?_ h3
  rintro z ⟨w, ⟨θ, hθ0, hθ1, rfl⟩, rfl⟩
  set y1 : V → ℤ := fun v => ⌈x1 v - θ⌉ with hy1def
  set y2 : V → ℤ := fun v => -⌈-x2 v - θ⌉ with hy2def
  have hy1 : y1 ∈ D1 := by
    apply lnat_mem D1 h1 x1 hx1 y1
    · intro v; have := Int.ceil_lt_add_one (x1 v - θ); simp only [hy1def]; linarith
    · intro v; have := Int.le_ceil (x1 v - θ); simp only [hy1def]; linarith
    · intro a b
      have := Int.ceil_lt_add_one (x1 b - θ); have := Int.le_ceil (x1 a - θ)
      simp only [hy1def]; linarith
  have hy2 : y2 ∈ D2 := by
    apply lnat_mem D2 h2 x2 hx2 y2
    · intro v; have := Int.le_ceil (-x2 v - θ); simp only [hy2def]; push_cast; linarith
    · intro v; have := Int.ceil_lt_add_one (-x2 v - θ); simp only [hy2def]; push_cast; linarith
    · intro a b
      have := Int.ceil_lt_add_one (-x2 a - θ); have := Int.le_ceil (-x2 b - θ)
      simp only [hy2def]; push_cast; linarith
  refine ⟨y1 + y2, ⟨Set.add_mem_add hy1 hy2, ?_⟩, ?_⟩
  · intro v
    have hpv : p v = x1 v + x2 v := by rw [← hsum]; rfl
    have a1 := Int.ceil_lt_add_one (x1 v - θ); have a2 := Int.le_ceil (x1 v - θ)
    have a3 := Int.ceil_lt_add_one (-x2 v - θ); have a4 := Int.le_ceil (-x2 v - θ)
    have lo : ⌊p v⌋ < (y1 + y2) v + 1 := by
      rw [Int.floor_lt]; simp only [Pi.add_apply, hy1def, hy2def]; push_cast; linarith
    have hi : (y1 + y2) v - 1 < ⌈p v⌉ := by
      rw [Int.lt_ceil]; simp only [Pi.add_apply, hy1def, hy2def]; push_cast; linarith
    constructor <;> omega
  · funext v
    simp [S, q, hy1def, hy2def]
    ring

theorem set_conj {V : Type*} [Fintype V] [DecidableEq V] :
    ∀ D : Set (V → ℤ), LNat2ConvexSet D → IsIntegrallyConvex D := by
  rintro D ⟨D1, D2, h1, h2, rfl⟩
  exact set_part D1 D2 h1 h2


section greedySec
open Finset

/-- Greedy (Edmonds) lemma on a ring family: a submodular `ρ` on a ring family `D` of subsets of
`W` has a modular minorant `μ` that is tight on a prescribed chain `C ⊆ D` and on `W`. -/
theorem greedy {α : Type*} [DecidableEq α] :
    ∀ (n : ℕ) (W : Finset α), W.card ≤ n → ∀ (D : Set (Finset α)) (ρ : Finset α → ℝ)
      (C : Set (Finset α)), (∀ X ∈ D, X ⊆ W) → ∅ ∈ D → W ∈ D →
      (∀ X ∈ D, ∀ Y ∈ D, X ∪ Y ∈ D ∧ X ∩ Y ∈ D) →
      (∀ X ∈ D, ∀ Y ∈ D, ρ (X ∪ Y) + ρ (X ∩ Y) ≤ ρ X + ρ Y) → ρ ∅ = 0 →
      C ⊆ D → IsChain (· ⊆ ·) C →
      ∃ μ : α → ℝ, (∀ X ∈ D, ∑ a ∈ X, μ a ≤ ρ X) ∧ (∀ X ∈ C, ∑ a ∈ X, μ a = ρ X) ∧
        ∑ a ∈ W, μ a = ρ W := by
  intro n
  induction n with
  | zero =>
    intro W hW D ρ C hDW _ _ _ _ hρ0 hCD _
    have hW0 : W = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hW)
    subst hW0
    refine ⟨0, ?_, ?_, ?_⟩
    · intro X hX; rw [Finset.subset_empty.mp (hDW X hX)]; simp [hρ0]
    · intro X hX; rw [Finset.subset_empty.mp (hDW X (hCD hX))]; simp [hρ0]
    · simp [hρ0]
  | succ n ih =>
    intro W hW D ρ C hDW hD0 hDW' hDcl hsub hρ0 hCD hC
    by_cases hWe : W = ∅
    · subst hWe
      refine ⟨0, ?_, ?_, ?_⟩
      · intro X hX; rw [Finset.subset_empty.mp (hDW X hX)]; simp [hρ0]
      · intro X hX; rw [Finset.subset_empty.mp (hDW X (hCD hX))]; simp [hρ0]
      · simp [hρ0]
    have hWne : W.Nonempty := Finset.nonempty_iff_ne_empty.mpr hWe
    -- B : a smallest member of {X ∈ C nonempty} ∪ {W}
    set K : Set (Finset α) := {X | (X ∈ C ∧ X.Nonempty) ∨ X = W} with hK
    have hKfin : K.Finite := by
      apply (W.powerset.finite_toSet).subset
      intro X hX
      rcases hX with ⟨hXC, -⟩ | rfl
      · exact Finset.mem_coe.mpr (Finset.mem_powerset.mpr (hDW X (hCD hXC)))
      · exact Finset.mem_coe.mpr (Finset.mem_powerset.mpr le_rfl)
    obtain ⟨B, hBK, hBmin⟩ := Set.exists_min_image K Finset.card hKfin ⟨W, Or.inr rfl⟩
    have hBD : B ∈ D := by
      rcases hBK with ⟨hBC, -⟩ | rfl
      · exact hCD hBC
      · exact hDW'
    have hBne : B.Nonempty := by
      rcases hBK with ⟨-, h⟩ | rfl
      · exact h
      · exact hWne
    have hBsub : ∀ X ∈ C, X.Nonempty → B ⊆ X := by
      intro X hXC hXne
      have hXK : X ∈ K := Or.inl ⟨hXC, hXne⟩
      have hcard := hBmin X hXK
      rcases hBK with ⟨hBC, -⟩ | rfl
      · by_cases hXB : X = B
        · rw [hXB]
        · rcases hC hXC hBC hXB with h | h
          · exact (Finset.eq_of_subset_of_card_le h hcard) ▸ le_rfl
          · exact h
      · have hXW : X ⊆ B := hDW X (hCD hXC)
        exact (Finset.eq_of_subset_of_card_le hXW hcard) ▸ le_rfl
    -- A : a minimal nonempty member of D inside B
    set Aset : Set (Finset α) := {X | X ∈ D ∧ X.Nonempty ∧ X ⊆ B} with hAset
    have hAfin : Aset.Finite := by
      apply (B.powerset.finite_toSet).subset
      intro X hX
      exact Finset.mem_coe.mpr (Finset.mem_powerset.mpr hX.2.2)
    obtain ⟨A, ⟨hAD, hAne, hAB⟩, hAmin⟩ :=
      Set.exists_min_image Aset Finset.card hAfin ⟨B, hBD, hBne, le_rfl⟩
    have hAW : A ⊆ W := hDW A hAD
    have hAdich : ∀ X ∈ D, X ∩ A = ∅ ∨ A ⊆ X := by
      intro X hX
      by_cases h : (X ∩ A).Nonempty
      · right
        have hmem : X ∩ A ∈ Aset :=
          ⟨(hDcl X hX A hAD).2, h, (Finset.inter_subset_right).trans hAB⟩
        have hc := hAmin _ hmem
        have heq := Finset.eq_of_subset_of_card_le (Finset.inter_subset_right (s₁ := X)) hc
        rw [← heq]; exact Finset.inter_subset_left
      · left; exact Finset.not_nonempty_iff_eq_empty.mp h
    obtain ⟨a0, ha0⟩ := hAne
    -- recursion
    set W' := W \ A with hW'
    have hW'card : W'.card ≤ n := by
      have h1 : W'.card < W.card := by
        apply Finset.card_lt_card
        refine ⟨Finset.sdiff_subset, ?_⟩
        intro h
        have := h (hAW ha0)
        simp [hW'] at this
        exact this.2 ha0
      omega
    set D' : Set (Finset α) := {Y | Y ⊆ W' ∧ Y ∪ A ∈ D} with hD'
    set ρ' : Finset α → ℝ := fun Y => ρ (Y ∪ A) - ρ A with hρ'
    set C' : Set (Finset α) := {Y | Y ⊆ W' ∧ Y ∪ A ∈ C} with hC'
    have eU : ∀ Y1 Y2 : Finset α, (Y1 ∪ Y2) ∪ A = (Y1 ∪ A) ∪ (Y2 ∪ A) := by
      intro Y1 Y2; ext a; simp only [Finset.mem_union]; tauto
    have eI : ∀ Y1 Y2 : Finset α, (Y1 ∩ Y2) ∪ A = (Y1 ∪ A) ∩ (Y2 ∪ A) := by
      intro Y1 Y2; ext a; simp only [Finset.mem_union, Finset.mem_inter]; tauto
    have hdisj : ∀ Y ⊆ W', Disjoint Y A := by
      intro Y hY
      rw [Finset.disjoint_left]
      intro a ha haA
      have := hY ha
      simp [hW'] at this
      exact this.2 haA
    have hrec : ∀ Y ⊆ W', (Y ∪ A) \ A = Y := by
      intro Y hY
      rw [Finset.union_sdiff_right]
      exact Finset.sdiff_eq_self_of_disjoint (hdisj Y hY)
    obtain ⟨μ', hμ'D, hμ'C, hμ'W⟩ := ih W' hW'card D' ρ' C'
      (fun X hX => hX.1)
      ⟨Finset.empty_subset _, by simpa using hAD⟩
      ⟨le_rfl, by rw [hW', Finset.sdiff_union_of_subset hAW]; exact hDW'⟩
      (by
        intro X hX Y hY
        refine ⟨⟨Finset.union_subset hX.1 hY.1, ?_⟩, ⟨(Finset.inter_subset_left).trans hX.1, ?_⟩⟩
        · rw [eU]; exact (hDcl _ hX.2 _ hY.2).1
        · rw [eI]; exact (hDcl _ hX.2 _ hY.2).2)
      (by
        intro X hX Y hY
        simp only [hρ']
        rw [eU, eI]
        have := hsub _ hX.2 _ hY.2
        linarith)
      (by simp [hρ'])
      (fun X hX => ⟨hX.1, hCD hX.2⟩)
      (by
        intro X hX Y hY hXY
        have hne : X ∪ A ≠ Y ∪ A := by
          intro h
          apply hXY
          rw [← hrec X hX.1, ← hrec Y hY.1, h]
        rcases hC hX.2 hY.2 hne with h | h
        · left
          intro a ha
          have := h (Finset.mem_union_left A ha)
          rcases Finset.mem_union.mp this with h1 | h1
          · exact h1
          · exact absurd h1 (Finset.disjoint_left.mp (hdisj X hX.1) ha)
        · right
          intro a ha
          have := h (Finset.mem_union_left A ha)
          rcases Finset.mem_union.mp this with h1 | h1
          · exact h1
          · exact absurd h1 (Finset.disjoint_left.mp (hdisj Y hY.1) ha))
    set μ : α → ℝ := fun a => if a ∈ A then (if a = a0 then ρ A else 0) else μ' a with hμ
    have hsplit : ∀ X : Finset α, ∑ a ∈ X, μ a = ∑ a ∈ X ∩ A, μ a + ∑ a ∈ X \ A, μ' a := by
      intro X
      rw [← Finset.sum_inter_add_sum_sdiff X A μ]
      congr 1
      apply Finset.sum_congr rfl
      intro a ha
      have : a ∉ A := (Finset.mem_sdiff.mp ha).2
      simp [hμ, this]
    have hAsum : ∑ a ∈ A, μ a = ρ A := by
      rw [Finset.sum_congr rfl (g := fun a => if a = a0 then ρ A else 0)]
      · rw [Finset.sum_ite_eq' A a0]; simp [ha0]
      · intro a ha; simp [hμ, ha]
    have hfull : ∀ X, A ⊆ X → X \ A ⊆ W' → (X \ A) ∪ A = X := by
      intro X hAX _
      exact Finset.sdiff_union_of_subset hAX
    refine ⟨μ, ?_, ?_, ?_⟩
    · intro X hX
      have hXW := hDW X hX
      have hXA' : X \ A ∈ D' := by
        refine ⟨Finset.sdiff_subset_sdiff hXW le_rfl, ?_⟩
        rw [Finset.sdiff_union_self_eq_union]
        exact (hDcl X hX A hAD).1
      have h1 := hμ'D _ hXA'
      simp only [hρ', Finset.sdiff_union_self_eq_union] at h1
      rw [hsplit]
      rcases hAdich X hX with h | h
      · rw [h, Finset.sum_empty, zero_add]
        have := hsub X hX A hAD
        rw [h, hρ0] at this
        linarith
      · rw [Finset.inter_eq_right.mpr h, hAsum]
        rw [Finset.union_eq_left.mpr h] at h1
        linarith
    · intro X hX
      by_cases hXe : X.Nonempty
      · have hAX : A ⊆ X := hAB.trans (hBsub X hX hXe)
        have hXW := hDW X (hCD hX)
        have hmem : X \ A ∈ C' := by
          refine ⟨Finset.sdiff_subset_sdiff hXW le_rfl, ?_⟩
          rw [Finset.sdiff_union_of_subset hAX]; exact hX
        have h1 := hμ'C _ hmem
        simp only [hρ', Finset.sdiff_union_of_subset hAX] at h1
        rw [hsplit, Finset.inter_eq_right.mpr hAX, hAsum, h1]
        ring
      · rw [Finset.not_nonempty_iff_eq_empty.mp hXe]; simp [hρ0]
    · simp only [hρ', hW', Finset.sdiff_union_of_subset hAW] at hμ'W
      rw [hsplit, Finset.inter_eq_right.mpr hAW, hAsum, hμ'W]
      ring

/-- Local optimality implies global optimality for a submodular, translation-invariant
function on `ℤ^W` (Murota's L-optimality criterion). -/
theorem loc_glob {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
    (G : (W → ℤ) → WithTop ℝ)
    (hsub : ∀ p q, G (p ⊔ q) + G (p ⊓ q) ≤ G p + G q)
    (htr : ∀ p, G (p + 1) = G p) (z : W → ℤ) (hz : G z ≠ ⊤)
    (hloc : ∀ X : Finset W, G z ≤ G (fun a => z a + if a ∈ X then 1 else 0)) :
    ∀ y, G z ≤ G y := by
  have htrk : ∀ (k : ℕ) (p : W → ℤ), G (fun a => p a + k) = G p := by
    intro k
    induction k with
    | zero => intro p; simp
    | succ k ih =>
      intro p
      rw [← ih p, ← htr (fun a => p a + k)]
      congr 1; funext a; simp; ring
  have key : ∀ M : ℕ, ∀ y : W → ℤ, (∀ a, z a ≤ y a) → (∀ a, y a - z a ≤ M) → G z ≤ G y := by
    intro M
    induction M with
    | zero =>
      intro y h1 h2
      have : y = z := funext fun a => by have := h1 a; have := h2 a; push_cast at *; omega
      rw [this]
    | succ M ih =>
      intro y h1 h2
      set U := Finset.univ.filter (fun a => z a < y a) with hU
      set y' : W → ℤ := (y - 1) ⊔ z with hy'
      have hs := hsub (y - 1) z
      have e1 : G (y - 1) = G y := by
        have := htr (y - 1); rw [sub_add_cancel] at this; exact this.symm
      have e2 : G ((y - 1) ⊓ z) = G (fun a => z a + if a ∈ U then 1 else 0) := by
        rw [← htr]; congr 1; funext a
        simp only [Pi.add_apply, Pi.inf_apply, Pi.sub_apply, Pi.one_apply, hU,
          Finset.mem_filter, Finset.mem_univ, true_and]
        have := h1 a
        split_ifs with h <;> omega
      have hy'1 : G z ≤ G y' := by
        apply ih y'
        · intro a; simp only [hy', Pi.sup_apply]; omega
        · intro a; simp only [hy', Pi.sup_apply, Pi.sub_apply, Pi.one_apply]
          have := h1 a; have := h2 a; push_cast at *; omega
      have hl := hloc U
      have hle : G y' + G z ≤ G y + G z := by
        calc G y' + G z ≤ G y' + G ((y - 1) ⊓ z) := by rw [e2]; exact add_le_add le_rfl hl
          _ ≤ G (y - 1) + G z := hs
          _ = G y + G z := by rw [e1]
      have := (WithTop.add_le_add_iff_right hz).mp hle
      exact le_trans hy'1 this
  intro y
  obtain ⟨a0, -, ha0⟩ := Finset.exists_min_image Finset.univ (fun a => y a - z a)
    Finset.univ_nonempty
  set y0 : W → ℤ := fun a => y a - (y a0 - z a0) with hy0
  obtain ⟨b0, -, hb0⟩ := Finset.exists_max_image Finset.univ (fun a => y0 a - z a)
    Finset.univ_nonempty
  have hge : ∀ a, z a ≤ y0 a := by
    intro a; have := ha0 a (Finset.mem_univ a); simp only [hy0]; omega
  have hk : G y = G y0 ∨ True := Or.inr trivial
  clear hk
  have hyy : G y = G y0 := by
    rcases le_total 0 (y a0 - z a0) with h | h
    · have := htrk (y a0 - z a0).toNat y0
      rw [← this]; congr 1; funext a; simp only [hy0]; omega
    · have := htrk (z a0 - y a0).toNat y
      rw [← this]; congr 1; funext a; simp only [hy0]; omega
  rw [hyy]
  apply key (y0 b0 - z b0).toNat y0 hge
  intro a
  have := hb0 a (Finset.mem_univ a)
  have := hge b0
  omega

end greedySec


theorem ceil_sub_eq (r θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ < 1) :
    ⌈r - θ⌉ = ⌊r⌋ + if θ < Int.fract r then 1 else 0 := by
  have e : r - θ = (⌊r⌋ : ℝ) + (Int.fract r - θ) := by
    have := Int.floor_add_fract r; linarith
  rw [e, ceil_int_add _ _ (by linarith [Int.fract_nonneg r]) (by linarith [Int.fract_lt_one r])]
  simp [sub_pos]

theorem wt_le_real {a b c d : WithTop ℝ} (ha : a ≠ ⊤) (hb : b ≠ ⊤) (hc : c ≠ ⊤) (hd : d ≠ ⊤)
    (h : c + d ≤ a + b) : c.untopD 0 + d.untopD 0 ≤ a.untopD 0 + b.untopD 0 := by
  lift a to ℝ using ha
  lift b to ℝ using hb
  lift c to ℝ using hc
  lift d to ℝ using hd
  simp only [WithTop.untopD_coe]
  exact_mod_cast h

theorem wt_eq_coe {a : WithTop ℝ} (ha : a ≠ ⊤) : a = ((a.untopD 0 : ℝ) : WithTop ℝ) := by
  lift a to ℝ using ha
  simp

theorem lift_eval {V : Type*} (f : (V → ℤ) → WithTop ℝ) (y : V → ℤ) :
    LiftedFunctionL f (fun o => Option.elim o 0 y) = f y := by
  simp [LiftedFunctionL]

theorem lift_tr {V : Type*} (f : (V → ℤ) → WithTop ℝ) (p : Option V → ℤ) :
    LiftedFunctionL f (p + 1) = LiftedFunctionL f p := by
  simp only [LiftedFunctionL, Pi.add_apply, Pi.one_apply]
  congr 1; funext v; ring

/-- The effective domain of an L♮-convex function is an L♮-convex set. -/
theorem dom_lnat {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ)
    (hf : LNaturalConvex f) (hne : (DomZ f).Nonempty) : LNatConvexSet (DomZ f) := by
  obtain ⟨hsbf, -⟩ := hf
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨y, hy⟩ := hne
    refine ⟨fun o => Option.elim o 0 y, ?_⟩
    show LiftedFunctionL f (fun o => Option.elim o 0 y) ≠ ⊤
    rw [lift_eval]; exact hy
  · intro p hp q hq
    have hp' : LiftedFunctionL f p ≠ ⊤ := hp
    have hq' : LiftedFunctionL f q ≠ ⊤ := hq
    have h : LiftedFunctionL f (p ⊔ q) + LiftedFunctionL f (p ⊓ q) ≤
        LiftedFunctionL f p + LiftedFunctionL f q := hsbf p q
    have hsum : LiftedFunctionL f (p ⊔ q) + LiftedFunctionL f (p ⊓ q) ≠ ⊤ :=
      ne_top_of_le_ne_top (WithTop.add_ne_top.mpr ⟨hp', hq'⟩) h
    rw [WithTop.add_ne_top] at hsum
    exact ⟨hsum.1, hsum.2⟩
  · intro p hp
    have hp' : LiftedFunctionL f p ≠ ⊤ := hp
    constructor
    · show LiftedFunctionL f (fun v => p v + 1) ≠ ⊤
      have : (fun v => p v + 1) = p + 1 := rfl
      rw [this, lift_tr]; exact hp'
    · show LiftedFunctionL f (fun v => p v - 1) ≠ ⊤
      have : p = (fun v => p v - 1) + 1 := by funext v; simp
      rw [this, lift_tr] at hp'; exact hp'

/-- Subgradient of an L♮-convex function along the threshold chain of a point `x` of the convex
hull of its domain (Murota Thm 7.20 core): there is an affine minorant of `f` that is exact on all
roundings `⌈x - θ⌉`, `θ ∈ [0,1)`. -/
theorem subgrad {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ)
    (hf : LNaturalConvex f) (x : V → ℝ) (hx : x ∈ convexHull ℝ (IntEmbed (DomZ f))) :
    ∃ (ℓ : V → ℝ) (c : ℝ),
      (∀ y : V → ℤ, (((∑ v, ℓ v * (y v : ℝ)) + c : ℝ) : WithTop ℝ) ≤ f y) ∧
      ∀ θ : ℝ, 0 ≤ θ → θ < 1 →
        f (fun v => ⌈x v - θ⌉) =
          (((∑ v, ℓ v * ((⌈x v - θ⌉ : ℤ) : ℝ)) + c : ℝ) : WithTop ℝ) := by
  have hne : (DomZ f).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h] at hx
    simp [IntEmbed] at hx
  have hD := dom_lnat f hf hne
  have hch : ∀ θ : ℝ, 0 ≤ θ → θ < 1 → (fun v => ⌈x v - θ⌉) ∈ DomZ f := by
    intro θ h0 h1
    apply lnat_mem (DomZ f) hD x hx
    · intro v; have := Int.ceil_lt_add_one (x v - θ); linarith
    · intro v; have := Int.le_ceil (x v - θ); linarith
    · intro a b; have := Int.ceil_lt_add_one (x b - θ); have := Int.le_ceil (x a - θ); linarith
  set b : V → ℤ := fun v => ⌊x v⌋ with hb
  have hbD : b ∈ DomZ f := by
    apply lnat_mem (DomZ f) hD x hx
    · intro v; have := Int.floor_le (x v); simp only [hb]; linarith
    · intro v; have := Int.lt_floor_add_one (x v); simp only [hb]; linarith
    · intro a b'; have := Int.floor_le (x a); have := Int.lt_floor_add_one (x b')
      have := Int.floor_le (x b'); have := Int.lt_floor_add_one (x a)
      simp only [hb]; linarith
  obtain ⟨hsbf, -⟩ := hf
  set F := LiftedFunctionL f with hF
  have hsbf' : ∀ p q, F (p ⊔ q) + F (p ⊓ q) ≤ F p + F q := fun p q => hsbf p q
  set zt : Option V → ℤ := fun o => Option.elim o 0 b with hzt
  set zX : Finset (Option V) → Option V → ℤ := fun X o => zt o + if o ∈ X then 1 else 0 with hzX
  have hzX_sup : ∀ X Y, zX X ⊔ zX Y = zX (X ∪ Y) := by
    intro X Y; funext o
    simp only [hzX, Pi.sup_apply]
    by_cases hx : o ∈ X <;> by_cases hy : o ∈ Y <;> simp [hx, hy]
  have hzX_inf : ∀ X Y, zX X ⊓ zX Y = zX (X ∩ Y) := by
    intro X Y; funext o
    simp only [hzX, Pi.inf_apply]
    by_cases hx : o ∈ X <;> by_cases hy : o ∈ Y <;> simp [hx, hy]
  have hzX0 : zX ∅ = zt := by funext o; simp [hzX]
  have hzXu : zX Finset.univ = zt + 1 := by funext o; simp [hzX]
  have hFz : F zt = f b := lift_eval f b
  have hFzt : F zt ≠ ⊤ := by rw [hFz]; exact hbD
  have hFu : F (zt + 1) = F zt := by rw [hF]; exact lift_tr f zt
  set D : Set (Finset (Option V)) := {X | F (zX X) ≠ ⊤} with hDdef
  set r0 : ℝ := (F zt).untopD 0 with hr0
  set ρ : Finset (Option V) → ℝ := fun X => (F (zX X)).untopD 0 - r0 with hρ
  -- the chain
  set Xθ : ℝ → Finset (Option V) := fun θ =>
    Finset.univ.filter (fun o => Option.elim o False (fun v => θ < Int.fract (x v))) with hXθ
  have hzXθ : ∀ θ : ℝ, 0 ≤ θ → θ < 1 →
      zX (Xθ θ) = fun o => Option.elim o 0 (fun v => ⌈x v - θ⌉) := by
    intro θ h0 h1; funext o
    cases o with
    | none => simp [hzX, hzt, hXθ]
    | some v =>
      rw [Option.elim_some, ceil_sub_eq (x v) θ h0 h1]
      simp [hzX, hzt, hXθ, hb]
  have hFlift : ∀ y : V → ℤ, F (fun o => Option.elim o 0 y) = f y := lift_eval f
  have hFXθ : ∀ θ : ℝ, 0 ≤ θ → θ < 1 → F (zX (Xθ θ)) = f (fun v => ⌈x v - θ⌉) := by
    intro θ h0 h1
    rw [hzXθ θ h0 h1, hFlift]
  set C : Set (Finset (Option V)) := {X | ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧ X = Xθ θ} with hCdef
  have hCD : C ⊆ D := by
    rintro X ⟨θ, h0, h1, rfl⟩
    show F _ ≠ ⊤
    rw [hFXθ θ h0 h1]; exact hch θ h0 h1
  have hCchain : IsChain (· ⊆ ·) C := by
    rintro X ⟨θ1, -, -, rfl⟩ Y ⟨θ2, -, -, rfl⟩ -
    rcases le_total θ1 θ2 with h | h
    · right
      intro o ho
      simp only [hXθ, Finset.mem_filter, Finset.mem_univ, true_and] at ho ⊢
      cases o with
      | none => simp at ho
      | some v => simp only [Option.elim_some] at ho ⊢; linarith
    · left
      intro o ho
      simp only [hXθ, Finset.mem_filter, Finset.mem_univ, true_and] at ho ⊢
      cases o with
      | none => simp at ho
      | some v => simp only [Option.elim_some] at ho ⊢; linarith
  have hDcl : ∀ X ∈ D, ∀ Y ∈ D, X ∪ Y ∈ D ∧ X ∩ Y ∈ D := by
    intro X hX Y hY
    have h := hsbf' (zX X) (zX Y)
    rw [hzX_sup, hzX_inf] at h
    have hsum : F (zX (X ∪ Y)) + F (zX (X ∩ Y)) ≠ ⊤ :=
      ne_top_of_le_ne_top (WithTop.add_ne_top.mpr ⟨hX, hY⟩) h
    rw [WithTop.add_ne_top] at hsum
    exact ⟨hsum.1, hsum.2⟩
  obtain ⟨μ, hμD, hμC, hμW⟩ := greedy (Fintype.card (Option V)) Finset.univ le_rfl D ρ C
    (fun X _ => Finset.subset_univ X)
    (by show F _ ≠ ⊤; rw [hzX0]; exact hFzt)
    (by show F _ ≠ ⊤; rw [hzXu, hFu]; exact hFzt)
    hDcl
    (by
      intro X hX Y hY
      have h := hsbf' (zX X) (zX Y)
      rw [hzX_sup, hzX_inf] at h
      have hU := (hDcl X hX Y hY)
      have := wt_le_real hX hY hU.1 hU.2 h
      simp only [hρ]
      linarith)
    (by simp [hρ, hzX0, hr0])
    hCD hCchain
  have hρu : ρ Finset.univ = 0 := by simp only [hρ, hzXu, hFu, hr0, sub_self]
  -- the tilted function
  set L : (Option V → ℤ) → ℝ := fun w => ∑ o, μ o * (w o : ℝ) with hL
  set G : (Option V → ℤ) → WithTop ℝ := fun w => F w + ((-(L w) : ℝ) : WithTop ℝ) with hG
  have hLmod : ∀ p q : Option V → ℤ, L (p ⊔ q) + L (p ⊓ q) = L p + L q := by
    intro p q
    simp only [hL, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro o _
    have h : ((p ⊔ q) o : ℝ) + ((p ⊓ q) o : ℝ) = (p o : ℝ) + (q o : ℝ) := by
      have : (p ⊔ q) o + (p ⊓ q) o = p o + q o := by
        show max (p o) (q o) + min (p o) (q o) = p o + q o
        omega
      exact_mod_cast this
    linear_combination μ o * h
  have hGsub : ∀ p q, G (p ⊔ q) + G (p ⊓ q) ≤ G p + G q := by
    intro p q
    simp only [hG]
    rw [add_add_add_comm, add_add_add_comm (F p), ← WithTop.coe_add, ← WithTop.coe_add]
    have : -L (p ⊔ q) + -L (p ⊓ q) = -L p + -L q := by linarith [hLmod p q]
    rw [this]
    exact add_le_add (hsbf' p q) le_rfl
  have hLtr : ∀ p : Option V → ℤ, L (p + 1) = L p := by
    intro p
    simp only [hL, Pi.add_apply, Pi.one_apply, Int.cast_add, Int.cast_one, mul_add,
      Finset.sum_add_distrib, mul_one]
    have : ∑ o, μ o = 0 := by rw [hμW, hρu]
    rw [this, add_zero]
  have hGtr : ∀ p, G (p + 1) = G p := by
    intro p; simp only [hG, hLtr, hF, lift_tr]
  have hLX : ∀ X : Finset (Option V), L (zX X) = L zt + ∑ o ∈ X, μ o := by
    intro X
    simp only [hL, hzX, Int.cast_add, mul_add, Finset.sum_add_distrib]
    congr 1
    simp [Finset.sum_ite_mem]
  have hGz : G zt ≠ ⊤ := by
    simp only [hG]; exact WithTop.add_ne_top.mpr ⟨hFzt, WithTop.coe_ne_top⟩
  have hloc : ∀ X : Finset (Option V), G zt ≤ G (fun a => zt a + if a ∈ X then 1 else 0) := by
    intro X
    show G zt ≤ G (zX X)
    by_cases hX : X ∈ D
    · have h1 := hμD X hX
      have e1 : F (zX X) = (((F (zX X)).untopD 0 : ℝ) : WithTop ℝ) := wt_eq_coe hX
      simp only [hG]
      rw [e1, wt_eq_coe hFzt, ← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe, hLX X]
      simp only [hρ, hr0] at h1
      linarith
    · have : F (zX X) = ⊤ := by simpa [hDdef] using hX
      simp only [hG, this, WithTop.top_add]; exact le_top
  have hglob := loc_glob G hGsub hGtr zt hGz hloc
  have hLlift : ∀ y : V → ℤ, L (fun o => Option.elim o 0 y) = ∑ v, μ (some v) * (y v : ℝ) := by
    intro y; simp [hL, Fintype.sum_option]
  have hLz : L zt = ∑ v, μ (some v) * (b v : ℝ) := hLlift b
  have hfb : f b = ((r0 : ℝ) : WithTop ℝ) := by rw [← hFz]; exact wt_eq_coe hFzt
  refine ⟨fun v => μ (some v), r0 - ∑ v, μ (some v) * (b v : ℝ), ?_, ?_⟩
  · intro y
    have h := hglob (fun o => Option.elim o 0 y)
    simp only [hG] at h
    rw [hFlift y, hLlift y, hFlift b, hLlift b, hfb] at h
    by_cases hy : f y = ⊤
    · rw [hy]; exact le_top
    · rw [wt_eq_coe hy] at h ⊢
      rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe] at h
      rw [WithTop.coe_le_coe]
      linarith
  · intro θ h0 h1
    have hmem : Xθ θ ∈ C := ⟨θ, h0, h1, rfl⟩
    have e1 := hμC _ hmem
    have e2 := hLX (Xθ θ)
    rw [hzXθ θ h0 h1, hLlift (fun v => ⌈x v - θ⌉), hLz] at e2
    rw [← hFXθ θ h0 h1, wt_eq_coe (hCD hmem)]
    congr 1
    have e3 : (F (zX (Xθ θ))).untopD 0 = ρ (Xθ θ) + r0 := by simp only [hρ]; ring
    rw [e3, ← e1, e2]
    ring



theorem lnat_neg {V : Type*} [Fintype V] [DecidableEq V] (g : (V → ℤ) → WithTop ℝ)
    (hg : LNaturalConvex g) : LNaturalConvex (fun y => g (-y)) := by
  obtain ⟨hs, -⟩ := hg
  have e : ∀ w : Option V → ℤ,
      LiftedFunctionL (fun y => g (-y)) w = LiftedFunctionL g (-w) := by
    intro w; simp only [LiftedFunctionL]; congr 1; funext v; simp; ring
  refine ⟨?_, ⟨0, ?_⟩⟩
  · intro p q
    show LiftedFunctionL (fun y => g (-y)) (p ⊔ q) + LiftedFunctionL (fun y => g (-y)) (p ⊓ q) ≤
      LiftedFunctionL (fun y => g (-y)) p + LiftedFunctionL (fun y => g (-y)) q
    rw [e, e, e, e, neg_sup, neg_inf, add_comm (LiftedFunctionL g (-p ⊓ -q))]
    exact hs (-p) (-q)
  · intro p; rw [WithTop.coe_zero, add_zero]; exact lift_tr _ p

theorem infconv_facts {V : Type*} [Fintype V] [DecidableEq V] (g1 g2 : (V → ℤ) → WithTop ℝ)
    (hE : ∀ p, InfConvE g1 g2 p ≠ ⊥) (p : V → ℤ) :
    (∀ p1 p2, p = p1 + p2 → InfConv g1 g2 p ≤ g1 p1 + g2 p2) ∧
    (InfConv g1 g2 p ≠ ⊤ → ∀ ε : ℝ, 0 < ε → ∃ p1 p2, p = p1 + p2 ∧ g1 p1 ≠ ⊤ ∧ g2 p2 ≠ ⊤ ∧
       (g1 p1).untopD 0 + (g2 p2).untopD 0 ≤ (InfConv g1 g2 p).untopD 0 + ε) := by
  set T : Set (WithTop ℝ) := {L | ∃ p1 p2 : V → ℤ, p = p1 + p2 ∧ L = g1 p1 + g2 p2} with hT
  have hIC : InfConv g1 g2 p = sInf T := rfl
  obtain ⟨w, hw⟩ := WithBot.ne_bot_iff_exists.mp (hE p)
  have hbdd : BddBelow T := by
    refine ⟨w, ?_⟩
    rintro L ⟨p1, p2, hp, rfl⟩
    have h1 : InfConvE g1 g2 p ≤ ToEReal (g1 p1) + ToEReal (g2 p2) :=
      sInf_le ⟨p1, p2, hp, rfl⟩
    rw [← hw] at h1
    have h2 : ToEReal (g1 p1) + ToEReal (g2 p2) = ToEReal (g1 p1 + g2 p2) := rfl
    rw [h2] at h1
    exact WithBot.coe_le_coe.mp h1
  have hglb := WithTop.isGLB_sInf' hbdd
  refine ⟨?_, ?_⟩
  · intro p1 p2 hp
    rw [hIC]
    exact hglb.1 ⟨p1, p2, hp, rfl⟩
  · intro hne ε hε
    rw [hIC] at hne ⊢
    set r := (sInf T).untopD 0 with hr
    have hsr : sInf T = ((r : ℝ) : WithTop ℝ) := wt_eq_coe hne
    have hnot : ¬ (((r + ε : ℝ) : WithTop ℝ) ∈ lowerBounds T) := by
      intro h
      have := hglb.2 h
      rw [hsr, WithTop.coe_le_coe] at this
      linarith
    simp only [lowerBounds, Set.mem_ofPred_eq, not_forall, not_le] at hnot
    obtain ⟨L, ⟨p1, p2, hp, rfl⟩, hlt⟩ := hnot
    have hne' : g1 p1 + g2 p2 ≠ ⊤ := ne_top_of_lt hlt
    rw [WithTop.add_ne_top] at hne'
    refine ⟨p1, p2, hp, hne'.1, hne'.2, ?_⟩
    have e1 := wt_eq_coe hne'.1
    have e2 := wt_eq_coe hne'.2
    rw [e1, e2, ← WithTop.coe_add, WithTop.coe_lt_coe] at hlt
    linarith

theorem rep_of_family {β : Type*} [DecidableEq β] (N : Finset β) {ι : Type*} (t : Finset ι)
    (w : ι → ℝ) (u : ι → β) (hw0 : ∀ i ∈ t, 0 ≤ w i) (hw1 : ∑ i ∈ t, w i = 1)
    (hu : ∀ i ∈ t, u i ∈ N) :
    ∃ lam : β → ℝ, (∀ z ∈ N, 0 ≤ lam z) ∧ ∑ z ∈ N, lam z = 1 ∧
      ∀ h : β → ℝ, ∑ z ∈ N, lam z * h z = ∑ i ∈ t, w i * h (u i) := by
  refine ⟨fun z => ∑ i ∈ t.filter (fun i => u i = z), w i, ?_, ?_, ?_⟩
  · intro z _
    exact Finset.sum_nonneg (fun i hi => hw0 i (Finset.mem_filter.mp hi).1)
  · rw [Finset.sum_fiberwise_of_maps_to hu]; exact hw1
  · intro h
    have : ∀ z, (∑ i ∈ t.filter (fun i => u i = z), w i) * h z =
        ∑ i ∈ t.filter (fun i => u i = z), w i * h (u i) := by
      intro z; rw [Finset.sum_mul]; apply Finset.sum_congr rfl
      intro i hi; rw [(Finset.mem_filter.mp hi).2]
    simp only [this]
    exact Finset.sum_fiberwise_of_maps_to hu (fun i => w i * h (u i))

theorem sum_swap {V : Type*} [Fintype V] {β : Type*} (S : Finset β) (lam : β → ℝ) (κ : V → ℝ)
    (d : β → V → ℝ) :
    ∑ v, κ v * (∑ y ∈ S, lam y * d y v) = ∑ y ∈ S, lam y * ∑ v, κ v * d y v := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro y _
  apply Finset.sum_congr rfl; intro v _
  ring

/-- Core estimate: every finite representation of `p` over `dom g` is beaten, up to `ε`, by a
representation over `N(p) ∩ dom g`. -/
theorem key {V : Type*} [Fintype V] [DecidableEq V] (g g1 g2 : (V → ℤ) → WithTop ℝ)
    (h1 : LNaturalConvex g1) (h2 : LNaturalConvex g2) (hE : ∀ p, InfConvE g1 g2 p ≠ ⊥)
    (hg : g = InfConv g1 g2) (p : V → ℝ) (S : Finset (V → ℤ)) (lam : (V → ℤ) → ℝ)
    (hl0 : ∀ y ∈ S, 0 ≤ lam y) (hl1 : ∑ y ∈ S, lam y = 1) (hSd : ∀ y ∈ S, y ∈ DomZ g)
    (hp : ∀ v, ∑ y ∈ S, lam y * (y v : ℝ) = p v) (ε : ℝ) (hε : 0 < ε) :
    ∃ (ι : Type) (t : Finset ι) (w : ι → ℝ) (u : ι → (V → ℤ)),
      (∀ i ∈ t, 0 ≤ w i) ∧ ∑ i ∈ t, w i = 1 ∧
      (∀ i ∈ t, u i ∈ IntegralNeighborhoodFinset p ∧ u i ∈ DomZ g) ∧
      (∀ v, ∑ i ∈ t, w i * (u i v : ℝ) = p v) ∧
      ∑ i ∈ t, w i * (g (u i)).untopD 0 ≤ ∑ y ∈ S, lam y * (g y).untopD 0 + ε := by
  have hfac := infconv_facts g1 g2 hE
  have hsplit : ∀ y, ∃ a b : V → ℤ, y ∈ S → (y = a + b ∧ g1 a ≠ ⊤ ∧ g2 b ≠ ⊤ ∧
      (g1 a).untopD 0 + (g2 b).untopD 0 ≤ (g y).untopD 0 + ε) := by
    intro y
    by_cases hy : y ∈ S
    · have hne : InfConv g1 g2 y ≠ ⊤ := by rw [← hg]; exact hSd y hy
      obtain ⟨a, b, h⟩ := (hfac y).2 hne ε hε
      exact ⟨a, b, fun _ => by rw [hg]; exact h⟩
    · exact ⟨0, 0, fun h => absurd h hy⟩
  choose a b hab using hsplit
  set x1 : V → ℝ := fun v => ∑ y ∈ S, lam y * (a y v : ℝ) with hx1
  set x2 : V → ℝ := fun v => ∑ y ∈ S, lam y * (b y v : ℝ) with hx2
  have hx12 : ∀ v, x1 v + x2 v = p v := by
    intro v; rw [← hp v]; simp only [hx1, hx2, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro y hy
    have hv : y v = a y v + b y v := congrFun (hab y hy).1 v
    have hv' : (y v : ℝ) = (a y v : ℝ) + (b y v : ℝ) := by exact_mod_cast hv
    rw [hv']; ring
  have hconv : ∀ (h : (V → ℤ) → WithTop ℝ) (c : (V → ℤ) → (V → ℤ)), (∀ y ∈ S, c y ∈ DomZ h) →
      (fun v => ∑ y ∈ S, lam y * (c y v : ℝ)) ∈ convexHull ℝ (IntEmbed (DomZ h)) := by
    intro h c hc
    have := (convex_convexHull ℝ (IntEmbed (DomZ h))).sum_mem hl0 hl1
      (z := fun y => fun v => (c y v : ℝ))
      (fun y hy => subset_convexHull ℝ _ ⟨c y, hc y hy, rfl⟩)
    convert this using 1
    funext v; simp [Finset.sum_apply]
  have hx1c := hconv g1 a (fun y hy => (hab y hy).2.1)
  set g2' : (V → ℤ) → WithTop ℝ := fun y => g2 (-y) with hg2'
  have hx2c : (fun v => -x2 v) ∈ convexHull ℝ (IntEmbed (DomZ g2')) := by
    have := hconv g2' (fun y => -b y) (fun y hy => by
      show g2 (- -b y) ≠ ⊤; rw [neg_neg]; exact (hab y hy).2.2.1)
    convert this using 1
    funext v; simp [hx2, Finset.sum_neg_distrib]
  obtain ⟨ℓ1, c1, hle1, heq1⟩ := subgrad g1 h1 x1 hx1c
  obtain ⟨ℓ2, c2, hle2, heq2⟩ := subgrad g2' (lnat_neg g2 h2) (fun v => -x2 v) hx2c
  set q : V ⊕ V → ℝ := Sum.elim x1 (fun v => -x2 v) with hq
  have hqh := round_hull _ q le_rfl
  rw [convexHull_eq] at hqh
  obtain ⟨ι, t, w, z, hw0, hw1, hz, hcm⟩ := hqh
  rw [Finset.centerMass_eq_of_sum_1 _ _ hw1] at hcm
  have hθ : ∀ i, ∃ θ : ℝ, i ∈ t → (0 ≤ θ ∧ θ < 1 ∧ z i = fun j => ((⌈q j - θ⌉ : ℤ) : ℝ)) := by
    intro i
    by_cases hi : i ∈ t
    · obtain ⟨θ, h0, h1, he⟩ := hz i hi
      exact ⟨θ, fun _ => ⟨h0, h1, he⟩⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose θ hθ using hθ
  have hcoord : ∀ j, ∑ i ∈ t, w i * ((⌈q j - θ i⌉ : ℤ) : ℝ) = q j := by
    intro j
    have := congrFun hcm j
    rw [Finset.sum_apply] at this
    calc ∑ i ∈ t, w i * ((⌈q j - θ i⌉ : ℤ) : ℝ) = ∑ c ∈ t, (w c • z c) j := by
          apply Finset.sum_congr rfl; intro i hi; rw [(hθ i hi).2.2]; simp [smul_eq_mul]
      _ = q j := this
  set c1p : ι → V → ℤ := fun i v => ⌈x1 v - θ i⌉ with hc1p
  set c2p : ι → V → ℤ := fun i v => ⌈-x2 v - θ i⌉ with hc2p
  set u : ι → V → ℤ := fun i => c1p i - c2p i with hu
  have hs1 : ∀ v, ∑ i ∈ t, w i * (c1p i v : ℝ) = x1 v := fun v => by
    simpa [hq] using hcoord (Sum.inl v)
  have hs2 : ∀ v, ∑ i ∈ t, w i * (c2p i v : ℝ) = -x2 v := fun v => by
    simpa [hq] using hcoord (Sum.inr v)
  have hval : ∀ i ∈ t, g (u i) ≤ g1 (c1p i) + g2' (c2p i) := by
    intro i _
    rw [hg]
    exact (hfac (u i)).1 (c1p i) (-(c2p i)) (by funext v; simp [hu, sub_eq_add_neg])
  have hui : ∀ i ∈ t, u i ∈ DomZ g ∧ (g (u i)).untopD 0 ≤
      (∑ v, ℓ1 v * (c1p i v : ℝ) + c1) + (∑ v, ℓ2 v * (c2p i v : ℝ) + c2) := by
    intro i hi
    obtain ⟨h0, h1', -⟩ := hθ i hi
    have e1 : g1 (c1p i) = (((∑ v, ℓ1 v * (c1p i v : ℝ)) + c1 : ℝ) : WithTop ℝ) :=
      heq1 (θ i) h0 h1'
    have e2 : g2' (c2p i) = (((∑ v, ℓ2 v * (c2p i v : ℝ)) + c2 : ℝ) : WithTop ℝ) :=
      heq2 (θ i) h0 h1'
    have hv := hval i hi
    rw [e1, e2, ← WithTop.coe_add] at hv
    have hne : g (u i) ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hv
    refine ⟨hne, ?_⟩
    rw [wt_eq_coe hne, WithTop.coe_le_coe] at hv
    exact hv
  have hN : ∀ i ∈ t, u i ∈ IntegralNeighborhoodFinset p := by
    intro i _
    simp only [IntegralNeighborhoodFinset, Fintype.mem_piFinset, Finset.mem_Icc]
    intro v
    have hpv : p v = x1 v + x2 v := (hx12 v).symm
    have a1 := Int.ceil_lt_add_one (x1 v - θ i); have a2 := Int.le_ceil (x1 v - θ i)
    have a3 := Int.ceil_lt_add_one (-x2 v - θ i); have a4 := Int.le_ceil (-x2 v - θ i)
    have lo : ⌊p v⌋ < u i v + 1 := by
      rw [Int.floor_lt]; simp only [hu, hc1p, hc2p, Pi.sub_apply]; push_cast; linarith
    have hi' : u i v - 1 < ⌈p v⌉ := by
      rw [Int.lt_ceil]; simp only [hu, hc1p, hc2p, Pi.sub_apply]; push_cast; linarith
    constructor <;> omega
  have hsum_u : ∀ v, ∑ i ∈ t, w i * (u i v : ℝ) = p v := by
    intro v
    have : ∀ i, (u i v : ℝ) = (c1p i v : ℝ) - (c2p i v : ℝ) := by intro i; simp [hu]
    simp only [this, mul_sub, Finset.sum_sub_distrib, hs1, hs2]
    linarith [hx12 v]
  have hlow : (∑ v, ℓ1 v * x1 v + c1) + (∑ v, ℓ2 v * (-x2 v) + c2) ≤
      ∑ y ∈ S, lam y * (g y).untopD 0 + ε := by
    have hyb : ∀ y ∈ S, (∑ v, ℓ1 v * (a y v : ℝ) + c1) + (∑ v, ℓ2 v * (-(b y v : ℝ)) + c2) ≤
        (g y).untopD 0 + ε := by
      intro y hy
      obtain ⟨-, ha, hb, hle⟩ := hab y hy
      have i1 := hle1 (a y)
      have i2 := hle2 (-b y)
      rw [wt_eq_coe ha, WithTop.coe_le_coe] at i1
      have hb' : g2' (-b y) ≠ ⊤ := by show g2 (- -b y) ≠ ⊤; rw [neg_neg]; exact hb
      rw [wt_eq_coe hb', WithTop.coe_le_coe] at i2
      have e : (g2' (-b y)).untopD 0 = (g2 (b y)).untopD 0 := by simp [hg2']
      simp only [Pi.neg_apply, Int.cast_neg] at i2
      linarith
    have eq1 := sum_swap S lam ℓ1 (fun y v => (a y v : ℝ))
    have eq2 := sum_swap S lam ℓ2 (fun y v => -(b y v : ℝ))
    have hx2' : ∀ v, -x2 v = ∑ y ∈ S, lam y * (-(b y v : ℝ)) := by
      intro v; simp [hx2, Finset.sum_neg_distrib]
    calc (∑ v, ℓ1 v * x1 v + c1) + (∑ v, ℓ2 v * (-x2 v) + c2)
        = ∑ y ∈ S, lam y * ((∑ v, ℓ1 v * (a y v : ℝ) + c1) +
            (∑ v, ℓ2 v * (-(b y v : ℝ)) + c2)) := by
          simp only [hx2']
          simp only [hx1] at eq1 ⊢
          rw [eq1, eq2]
          simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hl1, one_mul]
      _ ≤ ∑ y ∈ S, lam y * ((g y).untopD 0 + ε) :=
          Finset.sum_le_sum (fun y hy => mul_le_mul_of_nonneg_left (hyb y hy) (hl0 y hy))
      _ = _ := by
          rw [Finset.sum_congr rfl (fun y _ => mul_add (lam y) _ _), Finset.sum_add_distrib,
            ← Finset.sum_mul, hl1, one_mul]
  refine ⟨ι, t, w, u, hw0, hw1, fun i hi => ⟨hN i hi, (hui i hi).1⟩, hsum_u, ?_⟩
  calc ∑ i ∈ t, w i * (g (u i)).untopD 0
      ≤ ∑ i ∈ t, w i * ((∑ v, ℓ1 v * (c1p i v : ℝ) + c1) + (∑ v, ℓ2 v * (c2p i v : ℝ) + c2)) :=
        Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hui i hi).2 (hw0 i hi))
    _ = (∑ v, ℓ1 v * x1 v + c1) + (∑ v, ℓ2 v * (-x2 v) + c2) := by
        have e1 := sum_swap t w ℓ1 (fun i v => (c1p i v : ℝ))
        have e2 := sum_swap t w ℓ2 (fun i v => (c2p i v : ℝ))
        simp only [hs1, hs2] at e1 e2
        rw [e1, e2]
        simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hw1, one_mul]
    _ ≤ _ := hlow

theorem final {V : Type*} [Fintype V] [DecidableEq V] (g : (V → ℤ) → WithTop ℝ)
    (hkey : ∀ (p : V → ℝ) (S : Finset (V → ℤ)) (lam : (V → ℤ) → ℝ), (∀ y ∈ S, 0 ≤ lam y) →
      ∑ y ∈ S, lam y = 1 → (∀ y ∈ S, y ∈ DomZ g) → (∀ v, ∑ y ∈ S, lam y * (y v : ℝ) = p v) →
      ∀ ε : ℝ, 0 < ε → ∃ (ι : Type) (t : Finset ι) (w : ι → ℝ) (u : ι → (V → ℤ)),
        (∀ i ∈ t, 0 ≤ w i) ∧ ∑ i ∈ t, w i = 1 ∧
        (∀ i ∈ t, u i ∈ IntegralNeighborhoodFinset p ∧ u i ∈ DomZ g) ∧
        (∀ v, ∑ i ∈ t, w i * (u i v : ℝ) = p v) ∧
        ∑ i ∈ t, w i * (g (u i)).untopD 0 ≤ ∑ y ∈ S, lam y * (g y).untopD 0 + ε) :
    IsIntegrallyConvexFunction g := by
  intro p
  set N := Finset.filter (fun y => y ∈ DomZ g) (IntegralNeighborhoodFinset p) with hN
  set BN : Set (WithTop ℝ) := {L | ∃ lam : (V → ℤ) → ℝ, (∀ y ∈ N, 0 ≤ lam y) ∧
    (∑ y ∈ N, lam y = 1) ∧ (∀ y ∈ N, y ∈ DomZ g) ∧ (∀ v, ∑ y ∈ N, lam y * (y v : ℝ) = p v) ∧
    L = ((∑ y ∈ N, lam y * (g y).untopD 0 : ℝ) : WithTop ℝ)} with hBN
  have hR : ConvexClosureValOn g N p = sInf BN := rfl
  set M : ℝ := ∑ z ∈ N, |(g z).untopD 0| with hM
  have hbddN : BddBelow BN := by
    refine ⟨((-M : ℝ) : WithTop ℝ), ?_⟩
    rintro L ⟨lam, h0, h1, -, -, rfl⟩
    rw [WithTop.coe_le_coe]
    have hz : ∀ z ∈ N, lam z * (-M) ≤ lam z * (g z).untopD 0 := by
      intro z hz
      apply mul_le_mul_of_nonneg_left _ (h0 z hz)
      have := Finset.single_le_sum (f := fun z => |(g z).untopD 0|) (fun z _ => abs_nonneg _) hz
      have := neg_abs_le ((g z).untopD 0)
      linarith
    calc -M = ∑ z ∈ N, lam z * (-M) := by rw [← Finset.sum_mul, h1, one_mul]
      _ ≤ _ := Finset.sum_le_sum hz
  have hglbN := WithTop.isGLB_sInf' hbddN
  have hlow : ∀ (S : Finset (V → ℤ)) (lam : (V → ℤ) → ℝ), (∀ y ∈ S, 0 ≤ lam y) →
      ∑ y ∈ S, lam y = 1 → (∀ y ∈ S, y ∈ DomZ g) → (∀ v, ∑ y ∈ S, lam y * (y v : ℝ) = p v) →
      sInf BN ≤ ((∑ y ∈ S, lam y * (g y).untopD 0 : ℝ) : WithTop ℝ) := by
    intro S lam h0 h1 hd hrep
    have hε : ∀ ε : ℝ, 0 < ε →
        sInf BN ≤ ((∑ y ∈ S, lam y * (g y).untopD 0 + ε : ℝ) : WithTop ℝ) := by
      intro ε hε
      obtain ⟨ι, t, w, u, hw0, hw1, hu, hsum, hval⟩ := hkey p S lam h0 h1 hd hrep ε hε
      obtain ⟨lam', hl0, hl1, hlh⟩ := rep_of_family N t w u hw0 hw1
        (fun i hi => Finset.mem_filter.mpr ⟨(hu i hi).1, (hu i hi).2⟩)
      have hmem : ((∑ z ∈ N, lam' z * (g z).untopD 0 : ℝ) : WithTop ℝ) ∈ BN := by
        refine ⟨lam', hl0, hl1, fun y hy => (Finset.mem_filter.mp hy).2, ?_, rfl⟩
        intro v; rw [hlh (fun z => (z v : ℝ))]; exact hsum v
      calc sInf BN ≤ _ := hglbN.1 hmem
        _ ≤ _ := by rw [WithTop.coe_le_coe, hlh (fun z => (g z).untopD 0)]; exact hval
    by_cases htop : sInf BN = ⊤
    · exfalso
      have := hε 1 one_pos
      rw [htop] at this
      exact WithTop.coe_ne_top (top_le_iff.mp this)
    · rw [wt_eq_coe htop, WithTop.coe_le_coe]
      apply le_of_forall_pos_le_add
      intro ε hε'
      have := hε ε hε'
      rw [wt_eq_coe htop, WithTop.coe_le_coe] at this
      exact this
  have hlbS : ∀ S : Finset (V → ℤ), (∀ y ∈ S, y ∈ DomZ g) →
      sInf BN ≤ ConvexClosureValOn g S p := by
    intro S _
    unfold ConvexClosureValOn
    have hlb : sInf BN ∈ lowerBounds {L : WithTop ℝ | ∃ lam : (V → ℤ) → ℝ,
        (∀ y ∈ S, 0 ≤ lam y) ∧ (∑ y ∈ S, lam y = 1) ∧ (∀ y ∈ S, y ∈ DomZ g) ∧
        (∀ v, ∑ y ∈ S, lam y * (y v : ℝ) = p v) ∧
        L = ((∑ y ∈ S, lam y * (g y).untopD 0 : ℝ) : WithTop ℝ)} := by
      rintro L ⟨lam, h0, h1, hd, hrep, rfl⟩
      exact hlow S lam h0 h1 hd hrep
    exact (WithTop.isGLB_sInf' ⟨_, hlb⟩).2 hlb
  have hA : IsGLB {L : WithTop ℝ | ∃ S : Finset (V → ℤ), (∀ y ∈ S, y ∈ DomZ g) ∧
      L = ConvexClosureValOn g S p} (sInf BN) := by
    refine IsLeast.isGLB ⟨⟨N, fun y hy => (Finset.mem_filter.mp hy).2, hR.symm⟩, ?_⟩
    rintro L ⟨S, hS, rfl⟩
    exact hlbS S hS
  have hA' := WithTop.isGLB_sInf' ⟨_, hA.1⟩
  rw [hR]
  exact hA'.unique hA

theorem func_conj {V : Type*} [Fintype V] [DecidableEq V] :
    ∀ g : (V → ℤ) → WithTop ℝ, LNat2Convex g → IsIntegrallyConvexFunction g := by
  rintro g ⟨g1, g2, h1, h2, hE, hg⟩
  apply final g
  intro p S lam h0 h1' hd hrep ε hε
  exact key g g1 g2 h1 h2 hE hg p S lam h0 h1' hd hrep ε hε

end P7d18

open Classical DiscreteConvex.ConjugacyDualityC in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] :
    (∀ g : (V → ℤ) → WithTop ℝ, LNat2Convex g → IsIntegrallyConvexFunction g) ∧
    (∀ D : Set (V → ℤ), LNat2ConvexSet D → IsIntegrallyConvex D) := by
  exact ⟨P7d18.func_conj, P7d18.set_conj⟩
