-- Prove2me | solution 1 for DiscreteConvex.IntegralConvexity.integrally_convex_iff_restriction
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-02T12:13:49.112021+00:00
-- url     : https://prove2.me/submissions/7fd46507-62b7-4943-b6f4-0030ed418441

import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexity_IntegrallyConvex
import Definitions.Def_DiscreteConvex_IntegralConvexity_Restrict

namespace DiscreteConvex.IntegralConvexity.Prop319Aux

open DiscreteConvex.IntegralConvexity

variable {n : ℕ}

/-- Real embedding of an integer point. -/
abbrev toR (y : Fin n → ℤ) : Fin n → ℝ := fun i => (y i : ℝ)

/-- Affine function `α + ⟨p, v⟩`. -/
abbrev aff (p : Fin n → ℝ) (α : ℝ) (v : Fin n → ℝ) : ℝ := α + ∑ i, p i * v i

theorem le_localExt {f : (Fin n → ℤ) → WithTop ℝ} {v : Fin n → ℝ} (p : Fin n → ℝ) (α : ℝ)
    (h : ∀ y ∈ IntegralNeighborhood v, ((aff p α (toR y) : ℝ) : EReal) ≤ WithBot.some (f y)) :
    ((aff p α v : ℝ) : EReal) ≤ LocalConvexExtension f v :=
  le_sSup ⟨p, α, h, rfl⟩

theorem le_convexClosure {f : (Fin n → ℤ) → WithTop ℝ} {v : Fin n → ℝ} (p : Fin n → ℝ) (α : ℝ)
    (h : ∀ y, ((aff p α (toR y) : ℝ) : EReal) ≤ WithBot.some (f y)) :
    ((aff p α v : ℝ) : EReal) ≤ ConvexClosure f v :=
  le_sSup ⟨p, α, h, rfl⟩

theorem mem_integralNeighborhood_self (y : Fin n → ℤ) : y ∈ IntegralNeighborhood (toR y) := by
  intro i
  simp

theorem localExt_le_self (f : (Fin n → ℤ) → WithTop ℝ) (y : Fin n → ℤ) :
    LocalConvexExtension f (toR y) ≤ WithBot.some (f y) := by
  apply sSup_le
  rintro v ⟨p, α, h, rfl⟩
  exact h y (mem_integralNeighborhood_self y)

theorem convexClosure_le_localExt (f : (Fin n → ℤ) → WithTop ℝ) (v : Fin n → ℝ) :
    ConvexClosure f v ≤ LocalConvexExtension f v := by
  apply sSup_le
  rintro w ⟨p, α, h, rfl⟩
  exact le_sSup ⟨p, α, fun y _ => h y, rfl⟩

theorem localExt_restrict_eq {f : (Fin n → ℤ) → WithTop ℝ} {a b : Fin n → ℤ} {w : Fin n → ℝ}
    (hw : IntegralNeighborhood w ⊆ IntegerInterval a b) :
    LocalConvexExtension (Restrict f a b) w = LocalConvexExtension f w := by
  unfold LocalConvexExtension
  congr 1
  ext v
  constructor
  · rintro ⟨p, α, h, rfl⟩
    refine ⟨p, α, fun y hy => ?_, rfl⟩
    have := h y hy
    simpa [Restrict, hw hy] using this
  · rintro ⟨p, α, h, rfl⟩
    refine ⟨p, α, fun y hy => ?_, rfl⟩
    have := h y hy
    simpa [Restrict, hw hy] using this

theorem integerInterval_finite (a b : Fin n → ℤ) : (IntegerInterval a b).Finite := by
  have : IntegerInterval a b = Set.Icc a b := by
    ext y
    simp [IntegerInterval, Set.mem_Icc, Pi.le_def, forall_and]
  rw [this]
  exact Set.finite_Icc a b

theorem exists_const_le_box (f : (Fin n → ℤ) → WithTop ℝ) (a b : Fin n → ℤ) :
    ∃ c : ℝ, ∀ y ∈ IntegerInterval a b, (c : WithTop ℝ) ≤ f y := by
  obtain ⟨c, hc⟩ := ((integerInterval_finite a b).image (fun y => (f y).untopD 0)).bddBelow
  refine ⟨c, fun y hy => ?_⟩
  have := hc ⟨y, hy, rfl⟩
  cases h : f y with
  | top => exact le_top
  | coe t => simp [h] at this; exact_mod_cast this

/-- If `g` is `+∞` off a box and `x` lies strictly outside the box, `ḡ(x) = +∞`. -/
theorem convexClosure_eq_top_of_outside (g : (Fin n → ℤ) → WithTop ℝ) (a b : Fin n → ℤ)
    (hg : ∀ y, y ∉ IntegerInterval a b → g y = ⊤) (x : Fin n → ℝ) (i : Fin n)
    (hx : (b i : ℝ) < x i ∨ x i < (a i : ℝ)) : ConvexClosure g x = ⊤ := by
  obtain ⟨c, hc⟩ := exists_const_le_box g a b
  rw [EReal.eq_top_iff_forall_lt]
  intro M
  rcases hx with hx | hx
  · have hpos : 0 < x i - (b i : ℝ) := by linarith
    set K : ℝ := (|M - c| + 1) / (x i - b i)
    have hK : 0 ≤ K := by positivity
    have hKx : K * (x i - b i) = |M - c| + 1 := by
      simp only [K]; field_simp
    refine lt_of_lt_of_le ?_ (le_convexClosure (fun j => if j = i then K else 0) (c - K * b i) ?_)
    · simp only [aff, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      apply EReal.coe_lt_coe_iff.mpr
      have := le_abs_self (M - c)
      nlinarith
    · intro y
      by_cases hy : y ∈ IntegerInterval a b
      · simp only [aff, toR, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        have h1 : (y i : ℝ) ≤ b i := by exact_mod_cast (hy i).2
        have h2 := hc y hy
        have h3 : ((c - K * b i + K * (y i : ℝ) : ℝ) : EReal) ≤ ((c : ℝ) : EReal) := by
          apply EReal.coe_le_coe_iff.mpr; nlinarith
        exact le_trans h3 (WithBot.coe_le_coe.mpr h2)
      · rw [hg y hy]; exact le_top
  · have hpos : 0 < (a i : ℝ) - x i := by linarith
    set K : ℝ := (|M - c| + 1) / (a i - x i)
    have hK : 0 ≤ K := by positivity
    have hKx : K * (a i - x i) = |M - c| + 1 := by
      simp only [K]; field_simp
    refine lt_of_lt_of_le ?_ (le_convexClosure (fun j => if j = i then -K else 0) (c + K * a i) ?_)
    · simp only [aff, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      apply EReal.coe_lt_coe_iff.mpr
      have := le_abs_self (M - c)
      nlinarith
    · intro y
      by_cases hy : y ∈ IntegerInterval a b
      · simp only [aff, toR, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        have h1 : (a i : ℝ) ≤ y i := by exact_mod_cast (hy i).1
        have h2 := hc y hy
        have h3 : ((c + K * a i + -K * (y i : ℝ) : ℝ) : EReal) ≤ ((c : ℝ) : EReal) := by
          apply EReal.coe_le_coe_iff.mpr; nlinarith
        exact le_trans h3 (WithBot.coe_le_coe.mpr h2)
      · rw [hg y hy]; exact le_top

/-- From integral convexity of a restriction: a value below `f̃(w)` is beaten by an affine
minorant of `f` on the whole box, provided `N(w)` lies in the box. -/
theorem exists_box_minorant {f : (Fin n → ℤ) → WithTop ℝ} {a b : Fin n → ℤ}
    (hB : IntegrallyConvex (Restrict f a b)) {w : Fin n → ℝ}
    (hw : IntegralNeighborhood w ⊆ IntegerInterval a b) {r : EReal}
    (hr : r < LocalConvexExtension f w) :
    ∃ p α, (∀ y ∈ IntegerInterval a b, ((aff p α (toR y) : ℝ) : EReal) ≤ WithBot.some (f y)) ∧
      r < ((aff p α w : ℝ) : EReal) := by
  rw [← localExt_restrict_eq hw, hB w] at hr
  obtain ⟨v, ⟨p, α, h, rfl⟩, hv⟩ := lt_sSup_iff.mp hr
  refine ⟨p, α, fun y hy => ?_, hv⟩
  have := h y
  simpa [Restrict, hy] using this

theorem convexClosure_mono {f g : (Fin n → ℤ) → WithTop ℝ} (h : ∀ y, f y ≤ g y)
    (x : Fin n → ℝ) : ConvexClosure f x ≤ ConvexClosure g x := by
  apply sSup_le_sSup
  rintro v ⟨p, α, hp, rfl⟩
  exact ⟨p, α, fun y => (hp y).trans (WithBot.coe_le_coe.mpr (h y)), rfl⟩

/-- Forward direction of Proposition 3.19. -/
theorem restrict_integrallyConvex {f : (Fin n → ℤ) → WithTop ℝ} (hf : IntegrallyConvex f)
    (a b : Fin n → ℤ) : IntegrallyConvex (Restrict f a b) := by
  intro x
  apply le_antisymm _ (convexClosure_le_localExt _ x)
  by_cases hN : IntegralNeighborhood x ⊆ IntegerInterval a b
  · rw [localExt_restrict_eq hN, hf x]
    apply convexClosure_mono
    intro y
    unfold Restrict
    split_ifs
    · exact le_rfl
    · exact le_top
  · obtain ⟨y, hyN, hyB⟩ := Set.not_subset.mp hN
    simp only [IntegerInterval, Set.mem_setOf_eq, not_forall, not_and_or, not_le] at hyB
    obtain ⟨i, hi⟩ := hyB
    have hx : (b i : ℝ) < x i ∨ x i < (a i : ℝ) := by
      rcases hi with hi | hi
      · right
        have : ⌊x i⌋ < a i := lt_of_le_of_lt (hyN i).1 hi
        exact Int.floor_lt.mp this
      · left
        have : b i < ⌈x i⌉ := lt_of_lt_of_le hi (hyN i).2
        exact Int.lt_ceil.mp this
    rw [convexClosure_eq_top_of_outside (Restrict f a b) a b
      (fun y hy => by simp [Restrict, hy]) x i hx]
    exact le_top

theorem nbhd_subset_box {w : Fin n → ℝ} {A B : Fin n → ℤ} (hA : ∀ i, (A i : ℝ) ≤ w i)
    (hB : ∀ i, w i ≤ B i) : IntegralNeighborhood w ⊆ IntegerInterval A B := by
  intro y hy i
  exact ⟨(Int.le_floor.mpr (hA i)).trans (hy i).1, (hy i).2.trans (Int.ceil_le.mpr (hB i))⟩

theorem aff_combo (p : Fin n → ℝ) (α : ℝ) (u v : Fin n → ℝ) (s t : ℝ) (hst : s + t = 1) :
    aff p α (s • u + t • v) = s * aff p α u + t * aff p α v := by
  simp only [aff, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have : ∑ i, p i * (s * u i + t * v i) = s * ∑ i, p i * u i + t * ∑ i, p i * v i := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [this]
  have : α = s * α + t * α := by rw [← add_mul, hst, one_mul]
  linarith

/-- The (real) epigraph of the local convex extension. -/
def epiLocal (f : (Fin n → ℤ) → WithTop ℝ) : Set ((Fin n → ℝ) × ℝ) :=
  {q | LocalConvexExtension f q.1 ≤ ((q.2 : ℝ) : EReal)}

theorem convex_epiLocal {f : (Fin n → ℤ) → WithTop ℝ}
    (hB : ∀ a b : Fin n → ℤ, IntegrallyConvex (Restrict f a b)) :
    Convex ℝ (epiLocal f) := by
  intro q1 hq1 q2 hq2 s t hs ht hst
  simp only [epiLocal, Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul] at hq1 hq2 ⊢
  set z : Fin n → ℝ := s • q1.1 + t • q2.1 with hz
  by_contra hcon
  push_neg at hcon
  set A : Fin n → ℤ := fun i => min ⌊q1.1 i⌋ ⌊q2.1 i⌋
  set B : Fin n → ℤ := fun i => max ⌈q1.1 i⌉ ⌈q2.1 i⌉
  have hA1 : ∀ i, (A i : ℝ) ≤ q1.1 i := fun i => by
    simp only [A, Int.cast_min]; exact (min_le_left _ _).trans (Int.floor_le _)
  have hA2 : ∀ i, (A i : ℝ) ≤ q2.1 i := fun i => by
    simp only [A, Int.cast_min]; exact (min_le_right _ _).trans (Int.floor_le _)
  have hB1 : ∀ i, q1.1 i ≤ B i := fun i => by
    simp only [B, Int.cast_max]; exact (Int.le_ceil _).trans (le_max_left _ _)
  have hB2 : ∀ i, q2.1 i ≤ B i := fun i => by
    simp only [B, Int.cast_max]; exact (Int.le_ceil _).trans (le_max_right _ _)
  have hzA : ∀ i, (A i : ℝ) ≤ z i := fun i => by
    simp only [hz, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have e : s * (A i : ℝ) + t * (A i : ℝ) = A i := by rw [← add_mul, hst, one_mul]
    nlinarith [mul_le_mul_of_nonneg_left (hA1 i) hs, mul_le_mul_of_nonneg_left (hA2 i) ht]
  have hzB : ∀ i, z i ≤ B i := fun i => by
    simp only [hz, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have e : s * (B i : ℝ) + t * (B i : ℝ) = B i := by rw [← add_mul, hst, one_mul]
    nlinarith [mul_le_mul_of_nonneg_left (hB1 i) hs, mul_le_mul_of_nonneg_left (hB2 i) ht]
  obtain ⟨p, α, hmin, hlt⟩ := exists_box_minorant (hB A B) (nbhd_subset_box hzA hzB) hcon
  have h1 := (le_localExt (f := f) p α (fun y hy => hmin y (nbhd_subset_box hA1 hB1 hy))).trans hq1
  have h2 := (le_localExt (f := f) p α (fun y hy => hmin y (nbhd_subset_box hA2 hB2 hy))).trans hq2
  have h1' := EReal.coe_le_coe_iff.mp h1
  have h2' := EReal.coe_le_coe_iff.mp h2
  have hlt' := EReal.coe_lt_coe_iff.mp hlt
  rw [aff_combo p α q1.1 q2.1 s t hst] at hlt'
  nlinarith

theorem localExt_lsc {f : (Fin n → ℤ) → WithTop ℝ}
    (hB : ∀ a b : Fin n → ℤ, IntegrallyConvex (Restrict f a b)) {x : Fin n → ℝ} {r : ℝ}
    (hr : (r : EReal) < LocalConvexExtension f x) :
    ∃ δ > 0, ∀ v : Fin n → ℝ, (∀ i, |v i - x i| < δ) →
      ((r + δ : ℝ) : EReal) < LocalConvexExtension f v := by
  set A : Fin n → ℤ := fun i => ⌊x i⌋ - 1
  set B : Fin n → ℤ := fun i => ⌈x i⌉ + 1
  have hxA' : ∀ i, (A i : ℝ) ≤ x i - 1 := fun i => by
    simp only [A, Int.cast_sub, Int.cast_one]; linarith [Int.floor_le (x i)]
  have hxB' : ∀ i, x i + 1 ≤ B i := fun i => by
    simp only [B, Int.cast_add, Int.cast_one]; linarith [Int.le_ceil (x i)]
  have hxA : ∀ i, (A i : ℝ) ≤ x i := fun i => by linarith [hxA' i]
  have hxB : ∀ i, x i ≤ B i := fun i => by linarith [hxB' i]
  obtain ⟨p, α, hmin, hlt⟩ := exists_box_minorant (hB A B) (nbhd_subset_box hxA hxB) hr
  have hlt' := EReal.coe_lt_coe_iff.mp hlt
  set g := aff p α x - r with hg
  have hg0 : 0 < g := by linarith
  set S := ∑ i, |p i| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  refine ⟨min 1 (g / (2 * (S + 1))), by positivity, fun v hv => ?_⟩
  set δ := min 1 (g / (2 * (S + 1))) with hδ
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ2 : δ ≤ g / (2 * (S + 1)) := min_le_right _ _
  have hδ3 : δ * (S + 1) ≤ g / 2 := by
    have := mul_le_mul_of_nonneg_right hδ2 (by linarith : (0 : ℝ) ≤ S + 1)
    rwa [div_mul_eq_mul_div, mul_div_mul_right _ _ (by linarith : (S + 1 : ℝ) ≠ 0)] at this
  have hvA : ∀ i, (A i : ℝ) ≤ v i := fun i => by
    have := (abs_lt.mp (hv i)).1
    linarith [hxA' i]
  have hvB : ∀ i, v i ≤ B i := fun i => by
    have := (abs_lt.mp (hv i)).2
    linarith [hxB' i]
  have hle := le_localExt (f := f) p α (fun y hy => hmin y (nbhd_subset_box hvA hvB hy))
  refine lt_of_lt_of_le ?_ hle
  apply EReal.coe_lt_coe_iff.mpr
  have hdiff : aff p α x - aff p α v ≤ S * δ := by
    simp only [aff, hS, Finset.sum_mul]
    rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro i _
    rw [← mul_sub]
    calc p i * (x i - v i) ≤ |p i * (x i - v i)| := le_abs_self _
      _ = |p i| * |v i - x i| := by rw [abs_mul, abs_sub_comm]
      _ ≤ |p i| * δ := mul_le_mul_of_nonneg_left (hv i).le (abs_nonneg _)
  nlinarith

theorem not_mem_closure_epiLocal {f : (Fin n → ℤ) → WithTop ℝ}
    (hB : ∀ a b : Fin n → ℤ, IntegrallyConvex (Restrict f a b)) {x : Fin n → ℝ} {r : ℝ}
    (hr : (r : EReal) < LocalConvexExtension f x) :
    (x, r) ∉ closure (epiLocal f) := by
  intro hmem
  obtain ⟨δ, hδ, H⟩ := localExt_lsc hB hr
  obtain ⟨⟨v, s⟩, hb, hd⟩ := Metric.mem_closure_iff.mp hmem δ hδ
  rw [Prod.dist_eq, max_lt_iff] at hd
  have hv : ∀ i, |v i - x i| < δ := by
    intro i
    have := (dist_pi_lt_iff hδ).mp hd.1 i
    rwa [Real.dist_eq, abs_sub_comm] at this
  have hs : s < r + δ := by
    have := hd.2
    rw [Real.dist_eq] at this
    linarith [(abs_lt.mp this).1]
  have h1 := lt_of_lt_of_le (H v hv) hb
  have h2 := EReal.coe_lt_coe_iff.mp h1
  linarith

theorem clm_prod_decomp (φ : ((Fin n → ℝ) × ℝ) →L[ℝ] ℝ) (v : Fin n → ℝ) (s : ℝ) :
    φ (v, s) = ∑ i, φ ((Pi.single i 1 : Fin n → ℝ), (0 : ℝ)) * v i + φ (0, 1) * s := by
  have : (v, s) = ∑ i, v i • ((Pi.single i 1 : Fin n → ℝ), (0 : ℝ)) +
      s • ((0 : Fin n → ℝ), (1 : ℝ)) := by
    ext j
    · simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
    · simp [Prod.snd_sum]
  rw [this, map_add, map_sum, φ.map_smul]
  simp only [ContinuousLinearMap.map_smul, smul_eq_mul, mul_comm]

/-- Separation of a point below `f̃` from the epigraph. -/
theorem separate_epiLocal {f : (Fin n → ℤ) → WithTop ℝ}
    (hB : ∀ a b : Fin n → ℤ, IntegrallyConvex (Restrict f a b)) {x : Fin n → ℝ} {r : ℝ}
    (hr : (r : EReal) < LocalConvexExtension f x) :
    ∃ (p : Fin n → ℝ) (β u : ℝ),
      (∀ q ∈ epiLocal f, ∑ i, p i * q.1 i + β * q.2 < u) ∧ u < ∑ i, p i * x i + β * r := by
  obtain ⟨φ, u, h1, h2⟩ := geometric_hahn_banach_closed_point (convex_epiLocal hB).closure
    isClosed_closure (not_mem_closure_epiLocal hB hr)
  refine ⟨fun i => φ ((Pi.single i 1 : Fin n → ℝ), (0 : ℝ)), φ (0, 1), u, fun q hq => ?_, ?_⟩
  · have := h1 q (subset_closure hq)
    rwa [← Prod.mk.eta (p := q), clm_prod_decomp] at this
  · rwa [clm_prod_decomp] at h2

theorem aff_add_smul (p q : Fin n → ℝ) (α β K : ℝ) (v : Fin n → ℝ) :
    aff (fun i => p i + K * q i) (α + K * β) v = aff p α v + K * aff q β v := by
  simp only [aff, add_mul, Finset.sum_add_distrib, mul_add, Finset.mul_sum]
  have : ∀ i, K * q i * v i = K * (q i * v i) := fun i => by ring
  simp only [this]
  ring

theorem integralNeighborhood_toR {y w : Fin n → ℤ} (hw : w ∈ IntegralNeighborhood (toR y)) :
    w = y := by
  funext i
  have := hw i
  simp only [toR, Int.floor_intCast, Int.ceil_intCast] at this
  omega

theorem mem_epiLocal_of_eq {f : (Fin n → ℤ) → WithTop ℝ} {y : Fin n → ℤ} {c s : ℝ}
    (hy : f y = c) (hs : c ≤ s) : (toR y, s) ∈ epiLocal f := by
  have := localExt_le_self f y
  rw [hy] at this
  exact this.trans (EReal.coe_le_coe_iff.mpr hs)

/-- A non-vertical separating hyperplane yields a global affine minorant. -/
theorem minorant_of_sep {f : (Fin n → ℤ) → WithTop ℝ} {p : Fin n → ℝ} {β u : ℝ} (hβ : β < 0)
    (hsep : ∀ q ∈ epiLocal f, ∑ i, p i * q.1 i + β * q.2 < u) :
    ∀ y, ((aff (fun i => p i / (-β)) (-u / (-β)) (toR y) : ℝ) : EReal) ≤ WithBot.some (f y) := by
  intro y
  cases hfy : f y with
  | top => exact le_top
  | coe c =>
    have h := hsep _ (mem_epiLocal_of_eq hfy le_rfl)
    simp only at h
    change ((aff (fun i => p i / (-β)) (-u / (-β)) (toR y) : ℝ) : EReal) ≤ ((c : ℝ) : EReal)
    apply EReal.coe_le_coe_iff.mpr
    have hγ : 0 < -β := by linarith
    simp only [aff, div_mul_eq_mul_div, ← Finset.sum_div, ← add_div]
    rw [div_le_iff₀ hγ]
    simp only [toR] at h
    linarith

theorem aff_sep_value {p : Fin n → ℝ} {β u r : ℝ} {x : Fin n → ℝ} (hβ : β < 0)
    (h : u < ∑ i, p i * x i + β * r) :
    r < aff (fun i => p i / (-β)) (-u / (-β)) x := by
  have hγ : 0 < -β := by linarith
  simp only [aff, div_mul_eq_mul_div, ← Finset.sum_div, ← add_div]
  rw [lt_div_iff₀ hγ]
  linarith

/-- Backward direction of Proposition 3.19. -/
theorem integrallyConvex_of_restrict {f : (Fin n → ℤ) → WithTop ℝ}
    (hB : ∀ a b : Fin n → ℤ, IntegrallyConvex (Restrict f a b)) : IntegrallyConvex f := by
  intro x
  apply le_antisymm _ (convexClosure_le_localExt f x)
  by_cases hdom : ∀ y, f y = ⊤
  · have : ConvexClosure f x = ⊤ := by
      rw [EReal.eq_top_iff_forall_lt]
      intro M
      refine lt_of_lt_of_le ?_ (le_convexClosure (v := x) 0 (M + 1) (fun y => by rw [hdom y]; exact WithBot.coe_le_coe.mpr le_top))
      apply EReal.coe_lt_coe_iff.mpr
      simp [aff]
    rw [this]
    exact le_top
  push_neg at hdom
  obtain ⟨y1, hy1⟩ := hdom
  obtain ⟨c1, hc1⟩ := WithTop.ne_top_iff_exists.mp hy1
  have hc1' : f y1 = c1 := hc1.symm
  -- a base global affine minorant
  have hloc1 : ((c1 - 1 : ℝ) : EReal) < LocalConvexExtension f (toR y1) := by
    have h := le_localExt (f := f) (v := toR y1) 0 c1 (fun w hw => by
      rw [integralNeighborhood_toR hw, hc1']
      show ((aff 0 c1 (toR y1) : ℝ) : EReal) ≤ ((c1 : ℝ) : EReal)
      apply EReal.coe_le_coe_iff.mpr
      simp [aff])
    refine lt_of_lt_of_le ?_ h
    apply EReal.coe_lt_coe_iff.mpr
    simp [aff]
  obtain ⟨p0, β0, u0, hsep0, hval0⟩ := separate_epiLocal hB hloc1
  have hβ0 : β0 < 0 := by
    have := hsep0 _ (mem_epiLocal_of_eq hc1' le_rfl)
    simp only [toR] at this hval0
    linarith
  have hbase := minorant_of_sep hβ0 hsep0
  set p1 : Fin n → ℝ := fun i => p0 i / (-β0)
  set α1 : ℝ := -u0 / (-β0)
  -- main argument
  by_contra hcon
  push_neg at hcon
  obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.mp hcon
  obtain ⟨p, β, u, hsep, hval⟩ := separate_epiLocal hB hr2
  have hβ : β ≤ 0 := by
    by_contra hβ
    push_neg at hβ
    set P := ∑ i, p i * (toR y1) i
    have := hsep _ (mem_epiLocal_of_eq hc1' (le_max_left c1 ((u - P) / β)))
    simp only at this
    have h2 : β * ((u - P) / β) ≤ β * max c1 ((u - P) / β) :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) hβ.le
    rw [mul_div_cancel₀ _ hβ.ne'] at h2
    linarith
  rcases hβ.lt_or_eq with hβ | hβ
  · have h1 := le_convexClosure (v := x) _ _ (minorant_of_sep hβ hsep)
    have h2 := aff_sep_value hβ hval
    have := lt_of_le_of_lt h1 hr1
    have := EReal.coe_lt_coe_iff.mp this
    linarith
  · subst hβ
    set P := ∑ i, p i * x i
    have hgap : 0 < P - u := by simp only [zero_mul, add_zero] at hval; linarith
    set K : ℝ := (|r - aff p1 α1 x| + 1) / (P - u)
    have hK : 0 ≤ K := by positivity
    have hKx : K * (P - u) = |r - aff p1 α1 x| + 1 := by
      simp only [K]; field_simp
    have hmin : ∀ y, ((aff (fun i => p1 i + K * p i) (α1 + K * (-u)) (toR y) : ℝ) : EReal) ≤
        WithBot.some (f y) := by
      intro y
      cases hfy : f y with
      | top => exact le_top
      | coe c =>
        have h := hsep _ (mem_epiLocal_of_eq hfy le_rfl)
        simp only [zero_mul, add_zero] at h
        have hb := hbase y
        rw [hfy] at hb
        change _ ≤ ((c : ℝ) : EReal)
        change ((aff p1 α1 (toR y) : ℝ) : EReal) ≤ ((c : ℝ) : EReal) at hb
        apply EReal.coe_le_coe_iff.mpr
        have hb' := EReal.coe_le_coe_iff.mp hb
        rw [aff_add_smul]
        have : aff p (-u) (toR y) ≤ 0 := by simp only [aff]; linarith
        nlinarith
    have h1 := le_convexClosure (v := x) _ _ hmin
    have := EReal.coe_lt_coe_iff.mp (lt_of_le_of_lt h1 hr1)
    rw [aff_add_smul] at this
    have h3 : aff p (-u) x = P - u := by simp only [aff, P]; ring
    rw [h3, hKx] at this
    have := le_abs_self (r - aff p1 α1 x)
    linarith

end DiscreteConvex.IntegralConvexity.Prop319Aux

open DiscreteConvex.IntegralConvexity DiscreteConvex.IntegralConvexity.Prop319Aux

/-- Proposition 3.19 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.94). -/
theorem solution {n : ℕ} (f : (Fin n → ℤ) → WithTop ℝ) :
    IntegrallyConvex f ↔ ∀ a b : Fin n → ℤ, IntegrallyConvex (Restrict f a b) :=
  ⟨fun hf a b => restrict_integrallyConvex hf a b, integrallyConvex_of_restrict⟩

