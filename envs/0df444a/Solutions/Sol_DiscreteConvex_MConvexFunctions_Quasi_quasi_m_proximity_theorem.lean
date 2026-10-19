-- Prove2me | solution 1 for DiscreteConvex.MConvexFunctions.Quasi.quasi_m_proximity_theorem
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T01:34:01.792495+00:00
-- url     : https://prove2.me/submissions/ff877235-7500-4eee-9c8e-f9593d3161a3

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctions_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctions_CharVec
import Definitions.Def_DiscreteConvex_MConvexFunctions_ArgMin
import Definitions.Def_DiscreteConvex_MConvexFunctions_Quasi_SSQMNeq

open DiscreteConvex.MConvexFunctions DiscreteConvex.MConvexFunctions.Quasi
open scoped BigOperators

open DiscreteConvex.MConvexFunctions

namespace QMinimizerCut
variable {V : Type*} [Fintype V] [DecidableEq V]

def distance (a z : V → ℤ) : ℕ := (∑ w, |z w - a w|).toNat

theorem exchange_closer (a z : V → ℤ) (u v : V)
    (hu : a u < z u) (hv : z v < a v) :
    distance a (fun w => z w - CharVec u w + CharVec v w) < distance a z := by
  classical
  have huv : u ≠ v := by intro h; subst v; omega
  let z' : V → ℤ := fun w => z w - CharVec u w + CharVec v w
  have hdiff : (∑ w, |z' w - a w|) = (∑ w, |z w - a w|) - 2 := by
    have hp (w : V) : |z' w - a w| = |z w - a w| -
        (if w = u then 1 else 0) - (if w = v then 1 else 0) := by
      by_cases hwu : w = u
      · subst w
        simp only [z', CharVec, eq_self, if_true, if_neg huv, add_zero]
        rw [abs_of_nonneg (by omega : 0 ≤ z u - 1 - a u), abs_of_pos (by omega : 0 < z u - a u)]
        omega
      · by_cases hwv : w = v
        · subst w
          simp only [z', CharVec, eq_self, if_true, if_neg (Ne.symm huv), sub_zero]
          rw [abs_of_nonpos (by omega : z v + 1 - a v ≤ 0), abs_of_neg (by omega : z v - a v < 0)]
          omega
        · simp [z', CharVec, hwu, hwv]
    simp_rw [hp]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    simp
    ring
  change (∑ w, |z' w - a w|).toNat < (∑ w, |z w - a w|).toNat
  have hn : 0 ≤ ∑ w, |z' w - a w| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  apply (Int.toNat_lt_toNat (by omega : 0 < ∑ w, |z w - a w|)).mpr
  omega

end QMinimizerCut


open DiscreteConvex.MConvexFunctions DiscreteConvex.MConvexFunctions.Quasi

namespace QProximityCore
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma strict_cost {a b c d : WithTop ℝ} (ha : a ≠ ⊤) (hb : b ≠ ⊤)
    (hsum : c + d ≤ a + b) (hbd : b < d) : c < a := by
  obtain ⟨ra, rfl⟩ := WithTop.ne_top_iff_exists.mp ha
  obtain ⟨rb, rfl⟩ := WithTop.ne_top_iff_exists.mp hb
  have hc : c ≠ ⊤ := by intro h; simp [h] at hsum
  have hd : d ≠ ⊤ := by intro h; simp [h] at hsum
  obtain ⟨rc, rfl⟩ := WithTop.ne_top_iff_exists.mp hc
  obtain ⟨rd, rfl⟩ := WithTop.ne_top_iff_exists.mp hd
  rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe] at hsum
  rw [WithTop.coe_lt_coe] at hbd ⊢
  linarith

lemma finite_box (lo hi : V → ℤ) : (Set.Icc lo hi).Finite := by
  have h := Set.Finite.pi (fun v : V => Set.finite_Icc (lo v) (hi v))
  convert h using 1
  ext x
  simp [Set.mem_Icc, Set.mem_pi, Pi.le_def, forall_and]

def donorBox (x z : V → ℤ) (v : V) : Set (V → ℤ) :=
  {y | z v ≤ y v ∧ y v ≤ x v ∧
    (∀ w, w ≠ v → x w ≤ y w ∧ y w ≤ max (x w) (z w)) ∧
    ∑ w, y w = ∑ w, x w}

lemma donorBox_finite (x z : V → ℤ) (v : V) : (donorBox x z v).Finite := by
  classical
  apply (finite_box (fun w => if w = v then z w else x w)
    (fun w => if w = v then x w else max (x w) (z w))).subset
  intro y hy
  constructor <;> intro w <;> by_cases h : w = v
  · subst w; simpa using hy.1
  · simpa [h] using (hy.2.2.1 w h).1
  · subst w; simpa using hy.2.1
  · simpa [h] using (hy.2.2.1 w h).2

lemma donorBox_start (x z : V → ℤ) (v : V) (hv : z v ≤ x v) : x ∈ donorBox x z v := by
  exact ⟨hv, le_rfl, fun w _ => ⟨le_rfl, le_max_left _ _⟩, rfl⟩

lemma donorBox_down (x z y : V → ℤ) (v w : V) (hy : y ∈ donorBox x z v)
    (hvw : v ≠ w) (hv : z v < y v) (hw : y w < z w) :
    (fun i => y i - CharVec v i + CharVec w i) ∈ donorBox x z v := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [CharVec, eq_self, if_true, if_neg hvw, add_zero]; omega
  · simp only [CharVec, eq_self, if_true, if_neg hvw, add_zero]; linarith [hy.2.1]
  · intro i hiv
    by_cases hiw : i = w
    · subst i
      simp only [CharVec, if_neg (Ne.symm hvw), eq_self, if_true, sub_zero]
      exact ⟨by linarith [(hy.2.2.1 w (Ne.symm hvw)).1],
        (show y w + 1 ≤ z w by omega).trans (le_max_right _ _)⟩
    · simpa [CharVec, hiv, hiw] using hy.2.2.1 i hiv
  · simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp [CharVec, hy.2.2.2]

lemma donorBox_up (x z y : V → ℤ) (v w : V) (hy : y ∈ donorBox x z v)
    (hvw : v ≠ w) (hv : y v < x v) (hw : x w < y w) :
    (fun i => y i + CharVec v i - CharVec w i) ∈ donorBox x z v := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [CharVec, eq_self, if_true, if_neg hvw, sub_zero]; linarith [hy.1]
  · simp only [CharVec, eq_self, if_true, if_neg hvw, sub_zero]; omega
  · intro i hiv
    by_cases hiw : i = w
    · subst i
      simp only [CharVec, if_neg (Ne.symm hvw), eq_self, if_true, add_zero]
      exact ⟨by omega, by linarith [(hy.2.2.1 w (Ne.symm hvw)).2]⟩
    · simpa [CharVec, hiv, hiw] using hy.2.2.1 i hiv
  · simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    simp [CharVec, hy.2.2.2]

lemma box_closer (x z : V → ℤ) (v : V) (y : V → ℤ) (hy : y ∈ donorBox x z v) (hv : z v < y v) :
    QMinimizerCut.distance x y < QMinimizerCut.distance x z := by
  classical
  unfold QMinimizerCut.distance
  have hlt : (∑ w, |y w - x w|) < ∑ w, |z w - x w| := by
    apply Finset.sum_lt_sum
    · intro w _
      by_cases hwv : w = v
      · subst w
        have h2 := hy.2.1
        rw [abs_of_nonpos (by omega), abs_of_nonpos (by omega)]; omega
      · obtain ⟨h1, h2⟩ := hy.2.2.1 w hwv
        rcases le_total (x w) (z w) with h | h
        · rw [max_eq_right h] at h2
          rw [abs_of_nonneg (by omega), abs_of_nonneg (by omega)]; omega
        · rw [max_eq_left h] at h2
          rw [show y w - x w = 0 by omega, abs_zero]; exact abs_nonneg _
    · refine ⟨v, Finset.mem_univ _, ?_⟩
      have h2 := hy.2.1
      rw [abs_of_nonpos (by omega), abs_of_neg (by omega)]; omega
  have hn : 0 ≤ ∑ w, |y w - x w| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  exact (Int.toNat_lt_toNat (by omega)).mpr hlt

lemma donor_min_equal (f : (V → ℤ) → WithTop ℝ) (hf : SSQMNeq f)
    (x z : V → ℤ) (c : WithTop ℝ) (hz : z ∈ DomZ f) (hzc : f z ≤ c)
    (hne : ∀ q, f q ≤ c → ¬ QMinimizerCut.distance x q < QMinimizerCut.distance x z)
    (v : V) (y : V → ℤ) (hy : y ∈ donorBox x z v) (hyd : y ∈ DomZ f)
    (hmin : ∀ q ∈ donorBox x z v, f y ≤ f q) : y v = z v := by
  classical
  by_contra hnot
  have hv : z v < y v := lt_of_le_of_ne hy.1 (Ne.symm hnot)
  have hyc : c < f y := by
    by_contra hle
    exact hne y (le_of_not_gt hle) (box_closer x z v y hy hv)
  have hfyz : f y ≠ f z := ne_of_gt (hzc.trans_lt hyc)
  obtain ⟨w, hw, hres⟩ := hf y hyd z hz hfyz v (by simpa [SuppPos] using hv)
  have hw' : y w < z w := by simpa [SuppNeg] using hw
  have hvw : v ≠ w := by intro heq; subst w; omega
  have hwx : x w < z w := (hy.2.2.1 w (Ne.symm hvw)).1.trans_lt hw'
  have hvx : z v < x v := hv.trans_le hy.2.1
  let z' : V → ℤ := fun i => z i + CharVec v i - CharVec w i
  have hcloser : QMinimizerCut.distance x z' < QMinimizerCut.distance x z := by
    convert QMinimizerCut.exchange_closer x z w v hwx hvx using 1
    congr 1; funext i; dsimp [z']; ring
  have hz' : c < f z' := lt_of_not_ge (fun h => hne z' h hcloser)
  have hy' := donorBox_down x z y v w hy hvw hv hw'
  rcases hres with h1 | h2 | ⟨_, h3⟩
  · exact not_lt_of_ge (hmin _ hy') h1
  · exact absurd (h2.trans_le hzc) (not_lt_of_gt hz')
  · have : f z' = f z := h3
    rw [this] at hz'
    exact absurd hzc (not_le_of_gt hz')

lemma receiver_le_deficit (x z y : V → ℤ) (v w : V)
    (hy : y ∈ donorBox x z v) (hwv : w ≠ v) : y w - x w ≤ x v - y v := by
  classical
  have hp (i : V) : (if i = v then y v - x v else 0) +
      (if i = w then y w - x w else 0) ≤ y i - x i := by
    by_cases hiv : i = v
    · subst i; simp [Ne.symm hwv]
    · by_cases hiw : i = w
      · subst i; simp [hwv]
      · simp only [if_neg hiv, if_neg hiw, zero_add]
        linarith [(hy.2.2.1 i hiv).1]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hp i)
  simp only [Finset.sum_add_distrib] at hs
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at hs
  rw [Finset.sum_sub_distrib, hy.2.2.2] at hs
  omega

def ray (x : V → ℤ) (v w : V) (m : ℤ) : V → ℤ :=
  fun i => x i - m * CharVec v i + m * CharVec w i

lemma ray_mem_box (x z y : V → ℤ) (v w : V) (hy : y ∈ donorBox x z v)
    (hwv : w ≠ v) (m : ℤ) (hm : 0 ≤ m) (hmw : m ≤ y w - x w) :
    ray x v w m ∈ donorBox x z v := by
  classical
  have hdef := receiver_le_deficit x z y v w hy hwv
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [ray, CharVec, eq_self, if_true, if_neg (Ne.symm hwv), mul_one, mul_zero, add_zero]
    linarith [hy.1]
  · simp only [ray, CharVec, eq_self, if_true, if_neg (Ne.symm hwv), mul_one, mul_zero, add_zero]
    omega
  · intro i hiv
    by_cases hiw : i = w
    · subst i
      simp only [ray, CharVec, if_neg hwv, eq_self, if_true, mul_zero, sub_zero, mul_one]
      exact ⟨by omega, (show x w + m ≤ y w by omega).trans (hy.2.2.1 w hwv).2⟩
    · simpa [ray, CharVec, hiv, hiw] using (show x i ≤ x i ∧ x i ≤ max (x i) (z i) from ⟨le_rfl, le_max_left _ _⟩)
  · simp only [ray, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp [CharVec]

lemma box_min_strict_above (f : (V → ℤ) → WithTop ℝ) (hf : SSQMNeq f)
    (x z : V → ℤ) (c : WithTop ℝ) (hz : z ∈ DomZ f) (hzc : f z ≤ c)
    (hne : ∀ q, f q ≤ c → ¬ QMinimizerCut.distance x q < QMinimizerCut.distance x z)
    (v : V) (y : V → ℤ) (hyd : y ∈ DomZ f)
    (hmin : ∀ q ∈ donorBox x z v, f y ≤ f q)
    (q : V → ℤ) (hq : q ∈ donorBox x z v) (hqv : z v < q v) : f y < f q := by
  by_contra hnot
  have hqy : f q ≤ f y := le_of_not_gt hnot
  have hqd : q ∈ DomZ f := ne_top_of_le_ne_top hyd hqy
  have hqmin : ∀ r ∈ donorBox x z v, f q ≤ f r := fun r hr => hqy.trans (hmin r hr)
  have heq := donor_min_equal f hf x z c hz hzc hne v q hq hqd hqmin
  omega

lemma receiver_lt_scale (f : (V → ℤ) → WithTop ℝ) (hf : SSQMNeq f)
    (x z : V → ℤ) (c : WithTop ℝ) (hx : x ∈ DomZ f) (hz : z ∈ DomZ f) (hzc : f z ≤ c)
    (hne : ∀ q, f q ≤ c → ¬ QMinimizerCut.distance x q < QMinimizerCut.distance x z)
    (v : V) (hv : z v < x v) (y : V → ℤ) (hy : y ∈ donorBox x z v)
    (hyd : y ∈ DomZ f) (hmin : ∀ q ∈ donorBox x z v, f y ≤ f q)
    (alpha : ℤ) (ha : 0 < alpha)
    (hloc : ∀ u w : V, f x ≤ f (fun i => x i + alpha * (CharVec w i - CharVec u i)))
    (w : V) (hwv : w ≠ v) : y w - x w ≤ alpha - 1 := by
  classical
  have hyv : y v = z v := donor_min_equal f hf x z c hz hzc hne v y hy hyd hmin
  by_contra hnot
  have hcap : alpha ≤ y w - x w := by omega
  have hwy : x w < y w := by omega
  let yup : V → ℤ := fun i => y i + CharVec v i - CharVec w i
  have hup : yup ∈ donorBox x z v := donorBox_up x z y v w hy (Ne.symm hwv) (by omega) hwy
  have hupy : f y < f yup := box_min_strict_above f hf x z c hz hzc hne v y hyd hmin yup hup
    (by simp only [yup, CharVec, eq_self, if_true, if_neg (Ne.symm hwv), sub_zero]; omega)
  have step (m : ℕ) (hm : (m : ℤ) < y w - x w)
      (hr : ray x v w m ∈ DomZ f) : f (ray x v w ((m : ℤ) + 1)) < f (ray x v w m) := by
    have hww : (ray x v w m) w < y w := by simp [ray, CharVec, hwv]; omega
    have hrbox : ray x v w m ∈ donorBox x z v :=
      ray_mem_box x z y v w hy hwv m (by positivity) hm.le
    have hrv : z v < ray x v w m v := by
      have hdef := receiver_le_deficit x z y v w hy hwv
      have hyv' := hyv
      simp [ray, CharVec, Ne.symm hwv]
      omega
    have hlt : f y < f (ray x v w m) :=
      box_min_strict_above f hf x z c hz hzc hne v y hyd hmin _ hrbox hrv
    obtain ⟨i, hi, hres⟩ := hf y hyd (ray x v w m) hr (ne_of_lt hlt) w (by simpa [SuppPos] using hww)
    have hi' : y i < (ray x v w m) i := by simpa [SuppNeg] using hi
    have hiv : i = v := by
      by_contra hiv
      by_cases hiw : i = w
      · subst i; omega
      · have hh := (hy.2.2.1 i hiv).1
        simp only [ray, CharVec, if_neg hiv, if_neg hiw, mul_zero, sub_zero, add_zero] at hi'
        omega
    subst i
    have heq1 : (fun i => y i - CharVec w i + CharVec v i) = yup := by
      funext i; dsimp [yup]; ring
    have heq2 : (fun i => ray x v w m i + CharVec w i - CharVec v i) =
        ray x v w ((m : ℤ) + 1) := by funext i; dsimp [ray]; ring
    rw [heq1, heq2] at hres
    rcases hres with h1 | h2 | ⟨h3, _⟩
    · exact absurd h1 (not_lt_of_gt hupy)
    · exact h2
    · exact absurd h3 (ne_of_gt hupy)
  have ray_values : ∀ m : ℕ, (m : ℤ) ≤ y w - x w →
      f (ray x v w m) ≤ f x ∧ (0 < m → f (ray x v w m) < f x) := by
    intro m
    induction m with
    | zero =>
      intro _
      simp only [Nat.cast_zero]
      have hzero : ray x v w 0 = x := by funext i; simp [ray]
      rw [hzero]
      exact ⟨le_rfl, by omega⟩
    | succ m ih =>
      intro hm
      obtain ⟨hprev, _⟩ := ih (by omega)
      have hrd : ray x v w m ∈ DomZ f := ne_top_of_le_ne_top hx hprev
      have hs := step m (by omega) hrd
      have hs' : f (ray x v w (m + 1 : ℕ)) < f x := by
        simpa only [Nat.cast_add, Nat.cast_one] using hs.trans_le hprev
      exact ⟨hs'.le, fun _ => hs'⟩
  have hval := (ray_values alpha.toNat (by omega)).2 (by omega)
  have hval' : f (ray x v w alpha) < f x := by simpa [Int.toNat_of_nonneg ha.le] using hval
  have hlocal : f x ≤ f (ray x v w alpha) := by
    convert hloc v w using 1
    congr 1; funext i; dsimp [ray]; ring
  exact not_lt_of_ge hlocal hval'

lemma donor_bound (f : (V → ℤ) → WithTop ℝ) (hf : SSQMNeq f)
    (x z : V → ℤ) (c : WithTop ℝ) (hx : x ∈ DomZ f) (hz : z ∈ DomZ f) (hzc : f z ≤ c)
    (hne : ∀ q, f q ≤ c → ¬ QMinimizerCut.distance x q < QMinimizerCut.distance x z)
    (alpha : ℤ) (ha : 0 < alpha)
    (hloc : ∀ u w : V, f x ≤ f (fun i => x i + alpha * (CharVec w i - CharVec u i)))
    (v : V) : x v - z v ≤ ((Fintype.card V : ℤ) - 1) * (alpha - 1) := by
  classical
  have hcpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  by_cases hv : z v < x v
  · obtain ⟨y, hy, hmin⟩ := Set.exists_min_image (donorBox x z v) f (donorBox_finite x z v)
      ⟨x, donorBox_start x z v hv.le⟩
    have hyd : y ∈ DomZ f := ne_top_of_le_ne_top hx (hmin x (donorBox_start x z v hv.le))
    have hyv : y v = z v := donor_min_equal f hf x z c hz hzc hne v y hy hyd hmin
    have hb (w : V) (hwv : w ≠ v) : y w - x w ≤ alpha - 1 :=
      receiver_lt_scale f hf x z c hx hz hzc hne v hv y hy hyd hmin alpha ha hloc w hwv
    have hsum := Finset.sum_erase_add (s := Finset.univ) (fun w => y w - x w) (Finset.mem_univ v)
    have hs0 : (∑ w : V, (y w - x w)) = 0 := by rw [Finset.sum_sub_distrib, hy.2.2.2, sub_self]
    rw [hs0] at hsum
    have hle := Finset.sum_le_sum (s := Finset.univ.erase v)
      (fun w hw => hb w (Finset.mem_erase.mp hw).1)
    have hc : ((Finset.univ.erase v).card : ℤ) + 1 = (Fintype.card V : ℤ) := by
      exact_mod_cast Finset.card_erase_add_one (s := Finset.univ) (Finset.mem_univ v)
    simp only [Finset.sum_const, nsmul_eq_mul] at hle
    have hc' : ((Finset.univ.erase v).card : ℤ) = (Fintype.card V : ℤ) - 1 := by omega
    rw [hc'] at hle
    rw [hyv] at hsum
    linarith
  · have hb : 0 ≤ ((Fintype.card V : ℤ) - 1) * (alpha - 1) := mul_nonneg (by omega) (by omega)
    omega

lemma exchange_neg (f : (V → ℤ) → WithTop ℝ) (hf : SSQMNeq f) :
    SSQMNeq (fun x => f (fun w => -x w)) := by
  classical
  intro x hx y hy hxy u hu
  have hu' : (fun w => -x w) u < (fun w => -y w) u := by
    have h : y u < x u := by simpa [SuppPos] using hu
    change -x u < -y u
    omega
  obtain ⟨v, hv, hh⟩ := hf (fun w => -y w) hy (fun w => -x w) hx (Ne.symm hxy) u
    (by simpa [SuppPos] using hu')
  have hv' : x v < y v := by
    have h : -y v < -x v := by simpa [SuppNeg] using hv
    omega
  refine ⟨v, by simpa [SuppNeg] using hv', ?_⟩
  have heq1 : (fun w => -(x w - CharVec u w + CharVec v w)) =
      (fun w => -x w + CharVec u w - CharVec v w) := by funext w; ring
  have heq2 : (fun w => -(y w + CharVec u w - CharVec v w)) =
      (fun w => -y w - CharVec u w + CharVec v w) := by funext w; ring
  change f (fun w => -(x w - CharVec u w + CharVec v w)) < f (fun w => -x w) ∨
    f (fun w => -(y w + CharVec u w - CharVec v w)) < f (fun w => -y w) ∨
    (f (fun w => -(x w - CharVec u w + CharVec v w)) = f (fun w => -x w) ∧
      f (fun w => -(y w + CharVec u w - CharVec v w)) = f (fun w => -y w))
  rw [heq1, heq2]
  rcases hh with h | h | ⟨h1, h2⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr ⟨h2, h1⟩)

lemma distance_neg (a z : V → ℤ) :
    QMinimizerCut.distance (fun w => -a w) (fun w => -z w) = QMinimizerCut.distance a z := by
  unfold QMinimizerCut.distance
  have hp (w : V) : -z w - -a w = -(z w - a w) := by ring
  simp_rw [hp, abs_neg]

lemma receiver_bound (f : (V → ℤ) → WithTop ℝ) (hf : SSQMNeq f)
    (x z : V → ℤ) (c : WithTop ℝ) (hx : x ∈ DomZ f) (hz : z ∈ DomZ f) (hzc : f z ≤ c)
    (hne : ∀ q, f q ≤ c → ¬ QMinimizerCut.distance x q < QMinimizerCut.distance x z)
    (alpha : ℤ) (ha : 0 < alpha)
    (hloc : ∀ u w : V, f x ≤ f (fun i => x i + alpha * (CharVec w i - CharVec u i)))
    (v : V) : z v - x v ≤ ((Fintype.card V : ℤ) - 1) * (alpha - 1) := by
  let g : (V → ℤ) → WithTop ℝ := fun q => f (fun i => -q i)
  let nx : V → ℤ := fun i => -x i
  let nz : V → ℤ := fun i => -z i
  have hg : SSQMNeq g := exchange_neg f hf
  have hxg : nx ∈ DomZ g := by simpa [DomZ, g, nx] using hx
  have hzg : nz ∈ DomZ g := by simpa [DomZ, g, nz] using hz
  have hzcg : g nz ≤ c := by simpa [g, nz] using hzc
  have hneg : ∀ q, g q ≤ c → ¬ QMinimizerCut.distance nx q < QMinimizerCut.distance nx nz := by
    intro q hq hh
    apply hne (fun w => -q w) hq
    have hqdist := distance_neg x (fun w => -q w)
    simp only [neg_neg] at hqdist
    change QMinimizerCut.distance (fun w => -x w) q <
      QMinimizerCut.distance (fun w => -x w) (fun w => -z w) at hh
    rwa [hqdist, distance_neg] at hh
  have hlocg : ∀ u w : V, g nx ≤ g (fun i => nx i + alpha * (CharVec w i - CharVec u i)) := by
    intro u w
    dsimp only [g, nx]
    simp only [neg_neg]
    convert hloc w u using 1
    congr 1; funext i; ring
  have h := donor_bound g hg nx nz c hxg hzg hzcg hneg alpha ha hlocg v
  dsimp only [nx, nz] at h
  linarith

end QProximityCore


open DiscreteConvex.MConvexFunctions
open scoped BigOperators

namespace QProximityFinal
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem m_proximity (f : (V → ℤ) → WithTop ℝ) (hf : SSQMNeq f)
    (alpha : ℤ) (ha : 0 < alpha) (x : V → ℤ) (hx : x ∈ DomZ f)
    (hloc : ∀ u v : V, f x ≤ f (fun w => x w + alpha * (CharVec v w - CharVec u w))) :
    (ArgMin f).Nonempty ∧ ∃ z ∈ ArgMin f,
      ∀ v : V, |x v - z v| ≤ ((Fintype.card V : ℤ) - 1) * (alpha - 1) := by
  classical
  let B : ℤ := ((Fintype.card V : ℤ) - 1) * (alpha - 1)
  let S : Set (V → ℤ) := Set.Icc (fun v => x v - B) (fun v => x v + B)
  have hB (v : V) : 0 ≤ B := by
    have hc : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
    exact mul_nonneg (by omega) (by omega)
  have hxS : x ∈ S := by
    constructor
    · intro v
      change x v - B ≤ x v
      have h := hB v
      omega
    · intro v
      change x v ≤ x v + B
      have h := hB v
      omega
  have hSf : S.Finite := QProximityCore.finite_box _ _
  obtain ⟨a, haS, hamin⟩ := Set.exists_min_image S f hSf ⟨x, hxS⟩
  have hag : a ∈ ArgMin f := by
    intro y
    by_contra hnot
    have hya : f y < f a := lt_of_not_ge hnot
    have haf : a ∈ DomZ f := ne_top_of_le_ne_top hx (hamin x hxS)
    have hyf : y ∈ DomZ f := ne_top_of_lt hya
    obtain ⟨z, hz, hn⟩ := (measure (QMinimizerCut.distance x)).wf.has_min {q | f q ≤ f y} ⟨y, by change f y ≤ f y; exact le_rfl⟩
    change f z ≤ f y at hz
    have hzf : z ∈ DomZ f := ne_top_of_le_ne_top hyf hz
    have hzS : z ∈ S := by
      constructor <;> intro v
      · have h := QProximityCore.donor_bound f hf x z (f y) hx hzf hz hn alpha ha hloc v
        change x v - B ≤ z v
        dsimp [B]; linarith
      · have h := QProximityCore.receiver_bound f hf x z (f y) hx hzf hz hn alpha ha hloc v
        change z v ≤ x v + B
        dsimp [B]; linarith
    exact (not_lt_of_ge ((hamin z hzS).trans hz)) hya
  refine ⟨⟨a, hag⟩, a, hag, ?_⟩
  intro v
  have hlo := haS.1 v
  have hhi := haS.2 v
  change x v - B ≤ a v at hlo
  change a v ≤ x v + B at hhi
  change |x v - a v| ≤ B
  rw [abs_le]
  constructor <;> omega

end QProximityFinal


open DiscreteConvex.MConvexFunctions DiscreteConvex.MConvexFunctions.Quasi in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (α : ℤ) (hα : 0 < α)
    (f : (V → ℤ) → WithTop ℝ) (hf : SSQMNeq f) (xα : V → ℤ) (hxα : xα ∈ DomZ f)
    (hloc : ∀ u v : V, f xα ≤ f (fun w => xα w + α * (CharVec v w - CharVec u w))) :
    (ArgMin f).Nonempty ∧
      ∃ x ∈ ArgMin f, ∀ v : V, |xα v - x v| ≤ ((Fintype.card V : ℤ) - 1) * (α - 1) :=
  QProximityFinal.m_proximity f hf α hα xα hxα hloc
