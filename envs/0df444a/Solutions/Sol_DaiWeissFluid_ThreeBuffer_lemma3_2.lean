-- Prove2me | solution 1 for DaiWeissFluid.ThreeBuffer.lemma3_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T06:08:45.371549+00:00
-- url     : https://prove2.me/submissions/30dc1986-4b4a-4b84-9b29-ef17c303a54b

import Mathlib
import Definitions.Def_DaiWeissFluid_ThreeBuffer_FluidModel
import Definitions.Def_DaiWeissFluid_ThreeBuffer_Line



namespace DaiWeissFluid.ThreeBuffer
open Set

def LipP (f : ℝ → ℝ) : Prop :=
  ∃ K : ℝ, ∀ x y, 0 ≤ x → 0 ≤ y → |f x - f y| ≤ K * |x - y|

lemma LipP.const (c : ℝ) : LipP (fun _ => c) := ⟨0, by intros; simp⟩

lemma LipP.add {f g : ℝ → ℝ} (hf : LipP f) (hg : LipP g) : LipP (fun x => f x + g x) := by
  obtain ⟨K, hK⟩ := hf
  obtain ⟨K', hK'⟩ := hg
  refine ⟨K + K', fun x y hx hy => ?_⟩
  have h1 := hK x y hx hy
  have h2 := hK' x y hx hy
  calc |f x + g x - (f y + g y)| = |(f x - f y) + (g x - g y)| := by ring_nf
    _ ≤ |f x - f y| + |g x - g y| := abs_add_le _ _
    _ ≤ (K + K') * |x - y| := by rw [add_mul]; linarith

lemma LipP.const_mul {f : ℝ → ℝ} (hf : LipP f) (a : ℝ) : LipP (fun x => a * f x) := by
  obtain ⟨K, hK⟩ := hf
  refine ⟨|a| * K, fun x y hx hy => ?_⟩
  have h1 := hK x y hx hy
  calc |a * f x - a * f y| = |a| * |f x - f y| := by rw [← mul_sub, abs_mul]
    _ ≤ |a| * (K * |x - y|) := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = |a| * K * |x - y| := by ring

lemma LipP.sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ) (h : ∀ i ∈ s, LipP (f i)) :
    LipP (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using LipP.const 0
  | insert a s ha ih =>
    have := (h a (Finset.mem_insert_self a s)).add (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))
    simpa [Finset.sum_insert ha] using this

lemma LipP.iSup {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ → ℝ) (h : ∀ i, LipP (f i)) :
    LipP (fun x => ⨆ i, f i x) := by
  choose K hK using h
  refine ⟨∑ i, |K i|, fun x y hx hy => ?_⟩
  have hKi : ∀ i, K i ≤ ∑ j, |K j| := fun i =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |K j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i))
  have key : ∀ x y, 0 ≤ x → 0 ≤ y → (⨆ i, f i x) - (⨆ i, f i y) ≤ (∑ j, |K j|) * |x - y| := by
    intro x y hx hy
    have : (⨆ i, f i x) ≤ (⨆ i, f i y) + (∑ j, |K j|) * |x - y| := by
      apply ciSup_le
      intro i
      have h1 := hK i x y hx hy
      have h2 : f i y ≤ ⨆ i, f i y := le_ciSup (f := fun i => f i y) (Set.finite_range _).bddAbove i
      have h3 : K i * |x - y| ≤ (∑ j, |K j|) * |x - y| := mul_le_mul_of_nonneg_right (hKi i) (abs_nonneg _)
      have := (le_abs_self _).trans h1
      linarith
    linarith
  rw [abs_le]
  constructor
  · have := key y x hy hx
    rw [abs_sub_comm y x] at this
    linarith
  · exact key x y hx hy

lemma LipP.lipschitzOnWith {f : ℝ → ℝ} (hf : LipP f) :
    ∃ K : NNReal, LipschitzOnWith K f (Ici 0) := by
  obtain ⟨K, hK⟩ := hf
  refine ⟨⟨max K 0, le_max_right _ _⟩, LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_⟩
  have := hK x y hx hy
  rw [Real.dist_eq, Real.dist_eq]
  exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))

lemma LipP.continuousOn {f : ℝ → ℝ} (hf : LipP f) : ContinuousOn f (Ici 0) := by
  obtain ⟨K, hK⟩ := hf.lipschitzOnWith
  exact hK.continuousOn

lemma LipP.ac {f : ℝ → ℝ} (hf : LipP f) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    AbsolutelyContinuousOnInterval f a b := by
  obtain ⟨K, hK⟩ := hf.lipschitzOnWith
  apply LipschitzOnWith.absolutelyContinuousOnInterval
  refine hK.mono ?_
  rw [uIcc_of_le hab]
  intro x hx
  exact le_trans ha hx.1

namespace ReentrantLine

variable {I K : ℕ} (L : ReentrantLine I K) {Q T : ℝ → Fin K → ℝ}

lemma T_incr (h : L.IsFluidSolution Q T) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (k : Fin K) :
    0 ≤ T t k - T s k ∧ T t k - T s k ≤ t - s := by
  have ht : 0 ≤ t := hs.trans hst
  have hmono : ∀ l, T s l ≤ T t l := fun l => h.T_mono l (mem_Ici.2 hs) (mem_Ici.2 ht) hst
  refine ⟨sub_nonneg.2 (hmono k), ?_⟩
  have hidle := h.idle_mono (L.σ k) (mem_Ici.2 hs) (mem_Ici.2 ht) hst
  simp only [idle, busy] at hidle
  have hsum : T t k - T s k ≤ ∑ l ∈ L.C (L.σ k), (T t l - T s l) :=
    Finset.single_le_sum (f := fun l => T t l - T s l) (fun l _ => sub_nonneg.2 (hmono l))
      (by simp [C])
  rw [Finset.sum_sub_distrib] at hsum
  linarith

lemma Q_incr (h : L.IsFluidSolution Q T) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (k : Fin K) :
    |Q t k - Q s k| ≤ (1 + 2 * ∑ l, |L.μ l|) * (t - s) := by
  have ht : 0 ≤ t := hs.trans hst
  set M := ∑ l, |L.μ l| with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg (fun l _ => abs_nonneg _)
  have hμ : ∀ l, |L.μ l| ≤ M := fun l =>
    Finset.single_le_sum (f := fun l => |L.μ l|) (fun l _ => abs_nonneg _) (Finset.mem_univ l)
  have hts : 0 ≤ t - s := sub_nonneg.2 hst
  have key : ∀ l : Fin K, |L.μ l * T t l - L.μ l * T s l| ≤ M * (t - s) := by
    intro l
    obtain ⟨a, b⟩ := L.T_incr h hs hst l
    rw [← mul_sub, abs_mul, abs_of_nonneg a]
    exact mul_le_mul (hμ l) b a hM0
  have hflow : Q t k - Q s k = (L.inflow T k t - L.inflow T k s) - (L.μ k * T t k - L.μ k * T s k) := by
    rw [h.flow t ht k, h.flow s hs k]; ring
  have hin : |L.inflow T k t - L.inflow T k s| ≤ (1 + M) * (t - s) := by
    unfold inflow
    by_cases hk : (k : ℕ) = 0
    · rw [dif_pos hk, dif_pos hk, abs_of_nonneg (by linarith)]
      nlinarith
    · rw [dif_neg hk, dif_neg hk]
      have := key ⟨(k : ℕ) - 1, by have := k.isLt; omega⟩
      nlinarith
  rw [hflow]
  calc _ ≤ |L.inflow T k t - L.inflow T k s| + |L.μ k * T t k - L.μ k * T s k| := abs_sub _ _
    _ ≤ (1 + M) * (t - s) + M * (t - s) := add_le_add hin (key k)
    _ = _ := by ring

lemma lipP_Q (h : L.IsFluidSolution Q T) (k : Fin K) : LipP (fun t => Q t k) := by
  refine ⟨1 + 2 * ∑ l, |L.μ l|, fun x y hx hy => ?_⟩
  rcases le_total x y with hxy | hxy
  · have := L.Q_incr h hx hxy k
    rw [abs_sub_comm, abs_sub_comm x y, abs_of_nonneg (sub_nonneg.2 hxy)]
    exact this
  · have := L.Q_incr h hy hxy k
    rw [abs_of_nonneg (sub_nonneg.2 hxy)]
    exact this


lemma volume_nonneg (hm : ∀ k, 0 < L.m k) {u : ℝ} (hQ : ∀ k, 0 ≤ Q u k) (i : Fin I) :
    0 ≤ L.volume Q i u :=
  Finset.sum_nonneg (fun k _ => mul_nonneg (hm k).le (hQ k))

lemma Q_zero_of_volume_zero (hm : ∀ k, 0 < L.m k) {u : ℝ} (hQ : ∀ k, 0 ≤ Q u k)
    (h : ∀ i, L.volume Q i u = 0) (k : Fin K) : Q u k = 0 := by
  have h0 := h (L.σ k)
  unfold volume at h0
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun l _ => mul_nonneg (hm l).le (hQ l))] at h0
  have := h0 k (by simp [C])
  rcases mul_eq_zero.1 this with h1 | h1
  · exact absurd h1 (hm k).ne'
  · exact h1

lemma sum_pos_of_volume_pos (hm : ∀ k, 0 < L.m k) {u : ℝ} (hQ : ∀ k, 0 ≤ Q u k) {i : Fin I}
    (hv : 0 < L.volume Q i u) : 0 < ∑ k ∈ L.C i, Q u k := by
  by_contra hcon
  have hz : ∑ k ∈ L.C i, Q u k = 0 :=
    le_antisymm (not_lt.1 hcon) (Finset.sum_nonneg (fun k _ => hQ k))
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun l _ => hQ l)] at hz
  have : L.volume Q i u = 0 := Finset.sum_eq_zero (fun k hk => by rw [hz k hk, mul_zero])
  linarith

end ReentrantLine

theorem lemma3_2_core {I K : ℕ} (L : ReentrantLine I K) (hm : ∀ k, 0 < L.m k) (hI : 0 < I)
    (Q T : ℝ → Fin K → ℝ) (hsol : L.IsFluidSolution Q T)
    (c : Fin I → Fin K → ℝ) (hc : ∀ i k, 0 ≤ c i k) (ε : Fin I → ℝ) (hε : ∀ i, 0 < ε i)
    (ha : ∀ i t, 0 < t → 0 < L.volume Q i t →
      ∀ d, HasDerivAt (fun s => ∑ k, c i k * Q s k) d t → d ≤ -ε i)
    (hb : ∀ i t, 0 ≤ t → L.volume Q i t = 0 →
      ∀ j, j ≠ i → ∑ k, c i k * Q t k ≤ ∑ k, c j k * Q t k) :
    (∀ a b, 0 ≤ a → a ≤ b →
        AbsolutelyContinuousOnInterval (fun s => ⨆ i, ∑ k, c i k * Q s k) a b) ∧
    (∀ t, 0 ≤ t → 0 ≤ ⨆ i, ∑ k, c i k * Q t k) ∧
    (∀ t, 0 < t → 0 < (⨆ i, ∑ k, c i k * Q t k) →
      (∀ i, DifferentiableAt ℝ (fun s => ∑ k, c i k * Q s k) t) →
      ∀ d, HasDerivAt (fun s => ⨆ i, ∑ k, c i k * Q s k) d t →
        d ≤ -(Finset.univ.inf' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hI⟩⟩) ε)) := by
  haveI : Nonempty (Fin I) := ⟨⟨0, hI⟩⟩
  have hGi : ∀ i, LipP (fun s => ∑ k, c i k * Q s k) := fun i =>
    LipP.sum Finset.univ (fun k s => c i k * Q s k)
      (fun k _ => (L.lipP_Q hsol k).const_mul (c i k))
  have hG : LipP (fun s => ⨆ i, ∑ k, c i k * Q s k) := LipP.iSup _ hGi
  have hbdd : ∀ s, BddAbove (Set.range fun i => ∑ k, c i k * Q s k) :=
    fun s => (Set.finite_range _).bddAbove
  refine ⟨fun a b ha0 hab => hG.ac ha0 hab, ?_, ?_⟩
  · intro t ht
    exact le_ciSup_of_le (hbdd t) ⟨0, hI⟩
      (Finset.sum_nonneg (fun k _ => mul_nonneg (hc _ k) (hsol.nonneg t ht k)))
  · intro t ht hGpos hdiff d hd
    have hQ : ∀ k, 0 ≤ Q t k := hsol.nonneg t ht.le
    obtain ⟨i0, hi0⟩ := exists_eq_ciSup_of_finite (f := fun i => ∑ k, c i k * Q t k)
    -- find j with positive volume and G_j(t) = G(t)
    have hex : ∃ j, 0 < L.volume Q j t ∧ ∑ k, c j k * Q t k = ⨆ i, ∑ k, c i k * Q t k := by
      rcases (L.volume_nonneg hm hQ i0).eq_or_lt with h0 | h0
      · have hall : ∀ j, ∑ k, c j k * Q t k = ⨆ i, ∑ k, c i k * Q t k := by
          intro j
          by_cases hj : j = i0
          · subst hj; exact hi0
          · apply le_antisymm (le_ciSup (hbdd t) j)
            rw [← hi0]
            exact hb i0 t ht.le h0.symm j hj
        by_contra hcon
        push_neg at hcon
        have hz : ∀ j, L.volume Q j t = 0 := fun j =>
          le_antisymm (not_lt.1 (fun hp => hcon j hp (hall j))) (L.volume_nonneg hm hQ j)
        have hQz := L.Q_zero_of_volume_zero hm hQ hz
        have : ∑ k, c i0 k * Q t k = 0 := Finset.sum_eq_zero (fun k _ => by rw [hQz k, mul_zero])
        linarith
      · exact ⟨i0, h0, hi0⟩
    obtain ⟨j, hjW, hjG⟩ := hex
    have hdj := (hdiff j).hasDerivAt
    have hmin : IsLocalMin (fun s => (⨆ i, ∑ k, c i k * Q s k) - ∑ k, c j k * Q s k) t := by
      refine Filter.Eventually.of_forall (fun s => ?_)
      show _ ≤ _
      have := le_ciSup (hbdd s) j
      simp only
      rw [← hjG]
      simp only [sub_self]
      linarith
    have h0 : d - deriv (fun s => ∑ k, c j k * Q s k) t = 0 := hmin.hasDerivAt_eq_zero (hd.sub hdj)
    have h1 := ha j t ht hjW _ hdj
    have h2 : Finset.univ.inf' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hI⟩⟩) ε ≤ ε j :=
      Finset.inf'_le _ (Finset.mem_univ j)
    linarith

end DaiWeissFluid.ThreeBuffer

open DaiWeissFluid.ThreeBuffer


theorem solution {I K : ℕ} (L : ReentrantLine I K) (hm : ∀ k, 0 < L.m k) (hI : 0 < I)
    (Q T : ℝ → Fin K → ℝ) (hsol : L.IsFluidSolution Q T)
    (c : Fin I → Fin K → ℝ) (hc : ∀ i k, 0 ≤ c i k) (ε : Fin I → ℝ) (hε : ∀ i, 0 < ε i)
    (ha : ∀ i t, 0 < t → 0 < L.volume Q i t →
      ∀ d, HasDerivAt (fun s => ∑ k, c i k * Q s k) d t → d ≤ -ε i)
    (hb : ∀ i t, 0 ≤ t → L.volume Q i t = 0 →
      ∀ j, j ≠ i → ∑ k, c i k * Q t k ≤ ∑ k, c j k * Q t k) :
    (∀ a b, 0 ≤ a → a ≤ b →
        AbsolutelyContinuousOnInterval (fun s => ⨆ i, ∑ k, c i k * Q s k) a b) ∧
    (∀ t, 0 ≤ t → 0 ≤ ⨆ i, ∑ k, c i k * Q t k) ∧
    (∀ t, 0 < t → 0 < (⨆ i, ∑ k, c i k * Q t k) →
      (∀ i, DifferentiableAt ℝ (fun s => ∑ k, c i k * Q s k) t) →
      ∀ d, HasDerivAt (fun s => ⨆ i, ∑ k, c i k * Q s k) d t →
        d ≤ -(Finset.univ.inf' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hI⟩⟩) ε)) := by
  exact lemma3_2_core L hm hI Q T hsol c hc ε hε ha hb
