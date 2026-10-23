-- Prove2me | solution 1 for DaiWeissFluid.ThreeBuffer.emptying_time
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T06:15:02.384997+00:00
-- url     : https://prove2.me/submissions/9783474e-45c7-4f64-a7e6-c08ec6dfe9ba

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

section tb
variable {m : Fin 3 → ℝ} {Q T : ℝ → Fin 3 → ℝ}

lemma tb_C0 : (threeBuffer m).C 0 = {0, 2} := by
  have : Finset.filter (fun k : Fin 3 => (![0, 1, 0] : Fin 3 → Fin 2) k = 0) Finset.univ = {0, 2} := by
    decide
  exact this

lemma tb_C1 : (threeBuffer m).C 1 = {1} := by
  have : Finset.filter (fun k : Fin 3 => (![0, 1, 0] : Fin 3 → Fin 2) k = 1) Finset.univ = {1} := by
    decide
  exact this

lemma tb_rho0 : (threeBuffer m).ρ 0 = m 0 + m 2 := by
  have : (0 : Fin 3) ≠ 2 := by decide
  unfold ReentrantLine.ρ; rw [tb_C0, Finset.sum_pair this]; rfl

lemma tb_rho1 : (threeBuffer m).ρ 1 = m 1 := by
  unfold ReentrantLine.ρ; rw [tb_C1, Finset.sum_singleton]; rfl

lemma tb_vol0 (u : ℝ) : (threeBuffer m).volume Q 0 u = m 0 * Q u 0 + m 2 * Q u 2 := by
  have : (0 : Fin 3) ≠ 2 := by decide
  unfold ReentrantLine.volume; rw [tb_C0, Finset.sum_pair this]; rfl

lemma tb_vol1 (u : ℝ) : (threeBuffer m).volume Q 1 u = m 1 * Q u 1 := by
  unfold ReentrantLine.volume; rw [tb_C1, Finset.sum_singleton]; rfl

lemma tb_idle0 (u : ℝ) : (threeBuffer m).idle T 0 u = u - (T u 0 + T u 2) := by
  have : (0 : Fin 3) ≠ 2 := by decide
  unfold ReentrantLine.idle ReentrantLine.busy; rw [tb_C0, Finset.sum_pair this]

lemma tb_idle1 (u : ℝ) : (threeBuffer m).idle T 1 u = u - T u 1 := by
  unfold ReentrantLine.idle ReentrantLine.busy; rw [tb_C1, Finset.sum_singleton]

lemma tb_flow0 (h : (threeBuffer m).IsFluidSolution Q T) {u : ℝ} (hu : 0 ≤ u) :
    Q u 0 = Q 0 0 + u - (m 0)⁻¹ * T u 0 := by
  have := h.flow u hu 0
  simpa [ReentrantLine.inflow, ReentrantLine.μ, threeBuffer] using this

lemma tb_flow1 (h : (threeBuffer m).IsFluidSolution Q T) {u : ℝ} (hu : 0 ≤ u) :
    Q u 1 = Q 0 1 + (m 0)⁻¹ * T u 0 - (m 1)⁻¹ * T u 1 := by
  have := h.flow u hu 1
  simpa [ReentrantLine.inflow, ReentrantLine.μ, threeBuffer] using this

lemma tb_flow2 (h : (threeBuffer m).IsFluidSolution Q T) {u : ℝ} (hu : 0 ≤ u) :
    Q u 2 = Q 0 2 + (m 1)⁻¹ * T u 1 - (m 2)⁻¹ * T u 2 := by
  have := h.flow u hu 2
  simpa [ReentrantLine.inflow, ReentrantLine.μ, threeBuffer] using this

lemma qplus0 (u : ℝ) : Qplus Q 0 u = Q u 0 := by
  unfold Qplus
  have : Finset.univ.filter (· ≤ (0 : Fin 3)) = {0} := by decide
  rw [this]; simp

lemma qplus1 (u : ℝ) : Qplus Q 1 u = Q u 0 + Q u 1 := by
  unfold Qplus
  have : Finset.univ.filter (· ≤ (1 : Fin 3)) = {0, 1} := by decide
  rw [this]; simp

lemma qplus2 (u : ℝ) : Qplus Q 2 u = Q u 0 + Q u 1 + Q u 2 := by
  unfold Qplus
  have : Finset.univ.filter (· ≤ (2 : Fin 3)) = Finset.univ := by decide
  rw [this, Fin.sum_univ_three]

lemma lyap0 (u : ℝ) : lyap m Q 0 u = theta m * Q u 0 + (1 - theta m) * (Q u 0 + Q u 1 + Q u 2) := by
  show theta m * Qplus Q 0 u + (1 - theta m) * Qplus Q 2 u = _
  rw [qplus0, qplus2]

lemma lyap1 (u : ℝ) : lyap m Q 1 u = Q u 0 + Q u 1 := by
  show Qplus Q 1 u = _
  rw [qplus1]

lemma tb_rho_pos_lt (h1 : m 0 + m 2 < 1) (h2 : m 1 < 1) (hm : ∀ k, 0 < m k) (i : Fin 2) :
    0 < (threeBuffer m).ρ i ∧ (threeBuffer m).ρ i < 1 := by
  have : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  rcases this with rfl | rfl
  · rw [tb_rho0]; exact ⟨by linarith [hm 0, hm 2], h1⟩
  · rw [tb_rho1]; exact ⟨hm 1, h2⟩

lemma tb_key (hm : ∀ k, 0 < m k) (hs : (threeBuffer m).IsFluidSolution Q T) (i : Fin 2) {u v : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hid : (threeBuffer m).idle T i u = (threeBuffer m).idle T i v) :
    lyap m Q i u - lyap m Q i v = (1 - 1 / (threeBuffer m).ρ i) * (u - v) := by
  have : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  rcases this with rfl | rfl
  · rw [tb_idle0, tb_idle0] at hid
    rw [tb_rho0, lyap0, lyap0, tb_flow0 hs hu, tb_flow1 hs hu, tb_flow2 hs hu,
      tb_flow0 hs hv, tb_flow1 hs hv, tb_flow2 hs hv]
    have hm0 := hm 0
    have hm2 := hm 2
    have e1 : theta m * (m 0)⁻¹ = (m 0 + m 2)⁻¹ := by
      unfold theta; field_simp
    have e2 : (1 - theta m) * (m 2)⁻¹ = (m 0 + m 2)⁻¹ := by
      unfold theta; field_simp; ring
    rw [one_div]
    linear_combination (-(T u 0 - T v 0)) * e1 + (-(T u 2 - T v 2)) * e2 + (m 0 + m 2)⁻¹ * hid
  · rw [tb_idle1, tb_idle1] at hid
    rw [tb_rho1, lyap1, lyap1, tb_flow0 hs hu, tb_flow1 hs hu,
      tb_flow0 hs hv, tb_flow1 hs hv]
    rw [one_div]
    linear_combination (m 1)⁻¹ * hid

end tb

theorem idle_const_nbhd {I K : ℕ} (L : ReentrantLine I K) {Q T : ℝ → Fin K → ℝ}
    (hm : ∀ k, 0 < L.m k) (hwc : L.IsWorkConserving Q T) (i : Fin I) {t : ℝ} (ht : 0 < t)
    (hW : 0 < L.volume Q i t) :
    ∃ δ, 0 < δ ∧ δ < t ∧ ∀ u ∈ Icc (t - δ) (t + δ), L.idle T i u = L.idle T i t := by
  have hcont : ContinuousAt (L.volume Q i) t := by
    have : ContinuousOn (L.volume Q i) (Ici 0) := by
      unfold ReentrantLine.volume
      apply continuousOn_finset_sum
      intro k _
      exact continuousOn_const.mul (L.lipP_Q hwc.1 k).continuousOn
    exact this.continuousAt (Ici_mem_nhds ht)
  have hev := hcont.eventually (lt_mem_nhds hW)
  obtain ⟨e, he, hball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨min (e / 2) (t / 2), by positivity, ?_, ?_⟩
  · have := min_le_right (e / 2) (t / 2); linarith
  · intro u hu
    have hδ1 : min (e / 2) (t / 2) ≤ e / 2 := min_le_left _ _
    have hδ2 : min (e / 2) (t / 2) ≤ t / 2 := min_le_right _ _
    have hδ0 : 0 < min (e / 2) (t / 2) := by positivity
    have hpos : ∀ v ∈ Icc (t - min (e / 2) (t / 2)) (t + min (e / 2) (t / 2)),
        0 < ∑ k ∈ L.C i, Q v k := by
      intro v hv
      have : dist v t < e := by
        rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hv.1, hv.2]
      exact L.sum_pos_of_volume_pos hm (fun k => hwc.1.nonneg v (by linarith [hv.1]) k)
        (hball this)
    have hconst : ∀ w ∈ Icc (t - min (e / 2) (t / 2)) (t + min (e / 2) (t / 2)),
        L.idle T i w = L.idle T i (t - min (e / 2) (t / 2)) := by
      intro w hw
      refine hwc.2 i (t - min (e / 2) (t / 2)) w (by linarith) hw.1 (fun v hv => hpos v ⟨hv.1, hv.2.trans hw.2⟩)
    have htmem : t ∈ Icc (t - min (e / 2) (t / 2)) (t + min (e / 2) (t / 2)) :=
      ⟨by linarith, by linarith⟩
    rw [hconst u hu, hconst t htmem]

theorem drift_rate_core (m : Fin 3 → ℝ) (hm : ∀ k, 0 < m k) (h1 : m 0 + m 2 < 1) (h2 : m 1 < 1)
    (Q T : ℝ → Fin 3 → ℝ) (hwc : (threeBuffer m).IsWorkConserving Q T) (i : Fin 2) (t : ℝ)
    (ht : 0 < t) (hW : 0 < (threeBuffer m).volume Q i t) (d : ℝ)
    (hd : HasDerivAt (lyap m Q i) d t) :
    d = -(1 / (threeBuffer m).ρ i - 1) ∧ d < 0 := by
  obtain ⟨δ, hδ, hδt, hid⟩ := idle_const_nbhd (threeBuffer m) hm hwc i ht hW
  have hsol := hwc.1
  have key : ∀ u ∈ Icc (t - δ) (t + δ), lyap m Q i u =
      lyap m Q i t + (1 - 1 / (threeBuffer m).ρ i) * (u - t) := by
    intro u hu
    have := tb_key hm hsol i (u := u) (v := t) (by linarith [hu.1]) ht.le (hid u hu)
    linarith
  have hev : (fun u => lyap m Q i t + (1 - 1 / (threeBuffer m).ρ i) * (u - t)) =ᶠ[nhds t]
      lyap m Q i :=
    Filter.eventually_of_mem (Icc_mem_nhds (by linarith) (by linarith)) (fun u hu => (key u hu).symm)
  have hd2 : HasDerivAt (fun u => lyap m Q i t + (1 - 1 / (threeBuffer m).ρ i) * (u - t))
      (1 - 1 / (threeBuffer m).ρ i) t := by
    have := (((hasDerivAt_id t).sub_const t).const_mul (1 - 1 / (threeBuffer m).ρ i)).const_add
      (lyap m Q i t)
    simpa using this
  have hd3 : HasDerivAt (lyap m Q i) (1 - 1 / (threeBuffer m).ρ i) t := hd2.congr_of_eventuallyEq hev.symm
  have heq : d = 1 - 1 / (threeBuffer m).ρ i := hd.unique hd3
  obtain ⟨hp, hl⟩ := tb_rho_pos_lt h1 h2 hm i
  have := one_lt_one_div hp hl
  constructor <;> linarith

lemma aux_eps (ρ t : ℝ) (hp : 0 < ρ) (hl : ρ < 1) (h : ρ / (1 - ρ) ≤ t) : 1 ≤ (1 / ρ - 1) * t := by
  have h1 : 0 < 1 - ρ := by linarith
  have e : (1 / ρ - 1) * (ρ / (1 - ρ)) = 1 := by field_simp
  have : 0 ≤ 1 / ρ - 1 := by
    have := one_lt_one_div hp hl; linarith
  calc (1 : ℝ) = (1 / ρ - 1) * (ρ / (1 - ρ)) := e.symm
    _ ≤ (1 / ρ - 1) * t := mul_le_mul_of_nonneg_left h this

theorem emptying_time_core (m : Fin 3 → ℝ) (hm : ∀ k, 0 < m k) (h1 : m 0 + m 2 < 1) (h2 : m 1 < 1)
    (Q T : ℝ → Fin 3 → ℝ) (hwc : (threeBuffer m).IsWorkConserving Q T)
    (hQ0 : ∑ k, Q 0 k = 1) (t : ℝ)
    (ht : max ((m 0 + m 2) / (1 - (m 0 + m 2))) (m 1 / (1 - m 1)) ≤ t) (k : Fin 3) :
    Q t k = 0 := by
  have hsol := hwc.1
  have hm' : ∀ k, 0 < (threeBuffer m).m k := hm
  have hθ0 : 0 < theta m := div_pos (hm 0) (by linarith [hm 0, hm 2])
  have hθ1 : theta m < 1 := (div_lt_one (by linarith [hm 0, hm 2])).2 (by linarith [hm 2])
  let c : Fin 2 → Fin 3 → ℝ := ![![1, 1 - theta m, 1 - theta m], ![1, 1, 0]]
  let ε : Fin 2 → ℝ := fun i => 1 / (threeBuffer m).ρ i - 1
  have hc : ∀ i k, 0 ≤ c i k := by
    intro i k
    fin_cases i <;> fin_cases k <;> simp [c] <;> linarith
  have hε : ∀ i, 0 < ε i := fun i => by
    obtain ⟨hp, hl⟩ := tb_rho_pos_lt h1 h2 hm i
    have := one_lt_one_div hp hl
    simp only [ε]; linarith
  have hGc : ∀ i s, ∑ j, c i j * Q s j = lyap m Q i s := by
    intro i s
    have : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    rcases this with rfl | rfl
    · rw [lyap0]; simp [c, Fin.sum_univ_three]; ring
    · rw [lyap1]; simp [c, Fin.sum_univ_three]
  have ha : ∀ i t, 0 < t → 0 < (threeBuffer m).volume Q i t →
      ∀ d, HasDerivAt (fun s => ∑ j, c i j * Q s j) d t → d ≤ -ε i := by
    intro i t ht hW d hd
    have hf : (fun s => ∑ j, c i j * Q s j) = lyap m Q i := funext (hGc i)
    rw [hf] at hd
    have := (drift_rate_core m hm h1 h2 Q T hwc i t ht hW d hd).1
    simp only [ε]; linarith
  have hb : ∀ i t, 0 ≤ t → (threeBuffer m).volume Q i t = 0 →
      ∀ j, j ≠ i → ∑ j', c i j' * Q t j' ≤ ∑ j', c j j' * Q t j' := by
    intro i t ht0 hv j hj
    have hQn := hsol.nonneg t ht0
    rw [hGc, hGc]
    have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    have hj' : j = 0 ∨ j = 1 := by fin_cases j <;> simp
    rcases hi with rfl | rfl <;> rcases hj' with rfl | rfl
    · exact absurd rfl hj
    · rw [tb_vol0] at hv
      have e0 : m 0 * Q t 0 = 0 := by
        linarith [mul_nonneg (hm 0).le (hQn 0), mul_nonneg (hm 2).le (hQn 2)]
      have e2 : m 2 * Q t 2 = 0 := by
        linarith [mul_nonneg (hm 0).le (hQn 0), mul_nonneg (hm 2).le (hQn 2)]
      have q0 : Q t 0 = 0 := (mul_eq_zero.1 e0).resolve_left (hm 0).ne'
      have q2 : Q t 2 = 0 := (mul_eq_zero.1 e2).resolve_left (hm 2).ne'
      rw [lyap0, lyap1, q0, q2]
      nlinarith [mul_nonneg hθ0.le (hQn 1)]
    · rw [tb_vol1] at hv
      have q1 : Q t 1 = 0 := (mul_eq_zero.1 hv).resolve_left (hm 1).ne'
      rw [lyap0, lyap1, q1]
      nlinarith [mul_nonneg (sub_pos.2 hθ1).le (hQn 2)]
    · exact absurd rfl hj
  obtain ⟨hAC, hnn, hder⟩ := lemma3_2_core (threeBuffer m) hm' (by norm_num) Q T hsol c hc ε hε ha hb
  have hGi : ∀ i, LipP (fun s => ∑ j, c i j * Q s j) := fun i =>
    LipP.sum Finset.univ (fun j s => c i j * Q s j)
      (fun j _ => ((threeBuffer m).lipP_Q hsol j).const_mul (c i j))
  have hGlip : LipP (fun s => ⨆ i, ∑ j, c i j * Q s j) := LipP.iSup _ hGi
  have hbdd : ∀ s, BddAbove (Set.range fun i => ∑ j, c i j * Q s j) :=
    fun s => (Set.finite_range _).bddAbove
  have hne : (Finset.univ : Finset (Fin 2)).Nonempty := Finset.univ_nonempty_iff.mpr ⟨⟨0, by norm_num⟩⟩
  have hder' : ∀ t, 0 < t → 0 < (⨆ i, ∑ j, c i j * Q t j) →
      (∀ i, DifferentiableAt ℝ (fun s => ∑ j, c i j * Q s j) t) →
      ∀ d, HasDerivAt (fun s => ⨆ i, ∑ j, c i j * Q s j) d t →
        d ≤ -(Finset.univ.inf' hne ε) := hder
  clear hder
  generalize hemin : Finset.univ.inf' hne ε = emin at hder'
  have hemin_pos : 0 < emin := by
    rw [← hemin]; exact (Finset.lt_inf'_iff hne).2 (fun i _ => hε i)
  have hεt : 1 ≤ emin * t := by
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' hne ε
    rw [← hemin, hi]
    have hi' : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    rcases hi' with rfl | rfl
    · simp only [ε]; rw [tb_rho0]
      exact aux_eps _ _ (by linarith [hm 0, hm 2]) h1 ((le_max_left _ _).trans ht)
    · simp only [ε]; rw [tb_rho1]
      exact aux_eps _ _ (hm 1) h2 ((le_max_right _ _).trans ht)
  have ht0 : 0 ≤ t := by
    have := tb_rho_pos_lt h1 h2 hm 1
    have h3 : 0 ≤ m 1 / (1 - m 1) := div_nonneg (hm 1).le (by linarith)
    exact h3.trans ((le_max_right _ _).trans ht)
  have hG0 : (⨆ i, ∑ j, c i j * Q 0 j) ≤ 1 := by
    apply ciSup_le
    intro i
    have hq := hsol.nonneg 0 le_rfl
    rw [Fin.sum_univ_three] at hQ0
    have hi' : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    rcases hi' with rfl | rfl
    · simp [c, Fin.sum_univ_three]
      nlinarith [mul_nonneg hθ0.le (hq 1), mul_nonneg hθ0.le (hq 2), hq 0]
    · simp [c, Fin.sum_univ_three]
      linarith [hq 2]
  -- the main decrease claim
  have claimA : ∀ a b, 0 ≤ a → a ≤ b → (∀ u ∈ Ioc a b, 0 < ⨆ i, ∑ j, c i j * Q u j) →
      (⨆ i, ∑ j, c i j * Q b j) - (⨆ i, ∑ j, c i j * Q a j) ≤ -emin * (b - a) := by
    intro a b ha hab hpos
    have hACab := hAC a b ha hab
    have hint := hACab.integral_deriv_eq_sub
    have hII := hACab.intervalIntegrable_deriv
    have hae : ∀ᵐ x : ℝ, x ∈ Icc a b →
        deriv (fun s => ⨆ i, ∑ j, c i j * Q s j) x ≤ -emin := by
      have h0 := hACab.ae_differentiableAt
      have hi : ∀ᵐ x : ℝ, ∀ i, x ∈ uIcc a b → DifferentiableAt ℝ (fun s => ∑ j, c i j * Q s j) x := by
        rw [MeasureTheory.ae_all_iff]
        intro i
        exact ((hGi i).ac ha hab).ae_differentiableAt
      have hna : ∀ᵐ x : ℝ, x ≠ a := by
        have : (MeasureTheory.volume : MeasureTheory.Measure ℝ) {a} = 0 := by simp
        rw [MeasureTheory.ae_iff]
        simpa using this
      filter_upwards [h0, hi, hna] with x hx0 hxi hxa hxm
      have hxu : x ∈ uIcc a b := by rwa [uIcc_of_le hab]
      have hxpos : a < x := lt_of_le_of_ne hxm.1 (Ne.symm hxa)
      exact hder' x (by linarith) (hpos x ⟨hxpos, hxm.2⟩) (fun i => hxi i hxu) _
        (hx0 hxu).hasDerivAt
    have hmono : ∫ x in a..b, deriv (fun s => ⨆ i, ∑ j, c i j * Q s j) x ≤ ∫ x in a..b, (-emin) :=
      intervalIntegral.integral_mono_ae_restrict hab hII (by simp)
        ((MeasureTheory.ae_restrict_iff' measurableSet_Icc).2 hae)
    simp at hmono
    nlinarith [hmono, hint]
  have hGt : (⨆ i, ∑ j, c i j * Q t j) ≤ 0 := by
    by_contra hcon
    push_neg at hcon
    let Gf : ℝ → ℝ := fun s => ⨆ i, ∑ j, c i j * Q s j
    let F : ℝ → ℝ := fun u => max 0 (1 - emin * u)
    let S : Set ℝ := Icc 0 t ∩ (fun u => F u - Gf u) ⁻¹' Ici 0
    have hGcont : ContinuousOn Gf (Icc 0 t) := hGlip.continuousOn.mono (fun x hx => hx.1)
    have hFcont : Continuous F := by fun_prop
    have hSclosed : IsClosed S :=
      (hFcont.continuousOn.sub hGcont).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    have h0S : (0 : ℝ) ∈ S := by
      refine ⟨⟨le_rfl, ht0⟩, ?_⟩
      show 0 ≤ F 0 - Gf 0
      have : F 0 = 1 := by simp [F]
      have h' : Gf 0 ≤ 1 := hG0
      linarith
    have hbddS : BddAbove S := ⟨t, fun x hx => hx.1.2⟩
    have hsS : sSup S ∈ S := hSclosed.csSup_mem ⟨0, h0S⟩ hbddS
    have hst : sSup S ≤ t := hsS.1.2
    have hs0 : 0 ≤ sSup S := hsS.1.1
    have hGs : Gf (sSup S) ≤ F (sSup S) := by
      have := hsS.2
      simp only [mem_preimage, mem_Ici] at this
      linarith
    have hFt : F t = 0 := by simp only [F]; exact max_eq_left (by linarith)
    have hs_ne : sSup S ≠ t := by
      intro h
      rw [h, hFt] at hGs
      exact absurd hGs (not_le.2 hcon)
    have hs_lt : sSup S < t := lt_of_le_of_ne hst hs_ne
    have hposI : ∀ u ∈ Ioc (sSup S) t, 0 < ⨆ i, ∑ j, c i j * Q u j := by
      intro u hu
      by_contra hneg
      push_neg at hneg
      have hu0 : 0 ≤ u := by linarith [hu.1]
      have hFu : 0 ≤ F u := le_max_left _ _
      have huS : u ∈ S := ⟨⟨hu0, hu.2⟩, by
        show 0 ≤ F u - Gf u
        have : Gf u ≤ 0 := hneg
        linarith⟩
      exact absurd (le_csSup hbddS huS) (not_le.2 hu.1)
    have hA := claimA (sSup S) t hs0 hst hposI
    have hprod : 0 ≤ emin * (t - sSup S) := mul_nonneg hemin_pos.le (sub_nonneg.2 hst)
    have hFs : F (sSup S) - emin * (t - sSup S) ≤ 0 := by
      simp only [F]
      rcases max_cases 0 (1 - emin * sSup S) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> nlinarith
    have : Gf t - Gf (sSup S) ≤ -emin * (t - sSup S) := hA
    linarith
  have hq := hsol.nonneg t ht0
  have hG1 : ∑ j, c 1 j * Q t j ≤ 0 :=
    (le_ciSup (hbdd t) 1).trans hGt
  have hG0' : ∑ j, c 0 j * Q t j ≤ 0 :=
    (le_ciSup (hbdd t) 0).trans hGt
  simp [c, Fin.sum_univ_three] at hG1 hG0'
  have q0 : Q t 0 = 0 := le_antisymm (by linarith [hq 1]) (hq 0)
  have q1 : Q t 1 = 0 := le_antisymm (by linarith [hq 0]) (hq 1)
  have q2 : Q t 2 = 0 := by
    by_contra h
    have hp : 0 < Q t 2 := lt_of_le_of_ne (hq 2) (Ne.symm h)
    nlinarith [mul_pos (sub_pos.2 hθ1) hp, mul_nonneg (sub_pos.2 hθ1).le (hq 1)]
  fin_cases k
  · exact q0
  · exact q1
  · exact q2

end DaiWeissFluid.ThreeBuffer

open DaiWeissFluid.ThreeBuffer


theorem solution (m : Fin 3 → ℝ) (hm : ∀ k, 0 < m k) (h1 : m 0 + m 2 < 1) (h2 : m 1 < 1)
    (Q T : ℝ → Fin 3 → ℝ) (hwc : (threeBuffer m).IsWorkConserving Q T)
    (hQ0 : ∑ k, Q 0 k = 1) (t : ℝ)
    (ht : max ((m 0 + m 2) / (1 - (m 0 + m 2))) (m 1 / (1 - m 1)) ≤ t) (k : Fin 3) :
    Q t k = 0 := by
  exact emptying_time_core m hm h1 h2 Q T hwc hQ0 t ht k
