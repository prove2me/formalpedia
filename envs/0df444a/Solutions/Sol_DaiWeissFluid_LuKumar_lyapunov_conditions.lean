-- Prove2me | solution 1 for DaiWeissFluid.LuKumar.lyapunov_conditions
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T15:39:48.329843+00:00
-- url     : https://prove2.me/submissions/95a9b9ca-7584-4636-9354-8540e8eac8dc

import Mathlib
import Definitions.Def_DaiWeissFluid_LuKumar_FluidModel
import Definitions.Def_DaiWeissFluid_LuKumar_Network

open Filter Topology

namespace Aux_LK_lyap
open DaiWeissFluid.LuKumar

variable {I K : ℕ}

lemma T_lip (L : ReentrantLine I K) {Q T : ℝ → Fin K → ℝ} (hsol : L.IsFluidSolution Q T)
    (k : Fin K) (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) : T y k - T x k ≤ y - x := by
  have hy : 0 ≤ y := le_trans hx hxy
  have hidle := hsol.idle_mono (L.σ k) (Set.mem_Ici.mpr hx) (Set.mem_Ici.mpr hy) hxy
  simp only [ReentrantLine.idle, ReentrantLine.busy] at hidle
  have hk : k ∈ L.C (L.σ k) := by simp [ReentrantLine.C]
  have hsum : T y k - T x k ≤ ∑ l ∈ L.C (L.σ k), (T y l - T x l) :=
    Finset.single_le_sum (f := fun l => T y l - T x l)
      (fun l _ => sub_nonneg.mpr (hsol.T_mono l (Set.mem_Ici.mpr hx) (Set.mem_Ici.mpr hy) hxy)) hk
  rw [Finset.sum_sub_distrib] at hsum
  linarith

lemma T_cont (L : ReentrantLine I K) {Q T : ℝ → Fin K → ℝ} (hsol : L.IsFluidSolution Q T)
    (k : Fin K) (t : ℝ) (ht : 0 < t) : ContinuousAt (fun u => T u k) t := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  refine ⟨min ε t, lt_min hε ht, fun {u} hu => ?_⟩
  rw [Real.dist_eq] at hu ⊢
  have hu1 : |u - t| < ε := lt_of_lt_of_le hu (min_le_left _ _)
  have hu2 : |u - t| < t := lt_of_lt_of_le hu (min_le_right _ _)
  have hu0 : 0 ≤ u := by
    have := neg_abs_le (u - t); linarith
  rcases le_total u t with h | h
  · have a1 := T_lip L hsol k u t hu0 h
    have a2 := hsol.T_mono k (Set.mem_Ici.mpr hu0) (Set.mem_Ici.mpr ht.le) h
    simp only at a2
    rw [abs_sub_comm] at hu1 ⊢
    rw [abs_of_nonneg (by linarith)]
    rw [abs_of_nonneg (by linarith)] at hu1
    linarith
  · have a1 := T_lip L hsol k t u ht.le h
    have a2 := hsol.T_mono k (Set.mem_Ici.mpr ht.le) (Set.mem_Ici.mpr hu0) h
    simp only at a2
    rw [abs_of_nonneg (by linarith)]
    rw [abs_of_nonneg (by linarith)] at hu1
    linarith

lemma Q_cont (L : ReentrantLine I K) {Q T : ℝ → Fin K → ℝ} (hsol : L.IsFluidSolution Q T)
    (k : Fin K) (t : ℝ) (ht : 0 < t) : ContinuousAt (fun u => Q u k) t := by
  have h1 : ContinuousAt (fun u => Q 0 k + L.inflow T k u - L.μ k * T u k) t := by
    unfold ReentrantLine.inflow
    split_ifs with h
    · exact (continuousAt_const.add continuousAt_id).sub
        (continuousAt_const.mul (T_cont L hsol k t ht))
    · exact (continuousAt_const.add (continuousAt_const.mul (T_cont L hsol _ t ht))).sub
        (continuousAt_const.mul (T_cont L hsol k t ht))
  have h2 : (fun u => Q 0 k + L.inflow T k u - L.μ k * T u k) =ᶠ[𝓝 t] (fun u => Q u k) := by
    filter_upwards [Ioi_mem_nhds ht] with u hu
    exact (hsol.flow u (le_of_lt hu) k).symm
  exact h1.congr h2

lemma deriv_bound (G A B : ℝ → ℝ) (a b ε d t : ℝ)
    (hG : ∀ᶠ s in 𝓝[>] t, G s - G t = (s - t) - a * (A s - A t) - b * (B s - B t) ∧
      A s - A t + (B s - B t) = s - t ∧ A t ≤ A s ∧ B t ≤ B s)
    (ha : 1 + ε ≤ a) (hb : 1 + ε ≤ b) (hd : HasDerivAt G d t) : d ≤ -ε := by
  have hT : Tendsto (slope G t) (𝓝[>] t) (𝓝 d) :=
    (hasDerivAt_iff_tendsto_slope.mp hd).mono_left (nhdsWithin_mono _ (fun x hx => ne_of_gt hx))
  apply le_of_tendsto hT
  filter_upwards [hG, self_mem_nhdsWithin] with s ⟨h1, h2, h3, h4⟩ hs
  have hst : 0 < s - t := sub_pos.mpr hs
  rw [slope_def_field, div_le_iff₀ hst, h1]
  have e1 : (1 + ε) * (A s - A t) ≤ a * (A s - A t) :=
    mul_le_mul_of_nonneg_right ha (sub_nonneg.mpr h3)
  have e2 : (1 + ε) * (B s - B t) ≤ b * (B s - B t) :=
    mul_le_mul_of_nonneg_right hb (sub_nonneg.mpr h4)
  have e3 : ε * (A s - A t + (B s - B t)) = ε * (s - t) := by rw [h2]
  nlinarith

lemma C0_sum (m : Fin 4 → ℝ) (f : Fin 4 → ℝ) : ∑ k ∈ (luKumar m).C 0, f k = f 0 + f 3 := by
  unfold ReentrantLine.C
  rw [Finset.sum_filter, Fin.sum_univ_four]
  simp [luKumar]

lemma C1_sum (m : Fin 4 → ℝ) (f : Fin 4 → ℝ) : ∑ k ∈ (luKumar m).C 1, f k = f 1 + f 2 := by
  unfold ReentrantLine.C
  rw [Finset.sum_filter, Fin.sum_univ_four]
  simp [luKumar]

lemma Qp0 (Q : ℝ → Fin 4 → ℝ) (t : ℝ) : Qplus Q 0 t = Q t 0 := by
  unfold Qplus; rw [Finset.sum_filter, Fin.sum_univ_four]; simp
lemma Qp1 (Q : ℝ → Fin 4 → ℝ) (t : ℝ) : Qplus Q 1 t = Q t 0 + Q t 1 := by
  unfold Qplus; rw [Finset.sum_filter, Fin.sum_univ_four]; simp
lemma Qp2 (Q : ℝ → Fin 4 → ℝ) (t : ℝ) : Qplus Q 2 t = Q t 0 + Q t 1 + Q t 2 := by
  unfold Qplus; rw [Finset.sum_filter, Fin.sum_univ_four]; simp
lemma Qp3 (Q : ℝ → Fin 4 → ℝ) (t : ℝ) : Qplus Q 3 t = Q t 0 + Q t 1 + Q t 2 + Q t 3 := by
  unfold Qplus; rw [Finset.sum_filter, Fin.sum_univ_four]; simp

lemma in0 (m : Fin 4 → ℝ) (T : ℝ → Fin 4 → ℝ) (s : ℝ) : (luKumar m).inflow T 0 s = s := by
  unfold ReentrantLine.inflow; rfl
lemma in1 (m : Fin 4 → ℝ) (T : ℝ → Fin 4 → ℝ) (s : ℝ) :
    (luKumar m).inflow T 1 s = (m 0)⁻¹ * T s 0 := by
  unfold ReentrantLine.inflow ReentrantLine.μ; rfl
lemma in2 (m : Fin 4 → ℝ) (T : ℝ → Fin 4 → ℝ) (s : ℝ) :
    (luKumar m).inflow T 2 s = (m 1)⁻¹ * T s 1 := by
  unfold ReentrantLine.inflow ReentrantLine.μ; rfl
lemma in3 (m : Fin 4 → ℝ) (T : ℝ → Fin 4 → ℝ) (s : ℝ) :
    (luKumar m).inflow T 3 s = (m 2)⁻¹ * T s 2 := by
  unfold ReentrantLine.inflow ReentrantLine.μ; rfl
lemma mu (m : Fin 4 → ℝ) (k : Fin 4) : (luKumar m).μ k = (m k)⁻¹ := rfl

end Aux_LK_lyap

open DaiWeissFluid.LuKumar in
theorem solution (m : Fin 4 → ℝ) (hm : ∀ k, 0 < m k)
    (h51₁ : m 0 + m 3 < 1) (h51₂ : m 1 + m 2 < 1)
    (h52 : m 1 + m 3 < 1)
    (θ1 θ2 : ℝ)
    (hθ1a : m 0 < θ1) (hθ1b : θ1 < 1 - m 3)
    (hθ2a : m 1 < θ2) (hθ2b : θ2 < 1 - m 2)
    (hθorder : θ2 ≤ θ1)
    (Q T : ℝ → Fin 4 → ℝ) (hsol : (luKumar m).IsWorkConserving Q T) :
    (0 < min (θ1 * (m 0)⁻¹ - 1) ((1 - θ1) * (m 3)⁻¹ - 1)) ∧
    (0 < min (θ2 * (m 1)⁻¹ - 1) ((1 - θ2) * (m 2)⁻¹ - 1)) ∧
    (∀ t d, 0 < t → 0 < (luKumar m).volume Q 0 t →
      HasDerivAt (G1 θ1 Q) d t →
      d ≤ -min (θ1 * (m 0)⁻¹ - 1) ((1 - θ1) * (m 3)⁻¹ - 1)) ∧
    (∀ t d, 0 < t → 0 < (luKumar m).volume Q 1 t →
      HasDerivAt (G2 θ2 Q) d t →
      d ≤ -min (θ2 * (m 1)⁻¹ - 1) ((1 - θ2) * (m 2)⁻¹ - 1)) ∧
    (∀ t, 0 ≤ t → (luKumar m).volume Q 1 t = 0 → G2 θ2 Q t ≤ G1 θ1 Q t) ∧
    (∀ t, 0 ≤ t → (luKumar m).volume Q 0 t = 0 → G1 θ1 Q t ≤ G2 θ2 Q t) := by
  obtain ⟨hfl, hwc⟩ := hsol
  have hgt : ∀ a b : ℝ, 0 < b → b < a → 0 < a * b⁻¹ - 1 := by
    intro a b hb hab
    have : 1 < a * b⁻¹ := by rw [← div_eq_mul_inv, one_lt_div hb]; exact hab
    linarith
  have P1 : 0 < min (θ1 * (m 0)⁻¹ - 1) ((1 - θ1) * (m 3)⁻¹ - 1) :=
    lt_min (hgt _ _ (hm 0) hθ1a) (hgt _ _ (hm 3) (by linarith))
  have P2 : 0 < min (θ2 * (m 1)⁻¹ - 1) ((1 - θ2) * (m 2)⁻¹ - 1) :=
    lt_min (hgt _ _ (hm 1) hθ2a) (hgt _ _ (hm 2) (by linarith))
  -- flows
  have f0 : ∀ s, 0 ≤ s → Q s 0 = Q 0 0 + s - (m 0)⁻¹ * T s 0 := by
    intro s hs; rw [hfl.flow s hs 0, Aux_LK_lyap.in0, Aux_LK_lyap.mu]
  have f1 : ∀ s, 0 ≤ s → Q s 1 = Q 0 1 + (m 0)⁻¹ * T s 0 - (m 1)⁻¹ * T s 1 := by
    intro s hs; rw [hfl.flow s hs 1, Aux_LK_lyap.in1, Aux_LK_lyap.mu]
  have f2 : ∀ s, 0 ≤ s → Q s 2 = Q 0 2 + (m 1)⁻¹ * T s 1 - (m 2)⁻¹ * T s 2 := by
    intro s hs; rw [hfl.flow s hs 2, Aux_LK_lyap.in2, Aux_LK_lyap.mu]
  have f3 : ∀ s, 0 ≤ s → Q s 3 = Q 0 3 + (m 2)⁻¹ * T s 2 - (m 3)⁻¹ * T s 3 := by
    intro s hs; rw [hfl.flow s hs 3, Aux_LK_lyap.in3, Aux_LK_lyap.mu]
  have hG1 : ∀ s, 0 ≤ s → G1 θ1 Q s = θ1 * (Q 0 0 + s - (m 0)⁻¹ * T s 0) +
      (1 - θ1) * (Q 0 0 + Q 0 1 + Q 0 2 + Q 0 3 + s - (m 3)⁻¹ * T s 3) := by
    intro s hs
    unfold G1
    rw [Aux_LK_lyap.Qp0, Aux_LK_lyap.Qp3, f0 s hs, f1 s hs, f2 s hs, f3 s hs]
    ring
  have hG2 : ∀ s, 0 ≤ s → G2 θ2 Q s = θ2 * (Q 0 0 + Q 0 1 + s - (m 1)⁻¹ * T s 1) +
      (1 - θ2) * (Q 0 0 + Q 0 1 + Q 0 2 + s - (m 2)⁻¹ * T s 2) := by
    intro s hs
    unfold G2
    rw [Aux_LK_lyap.Qp1, Aux_LK_lyap.Qp2, f0 s hs, f1 s hs, f2 s hs]
    ring
  -- busy-period lemma
  have busy : ∀ (i : Fin 2) (k₁ k₂ : Fin 4),
      (∀ f : Fin 4 → ℝ, ∑ k ∈ (luKumar m).C i, f k = f k₁ + f k₂) →
      ∀ t, 0 < t → 0 < Q t k₁ + Q t k₂ →
      ∀ᶠ s in 𝓝[>] t, T s k₁ - T t k₁ + (T s k₂ - T t k₂) = s - t ∧
        T t k₁ ≤ T s k₁ ∧ T t k₂ ≤ T s k₂ := by
    intro i k₁ k₂ hC t ht hpos
    have hcont : ContinuousAt (fun u => Q u k₁ + Q u k₂) t :=
      (Aux_LK_lyap.Q_cont _ hfl k₁ t ht).add (Aux_LK_lyap.Q_cont _ hfl k₂ t ht)
    have hev : ∀ᶠ u in 𝓝 t, 0 < Q u k₁ + Q u k₂ := hcont.tendsto.eventually (lt_mem_nhds hpos)
    obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.mp hev
    filter_upwards [Ioo_mem_nhdsGT (show t < t + δ by linarith)] with s hs
    have hcw := hwc i t s ht.le hs.1.le (fun u hu => by
      show 0 < ∑ k ∈ (luKumar m).C i, Q u k
      rw [hC (fun k => Q u k)]
      apply hδ'
      rw [Real.dist_eq, abs_of_nonneg (by linarith [hu.1])]
      linarith [hu.2, hs.2])
    simp only [ReentrantLine.idle, ReentrantLine.busy] at hcw
    rw [hC (fun k => T s k), hC (fun k => T t k)] at hcw
    refine ⟨by linarith, ?_, ?_⟩
    · exact hfl.T_mono k₁ (Set.mem_Ici.mpr ht.le) (Set.mem_Ici.mpr (by linarith [hs.1])) hs.1.le
    · exact hfl.T_mono k₂ (Set.mem_Ici.mpr ht.le) (Set.mem_Ici.mpr (by linarith [hs.1])) hs.1.le
  have volpos : ∀ (a b : Fin 4) (t : ℝ), 0 ≤ t → 0 < m a * Q t a + m b * Q t b →
      0 < Q t a + Q t b := by
    intro a b t ht h
    have qa := hfl.nonneg t ht a
    have qb := hfl.nonneg t ht b
    by_contra hc
    push_neg at hc
    have za : Q t a = 0 := by linarith
    have zb : Q t b = 0 := by linarith
    rw [za, zb] at h
    simp at h
  have volzero : ∀ (a b : Fin 4) (t : ℝ), 0 ≤ t → m a * Q t a + m b * Q t b = 0 →
      Q t a = 0 ∧ Q t b = 0 := by
    intro a b t ht h
    have qa := mul_nonneg (hm a).le (hfl.nonneg t ht a)
    have qb := mul_nonneg (hm b).le (hfl.nonneg t ht b)
    have ea : m a * Q t a = 0 := by linarith
    have eb : m b * Q t b = 0 := by linarith
    exact ⟨(mul_eq_zero.mp ea).resolve_left (hm a).ne', (mul_eq_zero.mp eb).resolve_left (hm b).ne'⟩
  refine ⟨P1, P2, ?_, ?_, ?_, ?_⟩
  · intro t d ht hvol hd
    unfold ReentrantLine.volume at hvol
    rw [Aux_LK_lyap.C0_sum m (fun k => (luKumar m).m k * Q t k)] at hvol
    have hpos := volpos 0 3 t ht.le hvol
    have hb := busy 0 0 3 (Aux_LK_lyap.C0_sum m) t ht hpos
    apply Aux_LK_lyap.deriv_bound (G1 θ1 Q) (fun s => T s 0) (fun s => T s 3)
      (θ1 * (m 0)⁻¹) ((1 - θ1) * (m 3)⁻¹) _ d t _
      (by linarith [min_le_left (θ1 * (m 0)⁻¹ - 1) ((1 - θ1) * (m 3)⁻¹ - 1)])
      (by linarith [min_le_right (θ1 * (m 0)⁻¹ - 1) ((1 - θ1) * (m 3)⁻¹ - 1)]) hd
    filter_upwards [hb, self_mem_nhdsWithin] with s ⟨h1, h2, h3⟩ hs
    refine ⟨?_, h1, h2, h3⟩
    have hs0 : 0 ≤ s := by have := Set.mem_Ioi.mp hs; linarith
    rw [hG1 s hs0, hG1 t ht.le]
    ring
  · intro t d ht hvol hd
    unfold ReentrantLine.volume at hvol
    rw [Aux_LK_lyap.C1_sum m (fun k => (luKumar m).m k * Q t k)] at hvol
    have hpos := volpos 1 2 t ht.le hvol
    have hb := busy 1 1 2 (Aux_LK_lyap.C1_sum m) t ht hpos
    apply Aux_LK_lyap.deriv_bound (G2 θ2 Q) (fun s => T s 1) (fun s => T s 2)
      (θ2 * (m 1)⁻¹) ((1 - θ2) * (m 2)⁻¹) _ d t _
      (by linarith [min_le_left (θ2 * (m 1)⁻¹ - 1) ((1 - θ2) * (m 2)⁻¹ - 1)])
      (by linarith [min_le_right (θ2 * (m 1)⁻¹ - 1) ((1 - θ2) * (m 2)⁻¹ - 1)]) hd
    filter_upwards [hb, self_mem_nhdsWithin] with s ⟨h1, h2, h3⟩ hs
    refine ⟨?_, h1, h2, h3⟩
    have hs0 : 0 ≤ s := by have := Set.mem_Ioi.mp hs; linarith
    rw [hG2 s hs0, hG2 t ht.le]
    ring
  · intro t ht hvol
    unfold ReentrantLine.volume at hvol
    rw [Aux_LK_lyap.C1_sum m (fun k => (luKumar m).m k * Q t k)] at hvol
    obtain ⟨z1, z2⟩ := volzero 1 2 t ht hvol
    unfold G1 G2
    rw [Aux_LK_lyap.Qp0, Aux_LK_lyap.Qp1, Aux_LK_lyap.Qp2, Aux_LK_lyap.Qp3, z1, z2]
    have q3 := hfl.nonneg t ht 3
    have : 0 ≤ (1 - θ1) * Q t 3 := mul_nonneg (by linarith [hm 3]) q3
    nlinarith
  · intro t ht hvol
    unfold ReentrantLine.volume at hvol
    rw [Aux_LK_lyap.C0_sum m (fun k => (luKumar m).m k * Q t k)] at hvol
    obtain ⟨z0, z3⟩ := volzero 0 3 t ht hvol
    unfold G1 G2
    rw [Aux_LK_lyap.Qp0, Aux_LK_lyap.Qp1, Aux_LK_lyap.Qp2, Aux_LK_lyap.Qp3, z0, z3]
    have q1 := hfl.nonneg t ht 1
    have q2 := hfl.nonneg t ht 2
    have a1 : 0 ≤ θ1 * Q t 1 := mul_nonneg (by linarith [hm 0]) q1
    have a2 : 0 ≤ (θ1 - θ2) * Q t 2 := mul_nonneg (by linarith) q2
    nlinarith
