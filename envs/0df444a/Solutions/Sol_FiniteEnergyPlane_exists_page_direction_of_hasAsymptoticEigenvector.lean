-- Prove2me | solution 1 for FiniteEnergyPlane.exists_page_direction_of_hasAsymptoticEigenvector
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-21T15:45:04.38512+00:00
-- url     : https://prove2.me/submissions/46a0984b-b301-4fd4-81d8-b2d3413b23d0

import Definitions.Def_FiniteEnergyPlane_OpenBook
import Theorems.Thm_FiniteEnergyPlane_continuousOn_of_strictMonoOn_of_apply_eq
import Theorems.Thm_FiniteEnergyPlane_exists_mul_norm_le_unitaryXiFrame
import Theorems.Thm_FiniteEnergyPlane_isAsymptoticEigen_apply_ne_zero_of_unitaryXiFrame
import Theorems.Thm_FiniteEnergyPlane_exists_norm_sub_le_mul_abs_of_periodic
import Theorems.Thm_FiniteEnergyPlane_exists_norm_le_and_norm_sub_le_of_tendstoZeroCInfty
import Theorems.Thm_DbarRegularity_norm_inv_norm_smul_sub_le

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal Real

/-!
# Base layer for `exists_page_direction_of_hasAsymptoticEigenvector` (87bebfe8)

Thin wrappers over published helpers (the proofs of the new ones are in `Scratch/PD_help.lean`).
-/


namespace FiniteEnergyPlane

noncomputable section

theorem pd_periodic_bound {F : Type*} [NormedAddCommGroup F] {f : ℝ → F} (hf : Continuous f)
    (hper : Function.Periodic f 1) : ∃ B, 0 ≤ B ∧ ∀ t, ‖f t‖ ≤ B := by
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hf.continuousOn
  refine ⟨max K 0, le_max_right _ _, fun t => ?_⟩
  obtain ⟨y, hy, hyt⟩ := hper.exists_mem_Ico zero_lt_one t 0
  rw [hyt]
  exact (hK y ⟨hy.1, by linarith [hy.2]⟩).trans (le_max_left _ _)

theorem pd_periodic_lip {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℝ → F}
    (hf : ContDiff ℝ ∞ f) (hper : Function.Periodic f 1) :
    ∃ L, 0 ≤ L ∧ ∀ x y, ‖f x - f y‖ ≤ L * |x - y| :=
  exists_norm_sub_le_mul_abs_of_periodic (hf.of_le (by simp)) hper

theorem pd_frame_lower {H : V 1 → ℝ} {J : V 1 → V 1 →L[ℝ] V 1} {P : ReebOrbit H}
    {Z : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1} (hZ : IsUnitaryXiFrame J P Z) :
    ∃ c > 0, ∀ t a, c * ‖a‖ ≤ ‖Z t a‖ :=
  exists_mul_norm_le_unitaryXiFrame hZ

theorem pd_eigen_ne_zero {H : V 1 → ℝ} {J : V 1 → V 1 →L[ℝ] V 1} {P : ReebOrbit H}
    {Z : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1} (hH : IsStrictlyStarShapedLevel H)
    (hZ : IsUnitaryXiFrame J P Z) {μ : ℝ} {v : ℝ → V 1} (hv : IsAsymptoticEigen J P μ v)
    (t : ℝ) : v t ≠ 0 :=
  isAsymptoticEigen_apply_ne_zero_of_unitaryXiFrame hH hZ hv t

/-- Lipschitz and sup bounds from `C^∞` decay on the end, plus continuity. -/
theorem pd_tendsto_lip {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℝ × ℝ → F}
    (hf : TendstoZeroCInfty f) (η : ℝ) (hη : 0 < η) : ∃ S : ℝ,
      (∀ p : ℝ × ℝ, S ≤ p.1 → ‖f p‖ ≤ η) ∧
      (∀ p q : ℝ × ℝ, S ≤ p.1 → S ≤ q.1 → ‖f p - f q‖ ≤ η * ‖p - q‖) ∧
      ContinuousOn f (Ici S ×ˢ univ) := by
  obtain ⟨S₁, hS₁⟩ := exists_norm_le_and_norm_sub_le_of_tendstoZeroCInfty hf η hη
  obtain ⟨s₀, hs₀⟩ := hf.1
  set S := max S₁ (s₀ + 1) with hS
  have h1 : S₁ ≤ S := le_max_left _ _
  refine ⟨S, fun p hp => (hS₁ p p (h1.trans hp) (h1.trans hp)).1,
    fun p q hp hq => (hS₁ p q (h1.trans hp) (h1.trans hq)).2, ?_⟩
  refine hs₀.continuousOn.mono (fun x hx => ⟨?_, trivial⟩)
  simp only [mem_Ioi]
  linarith [le_max_right S₁ (s₀ + 1), (show S ≤ x.1 from hx.1)]

theorem pd_continuousOn_of_strictMonoOn {X : Type*} [TopologicalSpace X] {S : Set X}
    {I : Set ℝ} (hI : IsOpen I) (F : X → ℝ → ℝ)
    (hF : ∀ s ∈ I, ContinuousOn (fun x => F x s) S) (hmono : ∀ x ∈ S, StrictMonoOn (F x) I)
    (G y : X → ℝ) (hG : ∀ x ∈ S, G x ∈ I) (hy : ContinuousOn y S)
    (hFG : ∀ x ∈ S, F x (G x) = y x) : ContinuousOn G S :=
  continuousOn_of_strictMonoOn_of_apply_eq hI F hF hmono G y hG hy hFG

theorem pd_normalize_sub_le (x y : CauchyRiemannIndex.Vec 1) (_hx : x ≠ 0) (hy : y ≠ 0) :
    ‖‖x‖⁻¹ • x - ‖y‖⁻¹ • y‖ ≤ 2 * ‖x - y‖ / ‖y‖ :=
  DbarRegularity.norm_inv_norm_smul_sub_le x y hy

end

end FiniteEnergyPlane

/-!
# Core construction for `exists_page_direction_of_hasAsymptoticEigenvector` (87bebfe8)

Abstract setting: `Z (τ p / T) (b p) = v (τ p / T) + r p` on `s ≥ s₁`, with `τ - Tt - c₀` and `r`
small in `C¹`. We solve `e^{μ s} ‖b (s, t)‖ = ρ` for `s = σ (t, ρ)` and then `τ (σ, t) = τ₀`
for `t = θ (τ₀, ρ)`, both continuously.
-/


namespace FiniteEnergyPlane

noncomputable section

theorem pd_norm_pair (a b : ℝ) : ‖((a, b) : ℝ × ℝ)‖ = max |a| |b| := by
  simp only [Prod.norm_def, Real.norm_eq_abs]

theorem pd_norm_le (p : ℝ × ℝ) : ‖p‖ ≤ |p.1| + |p.2| := by
  simp only [Prod.norm_def, Real.norm_eq_abs]
  exact max_le_add_of_nonneg (abs_nonneg _) (abs_nonneg _)

theorem pd_norm_s (s s' t : ℝ) : ‖((s, t) : ℝ × ℝ) - (s', t)‖ = |s - s'| := by
  rw [Prod.mk_sub_mk, pd_norm_pair, sub_self, abs_zero]
  exact max_eq_left (abs_nonneg _)

theorem pd_norm_t (s t t' : ℝ) : ‖((s, t) : ℝ × ℝ) - (s, t')‖ = |t - t'| := by
  rw [Prod.mk_sub_mk, pd_norm_pair, sub_self, abs_zero]
  exact max_eq_right (abs_nonneg _)

structure PDHyp (T μ c₀ s₁ η cZ LZ Lv Vm m A K : ℝ) (τ : ℝ × ℝ → ℝ) (r : ℝ × ℝ → V 1)
    (b : ℝ × ℝ → CauchyRiemannIndex.Vec 1) (Z : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1)
    (v : ℝ → V 1) (E : ℝ → CauchyRiemannIndex.Vec 1) : Prop where
  T_pos : 0 < T
  μ_neg : μ < 0
  η_pos : 0 < η
  η_le_one : η ≤ 1
  cZ_pos : 0 < cZ
  LZ_nn : 0 ≤ LZ
  Lv_nn : 0 ≤ Lv
  m_pos : 0 < m
  Zlow : ∀ t a, cZ * ‖a‖ ≤ ‖Z t a‖
  Zlip : ∀ x y, ‖Z x - Z y‖ ≤ LZ * |x - y|
  vlip : ∀ x y, ‖v x - v y‖ ≤ Lv * |x - y|
  vbd : ∀ t, ‖v t‖ ≤ Vm
  hE : ∀ t, Z t (E t) = v t
  Elow : ∀ t, m ≤ ‖E t‖
  g_bd : ∀ p : ℝ × ℝ, s₁ ≤ p.1 → |τ p - T * p.2 - c₀| ≤ η
  g_lip : ∀ p q : ℝ × ℝ, s₁ ≤ p.1 → s₁ ≤ q.1 →
    |(τ p - T * p.2 - c₀) - (τ q - T * q.2 - c₀)| ≤ η * ‖p - q‖
  r_bd : ∀ p : ℝ × ℝ, s₁ ≤ p.1 → ‖r p‖ ≤ η
  r_lip : ∀ p q : ℝ × ℝ, s₁ ≤ p.1 → s₁ ≤ q.1 → ‖r p - r q‖ ≤ η * ‖p - q‖
  τ_cont : ContinuousOn τ (Ici s₁ ×ˢ univ)
  hb : ∀ p : ℝ × ℝ, s₁ ≤ p.1 → Z (τ p / T) (b p) = v (τ p / T) + r p
  hA : A = Lv + LZ * ((Vm + 1) / cZ)
  hK : K = 4 * ((A * (1 + 1 / T) + 1) / cZ) / (-μ * m)
  hη1 : η ≤ cZ * m / 2
  hη2 : η * (A / T + 1) / cZ ≤ -μ * m / 4
  hη3 : η * (1 + K) ≤ T / 2

/-- `N (s, t) = e^{μ s} ‖b (s, t)‖`. -/
def pdN (μ : ℝ) (b : ℝ × ℝ → CauchyRiemannIndex.Vec 1) (p : ℝ × ℝ) : ℝ :=
  Real.exp (μ * p.1) * ‖b p‖

section Core

variable {T μ c₀ s₁ η cZ LZ Lv Vm m A K : ℝ} {τ : ℝ × ℝ → ℝ} {r : ℝ × ℝ → V 1}
  {b : ℝ × ℝ → CauchyRiemannIndex.Vec 1} {Z : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1}
  {v : ℝ → V 1} {E : ℝ → CauchyRiemannIndex.Vec 1}
  (h : PDHyp T μ c₀ s₁ η cZ LZ Lv Vm m A K τ r b Z v E)
include h

theorem pd_Vm_nn : 0 ≤ Vm := (norm_nonneg _).trans (h.vbd 0)

theorem pd_A_nn : 0 ≤ A := by
  rw [h.hA]
  have := pd_Vm_nn h
  have := h.cZ_pos
  have := h.LZ_nn
  have := h.Lv_nn
  positivity

theorem pd_K_nn : 0 ≤ K := by
  rw [h.hK]
  have := pd_A_nn h
  have := h.cZ_pos
  have := h.T_pos
  have hμ : 0 < -μ * m := mul_pos (neg_pos.2 h.μ_neg) h.m_pos
  positivity

theorem pd_b_bd {p : ℝ × ℝ} (hp : s₁ ≤ p.1) : ‖b p‖ ≤ (Vm + 1) / cZ := by
  rw [le_div_iff₀ h.cZ_pos]
  have h1 := h.Zlow (τ p / T) (b p)
  rw [h.hb p hp] at h1
  have h2 := norm_add_le (v (τ p / T)) (r p)
  have := h.vbd (τ p / T)
  have := h.r_bd p hp
  have := h.η_le_one
  linarith

theorem pd_b_sub_E {p : ℝ × ℝ} (hp : s₁ ≤ p.1) : cZ * ‖b p - E (τ p / T)‖ ≤ ‖r p‖ := by
  have h1 := h.Zlow (τ p / T) (b p - E (τ p / T))
  rwa [map_sub, h.hb p hp, h.hE, add_sub_cancel_left] at h1

theorem pd_b_low {p : ℝ × ℝ} (hp : s₁ ≤ p.1) : m / 2 ≤ ‖b p‖ := by
  have h1 := pd_b_sub_E h hp
  have h2 := h.Elow (τ p / T)
  have h3 := norm_sub_norm_le (E (τ p / T)) (b p)
  rw [norm_sub_rev] at h3
  have h4 := h.r_bd p hp
  have h5 := h.hη1
  have h6 : ‖b p - E (τ p / T)‖ ≤ m / 2 := by
    have : cZ * ‖b p - E (τ p / T)‖ ≤ cZ * (m / 2) := by linarith
    exact le_of_mul_le_mul_left this h.cZ_pos
  linarith

theorem pd_b_ne_zero {p : ℝ × ℝ} (hp : s₁ ≤ p.1) : b p ≠ 0 := by
  intro h0
  have := pd_b_low h hp
  rw [h0, norm_zero] at this
  linarith [h.m_pos]

theorem pd_theta_diff {p q : ℝ × ℝ} (hp : s₁ ≤ p.1) (hq : s₁ ≤ q.1) :
    |τ p / T - τ q / T| ≤ |p.2 - q.2| + η * ‖p - q‖ / T := by
  have hg := h.g_lip p q hp hq
  have hT := h.T_pos
  have : τ p / T - τ q / T =
      (p.2 - q.2) + ((τ p - T * p.2 - c₀) - (τ q - T * q.2 - c₀)) / T := by
    field_simp; ring
  rw [this]
  refine (abs_add_le _ _).trans ?_
  rw [abs_div, abs_of_pos hT]
  gcongr

theorem pd_b_diff {p q : ℝ × ℝ} (hp : s₁ ≤ p.1) (hq : s₁ ≤ q.1) :
    cZ * ‖b p - b q‖ ≤ A * |τ p / T - τ q / T| + ‖r p - r q‖ := by
  have h1 := h.Zlow (τ p / T) (b p - b q)
  have hkey : Z (τ p / T) (b p - b q) = (v (τ p / T) - v (τ q / T)) + (r p - r q) +
      (Z (τ q / T) - Z (τ p / T)) (b q) := by
    rw [map_sub, h.hb p hp, ContinuousLinearMap.sub_apply, h.hb q hq]
    abel
  rw [hkey] at h1
  have h2 : ‖(v (τ p / T) - v (τ q / T)) + (r p - r q) + (Z (τ q / T) - Z (τ p / T)) (b q)‖ ≤
      ‖v (τ p / T) - v (τ q / T)‖ + ‖r p - r q‖ + ‖(Z (τ q / T) - Z (τ p / T)) (b q)‖ :=
    norm_add₃_le
  have h3 := h.vlip (τ p / T) (τ q / T)
  have h4 : ‖(Z (τ q / T) - Z (τ p / T)) (b q)‖ ≤ LZ * |τ p / T - τ q / T| * ((Vm + 1) / cZ) := by
    refine ((Z (τ q / T) - Z (τ p / T)).le_opNorm _).trans ?_
    have h5 := h.Zlip (τ q / T) (τ p / T)
    rw [abs_sub_comm] at h5
    exact mul_le_mul h5 (pd_b_bd h hq) (norm_nonneg _)
      (mul_nonneg h.LZ_nn (abs_nonneg _))
  rw [h.hA]
  nlinarith

theorem pd_b_lip {p q : ℝ × ℝ} (hp : s₁ ≤ p.1) (hq : s₁ ≤ q.1) :
    ‖b p - b q‖ ≤ ((A * (1 + 1 / T) + 1) / cZ) * ‖p - q‖ := by
  have h1 := pd_b_diff h hp hq
  have h2 := pd_theta_diff h hp hq
  have h3 := h.r_lip p q hp hq
  have h4 : |p.2 - q.2| ≤ ‖p - q‖ := norm_snd_le (p - q)
  have hT := h.T_pos
  have hA0 := pd_A_nn h
  have hn := norm_nonneg (p - q)
  have h5 : η * ‖p - q‖ / T ≤ ‖p - q‖ / T := by
    gcongr
    exact mul_le_of_le_one_left hn h.η_le_one
  have h6 : |τ p / T - τ q / T| ≤ (1 + 1 / T) * ‖p - q‖ := by
    have : (1 + 1 / T) * ‖p - q‖ = ‖p - q‖ + ‖p - q‖ / T := by ring
    linarith
  have h7 : A * |τ p / T - τ q / T| ≤ A * ((1 + 1 / T) * ‖p - q‖) :=
    mul_le_mul_of_nonneg_left h6 hA0
  have h8 : η * ‖p - q‖ ≤ ‖p - q‖ := mul_le_of_le_one_left hn h.η_le_one
  rw [div_mul_eq_mul_div, le_div_iff₀ h.cZ_pos]
  nlinarith

theorem pd_b_lip_s {s s' t : ℝ} (hs : s₁ ≤ s) (hs' : s₁ ≤ s') :
    ‖b (s, t) - b (s', t)‖ ≤ (η * (A / T + 1) / cZ) * |s - s'| := by
  have h1 := pd_b_diff h (p := (s, t)) (q := (s', t)) hs hs'
  have h2 := pd_theta_diff h (p := (s, t)) (q := (s', t)) hs hs'
  have h3 := h.r_lip (s, t) (s', t) hs hs'
  rw [pd_norm_s] at h2 h3
  simp only [sub_self, abs_zero, zero_add] at h2
  have hA0 := pd_A_nn h
  have h7 : A * |τ (s, t) / T - τ (s', t) / T| ≤ A * (η * |s - s'| / T) :=
    mul_le_mul_of_nonneg_left h2 hA0
  rw [div_mul_eq_mul_div, le_div_iff₀ h.cZ_pos]
  have : A * (η * |s - s'| / T) + η * |s - s'| = η * (A / T + 1) * |s - s'| := by
    field_simp
  nlinarith

theorem pd_b_cont : ContinuousOn b (Ici s₁ ×ˢ univ) := by
  rw [Metric.continuousOn_iff]
  intro p hp ε hε
  set L := (A * (1 + 1 / T) + 1) / cZ with hL
  have hL0 : 0 < L := by
    have := pd_A_nn h
    have := h.T_pos
    have := h.cZ_pos
    positivity
  refine ⟨ε / L, div_pos hε hL0, fun q hq hqp => ?_⟩
  rw [dist_eq_norm] at hqp ⊢
  have := pd_b_lip h hq.1 hp.1
  calc ‖b q - b p‖ ≤ L * ‖q - p‖ := this
    _ < L * (ε / L) := mul_lt_mul_of_pos_left hqp hL0
    _ = ε := by field_simp

theorem pd_N_anti {s s' t : ℝ} (hs : s₁ ≤ s) (hss' : s < s') :
    pdN μ b (s', t) < pdN μ b (s, t) := by
  unfold pdN
  simp only
  have hs' : s₁ ≤ s' := hs.trans hss'.le
  have hlip := pd_b_lip_s h (t := t) hs' hs
  rw [abs_of_pos (sub_pos.2 hss')] at hlip
  have hn := norm_sub_norm_le (b (s', t)) (b (s, t))
  have hC : η * (A / T + 1) / cZ * (s' - s) ≤ -μ * m / 4 * (s' - s) :=
    mul_le_mul_of_nonneg_right h.hη2 (sub_pos.2 hss').le
  have hlow := pd_b_low h (p := (s, t)) hs
  have hd : 0 < -μ * (s' - s) := mul_pos (neg_pos.2 h.μ_neg) (sub_pos.2 hss')
  have hstrict : -μ * (s' - s) * (m / 4) < -μ * (s' - s) * ‖b (s, t)‖ :=
    mul_lt_mul_of_pos_left (by linarith [h.m_pos]) hd
  have hexp : -μ * (s' - s) + 1 ≤ Real.exp (-μ * (s' - s)) := Real.add_one_le_exp _
  have hexp' : (-μ * (s' - s) + 1) * ‖b (s, t)‖ ≤ Real.exp (-μ * (s' - s)) * ‖b (s, t)‖ :=
    mul_le_mul_of_nonneg_right hexp (norm_nonneg _)
  have key : ‖b (s', t)‖ < Real.exp (-μ * (s' - s)) * ‖b (s, t)‖ := by nlinarith
  have e1 : Real.exp (μ * s') = Real.exp (μ * s) * Real.exp (μ * (s' - s)) := by
    rw [← Real.exp_add]; congr 1; ring
  have e2 : Real.exp (μ * (s' - s)) * Real.exp (-μ * (s' - s)) = 1 := by
    rw [← Real.exp_add, show μ * (s' - s) + -μ * (s' - s) = 0 by ring, Real.exp_zero]
  calc Real.exp (μ * s') * ‖b (s', t)‖
      = Real.exp (μ * s) * (Real.exp (μ * (s' - s)) * ‖b (s', t)‖) := by rw [e1]; ring
    _ < Real.exp (μ * s) * (Real.exp (μ * (s' - s)) *
        (Real.exp (-μ * (s' - s)) * ‖b (s, t)‖)) := by gcongr
    _ = Real.exp (μ * s) * ‖b (s, t)‖ := by rw [← mul_assoc (Real.exp (μ * (s' - s))), e2, one_mul]

theorem pd_N_cont : ContinuousOn (pdN μ b) (Ici s₁ ×ˢ univ) := by
  unfold pdN
  exact ((Real.continuous_exp.comp (continuous_const.mul continuous_fst)).continuousOn).mul
    (pd_b_cont h).norm

theorem pd_N_low {p : ℝ × ℝ} (hp : s₁ ≤ p.1) : Real.exp (μ * p.1) * (m / 2) ≤ pdN μ b p :=
  mul_le_mul_of_nonneg_left (pd_b_low h hp) (Real.exp_pos _).le

theorem pd_N_up {p : ℝ × ℝ} (hp : s₁ ≤ p.1) :
    pdN μ b p ≤ Real.exp (μ * p.1) * ((Vm + 1) / cZ) :=
  mul_le_mul_of_nonneg_left (pd_b_bd h hp) (Real.exp_pos _).le

theorem pd_sigma_exists {t ρ : ℝ} (hρ : ρ ∈ Ioo 0 (Real.exp (μ * (s₁ + 1)) * (m / 2))) :
    ∃ σ, s₁ + 1 < σ ∧ pdN μ b (σ, t) = ρ := by
  set Bm' := (Vm + 1) / cZ + 1 with hBm'
  have hBm'0 : 0 < Bm' := by
    have := pd_Vm_nn h; have := h.cZ_pos; positivity
  set S₂ := max (s₁ + 2) (Real.log (ρ / Bm') / μ + 1) with hS₂
  have h1 : Real.log (ρ / Bm') / μ < S₂ := lt_of_lt_of_le (lt_add_one _) (le_max_right _ _)
  have h2 : μ * S₂ < Real.log (ρ / Bm') := by
    have := (div_lt_iff_of_neg h.μ_neg).1 h1; linarith
  have h3 : Real.exp (μ * S₂) < ρ / Bm' := by
    rw [← Real.exp_log (div_pos hρ.1 hBm'0)]; exact Real.exp_lt_exp.2 h2
  have h4 : Real.exp (μ * S₂) * Bm' < ρ := (lt_div_iff₀ hBm'0).1 h3
  have hS₂1 : s₁ + 1 ≤ S₂ := by
    have := le_max_left (s₁ + 2) (Real.log (ρ / Bm') / μ + 1); linarith
  have hup : pdN μ b (S₂, t) < ρ := by
    have := pd_N_up h (p := (S₂, t)) (by simp only; linarith)
    have h5 : Real.exp (μ * S₂) * ((Vm + 1) / cZ) ≤ Real.exp (μ * S₂) * Bm' :=
      mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
    simp only at this
    linarith
  have hlo : ρ < pdN μ b (s₁ + 1, t) := by
    have := pd_N_low h (p := (s₁ + 1, t)) (by simp only; linarith)
    simp only at this
    linarith [hρ.2]
  have hcont : ContinuousOn (fun s => pdN μ b (s, t)) (Icc (s₁ + 1) S₂) :=
    (pd_N_cont h).comp (by fun_prop : Continuous fun s : ℝ => (s, t)).continuousOn
      (fun s hs => ⟨by simp only [mem_Ici]; linarith [hs.1], mem_univ _⟩)
  obtain ⟨σ, hσ, hσρ⟩ := intermediate_value_Icc' hS₂1 hcont ⟨hup.le, hlo.le⟩
  refine ⟨σ, lt_of_le_of_ne hσ.1 ?_, hσρ⟩
  rintro rfl
  simp only at hσρ
  linarith

end Core

open Classical in
/-- `σ (t, ρ)`: the solution `s > s₁ + 1` of `N (s, t) = ρ`. -/
def pdSigma (μ s₁ : ℝ) (b : ℝ × ℝ → CauchyRiemannIndex.Vec 1) (x : ℝ × ℝ) : ℝ :=
  if hx : ∃ σ, s₁ + 1 < σ ∧ pdN μ b (σ, x.1) = x.2 then hx.choose else 0

/-- `ψ (t, ρ) = τ (σ (t, ρ), t)`. -/
def pdPsi (μ s₁ : ℝ) (b : ℝ × ℝ → CauchyRiemannIndex.Vec 1) (τ : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : ℝ :=
  τ (pdSigma μ s₁ b x, x.1)

open Classical in
/-- `θ (τ₀, ρ)`: the solution `t` of `ψ (t, ρ) = τ₀`. -/
def pdTheta (μ s₁ : ℝ) (b : ℝ × ℝ → CauchyRiemannIndex.Vec 1) (τ : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : ℝ :=
  if hx : ∃ t, pdPsi μ s₁ b τ (t, x.2) = x.1 then hx.choose else 0

/-- The point `q (τ₀, ρ) = (σ (θ, ρ), θ)` of the end. -/
def pdQ (μ s₁ : ℝ) (b : ℝ × ℝ → CauchyRiemannIndex.Vec 1) (τ : ℝ × ℝ → ℝ) (x : ℝ × ℝ) :
    ℝ × ℝ :=
  (pdSigma μ s₁ b (pdTheta μ s₁ b τ x, x.2), pdTheta μ s₁ b τ x)

section Core2

variable {T μ c₀ s₁ η cZ LZ Lv Vm m A K : ℝ} {τ : ℝ × ℝ → ℝ} {r : ℝ × ℝ → V 1}
  {b : ℝ × ℝ → CauchyRiemannIndex.Vec 1} {Z : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1}
  {v : ℝ → V 1} {E : ℝ → CauchyRiemannIndex.Vec 1}
  (h : PDHyp T μ c₀ s₁ η cZ LZ Lv Vm m A K τ r b Z v E)
include h

theorem pd_sigma_spec {x : ℝ × ℝ} (hx : x.2 ∈ Ioo 0 (Real.exp (μ * (s₁ + 1)) * (m / 2))) :
    s₁ + 1 < pdSigma μ s₁ b x ∧ pdN μ b (pdSigma μ s₁ b x, x.1) = x.2 := by
  have hex := pd_sigma_exists h (t := x.1) hx
  rw [pdSigma, dif_pos hex]
  exact hex.choose_spec

theorem pd_sigma_cont :
    ContinuousOn (pdSigma μ s₁ b) (univ ×ˢ Ioo 0 (Real.exp (μ * (s₁ + 1)) * (m / 2))) := by
  refine pd_continuousOn_of_strictMonoOn (isOpen_Ioi (a := s₁)) (fun x s => -pdN μ b (s, x.1))
    (fun s hs => ?_) (fun x _ => ?_) (pdSigma μ s₁ b) (fun x => -x.2)
    (fun x hx => ?_) continuous_snd.neg.continuousOn (fun x hx => ?_)
  · exact ((pd_N_cont h).comp (by fun_prop : Continuous fun x : ℝ × ℝ => (s, x.1)).continuousOn
      (fun x _ => ⟨mem_Ici.2 (le_of_lt hs), mem_univ _⟩)).neg
  · intro a ha a' ha' haa'
    exact neg_lt_neg (pd_N_anti h (le_of_lt ha) haa')
  · exact mem_Ioi.2 (lt_trans (lt_add_one _) (pd_sigma_spec h hx.2).1)
  · simp only [(pd_sigma_spec h hx.2).2]

theorem pd_sigma_lip_aux {σ₁ σ₂ t₁ t₂ : ℝ} (hσ₁ : s₁ ≤ σ₁) (hlt : σ₁ < σ₂)
    (heq : pdN μ b (σ₁, t₁) = pdN μ b (σ₂, t₂)) : σ₂ - σ₁ ≤ K * |t₂ - t₁| := by
  have hσ₂ : s₁ ≤ σ₂ := hσ₁.trans hlt.le
  set d := σ₂ - σ₁ with hd
  have hd0 : 0 < d := sub_pos.2 hlt
  set Mb := (A * (1 + 1 / T) + 1) / cZ with hMb
  have hB := pd_b_low h (p := (σ₁, t₁)) hσ₁
  have h1 := pd_b_lip h (p := (σ₂, t₂)) (q := (σ₂, t₁)) hσ₂ hσ₂
  rw [pd_norm_t] at h1
  have h2 := pd_b_lip_s h (t := t₁) hσ₂ hσ₁
  rw [abs_of_pos hd0] at h2
  have hn1 := norm_sub_norm_le (b (σ₂, t₂)) (b (σ₂, t₁))
  have hn2 := norm_sub_norm_le (b (σ₂, t₁)) (b (σ₁, t₁))
  have hC : η * (A / T + 1) / cZ * d ≤ -μ * m / 4 * d :=
    mul_le_mul_of_nonneg_right h.hη2 hd0.le
  -- `‖b₁‖ = e^{μ d} ‖b₂‖`
  unfold pdN at heq
  simp only at heq
  have e1 : Real.exp (μ * σ₂) = Real.exp (μ * σ₁) * Real.exp (μ * d) := by
    rw [← Real.exp_add]; congr 1; rw [hd]; ring
  rw [e1, mul_assoc] at heq
  have heq' : ‖b (σ₁, t₁)‖ = Real.exp (μ * d) * ‖b (σ₂, t₂)‖ :=
    mul_left_cancel₀ (Real.exp_pos _).ne' heq
  have e2 : Real.exp (-μ * d) * Real.exp (μ * d) = 1 := by
    rw [← Real.exp_add, show -μ * d + μ * d = 0 by ring, Real.exp_zero]
  have h3 : Real.exp (-μ * d) * ‖b (σ₁, t₁)‖ = ‖b (σ₂, t₂)‖ := by
    rw [heq', ← mul_assoc, e2, one_mul]
  have hexp : (-μ * d + 1) * ‖b (σ₁, t₁)‖ ≤ Real.exp (-μ * d) * ‖b (σ₁, t₁)‖ :=
    mul_le_mul_of_nonneg_right (Real.add_one_le_exp _) (norm_nonneg _)
  have hμd : 0 < -μ * d := mul_pos (neg_pos.2 h.μ_neg) hd0
  have h4 : -μ * d * (m / 2) ≤ -μ * d * ‖b (σ₁, t₁)‖ := mul_le_mul_of_nonneg_left hB hμd.le
  -- `(-μ m / 4) d ≤ Mb |Δt|`
  have h5 : -μ * m / 4 * d ≤ Mb * |t₂ - t₁| := by nlinarith
  have hpos : 0 < -μ * m := mul_pos (neg_pos.2 h.μ_neg) h.m_pos
  rw [h.hK, ← hMb, div_mul_eq_mul_div, le_div_iff₀ hpos]
  nlinarith

theorem pd_sigma_lip {ρ : ℝ} (hρ : ρ ∈ Ioo 0 (Real.exp (μ * (s₁ + 1)) * (m / 2))) (t₁ t₂ : ℝ) :
    |pdSigma μ s₁ b (t₂, ρ) - pdSigma μ s₁ b (t₁, ρ)| ≤ K * |t₂ - t₁| := by
  obtain ⟨hs₁, hN₁⟩ := pd_sigma_spec h (x := (t₁, ρ)) hρ
  obtain ⟨hs₂, hN₂⟩ := pd_sigma_spec h (x := (t₂, ρ)) hρ
  have hK0 := pd_K_nn h
  rcases lt_trichotomy (pdSigma μ s₁ b (t₁, ρ)) (pdSigma μ s₁ b (t₂, ρ)) with hlt | heq | hgt
  · have := pd_sigma_lip_aux h (by linarith) hlt (hN₁.trans hN₂.symm)
    rw [abs_of_pos (sub_pos.2 hlt)]; exact this
  · rw [heq, sub_self, abs_zero]; positivity
  · have := pd_sigma_lip_aux h (by linarith) hgt (hN₂.trans hN₁.symm)
    rw [abs_sub_comm, abs_of_pos (sub_pos.2 hgt), abs_sub_comm]; exact this

theorem pd_psi_strictMono {ρ : ℝ} (hρ : ρ ∈ Ioo 0 (Real.exp (μ * (s₁ + 1)) * (m / 2))) :
    StrictMono (fun t => pdPsi μ s₁ b τ (t, ρ)) := by
  intro t₁ t₂ ht
  simp only [pdPsi]
  have hs₁ := (pd_sigma_spec h (x := (t₁, ρ)) hρ).1
  have hs₂ := (pd_sigma_spec h (x := (t₂, ρ)) hρ).1
  set p₁ : ℝ × ℝ := (pdSigma μ s₁ b (t₁, ρ), t₁) with hp₁
  set p₂ : ℝ × ℝ := (pdSigma μ s₁ b (t₂, ρ), t₂) with hp₂
  have hg := h.g_lip p₂ p₁ (by simp only [hp₂]; linarith) (by simp only [hp₁]; linarith)
  have hnorm := pd_norm_le (p₂ - p₁)
  have hsl := pd_sigma_lip h hρ t₁ t₂
  have hdt : |t₂ - t₁| = t₂ - t₁ := abs_of_pos (sub_pos.2 ht)
  rw [hdt] at hsl
  have h1 : |(p₂ - p₁).1| = |pdSigma μ s₁ b (t₂, ρ) - pdSigma μ s₁ b (t₁, ρ)| := rfl
  have h2 : |(p₂ - p₁).2| = t₂ - t₁ := hdt
  rw [h1, h2] at hnorm
  have h3 : ‖p₂ - p₁‖ ≤ (K + 1) * (t₂ - t₁) := by linarith
  have h4 : η * ‖p₂ - p₁‖ ≤ η * ((K + 1) * (t₂ - t₁)) :=
    mul_le_mul_of_nonneg_left h3 h.η_pos.le
  have h5 := (abs_le.1 hg).1
  have hη3 := h.hη3
  have hT := h.T_pos
  have hpt : p₂.2 = t₂ := rfl
  have hpt' : p₁.2 = t₁ := rfl
  rw [hpt, hpt'] at h5
  have h6 : η * ((K + 1) * (t₂ - t₁)) ≤ T / 2 * (t₂ - t₁) := by
    have := mul_le_mul_of_nonneg_right hη3 (sub_pos.2 ht).le
    linarith
  nlinarith

theorem pd_psi_bd {x : ℝ × ℝ} (hx : x.2 ∈ Ioo 0 (Real.exp (μ * (s₁ + 1)) * (m / 2))) :
    |pdPsi μ s₁ b τ x - T * x.1 - c₀| ≤ η := by
  have hs := (pd_sigma_spec h hx).1
  exact h.g_bd (pdSigma μ s₁ b x, x.1) (by simp only; linarith)

theorem pd_psi_cont :
    ContinuousOn (pdPsi μ s₁ b τ) (univ ×ˢ Ioo 0 (Real.exp (μ * (s₁ + 1)) * (m / 2))) := by
  unfold pdPsi
  refine h.τ_cont.comp ((pd_sigma_cont h).prodMk continuous_fst.continuousOn) ?_
  intro x hx
  exact ⟨mem_Ici.2 (by linarith [(pd_sigma_spec h hx.2).1]), mem_univ _⟩

theorem pd_theta_exists {x : ℝ × ℝ} (hx : x.2 ∈ Ioo 0 (Real.exp (μ * (s₁ + 1)) * (m / 2))) :
    ∃ t, pdPsi μ s₁ b τ (t, x.2) = x.1 := by
  have hT := h.T_pos
  have hη := h.η_le_one
  set a := (x.1 - c₀ - 2) / T
  set a' := (x.1 - c₀ + 2) / T
  have hab : a ≤ a' := by rw [div_le_div_iff_of_pos_right hT]; linarith
  have hlo : pdPsi μ s₁ b τ (a, x.2) ≤ x.1 := by
    have := abs_le.1 (pd_psi_bd h (x := (a, x.2)) hx)
    have e : T * a = x.1 - c₀ - 2 := by simp only [a]; field_simp
    simp only at this
    linarith [this.2]
  have hhi : x.1 ≤ pdPsi μ s₁ b τ (a', x.2) := by
    have := abs_le.1 (pd_psi_bd h (x := (a', x.2)) hx)
    have e : T * a' = x.1 - c₀ + 2 := by simp only [a']; field_simp
    simp only at this
    linarith [this.1]
  have hcont : ContinuousOn (fun t => pdPsi μ s₁ b τ (t, x.2)) (Icc a a') :=
    (pd_psi_cont h).comp (by fun_prop : Continuous fun t : ℝ => (t, x.2)).continuousOn
      (fun t _ => ⟨mem_univ _, hx⟩)
  obtain ⟨t, _, ht⟩ := intermediate_value_Icc hab hcont ⟨hlo, hhi⟩
  exact ⟨t, ht⟩

theorem pd_theta_spec {x : ℝ × ℝ} (hx : x.2 ∈ Ioo 0 (Real.exp (μ * (s₁ + 1)) * (m / 2))) :
    pdPsi μ s₁ b τ (pdTheta μ s₁ b τ x, x.2) = x.1 := by
  have hex := pd_theta_exists h hx
  rw [pdTheta, dif_pos hex]
  exact hex.choose_spec

theorem pd_theta_cont :
    ContinuousOn (pdTheta μ s₁ b τ) (univ ×ˢ Ioo 0 (Real.exp (μ * (s₁ + 1)) * (m / 2))) := by
  refine pd_continuousOn_of_strictMonoOn isOpen_univ (fun x t => pdPsi μ s₁ b τ (t, x.2))
    (fun t _ => ?_) (fun x hx => ?_) (pdTheta μ s₁ b τ) (fun x => x.1)
    (fun x _ => mem_univ _) continuous_fst.continuousOn (fun x hx => pd_theta_spec h hx.2)
  · exact (pd_psi_cont h).comp (by fun_prop : Continuous fun x : ℝ × ℝ => (t, x.2)).continuousOn
      (fun x hx => ⟨mem_univ _, hx.2⟩)
  · exact (pd_psi_strictMono h hx.2).strictMonoOn univ

theorem pd_Q_cont :
    ContinuousOn (pdQ μ s₁ b τ) (univ ×ˢ Ioo 0 (Real.exp (μ * (s₁ + 1)) * (m / 2))) := by
  unfold pdQ
  refine ContinuousOn.prodMk ?_ (pd_theta_cont h)
  exact (pd_sigma_cont h).comp ((pd_theta_cont h).prodMk continuous_snd.continuousOn)
    (fun x hx => ⟨mem_univ _, hx.2⟩)

theorem pd_Q_spec {x : ℝ × ℝ} (hx : x.2 ∈ Ioo 0 (Real.exp (μ * (s₁ + 1)) * (m / 2))) :
    s₁ + 1 < (pdQ μ s₁ b τ x).1 ∧ τ (pdQ μ s₁ b τ x) = x.1 ∧
      pdN μ b (pdQ μ s₁ b τ x) = x.2 := by
  have h1 := pd_sigma_spec h (x := (pdTheta μ s₁ b τ x, x.2)) hx
  have h2 := pd_theta_spec h hx
  exact ⟨h1.1, h2, h1.2⟩

theorem pd_Q_large {S' : ℝ} (hS' : s₁ ≤ S') {x : ℝ × ℝ}
    (hx : x.2 ∈ Ioo 0 (Real.exp (μ * (s₁ + 1)) * (m / 2)))
    (hsmall : x.2 < Real.exp (μ * S') * (m / 2)) : S' < (pdQ μ s₁ b τ x).1 := by
  obtain ⟨h1, _, h3⟩ := pd_Q_spec h hx
  by_contra hle
  push_neg at hle
  have hlow := pd_N_low h (p := (S', (pdQ μ s₁ b τ x).2)) hS'
  simp only at hlow
  have hge : pdN μ b (S', (pdQ μ s₁ b τ x).2) ≤ pdN μ b (pdQ μ s₁ b τ x) := by
    rcases hle.lt_or_eq with hlt | heq
    · exact (pd_N_anti h (by linarith) hlt).le
    · rw [← heq]
  linarith

end Core2

end

end FiniteEnergyPlane

/-!
# `exists_page_direction_of_hasAsymptoticEigenvector` (87bebfe8): assembly
-/


namespace FiniteEnergyPlane

noncomputable section

theorem pd_periodic_lower {f : ℝ → ℝ} (hf : Continuous f) (hper : Function.Periodic f 1)
    (hpos : ∀ t, 0 < f t) : ∃ m > 0, ∀ t, m ≤ f t := by
  obtain ⟨x, _, hmin⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_isMinOn
    (nonempty_Icc.2 zero_le_one) hf.continuousOn
  refine ⟨f x, hpos x, fun t => ?_⟩
  obtain ⟨y, hy, hyt⟩ := hper.exists_mem_Ico zero_lt_one t 0
  rw [hyt]
  exact isMinOn_iff.1 hmin y ⟨hy.1, by linarith [hy.2]⟩

theorem pd_main (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V 1 → V 1 →L[ℝ] V 1) (P : ReebOrbit H)
    (u : ℂ → V 1) (μ : ℝ) (v : ℝ → V 1) (hv : HasAsymptoticEigenvector H J u cylInf P 1 μ v)
    (Z : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1) (hZ : IsUnitaryXiFrame J P Z) :
    ∃ E : ℝ → CauchyRiemannIndex.Vec 1, Continuous E ∧ Function.Periodic E 1 ∧
      (∀ t : ℝ, E t ≠ 0) ∧ (∀ t : ℝ, v t = Z t (E t)) ∧
      ∃ ρ₀ > 0, ∃ dir : ℝ × ℝ → CauchyRiemannIndex.Vec 1,
        ContinuousOn dir (Set.univ ×ˢ Set.Ioo 0 ρ₀) ∧
        (∀ τ : ℝ, ∀ ρ ∈ Set.Ioo 0 ρ₀, ‖dir (τ, ρ)‖ = 1 ∧
          proj H (P.x τ + Z (τ / P.T) (ρ • dir (τ, ρ))) ∈ Set.range (fun z => proj H (u z))) ∧
        ∀ ε > 0, ∃ ρ₁ > 0, ∃ δ > 0, ∀ τ τ' : ℝ, |τ - τ'| < δ → ∀ ρ ∈ Set.Ioo 0 ρ₁,
          ‖dir (τ, ρ) - ‖E (τ' / P.T)‖⁻¹ • E (τ' / P.T)‖ < ε := by
  have heig := hv.1
  obtain ⟨_, hμ1, c₀, τ, r, s₀, hτ, hr, hrep⟩ := hv
  have hμ : μ < 0 := by simpa using hμ1
  obtain ⟨⟨hvs, hvper, hξ⟩, _, _⟩ := heig
  have hT := P.T_pos
  -- frame constants
  obtain ⟨cZ, hcZ, hZlow⟩ := pd_frame_lower hZ
  obtain ⟨LZ, hLZ, hZlip⟩ := pd_periodic_lip hZ.1 hZ.2.1
  obtain ⟨Lv, hLv, hvlip⟩ := pd_periodic_lip hvs hvper
  obtain ⟨Vm, hVm, hvbd⟩ := pd_periodic_bound hvs.continuous hvper
  have hZinj : ∀ t a a', Z t a = Z t a' → a = a' := by
    intro t a a' haa
    have h1 := hZlow t (a - a')
    rw [map_sub, haa, sub_self, norm_zero] at h1
    have h2 : ‖a - a'‖ ≤ 0 := by nlinarith [norm_nonneg (a - a')]
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h2)
  -- the eigenvector in the frame
  have hsurj : ∀ t, ∃ a, Z t a = v t := fun t => (hZ.2.2 t).2.1 (v t) (hξ t)
  choose E hE using hsurj
  have hEbd : ∀ t, ‖E t‖ ≤ Vm / cZ := by
    intro t
    rw [le_div_iff₀ hcZ]
    have := hZlow t (E t)
    rw [hE] at this
    linarith [hvbd t]
  set LE := (Lv + LZ * (Vm / cZ)) / cZ with hLE
  have hLE0 : 0 ≤ LE := by positivity
  have hElip : ∀ x y, ‖E x - E y‖ ≤ LE * |x - y| := by
    intro x y
    have h1 := hZlow x (E x - E y)
    have hk : Z x (E x - E y) = (v x - v y) + (Z y - Z x) (E y) := by
      rw [map_sub, hE, ContinuousLinearMap.sub_apply, hE]; abel
    rw [hk] at h1
    have h2 := norm_add_le (v x - v y) ((Z y - Z x) (E y))
    have h3 : ‖(Z y - Z x) (E y)‖ ≤ LZ * |x - y| * (Vm / cZ) := by
      refine ((Z y - Z x).le_opNorm _).trans ?_
      have h5 := hZlip y x
      rw [abs_sub_comm] at h5
      exact mul_le_mul h5 (hEbd y) (norm_nonneg _) (mul_nonneg hLZ (abs_nonneg _))
    have h4 := hvlip x y
    rw [hLE, div_mul_eq_mul_div, le_div_iff₀ hcZ]
    nlinarith
  have hEcont : Continuous E := by
    rw [Metric.continuous_iff]
    intro x ε hε
    refine ⟨ε / (LE + 1), by positivity, fun y hy => ?_⟩
    rw [dist_eq_norm]
    rw [Real.dist_eq] at hy
    calc ‖E y - E x‖ ≤ LE * |y - x| := hElip y x
      _ ≤ (LE + 1) * |y - x| := by nlinarith [abs_nonneg (y - x)]
      _ < (LE + 1) * (ε / (LE + 1)) := by gcongr
      _ = ε := by field_simp
  have hEper : Function.Periodic E 1 := by
    intro t
    apply hZinj t
    rw [hE t, ← hZ.2.1 t, hE (t + 1), hvper t]
  have hEne : ∀ t, E t ≠ 0 := by
    intro t h0
    have := hE t
    rw [h0, map_zero] at this
    exact pd_eigen_ne_zero hH hZ ‹IsAsymptoticEigen J P μ v› t this.symm
  obtain ⟨m, hm, hEm⟩ := pd_periodic_lower (continuous_norm.comp hEcont)
    (fun t => by simp only [Function.comp, hEper t]) (fun t => norm_pos_iff.2 (hEne t))
  -- constants
  set A := Lv + LZ * ((Vm + 1) / cZ) with hA
  have hA0 : 0 ≤ A := by positivity
  set K := 4 * ((A * (1 + 1 / P.T) + 1) / cZ) / (-μ * m) with hK
  have hμm : 0 < -μ * m := mul_pos (neg_pos.2 hμ) hm
  have hK0 : 0 ≤ K := by positivity
  set η := min (min 1 (cZ * m / 2)) (min (-μ * m / 4 * cZ / (A / P.T + 1)) (P.T / 2 / (1 + K)))
    with hη
  have hATp : 0 < A / P.T + 1 := by positivity
  have hη0 : 0 < η := by
    simp only [hη, lt_min_iff]
    refine ⟨⟨one_pos, by positivity⟩, by positivity, by positivity⟩
  have hη1 : η ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have hη2 : η ≤ cZ * m / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hη3 : η ≤ -μ * m / 4 * cZ / (A / P.T + 1) := (min_le_right _ _).trans (min_le_left _ _)
  have hη4 : η ≤ P.T / 2 / (1 + K) := (min_le_right _ _).trans (min_le_right _ _)
  have hη3' : η * (A / P.T + 1) / cZ ≤ -μ * m / 4 := by
    rw [div_le_iff₀ hcZ]
    have := (le_div_iff₀ hATp).1 hη3
    linarith
  have hη4' : η * (1 + K) ≤ P.T / 2 := (le_div_iff₀ (by positivity)).1 hη4
  -- decay bounds
  obtain ⟨Sg, hgbd, hglip, hgcont⟩ := pd_tendsto_lip hτ η hη0
  obtain ⟨Sr, hrbd, hrlip, hrcont⟩ := pd_tendsto_lip hr η hη0
  set s₁ := max (max Sg Sr) s₀ with hs₁
  have hSg : Sg ≤ s₁ := (le_max_left _ _).trans (le_max_left _ _)
  have hSr : Sr ≤ s₁ := (le_max_right _ _).trans (le_max_left _ _)
  have hs₀ : s₀ ≤ s₁ := le_max_right _ _
  -- the representation
  have hrep' : ∀ p : ℝ × ℝ, s₀ ≤ p.1 →
      IsInXi H (P.x (τ p)) (Real.exp (μ * p.1) • (v (τ p / P.T) + r p)) ∧
      endW H u cylInf p = proj H (P.x (τ p) + Real.exp (μ * p.1) • (v (τ p / P.T) + r p)) := by
    intro p hp
    have := hrep p.1 hp p.2
    simp only [one_mul] at this
    exact this
  have hTτ : ∀ x : ℝ, P.T * (x / P.T) = x := fun x => by field_simp
  have hex : ∀ p : ℝ × ℝ, s₀ ≤ p.1 →
      ∃ a, Z (τ p / P.T) a = Real.exp (μ * p.1) • (v (τ p / P.T) + r p) := by
    intro p hp
    refine (hZ.2.2 (τ p / P.T)).2.1 _ ?_
    rw [hTτ]
    exact (hrep' p hp).1
  classical
  set a : ℝ × ℝ → CauchyRiemannIndex.Vec 1 := fun p =>
    if hp : ∃ a, Z (τ p / P.T) a = Real.exp (μ * p.1) • (v (τ p / P.T) + r p) then hp.choose
    else 0 with ha
  have ha_spec : ∀ p : ℝ × ℝ, s₀ ≤ p.1 →
      Z (τ p / P.T) (a p) = Real.exp (μ * p.1) • (v (τ p / P.T) + r p) := by
    intro p hp
    simp only [ha, dif_pos (hex p hp)]
    exact (hex p hp).choose_spec
  set b : ℝ × ℝ → CauchyRiemannIndex.Vec 1 := fun p => Real.exp (-μ * p.1) • a p with hbdef
  have hb : ∀ p : ℝ × ℝ, s₁ ≤ p.1 → Z (τ p / P.T) (b p) = v (τ p / P.T) + r p := by
    intro p hp
    simp only [hbdef, map_smul, ha_spec p (hs₀.trans hp), smul_smul, ← Real.exp_add]
    rw [show -μ * p.1 + μ * p.1 = 0 by ring, Real.exp_zero, one_smul]
  have hτcont : ContinuousOn τ (Ici s₁ ×ˢ univ) := by
    have hfun : τ = fun p : ℝ × ℝ => (τ p - 1 * P.T * p.2 - c₀) + (1 * P.T * p.2 + c₀) := by
      funext p; ring
    rw [hfun]
    refine (hgcont.mono ?_).add (by fun_prop : Continuous fun p : ℝ × ℝ =>
      1 * P.T * p.2 + c₀).continuousOn
    exact prod_mono (Ici_subset_Ici.2 hSg) subset_rfl
  have hP : PDHyp P.T μ c₀ s₁ η cZ LZ Lv Vm m A K τ r b Z v E :=
    { T_pos := hT
      μ_neg := hμ
      η_pos := hη0
      η_le_one := hη1
      cZ_pos := hcZ
      LZ_nn := hLZ
      Lv_nn := hLv
      m_pos := hm
      Zlow := hZlow
      Zlip := hZlip
      vlip := hvlip
      vbd := hvbd
      hE := hE
      Elow := hEm
      g_bd := fun p hp => by
        have := hgbd p (hSg.trans hp)
        rwa [Real.norm_eq_abs, one_mul] at this
      g_lip := fun p q hp hq => by
        have := hglip p q (hSg.trans hp) (hSg.trans hq)
        rwa [Real.norm_eq_abs, one_mul] at this
      r_bd := fun p hp => hrbd p (hSr.trans hp)
      r_lip := fun p q hp hq => hrlip p q (hSr.trans hp) (hSr.trans hq)
      τ_cont := hτcont
      hb := hb
      hA := hA
      hK := hK
      hη1 := hη2
      hη2 := hη3'
      hη3 := hη4' }
  set ρ₀ := Real.exp (μ * (s₁ + 1)) * (m / 2) with hρ₀
  have hρ₀0 : 0 < ρ₀ := by positivity
  set q := pdQ μ s₁ b τ with hq
  have hqs : ∀ x : ℝ × ℝ, x.2 ∈ Ioo 0 ρ₀ → s₁ ≤ (q x).1 := fun x hx => by
    linarith [(pd_Q_spec hP hx).1]
  refine ⟨E, hEcont, hEper, hEne, fun t => (hE t).symm, ρ₀, hρ₀0,
    fun x => ‖b (q x)‖⁻¹ • b (q x), ?_, ?_, ?_⟩
  · -- continuity
    have hbq : ContinuousOn (fun x => b (q x)) (univ ×ˢ Ioo 0 ρ₀) :=
      (pd_b_cont hP).comp (pd_Q_cont hP) (fun x hx => ⟨mem_Ici.2 (hqs x hx.2), mem_univ _⟩)
    exact (hbq.norm.inv₀ (fun x hx => norm_ne_zero_iff.2 (pd_b_ne_zero hP (hqs x hx.2)))).smul hbq
  · -- unit length and membership in the image
    intro τ₀ ρ hρ
    obtain ⟨hq1, hq2, hq3⟩ := pd_Q_spec hP (x := (τ₀, ρ)) hρ
    set p := q (τ₀, ρ) with hp
    have hps : s₁ ≤ p.1 := by linarith
    have hbne := pd_b_ne_zero hP hps
    refine ⟨norm_smul_inv_norm (𝕜 := ℝ) hbne, ?_⟩
    have hbn : 0 < ‖b p‖ := norm_pos_iff.2 hbne
    unfold pdN at hq3
    simp only at hq2 hq3
    have hsm : ρ • (‖b p‖⁻¹ • b p) = a p := by
      rw [smul_smul, ← hq3, mul_assoc, mul_inv_cancel₀ hbn.ne', mul_one]
      simp only [hbdef, smul_smul, ← Real.exp_add]
      rw [show μ * p.1 + -μ * p.1 = 0 by ring, Real.exp_zero, one_smul]
    rw [hsm]
    rw [← hq2, ha_spec p (hs₀.trans hps), ← (hrep' p (hs₀.trans hps)).2]
    exact ⟨cylInf p.1 p.2, rfl⟩
  · -- uniform convergence to the eigen-direction
    intro ε hε
    obtain ⟨S₂, hS₂, -, -⟩ := pd_tendsto_lip hr (ε * cZ * m / 8) (by positivity)
    set S' := max s₁ S₂ with hS'
    set ρ₁ := min ρ₀ (Real.exp (μ * S') * (m / 2)) with hρ₁
    set δ := ε * m * P.T / (4 * (LE + 1)) with hδ
    refine ⟨ρ₁, by positivity, δ, by positivity, fun τ₀ τ' hττ ρ hρ => ?_⟩
    have hρ0 : ρ ∈ Ioo 0 ρ₀ := ⟨hρ.1, lt_of_lt_of_le hρ.2 (min_le_left _ _)⟩
    have hlarge := pd_Q_large hP (le_max_left s₁ S₂) (x := (τ₀, ρ)) hρ0
      (lt_of_lt_of_le hρ.2 (min_le_right _ _))
    obtain ⟨hq1, hq2, -⟩ := pd_Q_spec hP (x := (τ₀, ρ)) hρ0
    set p := q (τ₀, ρ) with hp
    simp only at hq2
    have hps : s₁ ≤ p.1 := by linarith
    have hrp : ‖r p‖ ≤ ε * cZ * m / 8 := hS₂ p (le_trans (le_max_right _ _) hlarge.le)
    have hbE := pd_b_sub_E hP hps
    rw [hq2] at hbE
    have hbE' : ‖b p - E (τ₀ / P.T)‖ ≤ ε * m / 8 := by
      have : cZ * ‖b p - E (τ₀ / P.T)‖ ≤ cZ * (ε * m / 8) := by linarith
      exact le_of_mul_le_mul_left this hcZ
    have hbne := pd_b_ne_zero hP hps
    have t1 := pd_normalize_sub_le (b p) (E (τ₀ / P.T)) hbne (hEne _)
    have t1' : 2 * ‖b p - E (τ₀ / P.T)‖ / ‖E (τ₀ / P.T)‖ ≤ ε / 4 := by
      calc 2 * ‖b p - E (τ₀ / P.T)‖ / ‖E (τ₀ / P.T)‖
          ≤ 2 * ‖b p - E (τ₀ / P.T)‖ / m :=
            div_le_div_of_nonneg_left (by positivity) hm (hEm _)
        _ ≤ 2 * (ε * m / 8) / m := by gcongr
        _ = ε / 4 := by field_simp; ring
    have t2 := pd_normalize_sub_le (E (τ₀ / P.T)) (E (τ' / P.T)) (hEne _) (hEne _)
    have hdiff : |τ₀ / P.T - τ' / P.T| ≤ δ / P.T := by
      rw [← sub_div, abs_div, abs_of_pos hT]
      exact div_le_div_of_nonneg_right hττ.le hT.le
    have t2' : 2 * ‖E (τ₀ / P.T) - E (τ' / P.T)‖ / ‖E (τ' / P.T)‖ ≤ ε / 2 := by
      calc 2 * ‖E (τ₀ / P.T) - E (τ' / P.T)‖ / ‖E (τ' / P.T)‖
          ≤ 2 * ‖E (τ₀ / P.T) - E (τ' / P.T)‖ / m :=
            div_le_div_of_nonneg_left (by positivity) hm (hEm _)
        _ ≤ 2 * (LE * (δ / P.T)) / m := by
            gcongr
            exact (hElip _ _).trans (mul_le_mul_of_nonneg_left hdiff hLE0)
        _ = ε / 2 * (LE / (LE + 1)) := by rw [hδ]; field_simp; ring
        _ ≤ ε / 2 := by
            have : LE / (LE + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
            nlinarith
    have tri := norm_sub_le_norm_sub_add_norm_sub (‖b p‖⁻¹ • b p)
      (‖E (τ₀ / P.T)‖⁻¹ • E (τ₀ / P.T)) (‖E (τ' / P.T)‖⁻¹ • E (τ' / P.T))
    show ‖‖b p‖⁻¹ • b p - ‖E (τ' / P.T)‖⁻¹ • E (τ' / P.T)‖ < ε
    linarith

end

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V 1 → V 1 →L[ℝ] V 1) (P : ReebOrbit H)
    (u : ℂ → V 1) (μ : ℝ) (v : ℝ → V 1) (hv : HasAsymptoticEigenvector H J u cylInf P 1 μ v)
    (Z : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1) (hZ : IsUnitaryXiFrame J P Z) :
    ∃ E : ℝ → CauchyRiemannIndex.Vec 1, Continuous E ∧ Function.Periodic E 1 ∧
      (∀ t : ℝ, E t ≠ 0) ∧ (∀ t : ℝ, v t = Z t (E t)) ∧
      ∃ ρ₀ > 0, ∃ dir : ℝ × ℝ → CauchyRiemannIndex.Vec 1,
        ContinuousOn dir (Set.univ ×ˢ Set.Ioo 0 ρ₀) ∧
        (∀ τ : ℝ, ∀ ρ ∈ Set.Ioo 0 ρ₀, ‖dir (τ, ρ)‖ = 1 ∧
          proj H (P.x τ + Z (τ / P.T) (ρ • dir (τ, ρ))) ∈ Set.range (fun z => proj H (u z))) ∧
        ∀ ε > 0, ∃ ρ₁ > 0, ∃ δ > 0, ∀ τ τ' : ℝ, |τ - τ'| < δ → ∀ ρ ∈ Set.Ioo 0 ρ₁,
          ‖dir (τ, ρ) - ‖E (τ' / P.T)‖⁻¹ • E (τ' / P.T)‖ < ε :=
  pd_main H hH J P u μ v hv Z hZ
