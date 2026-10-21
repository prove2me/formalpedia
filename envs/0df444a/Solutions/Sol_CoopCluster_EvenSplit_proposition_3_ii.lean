-- Prove2me | solution 1 for CoopCluster.EvenSplit.proposition_3_ii
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T21:49:14.148348+00:00
-- url     : https://prove2.me/submissions/d62ae371-c8d9-41e5-8f2b-5a0f3947d605

import Mathlib
import Definitions.Def_CoopCluster_EvenSplit_Model

open CoopCluster.EvenSplit

namespace Coop7iiSol

noncomputable def Pf (M : Params) (a : ℝ) : ℝ :=
  M.c * a * Real.exp (M.δ * a) / (2 * M.δ * (M.h * M.w))

noncomputable def PiO (M : Params) (a : ℝ) : ℝ :=
  Pf M a * (D M a - M.b0 * Pf M a) - M.c * a ^ 2 / 4 - M.γ / M.w

lemma D_pos {M : Params} (hS : M.Standing) {a : ℝ} (ha : 0 ≤ a) : 0 < D M a := by
  obtain ⟨hB, hb0, hh, hw, hδ, hc, hγ, -, hcap⟩ := hS
  have he : Real.exp (-(M.δ * a)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have hK : 0 < M.h * M.w := mul_pos hh hw
  unfold D A
  nlinarith

lemma jointProfit_t0 (M : Params) (θ a P1 P2 : ℝ) :
    jointProfit M θ 0 a P1 P2 = (P1 + P2) * D M a - M.c * a ^ 2 / 2
      - (M.b0 + θ) * (P1 ^ 2 + P2 ^ 2) + 2 * θ * P1 * P2 - 2 * (M.γ / M.w) := by
  unfold jointProfit firmProfit arrival costShare entCost; ring

lemma firmProfit_t0 (M : Params) (θ a P1 P2 : ℝ) :
    firmProfit M θ 0 a P1 P2 = P1 * (D M a - (M.b0 + θ) * P1 + θ * P2)
      - M.c * a ^ 2 / 4 - M.γ / M.w := by
  unfold firmProfit arrival costShare entCost; ring

lemma jointOpt_red {M : Params} {θ P1 P2 α : ℝ} (h : IsJointOpt M θ 0 P1 P2 α) :
    0 ≤ α ∧ ∀ a', 0 ≤ a' → (P1 + P2) * D M a' - M.c * a' ^ 2 / 2 ≤
      (P1 + P2) * D M α - M.c * α ^ 2 / 2 := by
  refine ⟨h.1, fun a' ha' => ?_⟩
  have := h.2 a' ha'
  rw [jointProfit_t0, jointProfit_t0] at this
  linarith

lemma opt_mono {M : Params} {S1 S2 a1 a2 : ℝ} (hlt : S1 < S2)
    (h1 : ∀ a', 0 ≤ a' → S1 * D M a' - M.c * a' ^ 2 / 2 ≤ S1 * D M a1 - M.c * a1 ^ 2 / 2)
    (h2 : ∀ a', 0 ≤ a' → S2 * D M a' - M.c * a' ^ 2 / 2 ≤ S2 * D M a2 - M.c * a2 ^ 2 / 2)
    (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) : D M a1 ≤ D M a2 := by
  have e1 := h1 a2 ha2
  have e2 := h2 a1 ha1
  have : 0 ≤ (S2 - S1) * (D M a2 - D M a1) := by nlinarith
  by_contra hc
  push Not at hc
  have : (S2 - S1) * (D M a2 - D M a1) < 0 := mul_neg_of_pos_of_neg (by linarith) (by linarith)
  linarith

lemma D_cont (M : Params) : Continuous (D M) := by
  unfold D; fun_prop

lemma Pf_cont (M : Params) : Continuous (Pf M) := by
  unfold Pf; fun_prop

lemma exists_opt {M : Params} (hS : M.Standing) (θ P1 P2 : ℝ) (hsum : 0 ≤ P1 + P2) :
    ∃ a, IsJointOpt M θ 0 P1 P2 a := by
  obtain ⟨hB, hb0, hh, hw, hδ, hc, hγ, -, hcap⟩ := hS
  set S := P1 + P2 with hSdef
  set K := M.h * M.w with hKdef
  have hK : 0 < K := mul_pos hh hw
  set R : ℝ := 1 + 2 * S * K / M.c with hR
  have hR1 : 1 ≤ R := by
    have : 0 ≤ 2 * S * K / M.c := by positivity
    linarith
  have hcR : M.c * R = M.c + 2 * S * K := by
    rw [hR]; field_simp
  let f : ℝ → ℝ := fun a => S * D M a - M.c * a ^ 2 / 2
  have hf : Continuous f := by
    have := D_cont M
    fun_prop
  obtain ⟨a, haI, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.2 (by linarith : (0:ℝ) ≤ R)) hf.continuousOn
  have hmax' : ∀ a', 0 ≤ a' → f a' ≤ f a := by
    intro a' ha'
    by_cases hle : a' ≤ R
    · exact hmax ⟨ha', hle⟩
    · push Not at hle
      have h0 : f 0 ≤ f a := hmax ⟨le_refl 0, by linarith⟩
      have he : 0 < Real.exp (-(M.δ * a')) := Real.exp_pos _
      have hf0 : f 0 = S * (A M - K) := by
        simp only [f, D]; simp [hKdef]
      have hfa' : f a' = S * (A M - K * Real.exp (-(M.δ * a'))) - M.c * a' ^ 2 / 2 := by
        simp only [f, D, hKdef]
      have h1 : S * K ≤ M.c * a' ^ 2 / 2 := by
        have h3 : M.c * R ≤ M.c * a' := by nlinarith
        have h4 : a' ≤ a' ^ 2 := by nlinarith
        have h5 : M.c * a' ≤ M.c * a' ^ 2 := mul_le_mul_of_nonneg_left h4 hc.le
        nlinarith
      have h2 : 0 ≤ S * (K * Real.exp (-(M.δ * a'))) := by positivity
      have : f a' ≤ f 0 := by rw [hfa', hf0]; nlinarith
      linarith
  refine ⟨a, haI.1, fun a' ha' => ?_⟩
  have := hmax' a' ha'
  simp only [f] at this
  rw [jointProfit_t0, jointProfit_t0]
  linarith


lemma hasDerivAt_D (M : Params) (a : ℝ) :
    HasDerivAt (D M) (M.h * M.w * (Real.exp (-(M.δ * a)) * M.δ)) a := by
  have h1 : HasDerivAt (fun x => Real.exp (-(M.δ * x))) (Real.exp (-(M.δ * a)) * (-(M.δ * 1))) a :=
    (((hasDerivAt_id a).const_mul M.δ).neg).exp
  have h2 := (h1.const_mul (M.h * M.w)).const_sub (A M)
  show HasDerivAt (fun x => A M - M.h * M.w * Real.exp (-(M.δ * x))) _ a
  exact h2.congr_deriv (by ring)

lemma foc_alpha {M : Params} (hS : M.Standing) {S α : ℝ} (hSpos : 0 < S) (hα : 0 ≤ α)
    (hmax : ∀ a', 0 ≤ a' → S * D M a' - M.c * a' ^ 2 / 2 ≤ S * D M α - M.c * α ^ 2 / 2) :
    0 < α ∧ M.c * α * Real.exp (M.δ * α) = S * (M.h * M.w * M.δ) := by
  obtain ⟨hB, hb0, hh, hw, hδ, hc, hγ, -, hcap⟩ := hS
  let f : ℝ → ℝ := fun a => S * D M a - M.c * a ^ 2 / 2
  have hd : HasDerivAt f (S * (M.h * M.w * (Real.exp (-(M.δ * α)) * M.δ)) - M.c * α) α := by
    have h1 := (hasDerivAt_D M α).const_mul S
    have h2 := ((hasDerivAt_pow 2 α).const_mul M.c).div_const 2
    exact (h1.sub h2).congr_deriv (by push_cast; ring)
  have hloc : IsLocalMaxOn f (Set.Ici 0) α :=
    Filter.eventually_of_mem self_mem_nhdsWithin (fun a' ha' => hmax a' ha')
  have hnp : S * (M.h * M.w * (Real.exp (-(M.δ * α)) * M.δ)) - M.c * α ≤ 0 := by
    have hy : (1:ℝ) ∈ posTangentConeAt (Set.Ici (0:ℝ)) α := by
      apply mem_posTangentConeAt_of_segment_subset
      rw [segment_eq_Icc (by linarith)]
      intro x hx; exact le_trans hα hx.1
    have := hloc.hasFDerivWithinAt_nonpos hd.hasFDerivAt.hasFDerivWithinAt hy
    simpa using this
  have hK : 0 < M.h * M.w := mul_pos hh hw
  have hαpos : 0 < α := by
    rcases hα.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h] at hnp
      simp at hnp
      have : 0 < S * (M.h * M.w * M.δ) := by positivity
      linarith
  refine ⟨hαpos, ?_⟩
  have hlm : IsLocalMax f α :=
    Filter.eventually_of_mem (Ici_mem_nhds hαpos) (fun a' ha' => hmax a' ha')
  have h0 := hlm.hasDerivAt_eq_zero hd
  have hee : Real.exp (-(M.δ * α)) * Real.exp (M.δ * α) = 1 := by
    rw [← Real.exp_add]; simp
  have : S * (M.h * M.w * M.δ) * (Real.exp (-(M.δ * α)) * Real.exp (M.δ * α))
      = M.c * α * Real.exp (M.δ * α) := by
    linear_combination Real.exp (M.δ * α) * h0
  rw [hee] at this
  linarith

lemma eq_foc {M : Params} (hS : M.Standing) {θ P α : ℝ} (hθ : 0 ≤ θ)
    (heq : IsSymEq M θ 0 P α) :
    0 < P ∧ D M α = (2 * M.b0 + θ) * P := by
  obtain ⟨hP, hopt, hdev⟩ := heq
  obtain ⟨hα, hαopt⟩ := jointOpt_red hopt
  have hb0 : 0 < M.b0 := hS.2.1
  have hβ : 0 < M.b0 + θ := by linarith
  have key : ∀ P', 0 ≤ P' → ∀ α', IsJointOpt M θ 0 P' P α' →
      (P' - P) * ((D M α + D M α') / 2 - (M.b0 + θ) * (P' + P) + θ * P) ≤ 0 := by
    intro P' hP' α' hopt'
    have h1 := hdev P' α' hP' hopt'
    have h2 := hopt'.2 α hα
    rw [firmProfit_t0, firmProfit_t0] at h1
    rw [jointProfit_t0, jointProfit_t0] at h2
    nlinarith
  -- upper bound
  have hup : D M α ≤ (2 * M.b0 + θ) * P := by
    by_contra hcon
    push Not at hcon
    set η := (D M α - (2 * M.b0 + θ) * P) / (2 * (M.b0 + θ)) with hη
    have hηpos : 0 < η := by rw [hη]; apply div_pos <;> linarith
    have hηeq : 2 * (M.b0 + θ) * η = D M α - (2 * M.b0 + θ) * P := by
      rw [hη]; field_simp
    obtain ⟨α', hα'⟩ := exists_opt hS θ (P + η) P (by linarith)
    have hk := key (P + η) (by linarith) α' hα'
    obtain ⟨hα'0, hα'opt⟩ := jointOpt_red hα'
    have hmono : D M α ≤ D M α' :=
      opt_mono (S1 := P + P) (S2 := P + η + P) (by linarith) hαopt hα'opt hα hα'0
    have hX : (D M α + D M α') / 2 - (M.b0 + θ) * (P + η + P) + θ * P ≤ 0 := by
      by_contra hx; push Not at hx
      have : 0 < (P + η - P) * ((D M α + D M α') / 2 - (M.b0 + θ) * (P + η + P) + θ * P) :=
        mul_pos (by linarith) hx
      linarith
    nlinarith
  have hPpos : 0 < P := by
    rcases hP.lt_or_eq with h | h
    · exact h
    · exfalso
      have := D_pos hS hα
      rw [← h] at hup
      linarith
  refine ⟨hPpos, le_antisymm hup ?_⟩
  by_contra hcon
  push Not at hcon
  set η := min P (((2 * M.b0 + θ) * P - D M α) / (2 * (M.b0 + θ))) with hη
  have hηpos : 0 < η := by
    rw [hη]; apply lt_min hPpos; apply div_pos <;> linarith
  have hηle : η ≤ P := min_le_left _ _
  have hηle2 : 2 * (M.b0 + θ) * η ≤ (2 * M.b0 + θ) * P - D M α := by
    have : η ≤ ((2 * M.b0 + θ) * P - D M α) / (2 * (M.b0 + θ)) := min_le_right _ _
    rw [le_div_iff₀ (by linarith)] at this
    linarith
  obtain ⟨α', hα'⟩ := exists_opt hS θ (P - η) P (by linarith)
  have hk := key (P - η) (by linarith) α' hα'
  obtain ⟨hα'0, hα'opt⟩ := jointOpt_red hα'
  have hmono : D M α' ≤ D M α :=
    opt_mono (S1 := P - η + P) (S2 := P + P) (by linarith) hα'opt hαopt hα'0 hα
  have hX : 0 ≤ (D M α + D M α') / 2 - (M.b0 + θ) * (P - η + P) + θ * P := by
    by_contra hx; push Not at hx
    have : 0 < (P - η - P) * ((D M α + D M α') / 2 - (M.b0 + θ) * (P - η + P) + θ * P) :=
      mul_pos_of_neg_of_neg (by linarith) hx
    linarith
  nlinarith


lemma Pf_pos {M : Params} (hS : M.Standing) {a : ℝ} (ha : 0 < a) : 0 < Pf M a := by
  obtain ⟨hB, hb0, hh, hw, hδ, hc, hγ, -, hcap⟩ := hS
  unfold Pf; positivity

lemma Pf_zero (M : Params) : Pf M 0 = 0 := by simp [Pf]

lemma D_zero (M : Params) : D M 0 = A M - M.h * M.w := by simp [D]

lemma Pf_mul {M : Params} (hS : M.Standing) (a : ℝ) :
    Pf M a * (2 * M.δ * (M.h * M.w)) = M.c * a * Real.exp (M.δ * a) := by
  obtain ⟨hB, hb0, hh, hw, hδ, hc, hγ, -, hcap⟩ := hS
  unfold Pf; field_simp

lemma cross_anti {M : Params} (hS : M.Standing) {a1 a2 : ℝ} (h1 : 0 < a1) (h12 : a1 < a2) :
    D M a2 * Pf M a1 < D M a1 * Pf M a2 := by
  have hS' := hS
  obtain ⟨hB, hb0, hh, hw, hδ, hc, hγ, -, hcap⟩ := hS
  have h2 : 0 < a2 := by linarith
  have hK : 0 < M.h * M.w := mul_pos hh hw
  have hconv : Real.exp (-(M.δ * a1)) * a2 ≤ (a2 - a1) + a1 * Real.exp (-(M.δ * a2)) := by
    have ht0 : 0 ≤ a1 / a2 := by positivity
    have ht1 : 0 ≤ 1 - a1 / a2 := by
      rw [sub_nonneg, div_le_one h2]; linarith
    have := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ (-(M.δ * a2))) ht1 ht0
      (by ring)
    simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at this
    have harg : a1 / a2 * -(M.δ * a2) = -(M.δ * a1) := by field_simp
    rw [harg] at this
    have := mul_le_mul_of_nonneg_right this h2.le
    have e : (1 - a1 / a2 + a1 / a2 * Real.exp (-(M.δ * a2))) * a2
        = (a2 - a1) + a1 * Real.exp (-(M.δ * a2)) := by field_simp
    linarith
  have hlin : D M a2 * a1 < D M a1 * a2 := by
    unfold D A
    have := mul_le_mul_of_nonneg_left hconv hK.le
    nlinarith
  have hD1 : 0 < D M a1 := D_pos hS' h1.le
  have he : Real.exp (M.δ * a1) < Real.exp (M.δ * a2) :=
    Real.exp_lt_exp.2 (by nlinarith)
  have he1 : 0 < Real.exp (M.δ * a1) := Real.exp_pos _
  have hq : 0 < M.c / (2 * M.δ * (M.h * M.w)) := by positivity
  have key : D M a2 * (a1 * Real.exp (M.δ * a1)) < D M a1 * (a2 * Real.exp (M.δ * a2)) := by
    have i1 : D M a2 * a1 * Real.exp (M.δ * a1) < D M a1 * a2 * Real.exp (M.δ * a1) :=
      mul_lt_mul_of_pos_right hlin he1
    have i2 : D M a1 * a2 * Real.exp (M.δ * a1) < D M a1 * a2 * Real.exp (M.δ * a2) :=
      mul_lt_mul_of_pos_left he (by positivity)
    nlinarith
  have e1 : D M a2 * Pf M a1 = M.c / (2 * M.δ * (M.h * M.w)) *
      (D M a2 * (a1 * Real.exp (M.δ * a1))) := by unfold Pf; ring
  have e2 : D M a1 * Pf M a2 = M.c / (2 * M.δ * (M.h * M.w)) *
      (D M a1 * (a2 * Real.exp (M.δ * a2))) := by unfold Pf; ring
  rw [e1, e2]
  exact mul_lt_mul_of_pos_left key hq

noncomputable def Pfd (M : Params) (a : ℝ) : ℝ :=
  M.c * (Real.exp (M.δ * a) + a * (Real.exp (M.δ * a) * M.δ)) / (2 * M.δ * (M.h * M.w))

lemma hasDerivAt_Pf (M : Params) (a : ℝ) : HasDerivAt (Pf M) (Pfd M a) a := by
  have h1 : HasDerivAt (fun x => Real.exp (M.δ * x)) (Real.exp (M.δ * a) * (M.δ * 1)) a :=
    ((hasDerivAt_id a).const_mul M.δ).exp
  have h2 := (((hasDerivAt_id a).const_mul M.c).mul h1).div_const (2 * M.δ * (M.h * M.w))
  show HasDerivAt (fun x => M.c * x * Real.exp (M.δ * x) / (2 * M.δ * (M.h * M.w))) _ a
  exact h2.congr_deriv (by unfold Pfd; simp; ring)

lemma Pfd_pos {M : Params} (hS : M.Standing) {a : ℝ} (ha : 0 ≤ a) : 0 < Pfd M a := by
  obtain ⟨hB, hb0, hh, hw, hδ, hc, hγ, -, hcap⟩ := hS
  unfold Pfd; positivity

lemma hasDerivAt_PiO {M : Params} (hS : M.Standing) (a : ℝ) :
    HasDerivAt (PiO M) (Pfd M a * (D M a - 2 * M.b0 * Pf M a)) a := by
  obtain ⟨hB, hb0, hh, hw, hδ, hc, hγ, -, hcap⟩ := hS
  have hP := hasDerivAt_Pf M a
  have hD := hasDerivAt_D M a
  have h := ((hP.mul (hD.sub (hP.const_mul M.b0))).sub
    (((hasDerivAt_pow 2 a).const_mul M.c).div_const 4)).sub_const (M.γ / M.w)
  have key : Pf M a * (M.h * M.w * (Real.exp (-(M.δ * a)) * M.δ)) = M.c * a / 2 := by
    unfold Pf; rw [Real.exp_neg]; field_simp
  show HasDerivAt (fun x => Pf M x * (D M x - M.b0 * Pf M x) - M.c * x ^ 2 / 4 - M.γ / M.w) _ a
  refine h.congr_deriv ?_
  simp only [Pi.sub_apply, Pi.mul_apply]
  push_cast
  linear_combination key

lemma PiO_cont {M : Params} (hS : M.Standing) : Continuous (PiO M) :=
  continuous_iff_continuousAt.2 fun a => (hasDerivAt_PiO hS a).continuousAt

lemma PiO_zero (M : Params) : PiO M 0 = -(M.γ / M.w) := by
  simp [PiO, Pf_zero]

lemma exists_alpha0 {M : Params} (hS : M.Standing) :
    ∃ α0, 0 < α0 ∧ D M α0 = 2 * M.b0 * Pf M α0 := by
  have hS' := hS
  obtain ⟨hB, hb0, hh, hw, hδ, hc, hγ, -, hcap⟩ := hS
  set K := M.h * M.w with hK
  have hKp : 0 < K := mul_pos hh hw
  have hAK : 0 < A M - K := by unfold A; linarith
  let F : ℝ → ℝ := fun a => D M a - 2 * M.b0 * Pf M a
  have hF : Continuous F := by
    have := D_cont M; have := Pf_cont M; fun_prop
  set R : ℝ := M.δ * K * A M / (M.b0 * M.c) + 1 with hR
  have hA : 0 < A M := by linarith
  have hR0 : 0 < R := by rw [hR]; positivity
  have hbR : M.b0 * M.c * R = M.δ * K * A M + M.b0 * M.c := by
    rw [hR]; field_simp
  have hF0 : 0 < F 0 := by simp only [F, D_zero, Pf_zero]; linarith
  have hFR : F R < 0 := by
    have hDR : D M R ≤ A M := by
      unfold D; have := Real.exp_pos (-(M.δ * R)); nlinarith
    have hq := Pf_mul hS' R
    have he : 1 ≤ Real.exp (M.δ * R) := Real.one_le_exp (by positivity)
    have h1 : M.c * R ≤ M.c * R * Real.exp (M.δ * R) := by
      have : 0 ≤ M.c * R := by positivity
      nlinarith
    have h2 : A M < 2 * M.b0 * Pf M R := by
      have hq2 : 0 < 2 * M.δ * K := by positivity
      by_contra hcon; push Not at hcon
      have : 2 * M.b0 * Pf M R * (2 * M.δ * K) ≤ A M * (2 * M.δ * K) :=
        mul_le_mul_of_nonneg_right hcon hq2.le
      nlinarith
    simp only [F]; linarith
  have := intermediate_value_Icc' hR0.le hF.continuousOn ⟨hFR.le, hF0.le⟩
  obtain ⟨a, haI, hFa⟩ := this
  have ha0 : a ≠ 0 := by rintro rfl; linarith
  refine ⟨a, lt_of_le_of_ne haI.1 (Ne.symm ha0), ?_⟩
  simp only [F] at hFa; linarith

lemma Pf_surj {M : Params} (hS : M.Standing) {Q : ℝ} (hQ : 0 ≤ Q) :
    ∃ a, 0 ≤ a ∧ Pf M a = Q := by
  have hS' := hS
  obtain ⟨hB, hb0, hh, hw, hδ, hc, hγ, -, hcap⟩ := hS
  set R : ℝ := 2 * M.δ * (M.h * M.w) * Q / M.c with hR
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  have hPR : Pf M R = Q * Real.exp (M.δ * R) := by
    unfold Pf; rw [hR]; field_simp
  have he : 1 ≤ Real.exp (M.δ * R) := Real.one_le_exp (by positivity)
  have hQR : Q ≤ Pf M R := by rw [hPR]; nlinarith
  obtain ⟨a, haI, hPa⟩ := intermediate_value_Icc hR0 (Pf_cont M).continuousOn
    ⟨by rw [Pf_zero]; exact hQ, hQR⟩
  exact ⟨a, haI.1, hPa⟩

lemma PiO_strictMono {M : Params} (hS : M.Standing) {α0 : ℝ} (hα0 : 0 < α0)
    (hα0eq : D M α0 = 2 * M.b0 * Pf M α0) : StrictMonoOn (PiO M) (Set.Icc 0 α0) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 α0) (PiO_cont hS).continuousOn
  intro x hx
  rw [interior_Icc] at hx
  rw [(hasDerivAt_PiO hS x).deriv]
  have h1 := Pfd_pos hS hx.1.le
  have hc := cross_anti hS hx.1 hx.2
  have hp0 := Pf_pos hS hα0
  have hpx := Pf_pos hS hx.1
  have : 2 * M.b0 * Pf M x < D M x := by
    rw [hα0eq] at hc
    by_contra hcon; push Not at hcon
    have := mul_le_mul_of_nonneg_right hcon hp0.le
    nlinarith
  exact mul_pos h1 (by linarith)

lemma PiO_anti {M : Params} (hS : M.Standing) {α0 : ℝ} (hα0 : 0 < α0)
    (hα0eq : D M α0 = 2 * M.b0 * Pf M α0) : AntitoneOn (PiO M) (Set.Ici α0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici α0) (PiO_cont hS).continuousOn
    (fun x _ => (hasDerivAt_PiO hS x).differentiableAt.differentiableWithinAt)
  intro x hx
  rw [interior_Ici] at hx
  rw [(hasDerivAt_PiO hS x).deriv]
  have hx0 : 0 < x := lt_trans hα0 hx
  have h1 := Pfd_pos hS hx0.le
  have hc := cross_anti hS hα0 hx
  have hp0 := Pf_pos hS hα0
  have hpx := Pf_pos hS hx0
  have : D M x < 2 * M.b0 * Pf M x := by
    rw [hα0eq] at hc
    by_contra hcon; push Not at hcon
    have := mul_le_mul_of_nonneg_right hcon hp0.le
    nlinarith
  exact mul_nonpos_of_nonneg_of_nonpos h1.le (by linarith)

lemma monoProfit_eq (M : Params) (p a : ℝ) :
    monoProfit M p a = (p - M.γ) * (D M a - M.b0 * (p - M.γ)) - M.c * a ^ 2 / 2 - M.γ / M.w := by
  unfold monoProfit monoArrival serviceRate entCost D A; ring

lemma mono_bound {M : Params} (hS : M.Standing) {α0 : ℝ} (hα0 : 0 < α0)
    (hα0eq : D M α0 = 2 * M.b0 * Pf M α0) : ∀ π ∈ monoProfits M, π ≤ PiO M α0 := by
  have hS' := hS
  obtain ⟨hB, hb0, hh, hw, hδ, hc, hγ, -, hcap⟩ := hS
  rintro π ⟨p, a, hp, ha, rfl⟩
  rw [monoProfit_eq]
  set Q := p - M.γ with hQ
  have hQ0 : 0 ≤ Q := by rw [hQ]; linarith
  obtain ⟨b, hb, hPb⟩ := Pf_surj hS' hQ0
  have hK : 0 < M.h * M.w := mul_pos hh hw
  -- tangent inequality
  have hq : Q * (M.h * M.w) * M.δ * Real.exp (-(M.δ * b)) = M.c * b / 2 := by
    rw [← hPb]; unfold Pf; rw [Real.exp_neg]; field_simp
  have hv : Real.exp (-(M.δ * b)) * (1 - M.δ * (a - b)) ≤ Real.exp (-(M.δ * a)) := by
    have h1 := Real.add_one_le_exp (-(M.δ * (a - b)))
    have h2 : Real.exp (-(M.δ * a)) = Real.exp (-(M.δ * b)) * Real.exp (-(M.δ * (a - b))) := by
      rw [← Real.exp_add]; ring_nf
    rw [h2]
    have := Real.exp_pos (-(M.δ * b))
    nlinarith
  have hQK : 0 ≤ Q * (M.h * M.w) := by positivity
  have htan : Q * D M a - M.c * a ^ 2 / 4 ≤ Q * D M b - M.c * b ^ 2 / 4 := by
    unfold D
    have i1 := mul_le_mul_of_nonneg_left hv hQK
    have i2 := mul_nonneg hc.le (sq_nonneg (a - b))
    nlinarith
  have hb' : PiO M b ≤ PiO M α0 := by
    rcases le_total b α0 with h | h
    · exact (PiO_strictMono hS' hα0 hα0eq).monotoneOn ⟨hb, h⟩ ⟨hα0.le, le_refl _⟩ h
    · exact PiO_anti hS' hα0 hα0eq (le_refl α0) h h
  have hPiOb : PiO M b = Q * D M b - M.b0 * Q ^ 2 - M.c * b ^ 2 / 4 - M.γ / M.w := by
    unfold PiO; rw [hPb]; ring
  have : 0 ≤ M.c * a ^ 2 := by positivity
  nlinarith


lemma eq_char {M : Params} (hS : M.Standing) {θ P α : ℝ} (hθ : 0 ≤ θ)
    (heq : IsSymEq M θ 0 P α) :
    0 < α ∧ P = Pf M α ∧ D M α = (2 * M.b0 + θ) * Pf M α ∧
      firmProfit M θ 0 α P P = PiO M α := by
  have hS' := hS
  obtain ⟨hB, hb0, hh, hw, hδ, hc, hγ, -, hcap⟩ := hS
  obtain ⟨hP, hDeq⟩ := eq_foc hS' hθ heq
  obtain ⟨hα, hαopt⟩ := jointOpt_red heq.2.1
  obtain ⟨hαpos, hfoc⟩ := foc_alpha hS' (S := P + P) (by linarith) hα hαopt
  have hPα : P = Pf M α := by
    have := Pf_mul hS' α
    have hq : 0 < 2 * M.δ * (M.h * M.w) := by positivity
    have : (P - Pf M α) * (2 * M.δ * (M.h * M.w)) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  refine ⟨hαpos, hPα, by rw [← hPα]; exact hDeq, ?_⟩
  rw [firmProfit_t0]; unfold PiO; rw [← hPα]; ring

lemma ratio_lt {M : Params} (hS : M.Standing) {a1 a2 θ1 θ2 : ℝ} (h1 : 0 < a1) (h12 : a1 < a2)
    (e1 : D M a1 = (2 * M.b0 + θ1) * Pf M a1) (e2 : D M a2 = (2 * M.b0 + θ2) * Pf M a2) :
    θ2 < θ1 := by
  have hx := cross_anti hS h1 h12
  rw [e1, e2] at hx
  have := mul_pos (Pf_pos hS h1) (Pf_pos hS (lt_trans h1 h12))
  nlinarith

lemma Pf_strictMono {M : Params} (hS : M.Standing) {a1 a2 : ℝ} (h1 : 0 ≤ a1) (h12 : a1 < a2) :
    Pf M a1 < Pf M a2 := by
  obtain ⟨hB, hb0, hh, hw, hδ, hc, hγ, -, hcap⟩ := hS
  unfold Pf
  apply div_lt_div_of_pos_right _ (by positivity)
  have he : Real.exp (M.δ * a1) < Real.exp (M.δ * a2) := Real.exp_lt_exp.2 (by nlinarith)
  have he1 := Real.exp_pos (M.δ * a1)
  have i1 : M.c * a1 * Real.exp (M.δ * a1) ≤ M.c * a1 * Real.exp (M.δ * a2) :=
    mul_le_mul_of_nonneg_left he.le (by positivity)
  have i2 : M.c * a1 * Real.exp (M.δ * a2) < M.c * a2 * Real.exp (M.δ * a2) :=
    mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left h12 hc) (Real.exp_pos _)
  linarith

end Coop7iiSol


open Coop7iiSol in
theorem solution (M : Params) (hS : M.Standing) (θ : ℝ) (hθ : 0 ≤ θ) :
    ∀ P α : ℝ, IsSymEq M θ 0 P α →
      arrival M θ α P P = (M.b0 + θ) * D M α / (2 * M.b0 + θ) ∧
      firmProfit M θ 0 α P P = P * arrival M θ α P P - entCost M α / 2 - M.γ / M.w ∧
      utilization M (arrival M θ α P P) = 1 - 1 / (M.w * arrival M θ α P P + 1) ∧
      costShare 0 (arrival M θ α P P) (arrival M θ α P P) = 1 / 2 := by
  intro P α heq
  have hb0 : 0 < M.b0 := hS.2.1
  have hw : 0 < M.w := hS.2.2.2.1
  obtain ⟨hP, hDeq⟩ := eq_foc hS hθ heq
  have harr : arrival M θ α P P = (M.b0 + θ) * P := by
    unfold arrival; rw [hDeq]; ring
  have h2 : (2 * M.b0 + θ) ≠ 0 := by positivity
  have hlam : 0 < arrival M θ α P P := by rw [harr]; positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [harr, hDeq]; field_simp
  · unfold firmProfit costShare; ring
  · unfold utilization serviceRate
    have : M.w * arrival M θ α P P + 1 ≠ 0 := by positivity
    have : arrival M θ α P P + 1 / M.w ≠ 0 := by positivity
    field_simp
    ring
  · unfold costShare; ring
