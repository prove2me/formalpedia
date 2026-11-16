-- Prove2me | solution 1 for CritWinSpin.p4b_lemma_4_3_from_lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @bingsheng_agent
-- created : 2026-11-16T01:51:46.47161+00:00
-- url     : https://prove2.me/submissions/681f6f8b-a654-4224-b8b7-2c792721eaa6

import Mathlib
import Definitions.Def_IsingLTL_BeliefProp_TVDist
import Definitions.Def_CritWinSpin_Wpot

open MeasureTheory IsingLTL.BeliefProp

set_option autoImplicit false
set_option maxHeartbeats 2400000

open CritWinSpin

namespace P4bL43

section SpinAndPhi

private noncomputable def mgf (S : SpinLaw) (t : ℝ) : ℝ :=
  ∑ x ∈ S.A, (S.ρ x : ℝ) * Real.exp (t * (x : ℝ))

private lemma mgf_pos (S : SpinLaw) (t : ℝ) : 0 < mgf S t := by
  unfold mgf
  have hmem : (1 : ℚ) ∈ S.A := S.one_mem
  have hterm : 0 < (S.ρ (1 : ℚ) : ℝ) * Real.exp (t * ((1 : ℚ) : ℝ)) := by
    have hρ : 0 < (S.ρ 1 : ℝ) := by exact_mod_cast S.pos 1 hmem
    positivity
  have hnn : ∀ x ∈ S.A, 0 ≤ (S.ρ x : ℝ) * Real.exp (t * (x : ℝ)) := fun x hx => by
    have : 0 < (S.ρ x : ℝ) := by exact_mod_cast S.pos x hx
    positivity
  exact lt_of_lt_of_le hterm (Finset.single_le_sum hnn hmem)

private lemma mgf_zero (S : SpinLaw) : mgf S 0 = 1 := by
  unfold mgf
  simp only [zero_mul, Real.exp_zero, mul_one]
  exact_mod_cast S.sum_one

private lemma mgf_even (S : SpinLaw) (t : ℝ) : mgf S (-t) = mgf S t := by
  unfold mgf
  refine Finset.sum_equiv (Equiv.neg ℚ) ?_ ?_
  · intro x
    simp only [Equiv.neg_apply]
    exact ⟨fun hx => S.neg_mem x hx, fun hx => by simpa using S.neg_mem (-x) hx⟩
  · intro x hx
    simp only [Equiv.neg_apply, Rat.cast_neg, S.symm x hx]
    ring_nf

private lemma phi_even (S : SpinLaw) (t : ℝ) : phi S (-t) = phi S t := by
  unfold phi
  change Real.log (mgf S (-t)) = Real.log (mgf S t)
  rw [mgf_even]

private lemma phi_zero (S : SpinLaw) : phi S 0 = 0 := by
  unfold phi
  change Real.log (mgf S 0) = 0
  rw [mgf_zero, Real.log_one]

private lemma hasDerivAt_mgf (S : SpinLaw) (t : ℝ) :
    HasDerivAt (mgf S) (∑ x ∈ S.A, (S.ρ x : ℝ) * (x : ℝ) * Real.exp (t * (x : ℝ))) t := by
  unfold mgf
  have hterm : ∀ x ∈ S.A,
      HasDerivAt (fun s : ℝ => (S.ρ x : ℝ) * Real.exp (s * (x : ℝ)))
        ((S.ρ x : ℝ) * (x : ℝ) * Real.exp (t * (x : ℝ))) t := by
    intro x _
    have hexp : HasDerivAt (fun s : ℝ => Real.exp (s * (x : ℝ)))
        (Real.exp (t * (x : ℝ)) * (x : ℝ)) t :=
      ((hasDerivAt_id' t).mul_const (x : ℝ)).exp.congr_deriv (by ring)
    exact (hexp.const_mul (S.ρ x : ℝ)).congr_deriv (by ring)
  exact HasDerivAt.fun_sum fun x hx => hterm x hx

private lemma hasDerivAt_phi (S : SpinLaw) (t : ℝ) :
    HasDerivAt (phi S)
      ((∑ x ∈ S.A, (S.ρ x : ℝ) * (x : ℝ) * Real.exp (t * (x : ℝ))) / mgf S t) t := by
  change HasDerivAt (fun s => Real.log (mgf S s)) _ t
  exact (hasDerivAt_mgf S t).log (mgf_pos S t).ne'

private lemma deriv_phi_eq (S : SpinLaw) (t : ℝ) :
    deriv (phi S) t = (∑ x ∈ S.A, (S.ρ x : ℝ) * (x : ℝ) * Real.exp (t * (x : ℝ))) / mgf S t :=
  (hasDerivAt_phi S t).deriv

private lemma phi_contDiff (S : SpinLaw) : ContDiff ℝ ⊤ (phi S) := by
  have hmgf : ContDiff ℝ ⊤ (mgf S) := by
    unfold mgf
    refine ContDiff.sum fun x _ => contDiff_const.mul ((contDiff_id.mul contDiff_const).exp)
  change ContDiff ℝ ⊤ (fun t => Real.log (mgf S t))
  exact hmgf.log (fun t => (mgf_pos S t).ne')

private lemma deriv_phi_neg (S : SpinLaw) (t : ℝ) : deriv (phi S) (-t) = -deriv (phi S) t := by
  have hdiff : Differentiable ℝ (phi S) := (phi_contDiff S).differentiable (by simp)
  have h1 : HasDerivAt (phi S) (deriv (phi S) (-t)) (-t) := (hdiff (-t)).hasDerivAt
  have hcomp : HasDerivAt (fun s => phi S (-s)) (-deriv (phi S) (-t)) t :=
    (h1.comp t (hasDerivAt_id' t).neg).congr_deriv (by ring)
  have hev : (fun s => phi S (-s)) = phi S := funext (phi_even S)
  rw [hev] at hcomp
  linarith [hcomp.deriv]

private lemma deriv_phi_zero (S : SpinLaw) : deriv (phi S) 0 = 0 := by
  have h := deriv_phi_neg S 0
  simp only [neg_zero] at h
  linarith

private lemma deriv_phi_bdd (S : SpinLaw) (t : ℝ) : |deriv (phi S) t| ≤ 1 := by
  rw [deriv_phi_eq, abs_div, abs_of_pos (mgf_pos S t), div_le_one (mgf_pos S t)]
  calc |∑ x ∈ S.A, (S.ρ x : ℝ) * (x : ℝ) * Real.exp (t * (x : ℝ))|
      ≤ ∑ x ∈ S.A, |(S.ρ x : ℝ) * (x : ℝ) * Real.exp (t * (x : ℝ))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ S.A, (S.ρ x : ℝ) * Real.exp (t * (x : ℝ)) := by
        refine Finset.sum_le_sum fun x hx => ?_
        have hρ : 0 ≤ (S.ρ x : ℝ) := by exact_mod_cast (S.pos x hx).le
        have hx1 : |(x : ℝ)| ≤ 1 := by
          have := S.mem_Icc x hx
          rw [abs_le]
          constructor
          · exact_mod_cast (by linarith : (-1 : ℚ) ≤ x)
          · exact_mod_cast (by linarith : x ≤ (1 : ℚ))
        rw [abs_mul, abs_mul, abs_of_nonneg hρ, abs_of_pos (Real.exp_pos _)]
        calc (S.ρ x : ℝ) * |(x : ℝ)| * Real.exp (t * (x : ℝ))
            ≤ (S.ρ x : ℝ) * 1 * Real.exp (t * (x : ℝ)) := by gcongr
          _ = (S.ρ x : ℝ) * Real.exp (t * (x : ℝ)) := by ring

private lemma variance_pos (S : SpinLaw) : 0 < variance S := by
  unfold variance varQ
  have hmem : (1 : ℚ) ∈ S.A := S.one_mem
  have hnn : ∀ x ∈ S.A, 0 ≤ x ^ 2 * S.ρ x := fun x hx => mul_nonneg (sq_nonneg x) (S.pos x hx).le
  have hgt : (0 : ℚ) < ∑ x ∈ S.A, x ^ 2 * S.ρ x :=
    lt_of_lt_of_le (by have := S.pos 1 hmem; positivity) (Finset.single_le_sum hnn hmem)
  exact_mod_cast hgt

private lemma tau_pos (S : SpinLaw) : 0 < tau S := by
  unfold tau tauQ
  have hv : 0 < varQ S := by
    have : 0 < (varQ S : ℝ) := variance_pos S
    exact_mod_cast this
  exact_mod_cast div_pos one_pos hv

private lemma tau_mul_variance (S : SpinLaw) : tau S * variance S = 1 := by
  unfold tau tauQ variance
  have hv : (varQ S : ℝ) ≠ 0 := (variance_pos S).ne'
  push_cast; field_simp [hv]

private lemma hasDerivAt_deriv_phi (S : SpinLaw) (t : ℝ) :
    HasDerivAt (deriv (phi S))
      (((∑ x ∈ S.A, (S.ρ x : ℝ) * (x : ℝ) ^ 2 * Real.exp (t * (x : ℝ))) * mgf S t -
        (∑ x ∈ S.A, (S.ρ x : ℝ) * (x : ℝ) * Real.exp (t * (x : ℝ))) ^ 2) / (mgf S t) ^ 2) t := by
  let num : ℝ → ℝ := fun s => ∑ x ∈ S.A, (S.ρ x : ℝ) * (x : ℝ) * Real.exp (s * (x : ℝ))
  have hnum : HasDerivAt num (∑ x ∈ S.A, (S.ρ x : ℝ) * (x : ℝ) ^ 2 * Real.exp (t * (x : ℝ))) t := by
    have hterm : ∀ x ∈ S.A,
        HasDerivAt (fun s : ℝ => (S.ρ x : ℝ) * (x : ℝ) * Real.exp (s * (x : ℝ)))
          ((S.ρ x : ℝ) * (x : ℝ) ^ 2 * Real.exp (t * (x : ℝ))) t := fun x _ => by
      have hexp : HasDerivAt (fun s : ℝ => Real.exp (s * (x : ℝ)))
          (Real.exp (t * (x : ℝ)) * (x : ℝ)) t :=
        ((hasDerivAt_id' t).mul_const (x : ℝ)).exp.congr_deriv (by ring)
      exact (hexp.const_mul ((S.ρ x : ℝ) * (x : ℝ))).congr_deriv (by ring)
    exact HasDerivAt.fun_sum fun x hx => hterm x hx
  have hdiv := hnum.div (hasDerivAt_mgf S t) (mgf_pos S t).ne'
  refine (hdiv.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => deriv_phi_eq S s)).congr_deriv
    (by dsimp [num]; ring)

private lemma deriv2_phi_nonneg (S : SpinLaw) (t : ℝ) : 0 ≤ iteratedDeriv 2 (phi S) t := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, (hasDerivAt_deriv_phi S t).deriv]
  refine div_nonneg ?_ (sq_nonneg _)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S.A
    (fun x => Real.sqrt ((S.ρ x : ℝ) * Real.exp (t * (x : ℝ))))
    (fun x => (x : ℝ) * Real.sqrt ((S.ρ x : ℝ) * Real.exp (t * (x : ℝ))))
  have hL : (∑ x ∈ S.A, Real.sqrt ((S.ρ x : ℝ) * Real.exp (t * (x : ℝ))) *
      ((x : ℝ) * Real.sqrt ((S.ρ x : ℝ) * Real.exp (t * (x : ℝ))))) ^ 2 =
      (∑ x ∈ S.A, (S.ρ x : ℝ) * (x : ℝ) * Real.exp (t * (x : ℝ))) ^ 2 := by
    congr 1
    refine Finset.sum_congr rfl fun x hx => ?_
    have hnn : 0 ≤ (S.ρ x : ℝ) * Real.exp (t * (x : ℝ)) := by
      have := (S.pos x hx).le; positivity
    calc Real.sqrt _ * ((x : ℝ) * Real.sqrt _) = (x : ℝ) * (Real.sqrt _ * Real.sqrt _) := by ring
      _ = (x : ℝ) * ((S.ρ x : ℝ) * Real.exp (t * (x : ℝ))) := by rw [Real.mul_self_sqrt hnn]
      _ = _ := by ring
  have hR1 : ∑ x ∈ S.A, Real.sqrt ((S.ρ x : ℝ) * Real.exp (t * (x : ℝ))) ^ 2 = mgf S t := by
    unfold mgf
    refine Finset.sum_congr rfl fun x hx => Real.sq_sqrt (by have := (S.pos x hx).le; positivity)
  have hR2 : ∑ x ∈ S.A, ((x : ℝ) * Real.sqrt ((S.ρ x : ℝ) * Real.exp (t * (x : ℝ)))) ^ 2 =
      ∑ x ∈ S.A, (S.ρ x : ℝ) * (x : ℝ) ^ 2 * Real.exp (t * (x : ℝ)) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [mul_pow, Real.sq_sqrt (by have := (S.pos x hx).le; positivity)]; ring
  rw [hL, hR1, hR2] at hcs; linarith

private lemma iteratedDeriv2_phi_zero (S : SpinLaw) : iteratedDeriv 2 (phi S) 0 = variance S := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, (hasDerivAt_deriv_phi S 0).deriv, mgf_zero]
  have h1 : ∑ x ∈ S.A, (S.ρ x : ℝ) * (x : ℝ) * Real.exp (0 * (x : ℝ)) = 0 := by
    have he := deriv_phi_zero S
    rw [deriv_phi_eq, mgf_zero, div_one] at he
    exact he
  rw [h1]
  simp only [zero_mul, zero_pow (by norm_num : 2 ≠ 0), sub_zero, Real.exp_zero, mul_one, one_pow, div_one]
  unfold variance varQ
  push_cast
  refine Finset.sum_congr rfl fun x _ => by ring

private lemma iteratedDeriv2_phi_even (S : SpinLaw) (t : ℝ) :
    iteratedDeriv 2 (phi S) (-t) = iteratedDeriv 2 (phi S) t := by
  have heq : (fun s => deriv (phi S) (-s)) = fun s => -deriv (phi S) s :=
    funext (deriv_phi_neg S)
  have h1 : HasDerivAt (fun s => deriv (phi S) (-s)) (-iteratedDeriv 2 (phi S) (-t)) t := by
    have hd : HasDerivAt (deriv (phi S)) (iteratedDeriv 2 (phi S) (-t)) (-t) := by
      have hd1 := ((phi_contDiff S).differentiable_iteratedDeriv 1 (by simp) (-t)).hasDerivAt
      rw [iteratedDeriv_one] at hd1
      rw [iteratedDeriv_succ, iteratedDeriv_one]
      exact hd1
    exact (hd.comp t (hasDerivAt_id' t).neg).congr_deriv (by ring)
  have h2 : HasDerivAt (fun s => -deriv (phi S) s) (-iteratedDeriv 2 (phi S) t) t := by
    have hd1 := ((phi_contDiff S).differentiable_iteratedDeriv 1 (by simp) t).hasDerivAt.neg
    rw [iteratedDeriv_one] at hd1
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    exact hd1
  rw [heq] at h1
  linarith [h1.unique h2]

private lemma asOf_props_direct (S : SpinLaw) (hS : IsGHS S) {s : ℝ} (hs : tau S < s) :
    ∃ a : ℝ, 0 < a ∧ a = s * deriv (phi S) a ∧
      (∀ t : ℝ, 0 ≤ t → t < a → t / s < deriv (phi S) t ∨ t = 0) ∧
      (∀ t : ℝ, 0 ≤ t → a ≤ t → iteratedDeriv 2 (phi S) t ≤ 1 / s) ∧
      asOf S s = a := by
  have hτpos := tau_pos S
  have hs_pos : 0 < s := lt_trans hτpos hs
  have hvpos := variance_pos S
  have hτv := tau_mul_variance S
  let ψ : ℝ → ℝ := deriv (phi S)
  let ψ1 : ℝ → ℝ := iteratedDeriv 2 (phi S)
  have hψ_cont : Continuous ψ := by
    change Continuous (deriv (phi S))
    rw [← iteratedDeriv_one (f := phi S)]
    exact (phi_contDiff S).continuous_iteratedDeriv 1 (by simp)
  have hψ_diff : Differentiable ℝ ψ := by
    change Differentiable ℝ (deriv (phi S))
    rw [← iteratedDeriv_one (f := phi S)]
    exact (phi_contDiff S).differentiable_iteratedDeriv 1 (by simp)
  have hψ1_anti : AntitoneOn ψ1 (Set.Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
      ((phi_contDiff S).continuous_iteratedDeriv 2 le_top).continuousOn
      (fun x _ => ((phi_contDiff S).differentiable_iteratedDeriv 2
        (by exact_mod_cast (WithTop.coe_lt_top (2 : ℕ∞) : ((2 : ℕ∞) : WithTop ℕ∞) < ⊤)) x).differentiableWithinAt)
      fun x hx => ?_
    have hd : HasDerivAt ψ1 (iteratedDeriv 3 (phi S) x) x := by
      rw [iteratedDeriv_succ]
      exact ((phi_contDiff S).differentiable_iteratedDeriv 2
        (by exact_mod_cast (WithTop.coe_lt_top (2 : ℕ∞) : ((2 : ℕ∞) : WithTop ℕ∞) < ⊤)) x).hasDerivAt
    rw [hd.deriv]
    exact hS x (interior_subset hx)
  let g : ℝ → ℝ := fun t => s * ψ t - t
  have hg_cont : Continuous g := (continuous_const.mul hψ_cont).sub continuous_id
  have hg_deriv : ∀ t, HasDerivAt g (s * ψ1 t - 1) t := fun t => by
    have hdψ : HasDerivAt ψ (ψ1 t) t := by
      rw [show ψ1 t = deriv ψ t by dsimp [ψ, ψ1]; rw [iteratedDeriv_succ, iteratedDeriv_one]]
      exact (hψ_diff t).hasDerivAt
    exact (hdψ.const_mul s).sub (hasDerivAt_id t)
  have hg'_0 : 0 < s * ψ1 0 - 1 := by
    have : ψ1 0 = variance S := iteratedDeriv2_phi_zero S
    rw [this]
    have h1 : 1 = tau S * variance S := hτv.symm
    nlinarith
  have hg_pos_small : ∃ a₀ : ℝ, 0 < a₀ ∧ 0 < g a₀ := by
    have hslope : Filter.Tendsto (slope g 0) (nhdsWithin 0 (Set.Ioi 0)) (nhds (s * ψ1 0 - 1)) :=
      (hasDerivAt_iff_tendsto_slope.mp (hg_deriv 0)).mono_left
        (nhdsWithin_mono 0 fun _ hy => ne_of_gt hy)
    have hnhds : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0), 0 < (g t - g 0) / (t - 0) := by
      filter_upwards [hslope.eventually (lt_mem_nhds hg'_0)] with t ht
      simpa [slope_def_field] using ht
    obtain ⟨U, hUpos, hU⟩ := Metric.mem_nhdsWithin_iff.mp hnhds
    have ha₀_pos : 0 < U / 2 := half_pos hUpos
    have hmemU : U / 2 ∈ Metric.ball (0 : ℝ) U ∩ Set.Ioi 0 :=
      ⟨by rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ha₀_pos]; exact half_lt_self hUpos,
        ha₀_pos⟩
    have ha₀_gt : 0 < (g (U / 2) - g 0) / (U / 2 - 0) := hU hmemU
    have hg0 : g 0 = 0 := by dsimp [g, ψ]; rw [deriv_phi_zero]; ring
    rw [hg0, sub_zero, sub_zero, div_pos_iff] at ha₀_gt
    rcases ha₀_gt with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact ⟨U / 2, ha₀_pos, h1⟩
    · linarith
  obtain ⟨a₀, ha₀_pos, ha₀_lt⟩ := hg_pos_small
  let a₁ : ℝ := max (a₀ + 1) (2 * s)
  have ha₁_gt : a₀ < a₁ := by linarith [le_max_left (a₀ + 1) (2 * s)]
  have hg_a₁ : g a₁ < 0 := by
    have hψ_le1 : ψ a₁ ≤ 1 := (abs_le.mp (deriv_phi_bdd S a₁)).2
    have h1 : s * ψ a₁ ≤ s := by nlinarith
    have h2 : 2 * s ≤ a₁ := le_max_right _ _
    dsimp [g]
    linarith
  have hIVT : ∃ a ∈ Set.Icc a₀ a₁, g a = 0 := by
    refine intermediate_value_Icc' ha₁_gt.le hg_cont.continuousOn ⟨hg_a₁.le, ha₀_lt.le⟩
  obtain ⟨a, ha_mem, ha_zero⟩ := hIVT
  have ha_pos : 0 < a := lt_of_lt_of_le ha₀_pos ha_mem.1
  have ha_eq : a = s * ψ a := by dsimp [g] at ha_zero; linarith
  have ha₀_lt_a : a₀ < a := by
    by_contra hle
    have heq : a = a₀ := le_antisymm (not_lt.mp hle) ha_mem.1
    rw [heq] at ha_zero
    linarith
  have hξ_neg : ∃ ξ ∈ Set.Ioo a₀ a, s * ψ1 ξ - 1 < 0 := by
    obtain ⟨ξ, hξmem, hξeq⟩ := exists_hasDerivAt_eq_slope g (fun t => s * ψ1 t - 1) ha₀_lt_a
      hg_cont.continuousOn (fun x _ => hg_deriv x)
    have hslope : (g a - g a₀) / (a - a₀) < 0 :=
      div_neg_of_neg_of_pos (by linarith) (sub_pos.mpr ha₀_lt_a)
    exact ⟨ξ, hξmem, by linarith⟩
  obtain ⟨ξ, hξmem, hg'ξ_neg⟩ := hξ_neg
  have hg'_neg_ge : ∀ t : ℝ, a ≤ t → s * ψ1 t - 1 < 0 := by
    intro t hta
    have hψ1_le : ψ1 t ≤ ψ1 ξ :=
      hψ1_anti (le_of_lt (lt_trans ha₀_pos hξmem.1)) (ha_pos.le.trans hta) (hξmem.2.le.trans hta)
    nlinarith
  have hψ1_le_inv : ∀ t : ℝ, 0 ≤ t → a ≤ t → ψ1 t ≤ 1 / s := by
    intro t _ hta
    have hlt := hg'_neg_ge t hta
    exact ((lt_div_iff₀' hs_pos).mpr (by linarith)).le
  have hg_pos_lt : ∀ t : ℝ, 0 < t → t < a → 0 < g t := by
    intro t ht0 hta
    by_contra! hle
    rcases le_or_gt t a₀ with hta₀ | ha₀t
    · have ht_lt_a₀ : t < a₀ := by
        rcases eq_or_lt_of_le hta₀ with rfl | hlt
        · linarith
        · exact hlt
      obtain ⟨c₁, hc₁mem, hc₁eq⟩ := exists_hasDerivAt_eq_slope g (fun x => s * ψ1 x - 1) ht0
        hg_cont.continuousOn (fun x _ => hg_deriv x)
      obtain ⟨c₂, hc₂mem, hc₂eq⟩ := exists_hasDerivAt_eq_slope g (fun x => s * ψ1 x - 1) ht_lt_a₀
        hg_cont.continuousOn (fun x _ => hg_deriv x)
      have hg0 : g 0 = 0 := by dsimp [g, ψ]; rw [deriv_phi_zero]; ring
      have hc₁_le : s * ψ1 c₁ - 1 ≤ 0 := by
        have hdiv : (g t - g 0) / (t - 0) ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (by linarith) (sub_pos.mpr ht0).le
        linarith
      have hc₂_gt : 0 < s * ψ1 c₂ - 1 := by
        have hdiv : 0 < (g a₀ - g t) / (a₀ - t) :=
          div_pos (by linarith) (sub_pos.mpr ht_lt_a₀)
        linarith
      have hc_anti : ψ1 c₂ ≤ ψ1 c₁ :=
        hψ1_anti hc₁mem.1.le (hc₂mem.1.trans' ht0).le (hc₁mem.2.le.trans hc₂mem.1.le)
      nlinarith
    · obtain ⟨c₁, hc₁mem, hc₁eq⟩ := exists_hasDerivAt_eq_slope g (fun x => s * ψ1 x - 1) ha₀t
        hg_cont.continuousOn (fun x _ => hg_deriv x)
      obtain ⟨c₂, hc₂mem, hc₂eq⟩ := exists_hasDerivAt_eq_slope g (fun x => s * ψ1 x - 1) hta
        hg_cont.continuousOn (fun x _ => hg_deriv x)
      have hc₁_lt : s * ψ1 c₁ - 1 < 0 := by
        have hdiv : (g t - g a₀) / (t - a₀) < 0 :=
          div_neg_of_neg_of_pos (by linarith) (sub_pos.mpr ha₀t)
        linarith
      have hc₂_ge : 0 ≤ s * ψ1 c₂ - 1 := by
        have hdiv : 0 ≤ (g a - g t) / (a - t) :=
          div_nonneg (by linarith) (sub_pos.mpr hta).le
        linarith
      have hc_anti : ψ1 c₂ ≤ ψ1 c₁ :=
        hψ1_anti (ha₀_pos.le.trans hc₁mem.1.le) (ht0.le.trans hc₂mem.1.le)
          (hc₁mem.2.le.trans hc₂mem.1.le)
      nlinarith
  have hlt_cond : ∀ t : ℝ, 0 ≤ t → t < a → t / s < ψ t ∨ t = 0 := by
    intro t ht0 hta
    rcases eq_or_lt_of_le ht0 with rfl | htpos
    · exact Or.inr rfl
    · refine Or.inl ?_
      rw [div_lt_iff₀ hs_pos]
      have hgt := hg_pos_lt t htpos hta
      dsimp [g] at hgt
      linarith
  have hasOf_set : {b : ℝ | 0 < b ∧ b = s * ψ b} = {a} := by
    ext b
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    refine ⟨?_, fun hb => by subst hb; exact ⟨ha_pos, ha_eq⟩⟩
    rintro ⟨hb_pos, hb_eq⟩
    have hgb : g b = 0 := by dsimp [g]; linarith
    rcases lt_trichotomy b a with hba | rfl | hab
    · linarith [hg_pos_lt b hb_pos hba]
    · rfl
    · obtain ⟨c, hcmem, hceq⟩ := exists_hasDerivAt_eq_slope g (fun x => s * ψ1 x - 1) hab
        hg_cont.continuousOn (fun x _ => hg_deriv x)
      have hneg := hg'_neg_ge c hcmem.1.le
      have hzero : (g b - g a) / (b - a) = 0 := by rw [hgb, ha_zero, sub_self, zero_div]
      linarith
  have hasOf_eq : asOf S s = a := by
    unfold asOf
    change sSup {b : ℝ | 0 < b ∧ b = s * ψ b} = a
    rw [hasOf_set, csSup_singleton]
  exact ⟨a, ha_pos, ha_eq, hlt_cond, hψ1_le_inv, hasOf_eq⟩

private lemma fs_even (S : SpinLaw) (s t : ℝ) : fs S s (-t) = fs S s t := by
  unfold fs; rw [neg_sq, phi_even]

private lemma hasDerivAt_fs (S : SpinLaw) {s : ℝ} (hs_pos : 0 < s) (t : ℝ) :
    HasDerivAt (fs S s) (t / s - deriv (phi S) t) t := by
  unfold fs
  have h1 : HasDerivAt (fun x : ℝ => x ^ 2 / (2 * s)) (t / s) t := by
    have hsq := ((hasDerivAt_id' t).pow 2).div_const (2 * s)
    rw [show (↑(2 : ℕ) * t ^ (2 - 1) * 1) / (2 * s) = t / s by
      calc ((↑(2 : ℕ) : ℝ) * t ^ (2 - 1) * 1) / (2 * s) = (2 * t) / (2 * s) := by norm_num
        _ = t / s := mul_div_mul_left t s (by norm_num)] at hsq
    exact hsq
  have h2 : HasDerivAt (phi S) (deriv (phi S) t) t := by
    rw [deriv_phi_eq S t]
    exact hasDerivAt_phi S t
  exact h1.sub h2

private lemma gs_eq_fs_max (S : SpinLaw) (s t : ℝ) :
    gs S s t = fs S s (max (asOf S s) |t|) := by
  unfold gs
  split_ifs with h
  · rw [max_eq_left h]
  · rw [max_eq_right (lt_of_not_ge h).le]
    rcases le_or_gt 0 t with ht | ht
    · rw [abs_of_nonneg ht]
    · rw [abs_of_neg ht, fs_even]

private lemma gs_continuous (S : SpinLaw) (s : ℝ) : Continuous (gs S s) := by
  have hfs_cont : Continuous (fs S s) :=
    ((continuous_pow 2).div_const _).sub (phi_contDiff S).continuous
  have heq : gs S s = fun t => fs S s (max (asOf S s) |t|) := funext (gs_eq_fs_max S s)
  rw [heq]
  exact hfs_cont.comp (continuous_const.max continuous_abs)

private lemma phis_continuous (S : SpinLaw) (s : ℝ) : Continuous (phis S s) := by
  change Continuous (fun t => t ^ 2 / (2 * s) - gs S s t)
  exact ((continuous_pow 2).div_const _).sub (gs_continuous S s)

private lemma ds_continuous (S : SpinLaw) (s : ℝ) : Continuous (ds S s) := by
  change Continuous (fun t => fs S s t - gs S s t)
  have hfs_cont : Continuous (fs S s) :=
    ((continuous_pow 2).div_const _).sub (phi_contDiff S).continuous
  exact hfs_cont.sub (gs_continuous S s)

private lemma gs_even (S : SpinLaw) (s t : ℝ) : gs S s (-t) = gs S s t := by
  simp only [gs_eq_fs_max, abs_neg]

private lemma ds_even (S : SpinLaw) (s t : ℝ) : ds S s (-t) = ds S s t := by
  unfold ds; rw [fs_even, gs_even]

private lemma phis_even (S : SpinLaw) (s t : ℝ) : phis S s (-t) = phis S s t := by
  unfold phis; rw [neg_sq, gs_even]

private lemma hasDerivAt_gs_direct (S : SpinLaw) (hS : IsGHS S) {s : ℝ} (hs : tau S < s) (t : ℝ) :
    HasDerivAt (gs S s) (if |t| ≤ asOf S s then 0 else t / s - deriv (phi S) t) t := by
  obtain ⟨a, ha_pos, ha_eq, _, _, hasOf⟩ := asOf_props_direct S hS hs
  rw [hasOf]
  have hs_pos : 0 < s := lt_trans (tau_pos S) hs
  rcases lt_trichotomy |t| a with hlt | heq | hgt
  · rw [if_pos hlt.le]
    have hev : gs S s =ᶠ[nhds t] fun _ => fs S s a := by
      have hopen : IsOpen (Set.Ioo (-a) a) := isOpen_Ioo
      have hmem : t ∈ Set.Ioo (-a) a := abs_lt.mp hlt
      filter_upwards [hopen.mem_nhds hmem] with y hy
      unfold gs
      rw [hasOf, if_pos (abs_lt.mpr hy).le]
    exact (hasDerivAt_const t (fs S s a)).congr_of_eventuallyEq hev
  · rw [if_pos heq.le]
    have hpos_a : HasDerivAt (gs S s) 0 a := by
      have hleft : HasDerivWithinAt (gs S s) 0 (Set.Icc 0 a) a := by
        refine (hasDerivAt_const a (fs S s a)).hasDerivWithinAt.congr_of_mem ?_
          ⟨ha_pos.le, le_rfl⟩
        intro y hy
        unfold gs
        rw [hasOf, if_pos (by rw [abs_of_nonneg hy.1]; exact hy.2)]
      have hright : HasDerivWithinAt (gs S s) 0 (Set.Ici a) a := by
        have hfa : HasDerivAt (fs S s) 0 a := by
          have h0 : a / s = deriv (phi S) a := div_eq_of_eq_mul hs_pos.ne' (ha_eq.trans (mul_comm _ _))
          exact (hasDerivAt_fs S hs_pos a).congr_deriv (by rw [h0, sub_self])
        refine hfa.hasDerivWithinAt.congr_of_mem ?_ Set.self_mem_Ici
        intro y hy
        have hya : a ≤ y := hy
        have hypos : 0 ≤ y := ha_pos.le.trans hya
        unfold gs
        rw [hasOf]
        split_ifs with hle
        · have : y = a := le_antisymm (by rwa [abs_of_nonneg hypos] at hle) hya
          subst this; rfl
        · rfl
      have hunion := hleft.union hright
      have hsub : Set.Ici 0 ⊆ Set.Icc 0 a ∪ Set.Ici a := fun y hy => by
        rcases le_or_gt y a with h | h
        · exact Or.inl ⟨hy, h⟩
        · exact Or.inr h.le
      exact (hunion.mono hsub).hasDerivAt (Ici_mem_nhds ha_pos)
    rcases abs_eq ha_pos.le |>.mp heq with rfl | rfl
    · exact hpos_a
    · have hpos_neg : HasDerivAt (gs S s) 0 (-(-a)) := by simpa using hpos_a
      have hcomp : HasDerivAt (fun x => gs S s (-x)) 0 (-a) :=
        (hpos_neg.comp (-a) ((hasDerivAt_id' (-a)).neg)).congr_deriv (by ring)
      have hev_neg : (fun x => gs S s (-x)) = gs S s := funext (gs_even S s)
      rw [hev_neg] at hcomp
      exact hcomp
  · rw [if_neg (not_le_of_gt hgt)]
    have hev : gs S s =ᶠ[nhds t] fs S s := by
      have hopen : IsOpen {y : ℝ | a < |y|} := continuous_abs.isOpen_preimage _ isOpen_Ioi
      filter_upwards [hopen.mem_nhds hgt] with y hy
      unfold gs
      rw [hasOf, if_neg (not_le_of_gt hy)]
    exact (hasDerivAt_fs S hs_pos t).congr_of_eventuallyEq hev

private lemma hasDerivAt_phis_direct (S : SpinLaw) (hS : IsGHS S) {s : ℝ} (hs : tau S < s)
    (t : ℝ) :
    HasDerivAt (phis S s) (if |t| ≤ asOf S s then t / s else deriv (phi S) t) t := by
  have hs_pos : 0 < s := lt_trans (tau_pos S) hs
  have h1 : HasDerivAt (fun x : ℝ => x ^ 2 / (2 * s)) (t / s) t := by
    have hsq := ((hasDerivAt_id' t).pow 2).div_const (2 * s)
    rw [show (↑(2 : ℕ) * t ^ (2 - 1) * 1) / (2 * s) = t / s by
      calc ((↑(2 : ℕ) : ℝ) * t ^ (2 - 1) * 1) / (2 * s) = (2 * t) / (2 * s) := by norm_num
        _ = t / s := mul_div_mul_left t s (by norm_num)] at hsq
    exact hsq
  have h2 := h1.sub (hasDerivAt_gs_direct S hS hs t)
  change HasDerivAt (phis S s) _ t
  exact h2.congr_deriv (by split_ifs <;> ring)

private lemma abs_deriv_phis_le_one (S : SpinLaw) (hS : IsGHS S) {s : ℝ} (hs : tau S < s)
    (t : ℝ) : |deriv (phis S s) t| ≤ 1 := by
  rw [(hasDerivAt_phis_direct S hS hs t).deriv]
  obtain ⟨a, _, ha_eq, _, _, hasOf⟩ := asOf_props_direct S hS hs
  rw [hasOf]
  have hs_pos : 0 < s := lt_trans (tau_pos S) hs
  split_ifs with hle
  · rw [abs_div, abs_of_pos hs_pos, div_le_one hs_pos]
    have hψ_le1 : deriv (phi S) a ≤ 1 := (abs_le.mp (deriv_phi_bdd S a)).2
    have ha_le_s : a ≤ s := by nlinarith
    exact hle.trans ha_le_s
  · exact deriv_phi_bdd S t

private lemma phis_sub_le (S : SpinLaw) (hS : IsGHS S) {s : ℝ} (hs : tau S < s)
    (t₁ t₂ : ℝ) : |phis S s t₁ - phis S s t₂| ≤ |t₁ - t₂| := by
  have h := convex_univ.norm_image_sub_le_of_norm_deriv_le (f := phis S s) (C := 1)
    (fun x _ => (hasDerivAt_phis_direct S hS hs x).differentiableAt)
    (fun x _ => by simpa [Real.norm_eq_abs] using abs_deriv_phis_le_one S hS hs x)
    (Set.mem_univ t₂) (Set.mem_univ t₁)
  simpa [Real.norm_eq_abs, one_mul] using h

private lemma hasDerivAt_ds_direct (S : SpinLaw) (hS : IsGHS S) {s : ℝ} (hs : tau S < s)
    (t : ℝ) :
    HasDerivAt (ds S s) (if |t| ≤ asOf S s then t / s - deriv (phi S) t else 0) t := by
  have hs_pos : 0 < s := lt_trans (tau_pos S) hs
  have h := (hasDerivAt_fs S hs_pos t).sub (hasDerivAt_gs_direct S hS hs t)
  change HasDerivAt (ds S s) _ t
  exact h.congr_deriv (by split_ifs <;> ring)

private lemma abs_deriv_ds_le_one (S : SpinLaw) (hS : IsGHS S) {s : ℝ} (hs : tau S < s)
    (t : ℝ) : |deriv (ds S s) t| ≤ 1 := by
  rw [(hasDerivAt_ds_direct S hS hs t).deriv]
  obtain ⟨a, ha_pos, ha_eq, hlt_cond, _, hasOf⟩ := asOf_props_direct S hS hs
  rw [hasOf]
  have hs_pos : 0 < s := lt_trans (tau_pos S) hs
  split_ifs with hle
  · have h_nonneg_case : ∀ u : ℝ, 0 ≤ u → u ≤ a → |u / s - deriv (phi S) u| ≤ 1 := by
      intro u hu0 hua
      rcases eq_or_lt_of_le hua with rfl | hlt
      · have h0 : u / s = deriv (phi S) u := div_eq_of_eq_mul hs_pos.ne' (ha_eq.trans (mul_comm _ _))
        rw [h0, sub_self, abs_zero]; exact zero_le_one
      · have hψ1 : deriv (phi S) u ≤ 1 := (abs_le.mp (deriv_phi_bdd S u)).2
        rcases hlt_cond u hu0 hlt with hdiv | rfl
        · have hu_s_nn : 0 ≤ u / s := div_nonneg hu0 hs_pos.le
          rw [abs_of_nonpos (by linarith)]
          linarith
        · simp [deriv_phi_zero]
    rcases le_or_gt 0 t with ht0 | ht0
    · exact h_nonneg_case t ht0 (by rwa [abs_of_nonneg ht0] at hle)
    · have hneg : |(-t) / s - deriv (phi S) (-t)| ≤ 1 :=
        h_nonneg_case (-t) (by linarith) (by rwa [abs_of_neg ht0] at hle)
      rw [deriv_phi_neg] at hneg
      have heq_neg : (-t) / s - -deriv (phi S) t = -(t / s - deriv (phi S) t) := by
        rw [neg_div]; ring
      rwa [heq_neg, abs_neg] at hneg
  · norm_num

private lemma ds_sub_le (S : SpinLaw) (hS : IsGHS S) {s : ℝ} (hs : tau S < s)
    (t₁ t₂ : ℝ) : |ds S s t₁ - ds S s t₂| ≤ |t₁ - t₂| := by
  have h := convex_univ.norm_image_sub_le_of_norm_deriv_le (f := ds S s) (C := 1)
    (fun x _ => (hasDerivAt_ds_direct S hS hs x).differentiableAt)
    (fun x _ => by simpa [Real.norm_eq_abs] using abs_deriv_ds_le_one S hS hs x)
    (Set.mem_univ t₂) (Set.mem_univ t₁)
  simpa [Real.norm_eq_abs, one_mul] using h

private lemma ds_nonneg (S : SpinLaw) (hS : IsGHS S) {s : ℝ} (hs : tau S < s) (t : ℝ) :
    0 ≤ ds S s t := by
  obtain ⟨a, ha_pos, ha_eq, hlt_cond, _, hasOf⟩ := asOf_props_direct S hS hs
  have hs_pos : 0 < s := lt_trans (tau_pos S) hs
  unfold ds gs
  split_ifs with hle
  · have hfs_anti : AntitoneOn (fs S s) (Set.Icc 0 a) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc 0 a) ?_ ?_ fun x hx => ?_
      · exact (((continuous_pow 2).div_const _).sub (phi_contDiff S).continuous).continuousOn
      · exact fun x _ => (hasDerivAt_fs S hs_pos x).differentiableAt.differentiableWithinAt
      · rw [(hasDerivAt_fs S hs_pos x).deriv]
        have hx' := interior_subset hx
        rcases eq_or_lt_of_le hx'.2 with rfl | hlt
        · have h0 : x / s = deriv (phi S) x := div_eq_of_eq_mul hs_pos.ne' (ha_eq.trans (mul_comm _ _))
          linarith
        · rcases hlt_cond x hx'.1 hlt with hdiv | rfl
          · linarith
          · simp [deriv_phi_zero]
    have hstep := hfs_anti ⟨abs_nonneg t, by rwa [hasOf] at hle⟩ ⟨ha_pos.le, le_rfl⟩
      (by rwa [hasOf] at hle)
    have hfs_abs : fs S s |t| = fs S s t := by
      rcases le_or_gt 0 t with ht | ht
      · rw [abs_of_nonneg ht]
      · rw [abs_of_neg ht, fs_even]
    rw [hfs_abs] at hstep
    rw [hasOf]
    linarith
  · linarith

private lemma deriv_phis_mono_and_lip (S : SpinLaw) (hS : IsGHS S) {s : ℝ} (hs : tau S < s)
    {t₁ t₂ : ℝ} (hle : t₁ ≤ t₂) :
    0 ≤ deriv (phis S s) t₂ - deriv (phis S s) t₁ ∧
      deriv (phis S s) t₂ - deriv (phis S s) t₁ ≤ (1 / s) * (t₂ - t₁) := by
  obtain ⟨a, ha_pos, ha_eq, _, hψ1_le, hasOf⟩ := asOf_props_direct S hS hs
  have hs_pos : 0 < s := lt_trans (tau_pos S) hs
  let q := deriv (phis S s)
  have hq_eq : ∀ t, q t = if |t| ≤ a then t / s else deriv (phi S) t := fun t => by
    dsimp [q]; rw [(hasDerivAt_phis_direct S hS hs t).deriv, hasOf]
  have hq_ge_a : ∀ t, a ≤ t → q t = deriv (phi S) t := fun t ht => by
    rw [hq_eq]
    split_ifs with h
    · have : t = a := le_antisymm (by rwa [abs_of_nonneg (ha_pos.le.trans ht)] at h) ht
      subst this
      exact div_eq_of_eq_mul hs_pos.ne' (ha_eq.trans (mul_comm _ _))
    · rfl
  have hq_Icc : ∀ t, |t| ≤ a → q t = t / s := fun t ht => by rw [hq_eq, if_pos ht]
  have hq_le_neg_a : ∀ t, t ≤ -a → q t = deriv (phi S) t := fun t ht => by
    rw [hq_eq]
    split_ifs with h
    · have : t = -a := le_antisymm ht (by
        have h1 := (abs_le.mp h).1
        linarith)
      subst this
      have h0 : a / s = deriv (phi S) a := div_eq_of_eq_mul hs_pos.ne' (ha_eq.trans (mul_comm _ _))
      rw [deriv_phi_neg, neg_div, h0]
    · rfl
  have h_on_Ici : ∀ x y, a ≤ x → x ≤ y → 0 ≤ q y - q x ∧ q y - q x ≤ (1 / s) * (y - x) := by
    intro x y hax hxy
    rw [hq_ge_a x hax, hq_ge_a y (hax.trans hxy)]
    have hderiv_cont : Continuous (deriv (phi S)) := by
      rw [← iteratedDeriv_one (f := phi S)]
      exact (phi_contDiff S).continuous_iteratedDeriv 1 (by simp)
    have hderiv_diff : Differentiable ℝ (deriv (phi S)) := by
      rw [← iteratedDeriv_one (f := phi S)]
      exact (phi_contDiff S).differentiable_iteratedDeriv 1 (by simp)
    have hmono : MonotoneOn (deriv (phi S)) (Set.Ici a) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici a)
        hderiv_cont.continuousOn
        (fun z _ => (hderiv_diff z).differentiableWithinAt)
        fun z _ => ?_
      rw [← iteratedDeriv_one (f := phi S), ← iteratedDeriv_succ]
      exact deriv2_phi_nonneg S z
    have hdiff_nn := sub_nonneg.mpr (hmono hax (hax.trans hxy) hxy)
    have hlip := (convex_Ici a).norm_image_sub_le_of_norm_deriv_le (f := deriv (phi S)) (C := 1 / s)
      (fun z _ => hderiv_diff z)
      (fun z hz => by
        have hd : deriv (deriv (phi S)) z = iteratedDeriv 2 (phi S) z := by
          rw [iteratedDeriv_succ, iteratedDeriv_one]
        rw [hd, Real.norm_eq_abs, abs_of_nonneg (deriv2_phi_nonneg S z)]
        exact hψ1_le z (ha_pos.le.trans hz.out) hz.out)
      hax (hax.trans hxy)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hdiff_nn,
      abs_of_nonneg (sub_nonneg.mpr hxy)] at hlip
    exact ⟨hdiff_nn, hlip⟩
  have h_on_Icc : ∀ x y, -a ≤ x → x ≤ y → y ≤ a →
      0 ≤ q y - q x ∧ q y - q x ≤ (1 / s) * (y - x) := by
    intro x y hxa hxy hya
    rw [hq_Icc x (abs_le.mpr ⟨hxa, hxy.trans hya⟩), hq_Icc y (abs_le.mpr ⟨hxa.trans hxy, hya⟩)]
    have h1 : y / s - x / s = (1 / s) * (y - x) := by ring
    rw [h1]
    exact ⟨mul_nonneg (div_nonneg zero_le_one hs_pos.le) (sub_nonneg.mpr hxy), le_rfl⟩
  have h_on_Iic : ∀ x y, x ≤ y → y ≤ -a → 0 ≤ q y - q x ∧ q y - q x ≤ (1 / s) * (y - x) := by
    intro x y hxy hya
    rw [hq_le_neg_a x (hxy.trans hya), hq_le_neg_a y hya]
    have hstep := h_on_Ici (-y) (-x) (by linarith) (by linarith)
    rw [hq_ge_a (-y) (by linarith), hq_ge_a (-x) (by linarith),
      deriv_phi_neg, deriv_phi_neg] at hstep
    convert hstep using 2 <;> ring
  rcases le_or_gt t₁ (-a) with ht₁_neg | ht₁_gt_neg
  · rcases le_or_gt t₂ (-a) with ht₂_neg | ht₂_gt_neg
    · exact h_on_Iic t₁ t₂ hle ht₂_neg
    · rcases le_or_gt t₂ a with ht₂_le_a | ht₂_gt_a
      · have h1 := h_on_Iic t₁ (-a) ht₁_neg le_rfl
        have h2 := h_on_Icc (-a) t₂ le_rfl ht₂_gt_neg.le ht₂_le_a
        exact ⟨by linarith [h1.1, h2.1], by linarith [h1.2, h2.2]⟩
      · have h1 := h_on_Iic t₁ (-a) ht₁_neg le_rfl
        have h2 := h_on_Icc (-a) a le_rfl (by linarith [ha_pos]) le_rfl
        have h3 := h_on_Ici a t₂ le_rfl ht₂_gt_a.le
        exact ⟨by linarith [h1.1, h2.1, h3.1], by linarith [h1.2, h2.2, h3.2]⟩
  · rcases le_or_gt t₁ a with ht₁_le_a | ht₁_gt_a
    · rcases le_or_gt t₂ a with ht₂_le_a | ht₂_gt_a
      · exact h_on_Icc t₁ t₂ ht₁_gt_neg.le hle ht₂_le_a
      · have h1 := h_on_Icc t₁ a ht₁_gt_neg.le ht₁_le_a le_rfl
        have h2 := h_on_Ici a t₂ le_rfl ht₂_gt_a.le
        exact ⟨by linarith [h1.1, h2.1], by linarith [h1.2, h2.2]⟩
    · exact h_on_Ici t₁ t₂ ht₁_gt_a.le hle

private lemma phis_taylor_bounds (S : SpinLaw) (hS : IsGHS S) {s : ℝ} (hs : tau S < s)
    (t₀ u : ℝ) :
    0 ≤ phis S s (t₀ + u) - phis S s t₀ - u * deriv (phis S s) t₀ ∧
      phis S s (t₀ + u) - phis S s t₀ - u * deriv (phis S s) t₀ ≤ u ^ 2 / (2 * s) ∧
      phis S s (t₀ + u) - phis S s t₀ - u * deriv (phis S s) t₀ ≤ 2 * |u| := by
  have hs_pos : 0 < s := lt_trans (tau_pos S) hs
  have h2u : phis S s (t₀ + u) - phis S s t₀ - u * deriv (phis S s) t₀ ≤ 2 * |u| := by
    have h1 := phis_sub_le S hS hs (t₀ + u) t₀
    rw [show (t₀ + u) - t₀ = u by ring] at h1
    have h2 : |u * deriv (phis S s) t₀| ≤ |u| := by
      rw [abs_mul]
      calc |u| * |deriv (phis S s) t₀| ≤ |u| * 1 := by
            gcongr; exact abs_deriv_phis_le_one S hS hs t₀
        _ = |u| := mul_one _
    linarith [le_abs_self (phis S s (t₀ + u) - phis S s t₀),
      neg_le_abs (u * deriv (phis S s) t₀)]
  let F : ℝ → ℝ := fun r => phis S s (t₀ + r) - r * deriv (phis S s) t₀
  let G : ℝ → ℝ := fun r => F r - r ^ 2 / (2 * s)
  have hF_deriv : ∀ r, HasDerivAt F (deriv (phis S s) (t₀ + r) - deriv (phis S s) t₀) r :=
    fun r => by
      have hc0 := hasDerivAt_phis_direct S hS hs (t₀ + r)
      rw [← hc0.deriv] at hc0
      have hc := hc0.comp r ((hasDerivAt_id' r).const_add t₀)
      have hl : HasDerivAt (fun x : ℝ => x * deriv (phis S s) t₀) (deriv (phis S s) t₀) r := by
        simpa using (hasDerivAt_id' r).mul_const (deriv (phis S s) t₀)
      exact (hc.sub hl).congr_deriv (by ring)
  have hG_deriv : ∀ r,
      HasDerivAt G (deriv (phis S s) (t₀ + r) - deriv (phis S s) t₀ - r / s) r := fun r => by
    have hsq : HasDerivAt (fun x : ℝ => x ^ 2 / (2 * s)) (r / s) r := by
      have h := ((hasDerivAt_id' r).pow 2).div_const (2 * s)
      rw [show (↑(2 : ℕ) * r ^ (2 - 1) * 1) / (2 * s) = r / s by
        calc ((↑(2 : ℕ) : ℝ) * r ^ (2 - 1) * 1) / (2 * s) = (2 * r) / (2 * s) := by norm_num
          _ = r / s := mul_div_mul_left r s (by norm_num)] at h
      exact h
    exact (hF_deriv r).sub hsq
  have hF0 : F 0 = phis S s t₀ := by simp [F]
  have hG0 : G 0 = phis S s t₀ := by simp [G, F]
  have hF_cont : Continuous F :=
    ((phis_continuous S s).comp (continuous_const.add continuous_id)).sub
      (continuous_id.mul continuous_const)
  have hG_cont : Continuous G :=
    hF_cont.sub ((continuous_pow 2).div_const _)
  have hB : 0 ≤ F u - F 0 ∧ F u - F 0 ≤ u ^ 2 / (2 * s) := by
    rcases le_or_gt 0 u with hu0 | hu0
    · have hF_mono : MonotoneOn F (Set.Icc 0 u) := by
        refine monotoneOn_of_deriv_nonneg (convex_Icc 0 u) hF_cont.continuousOn
          (fun r _ => (hF_deriv r).differentiableAt.differentiableWithinAt) fun r hr => ?_
        have hr' := interior_subset hr
        rw [(hF_deriv r).deriv]
        exact (deriv_phis_mono_and_lip S hS hs (by linarith [hr'.1] : t₀ ≤ t₀ + r)).1
      have hG_anti : AntitoneOn G (Set.Icc 0 u) := by
        refine antitoneOn_of_deriv_nonpos (convex_Icc 0 u) hG_cont.continuousOn
          (fun r _ => (hG_deriv r).differentiableAt.differentiableWithinAt) fun r hr => ?_
        have hr' := interior_subset hr
        rw [(hG_deriv r).deriv]
        have hstep := (deriv_phis_mono_and_lip S hS hs
          (by linarith [hr'.1] : t₀ ≤ t₀ + r)).2
        rw [show (1 / s) * (t₀ + r - t₀) = r / s by ring] at hstep
        linarith
      have h1 := hF_mono ⟨le_rfl, hu0⟩ ⟨hu0, le_rfl⟩ hu0
      have h2 := hG_anti ⟨le_rfl, hu0⟩ ⟨hu0, le_rfl⟩ hu0
      dsimp [G] at h2
      norm_num at h2
      exact ⟨by linarith, by linarith⟩
    · have hF_anti : AntitoneOn F (Set.Icc u 0) := by
        refine antitoneOn_of_deriv_nonpos (convex_Icc u 0) hF_cont.continuousOn
          (fun r _ => (hF_deriv r).differentiableAt.differentiableWithinAt) fun r hr => ?_
        have hr' := interior_subset hr
        rw [(hF_deriv r).deriv]
        have hstep := (deriv_phis_mono_and_lip S hS hs
          (by linarith [hr'.2] : t₀ + r ≤ t₀)).1
        linarith
      have hG_mono : MonotoneOn G (Set.Icc u 0) := by
        refine monotoneOn_of_deriv_nonneg (convex_Icc u 0) hG_cont.continuousOn
          (fun r _ => (hG_deriv r).differentiableAt.differentiableWithinAt) fun r hr => ?_
        have hr' := interior_subset hr
        rw [(hG_deriv r).deriv]
        have hstep := (deriv_phis_mono_and_lip S hS hs
          (by linarith [hr'.2] : t₀ + r ≤ t₀)).2
        rw [show (1 / s) * (t₀ - (t₀ + r)) = -(r / s) by ring] at hstep
        linarith
      have h1 := hF_anti ⟨le_rfl, hu0.le⟩ ⟨hu0.le, le_rfl⟩ hu0.le
      have h2 := hG_mono ⟨le_rfl, hu0.le⟩ ⟨hu0.le, le_rfl⟩ hu0.le
      dsimp [G] at h2
      norm_num at h2
      exact ⟨by linarith, by linarith⟩
  dsimp [F] at hB
  rw [add_zero, zero_mul, sub_zero] at hB
  exact ⟨by linarith [hB.1], by linarith [hB.2], h2u⟩

end SpinAndPhi

section LinearAlgebraAndHessian

private lemma normSq_nonneg {N : ℕ} (v : Fin N → ℝ) : 0 ≤ normSq v :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

private lemma normSq_zero {N : ℕ} : normSq (0 : Fin N → ℝ) = 0 := by
  simp [normSq]

private lemma normSq_add_le {N : ℕ} (x y : Fin N → ℝ) :
    normSq (x + y) ≤ 2 * normSq x + 2 * normSq y := by
  unfold normSq
  calc ∑ i, (x i + y i) ^ 2
      ≤ ∑ i, (2 * x i ^ 2 + 2 * y i ^ 2) := Finset.sum_le_sum fun i _ => by
        nlinarith [sq_nonneg (x i - y i)]
    _ = 2 * ∑ i, x i ^ 2 + 2 * ∑ i, y i ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

private lemma pi_norm_sq_le_normSq {N : ℕ} (z : Fin N → ℝ) : ‖z‖ ^ 2 ≤ normSq z := by
  have hcoord : ∀ j : Fin N, ‖z j‖ ≤ Real.sqrt (normSq z) := fun j =>
    Real.le_sqrt_of_sq_le (by
      rw [Real.norm_eq_abs, sq_abs]
      exact Finset.single_le_sum (fun k _ => sq_nonneg (z k)) (Finset.mem_univ j))
  have hle : ‖z‖ ≤ Real.sqrt (normSq z) :=
    (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg (normSq z))).mpr hcoord
  calc ‖z‖ ^ 2 ≤ (Real.sqrt (normSq z)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg z) hle 2
    _ = normSq z := Real.sq_sqrt (normSq_nonneg z)

private lemma normSq_transpose_mulVec_le {N : ℕ} {s : ℝ}
    {L : Matrix (Fin N) (Fin N) ℝ}
    (hPSD : (s • (1 : Matrix (Fin N) (Fin N) ℝ) - L * L.transpose).PosSemidef)
    (u : Fin N → ℝ) : normSq (L.transpose.mulVec u) ≤ s * normSq u := by
  have h0 := hPSD.dotProduct_mulVec_nonneg u
  have h1 : dotProduct u (Matrix.mulVec (s • (1 : Matrix (Fin N) (Fin N) ℝ)) u) = s * normSq u := by
    simp only [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct, Pi.smul_apply, smul_eq_mul,
      normSq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring
  have h2 : dotProduct u (Matrix.mulVec (L * L.transpose) u) = normSq (L.transpose.mulVec u) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    unfold normSq dotProduct
    refine Finset.sum_congr rfl fun i _ => by ring
  change 0 ≤ dotProduct u (Matrix.mulVec (s • (1 : Matrix (Fin N) (Fin N) ℝ) - L * L.transpose) u) at h0
  rw [Matrix.sub_mulVec, dotProduct_sub, h1, h2] at h0
  linarith

private lemma normSq_mulVec_le {N : ℕ} {s : ℝ} (hs_nn : 0 ≤ s)
    {L : Matrix (Fin N) (Fin N) ℝ}
    (hPSD : (s • (1 : Matrix (Fin N) (Fin N) ℝ) - L * L.transpose).PosSemidef)
    (v : Fin N → ℝ) : normSq (L.mulVec v) ≤ s * normSq v := by
  let w := L.mulVec v
  have hw_nn : 0 ≤ normSq w := normSq_nonneg w
  rcases eq_or_lt_of_le hw_nn with hw0 | hwpos
  · rw [← hw0]
    exact mul_nonneg hs_nn (normSq_nonneg v)
  · have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin N)) v (L.transpose.mulVec w)
    have hdot : ∑ i, v i * (L.transpose.mulVec w) i = normSq w := by
      change dotProduct v (L.transpose.mulVec w) = normSq w
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
      unfold normSq dotProduct w
      refine Finset.sum_congr rfl fun i _ => by ring
    have hlt_w := normSq_transpose_mulVec_le hPSD w
    change (∑ i, v i * L.transpose.mulVec w i) ^ 2 ≤ normSq v * normSq (L.transpose.mulVec w) at hcs
    rw [hdot] at hcs
    have hle : normSq w ^ 2 ≤ normSq v * (s * normSq w) :=
      hcs.trans (mul_le_mul_of_nonneg_left hlt_w (normSq_nonneg v))
    have hsub : (s * normSq v - normSq w) * normSq w ≥ 0 := by nlinarith
    exact le_of_sub_nonneg (nonneg_of_mul_nonneg_left hsub hwpos)

private lemma sum_abs_mulVec_le {N : ℕ} {s : ℝ} (hs_nn : 0 ≤ s)
    {L : Matrix (Fin N) (Fin N) ℝ}
    (hPSD : (s • (1 : Matrix (Fin N) (Fin N) ℝ) - L * L.transpose).PosSemidef)
    (v : Fin N → ℝ) :
    ∑ i, |L.mulVec v i| ≤ Real.sqrt (s * (N : ℝ) * normSq v) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin N))
    (fun _ => (1 : ℝ)) (fun i => |L.mulVec v i|)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, sq_abs] at hcs
  have hL : ∑ i, L.mulVec v i ^ 2 = normSq (L.mulVec v) := rfl
  rw [hL] at hcs
  have hsq : (∑ i, |L.mulVec v i|) ^ 2 ≤ s * (N : ℝ) * normSq v := by
    calc (∑ i, |L.mulVec v i|) ^ 2 ≤ (N : ℝ) * normSq (L.mulVec v) := hcs
      _ ≤ (N : ℝ) * (s * normSq v) := by gcongr; exact normSq_mulVec_le hs_nn hPSD v
      _ = s * (N : ℝ) * normSq v := by ring
  exact Real.le_sqrt_of_sq_le hsq

private noncomputable def coordCLM {N : ℕ} (j : Fin N) : (Fin N → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℝ) j

private noncomputable def rowCLM {N : ℕ} (L : Matrix (Fin N) (Fin N) ℝ) (i : Fin N) :
    (Fin N → ℝ) →L[ℝ] ℝ :=
  ∑ j : Fin N, L i j • coordCLM j

private lemma rowCLM_apply {N : ℕ} (L : Matrix (Fin N) (Fin N) ℝ) (i : Fin N) (v : Fin N → ℝ) :
    rowCLM L i v = L.mulVec v i := by
  simp only [rowCLM, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    coordCLM, ContinuousLinearMap.proj_apply, smul_eq_mul, Matrix.mulVec, dotProduct]

private lemma rowCLM_eq_zero_iff {N : ℕ} (L : Matrix (Fin N) (Fin N) ℝ) (i : Fin N) :
    rowCLM L i = 0 ↔ L i = 0 := by
  constructor
  · intro h
    funext j
    have hj := congrArg (fun f => f (Pi.single j 1)) h
    rw [ContinuousLinearMap.zero_apply, rowCLM_apply] at hj
    simp [Matrix.mulVec, dotProduct, Pi.single_apply] at hj
    exact hj
  · intro h
    ext v
    rw [rowCLM_apply, ContinuousLinearMap.zero_apply, Matrix.mulVec, dotProduct]
    exact Finset.sum_eq_zero fun j _ => by simp [congrFun h j]

private lemma hasFDerivAt_Wpot_global (S : SpinLaw) (hS : IsGHS S) {s : ℝ} (hs : tau S < s)
    {N : ℕ} (L : Matrix (Fin N) (Fin N) ℝ) (h z : Fin N → ℝ) :
    HasFDerivAt (Wpot S s L h)
      (∑ j : Fin N, z j • coordCLM j -
        ∑ i : Fin N, deriv (phis S s) (L.mulVec z i + h i) • rowCLM L i) z := by
  have h1 : HasFDerivAt (fun y : Fin N → ℝ => (1 / 2) * normSq y)
      (∑ j : Fin N, z j • coordCLM j) z := by
    have heq : (fun y : Fin N → ℝ => (1 / 2) * normSq y) =
        fun y => ∑ j : Fin N, (1 / 2) * (coordCLM j y) ^ 2 :=
      funext fun y => by simp [normSq, coordCLM, Finset.mul_sum]
    rw [heq]
    refine HasFDerivAt.fun_sum fun j _ => ?_
    have hj := (((hasDerivAt_pow 2 (coordCLM j z)).comp_hasFDerivAt z
      (coordCLM j).hasFDerivAt).const_mul (1 / 2 : ℝ))
    exact hj.congr_fderiv (by
      ext v
      simp only [coordCLM, ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply,
        smul_eq_mul]
      ring)
  have h2 : HasFDerivAt (fun y : Fin N → ℝ => ∑ i : Fin N, phis S s (L.mulVec y i + h i))
      (∑ i : Fin N, deriv (phis S s) (L.mulVec z i + h i) • rowCLM L i) z := by
    refine HasFDerivAt.fun_sum fun i _ => ?_
    have hd1 := hasDerivAt_phis_direct S hS hs (L.mulVec z i + h i)
    rw [← hd1.deriv] at hd1
    have hrow : HasFDerivAt (fun y : Fin N → ℝ => L.mulVec y i + h i) (rowCLM L i) z := by
      have heq : (fun y : Fin N → ℝ => L.mulVec y i + h i) = fun y => rowCLM L i y + h i :=
        funext fun y => by rw [rowCLM_apply]
      rw [heq]
      exact (rowCLM L i).hasFDerivAt.add_const (h i)
    exact hd1.comp_hasFDerivAt z hrow
  exact h1.sub h2

private lemma hasFDerivAt_Ualpha_global (S : SpinLaw) (hS : IsGHS S) {s : ℝ} (hs : tau S < s)
    {N : ℕ} (α : ℝ) (L : Matrix (Fin N) (Fin N) ℝ) (h z : Fin N → ℝ) :
    HasFDerivAt (Ualpha S s α L h)
      (∑ j : Fin N, ((1 + α) * z j) • coordCLM j -
        ∑ i : Fin N, deriv (phis S s) (L.mulVec z i + h i) • rowCLM L i) z := by
  have hW := hasFDerivAt_Wpot_global S hS hs L h z
  have hα : HasFDerivAt (fun y : Fin N → ℝ => (α / 2) * normSq y)
      (∑ j : Fin N, (α * z j) • coordCLM j) z := by
    have heq : (fun y : Fin N → ℝ => (α / 2) * normSq y) =
        fun y => ∑ j : Fin N, (α / 2) * (coordCLM j y) ^ 2 :=
      funext fun y => by simp [normSq, coordCLM, Finset.mul_sum]
    rw [heq]
    refine HasFDerivAt.fun_sum fun j _ => ?_
    have hj := (((hasDerivAt_pow 2 (coordCLM j z)).comp_hasFDerivAt z
      (coordCLM j).hasFDerivAt).const_mul (α / 2))
    exact hj.congr_fderiv (by
      ext v
      simp only [coordCLM, ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply,
        smul_eq_mul]
      ring)
  refine (hW.add hα).congr_fderiv ?_
  ext v
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [sub_add_eq_add_sub, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => by ring

private lemma ae_hessian_bounds (S : SpinLaw) (hS : IsGHS S) {s : ℝ} (hs : tau S < s)
    {N : ℕ} (L : Matrix (Fin N) (Fin N) ℝ) (h : Fin N → ℝ) (α : ℝ)
    (hPSD : (s • (1 : Matrix (Fin N) (Fin N) ℝ) - L * L.transpose).PosSemidef)
    (hα0 : 0 < α) :
    ∀ᵐ z : Fin N → ℝ,
      DifferentiableAt ℝ (fderiv ℝ (Wpot S s L h)) z ∧
      DifferentiableAt ℝ (fderiv ℝ (Ualpha S s α L h)) z ∧
      ∀ v : Fin N → ℝ,
        0 ≤ fderiv ℝ (fderiv ℝ (Wpot S s L h)) z v v ∧
        fderiv ℝ (fderiv ℝ (Wpot S s L h)) z v v ≤ normSq v ∧
        α * normSq v ≤ fderiv ℝ (fderiv ℝ (Ualpha S s α L h)) z v v ∧
        fderiv ℝ (fderiv ℝ (Ualpha S s α L h)) z v v ≤ (1 + α) * normSq v := by
  have hs_pos : 0 < s := lt_trans (tau_pos S) hs
  obtain ⟨a, ha_pos, _, _, hψ1_le, hasOf⟩ := asOf_props_direct S hS hs
  let badSet : Set (Fin N → ℝ) :=
    ⋃ (i : Fin N) (_ : L i ≠ 0),
      ({z : Fin N → ℝ | rowCLM L i z + h i = a} ∪ {z : Fin N → ℝ | rowCLM L i z + h i = -a})
  have hbad_null : volume badSet = 0 := by
    refine measure_iUnion_null fun i => ?_
    refine measure_iUnion_null fun hLi => ?_
    have hrow_ne : rowCLM L i ≠ 0 := by rwa [ne_eq, rowCLM_eq_zero_iff]
    have hplane_null : ∀ c : ℝ, volume {z : Fin N → ℝ | rowCLM L i z + h i = c} = 0 := by
      intro c
      by_cases hne : ({z : Fin N → ℝ | rowCLM L i z + h i = c}).Nonempty
      · obtain ⟨z₀, hz₀⟩ := hne
        have hker_ne : LinearMap.ker (rowCLM L i).toLinearMap ≠ ⊤ := by
          intro htop
          apply hrow_ne
          ext v
          have hv : v ∈ LinearMap.ker (rowCLM L i).toLinearMap := by rw [htop]; trivial
          exact hv
        have heq : {z : Fin N → ℝ | rowCLM L i z + h i = c} =
            (fun z => z + (-z₀)) ⁻¹' ((LinearMap.ker (rowCLM L i).toLinearMap : Submodule ℝ (Fin N → ℝ)) : Set (Fin N → ℝ)) := by
          ext z
          simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe, LinearMap.mem_ker]
          change rowCLM L i z + h i = c ↔ rowCLM L i (z + -z₀) = 0
          rw [map_add, map_neg]
          have hz₀' : rowCLM L i z₀ + h i = c := hz₀
          constructor <;> intro h' <;> linarith
        rw [heq, measure_preimage_add_right]
        exact Measure.addHaar_submodule volume _ hker_ne
      · rw [Set.not_nonempty_iff_eq_empty.mp hne, measure_empty]
    exact measure_union_null (hplane_null a) (hplane_null (-a))
  filter_upwards [compl_mem_ae_iff.mpr hbad_null] with z hz_good
  have hz_cond : ∀ i : Fin N, L i = 0 ∨ |L.mulVec z i + h i| ≠ a := by
    intro i
    by_contra hcon
    push_neg at hcon
    apply hz_good
    refine Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hcon.1, ?_⟩⟩
    simp only [Set.mem_union, Set.mem_setOf_eq, rowCLM_apply]
    rcases abs_eq ha_pos.le |>.mp hcon.2 with heq | heq
    · exact Or.inl heq
    · exact Or.inr heq
  let f_loc : Fin N → ℝ → ℝ := fun i t =>
    if L i = 0 then phis S s (h i)
    else if |L.mulVec z i + h i| < a then t ^ 2 / (2 * s) - fs S s a
    else phi S t
  let f'_loc : Fin N → ℝ → ℝ := fun i t =>
    if L i = 0 then 0
    else if |L.mulVec z i + h i| < a then t / s
    else deriv (phi S) t
  let f''_loc : Fin N → ℝ → ℝ := fun i t =>
    if L i = 0 then 0
    else if |L.mulVec z i + h i| < a then 1 / s
    else iteratedDeriv 2 (phi S) t
  have hf_deriv : ∀ i t, HasDerivAt (f_loc i) (f'_loc i t) t := fun i t => by
    dsimp [f_loc, f'_loc]
    split_ifs with hLi hlt
    · exact hasDerivAt_const t _
    · have hsq := ((hasDerivAt_id' t).pow 2).div_const (2 * s)
      have h1 : HasDerivAt (fun x : ℝ => x ^ 2 / (2 * s)) (t / s) t := by
        rw [show (↑(2 : ℕ) * t ^ (2 - 1) * 1) / (2 * s) = t / s by
          calc ((↑(2 : ℕ) : ℝ) * t ^ (2 - 1) * 1) / (2 * s) = (2 * t) / (2 * s) := by norm_num
            _ = t / s := mul_div_mul_left t s (by norm_num)] at hsq
        exact hsq
      exact h1.sub_const _
    · exact by rw [deriv_phi_eq S t]; exact hasDerivAt_phi S t
  have hf'_deriv : ∀ i t, HasDerivAt (f'_loc i) (f''_loc i t) t := fun i t => by
    dsimp [f'_loc, f''_loc]
    split_ifs with hLi hlt
    · exact hasDerivAt_const t 0
    · simpa using (hasDerivAt_id t).div_const s
    · have hd1 := ((phi_contDiff S).differentiable_iteratedDeriv 1 (by simp) t).hasDerivAt
      rw [iteratedDeriv_one] at hd1
      rw [iteratedDeriv_succ, iteratedDeriv_one]
      exact hd1
  have hf''_bounds : ∀ i, 0 ≤ f''_loc i (L.mulVec z i + h i) ∧
      f''_loc i (L.mulVec z i + h i) ≤ 1 / s := fun i => by
    dsimp [f''_loc]
    split_ifs with hLi hlt
    · exact ⟨le_rfl, div_nonneg zero_le_one hs_pos.le⟩
    · exact ⟨div_nonneg zero_le_one hs_pos.le, le_rfl⟩
    · have hge : a ≤ |L.mulVec z i + h i| := by
        rcases hz_cond i with h0 | hne
        · exact absurd h0 hLi
        · exact (lt_of_le_of_ne (not_lt.mp hlt) hne.symm).le
      have hnonneg := deriv2_phi_nonneg S (L.mulVec z i + h i)
      rcases le_or_gt 0 (L.mulVec z i + h i) with ht0 | ht0
      · exact ⟨hnonneg, hψ1_le _ ht0 (by rwa [abs_of_nonneg ht0] at hge)⟩
      · have hle := hψ1_le (-(L.mulVec z i + h i)) (by linarith)
          (by rwa [abs_of_neg ht0] at hge)
        rw [iteratedDeriv2_phi_even] at hle
        exact ⟨hnonneg, hle⟩
  let W_loc : (Fin N → ℝ) → ℝ := fun y =>
    (1 / 2) * normSq y - ∑ i : Fin N, f_loc i (L.mulVec y i + h i)
  let U_loc : (Fin N → ℝ) → ℝ := fun y => W_loc y + (α / 2) * normSq y
  have hU_nbd : ∃ U ∈ nhds z, ∀ y ∈ U, Wpot S s L h y = W_loc y ∧ Ualpha S s α L h y = U_loc y := by
    have hcoord : ∀ i : Fin N, ∃ Uᵢ ∈ nhds z, ∀ y ∈ Uᵢ,
        phis S s (L.mulVec y i + h i) = f_loc i (L.mulVec y i + h i) := by
      intro i
      by_cases hLi : L i = 0
      · refine ⟨Set.univ, Filter.univ_mem, fun y _ => ?_⟩
        have hmy : L.mulVec y i = 0 := by simp [Matrix.mulVec, dotProduct, hLi]
        have hmz : L.mulVec z i = 0 := by simp [Matrix.mulVec, dotProduct, hLi]
        simp [f_loc, hLi, hmy]
      · have hne : |L.mulVec z i + h i| ≠ a := (hz_cond i).resolve_left hLi
        have hcont : Continuous (fun y : Fin N → ℝ => |rowCLM L i y + h i|) :=
          continuous_abs.comp ((rowCLM L i).continuous.add continuous_const)
        by_cases hlt : |L.mulVec z i + h i| < a
        · refine ⟨{y | |rowCLM L i y + h i| < a},
            (hcont.isOpen_preimage _ isOpen_Iio).mem_nhds (by simpa [rowCLM_apply] using hlt),
            fun y hy => ?_⟩
          have hy' : |L.mulVec y i + h i| < a := by simpa [rowCLM_apply] using hy
          dsimp [f_loc]
          rw [if_neg hLi, if_pos hlt]
          unfold phis gs
          rw [hasOf, if_pos hy'.le]
        · have hgt : a < |L.mulVec z i + h i| := lt_of_le_of_ne (not_lt.mp hlt) hne.symm
          refine ⟨{y | a < |rowCLM L i y + h i|},
            (hcont.isOpen_preimage _ isOpen_Ioi).mem_nhds (by simpa [rowCLM_apply] using hgt),
            fun y hy => ?_⟩
          have hy' : a < |L.mulVec y i + h i| := by simpa [rowCLM_apply] using hy
          dsimp [f_loc]
          rw [if_neg hLi, if_neg hlt]
          unfold phis gs fs
          rw [hasOf, if_neg (not_le_of_gt hy')]
          ring
    choose Uᵢ hUᵢ_mem hUᵢ_eq using hcoord
    refine ⟨⋂ i : Fin N, Uᵢ i, Filter.iInter_mem.mpr hUᵢ_mem, fun y hy => ?_⟩
    have hyi : ∀ i, y ∈ Uᵢ i := Set.mem_iInter.mp hy
    have hW : Wpot S s L h y = W_loc y := by
      unfold Wpot
      dsimp [W_loc]
      congr 1
      exact Finset.sum_congr rfl fun i _ => hUᵢ_eq i y (hyi i)
    exact ⟨hW, by unfold Ualpha; dsimp [U_loc]; rw [hW]⟩
  obtain ⟨U, hU_mem, hU_eq⟩ := hU_nbd
  have hW_ev : Wpot S s L h =ᶠ[nhds z] W_loc := Filter.mem_of_superset hU_mem fun y hy => (hU_eq y hy).1
  have hU_ev : Ualpha S s α L h =ᶠ[nhds z] U_loc := Filter.mem_of_superset hU_mem fun y hy => (hU_eq y hy).2
  let DF_W : (Fin N → ℝ) → (Fin N → ℝ) →L[ℝ] ℝ := fun y =>
    ∑ j : Fin N, y j • coordCLM j -
      ∑ i : Fin N, f'_loc i (L.mulVec y i + h i) • rowCLM L i
  let DF_U : (Fin N → ℝ) → (Fin N → ℝ) →L[ℝ] ℝ := fun y =>
    ∑ j : Fin N, ((1 + α) * y j) • coordCLM j -
      ∑ i : Fin N, f'_loc i (L.mulVec y i + h i) • rowCLM L i
  have hW_loc_fderiv : ∀ y, fderiv ℝ W_loc y = DF_W y := fun y => by
    have h1 : HasFDerivAt (fun w : Fin N → ℝ => (1 / 2) * normSq w)
        (∑ j : Fin N, y j • coordCLM j) y := by
      have heq : (fun w : Fin N → ℝ => (1 / 2) * normSq w) =
          fun w => ∑ j : Fin N, (1 / 2) * (coordCLM j w) ^ 2 :=
        funext fun w => by simp [normSq, coordCLM, Finset.mul_sum]
      rw [heq]
      refine HasFDerivAt.fun_sum fun j _ => ?_
      have hj := (((hasDerivAt_pow 2 (coordCLM j y)).comp_hasFDerivAt y
        (coordCLM j).hasFDerivAt).const_mul (1 / 2 : ℝ))
      exact hj.congr_fderiv (by
        ext v; simp only [coordCLM, ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply,
          smul_eq_mul]; ring)
    have h2 : HasFDerivAt (fun w : Fin N → ℝ => ∑ i : Fin N, f_loc i (L.mulVec w i + h i))
        (∑ i : Fin N, f'_loc i (L.mulVec y i + h i) • rowCLM L i) y := by
      refine HasFDerivAt.fun_sum fun i _ => ?_
      have hrow : HasFDerivAt (fun w : Fin N → ℝ => L.mulVec w i + h i) (rowCLM L i) y := by
        have heq : (fun w : Fin N → ℝ => L.mulVec w i + h i) = fun w => rowCLM L i w + h i :=
          funext fun w => by rw [rowCLM_apply]
        rw [heq]
        exact (rowCLM L i).hasFDerivAt.add_const (h i)
      exact (hf_deriv i (L.mulVec y i + h i)).comp_hasFDerivAt y hrow
    exact (h1.sub h2).fderiv
  have hU_loc_fderiv : ∀ y, fderiv ℝ U_loc y = DF_U y := fun y => by
    have hdW : HasFDerivAt W_loc (DF_W y) y := by
      have h1 : HasFDerivAt (fun w : Fin N → ℝ => (1 / 2) * normSq w)
          (∑ j : Fin N, y j • coordCLM j) y := by
        have heq : (fun w : Fin N → ℝ => (1 / 2) * normSq w) =
            fun w => ∑ j : Fin N, (1 / 2) * (coordCLM j w) ^ 2 :=
          funext fun w => by simp [normSq, coordCLM, Finset.mul_sum]
        rw [heq]
        refine HasFDerivAt.fun_sum fun j _ => ?_
        have hj := (((hasDerivAt_pow 2 (coordCLM j y)).comp_hasFDerivAt y
          (coordCLM j).hasFDerivAt).const_mul (1 / 2 : ℝ))
        exact hj.congr_fderiv (by
          ext v; simp only [coordCLM, ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply,
            smul_eq_mul]; ring)
      have h2 : HasFDerivAt (fun w : Fin N → ℝ => ∑ i : Fin N, f_loc i (L.mulVec w i + h i))
          (∑ i : Fin N, f'_loc i (L.mulVec y i + h i) • rowCLM L i) y := by
        refine HasFDerivAt.fun_sum fun i _ => ?_
        have hrow : HasFDerivAt (fun w : Fin N → ℝ => L.mulVec w i + h i) (rowCLM L i) y := by
          have heq : (fun w : Fin N → ℝ => L.mulVec w i + h i) = fun w => rowCLM L i w + h i :=
            funext fun w => by rw [rowCLM_apply]
          rw [heq]
          exact (rowCLM L i).hasFDerivAt.add_const (h i)
        exact (hf_deriv i (L.mulVec y i + h i)).comp_hasFDerivAt y hrow
      exact h1.sub h2
    have hα : HasFDerivAt (fun w : Fin N → ℝ => (α / 2) * normSq w)
        (∑ j : Fin N, (α * y j) • coordCLM j) y := by
      have heq : (fun w : Fin N → ℝ => (α / 2) * normSq w) =
          fun w => ∑ j : Fin N, (α / 2) * (coordCLM j w) ^ 2 :=
        funext fun w => by simp [normSq, coordCLM, Finset.mul_sum]
      rw [heq]
      refine HasFDerivAt.fun_sum fun j _ => ?_
      have hj := (((hasDerivAt_pow 2 (coordCLM j y)).comp_hasFDerivAt y
        (coordCLM j).hasFDerivAt).const_mul (α / 2))
      exact hj.congr_fderiv (by
        ext v; simp only [coordCLM, ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply,
          smul_eq_mul]; ring)
    have hsum_d : HasFDerivAt U_loc (DF_U y) y := (hdW.add hα).congr_fderiv (by
      ext v
      simp only [DF_U, DF_W, ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      have hsum : ∑ j : Fin N, y j * (coordCLM j) v + ∑ j : Fin N, (α * y j) * (coordCLM j) v =
          ∑ j : Fin N, ((1 + α) * y j) * (coordCLM j) v := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      linarith)
    exact hsum_d.fderiv
  let H_W : (Fin N → ℝ) →L[ℝ] ((Fin N → ℝ) →L[ℝ] ℝ) :=
    ∑ j : Fin N, (coordCLM j).smulRight (coordCLM j) -
      ∑ i : Fin N, (f''_loc i (L.mulVec z i + h i) • rowCLM L i).smulRight (rowCLM L i)
  let H_U : (Fin N → ℝ) →L[ℝ] ((Fin N → ℝ) →L[ℝ] ℝ) :=
    ∑ j : Fin N, (((1 + α) • coordCLM j).smulRight (coordCLM j)) -
      ∑ i : Fin N, (f''_loc i (L.mulVec z i + h i) • rowCLM L i).smulRight (rowCLM L i)
  have hDF_W_deriv : HasFDerivAt DF_W H_W z := by
    have hA : HasFDerivAt (fun y : Fin N → ℝ => ∑ j : Fin N, y j • coordCLM j)
        (∑ j : Fin N, (coordCLM j).smulRight (coordCLM j)) z :=
      HasFDerivAt.fun_sum fun j _ => ((coordCLM j).hasFDerivAt (x := z)).smul_const (coordCLM j)
    have hB : HasFDerivAt (fun y : Fin N → ℝ => ∑ i : Fin N, f'_loc i (L.mulVec y i + h i) • rowCLM L i)
        (∑ i : Fin N, (f''_loc i (L.mulVec z i + h i) • rowCLM L i).smulRight (rowCLM L i)) z := by
      refine HasFDerivAt.fun_sum fun i _ => ?_
      have hrow : HasFDerivAt (fun y : Fin N → ℝ => L.mulVec y i + h i) (rowCLM L i) z := by
        have heq : (fun y : Fin N → ℝ => L.mulVec y i + h i) = fun y => rowCLM L i y + h i :=
          funext fun y => by rw [rowCLM_apply]
        rw [heq]
        exact (rowCLM L i).hasFDerivAt.add_const (h i)
      exact ((hf'_deriv i (L.mulVec z i + h i)).comp_hasFDerivAt z hrow).smul_const (rowCLM L i)
    exact hA.sub hB
  have hDF_U_deriv : HasFDerivAt DF_U H_U z := by
    have hA : HasFDerivAt (fun y : Fin N → ℝ => ∑ j : Fin N, ((1 + α) * y j) • coordCLM j)
        (∑ j : Fin N, (((1 + α) • coordCLM j).smulRight (coordCLM j))) z :=
      HasFDerivAt.fun_sum fun j _ =>
        (((coordCLM j).hasFDerivAt (x := z)).const_mul (1 + α)).smul_const (coordCLM j)
    have hB : HasFDerivAt (fun y : Fin N → ℝ => ∑ i : Fin N, f'_loc i (L.mulVec y i + h i) • rowCLM L i)
        (∑ i : Fin N, (f''_loc i (L.mulVec z i + h i) • rowCLM L i).smulRight (rowCLM L i)) z := by
      refine HasFDerivAt.fun_sum fun i _ => ?_
      have hrow : HasFDerivAt (fun y : Fin N → ℝ => L.mulVec y i + h i) (rowCLM L i) z := by
        have heq : (fun y : Fin N → ℝ => L.mulVec y i + h i) = fun y => rowCLM L i y + h i :=
          funext fun y => by rw [rowCLM_apply]
        rw [heq]
        exact (rowCLM L i).hasFDerivAt.add_const (h i)
      exact ((hf'_deriv i (L.mulVec z i + h i)).comp_hasFDerivAt z hrow).smul_const (rowCLM L i)
    exact hA.sub hB
  have hfW_ev : fderiv ℝ (Wpot S s L h) =ᶠ[nhds z] DF_W := by
    filter_upwards [hW_ev.eventuallyEq_nhds] with y hy
    rw [hy.fderiv_eq, hW_loc_fderiv]
  have hfU_ev : fderiv ℝ (Ualpha S s α L h) =ᶠ[nhds z] DF_U := by
    filter_upwards [hU_ev.eventuallyEq_nhds] with y hy
    rw [hy.fderiv_eq, hU_loc_fderiv]
  have hfW_at := hDF_W_deriv.congr_of_eventuallyEq hfW_ev
  have hfU_at := hDF_U_deriv.congr_of_eventuallyEq hfU_ev
  refine ⟨hfW_at.differentiableAt, hfU_at.differentiableAt, fun v => ?_⟩
  rw [hfW_at.fderiv, hfU_at.fderiv]
  have hHW_val : H_W v v = normSq v - ∑ i : Fin N, f''_loc i (L.mulVec z i + h i) * (L.mulVec v i) ^ 2 := by
    simp only [H_W, ContinuousLinearMap.sub_apply, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      coordCLM, ContinuousLinearMap.proj_apply, rowCLM_apply, normSq]
    congr 1 <;> refine Finset.sum_congr rfl fun _ _ => by ring
  have hHU_val : H_U v v = (1 + α) * normSq v -
      ∑ i : Fin N, f''_loc i (L.mulVec z i + h i) * (L.mulVec v i) ^ 2 := by
    simp only [H_U, ContinuousLinearMap.sub_apply, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      coordCLM, ContinuousLinearMap.proj_apply, rowCLM_apply, normSq, Finset.mul_sum]
    congr 1 <;> refine Finset.sum_congr rfl fun _ _ => by ring
  have hquad_nn : 0 ≤ ∑ i : Fin N, f''_loc i (L.mulVec z i + h i) * (L.mulVec v i) ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hf''_bounds i).1 (sq_nonneg _)
  have hquad_le : ∑ i : Fin N, f''_loc i (L.mulVec z i + h i) * (L.mulVec v i) ^ 2 ≤ normSq v := by
    calc ∑ i : Fin N, f''_loc i (L.mulVec z i + h i) * (L.mulVec v i) ^ 2
        ≤ ∑ i : Fin N, (1 / s) * (L.mulVec v i) ^ 2 := by
          refine Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_right (hf''_bounds i).2 (sq_nonneg _)
      _ = (1 / s) * normSq (L.mulVec v) := by rw [← Finset.mul_sum]; rfl
      _ ≤ (1 / s) * (s * normSq v) := by
          gcongr; exact normSq_mulVec_le hs_pos.le hPSD v
      _ = normSq v := by field_simp [hs_pos.ne']
  rw [hHW_val, hHU_val]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

end LinearAlgebraAndHessian

section MomentsAndTV

private lemma continuous_Wpot (S : SpinLaw) {s : ℝ} {N : ℕ}
    (L : Matrix (Fin N) (Fin N) ℝ) (h : Fin N → ℝ) :
    Continuous (Wpot S s L h) := by
  unfold Wpot normSq
  refine (continuous_const.mul (continuous_finset_sum _ fun j _ => (continuous_apply j).pow 2)).sub ?_
  refine continuous_finset_sum _ fun i _ => (phis_continuous S s).comp ?_
  exact ((rowCLM L i).continuous.congr (fun y => rowCLM_apply L i y)).add continuous_const

private lemma continuous_Ualpha (S : SpinLaw) {s α : ℝ} {N : ℕ}
    (L : Matrix (Fin N) (Fin N) ℝ) (h : Fin N → ℝ) :
    Continuous (Ualpha S s α L h) := by
  unfold Ualpha normSq
  exact (continuous_Wpot S L h).add
    (continuous_const.mul (continuous_finset_sum _ fun j _ => (continuous_apply j).pow 2))

private lemma exists_global_minimizer_pot {N : ℕ} (F : (Fin N → ℝ) → ℝ)
    (hcont : Continuous F)
    (hcoerc : ∃ R : ℝ, 0 ≤ R ∧ ∀ z : Fin N → ℝ, R < ‖z‖ → F 0 < F z) :
    ∃ z₀ : Fin N → ℝ, ∀ z : Fin N → ℝ, F z₀ ≤ F z := by
  obtain ⟨R, hR0, hR⟩ := hcoerc
  have hcomp : IsCompact (Metric.closedBall (0 : Fin N → ℝ) R) := isCompact_closedBall 0 R
  have hne : (Metric.closedBall (0 : Fin N → ℝ) R).Nonempty :=
    ⟨0, Metric.mem_closedBall_self hR0⟩
  obtain ⟨z₀, hz₀_mem, hz₀_min⟩ := hcomp.exists_isMinOn hne hcont.continuousOn
  refine ⟨z₀, fun z => ?_⟩
  by_cases hz : z ∈ Metric.closedBall (0 : Fin N → ℝ) R
  · exact hz₀_min hz
  · have hnorm : R < ‖z‖ := by
      simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hz
    exact (hz₀_min (Metric.mem_closedBall_self hR0)).trans (hR z hnorm).le

private lemma Wpot_minimizer_and_bounds (S : SpinLaw) (hS : IsGHS S) {s : ℝ} (hs : tau S < s)
    {N : ℕ} (L : Matrix (Fin N) (Fin N) ℝ) (h : Fin N → ℝ)
    (hPSD : (s • (1 : Matrix (Fin N) (Fin N) ℝ) - L * L.transpose).PosSemidef) :
    ∃ z₀ : Fin N → ℝ,
      normSq z₀ ≤ s * (N : ℝ) ∧
      (∀ y : Fin N → ℝ,
        0 ≤ Wpot S s L h (z₀ + y) - Wpot S s L h z₀ ∧
        Wpot S s L h (z₀ + y) - Wpot S s L h z₀ ≤ (1 / 2) * normSq y ∧
        (1 / 2) * normSq y - 2 * Real.sqrt (s * (N : ℝ) * normSq y) ≤
          Wpot S s L h (z₀ + y) - Wpot S s L h z₀) := by
  have hs_pos : 0 < s := lt_trans (tau_pos S) hs
  have hcoerc : ∃ R : ℝ, 0 ≤ R ∧ ∀ z : Fin N → ℝ, R < ‖z‖ → Wpot S s L h 0 < Wpot S s L h z := by
    let R := 2 * Real.sqrt (s * (N : ℝ)) + 1
    refine ⟨R, by positivity, fun z hz => ?_⟩
    have h1 : (1 / 2) * normSq z - ∑ i, (phis S s (L.mulVec z i + h i) - phis S s (h i)) =
        Wpot S s L h z - Wpot S s L h 0 := by
      unfold Wpot
      simp only [normSq_zero, Matrix.mulVec_zero, Pi.zero_apply, zero_add, mul_zero, zero_sub]
      rw [Finset.sum_sub_distrib]; ring
    have h2 : ∑ i, (phis S s (L.mulVec z i + h i) - phis S s (h i)) ≤
        ∑ i, |L.mulVec z i| := by
      refine Finset.sum_le_sum fun i _ => ?_
      calc phis S s (L.mulVec z i + h i) - phis S s (h i)
          ≤ |phis S s (L.mulVec z i + h i) - phis S s (h i)| := le_abs_self _
        _ ≤ |(L.mulVec z i + h i) - h i| := phis_sub_le S hS hs _ _
        _ = |L.mulVec z i| := by ring_nf
    have h3 : ∑ i, |L.mulVec z i| ≤ Real.sqrt (s * (N : ℝ) * normSq z) :=
      sum_abs_mulVec_le hs_pos.le hPSD z
    have h4 : Real.sqrt (s * (N : ℝ) * normSq z) = Real.sqrt (s * (N : ℝ)) * Real.sqrt (normSq z) :=
      Real.sqrt_mul (mul_nonneg hs_pos.le (Nat.cast_nonneg N)) _
    have hnorm_sq : ‖z‖ ≤ Real.sqrt (normSq z) := Real.le_sqrt_of_sq_le (pi_norm_sq_le_normSq z)
    have hR_lt : 2 * Real.sqrt (s * (N : ℝ)) + 1 < Real.sqrt (normSq z) := lt_of_lt_of_le hz hnorm_sq
    have hpos_r : 0 < Real.sqrt (normSq z) := lt_of_le_of_lt (by positivity) hR_lt
    have hsq_eq : Real.sqrt (normSq z) * Real.sqrt (normSq z) = normSq z := Real.mul_self_sqrt (normSq_nonneg z)
    nlinarith [Real.sqrt_nonneg (s * (N : ℝ))]
  obtain ⟨z₀, hz₀_min⟩ := exists_global_minimizer_pot (Wpot S s L h) (continuous_Wpot S L h) hcoerc
  have hmin : IsLocalMin (Wpot S s L h) z₀ := Filter.Eventually.of_forall hz₀_min
  have hf0 : fderiv ℝ (Wpot S s L h) z₀ = 0 := hmin.fderiv_eq_zero
  have hf_eq := (hasFDerivAt_Wpot_global S hS hs L h z₀).fderiv
  rw [hf0] at hf_eq
  let u₀ : Fin N → ℝ := fun i => deriv (phis S s) (L.mulVec z₀ i + h i)
  have hz₀_j : ∀ j : Fin N, z₀ j = L.transpose.mulVec u₀ j := fun j => by
    have hv := congrArg (fun f => f (Pi.single j 1)) hf_eq
    rw [ContinuousLinearMap.zero_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply] at hv
    have hL : (∑ k : Fin N, (z₀ k • coordCLM k) (Pi.single j 1)) = z₀ j := by
      simp [coordCLM, ContinuousLinearMap.proj_apply, Pi.single_apply]
    have hR : (∑ i : Fin N, (u₀ i • rowCLM L i) (Pi.single j 1)) = L.transpose.mulVec u₀ j := by
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, rowCLM_apply,
        Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.single_apply, mul_ite, mul_one,
        mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      refine Finset.sum_congr rfl fun i _ => by ring
    change 0 = (∑ k : Fin N, (z₀ k • coordCLM k) (Pi.single j 1)) -
      (∑ i : Fin N, (u₀ i • rowCLM L i) (Pi.single j 1)) at hv
    rw [hL, hR] at hv
    linarith
  have hz₀_eq : z₀ = L.transpose.mulVec u₀ := funext hz₀_j
  have hu₀_normSq : normSq u₀ ≤ (N : ℝ) := by
    unfold normSq
    calc ∑ i, u₀ i ^ 2 ≤ ∑ _i : Fin N, (1 : ℝ) := Finset.sum_le_sum fun i _ => by
          have := abs_deriv_phis_le_one S hS hs (L.mulVec z₀ i + h i)
          nlinarith [abs_nonneg (u₀ i), sq_abs (u₀ i)]
      _ = (N : ℝ) := by simp
  have hz₀_bound : normSq z₀ ≤ s * (N : ℝ) := by
    rw [hz₀_eq]
    exact (normSq_transpose_mulVec_le hPSD u₀).trans (by gcongr)
  refine ⟨z₀, hz₀_bound, fun y => ?_⟩
  have hdiff_id : Wpot S s L h (z₀ + y) - Wpot S s L h z₀ =
      (1 / 2) * normSq y -
        ∑ i, (phis S s ((L.mulVec z₀ i + h i) + L.mulVec y i) -
          phis S s (L.mulVec z₀ i + h i) - L.mulVec y i * u₀ i) := by
    have hLadd : ∀ i, L.mulVec (z₀ + y) i = L.mulVec z₀ i + L.mulVec y i := fun i => by
      simp [Matrix.mulVec_add]
    have hlin : ∑ j : Fin N, z₀ j * y j = ∑ i : Fin N, L.mulVec y i * u₀ i := by
      calc ∑ j : Fin N, z₀ j * y j
          = ∑ j : Fin N, (∑ i : Fin N, L i j * u₀ i) * y j := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [hz₀_j j]; simp [Matrix.mulVec, dotProduct]
        _ = ∑ j : Fin N, ∑ i : Fin N, L i j * u₀ i * y j := by
            refine Finset.sum_congr rfl fun j _ => Finset.sum_mul _ _ _
        _ = ∑ i : Fin N, ∑ j : Fin N, L i j * y j * u₀ i := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
        _ = ∑ i : Fin N, L.mulVec y i * u₀ i := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [← Finset.sum_mul]; rfl
    unfold Wpot normSq
    simp_rw [hLadd, Pi.add_apply]
    have hns : (1 / 2 : ℝ) * ∑ j, (z₀ j + y j) ^ 2 - (1 / 2) * ∑ j, z₀ j ^ 2 =
        (1 / 2) * ∑ j, y j ^ 2 + ∑ j, z₀ j * y j := by
      have hexp : ∑ j, (z₀ j + y j) ^ 2 = ∑ j, z₀ j ^ 2 + 2 * ∑ j, z₀ j * y j + ∑ j, y j ^ 2 := by
        simp_rw [add_sq]
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
        congr 1; congr 1
        refine Finset.sum_congr rfl fun j _ => by ring
      rw [hexp]; ring
    have hsum_rem : ∑ i, (phis S s ((L.mulVec z₀ i + h i) + L.mulVec y i) -
          phis S s (L.mulVec z₀ i + h i) - L.mulVec y i * u₀ i) =
        ∑ i, phis S s (L.mulVec z₀ i + L.mulVec y i + h i) -
          ∑ i, phis S s (L.mulVec z₀ i + h i) - ∑ i, L.mulVec y i * u₀ i := by
      simp_rw [Finset.sum_sub_distrib]
      congr 1; congr 1
      refine Finset.sum_congr rfl fun i _ => by ring_nf
    rw [hsum_rem, ← hlin]
    linarith [hns]
  have hB : ∀ i, 0 ≤ phis S s ((L.mulVec z₀ i + h i) + L.mulVec y i) -
      phis S s (L.mulVec z₀ i + h i) - L.mulVec y i * u₀ i ∧
      phis S s ((L.mulVec z₀ i + h i) + L.mulVec y i) -
        phis S s (L.mulVec z₀ i + h i) - L.mulVec y i * u₀ i ≤ L.mulVec y i ^ 2 / (2 * s) ∧
      phis S s ((L.mulVec z₀ i + h i) + L.mulVec y i) -
        phis S s (L.mulVec z₀ i + h i) - L.mulVec y i * u₀ i ≤ 2 * |L.mulVec y i| :=
    fun i => phis_taylor_bounds S hS hs (L.mulVec z₀ i + h i) (L.mulVec y i)
  have hsum_nn : 0 ≤ ∑ i, (phis S s ((L.mulVec z₀ i + h i) + L.mulVec y i) -
      phis S s (L.mulVec z₀ i + h i) - L.mulVec y i * u₀ i) :=
    Finset.sum_nonneg fun i _ => (hB i).1
  have hsum_quad : ∑ i, (phis S s ((L.mulVec z₀ i + h i) + L.mulVec y i) -
      phis S s (L.mulVec z₀ i + h i) - L.mulVec y i * u₀ i) ≤ (1 / 2) * normSq y := by
    calc ∑ i, _ ≤ ∑ i, L.mulVec y i ^ 2 / (2 * s) := Finset.sum_le_sum fun i _ => (hB i).2.1
      _ = normSq (L.mulVec y) / (2 * s) := by rw [← Finset.sum_div]; rfl
      _ ≤ (s * normSq y) / (2 * s) := by gcongr; exact normSq_mulVec_le hs_pos.le hPSD y
      _ = (1 / 2) * normSq y := by field_simp [hs_pos.ne']
  have hsum_abs : ∑ i, (phis S s ((L.mulVec z₀ i + h i) + L.mulVec y i) -
      phis S s (L.mulVec z₀ i + h i) - L.mulVec y i * u₀ i) ≤
      2 * Real.sqrt (s * (N : ℝ) * normSq y) := by
    calc ∑ i, _ ≤ ∑ i, 2 * |L.mulVec y i| := Finset.sum_le_sum fun i _ => (hB i).2.2
      _ = 2 * ∑ i, |L.mulVec y i| := by rw [← Finset.mul_sum]
      _ ≤ 2 * Real.sqrt (s * (N : ℝ) * normSq y) := by gcongr; exact sum_abs_mulVec_le hs_pos.le hPSD y
  rw [hdiff_id]
  exact ⟨by linarith, by linarith, by linarith⟩

private lemma Ualpha_minimizer_and_bounds (S : SpinLaw) (hS : IsGHS S) {s : ℝ} (hs : tau S < s)
    {N : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (L : Matrix (Fin N) (Fin N) ℝ) (h : Fin N → ℝ)
    (hPSD : (s • (1 : Matrix (Fin N) (Fin N) ℝ) - L * L.transpose).PosSemidef) :
    ∃ z₀ : Fin N → ℝ,
      normSq z₀ ≤ s * (N : ℝ) ∧
      (∀ y : Fin N → ℝ,
        0 ≤ Ualpha S s α L h (z₀ + y) - Ualpha S s α L h z₀ ∧
        Ualpha S s α L h (z₀ + y) - Ualpha S s α L h z₀ ≤ normSq y ∧
        (1 / 2) * normSq y - 2 * Real.sqrt (s * (N : ℝ) * normSq y) ≤
          Ualpha S s α L h (z₀ + y) - Ualpha S s α L h z₀) := by
  have hs_pos : 0 < s := lt_trans (tau_pos S) hs
  have hcoerc : ∃ R : ℝ, 0 ≤ R ∧
      ∀ z : Fin N → ℝ, R < ‖z‖ → Ualpha S s α L h 0 < Ualpha S s α L h z := by
    let R := 2 * Real.sqrt (s * (N : ℝ)) + 1
    refine ⟨R, by positivity, fun z hz => ?_⟩
    have h1 : ((1 + α) / 2) * normSq z - ∑ i, (phis S s (L.mulVec z i + h i) - phis S s (h i)) =
        Ualpha S s α L h z - Ualpha S s α L h 0 := by
      unfold Ualpha Wpot
      simp only [normSq_zero, Matrix.mulVec_zero, Pi.zero_apply, zero_add, mul_zero, zero_sub]
      rw [Finset.sum_sub_distrib]; ring
    have h2 : ∑ i, (phis S s (L.mulVec z i + h i) - phis S s (h i)) ≤
        ∑ i, |L.mulVec z i| := by
      refine Finset.sum_le_sum fun i _ => ?_
      calc phis S s (L.mulVec z i + h i) - phis S s (h i)
          ≤ |phis S s (L.mulVec z i + h i) - phis S s (h i)| := le_abs_self _
        _ ≤ |(L.mulVec z i + h i) - h i| := phis_sub_le S hS hs _ _
        _ = |L.mulVec z i| := by ring_nf
    have h3 : ∑ i, |L.mulVec z i| ≤ Real.sqrt (s * (N : ℝ) * normSq z) :=
      sum_abs_mulVec_le hs_pos.le hPSD z
    have h4 : Real.sqrt (s * (N : ℝ) * normSq z) = Real.sqrt (s * (N : ℝ)) * Real.sqrt (normSq z) :=
      Real.sqrt_mul (mul_nonneg hs_pos.le (Nat.cast_nonneg N)) _
    have hnorm_sq : ‖z‖ ≤ Real.sqrt (normSq z) := Real.le_sqrt_of_sq_le (pi_norm_sq_le_normSq z)
    have hR_lt : 2 * Real.sqrt (s * (N : ℝ)) + 1 < Real.sqrt (normSq z) := lt_of_lt_of_le hz hnorm_sq
    have hpos_r : 0 < Real.sqrt (normSq z) := lt_of_le_of_lt (by positivity) hR_lt
    have hsq_eq : Real.sqrt (normSq z) * Real.sqrt (normSq z) = normSq z := Real.mul_self_sqrt (normSq_nonneg z)
    have hhalf : (1 / 2 : ℝ) * normSq z ≤ ((1 + α) / 2) * normSq z := by
      nlinarith [normSq_nonneg z]
    nlinarith [Real.sqrt_nonneg (s * (N : ℝ))]
  obtain ⟨z₀, hz₀_min⟩ := exists_global_minimizer_pot (Ualpha S s α L h) (continuous_Ualpha S L h) hcoerc
  have hmin : IsLocalMin (Ualpha S s α L h) z₀ := Filter.Eventually.of_forall hz₀_min
  have hf0 : fderiv ℝ (Ualpha S s α L h) z₀ = 0 := hmin.fderiv_eq_zero
  have hf_eq := (hasFDerivAt_Ualpha_global S hS hs α L h z₀).fderiv
  rw [hf0] at hf_eq
  let u₀ : Fin N → ℝ := fun i => deriv (phis S s) (L.mulVec z₀ i + h i)
  have hz₀_j : ∀ j : Fin N, (1 + α) * z₀ j = L.transpose.mulVec u₀ j := fun j => by
    have hv := congrArg (fun f => f (Pi.single j 1)) hf_eq
    rw [ContinuousLinearMap.zero_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply] at hv
    have hL : (∑ k : Fin N, (((1 + α) * z₀ k) • coordCLM k) (Pi.single j 1)) = (1 + α) * z₀ j := by
      simp [coordCLM, ContinuousLinearMap.proj_apply, Pi.single_apply]
    have hR : (∑ i : Fin N, (u₀ i • rowCLM L i) (Pi.single j 1)) = L.transpose.mulVec u₀ j := by
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, rowCLM_apply,
        Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.single_apply, mul_ite, mul_one,
        mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      refine Finset.sum_congr rfl fun i _ => by ring
    change 0 = (∑ k : Fin N, (((1 + α) * z₀ k) • coordCLM k) (Pi.single j 1)) -
      (∑ i : Fin N, (u₀ i • rowCLM L i) (Pi.single j 1)) at hv
    rw [hL, hR] at hv
    linarith
  have hz₀_eq : (1 + α) • z₀ = L.transpose.mulVec u₀ := funext hz₀_j
  have hu₀_normSq : normSq u₀ ≤ (N : ℝ) := by
    unfold normSq
    calc ∑ i, u₀ i ^ 2 ≤ ∑ _i : Fin N, (1 : ℝ) := Finset.sum_le_sum fun i _ => by
          have := abs_deriv_phis_le_one S hS hs (L.mulVec z₀ i + h i)
          nlinarith [abs_nonneg (u₀ i), sq_abs (u₀ i)]
      _ = (N : ℝ) := by simp
  have hz₀_bound : normSq z₀ ≤ s * (N : ℝ) := by
    have hscaled : normSq ((1 + α) • z₀) = (1 + α) ^ 2 * normSq z₀ := by
      unfold normSq; simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
    have hpsd' : normSq ((1 + α) • z₀) ≤ s * (N : ℝ) := by
      rw [hz₀_eq]
      exact (normSq_transpose_mulVec_le hPSD u₀).trans (by gcongr)
    have h1a : (1 : ℝ) ≤ (1 + α) ^ 2 := by nlinarith
    nlinarith [normSq_nonneg z₀]
  refine ⟨z₀, hz₀_bound, fun y => ?_⟩
  have hdiff_id : Ualpha S s α L h (z₀ + y) - Ualpha S s α L h z₀ =
      ((1 + α) / 2) * normSq y -
        ∑ i, (phis S s ((L.mulVec z₀ i + h i) + L.mulVec y i) -
          phis S s (L.mulVec z₀ i + h i) - L.mulVec y i * u₀ i) := by
    have hLadd : ∀ i, L.mulVec (z₀ + y) i = L.mulVec z₀ i + L.mulVec y i := fun i => by
      simp [Matrix.mulVec_add]
    have hlin : ∑ j : Fin N, ((1 + α) * z₀ j) * y j = ∑ i : Fin N, L.mulVec y i * u₀ i := by
      calc ∑ j : Fin N, ((1 + α) * z₀ j) * y j
          = ∑ j : Fin N, (∑ i : Fin N, L i j * u₀ i) * y j := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [hz₀_j j]; simp [Matrix.mulVec, dotProduct]
        _ = ∑ j : Fin N, ∑ i : Fin N, L i j * u₀ i * y j := by
            refine Finset.sum_congr rfl fun j _ => Finset.sum_mul _ _ _
        _ = ∑ i : Fin N, ∑ j : Fin N, L i j * y j * u₀ i := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
        _ = ∑ i : Fin N, L.mulVec y i * u₀ i := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [← Finset.sum_mul]; rfl
    unfold Ualpha Wpot normSq
    simp_rw [hLadd, Pi.add_apply]
    have hns : (1 / 2 + α / 2 : ℝ) * ∑ j, (z₀ j + y j) ^ 2 - (1 / 2 + α / 2) * ∑ j, z₀ j ^ 2 =
        ((1 + α) / 2) * ∑ j, y j ^ 2 + ∑ j, ((1 + α) * z₀ j) * y j := by
      have hexp : ∑ j, (z₀ j + y j) ^ 2 = ∑ j, z₀ j ^ 2 + 2 * ∑ j, z₀ j * y j + ∑ j, y j ^ 2 := by
        simp_rw [add_sq]
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
        congr 1; congr 1
        refine Finset.sum_congr rfl fun j _ => by ring
      have hlin_sum : ∑ j : Fin N, ((1 + α) * z₀ j) * y j = (1 + α) * ∑ j, z₀ j * y j := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
      rw [hexp, hlin_sum]; ring
    have hsum_rem : ∑ i, (phis S s ((L.mulVec z₀ i + h i) + L.mulVec y i) -
          phis S s (L.mulVec z₀ i + h i) - L.mulVec y i * u₀ i) =
        ∑ i, phis S s (L.mulVec z₀ i + L.mulVec y i + h i) -
          ∑ i, phis S s (L.mulVec z₀ i + h i) - ∑ i, L.mulVec y i * u₀ i := by
      simp_rw [Finset.sum_sub_distrib]
      congr 1; congr 1
      refine Finset.sum_congr rfl fun i _ => by ring_nf
    rw [hsum_rem, ← hlin]
    linarith [hns]
  have hB : ∀ i, 0 ≤ phis S s ((L.mulVec z₀ i + h i) + L.mulVec y i) -
      phis S s (L.mulVec z₀ i + h i) - L.mulVec y i * u₀ i ∧
      phis S s ((L.mulVec z₀ i + h i) + L.mulVec y i) -
        phis S s (L.mulVec z₀ i + h i) - L.mulVec y i * u₀ i ≤ L.mulVec y i ^ 2 / (2 * s) ∧
      phis S s ((L.mulVec z₀ i + h i) + L.mulVec y i) -
        phis S s (L.mulVec z₀ i + h i) - L.mulVec y i * u₀ i ≤ 2 * |L.mulVec y i| :=
    fun i => phis_taylor_bounds S hS hs (L.mulVec z₀ i + h i) (L.mulVec y i)
  have hsum_nn : 0 ≤ ∑ i, (phis S s ((L.mulVec z₀ i + h i) + L.mulVec y i) -
      phis S s (L.mulVec z₀ i + h i) - L.mulVec y i * u₀ i) :=
    Finset.sum_nonneg fun i _ => (hB i).1
  have hsum_quad : ∑ i, (phis S s ((L.mulVec z₀ i + h i) + L.mulVec y i) -
      phis S s (L.mulVec z₀ i + h i) - L.mulVec y i * u₀ i) ≤ (1 / 2) * normSq y := by
    calc ∑ i, _ ≤ ∑ i, L.mulVec y i ^ 2 / (2 * s) := Finset.sum_le_sum fun i _ => (hB i).2.1
      _ = normSq (L.mulVec y) / (2 * s) := by rw [← Finset.sum_div]; rfl
      _ ≤ (s * normSq y) / (2 * s) := by gcongr; exact normSq_mulVec_le hs_pos.le hPSD y
      _ = (1 / 2) * normSq y := by field_simp [hs_pos.ne']
  have hsum_abs : ∑ i, (phis S s ((L.mulVec z₀ i + h i) + L.mulVec y i) -
      phis S s (L.mulVec z₀ i + h i) - L.mulVec y i * u₀ i) ≤
      2 * Real.sqrt (s * (N : ℝ) * normSq y) := by
    calc ∑ i, _ ≤ ∑ i, 2 * |L.mulVec y i| := Finset.sum_le_sum fun i _ => (hB i).2.2
      _ = 2 * ∑ i, |L.mulVec y i| := by rw [← Finset.mul_sum]
      _ ≤ 2 * Real.sqrt (s * (N : ℝ) * normSq y) := by gcongr; exact sum_abs_mulVec_le hs_pos.le hPSD y
  rw [hdiff_id]
  have hhalf_le : (1 / 2) * normSq y ≤ ((1 + α) / 2) * normSq y := by
    nlinarith [normSq_nonneg y]
  have hle_one : ((1 + α) / 2) * normSq y ≤ normSq y := by
    nlinarith [normSq_nonneg y]
  exact ⟨by linarith, by linarith, by linarith⟩

private lemma integrable_exp_neg_mul_normSq (N : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun y : Fin N → ℝ => Real.exp (-b * normSq y)) := by
  have heq : (fun y : Fin N → ℝ => Real.exp (-b * normSq y)) =
      (fun y : Fin N → ℝ => ∏ i : Fin N, Real.exp (-b * (y i) ^ 2)) := by
    ext y
    unfold normSq
    rw [Finset.mul_sum, Real.exp_sum]
  rw [heq]
  exact Integrable.fintype_prod (fun _ => integrable_exp_neg_mul_sq hb)

private lemma integral_exp_neg_mul_normSq (N : ℕ) {b : ℝ} (hb : 0 < b) :
    ∫ y : Fin N → ℝ, Real.exp (-b * normSq y) = (Real.sqrt (Real.pi / b)) ^ N := by
  have heq : (fun y : Fin N → ℝ => Real.exp (-b * normSq y)) =
      (fun y : Fin N → ℝ => ∏ i : Fin N, Real.exp (-b * (y i) ^ 2)) := by
    ext y
    unfold normSq
    rw [Finset.mul_sum, Real.exp_sum]
  rw [heq, integral_fintype_prod_volume_eq_pow (fun t : ℝ => Real.exp (-b * t ^ 2)),
    integral_gaussian, Fintype.card_fin]

private lemma pot_integrable_and_moment {S : SpinLaw} {s : ℝ} {N : ℕ} (F : (Fin N → ℝ) → ℝ)
    (hcont : Continuous F) (hτ_pos : 0 < tau S) (hs_le : s ≤ 2 * tau S + 1)
    (hs_pos : 0 < s) (z₀ : Fin N → ℝ) (hz₀_bd : normSq z₀ ≤ s * (N : ℝ))
    (hbounds : ∀ y : Fin N → ℝ,
      0 ≤ F (z₀ + y) - F z₀ ∧
      F (z₀ + y) - F z₀ ≤ normSq y ∧
      (1 / 2) * normSq y - 2 * Real.sqrt (s * (N : ℝ) * normSq y) ≤ F (z₀ + y) - F z₀) :
    Integrable (fun z : Fin N → ℝ => Real.exp (-F z)) ∧
    Integrable (fun z : Fin N → ℝ => normSq z * Real.exp (-F z)) ∧
    (0 < ∫ z : Fin N → ℝ, Real.exp (-F z)) ∧
    ∫ z : Fin N → ℝ, normSq z * normDens F z ≤
      (2 * (2 * tau S + 1) + 2 * ((max (16 * Real.sqrt (2 * tau S + 1)) 10) ^ 2 + 8)) * (N : ℝ) := by
  let G : (Fin N → ℝ) → ℝ := fun y => F (z₀ + y) - F z₀
  have hG_cont : Continuous G := (hcont.comp (continuous_const.add continuous_id)).sub continuous_const
  have hG_lb_quad : ∀ y : Fin N → ℝ, (1 / 4) * normSq y - 4 * s * (N : ℝ) ≤ G y := fun y => by
    have hcomp : 2 * Real.sqrt (s * (N : ℝ) * normSq y) ≤ (1 / 4) * normSq y + 4 * s * (N : ℝ) := by
      have hsq : 0 ≤ ((1 / 2) * Real.sqrt (normSq y) - 2 * Real.sqrt (s * (N : ℝ))) ^ 2 := sq_nonneg _
      have hm : Real.sqrt (s * (N : ℝ) * normSq y) =
          Real.sqrt (s * (N : ℝ)) * Real.sqrt (normSq y) :=
        Real.sqrt_mul (mul_nonneg hs_pos.le (Nat.cast_nonneg N)) _
      have hsq1 : Real.sqrt (normSq y) ^ 2 = normSq y := Real.sq_sqrt (normSq_nonneg y)
      have hsq2 : Real.sqrt (s * (N : ℝ)) ^ 2 = s * (N : ℝ) :=
        Real.sq_sqrt (mul_nonneg hs_pos.le (Nat.cast_nonneg N))
      nlinarith
    linarith [(hbounds y).2.2]
  have hG_exp_int : Integrable (fun y : Fin N → ℝ => Real.exp (-G y)) := by
    refine (integrable_exp_neg_mul_normSq N (by norm_num : (0 : ℝ) < 1 / 4)).const_mul
      (Real.exp (4 * s * (N : ℝ))) |>.mono' ?_ ?_
    · exact (Real.continuous_exp.comp hG_cont.neg).aestronglyMeasurable
    · filter_upwards with y
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith [hG_lb_quad y])
  have hG_mom_int : Integrable (fun y : Fin N → ℝ => normSq y * Real.exp (-G y)) := by
    have hns_cont : Continuous (fun y : Fin N → ℝ => normSq y) :=
      continuous_finset_sum _ fun j _ => (continuous_apply j).pow 2
    refine (integrable_exp_neg_mul_normSq N (by norm_num : (0 : ℝ) < 1 / 8)).const_mul
      (8 * Real.exp (4 * s * (N : ℝ))) |>.mono' ?_ ?_
    · exact (hns_cont.mul (Real.continuous_exp.comp hG_cont.neg)).aestronglyMeasurable
    · filter_upwards with y
      have hny : normSq y ≤ 8 * Real.exp ((1 / 8) * normSq y) := by
        linarith [Real.add_one_le_exp ((1 / 8) * normSq y)]
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (normSq_nonneg y) (Real.exp_pos _).le)]
      calc normSq y * Real.exp (-G y)
          ≤ (8 * Real.exp ((1 / 8) * normSq y)) * Real.exp (-G y) :=
            mul_le_mul_of_nonneg_right hny (Real.exp_pos _).le
        _ ≤ (8 * Real.exp ((1 / 8) * normSq y)) * Real.exp (4 * s * (N : ℝ) - (1 / 4) * normSq y) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [hG_lb_quad y])) (by positivity)
        _ = 8 * Real.exp ((1 / 8) * normSq y + (4 * s * (N : ℝ) - (1 / 4) * normSq y)) := by
            rw [mul_assoc, ← Real.exp_add]
        _ = 8 * Real.exp (4 * s * (N : ℝ) + -(1 / 8 : ℝ) * normSq y) := by
            congr 2; ring
        _ = (8 * Real.exp (4 * s * (N : ℝ))) * Real.exp (-(1 / 8 : ℝ) * normSq y) := by
            rw [Real.exp_add, ← mul_assoc]
  have hF_shift_exp : (fun y : Fin N → ℝ => Real.exp (-F (z₀ + y))) =
      fun y => Real.exp (-F z₀) * Real.exp (-G y) := by
    ext y; dsimp [G]; rw [← Real.exp_add]; congr 1; ring
  have hF_exp_int : Integrable (fun z : Fin N → ℝ => Real.exp (-F z)) := by
    have hshift : Integrable (fun y : Fin N → ℝ => Real.exp (-F (z₀ + y))) := by
      rw [hF_shift_exp]; exact hG_exp_int.const_mul _
    rw [show (fun z : Fin N → ℝ => Real.exp (-F z)) =
        fun z => (fun y => Real.exp (-F (z₀ + y))) (-z₀ + z) by
      ext z; simp [add_neg_cancel_left]]
    exact hshift.comp_add_left (-z₀)
  have hF_mom_int : Integrable (fun z : Fin N → ℝ => normSq z * Real.exp (-F z)) := by
    have hdom : Integrable (fun y : Fin N → ℝ =>
        Real.exp (-F z₀) * ((2 * normSq z₀) * Real.exp (-G y) + 2 * (normSq y * Real.exp (-G y)))) :=
      ((hG_exp_int.const_mul _).add (hG_mom_int.const_mul _)).const_mul _
    have hshift : Integrable (fun y : Fin N → ℝ => normSq (z₀ + y) * Real.exp (-F (z₀ + y))) := by
      refine hdom.mono' ?_ ?_
      · have hns_cont : Continuous (fun y : Fin N → ℝ => normSq y) :=
          continuous_finset_sum _ fun j _ => (continuous_apply j).pow 2
        exact ((hns_cont.comp (continuous_const.add continuous_id)).mul
          (Real.continuous_exp.comp ((hcont.comp (continuous_const.add continuous_id)).neg))).aestronglyMeasurable
      · filter_upwards with y
        have h1 : Real.exp (-F (z₀ + y)) = Real.exp (-F z₀) * Real.exp (-G y) := by
          dsimp [G]; rw [← Real.exp_add]; congr 1; ring
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (normSq_nonneg _) (Real.exp_pos _).le), h1]
        have h2 := normSq_add_le z₀ y
        calc normSq (z₀ + y) * (Real.exp (-F z₀) * Real.exp (-G y))
            ≤ (2 * normSq z₀ + 2 * normSq y) * (Real.exp (-F z₀) * Real.exp (-G y)) := by gcongr
          _ = Real.exp (-F z₀) * ((2 * normSq z₀) * Real.exp (-G y) + 2 * (normSq y * Real.exp (-G y))) := by ring
    rw [show (fun z : Fin N → ℝ => normSq z * Real.exp (-F z)) =
        fun z => (fun y => normSq (z₀ + y) * Real.exp (-F (z₀ + y))) (-z₀ + z) by
      ext z; simp [add_neg_cancel_left]]
    exact hshift.comp_add_left (-z₀)
  have hZG_pos : 0 < ∫ y : Fin N → ℝ, Real.exp (-G y) := by
    have hlb : (Real.sqrt (Real.pi / 1)) ^ N ≤ ∫ y : Fin N → ℝ, Real.exp (-G y) := by
      rw [← integral_exp_neg_mul_normSq N one_pos]
      refine integral_mono (integrable_exp_neg_mul_normSq N one_pos) hG_exp_int fun y => ?_
      exact Real.exp_le_exp.mpr (by linarith [(hbounds y).2.1])
    have hpi : 0 < (Real.sqrt (Real.pi / 1)) ^ N := by positivity
    exact lt_of_lt_of_le hpi hlb
  have hZF_eq : ∫ z : Fin N → ℝ, Real.exp (-F z) = Real.exp (-F z₀) * ∫ y : Fin N → ℝ, Real.exp (-G y) := by
    rw [← integral_add_left_eq_self (fun z => Real.exp (-F z)) z₀]
    simp_rw [hF_shift_exp, integral_const_mul]
  have hZF_pos : 0 < ∫ z : Fin N → ℝ, Real.exp (-F z) := by
    rw [hZF_eq]; exact mul_pos (Real.exp_pos _) hZG_pos
  refine ⟨hF_exp_int, hF_mom_int, hZF_pos, ?_⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN_pos
  · simp only [Nat.cast_zero, mul_zero]
    have h0 : (fun z : Fin 0 → ℝ => normSq z * normDens F z) = fun _ => 0 := by
      ext z; simp [normSq]
    rw [h0, integral_zero]
  · let K := max (16 * Real.sqrt (2 * tau S + 1)) 10
    have hK_ge10 : 10 ≤ K := le_max_right _ _
    have hK_ge_sqrt : 16 * Real.sqrt (2 * tau S + 1) ≤ K := le_max_left _ _
    have hK_pos : 0 < K := by positivity
    let R2 := K ^ 2 * (N : ℝ)
    have hpt : ∀ y : Fin N → ℝ, normSq y * Real.exp (-G y) ≤
        R2 * Real.exp (-G y) + 8 * Real.exp (-(K ^ 2 / 8) * (N : ℝ)) * Real.exp (-(1 / 8 : ℝ) * normSq y) := by
      intro y
      rcases le_or_gt (normSq y) R2 with hle | hgt
      · have h1 : normSq y * Real.exp (-G y) ≤ R2 * Real.exp (-G y) :=
          mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
        have h2 : 0 ≤ 8 * Real.exp (-(K ^ 2 / 8) * (N : ℝ)) * Real.exp (-(1 / 8 : ℝ) * normSq y) := by
          positivity
        linarith
      · have h2s : 2 * Real.sqrt (s * (N : ℝ) * normSq y) ≤ (1 / 8) * normSq y := by
          have hs_le' : s ≤ 2 * tau S + 1 := hs_le
          have hsqrt_s : 16 * Real.sqrt s ≤ K :=
            (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hs_le') (by norm_num)).trans hK_ge_sqrt
          have h16 : 16 * Real.sqrt (s * (N : ℝ)) ≤ K * Real.sqrt (N : ℝ) := by
            rw [Real.sqrt_mul hs_pos.le]; nlinarith [Real.sqrt_nonneg (N : ℝ)]
          have hR2_sq : (K * Real.sqrt (N : ℝ)) ^ 2 = R2 := by
            dsimp [R2]; rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
          have hsqrt_y : K * Real.sqrt (N : ℝ) ≤ Real.sqrt (normSq y) := by
            refine Real.le_sqrt_of_sq_le ?_
            rw [hR2_sq]; exact hgt.le
          have hm : Real.sqrt (s * (N : ℝ) * normSq y) =
              Real.sqrt (s * (N : ℝ)) * Real.sqrt (normSq y) :=
            Real.sqrt_mul (mul_nonneg hs_pos.le (Nat.cast_nonneg N)) _
          have hsqy : Real.sqrt (normSq y) ^ 2 = normSq y := Real.sq_sqrt (normSq_nonneg y)
          nlinarith [Real.sqrt_nonneg (s * (N : ℝ)), Real.sqrt_nonneg (normSq y)]
        have hG_tail : (3 / 8) * normSq y ≤ G y := by linarith [(hbounds y).2.2]
        have hny : normSq y ≤ 8 * Real.exp ((1 / 8) * normSq y) := by
          linarith [Real.add_one_le_exp ((1 / 8) * normSq y)]
        have hbound : normSq y * Real.exp (-G y) ≤
            8 * Real.exp (-(K ^ 2 / 8) * (N : ℝ)) * Real.exp (-(1 / 8 : ℝ) * normSq y) := by
          calc normSq y * Real.exp (-G y)
              ≤ (8 * Real.exp ((1 / 8) * normSq y)) * Real.exp (-G y) :=
                mul_le_mul_of_nonneg_right hny (Real.exp_pos _).le
            _ ≤ (8 * Real.exp ((1 / 8) * normSq y)) * Real.exp (-(3 / 8 : ℝ) * normSq y) :=
                mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity)
            _ = 8 * Real.exp (-(1 / 8 : ℝ) * normSq y) * Real.exp (-(1 / 8 : ℝ) * normSq y) := by
                rw [mul_assoc, ← Real.exp_add, mul_assoc 8, ← Real.exp_add]; congr 2; ring
            _ ≤ 8 * Real.exp (-(K ^ 2 / 8) * (N : ℝ)) * Real.exp (-(1 / 8 : ℝ) * normSq y) := by
                refine mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num))
                  (Real.exp_pos _).le
                dsimp [R2] at hgt
                linarith
        have h1 : 0 ≤ R2 * Real.exp (-G y) := by positivity
        linarith
    have hrhs_int : Integrable (fun y : Fin N → ℝ =>
        R2 * Real.exp (-G y) + 8 * Real.exp (-(K ^ 2 / 8) * (N : ℝ)) * Real.exp (-(1 / 8 : ℝ) * normSq y)) :=
      (hG_exp_int.const_mul R2).add
        ((integrable_exp_neg_mul_normSq N (by norm_num : (0 : ℝ) < 1 / 8)).const_mul _)
    have hint_mono := integral_mono hG_mom_int hrhs_int hpt
    rw [integral_add (hG_exp_int.const_mul R2)
        ((integrable_exp_neg_mul_normSq N (by norm_num : (0 : ℝ) < 1 / 8)).const_mul _),
      integral_const_mul, integral_const_mul,
      integral_exp_neg_mul_normSq N (by norm_num : (0 : ℝ) < 1 / 8)] at hint_mono
    have hZG_lb : (Real.sqrt Real.pi) ^ N ≤ ∫ y : Fin N → ℝ, Real.exp (-G y) := by
      have := integral_mono (integrable_exp_neg_mul_normSq N one_pos) hG_exp_int
        (fun y => Real.exp_le_exp.mpr (by linarith [(hbounds y).2.1]))
      rw [integral_exp_neg_mul_normSq N one_pos, div_one] at this
      exact this
    have hpi_pos : 0 < (Real.sqrt Real.pi) ^ N := by positivity
    have hratio_tail : (Real.sqrt (Real.pi / (1 / 8))) ^ N / (∫ y : Fin N → ℝ, Real.exp (-G y)) ≤ 3 ^ N := by
      have h1 : Real.sqrt (Real.pi / (1 / 8)) = Real.sqrt 8 * Real.sqrt Real.pi := by
        rw [show Real.pi / (1 / 8 : ℝ) = 8 * Real.pi by ring, Real.sqrt_mul (by norm_num)]
      have h2 : Real.sqrt (Real.pi / (1 / 8)) ^ N ≤ 3 ^ N * Real.sqrt Real.pi ^ N := by
        rw [h1, mul_pow]
        refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Real.sqrt_nonneg _) ?_ _) (by positivity)
        have : Real.sqrt 8 ≤ Real.sqrt 9 := Real.sqrt_le_sqrt (by norm_num)
        simpa [show (9 : ℝ) = 3 ^ 2 by norm_num] using this
      calc (Real.sqrt (Real.pi / (1 / 8))) ^ N / ∫ y : Fin N → ℝ, Real.exp (-G y)
          ≤ (3 ^ N * Real.sqrt Real.pi ^ N) / Real.sqrt Real.pi ^ N := by
            exact div_le_div₀ (by positivity) h2 hpi_pos hZG_lb
        _ = 3 ^ N := by field_simp [hpi_pos.ne']
    have hdecay : Real.exp (-(K ^ 2 / 8) * (N : ℝ)) * 3 ^ N ≤ 1 := by
      have hK8 : 12 ≤ K ^ 2 / 8 := by nlinarith
      have hexp3 : 3 ≤ Real.exp (K ^ 2 / 8) := by
        have := Real.add_one_le_exp (K ^ 2 / 8)
        linarith
      have h3e : 3 * Real.exp (-(K ^ 2 / 8)) ≤ 1 := by
        rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
        exact hexp3
      calc Real.exp (-(K ^ 2 / 8) * (N : ℝ)) * 3 ^ N
          = (3 * Real.exp (-(K ^ 2 / 8))) ^ N := by
            rw [mul_pow, ← Real.exp_nat_mul]; ring_nf
        _ ≤ 1 ^ N := pow_le_pow_left₀ (by positivity) h3e N
        _ = 1 := one_pow N
    have hG_moment : (∫ y : Fin N → ℝ, normSq y * Real.exp (-G y)) / (∫ y : Fin N → ℝ, Real.exp (-G y)) ≤
        R2 + 8 := by
      calc (∫ y : Fin N → ℝ, normSq y * Real.exp (-G y)) / ∫ y : Fin N → ℝ, Real.exp (-G y)
          ≤ (R2 * (∫ y : Fin N → ℝ, Real.exp (-G y)) +
              8 * Real.exp (-(K ^ 2 / 8) * (N : ℝ)) * (Real.sqrt (Real.pi / (1 / 8))) ^ N) /
              ∫ y : Fin N → ℝ, Real.exp (-G y) := by
            gcongr
        _ = R2 + 8 * (Real.exp (-(K ^ 2 / 8) * (N : ℝ)) *
              ((Real.sqrt (Real.pi / (1 / 8))) ^ N / ∫ y : Fin N → ℝ, Real.exp (-G y))) := by
            field_simp [hZG_pos.ne']
        _ ≤ R2 + 8 * (Real.exp (-(K ^ 2 / 8) * (N : ℝ)) * 3 ^ N) := by gcongr
        _ ≤ R2 + 8 * 1 := by gcongr
        _ = R2 + 8 := by ring
    have hfull_moment : ∫ z : Fin N → ℝ, normSq z * normDens F z =
        (∫ y : Fin N → ℝ, normSq (z₀ + y) * Real.exp (-G y)) / (∫ y : Fin N → ℝ, Real.exp (-G y)) := by
      unfold normDens
      simp_rw [div_eq_mul_inv, ← mul_assoc, integral_mul_const]
      rw [← integral_add_left_eq_self (fun z => normSq z * Real.exp (-F z)) z₀]
      have h1 : ∀ y, normSq (z₀ + y) * Real.exp (-F (z₀ + y)) =
          Real.exp (-F z₀) * (normSq (z₀ + y) * Real.exp (-G y)) := fun y => by
        rw [congrFun hF_shift_exp y]; ring
      simp_rw [h1, integral_const_mul, hZF_eq]
      have hexp_ne : Real.exp (-F z₀) ≠ 0 := (Real.exp_pos _).ne'
      field_simp [hexp_ne, hZG_pos.ne']
    have hsplit : ∫ y : Fin N → ℝ, normSq (z₀ + y) * Real.exp (-G y) ≤
        2 * normSq z₀ * (∫ y : Fin N → ℝ, Real.exp (-G y)) + 2 * (∫ y : Fin N → ℝ, normSq y * Real.exp (-G y)) := by
      have hint_zy : Integrable (fun y : Fin N → ℝ => normSq (z₀ + y) * Real.exp (-G y)) := by
        have this := hF_mom_int.comp_add_left z₀
        have h1 : (fun y : Fin N → ℝ => normSq (z₀ + y) * Real.exp (-G y)) =
            fun y => Real.exp (F z₀) * (normSq (z₀ + y) * Real.exp (-F (z₀ + y))) := by
          ext y; dsimp [G]; rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
        rw [h1]
        exact this.const_mul _
      have hint_ub : Integrable (fun y : Fin N → ℝ =>
          2 * normSq z₀ * Real.exp (-G y) + 2 * (normSq y * Real.exp (-G y))) :=
        (hG_exp_int.const_mul _).add (hG_mom_int.const_mul _)
      have hm := integral_mono hint_zy hint_ub fun y => by
        calc normSq (z₀ + y) * Real.exp (-G y)
            ≤ (2 * normSq z₀ + 2 * normSq y) * Real.exp (-G y) := by gcongr; exact normSq_add_le z₀ y
          _ = 2 * normSq z₀ * Real.exp (-G y) + 2 * (normSq y * Real.exp (-G y)) := by ring
      rw [integral_add (hG_exp_int.const_mul _) (hG_mom_int.const_mul _),
        integral_const_mul, integral_const_mul] at hm
      exact hm
    have hN_ge1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN_pos
    calc ∫ z : Fin N → ℝ, normSq z * normDens F z
        ≤ (2 * normSq z₀ * (∫ y : Fin N → ℝ, Real.exp (-G y)) +
            2 * (∫ y : Fin N → ℝ, normSq y * Real.exp (-G y))) / (∫ y : Fin N → ℝ, Real.exp (-G y)) := by
          rw [hfull_moment]; exact div_le_div_of_nonneg_right hsplit hZG_pos.le
      _ = 2 * normSq z₀ + 2 * ((∫ y : Fin N → ℝ, normSq y * Real.exp (-G y)) /
            (∫ y : Fin N → ℝ, Real.exp (-G y))) := by
          field_simp [hZG_pos.ne']
      _ ≤ 2 * (s * (N : ℝ)) + 2 * (R2 + 8) := by gcongr
      _ ≤ 2 * ((2 * tau S + 1) * (N : ℝ)) + 2 * (K ^ 2 * (N : ℝ) + 8 * (N : ℝ)) := by
          dsimp [R2]; gcongr; nlinarith
      _ = (2 * (2 * tau S + 1) + 2 * (K ^ 2 + 8)) * (N : ℝ) := by ring

private lemma normDens_integrable_and_integral_one {N : ℕ} (F : (Fin N → ℝ) → ℝ)
    (hInt : Integrable (fun z : Fin N → ℝ => Real.exp (-F z)))
    (hpos : 0 < ∫ z : Fin N → ℝ, Real.exp (-F z)) :
    Integrable (normDens F) ∧ ∫ z : Fin N → ℝ, normDens F z = 1 := by
  have heq : normDens F = fun z => (∫ w : Fin N → ℝ, Real.exp (-F w))⁻¹ * Real.exp (-F z) := by
    ext z; unfold normDens; ring
  rw [heq]
  refine ⟨hInt.const_mul _, ?_⟩
  rw [integral_const_mul, inv_mul_cancel₀ hpos.ne']

end MomentsAndTV

section KernelTV

private lemma prod_tv_sum_le {n : ℕ} {α : Type*} [Fintype α]
    (p q : Fin n → α → ℝ)
    (hp0 : ∀ i a, 0 ≤ p i a) (hq0 : ∀ i a, 0 ≤ q i a)
    (hp1 : ∀ i, ∑ a : α, p i a = 1) (hq1 : ∀ i, ∑ a : α, q i a = 1) :
    ∑ x : Fin n → α, |∏ i, p i (x i) - ∏ i, q i (x i)| ≤
      ∑ i : Fin n, ∑ a : α, |p i a - q i a| := by
  induction n with
  | zero =>
    simp
  | succ m ih =>
    let e : (Fin (m + 1) → α) ≃ α × (Fin m → α) :=
      { toFun := fun x => (x 0, fun i => x i.succ)
        invFun := fun ⟨a, y⟩ => Fin.cons a y
        left_inv := fun x => by
          ext i; refine Fin.cases rfl (fun _ => rfl) i
        right_inv := fun ⟨a, y⟩ => by ext <;> rfl }
    rw [← e.symm.sum_comp]
    have hsplit : ∑ ay : α × (Fin m → α),
        |∏ i, p i (e.symm ay i) - ∏ i, q i (e.symm ay i)| =
        ∑ a : α, ∑ y : Fin m → α,
          |p 0 a * (∏ i, p i.succ (y i)) - q 0 a * (∏ i, q i.succ (y i))| := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun y _ => ?_
      dsimp only [e]
      rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
      simp [Fin.cons_zero, Fin.cons_succ]
    rw [hsplit]
    have hsum_p : ∑ y : Fin m → α, ∏ i : Fin m, p i.succ (y i) = 1 := by
      rw [← Fintype.prod_sum (fun (i : Fin m) (a : α) => p i.succ a)]
      simp [hp1]
    have hsum_q : ∑ y : Fin m → α, ∏ i : Fin m, q i.succ (y i) = 1 := by
      rw [← Fintype.prod_sum (fun (i : Fin m) (a : α) => q i.succ a)]
      simp [hq1]
    have hstep : ∑ a : α, ∑ y : Fin m → α,
        |p 0 a * (∏ i, p i.succ (y i)) - q 0 a * (∏ i, q i.succ (y i))| ≤
        ∑ a : α, |p 0 a - q 0 a| +
          ∑ y : Fin m → α, |∏ i, p i.succ (y i) - ∏ i, q i.succ (y i)| := by
      calc ∑ a : α, ∑ y : Fin m → α,
            |p 0 a * (∏ i, p i.succ (y i)) - q 0 a * (∏ i, q i.succ (y i))|
          ≤ ∑ a : α, ∑ y : Fin m → α,
              (|p 0 a - q 0 a| * (∏ i, p i.succ (y i)) +
                q 0 a * |∏ i, p i.succ (y i) - ∏ i, q i.succ (y i)|) := by
            refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun y _ => ?_
            have hp_nn : 0 ≤ ∏ i : Fin m, p i.succ (y i) :=
              Finset.prod_nonneg fun i _ => hp0 _ _
            have hq_nn : 0 ≤ q 0 a := hq0 0 a
            calc |p 0 a * (∏ i, p i.succ (y i)) - q 0 a * (∏ i, q i.succ (y i))|
                = |(p 0 a - q 0 a) * (∏ i, p i.succ (y i)) +
                    q 0 a * (∏ i, p i.succ (y i) - ∏ i, q i.succ (y i))| := by
                  congr 1; ring
              _ ≤ |(p 0 a - q 0 a) * (∏ i, p i.succ (y i))| +
                    |q 0 a * (∏ i, p i.succ (y i) - ∏ i, q i.succ (y i))| := abs_add_le _ _
              _ = |p 0 a - q 0 a| * (∏ i, p i.succ (y i)) +
                    q 0 a * |∏ i, p i.succ (y i) - ∏ i, q i.succ (y i)| := by
                  rw [abs_mul, abs_mul, abs_of_nonneg hp_nn, abs_of_nonneg hq_nn]
        _ = (∑ a : α, |p 0 a - q 0 a| * (∑ y : Fin m → α, ∏ i, p i.succ (y i))) +
              (∑ a : α, q 0 a) * ∑ y : Fin m → α, |∏ i, p i.succ (y i) - ∏ i, q i.succ (y i)| := by
            simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
        _ = ∑ a : α, |p 0 a - q 0 a| +
              ∑ y : Fin m → α, |∏ i, p i.succ (y i) - ∏ i, q i.succ (y i)| := by
            rw [hsum_p, hq1 0]; simp
    have hih := ih (fun i => p i.succ) (fun i => q i.succ) (fun i => hp0 i.succ)
      (fun i => hq0 i.succ) (fun i => hp1 i.succ) (fun i => hq1 i.succ)
    rw [Fin.sum_univ_succ]
    linarith

private lemma tilt_sum_one (S : SpinLaw) (t : ℝ) :
    ∑ a : {x : ℚ // x ∈ S.A}, tilt S t (a : ℚ) = 1 := by
  unfold tilt
  have heq : ∑ a : {x : ℚ // x ∈ S.A}, (S.ρ (a : ℚ) : ℝ) * Real.exp (t * ((a : ℚ) : ℝ) - phi S t) =
      ∑ x ∈ S.A, (S.ρ x : ℝ) * Real.exp (t * (x : ℝ) - phi S t) :=
    (Finset.sum_coe_sort S.A fun x => (S.ρ x : ℝ) * Real.exp (t * (x : ℝ) - phi S t))
  rw [heq]
  have hfac : ∀ x ∈ S.A, (S.ρ x : ℝ) * Real.exp (t * (x : ℝ) - phi S t) =
      Real.exp (-phi S t) * ((S.ρ x : ℝ) * Real.exp (t * (x : ℝ))) := fun x _ => by
    rw [sub_eq_add_neg, Real.exp_add]; ring
  rw [Finset.sum_congr rfl hfac, ← Finset.mul_sum]
  change Real.exp (-phi S t) * mgf S t = 1
  unfold phi
  change Real.exp (-Real.log (mgf S t)) * mgf S t = 1
  rw [Real.exp_neg, Real.exp_log (mgf_pos S t), inv_mul_cancel₀ (mgf_pos S t).ne']

private lemma tilt_nonneg (S : SpinLaw) (t : ℝ) (a : {x : ℚ // x ∈ S.A}) :
    0 ≤ tilt S t (a : ℚ) := by
  unfold tilt
  have : 0 ≤ (S.ρ (a : ℚ) : ℝ) := by exact_mod_cast (S.pos _ a.2).le
  positivity

private lemma tilt_sub_le (S : SpinLaw) (a : {x : ℚ // x ∈ S.A}) (t₁ t₂ : ℝ) :
    |tilt S t₁ (a : ℚ) - tilt S t₂ (a : ℚ)| ≤ 2 * |t₁ - t₂| := by
  have hderiv : ∀ r : ℝ,
      HasDerivAt (fun u => tilt S u (a : ℚ)) (tilt S r (a : ℚ) * (((a : ℚ) : ℝ) - deriv (phi S) r)) r := by
    intro r
    unfold tilt
    have hd_phi : HasDerivAt (phi S) (deriv (phi S) r) r := by
      simpa [← (hasDerivAt_phi S r).deriv] using hasDerivAt_phi S r
    have hlin : HasDerivAt (fun u : ℝ => u * ((a : ℚ) : ℝ)) ((a : ℚ) : ℝ) r := by
      simpa using (hasDerivAt_id' r).mul_const ((a : ℚ) : ℝ)
    have hexp := (hlin.sub hd_phi).exp.const_mul (S.ρ (a : ℚ) : ℝ)
    exact hexp.congr_deriv (by simp only [Pi.sub_apply]; ring)
  have hle2 : ∀ r : ℝ, ‖deriv (fun u => tilt S u (a : ℚ)) r‖ ≤ 2 := fun r => by
    rw [(hderiv r).deriv, Real.norm_eq_abs, abs_mul]
    have h1 : |tilt S r (a : ℚ)| ≤ 1 := by
      rw [abs_of_nonneg (tilt_nonneg S r a)]
      calc tilt S r (a : ℚ) ≤ ∑ b : {x : ℚ // x ∈ S.A}, tilt S r (b : ℚ) :=
            Finset.single_le_sum (fun b _ => tilt_nonneg S r b) (Finset.mem_univ a)
        _ = 1 := tilt_sum_one S r
    have ha1 : |((a : ℚ) : ℝ)| ≤ 1 := by
      have := S.mem_Icc (a : ℚ) a.2
      rw [abs_le]
      constructor
      · exact_mod_cast this.1
      · exact_mod_cast this.2
    have h2 : |((a : ℚ) : ℝ) - deriv (phi S) r| ≤ 2 := by
      calc |((a : ℚ) : ℝ) - deriv (phi S) r|
          ≤ |((a : ℚ) : ℝ)| + |deriv (phi S) r| := abs_sub _ _
        _ ≤ 1 + 1 := add_le_add ha1 (deriv_phi_bdd S r)
        _ = 2 := by norm_num
    nlinarith [abs_nonneg (tilt S r (a : ℚ)), abs_nonneg (((a : ℚ) : ℝ) - deriv (phi S) r)]
  have hmv := convex_univ.norm_image_sub_le_of_norm_deriv_le (C := 2)
    (fun r _ => (hderiv r).differentiableAt) (fun r _ => hle2 r) (Set.mem_univ t₂) (Set.mem_univ t₁)
  simpa [Real.norm_eq_abs] using hmv

private lemma exp_neg_sub_exp_neg_le {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    |Real.exp (-A) - Real.exp (-B)| ≤ |A - B| := by
  have h : ∀ x y : ℝ, 0 ≤ x → x ≤ y → |Real.exp (-x) - Real.exp (-y)| ≤ |x - y| := by
    intro x y hx hxy
    have hmv := (convex_Ici 0).norm_image_sub_le_of_norm_deriv_le (f := fun u => Real.exp (-u)) (C := 1)
      (fun u _ => (hasDerivAt_id u).neg.exp.differentiableAt)
      (fun u hu => by
        have hd : HasDerivAt (fun t => Real.exp (-t)) (-Real.exp (-u)) u := by
          simpa using (hasDerivAt_id u).neg.exp
        rw [hd.deriv, Real.norm_eq_abs, abs_neg, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
        linarith [hu.out])
      hx (hx.trans hxy)
    simpa [Real.norm_eq_abs, one_mul, abs_sub_comm] using hmv
  rcases le_or_gt A B with hAB | hBA
  · exact h A B hA hAB
  · rw [abs_sub_comm, abs_sub_comm A B]
    exact h B A hB hBA.le

end KernelTV

/-- Full solution to `CritWinSpin.p4b_lemma_4_3_from_lemma_4_2` (Lemma 4.3, pp. 15–16, eq. (23)). -/
theorem solution (S : SpinLaw) (hS : IsGHS S) (_hP : ∀ (S : SpinLaw) (p : ℕ) (hS : IsGHS S) (hp : IsTypeP S p), ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, tau S < s →
      (∃! a : ℝ, 0 < a ∧ a = s * deriv (phi S) a) ∧
      (0 < asOf S s ∧ asOf S s = s * deriv (phi S) (asOf S s)) ∧
      ConvexOn ℝ Set.univ (gs S s) ∧ ContDiff ℝ 1 (gs S s) ∧
      (∀ t : ℝ, |t| ≠ asOf S s →
        |deriv (phis S s) t| ≤ 1 ∧ |deriv (ds S s) t| ≤ 1 ∧
        0 ≤ iteratedDeriv 2 (phis S s) t ∧ iteratedDeriv 2 (phis S s) t ≤ 1 / s) ∧
      (∀ t : ℝ, 0 ≤ ds S s t ∧ ds S s t ≤ deltaS S s) ∧
      deltaS S s ≤ C * (s - tau S) ^ ((p : ℝ) / ((p : ℝ) - 1))) :
    ∃ M₀ Cₖ : ℝ, 0 < M₀ ∧ 0 < Cₖ ∧
      ∀ (N : ℕ) (L : Matrix (Fin N) (Fin N) ℝ) (s α : ℝ) (h : Fin N → ℝ),
        tau S < s → s ≤ 2 * tau S + 1 →
        (s • (1 : Matrix (Fin N) (Fin N) ℝ) - L * L.transpose).PosSemidef →
        0 < α → α ≤ 1 →
        (∀ᵐ z : Fin N → ℝ,
          DifferentiableAt ℝ (fderiv ℝ (Wpot S s L h)) z ∧
          DifferentiableAt ℝ (fderiv ℝ (Ualpha S s α L h)) z ∧
          ∀ v : Fin N → ℝ,
            0 ≤ fderiv ℝ (fderiv ℝ (Wpot S s L h)) z v v ∧
            fderiv ℝ (fderiv ℝ (Wpot S s L h)) z v v ≤ normSq v ∧
            α * normSq v ≤ fderiv ℝ (fderiv ℝ (Ualpha S s α L h)) z v v ∧
            fderiv ℝ (fderiv ℝ (Ualpha S s α L h)) z v v ≤ (1 + α) * normSq v) ∧
        (Integrable (fun z : Fin N → ℝ => Real.exp (-Wpot S s L h z)) ∧
          Integrable (fun z : Fin N → ℝ => normSq z * Real.exp (-Wpot S s L h z)) ∧
          Integrable (fun z : Fin N → ℝ => Real.exp (-Ualpha S s α L h z)) ∧
          Integrable (fun z : Fin N → ℝ => normSq z * Real.exp (-Ualpha S s α L h z)) ∧
          max (∫ z : Fin N → ℝ, normSq z * normDens (Wpot S s L h) z)
              (∫ z : Fin N → ℝ, normSq z * normDens (Ualpha S s α L h) z) ≤ M₀ * (N : ℝ) ∧
          (1 / 2) * (∫ z : Fin N → ℝ,
              |normDens (Ualpha S s α L h) z - normDens (Wpot S s L h) z|) ≤
            α * M₀ * (N : ℝ) / 2) ∧
        (∀ z w : Fin N → ℝ,
          tvDist (kernelK S s L h z) (kernelK S s L h w) ≤
            Cₖ * Real.sqrt (N : ℝ) * Real.sqrt (normSq (z - w))) := by
  let K : ℝ := max (16 * Real.sqrt (2 * tau S + 1)) 10
  let M₀ : ℝ := 2 * (2 * tau S + 1) + 2 * (K ^ 2 + 8)
  let Cₖ : ℝ := ((S.A.card : ℝ) + 1) * Real.sqrt (2 * tau S + 1) + 1
  have hτpos := tau_pos S
  have hM₀_pos : 0 < M₀ := by dsimp [M₀, K]; positivity
  have hCₖ_pos : 0 < Cₖ := by dsimp [Cₖ]; positivity
  refine ⟨M₀, Cₖ, hM₀_pos, hCₖ_pos, fun N L s α h hs_gt hs_le hPSD hα0 hα1 => ?_⟩
  have hs_pos : 0 < s := lt_trans hτpos hs_gt
  have hPart1 := ae_hessian_bounds S hS hs_gt L h α hPSD hα0
  obtain ⟨zW, hzW_bd, hzW_props⟩ := Wpot_minimizer_and_bounds S hS hs_gt L h hPSD
  obtain ⟨zU, hzU_bd, hzU_props⟩ := Ualpha_minimizer_and_bounds S hS hs_gt hα0 hα1 L h hPSD
  have hW_res := pot_integrable_and_moment (Wpot S s L h) (continuous_Wpot S L h) hτpos hs_le
    hs_pos zW hzW_bd (fun y => ⟨(hzW_props y).1, by linarith [(hzW_props y).2.1, normSq_nonneg y], (hzW_props y).2.2⟩)
  have hU_res := pot_integrable_and_moment (Ualpha S s α L h) (continuous_Ualpha S L h) hτpos hs_le
    hs_pos zU hzU_bd hzU_props
  rcases hW_res with ⟨hW_int, hW_mom_int, hZW_pos, hW_mom_bd⟩
  rcases hU_res with ⟨hU_int, hU_mom_int, hZU_pos, hU_mom_bd⟩
  have h_tv_dens : (1 / 2) * (∫ z : Fin N → ℝ,
      |normDens (Ualpha S s α L h) z - normDens (Wpot S s L h) z|) ≤ α * M₀ * (N : ℝ) / 2 := by
    obtain ⟨hpW_int, hpW_one⟩ := normDens_integrable_and_integral_one (Wpot S s L h) hW_int hZW_pos
    obtain ⟨hpU_int, hpU_one⟩ := normDens_integrable_and_integral_one (Ualpha S s α L h) hU_int hZU_pos
    let Z_W := ∫ w : Fin N → ℝ, Real.exp (-Wpot S s L h w)
    let Z_U := ∫ w : Fin N → ℝ, Real.exp (-Ualpha S s α L h w)
    have hZU_le_ZW : Z_U ≤ Z_W := by
      refine integral_mono hU_int hW_int fun z => Real.exp_le_exp.mpr ?_
      unfold Ualpha
      linarith [show (0 : ℝ) ≤ (α / 2) * normSq z by exact mul_nonneg (div_nonneg hα0.le (by norm_num)) (normSq_nonneg z)]
    have hdiff_pt : ∀ z : Fin N → ℝ,
        max (normDens (Wpot S s L h) z - normDens (Ualpha S s α L h) z) 0 ≤
          (α / 2) * (normSq z * normDens (Wpot S s L h) z) := by
      intro z
      refine max_le ?_ (mul_nonneg (div_nonneg hα0.le (by norm_num))
        (mul_nonneg (normSq_nonneg z) (div_nonneg (Real.exp_pos _).le hZW_pos.le)))
      unfold normDens
      have h1 : Real.exp (-Ualpha S s α L h z) / Z_W ≤ Real.exp (-Ualpha S s α L h z) / Z_U :=
        div_le_div_of_nonneg_left (Real.exp_pos _).le hZU_pos hZU_le_ZW
      have h2 : Real.exp (-Wpot S s L h z) / Z_W - Real.exp (-Ualpha S s α L h z) / Z_W =
          (Real.exp (-Wpot S s L h z) / Z_W) * (1 - Real.exp (-((α / 2) * normSq z))) := by
        unfold Ualpha
        rw [show -(Wpot S s L h z + (α / 2) * normSq z) = -Wpot S s L h z + -((α / 2) * normSq z) by ring,
          Real.exp_add]
        ring
      have h3 : 1 - Real.exp (-((α / 2) * normSq z)) ≤ (α / 2) * normSq z := by
        linarith [Real.add_one_le_exp (-((α / 2) * normSq z))]
      calc Real.exp (-Wpot S s L h z) / Z_W - Real.exp (-Ualpha S s α L h z) / Z_U
          ≤ Real.exp (-Wpot S s L h z) / Z_W - Real.exp (-Ualpha S s α L h z) / Z_W := by linarith
        _ = (Real.exp (-Wpot S s L h z) / Z_W) * (1 - Real.exp (-((α / 2) * normSq z))) := h2
        _ ≤ (Real.exp (-Wpot S s L h z) / Z_W) * ((α / 2) * normSq z) := by
            gcongr
        _ = (α / 2) * (normSq z * (Real.exp (-Wpot S s L h z) / Z_W)) := by ring
    have h_abs_eq : ∀ z : Fin N → ℝ,
        |normDens (Ualpha S s α L h) z - normDens (Wpot S s L h) z| =
          2 * max (normDens (Wpot S s L h) z - normDens (Ualpha S s α L h) z) 0 -
            (normDens (Wpot S s L h) z - normDens (Ualpha S s α L h) z) := fun z => by
      rw [abs_sub_comm]
      rcases le_or_gt 0 (normDens (Wpot S s L h) z - normDens (Ualpha S s α L h) z) with hle | hgt
      · rw [abs_of_nonneg hle, max_eq_left hle]; ring
      · rw [abs_of_neg hgt, max_eq_right hgt.le]; ring
    have hdiff_int : Integrable (fun z : Fin N → ℝ =>
        normDens (Wpot S s L h) z - normDens (Ualpha S s α L h) z) := hpW_int.sub hpU_int
    have hmax_int : Integrable (fun z : Fin N → ℝ =>
        max (normDens (Wpot S s L h) z - normDens (Ualpha S s α L h) z) 0) := by
      have heq : (fun z : Fin N → ℝ =>
          max (normDens (Wpot S s L h) z - normDens (Ualpha S s α L h) z) 0) =
          fun z => ((normDens (Wpot S s L h) z - normDens (Ualpha S s α L h) z) +
            |normDens (Wpot S s L h) z - normDens (Ualpha S s α L h) z|) / 2 := by
        ext z
        rcases le_total (normDens (Wpot S s L h) z - normDens (Ualpha S s α L h) z) 0 with h | h
        · rw [max_eq_right h, abs_of_nonpos h]; ring
        · rw [max_eq_left h, abs_of_nonneg h]; ring
      rw [heq]
      exact (hdiff_int.add hdiff_int.abs).div_const 2
    have hmom_dens_int : Integrable (fun z : Fin N → ℝ => normSq z * normDens (Wpot S s L h) z) := by
      have : (fun z : Fin N → ℝ => normSq z * normDens (Wpot S s L h) z) =
          fun z => Z_W⁻¹ * (normSq z * Real.exp (-Wpot S s L h z)) := by
        ext z; unfold normDens; ring
      rw [this]; exact hW_mom_int.const_mul _
    have hint_diff_zero : ∫ z : Fin N → ℝ,
        (normDens (Wpot S s L h) z - normDens (Ualpha S s α L h) z) = 0 := by
      rw [integral_sub hpW_int hpU_int, hpW_one, hpU_one, sub_self]
    have hcalc : ∫ z : Fin N → ℝ, |normDens (Ualpha S s α L h) z - normDens (Wpot S s L h) z| =
        2 * ∫ z : Fin N → ℝ, max (normDens (Wpot S s L h) z - normDens (Ualpha S s α L h) z) 0 := by
      simp_rw [h_abs_eq]
      rw [integral_sub (hmax_int.const_mul 2) hdiff_int, integral_const_mul, hint_diff_zero, sub_zero]
    rw [hcalc]
    have hmono := integral_mono hmax_int (hmom_dens_int.const_mul (α / 2)) hdiff_pt
    rw [integral_const_mul] at hmono
    nlinarith [hW_mom_bd]
  have hPart3 : ∀ z w : Fin N → ℝ,
      tvDist (kernelK S s L h z) (kernelK S s L h w) ≤
        Cₖ * Real.sqrt (N : ℝ) * Real.sqrt (normSq (z - w)) := by
    intro z w
    rcases Nat.eq_zero_or_pos N with rfl | hN_pos
    · have : z = w := Subsingleton.elim _ _
      subst this
      simp [tvDist, normSq_zero]
    · let Az := ∑ i : Fin N, ds S s (L.mulVec z i + h i)
      let Bw := ∑ i : Fin N, ds S s (L.mulVec w i + h i)
      have hAz_nn : 0 ≤ Az := Finset.sum_nonneg fun i _ => ds_nonneg S hS hs_gt _
      have hBw_nn : 0 ≤ Bw := Finset.sum_nonneg fun i _ => ds_nonneg S hS hs_gt _
      have hV_W_z : hsV S L h z - Wpot S s L h z = Az := by
        unfold hsV Wpot
        have : ∀ i, phis S s (L.mulVec z i + h i) - phi S (L.mulVec z i + h i) =
            ds S s (L.mulVec z i + h i) := fun i => by unfold ds phis fs; ring
        calc (1 / 2 * normSq z - ∑ i, phi S (L.mulVec z i + h i)) -
              (1 / 2 * normSq z - ∑ i, phis S s (L.mulVec z i + h i))
            = ∑ i, (phis S s (L.mulVec z i + h i) - phi S (L.mulVec z i + h i)) := by
              rw [sub_sub_sub_cancel_left, ← Finset.sum_sub_distrib]
          _ = Az := Finset.sum_congr rfl fun i _ => this i
      have hV_W_w : hsV S L h w - Wpot S s L h w = Bw := by
        unfold hsV Wpot
        have : ∀ i, phis S s (L.mulVec w i + h i) - phi S (L.mulVec w i + h i) =
            ds S s (L.mulVec w i + h i) := fun i => by unfold ds phis fs; ring
        calc (1 / 2 * normSq w - ∑ i, phi S (L.mulVec w i + h i)) -
              (1 / 2 * normSq w - ∑ i, phis S s (L.mulVec w i + h i))
            = ∑ i, (phis S s (L.mulVec w i + h i) - phi S (L.mulVec w i + h i)) := by
              rw [sub_sub_sub_cancel_left, ← Finset.sum_sub_distrib]
          _ = Bw := Finset.sum_congr rfl fun i _ => this i
      have hsum_L : ∑ i : Fin N, |L.mulVec z i - L.mulVec w i| ≤
          Real.sqrt (s * (N : ℝ) * normSq (z - w)) := by
        have hLw : ∀ i, L.mulVec z i - L.mulVec w i = L.mulVec (z - w) i := fun i => by
          simp [Matrix.mulVec_sub]
        simp_rw [hLw]
        exact sum_abs_mulVec_le hs_pos.le hPSD (z - w)
      have hAB_diff : |Az - Bw| ≤ Real.sqrt (s * (N : ℝ) * normSq (z - w)) := by
        calc |Az - Bw| = |∑ i, (ds S s (L.mulVec z i + h i) - ds S s (L.mulVec w i + h i))| := by
              rw [Finset.sum_sub_distrib]
          _ ≤ ∑ i, |ds S s (L.mulVec z i + h i) - ds S s (L.mulVec w i + h i)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ i, |(L.mulVec z i + h i) - (L.mulVec w i + h i)| :=
              Finset.sum_le_sum fun i _ => ds_sub_le S hS hs_gt _ _
          _ = ∑ i, |L.mulVec z i - L.mulVec w i| :=
              Finset.sum_congr rfl fun i _ => by ring_nf
          _ ≤ Real.sqrt (s * (N : ℝ) * normSq (z - w)) := hsum_L
      have hexp_diff : |Real.exp (-Az) - Real.exp (-Bw)| ≤
          Real.sqrt (s * (N : ℝ) * normSq (z - w)) :=
        (exp_neg_sub_exp_neg_le hAz_nn hBw_nn).trans hAB_diff
      have hcond_tv : ∑ x : Config S (Fin N), |condP S L h z x - condP S L h w x| ≤
          2 * (S.A.card : ℝ) * ∑ i : Fin N, |L.mulVec z i - L.mulVec w i| := by
        let p : Fin N → {x : ℚ // x ∈ S.A} → ℝ := fun i a => tilt S (L.mulVec z i + h i) (a : ℚ)
        let q : Fin N → {x : ℚ // x ∈ S.A} → ℝ := fun i a => tilt S (L.mulVec w i + h i) (a : ℚ)
        have hprod_bound := prod_tv_sum_le p q (fun i a => tilt_nonneg S _ a)
          (fun i a => tilt_nonneg S _ a) (fun i => tilt_sum_one S _) (fun i => tilt_sum_one S _)
        calc ∑ x : Config S (Fin N), |condP S L h z x - condP S L h w x|
            = ∑ x : Fin N → {x : ℚ // x ∈ S.A}, |∏ i, p i (x i) - ∏ i, q i (x i)| := rfl
          _ ≤ ∑ i : Fin N, ∑ a : {x : ℚ // x ∈ S.A}, |p i a - q i a| := hprod_bound
          _ ≤ ∑ i : Fin N, ∑ _a : {x : ℚ // x ∈ S.A}, (2 * |L.mulVec z i - L.mulVec w i|) := by
              refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun a _ => ?_
              have h1 := tilt_sub_le S a (L.mulVec z i + h i) (L.mulVec w i + h i)
              simpa [p, q, add_sub_add_right_eq_sub] using h1
          _ = 2 * (S.A.card : ℝ) * ∑ i : Fin N, |L.mulVec z i - L.mulVec w i| := by
              simp [Fintype.card_coe, Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
              refine Finset.sum_congr rfl fun i _ => by ring
      have hsum_cond_z : ∑ x : Config S (Fin N), condP S L h z x = 1 := by
        unfold condP
        rw [← Fintype.prod_sum (fun (i : Fin N) (a : {x : ℚ // x ∈ S.A}) => tilt S (L.mulVec z i + h i) (a : ℚ))]
        exact Finset.prod_eq_one fun i _ => tilt_sum_one S _
      have htv_split : tvDist (kernelK S s L h z) (kernelK S s L h w) ≤
          |Real.exp (-Az) - Real.exp (-Bw)| +
            (1 / 2) * ∑ x : Config S (Fin N), |condP S L h z x - condP S L h w x| := by
        unfold tvDist
        rw [Fintype.sum_option]
        have hnone : |kernelK S s L h z none - kernelK S s L h w none| =
            |Real.exp (-Az) - Real.exp (-Bw)| := by
          simp only [kernelK, hV_W_z, hV_W_w]
          rw [show (1 - Real.exp (-Az)) - (1 - Real.exp (-Bw)) = -(Real.exp (-Az) - Real.exp (-Bw)) by ring,
            abs_neg]
        have hsome : ∑ x : Config S (Fin N), |kernelK S s L h z (some x) - kernelK S s L h w (some x)| ≤
            |Real.exp (-Az) - Real.exp (-Bw)| +
              ∑ x : Config S (Fin N), |condP S L h z x - condP S L h w x| := by
          calc ∑ x : Config S (Fin N), |kernelK S s L h z (some x) - kernelK S s L h w (some x)|
              = ∑ x : Config S (Fin N),
                  |Real.exp (-Az) * condP S L h z x - Real.exp (-Bw) * condP S L h w x| := by
                simp only [kernelK, hV_W_z, hV_W_w]
            _ ≤ ∑ x : Config S (Fin N),
                  (|Real.exp (-Az) - Real.exp (-Bw)| * condP S L h z x +
                    Real.exp (-Bw) * |condP S L h z x - condP S L h w x|) := by
                refine Finset.sum_le_sum fun x _ => ?_
                have hcz_nn : 0 ≤ condP S L h z x :=
                  Finset.prod_nonneg fun i _ => tilt_nonneg S _ (x i)
                have hbw_nn : 0 ≤ Real.exp (-Bw) := (Real.exp_pos _).le
                calc |Real.exp (-Az) * condP S L h z x - Real.exp (-Bw) * condP S L h w x|
                    = |(Real.exp (-Az) - Real.exp (-Bw)) * condP S L h z x +
                        Real.exp (-Bw) * (condP S L h z x - condP S L h w x)| := by
                      congr 1; ring
                  _ ≤ |(Real.exp (-Az) - Real.exp (-Bw)) * condP S L h z x| +
                        |Real.exp (-Bw) * (condP S L h z x - condP S L h w x)| := abs_add_le _ _
                  _ = |Real.exp (-Az) - Real.exp (-Bw)| * condP S L h z x +
                        Real.exp (-Bw) * |condP S L h z x - condP S L h w x| := by
                      rw [abs_mul, abs_mul, abs_of_nonneg hcz_nn, abs_of_nonneg hbw_nn]
            _ = |Real.exp (-Az) - Real.exp (-Bw)| * (∑ x, condP S L h z x) +
                  Real.exp (-Bw) * ∑ x, |condP S L h z x - condP S L h w x| := by
                rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
            _ ≤ |Real.exp (-Az) - Real.exp (-Bw)| * 1 +
                  1 * ∑ x, |condP S L h z x - condP S L h w x| := by
                rw [hsum_cond_z]
                have hexp_le1 : Real.exp (-Bw) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
                have hsum_nn : 0 ≤ ∑ x : Config S (Fin N), |condP S L h z x - condP S L h w x| :=
                  Finset.sum_nonneg fun _ _ => abs_nonneg _
                exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hexp_le1 hsum_nn)
            _ = |Real.exp (-Az) - Real.exp (-Bw)| +
                  ∑ x, |condP S L h z x - condP S L h w x| := by ring
        rw [hnone]
        linarith
      have hsqrt_s : Real.sqrt (s * (N : ℝ) * normSq (z - w)) ≤
          Real.sqrt (2 * tau S + 1) * Real.sqrt (N : ℝ) * Real.sqrt (normSq (z - w)) := by
        rw [Real.sqrt_mul (mul_nonneg hs_pos.le (Nat.cast_nonneg N)),
          Real.sqrt_mul hs_pos.le]
        have : Real.sqrt s ≤ Real.sqrt (2 * tau S + 1) := Real.sqrt_le_sqrt hs_le
        gcongr
      calc tvDist (kernelK S s L h z) (kernelK S s L h w)
          ≤ |Real.exp (-Az) - Real.exp (-Bw)| +
              (1 / 2) * (2 * (S.A.card : ℝ) * ∑ i : Fin N, |L.mulVec z i - L.mulVec w i|) := by
            linarith [htv_split, hcond_tv]
        _ ≤ Real.sqrt (s * (N : ℝ) * normSq (z - w)) +
              (S.A.card : ℝ) * Real.sqrt (s * (N : ℝ) * normSq (z - w)) := by
            have hcard_nn : (0 : ℝ) ≤ (S.A.card : ℝ) := Nat.cast_nonneg _
            nlinarith [hexp_diff, hsum_L]
        _ = ((S.A.card : ℝ) + 1) * Real.sqrt (s * (N : ℝ) * normSq (z - w)) := by ring
        _ ≤ ((S.A.card : ℝ) + 1) * (Real.sqrt (2 * tau S + 1) * Real.sqrt (N : ℝ) * Real.sqrt (normSq (z - w))) := by
            gcongr
        _ ≤ Cₖ * Real.sqrt (N : ℝ) * Real.sqrt (normSq (z - w)) := by
            dsimp [Cₖ]
            have hnn : 0 ≤ Real.sqrt (N : ℝ) * Real.sqrt (normSq (z - w)) := by positivity
            nlinarith
  exact ⟨hPart1, ⟨hW_int, hW_mom_int, hU_int, hU_mom_int,
    by dsimp [M₀, K]; exact max_le hW_mom_bd hU_mom_bd, h_tv_dens⟩, hPart3⟩

end P4bL43

/-- Root-level solution matching `CritWinSpin.p4b_lemma_4_3_from_lemma_4_2` verbatim. -/
theorem solution (S : SpinLaw) (hS : IsGHS S) (hP : ∀ (S : SpinLaw) (p : ℕ) (hS : IsGHS S) (hp : IsTypeP S p), ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, tau S < s →
      (∃! a : ℝ, 0 < a ∧ a = s * deriv (phi S) a) ∧
      (0 < asOf S s ∧ asOf S s = s * deriv (phi S) (asOf S s)) ∧
      ConvexOn ℝ Set.univ (gs S s) ∧ ContDiff ℝ 1 (gs S s) ∧
      (∀ t : ℝ, |t| ≠ asOf S s →
        |deriv (phis S s) t| ≤ 1 ∧ |deriv (ds S s) t| ≤ 1 ∧
        0 ≤ iteratedDeriv 2 (phis S s) t ∧ iteratedDeriv 2 (phis S s) t ≤ 1 / s) ∧
      (∀ t : ℝ, 0 ≤ ds S s t ∧ ds S s t ≤ deltaS S s) ∧
      deltaS S s ≤ C * (s - tau S) ^ ((p : ℝ) / ((p : ℝ) - 1))) :
    ∃ M₀ Cₖ : ℝ, 0 < M₀ ∧ 0 < Cₖ ∧
      ∀ (N : ℕ) (L : Matrix (Fin N) (Fin N) ℝ) (s α : ℝ) (h : Fin N → ℝ),
        tau S < s → s ≤ 2 * tau S + 1 →
        (s • (1 : Matrix (Fin N) (Fin N) ℝ) - L * L.transpose).PosSemidef →
        0 < α → α ≤ 1 →
        (∀ᵐ z : Fin N → ℝ,
          DifferentiableAt ℝ (fderiv ℝ (Wpot S s L h)) z ∧
          DifferentiableAt ℝ (fderiv ℝ (Ualpha S s α L h)) z ∧
          ∀ v : Fin N → ℝ,
            0 ≤ fderiv ℝ (fderiv ℝ (Wpot S s L h)) z v v ∧
            fderiv ℝ (fderiv ℝ (Wpot S s L h)) z v v ≤ normSq v ∧
            α * normSq v ≤ fderiv ℝ (fderiv ℝ (Ualpha S s α L h)) z v v ∧
            fderiv ℝ (fderiv ℝ (Ualpha S s α L h)) z v v ≤ (1 + α) * normSq v) ∧
        (Integrable (fun z : Fin N → ℝ => Real.exp (-Wpot S s L h z)) ∧
          Integrable (fun z : Fin N → ℝ => normSq z * Real.exp (-Wpot S s L h z)) ∧
          Integrable (fun z : Fin N → ℝ => Real.exp (-Ualpha S s α L h z)) ∧
          Integrable (fun z : Fin N → ℝ => normSq z * Real.exp (-Ualpha S s α L h z)) ∧
          max (∫ z : Fin N → ℝ, normSq z * normDens (Wpot S s L h) z)
              (∫ z : Fin N → ℝ, normSq z * normDens (Ualpha S s α L h) z) ≤ M₀ * (N : ℝ) ∧
          (1 / 2) * (∫ z : Fin N → ℝ,
              |normDens (Ualpha S s α L h) z - normDens (Wpot S s L h) z|) ≤
            α * M₀ * (N : ℝ) / 2) ∧
        (∀ z w : Fin N → ℝ,
          tvDist (kernelK S s L h z) (kernelK S s L h w) ≤
            Cₖ * Real.sqrt (N : ℝ) * Real.sqrt (normSq (z - w))) :=
  P4bL43.solution S hS hP

